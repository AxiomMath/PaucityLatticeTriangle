/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Data.Nat.Log
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Paucity.Defs.Resonant
public import Paucity.Main.CountSmallM
public import Paucity.Lattice.Quadcount

/-!
# Resonant pairs are few

For every `ε > 0`, the pairs `(p, q) ∈ H n` that are resonant for `n` number at most
`C(ε) n^(1+ε)`, with `C` depending only on `ε`. A resonant pair is assigned the five
dyadic exponents of a chosen resonance witness `(d, k, ℓ)`, and each fibre of that
assignment injects into a set of quadruples counted by `quadcount`.

## Main definitions

* `ResData`: the resonance witness data `(d, k, ℓ)` of a pair.
* `resWit`: a chosen resonance witness.
* `resIdx`: the five dyadic exponents `(d, log₂|k|, log₂|ℓ|, log₂ p, log₂ q)` of a pair.
* `idxBox`: the admissible exponent tuples.

## Main results

* `dyadic_bounds`: `2^(log₂ m) ≤ m < 2 · 2^(log₂ m)` for `m ≠ 0`.
* `card_fiber_le_ncard_quadSet`: each fibre of `resIdx` injects into the quadruples of the
  corresponding `quadSet`.
* `dyadic_prod_le`: the witness inequality in dyadic form.
* `card_fiber_le`: the count of a single fibre.
* `log_two_succ_le`: `log₂ n + 1 ≤ (1 + 1/log 2)(1 + log n)`.
* `card_resonant_le`: for every `ε > 0` there is `C > 0` bounding the number of pairs of
  `H n` that are resonant for `n` by `C n^(1+ε)`, for every `n ≥ 5`.
-/

@[expose] public section

namespace Paucity

open Finset

/-- `ResData n p q w`: the tuple `w = (d, k, ℓ)` witnesses the resonance of `(p, q)`, that
is, `d ∈ D n`, `(k, ℓ) ∈ latticeBox d p q`, `k ℓ ≠ 0` and
`|k ℓ| M n p q ≤ 1000 d Q n`. -/
def ResData (n p q : ℕ) (w : ℕ × ℤ × ℤ) : Prop :=
  w.1 ∈ D n ∧ w.2 ∈ latticeBox w.1 p q ∧ w.2.1 * w.2.2 ≠ 0 ∧
    |((w.2.1 * w.2.2 : ℤ) : ℝ)| * M n p q ≤ 1000 * (w.1 : ℝ) * Q n

theorem resonant_iff {n p q : ℕ} : Resonant n p q ↔ ∃ w, ResData n p q w :=
  ⟨fun ⟨d, hd, kl, hkl, hne, hle⟩ => ⟨(d, kl), hd, hkl, hne, hle⟩,
    fun ⟨w, hd, hkl, hne, hle⟩ => ⟨w.1, hd, w.2, hkl, hne, hle⟩⟩

/-- A tuple witnessing the resonance of `(p, q)` when the pair is resonant, and
`(0, 0, 0)` otherwise. -/
noncomputable def resWit (n p q : ℕ) : ℕ × ℤ × ℤ :=
  if h : Resonant n p q then (resonant_iff.mp h).choose else (0, 0, 0)

theorem resData_resWit {n p q : ℕ} (h : Resonant n p q) : ResData n p q (resWit n p q) := by
  rw [resWit, dif_pos h]
  exact (resonant_iff.mp h).choose_spec

/-- The five dyadic exponents of a pair: the modulus of its chosen resonance witness
together with `log₂` of `|k|`, `|ℓ|`, `p` and `q`. -/
noncomputable def resIdx (n : ℕ) (pq : ℕ × ℕ) : ℕ × ℕ × ℕ × ℕ × ℕ :=
  ((resWit n pq.1 pq.2).1, Nat.log 2 (resWit n pq.1 pq.2).2.1.natAbs,
    Nat.log 2 (resWit n pq.1 pq.2).2.2.natAbs, Nat.log 2 pq.1, Nat.log 2 pq.2)

/-- The admissible exponent tuples: `d ∈ D n` together with four exponents at most
`log₂ n`. -/
def idxBox (n : ℕ) : Finset (ℕ × ℕ × ℕ × ℕ × ℕ) :=
  D n ×ˢ range (Nat.log 2 n + 1) ×ˢ range (Nat.log 2 n + 1) ×ˢ
    range (Nat.log 2 n + 1) ×ˢ range (Nat.log 2 n + 1)

theorem mem_idxBox {n : ℕ} {y : ℕ × ℕ × ℕ × ℕ × ℕ} :
    y ∈ idxBox n ↔ y.1 ∈ D n ∧ y.2.1 ≤ Nat.log 2 n ∧ y.2.2.1 ≤ Nat.log 2 n ∧
      y.2.2.2.1 ≤ Nat.log 2 n ∧ y.2.2.2.2 ≤ Nat.log 2 n := by
  simp only [idxBox, mem_product, mem_range, Nat.lt_succ_iff]

theorem card_idxBox (n : ℕ) : #(idxBox n) = #(D n) * (Nat.log 2 n + 1) ^ 4 := by
  simp only [idxBox, card_product, card_range]
  ring

/-- The dyadic block of a positive natural, at the real level:
`2^(log₂ m) ≤ m < 2 · 2^(log₂ m)`. -/
theorem dyadic_bounds {m : ℕ} (hm : m ≠ 0) :
    (2 : ℝ) ^ Nat.log 2 m ≤ (m : ℝ) ∧ (m : ℝ) < 2 * (2 : ℝ) ^ Nat.log 2 m := by
  refine ⟨by exact_mod_cast Nat.pow_log_le_self 2 hm, ?_⟩
  have h : (m : ℝ) < ((2 ^ (Nat.log 2 m + 1) : ℕ) : ℝ) := by
    exact_mod_cast Nat.lt_pow_succ_log_self (by norm_num) m
  push_cast [pow_succ] at h
  linarith only [h]

/-- `dyadic_bounds` at the absolute value of a nonzero integer. -/
private theorem dyadic_bounds_abs {x : ℤ} (hx : x ≠ 0) :
    (2 : ℝ) ^ Nat.log 2 x.natAbs ≤ |(x : ℝ)| ∧
      |(x : ℝ)| < 2 * (2 : ℝ) ^ Nat.log 2 x.natAbs := by
  simpa only [Nat.cast_natAbs, Int.cast_abs] using dyadic_bounds (Int.natAbs_ne_zero.mpr hx)

/-- `2 ^ a ≤ n` for every exponent `a ≤ log₂ n`, at the real level. -/
theorem two_pow_le_of_le_log {n a : ℕ} (hn : n ≠ 0) (ha : a ≤ Nat.log 2 n) :
    (2 : ℝ) ^ a ≤ (n : ℝ) := by
  exact_mod_cast (Nat.pow_le_pow_right (by norm_num) ha).trans (Nat.pow_log_le_self 2 hn)

/-- Each fibre of `resIdx` injects into the quadruples of `quadSet`, by
`(p, q) ↦ (k, ℓ, p, q)` for the chosen witness `(d, k, ℓ)`. -/
theorem card_fiber_le_ncard_quadSet (n d a b c e : ℕ) :
    #(((H n).filter fun pq => Resonant n pq.1 pq.2).filter
        fun pq => resIdx n pq = (d, a, b, c, e))
      ≤ (quadSet d ((2 : ℝ) ^ a) ((2 : ℝ) ^ b) ((2 : ℝ) ^ c) ((2 : ℝ) ^ e)).ncard := by
  set G : Finset (ℕ × ℕ) := ((H n).filter fun pq => Resonant n pq.1 pq.2).filter
    fun pq => resIdx n pq = (d, a, b, c, e) with hGdef
  set g : ℕ × ℕ → ℤ × ℤ × ℤ × ℤ := fun pq =>
    ((resWit n pq.1 pq.2).2.1, (resWit n pq.1 pq.2).2.2, (pq.1 : ℤ), (pq.2 : ℤ)) with hgdef
  have hmem : ∀ pq ∈ G, g pq ∈ quadSet d ((2 : ℝ) ^ a) ((2 : ℝ) ^ b) ((2 : ℝ) ^ c)
      ((2 : ℝ) ^ e) := by
    intro pq hpq
    rw [hGdef, mem_filter, mem_filter, mem_H, mem_T] at hpq
    obtain ⟨⟨⟨⟨hp1, hq1, -⟩, -⟩, hres⟩, hidx⟩ := hpq
    obtain ⟨-, hbox, hne, -⟩ := resData_resWit hres
    simp only [resIdx, Prod.mk.injEq] at hidx
    obtain ⟨hd, ha, hb, hc, he⟩ := hidx
    obtain ⟨hk0, hl0⟩ := mul_ne_zero_iff.mp hne
    obtain ⟨hk1, hk2⟩ := dyadic_bounds_abs hk0
    obtain ⟨hl1, hl2⟩ := dyadic_bounds_abs hl0
    obtain ⟨hp1', hp2'⟩ := dyadic_bounds (show pq.1 ≠ 0 by omega)
    obtain ⟨hq1', hq2'⟩ := dyadic_bounds (show pq.2 ≠ 0 by omega)
    rw [ha] at hk1 hk2
    rw [hb] at hl1 hl2
    rw [hc] at hp1' hp2'
    rw [he] at hq1' hq2'
    have hdvd := mem_dualLattice.mp (mem_latticeBox.mp hbox).2
    rw [hd] at hdvd
    rw [hgdef]
    exact mem_quadSet.mpr ⟨⟨hk1, hk2⟩, ⟨hl1, hl2⟩,
      ⟨by push_cast; exact hp1', by push_cast; exact hp2'⟩,
      ⟨by push_cast; exact hq1', by push_cast; exact hq2'⟩, hdvd⟩
  have hinj : Set.InjOn g ↑G := by
    intro x _ y _ hxy
    rw [hgdef] at hxy
    simp only [Prod.mk.injEq, Nat.cast_inj] at hxy
    exact Prod.ext hxy.2.2.1 hxy.2.2.2
  calc #G = #(G.image g) := (card_image_of_injOn hinj).symm
    _ = (↑(G.image g) : Set (ℤ × ℤ × ℤ × ℤ)).ncard := (Set.ncard_coe_finset _).symm
    _ ≤ _ := Set.ncard_le_ncard (by rw [coe_image]; exact Set.image_subset_iff.mpr hmem)
        (quadSet_finite _ _ _ _ _ (by positivity) (by positivity))

/-- The witness inequality in dyadic form: for a resonant pair in the fibre of
`(d, a, b, c, e)`, `2^a 2^b 2^c 2^e ≤ d · (1000 Q(n) n²/φ(n))`. -/
theorem dyadic_prod_le {n : ℕ} (hn : 5 ≤ n) {d a b c e : ℕ} {pq : ℕ × ℕ}
    (hpq : pq ∈ ((H n).filter fun pq => Resonant n pq.1 pq.2).filter
      fun pq => resIdx n pq = (d, a, b, c, e)) :
    (2 : ℝ) ^ a * (2 : ℝ) ^ b * ((2 : ℝ) ^ c * (2 : ℝ) ^ e)
      ≤ (d : ℝ) * (1000 * Q n * (n : ℝ) ^ 2 / (n.totient : ℝ)) := by
  rw [mem_filter, mem_filter, mem_H, mem_T] at hpq
  obtain ⟨⟨⟨⟨hp1, hq1, -⟩, -⟩, hres⟩, hidx⟩ := hpq
  obtain ⟨-, -, hne, hle⟩ := resData_resWit hres
  simp only [resIdx, Prod.mk.injEq] at hidx
  obtain ⟨hd, ha, hb, hc, he⟩ := hidx
  rw [hd] at hle
  obtain ⟨hk0, hl0⟩ := mul_ne_zero_iff.mp hne
  have hφ0 : (0 : ℝ) < (n.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (show 0 < n by omega)
  have hk1 := (dyadic_bounds_abs hk0).1
  have hl1 := (dyadic_bounds_abs hl0).1
  have hp1' := (dyadic_bounds (show pq.1 ≠ 0 by omega)).1
  have hq1' := (dyadic_bounds (show pq.2 ≠ 0 by omega)).1
  rw [ha] at hk1
  rw [hb] at hl1
  rw [hc] at hp1'
  rw [he] at hq1'
  have habs : (2 : ℝ) ^ a * (2 : ℝ) ^ b
      ≤ |(((resWit n pq.1 pq.2).2.1 * (resWit n pq.1 pq.2).2.2 : ℤ) : ℝ)| := by
    push_cast [abs_mul]
    exact mul_le_mul hk1 hl1 (by positivity) (abs_nonneg _)
  have hY : (2 : ℝ) ^ c * (2 : ℝ) ^ e ≤ (h pq.1 : ℝ) * (h pq.2 : ℝ) :=
    mul_le_mul (hp1'.trans (by exact_mod_cast le_h hp1))
      (hq1'.trans (by exact_mod_cast le_h hq1)) (by positivity) (Nat.cast_nonneg _)
  have hMN : M n pq.1 pq.2 * (n : ℝ) ^ 2
      = (h pq.1 : ℝ) * (h pq.2 : ℝ) * (n.totient : ℝ) := by
    have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    unfold M
    field_simp
  rw [show (d : ℝ) * (1000 * Q n * (n : ℝ) ^ 2 / (n.totient : ℝ))
      = ((d : ℝ) * (1000 * Q n * (n : ℝ) ^ 2)) / (n.totient : ℝ) by ring,
    le_div_iff₀ hφ0]
  calc (2 : ℝ) ^ a * (2 : ℝ) ^ b * ((2 : ℝ) ^ c * (2 : ℝ) ^ e) * (n.totient : ℝ)
      = ((2 : ℝ) ^ a * (2 : ℝ) ^ b) * (((2 : ℝ) ^ c * (2 : ℝ) ^ e) * (n.totient : ℝ)) := by
        ring
    _ ≤ |(((resWit n pq.1 pq.2).2.1 * (resWit n pq.1 pq.2).2.2 : ℤ) : ℝ)|
          * ((h pq.1 : ℝ) * (h pq.2 : ℝ) * (n.totient : ℝ)) :=
        mul_le_mul habs (mul_le_mul_of_nonneg_right hY hφ0.le) (by positivity) (abs_nonneg _)
    _ = |(((resWit n pq.1 pq.2).2.1 * (resWit n pq.1 pq.2).2.2 : ℤ) : ℝ)|
          * M n pq.1 pq.2 * (n : ℝ) ^ 2 := by rw [← hMN]; ring
    _ ≤ (1000 * (d : ℝ) * Q n) * (n : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right hle (by positivity)
    _ = (d : ℝ) * (1000 * Q n * (n : ℝ) ^ 2) := by ring

/-- The per-index fibre bound: at a fixed exponent tuple the resonant pairs number at
most `C₄ (2B) n^(1+3δ)`, where `hquad` bounds the counts of `quadSet` at `δ` and `hW`
bounds `1000 Q(n) n²/φ(n)` by `B n^(1+2δ)`. -/
theorem card_fiber_le {n : ℕ} (hn : 5 ≤ n) {δ B C₄ : ℝ} (hB1 : 1 ≤ B) (hC₄0 : 0 < C₄)
    (hW : 1000 * Q n * (n : ℝ) ^ 2 / (n.totient : ℝ) ≤ B * (n : ℝ) ^ (1 + 2 * δ))
    (hδ0 : 0 < δ)
    (hquad : ∀ d : ℕ, 1 ≤ d → d ∣ n → ∀ K L P R : ℝ, 1 ≤ K → 1 ≤ L → 1 ≤ P → 1 ≤ R →
      K * P ≤ (n : ℝ) ^ 2 → L * R ≤ (n : ℝ) ^ 2 →
      ((quadSet d K L P R).ncard : ℝ)
        ≤ C₄ * (n : ℝ) ^ δ * (K * L * P * R / (d : ℝ) + min (K * P) (L * R)))
    {y : ℕ × ℕ × ℕ × ℕ × ℕ} (hy : y ∈ idxBox n) :
    (#(((H n).filter fun pq => Resonant n pq.1 pq.2).filter fun pq => resIdx n pq = y) : ℝ)
      ≤ C₄ * (2 * B) * (n : ℝ) ^ (1 + 3 * δ) := by
  obtain ⟨d, a, b, c, e⟩ := y
  rw [mem_idxBox] at hy
  obtain ⟨hdD, ha, hb, hc, he⟩ := hy
  have hn0 : n ≠ 0 := by omega
  have hnR1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hnR0 : (0 : ℝ) < (n : ℝ) := by linarith only [hnR1]
  have hB0 : (0 : ℝ) < B := lt_of_lt_of_le one_pos hB1
  have hX0 : (0 : ℝ) < B * (n : ℝ) ^ (1 + 2 * δ) :=
    mul_pos hB0 (Real.rpow_pos_of_pos hnR0 _)
  have hRHS0 : (0 : ℝ) ≤ C₄ * (2 * B) * (n : ℝ) ^ (1 + 3 * δ) :=
    (mul_pos (mul_pos hC₄0 (by linarith only [hB0])) (Real.rpow_pos_of_pos hnR0 _)).le
  have hdvd : d ∣ n := dvd_of_mem_D hdD
  have hd1 : 1 ≤ d := Nat.pos_of_mem_divisors (D_subset_divisors n hdD)
  have hdR0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
  have hdn : (d : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.le_of_dvd (by omega) hdvd
  have hKa : (1 : ℝ) ≤ (2 : ℝ) ^ a := one_le_pow₀ (by norm_num)
  have hKb : (1 : ℝ) ≤ (2 : ℝ) ^ b := one_le_pow₀ (by norm_num)
  have hKc : (1 : ℝ) ≤ (2 : ℝ) ^ c := one_le_pow₀ (by norm_num)
  have hKe : (1 : ℝ) ≤ (2 : ℝ) ^ e := one_le_pow₀ (by norm_num)
  have hsq : ∀ u v : ℕ, u ≤ Nat.log 2 n → v ≤ Nat.log 2 n →
      (2 : ℝ) ^ u * (2 : ℝ) ^ v ≤ (n : ℝ) ^ 2 := fun u v hu hv => by
    rw [pow_two]
    exact mul_le_mul (two_pow_le_of_le_log hn0 hu) (two_pow_le_of_le_log hn0 hv)
      (by positivity) hnR0.le
  rcases Finset.eq_empty_or_nonempty
    ((((H n).filter fun pq => Resonant n pq.1 pq.2).filter
      fun pq => resIdx n pq = (d, a, b, c, e))) with hemp | ⟨pq0, hpq0⟩
  · rw [hemp, Finset.card_empty, Nat.cast_zero]
    exact hRHS0
  have hprod : (2 : ℝ) ^ a * (2 : ℝ) ^ b * (2 : ℝ) ^ c * (2 : ℝ) ^ e
      ≤ (d : ℝ) * (B * (n : ℝ) ^ (1 + 2 * δ)) := by
    calc (2 : ℝ) ^ a * (2 : ℝ) ^ b * (2 : ℝ) ^ c * (2 : ℝ) ^ e
        = (2 : ℝ) ^ a * (2 : ℝ) ^ b * ((2 : ℝ) ^ c * (2 : ℝ) ^ e) := by ring
      _ ≤ (d : ℝ) * (1000 * Q n * (n : ℝ) ^ 2 / (n.totient : ℝ)) := dyadic_prod_le hn hpq0
      _ ≤ (d : ℝ) * (B * (n : ℝ) ^ (1 + 2 * δ)) := mul_le_mul_of_nonneg_left hW hdR0.le
  have hfirst : (2 : ℝ) ^ a * (2 : ℝ) ^ b * (2 : ℝ) ^ c * (2 : ℝ) ^ e / (d : ℝ)
      ≤ B * (n : ℝ) ^ (1 + 2 * δ) := (div_le_iff₀ hdR0).mpr (by linarith only [hprod])
  have hsecond : min ((2 : ℝ) ^ a * (2 : ℝ) ^ c) ((2 : ℝ) ^ b * (2 : ℝ) ^ e)
      ≤ B * (n : ℝ) ^ (1 + 2 * δ) := by
    have hnle : (n : ℝ) ≤ (n : ℝ) ^ (1 + 2 * δ) := by
      simpa using Real.rpow_le_rpow_of_exponent_le hnR1
        (by linarith only [hδ0] : (1 : ℝ) ≤ 1 + 2 * δ)
    have hsquare : ((2 : ℝ) ^ a * (2 : ℝ) ^ c) * ((2 : ℝ) ^ b * (2 : ℝ) ^ e)
        ≤ (B * (n : ℝ) ^ (1 + 2 * δ)) * (B * (n : ℝ) ^ (1 + 2 * δ)) :=
      calc ((2 : ℝ) ^ a * (2 : ℝ) ^ c) * ((2 : ℝ) ^ b * (2 : ℝ) ^ e)
          = (2 : ℝ) ^ a * (2 : ℝ) ^ b * (2 : ℝ) ^ c * (2 : ℝ) ^ e := by ring
        _ ≤ (d : ℝ) * (B * (n : ℝ) ^ (1 + 2 * δ)) := hprod
        _ ≤ (n : ℝ) ^ (1 + 2 * δ) * (B * (n : ℝ) ^ (1 + 2 * δ)) :=
            mul_le_mul_of_nonneg_right (hdn.trans hnle) hX0.le
        _ ≤ (B * (n : ℝ) ^ (1 + 2 * δ)) * (B * (n : ℝ) ^ (1 + 2 * δ)) :=
            mul_le_mul_of_nonneg_right
              (le_mul_of_one_le_left (Real.rpow_pos_of_pos hnR0 _).le hB1) hX0.le
    refine nonneg_le_nonneg_of_sq_le_sq hX0.le (le_trans ?_ hsquare)
    exact mul_le_mul (min_le_left _ _) (min_le_right _ _)
      (le_min (by positivity) (by positivity)) (by positivity)
  have hmerge : (n : ℝ) ^ δ * (n : ℝ) ^ (1 + 2 * δ) = (n : ℝ) ^ (1 + 3 * δ) := by
    rw [← Real.rpow_add hnR0]; ring_nf
  calc (#(((H n).filter fun pq => Resonant n pq.1 pq.2).filter
        fun pq => resIdx n pq = (d, a, b, c, e)) : ℝ)
      ≤ ((quadSet d ((2 : ℝ) ^ a) ((2 : ℝ) ^ b) ((2 : ℝ) ^ c) ((2 : ℝ) ^ e)).ncard : ℝ) := by
        exact_mod_cast card_fiber_le_ncard_quadSet n d a b c e
    _ ≤ C₄ * (n : ℝ) ^ δ * ((2 : ℝ) ^ a * (2 : ℝ) ^ b * (2 : ℝ) ^ c * (2 : ℝ) ^ e / (d : ℝ)
          + min ((2 : ℝ) ^ a * (2 : ℝ) ^ c) ((2 : ℝ) ^ b * (2 : ℝ) ^ e)) :=
        hquad d hd1 hdvd _ _ _ _ hKa hKb hKc hKe (hsq a c ha hc) (hsq b e hb he)
    _ ≤ C₄ * (n : ℝ) ^ δ * (2 * B * (n : ℝ) ^ (1 + 2 * δ)) :=
        mul_le_mul_of_nonneg_left (by linarith only [hfirst, hsecond])
          (mul_pos hC₄0 (Real.rpow_pos_of_pos hnR0 δ)).le
    _ = C₄ * (2 * B) * ((n : ℝ) ^ δ * (n : ℝ) ^ (1 + 2 * δ)) := by ring
    _ = C₄ * (2 * B) * (n : ℝ) ^ (1 + 3 * δ) := by rw [hmerge]

/-- `log₂ n + 1 ≤ (1 + 1/log 2)(1 + log n)`. -/
theorem log_two_succ_le {n : ℕ} (hn : n ≠ 0) :
    ((Nat.log 2 n : ℕ) : ℝ) + 1 ≤ (1 + 1 / Real.log 2) * (1 + Real.log n) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h1 : ((Nat.log 2 n : ℕ) : ℝ) * Real.log 2 ≤ Real.log n := by
    have h := Real.log_le_log (by positivity) (two_pow_le_of_le_log hn le_rfl)
    rwa [Real.log_pow] at h
  have h2 : (0 : ℝ) ≤ Real.log n := Real.log_natCast_nonneg n
  refine le_of_mul_le_mul_right ?_ hlog2
  rw [show (1 + 1 / Real.log 2) * (1 + Real.log n) * Real.log 2
      = Real.log 2 * (1 + Real.log n) + (1 + Real.log n) by field_simp]
  nlinarith only [h1, h2, hlog2, mul_nonneg hlog2.le h2]

/-- For every `ε > 0` there is `C > 0` such that the pairs of `H n` that are resonant for
`n` number at most `C n^(1+ε)`, for every `n ≥ 5`.

The constant is `C₃ (κ(1 + 1/δ))^4 C₄ (2 max 1 (1000 C₁ c₁))` with `δ = ε/8`,
`κ = 1 + 1/log 2`, and `C₁, c₁, C₃, C₄` the constants of `Q_small`, `totient_lower`,
`divisor_bound` and `quadcount` at `δ`. -/
theorem card_resonant_le {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 5 ≤ n →
      (((H n).filter fun pq => Resonant n pq.1 pq.2).card : ℝ)
        ≤ C * (n : ℝ) ^ (1 + ε) := by
  set δ : ℝ := ε / 8 with hδdef
  have hδ0 : 0 < δ := by rw [hδdef]; linarith only [hε]
  obtain ⟨C₁, hC₁0, hC₁⟩ := Q_small hδ0
  obtain ⟨c₁, hc₁0, hc₁⟩ := totient_lower hδ0
  obtain ⟨C₃, hC₃0, hC₃⟩ := divisor_bound hδ0
  obtain ⟨C₄, hC₄0, hC₄⟩ := quadcount hδ0
  set B : ℝ := max 1 (1000 * C₁ * c₁)
  have hB1 : (1 : ℝ) ≤ B := le_max_left _ _
  have hBc : 1000 * C₁ * c₁ ≤ B := le_max_right _ _
  set κ : ℝ := 1 + 1 / Real.log 2 with hκdef
  have hκ0 : (0 : ℝ) < κ := by rw [hκdef]; positivity
  have hinvδ : (0 : ℝ) < 1 / δ := by positivity
  have hCδ : (0 : ℝ) < κ * (1 + 1 / δ) := mul_pos hκ0 (by linarith only [hinvδ])
  refine ⟨C₃ * (κ * (1 + 1 / δ)) ^ 4 * (C₄ * (2 * B)),
    mul_pos (mul_pos hC₃0 (pow_pos hCδ 4))
      (mul_pos hC₄0 (by linarith only [hB1])), fun n hn => ?_⟩
  have hn0 : n ≠ 0 := by omega
  have hnR1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hnR0 : (0 : ℝ) < (n : ℝ) := by linarith only [hnR1]
  have hφ0 : (0 : ℝ) < (n.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (show 0 < n by omega)
  set S : Finset (ℕ × ℕ) := (H n).filter fun pq => Resonant n pq.1 pq.2 with hSdef
  have hmaps : ∀ pq ∈ S, resIdx n pq ∈ idxBox n := by
    intro pq hpq
    rw [hSdef, mem_filter, mem_H, mem_T] at hpq
    obtain ⟨⟨⟨-, -, hlt⟩, -⟩, hres⟩ := hpq
    obtain ⟨hdD, hbox, -, -⟩ := resData_resWit hres
    have hdle : (resWit n pq.1 pq.2).1 ≤ n := Nat.le_of_dvd (by omega) (dvd_of_mem_D hdD)
    have hFle : ∀ j : ℤ, j ∈ F (resWit n pq.1 pq.2).1 → j.natAbs ≤ n := by
      intro j hj
      have h1 : 2 * (j.natAbs : ℤ) ≤ ((resWit n pq.1 pq.2).1 : ℤ) := by
        rw [← Int.abs_eq_natAbs]; exact two_mul_abs_le_of_mem_F hj
      have h2 : 2 * j.natAbs ≤ (resWit n pq.1 pq.2).1 := by exact_mod_cast h1
      omega
    rw [mem_idxBox]
    simp only [resIdx]
    exact ⟨hdD, Nat.log_mono_right (hFle _ (mem_latticeBox.mp hbox).1.1),
      Nat.log_mono_right (hFle _ (mem_latticeBox.mp hbox).1.2),
      Nat.log_mono_right (by omega), Nat.log_mono_right (by omega)⟩
  have hcard : (S.card : ℝ)
      = ∑ y ∈ idxBox n, (#(S.filter fun pq => resIdx n pq = y) : ℝ) := by
    rw [Finset.card_eq_sum_card_fiberwise hmaps, Nat.cast_sum]
  have hW : 1000 * Q n * (n : ℝ) ^ 2 / (n.totient : ℝ) ≤ B * (n : ℝ) ^ (1 + 2 * δ) := by
    have hQ0 : (0 : ℝ) < Q n := Q_pos n
    have hn2δ : (n : ℝ) ^ δ * (n : ℝ) ^ (1 + δ) = (n : ℝ) ^ (1 + 2 * δ) := by
      rw [← Real.rpow_add hnR0]; ring_nf
    rw [div_le_iff₀ hφ0]
    calc 1000 * Q n * (n : ℝ) ^ 2
        ≤ 1000 * Q n * (c₁ * (n : ℝ) ^ (1 + δ) * (n.totient : ℝ)) :=
          mul_le_mul_of_nonneg_left (hc₁ n (by omega)) (by linarith only [hQ0])
      _ ≤ 1000 * (C₁ * (n : ℝ) ^ δ) * (c₁ * (n : ℝ) ^ (1 + δ) * (n.totient : ℝ)) :=
          mul_le_mul_of_nonneg_right (by linarith only [hC₁ n (by omega : 2 ≤ n)])
            (mul_nonneg (mul_nonneg hc₁0.le (Real.rpow_pos_of_pos hnR0 _).le) hφ0.le)
      _ = (1000 * C₁ * c₁) * ((n : ℝ) ^ δ * (n : ℝ) ^ (1 + δ)) * (n.totient : ℝ) := by ring
      _ = (1000 * C₁ * c₁) * (n : ℝ) ^ (1 + 2 * δ) * (n.totient : ℝ) := by rw [hn2δ]
      _ ≤ B * (n : ℝ) ^ (1 + 2 * δ) * (n.totient : ℝ) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hBc (Real.rpow_pos_of_pos hnR0 _).le) hφ0.le
  have hfib : ∀ y ∈ idxBox n, (#(S.filter fun pq => resIdx n pq = y) : ℝ)
      ≤ C₄ * (2 * B) * (n : ℝ) ^ (1 + 3 * δ) := fun y hy => by
    rw [hSdef]
    exact card_fiber_le hn hB1 hC₄0 hW hδ0
      (fun d hd1 hdvd => hC₄ n d (by omega) hd1 hdvd) hy
  have hbox : (#(idxBox n) : ℝ) ≤ C₃ * (κ * (1 + 1 / δ)) ^ 4 * (n : ℝ) ^ (5 * δ) := by
    have hτ : (#(D n) : ℝ) ≤ C₃ * (n : ℝ) ^ δ :=
      le_trans (by exact_mod_cast card_le_card (D_subset_divisors n)) (hC₃ n (by omega))
    have hlogpow : ((Nat.log 2 n + 1 : ℕ) : ℝ) ^ 4
        ≤ (κ * (1 + 1 / δ)) ^ 4 * (n : ℝ) ^ (4 * δ) := by
      have h1 : ((Nat.log 2 n + 1 : ℕ) : ℝ) ≤ κ * ((1 + 1 / δ) * (n : ℝ) ^ δ) := by
        have h2 : κ * (1 + Real.log n) ≤ κ * ((1 + 1 / δ) * (n : ℝ) ^ δ) :=
          mul_le_mul_of_nonneg_left (one_add_log_le_rpow hδ0 hnR1) hκ0.le
        have h3 := log_two_succ_le hn0
        rw [← hκdef] at h3
        push_cast
        linarith only [h2, h3]
      have h4 : ((n : ℝ) ^ δ) ^ (4 : ℕ) = (n : ℝ) ^ (4 * δ) := by
        rw [← Real.rpow_natCast ((n : ℝ) ^ δ) 4, ← Real.rpow_mul hnR0.le,
          show δ * ((4 : ℕ) : ℝ) = 4 * δ by push_cast; ring]
      calc ((Nat.log 2 n + 1 : ℕ) : ℝ) ^ 4
          ≤ (κ * ((1 + 1 / δ) * (n : ℝ) ^ δ)) ^ 4 := pow_le_pow_left₀ (by positivity) h1 4
        _ = (κ * (1 + 1 / δ)) ^ 4 * ((n : ℝ) ^ δ) ^ (4 : ℕ) := by ring
        _ = (κ * (1 + 1 / δ)) ^ 4 * (n : ℝ) ^ (4 * δ) := by rw [h4]
    have hmerge : (n : ℝ) ^ δ * (n : ℝ) ^ (4 * δ) = (n : ℝ) ^ (5 * δ) := by
      rw [← Real.rpow_add hnR0]; ring_nf
    calc (#(idxBox n) : ℝ) = (#(D n) : ℝ) * ((Nat.log 2 n + 1 : ℕ) : ℝ) ^ 4 := by
          rw [card_idxBox]; push_cast; ring
      _ ≤ (C₃ * (n : ℝ) ^ δ) * ((κ * (1 + 1 / δ)) ^ 4 * (n : ℝ) ^ (4 * δ)) :=
          mul_le_mul hτ hlogpow (by positivity)
            (mul_pos hC₃0 (Real.rpow_pos_of_pos hnR0 _)).le
      _ = C₃ * (κ * (1 + 1 / δ)) ^ 4 * ((n : ℝ) ^ δ * (n : ℝ) ^ (4 * δ)) := by ring
      _ = C₃ * (κ * (1 + 1 / δ)) ^ 4 * (n : ℝ) ^ (5 * δ) := by rw [hmerge]
  have hRHS0 : (0 : ℝ) ≤ C₄ * (2 * B) * (n : ℝ) ^ (1 + 3 * δ) :=
    (mul_pos (mul_pos hC₄0 (by linarith only [hB1])) (Real.rpow_pos_of_pos hnR0 _)).le
  have hfinal : (n : ℝ) ^ (5 * δ) * (n : ℝ) ^ (1 + 3 * δ) = (n : ℝ) ^ (1 + ε) := by
    rw [← Real.rpow_add hnR0, hδdef]; ring_nf
  calc (S.card : ℝ) = ∑ y ∈ idxBox n, (#(S.filter fun pq => resIdx n pq = y) : ℝ) := hcard
    _ ≤ ∑ _y ∈ idxBox n, C₄ * (2 * B) * (n : ℝ) ^ (1 + 3 * δ) := Finset.sum_le_sum hfib
    _ = (#(idxBox n) : ℝ) * (C₄ * (2 * B) * (n : ℝ) ^ (1 + 3 * δ)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (C₃ * (κ * (1 + 1 / δ)) ^ 4 * (n : ℝ) ^ (5 * δ))
          * (C₄ * (2 * B) * (n : ℝ) ^ (1 + 3 * δ)) := mul_le_mul_of_nonneg_right hbox hRHS0
    _ = C₃ * (κ * (1 + 1 / δ)) ^ 4 * (C₄ * (2 * B))
          * ((n : ℝ) ^ (5 * δ) * (n : ℝ) ^ (1 + 3 * δ)) := by ring
    _ = C₃ * (κ * (1 + 1 / δ)) ^ 4 * (C₄ * (2 * B)) * (n : ℝ) ^ (1 + ε) := by rw [hfinal]

end Paucity
