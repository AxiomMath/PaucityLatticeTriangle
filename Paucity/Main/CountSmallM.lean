/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Paucity.Defs.Hn
public import Paucity.Defs.M
public import Paucity.Defs.Q
public import Paucity.Estimates.Hyperbola
public import Paucity.Estimates.QSmall
public import Paucity.Estimates.TotientLower

/-!
# Pairs with small expectation are few

For every `ε > 0`, the pairs `(p, q) ∈ H n` whose expected witness count `M n p q` falls
below `1000 * Q n` number at most `C(ε) n^(1+ε)`, with `C` depending only on `ε`. Such a
pair satisfies `p q ≤ X` for a threshold `X = K n^(1+2δ)`, so it lies in a hyperbola
region whose points are counted by `hyperbola_card_le`.

## Main definitions

* `hyperBox`: the pairs `(a, b)` of positive naturals with `a b ≤ ⌊X⌋₊`.

## Main results

* `one_add_log_le_rpow`: `1 + log X ≤ (1 + 1/δ) X^δ` for `X ≥ 1` and `δ > 0`.
* `mem_hyperBox`: membership in `hyperBox X`, at the real threshold `X`.
* `card_hyperBox_le`: `#(hyperBox X) ≤ (1 + 1/δ) X^(1+δ)`.
* `exists_bound_of_le_thousand_Q`: a constant `K ≥ 1` with `x ≤ K n^(1+2δ)` for every
  `x ≥ 0` satisfying `x φ(n) / n² ≤ 1000 Q n`.
* `card_smallM_le`: for every `ε > 0` there is `C > 0` bounding the number of pairs of
  `H n` with `M n p q < 1000 Q n` by `C n^(1+ε)`, for every `n ≥ 5`.
-/

@[expose] public section

namespace Paucity

open Finset

/-- `1 + log X ≤ (1 + 1/δ) X^δ` for every `X ≥ 1` and `δ > 0`. -/
theorem one_add_log_le_rpow {δ X : ℝ} (hδ : 0 < δ) (hX : 1 ≤ X) :
    1 + Real.log X ≤ (1 + 1 / δ) * X ^ δ := by
  have h1 : (1 : ℝ) ≤ X ^ δ := Real.one_le_rpow hX hδ.le
  have h2 : Real.log X ≤ X ^ δ / δ := log_le_rpow_div hX hδ
  have h3 : (1 + 1 / δ) * X ^ δ = X ^ δ + X ^ δ / δ := by field_simp
  rw [h3]
  linarith

/-- `hyperBox X`: the pairs `(a, b)` of positive naturals with `a b ≤ ⌊X⌋₊`. -/
noncomputable def hyperBox (X : ℝ) : Finset (ℕ × ℕ) :=
  ((Icc 1 ⌊X⌋₊) ×ˢ (Icc 1 ⌊X⌋₊)).filter fun ab => ab.1 * ab.2 ≤ ⌊X⌋₊

/-- `(a, b) ∈ hyperBox X` as soon as `1 ≤ a`, `1 ≤ b` and `a b ≤ X`. -/
theorem mem_hyperBox {X : ℝ} {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hab : (a : ℝ) * (b : ℝ) ≤ X) : (a, b) ∈ hyperBox X := by
  have hfloor : a * b ≤ ⌊X⌋₊ := Nat.le_floor (by push_cast; exact hab)
  have haN : a ≤ ⌊X⌋₊ := le_trans (Nat.le_mul_of_pos_right a hb) hfloor
  have hbN : b ≤ ⌊X⌋₊ := le_trans (Nat.le_mul_of_pos_left b ha) hfloor
  simp only [hyperBox, mem_filter, mem_product, mem_Icc]
  exact ⟨⟨⟨ha, haN⟩, hb, hbN⟩, hfloor⟩

/-- `#(hyperBox X) ≤ (1 + 1/δ) X^(1+δ)` for every `X ≥ 1` and `δ > 0`. -/
theorem card_hyperBox_le {δ X : ℝ} (hδ : 0 < δ) (hX : 1 ≤ X) :
    ((hyperBox X).card : ℝ) ≤ (1 + 1 / δ) * X ^ (1 + δ) := by
  have hN1 : 1 ≤ ⌊X⌋₊ := Nat.le_floor (by exact_mod_cast hX)
  have hNX : ((⌊X⌋₊ : ℕ) : ℝ) ≤ X := Nat.floor_le (by linarith)
  have hlogN : Real.log (⌊X⌋₊ : ℕ) ≤ Real.log X :=
    Real.log_le_log (by exact_mod_cast hN1) hNX
  have hlogNnn : 0 ≤ Real.log ((⌊X⌋₊ : ℕ) : ℝ) := Real.log_nonneg (by exact_mod_cast hN1)
  have h1 : ((hyperBox X).card : ℝ) ≤ ((⌊X⌋₊ : ℕ) : ℝ) * (1 + Real.log (⌊X⌋₊ : ℕ)) :=
    hyperbola_card_le _
  have h2 : ((⌊X⌋₊ : ℕ) : ℝ) * (1 + Real.log (⌊X⌋₊ : ℕ)) ≤ X * (1 + Real.log X) :=
    mul_le_mul hNX (by linarith) (by linarith) (by linarith)
  have h3 : 1 + Real.log X ≤ (1 + 1 / δ) * X ^ δ := one_add_log_le_rpow hδ hX
  have h4 : X * (1 + Real.log X) ≤ X * ((1 + 1 / δ) * X ^ δ) :=
    mul_le_mul_of_nonneg_left h3 (by linarith)
  have h5 : X * ((1 + 1 / δ) * X ^ δ) = (1 + 1 / δ) * X ^ (1 + δ) := by
    rw [Real.rpow_add (by linarith) 1 δ, Real.rpow_one]; ring
  linarith

/-- For `δ > 0` there is `K ≥ 1` such that, for every `n ≥ 5`, every `x ≥ 0` with
`x φ(n) / n² ≤ 1000 Q n` satisfies `x ≤ K n^(1+2δ)`. -/
theorem exists_bound_of_le_thousand_Q {δ : ℝ} (hδ : 0 < δ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ n : ℕ, 5 ≤ n → ∀ x : ℝ, 0 ≤ x →
      x * (n.totient : ℝ) / (n : ℝ) ^ 2 ≤ 1000 * Q n → x ≤ K * (n : ℝ) ^ (1 + 2 * δ) := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := Q_small hδ
  obtain ⟨c₁, hc₁0, hc₁⟩ := totient_lower hδ
  refine ⟨max 1 (1000 * C₁ * c₁), le_max_left _ _, fun n hn x hx hxle => ?_⟩
  have hnR : (0 : ℝ) < (n : ℝ) := by positivity
  have hphi : (0 : ℝ) < (n.totient : ℝ) := by
    have := Nat.totient_pos.mpr (show 0 < n by omega)
    exact_mod_cast this
  have hQ : Q n ≤ C₁ * (n : ℝ) ^ δ := hC₁ n (by omega)
  have hQ0 : 0 < Q n := Q_pos n
  have htot : (n : ℝ) ^ 2 ≤ c₁ * (n : ℝ) ^ (1 + δ) * (n.totient : ℝ) := hc₁ n (by omega)
  have step1 : x * (n.totient : ℝ) ≤ 1000 * Q n * (n : ℝ) ^ 2 := by
    rw [div_le_iff₀ (by positivity)] at hxle
    linarith
  have step2 : 1000 * Q n * (n : ℝ) ^ 2
      ≤ 1000 * Q n * (c₁ * (n : ℝ) ^ (1 + δ)) * (n.totient : ℝ) := by
    have h := mul_le_mul_of_nonneg_left htot (by positivity : (0 : ℝ) ≤ 1000 * Q n)
    calc 1000 * Q n * (n : ℝ) ^ 2 = 1000 * Q n * ((n : ℝ) ^ 2) := by ring
      _ ≤ 1000 * Q n * (c₁ * (n : ℝ) ^ (1 + δ) * (n.totient : ℝ)) := h
      _ = 1000 * Q n * (c₁ * (n : ℝ) ^ (1 + δ)) * (n.totient : ℝ) := by ring
  have step3 : x ≤ 1000 * Q n * (c₁ * (n : ℝ) ^ (1 + δ)) :=
    le_of_mul_le_mul_right (by linarith) hphi
  have step4 : 1000 * Q n * (c₁ * (n : ℝ) ^ (1 + δ))
      ≤ 1000 * C₁ * c₁ * (n : ℝ) ^ (1 + 2 * δ) := by
    have hsplit : (n : ℝ) ^ (1 + 2 * δ) = (n : ℝ) ^ δ * (n : ℝ) ^ (1 + δ) := by
      rw [← Real.rpow_add hnR]; ring_nf
    have hmul : 1000 * Q n * (c₁ * (n : ℝ) ^ (1 + δ))
        ≤ 1000 * (C₁ * (n : ℝ) ^ δ) * (c₁ * (n : ℝ) ^ (1 + δ)) := by
      have hnn : (0 : ℝ) ≤ c₁ * (n : ℝ) ^ (1 + δ) := by positivity
      have h := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hQ (by norm_num : (0 : ℝ) ≤ 1000)) hnn
      linarith
    rw [hsplit]
    calc 1000 * Q n * (c₁ * (n : ℝ) ^ (1 + δ))
        ≤ 1000 * (C₁ * (n : ℝ) ^ δ) * (c₁ * (n : ℝ) ^ (1 + δ)) := hmul
      _ = 1000 * C₁ * c₁ * ((n : ℝ) ^ δ * (n : ℝ) ^ (1 + δ)) := by ring
  have step5 : 1000 * C₁ * c₁ * (n : ℝ) ^ (1 + 2 * δ)
      ≤ max 1 (1000 * C₁ * c₁) * (n : ℝ) ^ (1 + 2 * δ) :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  linarith

/-- For every `ε > 0` there is `C > 0` such that the pairs of `H n` with
`M n p q < 1000 Q n` number at most `C n^(1+ε)`, for every `n ≥ 5`.

The constant is `(1 + 1/δ) K^(1+δ)`, where `δ = min (ε/4) (1/4)` and `K` is the constant
of `exists_bound_of_le_thousand_Q` at `δ`. -/
theorem card_smallM_le {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 5 ≤ n →
      (((H n).filter fun pq => M n pq.1 pq.2 < 1000 * Q n).card : ℝ)
        ≤ C * (n : ℝ) ^ (1 + ε) := by
  set δ : ℝ := min (ε / 4) (1 / 4) with hδdef
  have hδ0 : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδ4 : δ ≤ 1 / 4 := min_le_right _ _
  have hδε : 4 * δ ≤ ε := by
    have : δ ≤ ε / 4 := min_le_left _ _
    linarith
  obtain ⟨K, hK1, hK⟩ := exists_bound_of_le_thousand_Q hδ0
  have hK0 : (0 : ℝ) < K := lt_of_lt_of_le one_pos hK1
  have hinv : (0 : ℝ) < 1 / δ := one_div_pos.mpr hδ0
  have hC2pos : (0 : ℝ) < 1 + 1 / δ := by linarith
  refine ⟨(1 + 1 / δ) * K ^ (1 + δ), mul_pos hC2pos (Real.rpow_pos_of_pos hK0 _), fun n hn => ?_⟩
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  set X : ℝ := K * (n : ℝ) ^ (1 + 2 * δ) with hXdef
  have hnrpow : (1 : ℝ) ≤ (n : ℝ) ^ (1 + 2 * δ) := Real.one_le_rpow hn1 (by linarith)
  have hX1 : (1 : ℝ) ≤ X := by
    have h : (1 : ℝ) * 1 ≤ K * (n : ℝ) ^ (1 + 2 * δ) :=
      mul_le_mul hK1 hnrpow (by norm_num) (by linarith)
    rw [hXdef]; linarith
  have hsub : ((H n).filter fun pq => M n pq.1 pq.2 < 1000 * Q n) ⊆ hyperBox X := by
    intro pq hpq
    rw [mem_filter, mem_H, mem_T] at hpq
    obtain ⟨⟨⟨hp1, hq1, -⟩, -⟩, hM⟩ := hpq
    have hxle : (h pq.1 : ℝ) * (h pq.2 : ℝ) * (n.totient : ℝ) / (n : ℝ) ^ 2 ≤ 1000 * Q n :=
      hM.le
    have hbound : (h pq.1 : ℝ) * (h pq.2 : ℝ) ≤ X := hK n hn _ (by positivity) hxle
    have h1 : (pq.1 : ℝ) ≤ (h pq.1 : ℝ) := by exact_mod_cast le_h hp1
    have h2 : (pq.2 : ℝ) ≤ (h pq.2 : ℝ) := by exact_mod_cast le_h hq1
    have h3 : (pq.1 : ℝ) * (pq.2 : ℝ) ≤ (h pq.1 : ℝ) * (h pq.2 : ℝ) :=
      mul_le_mul h1 h2 (by positivity) (by positivity)
    simpa using mem_hyperBox hp1 hq1 (le_trans h3 hbound)
  have hexp : (1 + 2 * δ) * (1 + δ) ≤ 1 + ε := by
    nlinarith [mul_le_mul_of_nonneg_left hδ4 hδ0.le]
  calc (((H n).filter fun pq => M n pq.1 pq.2 < 1000 * Q n).card : ℝ)
      ≤ ((hyperBox X).card : ℝ) := Nat.cast_le.mpr (Finset.card_le_card hsub)
    _ ≤ (1 + 1 / δ) * X ^ (1 + δ) := card_hyperBox_le hδ0 hX1
    _ = (1 + 1 / δ) * (K ^ (1 + δ) * (n : ℝ) ^ ((1 + 2 * δ) * (1 + δ))) := by
        rw [hXdef, Real.mul_rpow hK0.le (by positivity), ← Real.rpow_mul (Nat.cast_nonneg n)]
    _ ≤ (1 + 1 / δ) * (K ^ (1 + δ) * (n : ℝ) ^ (1 + ε)) := by
        refine mul_le_mul_of_nonneg_left ?_ hC2pos.le
        refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_pos_of_pos hK0 _).le
        exact Real.rpow_le_rpow_of_exponent_le hn1 hexp
    _ = (1 + 1 / δ) * K ^ (1 + δ) * (n : ℝ) ^ (1 + ε) := by ring

end Paucity
