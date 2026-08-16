/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Interval.Finset.Defs
public import Paucity.Estimates.DivisorBound

/-!
# Counting resonant quadruples

For every `ε > 0` there is `C(ε) > 0` such that, for all integers `n, d ≥ 1` with `d ∣ n` and all
reals `K, L, P, Q ≥ 1` with `KP ≤ n²` and `LQ ≤ n²`, the quadruples `(k, ℓ, p, q) ∈ ℤ⁴` with
`K ≤ |k| < 2K`, `L ≤ |ℓ| < 2L`, `P ≤ p < 2P`, `Q ≤ q < 2Q` and `kp + ℓq ≡ 0 (mod d)` number at most
`C(ε) nᵋ (KLPQ/d + min (KP) (LQ))`.

## Main definitions

* `quadSet`: the set of quadruples being counted.
* `quadIdx`: the index `(ℓ, q, (kp + ℓq)/d)` of the fibre a quadruple lies in.

## Main results

* `mem_quadSet`: membership in `quadSet`, on an explicit quadruple.
* `quadSet_finite`: `quadSet d K L P Q` is finite.
* `quadFiber_card_le_divisors`: a fibre of `quadIdx` over `(ℓ, q, m)` has at most as many elements
  as `m d - ℓ q` has divisors.
* `quadSet_ncard_le_of_le`: the count under the extra hypothesis `LQ ≤ KP`.
* `quadSet_ncard_swap`: transposing `(k, p)` with `(ℓ, q)` preserves the count.
* `quadcount`: the count above.
-/

@[expose] public section

namespace Paucity

open Finset

/-- `quadSet d K L P Q` is the set of quadruples `(k, ℓ, p, q) ∈ ℤ⁴` with `K ≤ |k| < 2K`,
`L ≤ |ℓ| < 2L`, `P ≤ p < 2P`, `Q ≤ q < 2Q` and `kp + ℓq ≡ 0 (mod d)`. -/
def quadSet (d : ℕ) (K L P Q : ℝ) : Set (ℤ × ℤ × ℤ × ℤ) :=
  {v | (K ≤ |(v.1 : ℝ)| ∧ |(v.1 : ℝ)| < 2 * K) ∧
    (L ≤ |(v.2.1 : ℝ)| ∧ |(v.2.1 : ℝ)| < 2 * L) ∧
    (P ≤ (v.2.2.1 : ℝ) ∧ (v.2.2.1 : ℝ) < 2 * P) ∧
    (Q ≤ (v.2.2.2 : ℝ) ∧ (v.2.2.2 : ℝ) < 2 * Q) ∧
    (d : ℤ) ∣ v.1 * v.2.2.1 + v.2.1 * v.2.2.2}

/-- Membership in `quadSet`, on an explicit quadruple. -/
theorem mem_quadSet {d : ℕ} {K L P Q : ℝ} {k l p q : ℤ} :
    (k, l, p, q) ∈ quadSet d K L P Q ↔
      (K ≤ |(k : ℝ)| ∧ |(k : ℝ)| < 2 * K) ∧
      (L ≤ |(l : ℝ)| ∧ |(l : ℝ)| < 2 * L) ∧
      (P ≤ (p : ℝ) ∧ (p : ℝ) < 2 * P) ∧
      (Q ≤ (q : ℝ) ∧ (q : ℝ) < 2 * Q) ∧
      (d : ℤ) ∣ k * p + l * q :=
  Iff.rfl

/-- An integer whose real image has `|x| < 2R` lies in `[-⌈2R⌉, ⌈2R⌉]`. -/
theorem abs_le_ceil_of_abs_lt_two_mul {x : ℤ} {R : ℝ} (h : |(x : ℝ)| < 2 * R) :
    -⌈2 * R⌉ ≤ x ∧ x ≤ ⌈2 * R⌉ := by
  have h1 : ((|x| : ℤ) : ℝ) < ((⌈2 * R⌉ : ℤ) : ℝ) := by
    rw [Int.cast_abs]
    exact h.trans_le (Int.le_ceil _)
  have h2 : |x| < ⌈2 * R⌉ := by exact_mod_cast h1
  have h3 := abs_lt.mp h2
  omega

/-- An integer whose real image is `< 2R` is at most `⌈2R⌉`. -/
theorem le_ceil_of_lt_two_mul {x : ℤ} {R : ℝ} (h : (x : ℝ) < 2 * R) : x ≤ ⌈2 * R⌉ := by
  have : ((x : ℤ) : ℝ) ≤ ((⌈2 * R⌉ : ℤ) : ℝ) := h.le.trans (Int.le_ceil _)
  exact_mod_cast this

/-- The counted set is finite. -/
theorem quadSet_finite (d : ℕ) (K L P Q : ℝ) (hP : 0 ≤ P) (hQ : 0 ≤ Q) :
    (quadSet d K L P Q).Finite := by
  refine Set.Finite.subset (Set.finite_Icc ((-⌈2 * K⌉, -⌈2 * L⌉, 0, 0) : ℤ × ℤ × ℤ × ℤ)
    ((⌈2 * K⌉, ⌈2 * L⌉, ⌈2 * P⌉, ⌈2 * Q⌉) : ℤ × ℤ × ℤ × ℤ)) ?_
  intro v hv
  obtain ⟨k, l, p, q⟩ := v
  rw [mem_quadSet] at hv
  obtain ⟨⟨-, hk⟩, ⟨-, hl⟩, ⟨hp1, hp2⟩, ⟨hq1, hq2⟩, -⟩ := hv
  have hp0 : (0 : ℤ) ≤ p := by exact_mod_cast hP.trans hp1
  have hq0 : (0 : ℤ) ≤ q := by exact_mod_cast hQ.trans hq1
  simp only [Set.mem_Icc, Prod.mk_le_mk]
  exact ⟨⟨(abs_le_ceil_of_abs_lt_two_mul hk).1, (abs_le_ceil_of_abs_lt_two_mul hl).1, hp0, hq0⟩,
    (abs_le_ceil_of_abs_lt_two_mul hk).2, (abs_le_ceil_of_abs_lt_two_mul hl).2,
    le_ceil_of_lt_two_mul hp2, le_ceil_of_lt_two_mul hq2⟩

/-- The index of the fibre a quadruple lies in: `(k, ℓ, p, q) ↦ (ℓ, q, m)` with `m = (kp + ℓq)/d`.
On `quadSet d K L P Q` the division is exact, so `m d = kp + ℓq`. -/
def quadIdx (d : ℕ) (v : ℤ × ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ :=
  (v.2.1, v.2.2.2, (v.1 * v.2.2.1 + v.2.1 * v.2.2.2) / (d : ℤ))

/-- The fibre of `quadIdx` over `(ℓ, q, m)` has at most as many elements as `m d - ℓ q` has
divisors. -/
theorem quadFiber_card_le_divisors {d : ℕ} {K L P Q : ℝ} (hK : 0 < K) (hP : 0 < P)
    {F : Finset (ℤ × ℤ × ℤ × ℤ)} (hF : ∀ v, v ∈ F ↔ v ∈ quadSet d K L P Q)
    (l₀ q₀ m₀ : ℤ) :
    #(F.filter fun v => quadIdx d v = (l₀, q₀, m₀))
      ≤ #(m₀ * (d : ℤ) - l₀ * q₀).natAbs.divisors := by
  have key : ∀ v ∈ F.filter fun v => quadIdx d v = (l₀, q₀, m₀),
      v.1 * v.2.2.1 = m₀ * (d : ℤ) - l₀ * q₀ ∧ v.1 ≠ 0 ∧ 0 < v.2.2.1 ∧
        v.2.1 = l₀ ∧ v.2.2.2 = q₀ := by
    intro v hv
    rw [Finset.mem_filter] at hv
    obtain ⟨hvF, hvy⟩ := hv
    obtain ⟨k, l, p, q⟩ := v
    rw [hF, mem_quadSet] at hvF
    obtain ⟨⟨hk1, -⟩, -, ⟨hp1, -⟩, -, hdvd⟩ := hvF
    simp only [quadIdx, Prod.mk.injEq] at hvy
    obtain ⟨hl, hq, hm⟩ := hvy
    have hk0 : k ≠ 0 := by
      have h : (0 : ℝ) < |(k : ℝ)| := lt_of_lt_of_le hK hk1
      rintro rfl
      simp at h
    have hp0 : 0 < p := by
      have : (0 : ℝ) < (p : ℝ) := lt_of_lt_of_le hP hp1
      exact_mod_cast this
    refine ⟨?_, hk0, hp0, hl, hq⟩
    have hmd : m₀ * (d : ℤ) = k * p + l * q := by
      rw [← hm]; exact Int.ediv_mul_cancel hdvd
    rw [hmd, hl, hq]; ring
  refine Finset.card_le_card_of_injOn (fun v => v.2.2.1.natAbs) ?_ ?_
  · intro v hv
    obtain ⟨hkp, hk0, hp0, -, -⟩ := key v hv
    simp only [Finset.mem_coe, Nat.mem_divisors]
    refine ⟨Int.natAbs_dvd_natAbs.mpr ⟨v.1, by rw [← hkp]; ring⟩, ?_⟩
    rw [Int.natAbs_ne_zero, ← hkp]
    exact mul_ne_zero hk0 hp0.ne'
  · intro v hv w hw hvw
    rw [Finset.mem_coe] at hv hw
    obtain ⟨hkpv, -, hpv, hlv, hqv⟩ := key v hv
    obtain ⟨hkpw, -, hpw, hlw, hqw⟩ := key w hw
    have hvw' : v.2.2.1.natAbs = w.2.2.1.natAbs := hvw
    have hp : v.2.2.1 = w.2.2.1 := by
      rw [← Int.natAbs_of_nonneg hpv.le, ← Int.natAbs_of_nonneg hpw.le, hvw']
    have hk : v.1 = w.1 := by
      refine mul_right_cancel₀ (b := v.2.2.1) hpv.ne' ?_
      rw [hkpv, hp, hkpw]
    exact Prod.ext hk (Prod.ext (hlv.trans hlw.symm) (Prod.ext hp (hqv.trans hqw.symm)))

/-- The count under the extra hypothesis `LQ ≤ KP`, with the constant explicit in terms of a
divisor bound `#m.divisors ≤ C₁ m^(ε/3)`. -/
theorem quadSet_ncard_le_of_le {ε : ℝ} (hε : 0 < ε) {C₁ : ℝ} (hC₁ : 0 < C₁)
    (hdiv : ∀ m : ℕ, 1 ≤ m → (#m.divisors : ℝ) ≤ C₁ * (m : ℝ) ^ (ε / 3))
    {n d : ℕ} (hn : 1 ≤ n) (hd : 1 ≤ d) {K L P Q : ℝ}
    (hK : 1 ≤ K) (hL : 1 ≤ L) (hP : 1 ≤ P) (hQ : 1 ≤ Q)
    (hKP : K * P ≤ (n : ℝ) ^ 2) (hLQ : L * Q ≤ K * P) :
    ((quadSet d K L P Q).ncard : ℝ)
      ≤ 336 * C₁ * (4 : ℝ) ^ (ε / 3) * (n : ℝ) ^ ε * (K * L * P * Q / d + L * Q) := by
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < (d : ℝ) := lt_of_lt_of_le zero_lt_one hd1
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hfin := quadSet_finite d K L P Q (zero_le_one.trans hP) (zero_le_one.trans hQ)
  set F : Finset (ℤ × ℤ × ℤ × ℤ) := hfin.toFinset with hFdef
  have hF : ∀ v, v ∈ F ↔ v ∈ quadSet d K L P Q := fun v => by
    rw [hFdef]; exact hfin.mem_toFinset
  set cL : ℤ := ⌈2 * L⌉ with hcL
  set cQ : ℤ := ⌈2 * Q⌉ with hcQ
  set cM : ℤ := ⌈8 * (K * P) / (d : ℝ)⌉ with hcM
  set box : Finset (ℤ × ℤ × ℤ) := Icc (-cL) cL ×ˢ Icc 1 cQ ×ˢ Icc (-cM) cM with hbox
  have hmaps : ∀ v ∈ F, quadIdx d v ∈ box := by
    intro v hv
    rw [hF] at hv
    obtain ⟨k, l, p, q⟩ := v
    rw [mem_quadSet] at hv
    obtain ⟨⟨hk1, hk2⟩, ⟨hl1, hl2⟩, ⟨hp1, hp2⟩, ⟨hq1, hq2⟩, hdvd⟩ := hv
    have hp0 : (0 : ℝ) < (p : ℝ) := lt_of_lt_of_le zero_lt_one (le_trans hP hp1)
    have hq0 : (0 : ℝ) < (q : ℝ) := lt_of_lt_of_le zero_lt_one (le_trans hQ hq1)
    have hqZ : (1 : ℤ) ≤ q := by exact_mod_cast (le_trans hQ hq1)
    have hmd : ((k * p + l * q) / (d : ℤ)) * (d : ℤ) = k * p + l * q :=
      Int.ediv_mul_cancel hdvd
    set m : ℤ := (k * p + l * q) / (d : ℤ) with hm
    have hmdR : (m : ℝ) * (d : ℝ) = (k : ℝ) * (p : ℝ) + (l : ℝ) * (q : ℝ) := by
      have := congrArg (fun z : ℤ => (z : ℝ)) hmd
      push_cast at this
      exact this
    have habs : |(m : ℝ)| * (d : ℝ) < 8 * (K * P) := by
      have h1 : |(k : ℝ) * (p : ℝ) + (l : ℝ) * (q : ℝ)| < 4 * (K * P) + 4 * (L * Q) := by
        have hkp : |(k : ℝ) * (p : ℝ)| < 2 * K * (2 * P) := by
          rw [abs_mul, abs_of_pos hp0]
          exact mul_lt_mul'' hk2 hp2 (abs_nonneg _) hp0.le
        have hlq : |(l : ℝ) * (q : ℝ)| < 2 * L * (2 * Q) := by
          rw [abs_mul, abs_of_pos hq0]
          exact mul_lt_mul'' hl2 hq2 (abs_nonneg _) hq0.le
        calc |(k : ℝ) * (p : ℝ) + (l : ℝ) * (q : ℝ)|
            ≤ |(k : ℝ) * (p : ℝ)| + |(l : ℝ) * (q : ℝ)| := abs_add_le _ _
          _ < 2 * K * (2 * P) + 2 * L * (2 * Q) := by linarith
          _ = 4 * (K * P) + 4 * (L * Q) := by ring
      have h2 : |(m : ℝ)| * (d : ℝ) = |(k : ℝ) * (p : ℝ) + (l : ℝ) * (q : ℝ)| := by
        rw [← hmdR, abs_mul, abs_of_pos hd0]
      rw [h2]
      linarith
    have hmM : |m| ≤ cM := by
      have h1 : |(m : ℝ)| < 8 * (K * P) / (d : ℝ) := by
        rw [lt_div_iff₀ hd0]; exact habs
      have h2 : ((|m| : ℤ) : ℝ) ≤ ((cM : ℤ) : ℝ) := by
        rw [Int.cast_abs, hcM]
        exact h1.le.trans (Int.le_ceil _)
      exact_mod_cast h2
    have hmM' := abs_le.mp hmM
    rw [hbox, Finset.mem_product, Finset.mem_product]
    refine ⟨?_, ?_, ?_⟩
    · rw [Finset.mem_Icc]
      exact ⟨(abs_le_ceil_of_abs_lt_two_mul hl2).1, (abs_le_ceil_of_abs_lt_two_mul hl2).2⟩
    · rw [Finset.mem_Icc]
      exact ⟨hqZ, le_ceil_of_lt_two_mul hq2⟩
    · rw [Finset.mem_Icc]
      exact ⟨hmM'.1, hmM'.2⟩
  have hfibre : ∀ y ∈ box,
      (#(F.filter fun v => quadIdx d v = y) : ℝ) ≤ C₁ * (4 * (n : ℝ) ^ 2) ^ (ε / 3) := by
    intro y _
    obtain ⟨l₀, q₀, m₀⟩ := y
    set A : ℤ := m₀ * (d : ℤ) - l₀ * q₀ with hA
    rcases Finset.eq_empty_or_nonempty (F.filter fun v => quadIdx d v = (l₀, q₀, m₀)) with
      hempty | ⟨w, hw⟩
    · rw [hempty]
      simp only [Finset.card_empty, Nat.cast_zero]
      positivity
    have hwmem := hw
    rw [Finset.mem_filter] at hwmem
    obtain ⟨hwF, hwy⟩ := hwmem
    have hAeq : w.1 * w.2.2.1 = A := by
      obtain ⟨k, l, p, q⟩ := w
      rw [hF, mem_quadSet] at hwF
      obtain ⟨-, -, -, -, hdvd⟩ := hwF
      simp only [quadIdx, Prod.mk.injEq] at hwy
      obtain ⟨hl, hq, hmm⟩ := hwy
      have hmd : m₀ * (d : ℤ) = k * p + l * q := by
        rw [← hmm]; exact Int.ediv_mul_cancel hdvd
      rw [hA, hmd, hl, hq]; ring
    have hbnd : ((A.natAbs : ℝ)) ≤ 4 * (n : ℝ) ^ 2 ∧ 1 ≤ A.natAbs := by
      obtain ⟨k, l, p, q⟩ := w
      rw [hF, mem_quadSet] at hwF
      obtain ⟨⟨hk1, hk2⟩, -, ⟨hp1, hp2⟩, -, -⟩ := hwF
      have hp0 : (0 : ℝ) < (p : ℝ) := lt_of_lt_of_le zero_lt_one (le_trans hP hp1)
      have hk0 : (0 : ℝ) < |(k : ℝ)| := lt_of_lt_of_le zero_lt_one (le_trans hK hk1)
      have hAabs : ((A.natAbs : ℝ)) = |(k : ℝ)| * (p : ℝ) := by
        rw [← hAeq, Nat.cast_natAbs]
        push_cast
        rw [abs_mul, abs_of_pos hp0]
      have hlt : |(k : ℝ)| * (p : ℝ) < 4 * (K * P) := by
        have := mul_lt_mul'' hk2 hp2 (abs_nonneg _) hp0.le
        nlinarith
      refine ⟨?_, ?_⟩
      · rw [hAabs]; nlinarith
      · have : (0 : ℝ) < ((A.natAbs : ℝ)) := by rw [hAabs]; positivity
        have : 0 < A.natAbs := by exact_mod_cast this
        omega
    calc (#(F.filter fun v => quadIdx d v = (l₀, q₀, m₀)) : ℝ)
        ≤ (#A.natAbs.divisors : ℝ) := by
          exact_mod_cast quadFiber_card_le_divisors (K := K) (L := L) (P := P) (Q := Q)
            (lt_of_lt_of_le zero_lt_one hK) (lt_of_lt_of_le zero_lt_one hP) hF l₀ q₀ m₀
      _ ≤ C₁ * ((A.natAbs : ℝ)) ^ (ε / 3) := hdiv _ hbnd.2
      _ ≤ C₁ * (4 * (n : ℝ) ^ 2) ^ (ε / 3) := by
          refine mul_le_mul_of_nonneg_left ?_ hC₁.le
          exact Real.rpow_le_rpow (by positivity) hbnd.1 (by positivity)
  have hsum : ((quadSet d K L P Q).ncard : ℝ)
      ≤ (#box : ℝ) * (C₁ * (4 * (n : ℝ) ^ 2) ^ (ε / 3)) := by
    rw [Set.ncard_eq_toFinset_card _ hfin, ← hFdef,
      Finset.card_eq_sum_card_fiberwise hmaps]
    push_cast
    calc ∑ y ∈ box, (#(F.filter fun v => quadIdx d v = y) : ℝ)
        ≤ ∑ _y ∈ box, C₁ * (4 * (n : ℝ) ^ 2) ^ (ε / 3) := Finset.sum_le_sum hfibre
      _ = (#box : ℝ) * (C₁ * (4 * (n : ℝ) ^ 2) ^ (ε / 3)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hLQ0 : (0 : ℝ) ≤ L * Q := by positivity
  have hboxcard : (#box : ℝ) ≤ 7 * L * (3 * Q * (16 * (K * P) / (d : ℝ) + 3)) := by
    have hcL2 : (2 : ℝ) ≤ (cL : ℝ) := by
      rw [hcL]
      have : (2 : ℝ) ≤ 2 * L := by linarith
      exact this.trans (Int.le_ceil _)
    have hcQ2 : (2 : ℝ) ≤ (cQ : ℝ) := by
      rw [hcQ]
      have : (2 : ℝ) ≤ 2 * Q := by linarith
      exact this.trans (Int.le_ceil _)
    have hcM0 : (0 : ℝ) ≤ (cM : ℝ) := by
      rw [hcM]
      have h0 : (0 : ℝ) ≤ 8 * (K * P) / (d : ℝ) := by positivity
      exact h0.trans (Int.le_ceil _)
    have hcLlt : (cL : ℝ) < 2 * L + 1 := by rw [hcL]; exact Int.ceil_lt_add_one _
    have hcQlt : (cQ : ℝ) < 2 * Q + 1 := by rw [hcQ]; exact Int.ceil_lt_add_one _
    have hcMlt : (cM : ℝ) < 8 * (K * P) / (d : ℝ) + 1 := by
      rw [hcM]; exact Int.ceil_lt_add_one _
    have hcLZ : (2 : ℤ) ≤ cL := by exact_mod_cast hcL2
    have hcQZ : (2 : ℤ) ≤ cQ := by exact_mod_cast hcQ2
    have hcMZ : (0 : ℤ) ≤ cM := by exact_mod_cast hcM0
    have e1 : (#(Icc (-cL) cL) : ℝ) ≤ 7 * L := by
      have h1 : ((#(Icc (-cL) cL) : ℤ)) = cL + 1 - -cL :=
        Int.card_Icc_of_le _ _ (by omega)
      have h2 := congrArg (fun z : ℤ => (z : ℝ)) h1
      push_cast at h2
      rw [h2]; linarith
    have e2 : (#(Icc (1 : ℤ) cQ) : ℝ) ≤ 3 * Q := by
      have h1 : ((#(Icc (1 : ℤ) cQ) : ℤ)) = cQ + 1 - 1 :=
        Int.card_Icc_of_le _ _ (by omega)
      have h2 := congrArg (fun z : ℤ => (z : ℝ)) h1
      push_cast at h2
      rw [h2]; linarith
    have e3 : (#(Icc (-cM) cM) : ℝ) ≤ 16 * (K * P) / (d : ℝ) + 3 := by
      have h1 : ((#(Icc (-cM) cM) : ℤ)) = cM + 1 - -cM :=
        Int.card_Icc_of_le _ _ (by omega)
      have h2 := congrArg (fun z : ℤ => (z : ℝ)) h1
      push_cast at h2
      have h3 : 16 * (K * P) / (d : ℝ) = 2 * (8 * (K * P) / (d : ℝ)) := by ring
      rw [h2, h3]; linarith
    have hbc : (#box : ℝ)
        = (#(Icc (-cL) cL) : ℝ) * ((#(Icc (1 : ℤ) cQ) : ℝ) * (#(Icc (-cM) cM) : ℝ)) := by
      rw [hbox, Finset.card_product, Finset.card_product]
      push_cast; ring
    rw [hbc]
    gcongr
  have hrpow : (4 * (n : ℝ) ^ 2) ^ (ε / 3) ≤ (4 : ℝ) ^ (ε / 3) * (n : ℝ) ^ ε := by
    rw [Real.mul_rpow (by norm_num) (by positivity)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc ((n : ℝ) ^ 2) ^ (ε / 3) = ((n : ℝ) ^ (2 : ℝ)) ^ (ε / 3) := by
          rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      _ = (n : ℝ) ^ (2 * (ε / 3)) := by
          rw [← Real.rpow_mul (by positivity)]
      _ ≤ (n : ℝ) ^ ε := Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have hfac : (0 : ℝ) ≤ C₁ * ((4 : ℝ) ^ (ε / 3) * (n : ℝ) ^ ε) := by positivity
  have harith : 7 * L * (3 * Q * (16 * (K * P) / (d : ℝ) + 3))
      ≤ 336 * (K * L * P * Q / (d : ℝ) + L * Q) := by
    have e : 7 * L * (3 * Q * (16 * (K * P) / (d : ℝ) + 3))
        = 336 * (K * L * P * Q / (d : ℝ)) + 63 * (L * Q) := by ring
    rw [e]; nlinarith
  calc ((quadSet d K L P Q).ncard : ℝ)
      ≤ (#box : ℝ) * (C₁ * (4 * (n : ℝ) ^ 2) ^ (ε / 3)) := hsum
    _ ≤ (#box : ℝ) * (C₁ * ((4 : ℝ) ^ (ε / 3) * (n : ℝ) ^ ε)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul_of_nonneg_left hrpow hC₁.le
    _ ≤ (7 * L * (3 * Q * (16 * (K * P) / (d : ℝ) + 3)))
          * (C₁ * ((4 : ℝ) ^ (ε / 3) * (n : ℝ) ^ ε)) := by
        exact mul_le_mul_of_nonneg_right hboxcard hfac
    _ ≤ (336 * (K * L * P * Q / (d : ℝ) + L * Q)) * (C₁ * ((4 : ℝ) ^ (ε / 3) * (n : ℝ) ^ ε)) := by
        exact mul_le_mul_of_nonneg_right harith hfac
    _ = 336 * C₁ * (4 : ℝ) ^ (ε / 3) * (n : ℝ) ^ ε * (K * L * P * Q / d + L * Q) := by ring

/-- Transposing `(k, p)` with `(ℓ, q)` is a bijection between the two counted sets, so they have
equally many elements. -/
theorem quadSet_ncard_swap (d : ℕ) (K L P Q : ℝ) :
    (quadSet d L K Q P).ncard = (quadSet d K L P Q).ncard := by
  have hinj : Function.Injective
      (fun v : ℤ × ℤ × ℤ × ℤ => (v.2.1, v.1, v.2.2.2, v.2.2.1)) := by
    intro a b hab
    simp only [Prod.mk.injEq] at hab
    obtain ⟨h1, h2, h3, h4⟩ := hab
    exact Prod.ext h2 (Prod.ext h1 (Prod.ext h4 h3))
  have himg : (fun v : ℤ × ℤ × ℤ × ℤ => (v.2.1, v.1, v.2.2.2, v.2.2.1)) ''
      quadSet d K L P Q = quadSet d L K Q P := by
    ext v
    simp only [Set.mem_image]
    constructor
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨k, l, p, q⟩ := w
      rw [mem_quadSet] at hw
      obtain ⟨hk, hl, hp, hq, hdvd⟩ := hw
      exact mem_quadSet.mpr ⟨hl, hk, hq, hp, by rw [add_comm]; exact hdvd⟩
    · intro hv
      obtain ⟨a, b, c, e⟩ := v
      rw [mem_quadSet] at hv
      obtain ⟨ha, hb, hc, he, hdvd⟩ := hv
      exact ⟨(b, a, e, c), mem_quadSet.mpr ⟨hb, ha, he, hc, by rw [add_comm]; exact hdvd⟩, rfl⟩
  rw [← himg, Set.ncard_image_of_injective _ hinj]

/-- For every `ε > 0` there is `C(ε) > 0` such that for all integers `n, d ≥ 1` with `d ∣ n` and
all reals `K, L, P, Q ≥ 1` with `KP ≤ n²` and `LQ ≤ n²`, the number of quadruples
`(k, ℓ, p, q) ∈ ℤ⁴` with `K ≤ |k| < 2K`, `L ≤ |ℓ| < 2L`, `P ≤ p < 2P`, `Q ≤ q < 2Q` and
`kp + ℓq ≡ 0 (mod d)` is at most `C(ε) nᵋ (KLPQ/d + min (KP) (LQ))`. -/
theorem quadcount {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n d : ℕ, 1 ≤ n → 1 ≤ d → d ∣ n → ∀ K L P Q : ℝ,
      1 ≤ K → 1 ≤ L → 1 ≤ P → 1 ≤ Q → K * P ≤ (n : ℝ) ^ 2 → L * Q ≤ (n : ℝ) ^ 2 →
      ((quadSet d K L P Q).ncard : ℝ)
        ≤ C * (n : ℝ) ^ ε * (K * L * P * Q / d + min (K * P) (L * Q)) := by
  obtain ⟨C₁, hC₁, hdiv⟩ := divisor_bound (by linarith : (0 : ℝ) < ε / 3)
  refine ⟨336 * C₁ * (4 : ℝ) ^ (ε / 3), by positivity, ?_⟩
  intro n d hn hd _hdn K L P Q hK hL hP hQ hKP hLQ
  rcases le_total (L * Q) (K * P) with h | h
  · rw [min_eq_right h]
    exact quadSet_ncard_le_of_le hε hC₁ hdiv hn hd hK hL hP hQ hKP h
  · rw [min_eq_left h]
    have hswap := quadSet_ncard_le_of_le hε hC₁ hdiv hn hd hL hK hQ hP hLQ h
    rw [quadSet_ncard_swap] at hswap
    exact hswap.trans_eq (by ring)

end Paucity
