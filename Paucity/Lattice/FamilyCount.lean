/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Paucity.Defs.Bd
public import Paucity.Defs.Dn
public import Paucity.Defs.LambdaKL
public import Paucity.Defs.Q

/-!
# Counting the families

For `n ≥ 2` the number of pairs `(d, X)` in which `d ∈ D_n` and `X` is one of `A_d`, `B_d`, or a
class `Λ_d(K,L)` with `K` and `L` powers of two satisfying `2K ≤ d` and `2L ≤ d`, is at most
`5 Q(n) / (1 + log n)²`.

## Main definitions

* `scales`: the powers of two `K` with `2K ≤ d`.
* `familyIndex`: the labels `(d, X)` with `d ∈ D_n` and `X` naming `A_d`, `B_d` or a dyadic class
  at admissible scales.
* `familyOf`: the family `A_d(p,q)`, `B_d(p,q)` or `Λ_d(K,L;p,q)` that a label names.

## Main results

* `mem_scales`: `K ∈ scales d` exactly when `K` is a power of two with `2K ≤ d`.
* `mem_familyIndex`: membership in the label set.
* `mem_image_familyOf`: the point sets named by the labels are exactly `A_d(p,q)`, `B_d(p,q)` and
  the dyadic classes at admissible scales.
* `card_scales_le`: `#(scales d) ≤ log₂ n` for `d ≤ n`.
* `card_D_le`: `#D_n ≤ 2 ^ ω(n)`.
* `card_familyIndex_le`: `#(familyIndex n) ≤ 5 Q(n) / (1 + log n)²`.
* `card_familySets_le`: the same bound for the pairs `(d, X)` read as point sets.
-/

@[expose] public section

namespace Paucity

open Finset

/-- `scales d`: the admissible dyadic scales at level `d`, i.e. the powers of two `K` with
`2K ≤ d`. -/
def scales (d : ℕ) : Finset ℕ :=
  ((Finset.range d).image fun i => 2 ^ i).filter fun K => 2 * K ≤ d

/-- `scales d` is exactly the set of powers of two `K` with `2K ≤ d`. -/
theorem mem_scales {d K : ℕ} : K ∈ scales d ↔ (∃ i, K = 2 ^ i) ∧ 2 * K ≤ d := by
  unfold scales
  rw [Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨⟨i, -, rfl⟩, h2⟩
    exact ⟨⟨i, rfl⟩, h2⟩
  · rintro ⟨⟨i, rfl⟩, h2⟩
    refine ⟨⟨i, ?_, rfl⟩, h2⟩
    rw [Finset.mem_range]
    have h1 : i < 2 ^ i := Nat.lt_two_pow_self
    omega

/-- The labels of the families: pairs `(d, X)` with `d ∈ D n` and `X` naming `A_d` (`.inl false`),
`B_d` (`.inl true`), or the dyadic class `Λ_d(K,L)` (`.inr (K, L)`) for admissible scales `K, L`.
-/
def familyIndex (n : ℕ) : Finset (ℕ × (Bool ⊕ ℕ × ℕ)) :=
  (D n).biUnion fun d => ({d} : Finset ℕ) ×ˢ
    (({Sum.inl false, Sum.inl true} : Finset (Bool ⊕ ℕ × ℕ)) ∪
      (scales d ×ˢ scales d).image Sum.inr)

/-- Membership in the label set: `(d, X) ∈ familyIndex n` exactly when `d ∈ D n` and `X` is one of
the two axis labels or a pair of admissible scales. -/
theorem mem_familyIndex {n d : ℕ} {X : Bool ⊕ ℕ × ℕ} :
    (d, X) ∈ familyIndex n ↔ d ∈ D n ∧
      (X = Sum.inl false ∨ X = Sum.inl true ∨
        ∃ K L : ℕ, K ∈ scales d ∧ L ∈ scales d ∧ X = Sum.inr (K, L)) := by
  simp only [familyIndex, Finset.mem_biUnion, Finset.mem_product, Finset.mem_singleton,
    Finset.mem_union, Finset.mem_insert, Finset.mem_image, Prod.exists]
  constructor
  · rintro ⟨d', hd', rfl, h⟩
    refine ⟨hd', ?_⟩
    rcases h with (h | h) | ⟨K, L, hKL, rfl⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨K, L, hKL.1, hKL.2, rfl⟩)
  · rintro ⟨hd, h⟩
    refine ⟨d, hd, rfl, ?_⟩
    rcases h with h | h | ⟨K, L, hK, hL, rfl⟩
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr ⟨K, L, ⟨hK, hL⟩, rfl⟩

/-- The family a label names: `A_d`, `B_d`, or the dyadic class `Λ_d(K,L;p,q)`. -/
noncomputable def familyOf (p q d : ℕ) : Bool ⊕ ℕ × ℕ → Finset (ℤ × ℤ)
  | Sum.inl false => A d p q
  | Sum.inl true => B d p q
  | Sum.inr (K, L) => dyadicBox d (K : ℝ) (L : ℝ) p q

/-- The pairs `(d, X)` named by `familyIndex n` are exactly those with `d ∈ D_n` and `X` one of
`A_d(p,q)`, `B_d(p,q)`, or a dyadic class `Λ_d(K,L;p,q)` with `K, L` powers of two satisfying
`2K ≤ d`, `2L ≤ d`. -/
theorem mem_image_familyOf {n p q d : ℕ} {X : Finset (ℤ × ℤ)} :
    (d, X) ∈ (familyIndex n).image (fun x => (x.1, familyOf p q x.1 x.2)) ↔
      d ∈ D n ∧ (X = A d p q ∨ X = B d p q ∨
        ∃ K L : ℕ, (∃ i, K = 2 ^ i) ∧ (∃ j, L = 2 ^ j) ∧ 2 * K ≤ d ∧ 2 * L ≤ d ∧
          X = dyadicBox d (K : ℝ) (L : ℝ) p q) := by
  rw [Finset.mem_image]
  constructor
  · rintro ⟨⟨d', Y⟩, hmem, heq⟩
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    obtain ⟨hd, hY⟩ := mem_familyIndex.mp hmem
    refine ⟨hd, ?_⟩
    rcases hY with rfl | rfl | ⟨K, L, hK, hL, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · obtain ⟨hK2, hKd⟩ := mem_scales.mp hK
      obtain ⟨hL2, hLd⟩ := mem_scales.mp hL
      exact Or.inr (Or.inr ⟨K, L, hK2, hL2, hKd, hLd, rfl⟩)
  · rintro ⟨hd, hX⟩
    rcases hX with rfl | rfl | ⟨K, L, hK2, hL2, hKd, hLd, rfl⟩
    · exact ⟨(d, Sum.inl false), mem_familyIndex.mpr ⟨hd, Or.inl rfl⟩, rfl⟩
    · exact ⟨(d, Sum.inl true), mem_familyIndex.mpr ⟨hd, Or.inr (Or.inl rfl)⟩, rfl⟩
    · exact ⟨(d, Sum.inr (K, L)), mem_familyIndex.mpr ⟨hd,
        Or.inr (Or.inr ⟨K, L, mem_scales.mpr ⟨hK2, hKd⟩, mem_scales.mpr ⟨hL2, hLd⟩, rfl⟩)⟩, rfl⟩

/-- At most `log₂ n` scales are admissible at any level `d ≤ n`. -/
theorem card_scales_le {n d : ℕ} (hd : d ≤ n) : (scales d).card ≤ Nat.log 2 n := by
  have hsub : scales d ⊆ (Finset.range (Nat.log 2 n)).image fun i => 2 ^ i := by
    intro K hK
    obtain ⟨⟨i, rfl⟩, h2⟩ := mem_scales.mp hK
    refine Finset.mem_image.mpr ⟨i, ?_, rfl⟩
    rw [Finset.mem_range]
    have hpow : 2 ^ (i + 1) ≤ n := by
      rw [pow_succ]
      omega
    have := Nat.le_log_of_pow_le (b := 2) (by norm_num) hpow
    omega
  calc (scales d).card
      ≤ ((Finset.range (Nat.log 2 n)).image fun i => 2 ^ i).card := Finset.card_le_card hsub
    _ ≤ (Finset.range (Nat.log 2 n)).card := Finset.card_image_le
    _ = Nat.log 2 n := Finset.card_range _

/-- `#D_n ≤ 2 ^ ω(n)`. -/
theorem card_D_le {n : ℕ} (hn : n ≠ 0) : (D n).card ≤ 2 ^ n.primeFactors.card := by
  rw [← Finset.card_powerset]
  refine Finset.card_le_card_of_injOn (fun d => (n / d).primeFactors) ?_ ?_
  · intro d hd
    simp only [Finset.mem_coe, Finset.mem_powerset]
    exact Nat.primeFactors_mono (Nat.div_dvd_of_dvd (dvd_of_mem_D hd)) hn
  · intro d₁ h₁ d₂ h₂ heq
    simp only [Finset.mem_coe] at h₁ h₂
    simp only at heq
    have hq : n / d₁ = n / d₂ := by
      rw [← Nat.prod_primeFactors_of_squarefree (mem_D.mp h₁).2,
        ← Nat.prod_primeFactors_of_squarefree (mem_D.mp h₂).2, heq]
    rw [← Nat.div_div_self (dvd_of_mem_D h₁) hn, ← Nat.div_div_self (dvd_of_mem_D h₂) hn, hq]

/-- The number of pairs `(d, X)` with `d ∈ D_n` and `X` one of `A_d`, `B_d` or a dyadic class
`Λ_d(K,L)` with `K, L` powers of two obeying `2K ≤ d`, `2L ≤ d`, is at most
`5 Q(n) / (1 + log n)²`. -/
theorem card_familyIndex_le {n : ℕ} (hn : 2 ≤ n) :
    ((familyIndex n).card : ℝ) ≤ 5 * Q n / (1 + Real.log n) ^ 2 := by
  have hstep : ∀ d ∈ D n,
      (({d} : Finset ℕ) ×ˢ
        (({Sum.inl false, Sum.inl true} : Finset (Bool ⊕ ℕ × ℕ)) ∪
          (scales d ×ˢ scales d).image Sum.inr)).card ≤ 2 + Nat.log 2 n ^ 2 := by
    intro d hd
    have hdn : d ≤ n := Nat.le_of_dvd (by omega) (dvd_of_mem_D hd)
    have hs : (scales d).card ≤ Nat.log 2 n := card_scales_le hdn
    calc (({d} : Finset ℕ) ×ˢ
          (({Sum.inl false, Sum.inl true} : Finset (Bool ⊕ ℕ × ℕ)) ∪
            (scales d ×ˢ scales d).image Sum.inr)).card
        = (({Sum.inl false, Sum.inl true} : Finset (Bool ⊕ ℕ × ℕ)) ∪
            (scales d ×ˢ scales d).image Sum.inr).card := by
          rw [Finset.card_product, Finset.card_singleton, one_mul]
      _ ≤ ({Sum.inl false, Sum.inl true} : Finset (Bool ⊕ ℕ × ℕ)).card
            + ((scales d ×ˢ scales d).image Sum.inr).card := Finset.card_union_le _ _
      _ ≤ 2 + (scales d).card ^ 2 := by
          have h1 : ({Sum.inl false, Sum.inl true} : Finset (Bool ⊕ ℕ × ℕ)).card ≤ 2 := by
            refine le_trans (Finset.card_insert_le _ _) ?_
            simp
          have h2 : ((scales d ×ˢ scales d).image
              (Sum.inr : ℕ × ℕ → Bool ⊕ ℕ × ℕ)).card ≤ (scales d).card ^ 2 := by
            refine le_trans Finset.card_image_le ?_
            rw [Finset.card_product, sq]
          omega
      _ ≤ 2 + Nat.log 2 n ^ 2 := by
          have := Nat.pow_le_pow_left hs 2
          omega
  have hcount : (familyIndex n).card ≤ (D n).card * (2 + Nat.log 2 n ^ 2) := by
    calc (familyIndex n).card
        ≤ ∑ d ∈ D n, (({d} : Finset ℕ) ×ˢ
            (({Sum.inl false, Sum.inl true} : Finset (Bool ⊕ ℕ × ℕ)) ∪
              (scales d ×ˢ scales d).image Sum.inr)).card := Finset.card_biUnion_le
      _ ≤ ∑ _d ∈ D n, (2 + Nat.log 2 n ^ 2) := Finset.sum_le_sum hstep
      _ = (D n).card * (2 + Nat.log 2 n ^ 2) := by
          rw [Finset.sum_const, smul_eq_mul]
  have hnat : (familyIndex n).card ≤ 2 ^ n.primeFactors.card * (2 + Nat.log 2 n ^ 2) :=
    le_trans hcount (Nat.mul_le_mul_right _ (card_D_le (by omega)))
  have hu : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  have hlR : (Nat.log 2 n : ℝ) * Real.log 2 ≤ Real.log n := by
    have h1 : ((2 : ℝ) ^ (Nat.log 2 n)) ≤ (n : ℝ) := by
      exact_mod_cast Nat.pow_log_le_self 2 (by omega : n ≠ 0)
    have h2 : Real.log ((2 : ℝ) ^ (Nat.log 2 n)) ≤ Real.log n :=
      Real.log_le_log (by positivity) h1
    rwa [Real.log_pow] at h2
  have hl15 : (Nat.log 2 n : ℝ) ≤ 1.5 * Real.log n := by
    have hnn : (0 : ℝ) ≤ (Nat.log 2 n : ℝ) := Nat.cast_nonneg _
    have h2 : (Nat.log 2 n : ℝ) * 0.6931471803 ≤ (Nat.log 2 n : ℝ) * Real.log 2 :=
      mul_le_mul_of_nonneg_left Real.log_two_gt_d9.le hnn
    linarith
  have hkey : (2 : ℝ) + (Nat.log 2 n : ℝ) ^ 2 ≤ 5 * (1 + Real.log n) ^ 2 := by
    have hnn : (0 : ℝ) ≤ (Nat.log 2 n : ℝ) := Nat.cast_nonneg _
    nlinarith [mul_self_le_mul_self hnn hl15]
  have hpow : (0 : ℝ) < 2 ^ n.primeFactors.card := by positivity
  have hcast : ((familyIndex n).card : ℝ)
      ≤ (2 ^ n.primeFactors.card : ℝ) * (2 + (Nat.log 2 n : ℝ) ^ 2) := by
    exact_mod_cast hnat
  have hQ : 5 * Q n / (1 + Real.log n) ^ 2
      = 5 * (2 ^ n.primeFactors.card : ℝ) * (1 + Real.log n) ^ 2 := by
    have hne : (1 : ℝ) + Real.log n ≠ 0 := by positivity
    unfold Q
    field_simp
  rw [hQ]
  calc ((familyIndex n).card : ℝ)
      ≤ (2 ^ n.primeFactors.card : ℝ) * (2 + (Nat.log 2 n : ℝ) ^ 2) := hcast
    _ ≤ (2 ^ n.primeFactors.card : ℝ) * (5 * (1 + Real.log n) ^ 2) :=
        mul_le_mul_of_nonneg_left hkey hpow.le
    _ = 5 * (2 ^ n.primeFactors.card : ℝ) * (1 + Real.log n) ^ 2 := by ring

/-- The same bound for the pairs `(d, X)` read as point sets: the number of pairs `(d, X)` with
`d ∈ D_n` and `X` equal to `A_d(p,q)`, `B_d(p,q)` or a dyadic class `Λ_d(K,L;p,q)` with admissible
`K, L` (see `mem_image_familyOf`) is at most `5 Q(n) / (1 + log n)²`. -/
theorem card_familySets_le {n : ℕ} (hn : 2 ≤ n) (p q : ℕ) :
    (((familyIndex n).image fun x => (x.1, familyOf p q x.1 x.2)).card : ℝ)
      ≤ 5 * Q n / (1 + Real.log n) ^ 2 := by
  refine le_trans ?_ (card_familyIndex_le hn)
  exact_mod_cast Finset.card_image_le

end Paucity
