/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Paucity.Defs.Lambdamin

/-!
# A minimizing vector is primitive

For `A, B > 0`, a subgroup `Λ ⊆ ℝ²` and `w ∈ Λ \ {0}` with `‖w‖_{A,B} = λ_{A,B}(Λ)`, there are no
`v ∈ Λ` and integer `m ≥ 2` with `w = m v`.

## Main results

* `not_proper_multiple_of_boxNorm_eq_lambdaMin`: a nonzero element of `Λ` attaining `λ_{A,B}` is
  not a proper integer multiple of another element of `Λ`.
-/

@[expose] public section

namespace Paucity

/-- A nonzero element of `Λ` attaining `λ_{A,B}` is not a proper integer multiple of another
element of `Λ`. -/
theorem not_proper_multiple_of_boxNorm_eq_lambdaMin {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    {Λ : AddSubgroup (ℝ × ℝ)} {w : ℝ × ℝ} (hw : w ∈ Λ) (hw0 : w ≠ 0)
    (hmin : boxNorm A B w = lambdaMin A B Λ) :
    ¬ ∃ v ∈ Λ, ∃ m : ℤ, 2 ≤ m ∧ w = (m : ℝ) • v := by
  rintro ⟨v, hv, m, hm, rfl⟩
  have hv0 : v ≠ 0 := by
    rintro rfl
    exact hw0 (by simp)
  have hvpos : 0 < boxNorm A B v := by
    rcases (boxNorm_nonneg hA B v).lt_or_eq with h | h
    · exact h
    · exact absurd ((boxNorm_eq_zero_iff hA hB).mp h.symm) hv0
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast lt_of_lt_of_le zero_lt_two hm
  have hhom : boxNorm A B ((m : ℝ) • v) = (m : ℝ) * boxNorm A B v := by
    rw [boxNorm_smul, abs_of_pos hmpos]
  have hle : lambdaMin A B Λ ≤ boxNorm A B v := lambdaMin_le hA B hv hv0
  have hm2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  rw [hhom] at hmin
  nlinarith [hle, hmin, hvpos, hm2]

end Paucity
