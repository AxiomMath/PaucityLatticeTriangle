/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The box norm

The sup norm on `ℝ × ℝ` rescaled by box dimensions `A` and `B`, given by
`‖(x,y)‖_{A,B} = max (|x| / A) (|y| / B)`. For `0 < A` and `0 < B` it is a norm.

## Main definitions

* `boxNorm`: the sup norm rescaled by the box dimensions `A` and `B`.

## Main results

* `abs_le_of_boxNorm_le`: a bound on the box norm bounds each coordinate.
* `boxNorm_smul`: absolute homogeneity, `boxNorm A B (c • v) = |c| * boxNorm A B v`.
* `boxNorm_eq_zero_iff`: for positive box dimensions the box norm vanishes only at the origin.
-/

@[expose] public section

namespace Paucity

/-- `boxNorm A B v`, the quantity `‖v‖_{A,B}`: the sup norm rescaled by the box dimensions `A` and
`B`. -/
noncomputable def boxNorm (A B : ℝ) (v : ℝ × ℝ) : ℝ := max (|v.1| / A) (|v.2| / B)

@[simp] theorem boxNorm_zero (A B : ℝ) : boxNorm A B (0, 0) = 0 := by simp [boxNorm]

theorem boxNorm_nonneg {A : ℝ} (hA : 0 < A) (B : ℝ) (v : ℝ × ℝ) :
    0 ≤ boxNorm A B v :=
  le_max_of_le_left (by positivity)

/-- Each coordinate is bounded by the box norm times the corresponding box dimension. -/
theorem abs_le_of_boxNorm_le {A B r : ℝ} (hA : 0 < A) (hB : 0 < B) {v : ℝ × ℝ}
    (h : boxNorm A B v ≤ r) : |v.1| ≤ r * A ∧ |v.2| ≤ r * B := by
  unfold boxNorm at h
  exact ⟨(div_le_iff₀ hA).mp (le_trans (le_max_left _ _) h),
    (div_le_iff₀ hB).mp (le_trans (le_max_right _ _) h)⟩

/-- Absolute homogeneity of the box norm. -/
theorem boxNorm_smul (A B c : ℝ) (v : ℝ × ℝ) :
    boxNorm A B (c • v) = |c| * boxNorm A B v := by
  unfold boxNorm
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, abs_mul]
  rw [mul_div_assoc, mul_div_assoc, ← mul_max_of_nonneg _ _ (abs_nonneg c)]

/-- Nondegeneracy: for positive box dimensions the box norm vanishes only at the origin. -/
theorem boxNorm_eq_zero_iff {A B : ℝ} (hA : 0 < A) (hB : 0 < B) {v : ℝ × ℝ} :
    boxNorm A B v = 0 ↔ v = (0, 0) := by
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := abs_le_of_boxNorm_le hA hB h.le
    rw [zero_mul] at h1 h2
    exact Prod.ext (abs_nonpos_iff.mp h1) (abs_nonpos_iff.mp h2)
  · rintro rfl; simp

end Paucity
