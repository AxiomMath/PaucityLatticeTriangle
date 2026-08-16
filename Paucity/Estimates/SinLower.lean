/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The sine lower bound

On `[0, 1]` the sine satisfies `|sin (π x)| ≥ 2 min(x, 1 - x)`.

## Main results

* `two_mul_le_sin_pi_mul`: `2x ≤ sin (π x)` for `0 ≤ x ≤ 1/2`.
* `two_mul_min_le_abs_sin`: `2 min(x, 1 - x) ≤ |sin (π x)|` for `0 ≤ x ≤ 1`.
-/

@[expose] public section

namespace Paucity

open Real

/-- The half-range case: on `[0, 1/2]`, `2x ≤ sin (π x)`. -/
theorem two_mul_le_sin_pi_mul {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    2 * x ≤ Real.sin (π * x) := by
  have h1 : (0 : ℝ) ≤ 2 * x := by linarith
  have h2 : 2 * x ≤ 1 := by linarith
  have := Real.le_sin_mul h1 h2
  have hpi : π / 2 * (2 * x) = π * x := by ring
  rwa [hpi] at this

/-- `2 min(x, 1 - x) ≤ |sin (π x)|` for `x ∈ [0, 1]`. -/
theorem two_mul_min_le_abs_sin {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    2 * min x (1 - x) ≤ |Real.sin (π * x)| := by
  by_cases hhalf : x ≤ 1 / 2
  · have hmin : min x (1 - x) = x := min_eq_left (by linarith)
    have hnn : 0 ≤ Real.sin (π * x) := by
      apply Real.sin_nonneg_of_nonneg_of_le_pi
      · positivity
      · nlinarith [Real.pi_pos]
    rw [hmin, abs_of_nonneg hnn]
    exact two_mul_le_sin_pi_mul hx0 hhalf
  · have hgt : 1 / 2 < x := lt_of_not_ge hhalf
    have hmin : min x (1 - x) = 1 - x := min_eq_right (by linarith)
    have hrefl : Real.sin (π * (1 - x)) = Real.sin (π * x) := by
      have : π * (1 - x) = π - π * x := by ring
      rw [this, Real.sin_pi_sub]
    have hnn : 0 ≤ Real.sin (π * x) := by
      rw [← hrefl]
      apply Real.sin_nonneg_of_nonneg_of_le_pi
      · nlinarith [Real.pi_pos]
      · nlinarith [Real.pi_pos]
    rw [hmin, abs_of_nonneg hnn, ← hrefl]
    exact two_mul_le_sin_pi_mul (by linarith) (by linarith)

end Paucity
