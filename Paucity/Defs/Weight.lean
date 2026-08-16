/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The circle weight `w`

`w_N(k) = 1 / (2 min(k, N-k))`, where `min(k, N-k)` is the distance from `k` to `0` modulo `N`. The
denominator vanishes at `k = 0` and at `k = N`, where `w_N(k) = 0`.

## Main definitions

* `w`: the circle weight $w_N(k)$.

## Main results

* `w_nonneg`: `w` is nonnegative.
-/

@[expose] public section

namespace Paucity

/-- `w N k = 1 / (2 min(k, N-k))`, the circle weight $w_N(k)$. -/
noncomputable def w (N k : ℕ) : ℝ := 1 / (2 * ((min k (N - k) : ℕ) : ℝ))

theorem w_nonneg (N k : ℕ) : 0 ≤ w N k := by
  unfold w
  apply div_nonneg (by norm_num)
  have h : (0 : ℝ) ≤ ((min k (N - k) : ℕ) : ℝ) := Nat.cast_nonneg _
  linarith

end Paucity
