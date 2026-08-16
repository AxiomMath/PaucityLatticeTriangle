/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The majorant weight `nu`

`ν_{d,H}(k) = H` if `k = 0`, and `d/(2|k|)` otherwise: a total, nonnegative real-valued weight on
the signed residues `k : ℤ`.

## Main definitions

* `nu`: the majorant weight `ν_{d,H}(k)`.

## Main results

* `nu_zero`, `nu_of_ne_zero`: the two branches of `nu`.
* `nu_nonneg`: `nu` is nonnegative.
-/

@[expose] public section

namespace Paucity

/-- `nu d H k`, the majorant weight `ν_{d,H}(k)`: equal to `H` at `k = 0` and `d/(2|k|)` away
from it. -/
noncomputable def nu (d H : ℕ) (k : ℤ) : ℝ :=
  if k = 0 then (H : ℝ) else (d : ℝ) / (2 * |(k : ℝ)|)

@[simp] theorem nu_zero (d H : ℕ) : nu d H 0 = (H : ℝ) := by simp [nu]

theorem nu_of_ne_zero {d H : ℕ} {k : ℤ} (hk : k ≠ 0) :
    nu d H k = (d : ℝ) / (2 * |(k : ℝ)|) := by simp [nu, hk]

theorem nu_nonneg (d H : ℕ) (k : ℤ) : 0 ≤ nu d H k := by
  unfold nu
  split
  · exact Nat.cast_nonneg H
  · positivity

end Paucity
