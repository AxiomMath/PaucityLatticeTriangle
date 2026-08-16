/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Data.Nat.Basic
public import Mathlib.Order.Monotone.Defs

/-!
# The doubling map

The map $h(t) = 2t - 1$ on `ℕ`, where the subtraction is truncated, so `h 0 = 0`.

## Main definitions

* `h`: the map `t ↦ 2 * t - 1` on `ℕ`.

## Main results

* `h_of_pos`: `h t + 1 = 2 * t` for `1 ≤ t`.
* `le_h`: `h` is inflationary on positive arguments.
* `h_pos`: `h` is positive on positive arguments.
* `h_monotone`: `h` is monotone.
-/

@[expose] public section

namespace Paucity

/-- `h t = 2t - 1`, the doubling map on `ℕ`. -/
def h (t : ℕ) : ℕ := 2 * t - 1

/-- At a positive argument `h` is `2t - 1` with no truncation. -/
theorem h_of_pos {t : ℕ} (ht : 1 ≤ t) : h t + 1 = 2 * t := by
  unfold h; omega

@[simp] theorem h_one : h 1 = 1 := rfl

/-- `h` is inflationary on positive arguments. -/
theorem le_h {t : ℕ} (ht : 1 ≤ t) : t ≤ h t := by
  unfold h; omega

/-- `h` is positive on positive arguments. -/
theorem h_pos {t : ℕ} (ht : 1 ≤ t) : 0 < h t := by
  unfold h; omega

theorem h_monotone : Monotone h := by
  intro a b hab
  unfold h
  omega

end Paucity
