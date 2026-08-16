/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Paucity.Defs.M
public import Paucity.Defs.S

/-!
# The discrepancy `E`

The real-valued difference $E_n(p,q) = S_n(p,q) - M_n(p,q)$ between the true witness count and its
expected value.

## Main definitions

* `E`: the difference `(S n p q : ℝ) - M n p q`.

## Main results

* `S_eq_M_add_E`: the witness count is its expected value plus the discrepancy.
-/

@[expose] public section

namespace Paucity

/-- `E n p q = S n p q - M n p q`, the quantity $E_n(p,q)$: the real-valued discrepancy between the
true witness count and its expected value. -/
noncomputable def E (n p q : ℕ) : ℝ := (S n p q : ℝ) - M n p q

/-- The witness count is its expected value plus the discrepancy. -/
theorem S_eq_M_add_E (n p q : ℕ) : (S n p q : ℝ) = M n p q + E n p q := by
  unfold E; ring

end Paucity
