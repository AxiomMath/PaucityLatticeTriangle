/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Paucity.Defs.Notation.Res

/-!
# The initial-segment indicator

The `ℕ`-valued indicator `χ_{d,H}(x)` of the condition `1 ≤ [x]_d ≤ H` on the least nonnegative
residue of `x` modulo `d`. The lower endpoint is `1`, so the residue `0` is excluded.

## Main definitions

* `ind`: the indicator of `1 ≤ res x d ∧ res x d ≤ H`.

## Main results

* `ind_eq_one_iff`: `ind d H x = 1` exactly when `1 ≤ res x d ≤ H`.
* `ind_le_one`: `ind d H x ≤ 1`.
-/

@[expose] public section

namespace Paucity

/-- `ind d H x = χ_{d,H}(x)`, the indicator of `1 ≤ [x]_d ≤ H`. -/
def ind (d H : ℕ) (x : ℤ) : ℕ := if 1 ≤ res x d ∧ res x d ≤ H then 1 else 0

theorem ind_eq_one_iff {d H : ℕ} {x : ℤ} :
    ind d H x = 1 ↔ 1 ≤ res x d ∧ res x d ≤ H := by
  unfold ind; split <;> simp_all

theorem ind_le_one (d H : ℕ) (x : ℤ) : ind d H x ≤ 1 := by
  unfold ind; split <;> simp

end Paucity
