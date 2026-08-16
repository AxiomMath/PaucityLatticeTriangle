/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Push
public import Paucity.Defs.Notation.Res
public import Paucity.Defs.Notation.Units

/-!
# The witness count `S`

`S_n(p,q) = #{a ∈ U_n : [ap]_n < [2p]_n and [aq]_n < [2q]_n}`, the number of units mod `n` whose
two residues both fall below the corresponding window endpoint.

## Main definitions

* `S`: the witness count `S_n(p,q)`.

## Main results

* `S_le_totient`: `S_n(p,q) ≤ #U_n`.
-/

@[expose] public section

namespace Paucity

open Finset

/-- `S n p q`, the witness count $S_n(p,q)$: the units witnessing the criterion. -/
def S (n p q : ℕ) : ℕ :=
  ((U n).filter fun a : ℕ => res ((a : ℤ) * p) n < res (2 * (p : ℤ)) n
      ∧ res ((a : ℤ) * q) n < res (2 * (q : ℤ)) n).card

theorem S_le_totient (n p q : ℕ) : S n p q ≤ (U n).card := by
  unfold S; exact Finset.card_filter_le _ _

end Paucity
