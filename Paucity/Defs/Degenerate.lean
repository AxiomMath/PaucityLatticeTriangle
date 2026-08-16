/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Paucity.Defs.M
public import Paucity.Defs.Q

/-!
# Degenerate pairs

A pair `(p,q)` is degenerate for `n` when the expected witness count `M_n(p,q)` is at most
`1000 Q(n) max(gcd(p,n), gcd(q,n))`.

## Main definitions

* `Degenerate`: the predicate `M n p q ≤ 1000 * Q n * max (gcd p n) (gcd q n)`.

## Main results

* `degenerate_symm`: degeneracy is invariant under exchanging `p` and `q`.
-/

@[expose] public section

namespace Paucity

/-- `Degenerate n p q`: the pair `(p,q)` is degenerate for `n`, that is
`M_n(p,q) ≤ 1000 Q(n) max(gcd(p,n), gcd(q,n))`. -/
noncomputable def Degenerate (n p q : ℕ) : Prop :=
  M n p q ≤ 1000 * Q n * (max (Nat.gcd p n) (Nat.gcd q n) : ℝ)

theorem degenerate_iff {n p q : ℕ} :
    Degenerate n p q ↔ M n p q ≤ 1000 * Q n * (max (Nat.gcd p n) (Nat.gcd q n) : ℝ) :=
  Iff.rfl

theorem degenerate_symm {n p q : ℕ} : Degenerate n p q ↔ Degenerate n q p := by
  unfold Degenerate
  rw [M_symm, max_comm]

noncomputable instance decidableDegenerate (n p q : ℕ) : Decidable (Degenerate n p q) :=
  Classical.propDecidable _

end Paucity
