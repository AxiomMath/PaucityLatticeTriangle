/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Push
public import Paucity.Defs.Notation.Res
public import Paucity.Defs.Tn

/-!
# Doubling is residue-free

For an obtuse pair `(p, q) ∈ T n` the doubled first coordinate `2p` is smaller than the modulus
`n`, hence is its own residue modulo `n`.

## Main results

* `res_two_mul`: `res (2 * p) n = 2 * p` for `(p, q) ∈ T n`.
-/

@[expose] public section

namespace Paucity

/-- Obtuseness makes `2p` its own residue. -/
theorem res_two_mul {n : ℕ} {pq : ℕ × ℕ} (hpq : pq ∈ T n) :
    res (2 * (pq.1 : ℤ)) n = 2 * pq.1 := by
  rw [mem_T] at hpq
  have hlt : 2 * pq.1 < n := by omega
  have : (2 * (pq.1 : ℤ)) = ((2 * pq.1 : ℕ) : ℤ) := by push_cast; ring
  rw [this, res_natCast]
  exact Nat.mod_eq_of_lt hlt

end Paucity
