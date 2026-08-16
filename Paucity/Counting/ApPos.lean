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
# Units do not annihilate

For a unit `a` modulo `n` and `1 ≤ p ≤ n - 1`, the residue of `ap` modulo `n` is nonzero.

## Main results

* `one_le_res_mul`: `1 ≤ res (a * p) n` for `a ∈ U n`, `1 ≤ p` and `p ≤ n - 1`.
-/

@[expose] public section

namespace Paucity

/-- A unit times a nonzero residue is a nonzero residue. -/
theorem one_le_res_mul {n a p : ℕ} (ha : a ∈ U n) (hp1 : 1 ≤ p) (hp2 : p ≤ n - 1) :
    1 ≤ res ((a : ℤ) * p) n := by
  have hn : 1 ≤ n := le_trans (pos_of_mem_U ha) (mem_U.mp ha).1.2
  have hcast : ((a : ℤ) * p) = ((a * p : ℕ) : ℤ) := by push_cast; ring
  rw [hcast, res_natCast]
  rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero]
  rcases Nat.eq_zero_or_pos (a * p % n) with hz | hpos
  · exfalso
    have hdvd : n ∣ a * p := Nat.dvd_of_mod_eq_zero hz
    have hcop : Nat.gcd n a = 1 := by rw [Nat.gcd_comm]; exact coprime_of_mem_U ha
    have hnp : n ∣ p := (Nat.Coprime.dvd_of_dvd_mul_left hcop hdvd)
    have := Nat.le_of_dvd (by omega) hnp
    omega
  · exact hpos

end Paucity
