/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Paucity.Defs.Ind
public import Paucity.Defs.H
public import Paucity.Counting.TwoP
public import Paucity.Counting.ApPos
public import Paucity.Counting.HSumLt

/-!
# The indicator detects the criterion

For `(p, q) ∈ T n` and a unit `a` modulo `n`, the indicator of the interval `[1, h p]` at `ap`
equals `1` exactly when `[ap]_n < [2p]_n`.

## Main results

* `ind_eq_one_iff_res_lt`: `ind n (h p) (a * p) = 1 ↔ res (a * p) n < res (2 * p) n`.
-/

@[expose] public section

namespace Paucity

/-- The indicator of `[1, h p]` detects `[ap]_n < [2p]_n`. -/
theorem ind_eq_one_iff_res_lt {n a : ℕ} {pq : ℕ × ℕ} (hpq : pq ∈ T n)
    (ha : a ∈ U n) :
    ind n (h pq.1) ((a : ℤ) * pq.1) = 1 ↔ res ((a : ℤ) * pq.1) n < res (2 * (pq.1 : ℤ)) n := by
  have hmem := mem_T.mp hpq
  have h2p : res (2 * (pq.1 : ℤ)) n = 2 * pq.1 := res_two_mul hpq
  have hp1 : 1 ≤ pq.1 := hmem.1
  have hp2 : pq.1 ≤ n - 1 := by omega
  have hpos : 1 ≤ res ((a : ℤ) * pq.1) n := one_le_res_mul ha hp1 hp2
  rw [ind_eq_one_iff, h2p]
  constructor
  · intro hle
    have : res ((a : ℤ) * pq.1) n ≤ h pq.1 := hle.2
    unfold h at this
    omega
  · intro hlt
    refine ⟨hpos, ?_⟩
    unfold h
    omega

end Paucity
