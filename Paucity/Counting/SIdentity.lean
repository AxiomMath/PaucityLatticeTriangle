/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Paucity.Defs.S
public import Paucity.Counting.ChiIff

/-!
# Indicator form of the witness count

For an obtuse pair `(p, q) ∈ T n`, the witness count `S n p q` is the sum over the units `a`
modulo `n` of the product of the two interval indicators at `ap` and at `aq`.

## Main results

* `S_eq_sum_ind`: `S n p q = ∑ a ∈ U n, ind n (h p) (a * p) * ind n (h q) (a * q)`.
-/

@[expose] public section

namespace Paucity

open Finset

/-- The witness count as a sum of indicator products. -/
theorem S_eq_sum_ind {n : ℕ} {pq : ℕ × ℕ} (hpq : pq ∈ T n) :
    S n pq.1 pq.2
      = ∑ a ∈ U n, ind n (h pq.1) ((a : ℤ) * pq.1) * ind n (h pq.2) ((a : ℤ) * pq.2) := by
  have hswap : pq.swap ∈ T n := swap_mem_T hpq
  unfold S
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  refine Finset.sum_congr rfl fun a ha => ?_
  have h1 := ind_eq_one_iff_res_lt hpq ha
  have h2 := ind_eq_one_iff_res_lt hswap ha
  rw [Prod.fst_swap] at h2
  by_cases hc1 : res ((a : ℤ) * pq.1) n < res (2 * (pq.1 : ℤ)) n
  · by_cases hc2 : res ((a : ℤ) * pq.2) n < res (2 * (pq.2 : ℤ)) n
    · rw [if_pos ⟨hc1, hc2⟩, h1.mpr hc1, h2.mpr hc2, one_mul]
    · rw [if_neg (by tauto)]
      have : ind n (h pq.2) ((a : ℤ) * pq.2) = 0 := by
        rcases Nat.lt_or_ge (ind n (h pq.2) ((a : ℤ) * pq.2)) 1 with hlt | hge
        · omega
        · exact absurd (h2.mp (le_antisymm (ind_le_one _ _ _) hge)) hc2
      rw [this, mul_zero]
  · rw [if_neg (by tauto)]
    have : ind n (h pq.1) ((a : ℤ) * pq.1) = 0 := by
      rcases Nat.lt_or_ge (ind n (h pq.1) ((a : ℤ) * pq.1)) 1 with hlt | hge
      · omega
      · exact absurd (h1.mp (le_antisymm (ind_le_one _ _ _) hge)) hc1
    rw [this, zero_mul]

end Paucity
