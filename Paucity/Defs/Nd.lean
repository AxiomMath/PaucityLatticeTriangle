/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Paucity.Defs.Hd
public import Paucity.Defs.Ind
public import Paucity.Defs.Notation.Res
public import Paucity.Defs.Notation.Units

/-!
# The divisor-level count `Nd`

    N_d(n,p,q) = #{b : 1 ≤ b ≤ d, 1 ≤ [bp]_d ≤ H^(d)_n(p), 1 ≤ [bq]_d ≤ H^(d)_n(q)}.

The divisor-level analogue of the witness count: `b` runs over a full period `[1,d]` with no
coprimality condition, and both residues are taken modulo `d`. Both window conditions are
`1 ≤ [bp]_d`, so the residue `0` is excluded.

## Main definitions

* `Nd`: the divisor-level count `N_d(n,p,q)`.

## Main results

* `Nd_eq_sum_ind`: `N_d` is the sum over `[1,d]` of the product of the two window indicators.
* `Nd_le`: `N_d(n,p,q) ≤ d`.
* `Nd_symm`: `N_d` is symmetric in `p` and `q`.
-/

@[expose] public section

namespace Paucity

open Finset

/-- `Nd n d p q`, the count `N_d(n,p,q)`: the `b ∈ [1,d]` whose two residues both land in the
prescribed windows. -/
def Nd (n d p q : ℕ) : ℕ :=
  ((Icc 1 d).filter fun b : ℕ =>
    1 ≤ res ((b : ℤ) * p) d ∧ res ((b : ℤ) * p) d ≤ Hd n d p ∧
    1 ≤ res ((b : ℤ) * q) d ∧ res ((b : ℤ) * q) d ≤ Hd n d q).card

/-- `N_d` in indicator form: the count is the sum, over a full period, of the product of
the two window indicators. -/
theorem Nd_eq_sum_ind (n d p q : ℕ) :
    Nd n d p q
      = ∑ b ∈ Icc 1 d, ind d (Hd n d p) ((b : ℤ) * p) * ind d (Hd n d q) ((b : ℤ) * q) := by
  unfold Nd
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases hA : 1 ≤ res ((b : ℤ) * p) d ∧ res ((b : ℤ) * p) d ≤ Hd n d p
  · by_cases hB : 1 ≤ res ((b : ℤ) * q) d ∧ res ((b : ℤ) * q) d ≤ Hd n d q
    · simp only [ind, if_pos hA, if_pos hB, mul_one]
      rw [if_pos ⟨hA.1, hA.2, hB.1, hB.2⟩]
    · simp only [ind, if_pos hA, if_neg hB, mul_zero]
      rw [if_neg (by tauto)]
  · simp only [ind, if_neg hA, zero_mul]
    rw [if_neg (by tauto)]

theorem Nd_le (n d p q : ℕ) : Nd n d p q ≤ d := by
  unfold Nd
  calc _ ≤ (Icc 1 d).card := card_filter_le _ _
    _ = d := by rw [Nat.card_Icc, Nat.add_sub_cancel]

theorem Nd_symm (n d p q : ℕ) : Nd n d p q = Nd n d q p := by
  unfold Nd
  congr 1
  apply filter_congr
  intro b _
  constructor
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨h3, h4, h1, h2⟩
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨h3, h4, h1, h2⟩

end Paucity
