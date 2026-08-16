/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Paucity.Defs.Hn
public import Paucity.Defs.Lat

/-!
# The lattice pairs `L`

`L_n = {(p,q) ∈ H_n : Lat_n(p,q)}`, the pairs of `H_n` whose associated triangle has Veech group
a lattice, cut out of `H_n` by an abstract lattice predicate.

## Main definitions

* `L`: the lattice pairs `L_n`, for a given lattice predicate.

## Main results

* `mem_L`: membership in `L_n`, unfolded into its two conditions.
* `L_subset_H`: `L n ⊆ H n`.
* `card_L_le_card_H`: `#L_n ≤ #H_n`.
-/

@[expose] public section

namespace Paucity

open Finset

open scoped Classical in
/-- `L P n`: the pairs of `H n` whose triangle has Veech group a lattice, for the lattice
predicate `P`. -/
noncomputable def L (P : LatPred) (n : ℕ) : Finset (ℕ × ℕ) :=
  (H n).filter fun pq => P.Lat n pq.1 pq.2

open scoped Classical in
@[simp] theorem mem_L {P : LatPred} {n : ℕ} {pq : ℕ × ℕ} :
    pq ∈ L P n ↔ pq ∈ H n ∧ P.Lat n pq.1 pq.2 := by
  unfold L; exact mem_filter

theorem L_subset_H (P : LatPred) (n : ℕ) : L P n ⊆ H n := fun _ h => (mem_L.mp h).1

theorem card_L_le_card_H (P : LatPred) (n : ℕ) : (L P n).card ≤ (H n).card :=
  card_le_card (L_subset_H P n)

end Paucity
