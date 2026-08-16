/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Data.Nat.Basic

/-!
# The Veech-group lattice property

`Lat_n(p,q)` asserts that the triangle with angles `(pπ/n, qπ/n, (n-p-q)π/n)` unfolds to a
translation surface whose Veech group is a lattice in `SL₂(ℝ)`. It is treated as an abstract
predicate, bundled as the single field of a structure and never unfolded, so that every statement
resting on it is quantified over all such predicates.

## Main definitions

* `LatPred`: the data of a Veech-group lattice predicate `Lat : ℕ → ℕ → ℕ → Prop`.
-/

@[expose] public section

namespace Paucity

/-- `LatPred`: the data of a Veech-group lattice predicate. `P.Lat n p q` asserts that the triangle
with angles `(pπ/n, qπ/n, (n-p-q)π/n)` unfolds to a translation surface whose Veech group is a
lattice in `SL₂(ℝ)`. -/
structure LatPred where
  /-- `Lat n p q`: the triangle with angles `(pπ/n, qπ/n, (n-p-q)π/n)` has Veech group a lattice in
  `SL₂(ℝ)`. -/
  Lat : ℕ → ℕ → ℕ → Prop

end Paucity
