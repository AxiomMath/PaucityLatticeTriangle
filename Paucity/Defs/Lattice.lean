/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.LinearCombination

/-!
# Lattices in `ℝ²`

A *lattice* in `ℝ²` is a subgroup `Λ ⊆ ℝ²` for which there exist `v, w ∈ Λ`, linearly independent
over `ℝ`, such that every element of `Λ` is `a v + b w` for exactly one pair `(a,b) ∈ ℤ²`. Such a
pair `(v, w)` is a *basis* of `Λ`. In `ℝ²` linear independence of a pair is equivalent to the
nonvanishing of the determinant `v.1 w.2 - v.2 w.1`.

## Main definitions

* `IsBasis`: `(v, w)` is a basis of the subgroup `Λ ⊆ ℝ²`.
* `IsLattice`: the subgroup `Λ ⊆ ℝ²` admits a basis.

## Main results

* `linearIndependent_iff_det_ne_zero`: a pair in `ℝ²` is `ℝ`-linearly independent if and only if
  its determinant is nonzero.
* `IsBasis.det_ne_zero`: a basis has nonvanishing determinant.
* `IsBasis.exists_rep`: every element of `Λ` has an integer coordinate representation in a basis.
* `coords_injective`: integer coordinates against an independent pair are unique.
-/

@[expose] public section

namespace Paucity

/-- `(v, w)` is a basis of the subgroup `Λ ⊆ ℝ²`: both lie in `Λ`, they are
`ℝ`-linearly independent, and every element of `Λ` has a unique representation
`a v + b w` with `(a,b) ∈ ℤ²`. -/
structure IsBasis (Λ : AddSubgroup (ℝ × ℝ)) (v w : ℝ × ℝ) : Prop where
  mem_left : v ∈ Λ
  mem_right : w ∈ Λ
  indep : LinearIndependent ℝ ![v, w]
  unique_rep : ∀ x ∈ Λ, ∃! ab : ℤ × ℤ, x = (ab.1 : ℝ) • v + (ab.2 : ℝ) • w

/-- `IsLattice Λ`: the subgroup `Λ` is a lattice in `ℝ²`, that is, it admits a basis. -/
def IsLattice (Λ : AddSubgroup (ℝ × ℝ)) : Prop := ∃ v w, IsBasis Λ v w

/-- In `ℝ²`, linear independence of a pair is nonvanishing of the determinant. -/
theorem linearIndependent_iff_det_ne_zero {v w : ℝ × ℝ} :
    LinearIndependent ℝ ![v, w] ↔ v.1 * w.2 - v.2 * w.1 ≠ 0 := by
  have hcomp : ∀ s t : ℝ,
      s • v + t • w = 0 ↔ (s * v.1 + t * w.1 = 0 ∧ s * v.2 + t * w.2 = 0) := by
    intro s t
    rw [Prod.ext_iff]
    simp [smul_eq_mul]
  rw [LinearIndependent.pair_iff]
  constructor
  · intro h hdet
    rcases eq_or_ne v 0 with rfl | hv
    · exact absurd (h 1 0 (by simp)).1 one_ne_zero
    obtain ⟨-, h1⟩ := h w.1 (-v.1) ((hcomp _ _).mpr ⟨by ring, by linear_combination -hdet⟩)
    obtain ⟨-, h2⟩ := h w.2 (-v.2) ((hcomp _ _).mpr ⟨by linear_combination hdet, by ring⟩)
    exact hv (Prod.ext (by simpa using neg_eq_zero.mp h1) (by simpa using neg_eq_zero.mp h2))
  · intro hdet s t hst
    obtain ⟨h1, h2⟩ := (hcomp s t).mp hst
    have hs : s * (v.1 * w.2 - v.2 * w.1) = 0 := by linear_combination w.2 * h1 - w.1 * h2
    have ht : t * (v.1 * w.2 - v.2 * w.1) = 0 := by linear_combination v.1 * h2 - v.2 * h1
    exact ⟨by simpa [hdet] using hs, by simpa [hdet] using ht⟩

/-- A basis has nonvanishing determinant. -/
theorem IsBasis.det_ne_zero {Λ : AddSubgroup (ℝ × ℝ)} {v w : ℝ × ℝ}
    (hb : IsBasis Λ v w) : v.1 * w.2 - v.2 * w.1 ≠ 0 :=
  linearIndependent_iff_det_ne_zero.mp hb.indep

/-- The representation supplied by a basis, as a plain existence statement. -/
theorem IsBasis.exists_rep {Λ : AddSubgroup (ℝ × ℝ)} {v w : ℝ × ℝ}
    (hb : IsBasis Λ v w) {x : ℝ × ℝ} (hx : x ∈ Λ) :
    ∃ ab : ℤ × ℤ, x = (ab.1 : ℝ) • v + (ab.2 : ℝ) • w :=
  (hb.unique_rep x hx).exists

/-- Two integer coordinate pairs giving the same point against an `ℝ`-linearly independent pair
`v, w` are equal. -/
theorem coords_injective {v w : ℝ × ℝ} (h : LinearIndependent ℝ ![v, w])
    {a b a' b' : ℤ} (heq : (a : ℝ) • v + (b : ℝ) • w = (a' : ℝ) • v + (b' : ℝ) • w) :
    a = a' ∧ b = b' := by
  have hz : ((a : ℝ) - (a' : ℝ)) • v + ((b : ℝ) - (b' : ℝ)) • w = 0 := by
    rw [sub_smul, sub_smul]
    rw [sub_add_sub_comm, heq, sub_self]
  obtain ⟨h1, h2⟩ := h.eq_zero_of_pair hz
  exact ⟨by exact_mod_cast sub_eq_zero.mp h1, by exact_mod_cast sub_eq_zero.mp h2⟩

end Paucity
