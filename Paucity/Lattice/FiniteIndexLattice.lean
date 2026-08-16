/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.IndexNSmul
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.FreeModule.Int
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring
public import Paucity.Defs.Lattice

/-!
# Finite-index subgroups of `ℤ²` are lattices in `ℝ²`

If `Λ ⊆ ℤ²` is a subgroup of finite index, then its image in `ℝ²` under the coordinatewise cast is
a lattice in the sense of `Paucity.IsLattice`.

## Main definitions

* `intPairCast`: the coordinatewise cast `ℤ² → ℝ²`, as an additive group homomorphism.

## Main results

* `finrank_int_prod`: `ℤ²` has `ℤ`-rank `2`.
* `isLattice_map_intPairCast`: the image under `intPairCast` of a subgroup of `ℤ²` of finite index
  is a lattice.
-/

@[expose] public section

namespace Paucity

/-- The coordinatewise cast `ℤ² → ℝ²`, as an additive group homomorphism. -/
def intPairCast : (ℤ × ℤ) →+ (ℝ × ℝ) where
  toFun p := ((p.1 : ℝ), (p.2 : ℝ))
  map_zero' := by simp
  map_add' p q := by simp

/-- `intPairCast` applied to a pair, unfolded. -/
theorem intPairCast_apply (p : ℤ × ℤ) :
    intPairCast p = ((p.1 : ℝ), (p.2 : ℝ)) := rfl

theorem intPairCast_injective : Function.Injective intPairCast := by
  intro p q h
  have h' : ((p.1 : ℝ), (p.2 : ℝ)) = ((q.1 : ℝ), (q.2 : ℝ)) := h
  rw [Prod.mk.injEq] at h'
  exact Prod.ext (by exact_mod_cast h'.1) (by exact_mod_cast h'.2)

/-- `ℤ²` has `ℤ`-rank `2`. -/
theorem finrank_int_prod : Module.finrank ℤ (ℤ × ℤ) = 2 := by
  simp [Module.finrank_prod]

/-- **Finite index gives a lattice.** If `Λ ⊆ ℤ²` is a subgroup of finite index (`Λ.index ≠ 0`),
then its image in `ℝ²` under the coordinatewise cast is a lattice: it has a basis in the sense of
`Paucity.IsBasis`. -/
theorem isLattice_map_intPairCast (Λ : AddSubgroup (ℤ × ℤ)) (hΛ : Λ.index ≠ 0) :
    IsLattice (Λ.map intPairCast) := by
  haveI : Λ.FiniteIndex := ⟨hΛ⟩
  haveI : Module.Finite ℤ ↥Λ := by
    have : Module.Finite ℤ ↥Λ.toIntSubmodule := inferInstance
    exact this
  haveI : Module.Free ℤ ↥Λ := by
    have : Module.Free ℤ ↥Λ.toIntSubmodule := inferInstance
    exact this
  have h2 : Module.finrank ℤ ↥Λ = 2 := by
    rw [AddSubgroup.finrank_eq_of_finiteIndex Λ, finrank_int_prod]
  set b := Module.finBasisOfFinrankEq ℤ ↥Λ h2
  set v : ℝ × ℝ := intPairCast ((b 0 : ↥Λ) : ℤ × ℤ) with hv
  set w : ℝ × ℝ := intPairCast ((b 1 : ↥Λ) : ℤ × ℤ) with hw
  have key : ∀ y : ↥Λ, intPairCast (y : ℤ × ℤ)
      = ((b.repr y 0 : ℤ) : ℝ) • v + ((b.repr y 1 : ℤ) : ℝ) • w := by
    intro y
    have hy : (b.repr y 0) • b 0 + (b.repr y 1) • b 1 = y := by
      have := b.sum_repr y
      rwa [Fin.sum_univ_two] at this
    have : intPairCast (y : ℤ × ℤ)
        = (b.repr y 0) • v + (b.repr y 1) • w := by
      rw [hv, hw, ← map_zsmul, ← map_zsmul, ← map_add]
      congr 1
      rw [← AddSubgroup.coe_zsmul, ← AddSubgroup.coe_zsmul, ← AddSubgroup.coe_add, hy]
    rw [this, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
  have comp : ∀ (p : ℤ × ℤ) (s t : ℝ), intPairCast p = s • v + t • w →
      ((p.1 : ℝ) = s * v.1 + t * w.1 ∧ (p.2 : ℝ) = s * v.2 + t * w.2) := by
    intro p s t h
    rw [intPairCast_apply, Prod.ext_iff] at h
    simpa using h
  set m := Λ.index with hmdef
  have hp1 : (((m : ℤ)), (0 : ℤ)) ∈ Λ := by
    have h := Λ.nsmul_index_mem ((1 : ℤ), (0 : ℤ))
    simpa [hmdef] using h
  have hp2 : ((0 : ℤ), ((m : ℤ))) ∈ Λ := by
    have h := Λ.nsmul_index_mem ((0 : ℤ), (1 : ℤ))
    simpa [hmdef] using h
  obtain ⟨E1, E2⟩ := comp _ _ _ (key ⟨_, hp1⟩)
  obtain ⟨E3, E4⟩ := comp _ _ _ (key ⟨_, hp2⟩)
  set a := ((b.repr ⟨_, hp1⟩ 0 : ℤ) : ℝ)
  set b' := ((b.repr ⟨_, hp1⟩ 1 : ℤ) : ℝ)
  set c := ((b.repr ⟨_, hp2⟩ 0 : ℤ) : ℝ)
  set d := ((b.repr ⟨_, hp2⟩ 1 : ℤ) : ℝ)
  have hD : (m : ℝ) * (m : ℝ) = (a * d - b' * c) * (v.1 * w.2 - v.2 * w.1) := by
    push_cast at E1 E2 E3 E4
    linear_combination (c * v.2 + d * w.2) * E1 - (c * v.1 + d * w.1) * E2 + (m : ℝ) * E4
  have hindep : LinearIndependent ℝ ![v, w] := by
    refine linearIndependent_iff_det_ne_zero.mpr fun h0 ↦ hΛ ?_
    rw [h0, mul_zero] at hD
    exact_mod_cast mul_self_eq_zero.mp hD
  refine ⟨v, w, ⟨AddSubgroup.mem_map_of_mem _ (b 0).2,
    AddSubgroup.mem_map_of_mem _ (b 1).2, hindep, ?_⟩⟩
  intro x hx
  rw [AddSubgroup.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨(b.repr ⟨y, hy⟩ 0, b.repr ⟨y, hy⟩ 1), key ⟨y, hy⟩, fun ab hab ↦ ?_⟩
  obtain ⟨h1, h2⟩ := coords_injective hindep (hab.symm.trans (key ⟨y, hy⟩))
  exact Prod.ext h1 h2

end Paucity
