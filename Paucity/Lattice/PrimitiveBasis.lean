/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Data.Int.GCD
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.Ring
public import Paucity.Defs.Lattice

/-!
# Primitive vectors extend to a basis

If `Λ ⊆ ℝ²` is a lattice and `w ∈ Λ \ {0}` is not `m` times an element of `Λ` for any integer
`m ≥ 2`, then there is `w' ∈ Λ` for which `(w, w')` is a basis of `Λ`.

## Main results

* `intCast_smul_add_intCast_smul_mem`: an integer combination of two elements of a subgroup of `ℝ²`
  lies in the subgroup.
* `exists_isBasis_of_not_proper_multiple`: a nonzero vector of a lattice that is not a proper
  integer multiple of another element is part of a basis.
-/

@[expose] public section

namespace Paucity

/-- An integer combination of two elements of a subgroup of `ℝ²` lies in the subgroup. -/
theorem intCast_smul_add_intCast_smul_mem {Λ : AddSubgroup (ℝ × ℝ)} {v₁ v₂ : ℝ × ℝ}
    (h₁ : v₁ ∈ Λ) (h₂ : v₂ ∈ Λ) (p q : ℤ) : (p : ℝ) • v₁ + (q : ℝ) • v₂ ∈ Λ := by
  rw [Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
  exact Λ.add_mem (Λ.zsmul_mem h₁ p) (Λ.zsmul_mem h₂ q)

/-- **Primitive vectors extend to a basis.** If `Λ ⊆ ℝ²` is a lattice and `w ∈ Λ` is nonzero and
not `m` times an element of `Λ` for any integer `m ≥ 2`, then `w` is part of a basis `(w, w')` of
`Λ`. -/
theorem exists_isBasis_of_not_proper_multiple {Λ : AddSubgroup (ℝ × ℝ)} (hΛ : IsLattice Λ)
    {w : ℝ × ℝ} (hw : w ∈ Λ) (hw0 : w ≠ 0)
    (hprim : ¬ ∃ v ∈ Λ, ∃ m : ℤ, 2 ≤ m ∧ w = (m : ℝ) • v) :
    ∃ w', IsBasis Λ w w' := by
  obtain ⟨v₁, v₂, hb⟩ := hΛ
  obtain ⟨⟨a, b⟩, hab⟩ := hb.exists_rep hw
  simp only at hab
  have hgcd : Int.gcd a b = 1 := by
    have hne : ¬ (a = 0 ∧ b = 0) := by
      rintro ⟨rfl, rfl⟩
      exact hw0 (by simpa using hab)
    have h0 : Int.gcd a b ≠ 0 := fun h ↦ hne (Int.gcd_eq_zero_iff.mp h)
    by_contra h1
    have h2 : (2 : ℤ) ≤ (Int.gcd a b : ℤ) := by omega
    obtain ⟨a', ha'⟩ := Int.gcd_dvd_left a b
    obtain ⟨b', hb'⟩ := Int.gcd_dvd_right a b
    have hA : (a : ℝ) = ((Int.gcd a b : ℤ) : ℝ) * (a' : ℝ) := by exact_mod_cast ha'
    have hB : (b : ℝ) = ((Int.gcd a b : ℤ) : ℝ) * (b' : ℝ) := by exact_mod_cast hb'
    refine hprim ⟨(a' : ℝ) • v₁ + (b' : ℝ) • v₂,
      intCast_smul_add_intCast_smul_mem hb.mem_left hb.mem_right a' b', Int.gcd a b, h2, ?_⟩
    rw [hab, hA, hB]
    module
  obtain ⟨c, d, hdet⟩ : ∃ c d : ℤ, a * d - b * c = 1 :=
    ⟨-Int.gcdB a b, Int.gcdA a b, by
      have h := Int.gcd_eq_gcd_ab a b
      rw [hgcd] at h
      push_cast at h
      linarith⟩
  have hdetR : (a : ℝ) * (d : ℝ) - (b : ℝ) * (c : ℝ) = 1 := by exact_mod_cast hdet
  set w' : ℝ × ℝ := (c : ℝ) • v₁ + (d : ℝ) • v₂ with hw'def
  have hw1 : w.1 = (a : ℝ) * v₁.1 + (b : ℝ) * v₂.1 := by rw [hab]; simp
  have hw2 : w.2 = (a : ℝ) * v₁.2 + (b : ℝ) * v₂.2 := by rw [hab]; simp
  have hindep : LinearIndependent ℝ ![w, w'] := by
    refine linearIndependent_iff_det_ne_zero.mpr ?_
    have hswap : w.1 * w'.2 - w.2 * w'.1 = v₁.1 * v₂.2 - v₁.2 * v₂.1 := by
      simp only [hw'def, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
        hw1, hw2]
      linear_combination (v₁.1 * v₂.2 - v₁.2 * v₂.1) * hdetR
    rw [hswap]
    exact hb.det_ne_zero
  have hrepr : ∀ x ∈ Λ, ∃ ab : ℤ × ℤ, x = (ab.1 : ℝ) • w + (ab.2 : ℝ) • w' := by
    intro x hx
    obtain ⟨⟨p, q⟩, hpq⟩ := hb.exists_rep hx
    simp only at hpq
    refine ⟨(d * p - c * q, a * q - b * p), ?_⟩
    have e₁ : ((d * p - c * q : ℤ) : ℝ) * (a : ℝ) + ((a * q - b * p : ℤ) : ℝ) * (c : ℝ)
        = (p : ℝ) := by push_cast; linear_combination (p : ℝ) * hdetR
    have e₂ : ((d * p - c * q : ℤ) : ℝ) * (b : ℝ) + ((a * q - b * p : ℤ) : ℝ) * (d : ℝ)
        = (q : ℝ) := by push_cast; linear_combination (q : ℝ) * hdetR
    rw [hpq, hab, hw'def, ← e₁, ← e₂]
    module
  refine ⟨w', hw, intCast_smul_add_intCast_smul_mem hb.mem_left hb.mem_right c d, hindep,
    fun x hx ↦ ?_⟩
  obtain ⟨ab₀, hab₀⟩ := hrepr x hx
  exact ⟨ab₀, hab₀, fun ab h ↦
    Prod.ext (coords_injective hindep (h.symm.trans hab₀)).1
      (coords_injective hindep (h.symm.trans hab₀)).2⟩

end Paucity
