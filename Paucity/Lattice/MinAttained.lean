/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Data.Finite.Prod
public import Mathlib.Data.Set.Finite.Lemmas
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Paucity.Defs.Boxnorm
public import Paucity.Defs.Lambdamin
public import Paucity.Defs.Lattice

/-!
# The first minimum is attained

For reals `A, B > 0` and a lattice `Λ ⊆ ℝ²` there is `w ∈ Λ \ {0}` with `‖w‖_{A,B} = λ_{A,B}(Λ)`.

## Main results

* `IsBasis.left_ne_zero`: a basis vector is nonzero.
* `IsLattice.exists_ne_zero`: a lattice has a nonzero point.
* `normSet_nonempty`: for a lattice the set whose infimum defines `lambdaMin` is nonempty.
* `IsBasis.finite_setOf_boxNorm_le`: a box-norm ball meets a lattice in a finite set.
* `exists_boxNorm_eq_lambdaMin`: the infimum defining `λ_{A,B}(Λ)` is attained at a nonzero lattice
  point.
-/

@[expose] public section

namespace Paucity

/-- A basis vector is nonzero. -/
theorem IsBasis.left_ne_zero {Λ : AddSubgroup (ℝ × ℝ)} {v u : ℝ × ℝ}
    (hb : IsBasis Λ v u) : v ≠ 0 := by
  intro hv
  exact hb.det_ne_zero (by rw [hv]; simp)

/-- A lattice has a nonzero point. -/
theorem IsLattice.exists_ne_zero {Λ : AddSubgroup (ℝ × ℝ)} (hΛ : IsLattice Λ) :
    ∃ w ∈ Λ, w ≠ 0 := by
  obtain ⟨v, u, hb⟩ := hΛ
  exact ⟨v, hb.mem_left, hb.left_ne_zero⟩

/-- For a lattice the set whose infimum defines `lambdaMin` is nonempty. -/
theorem normSet_nonempty {A B : ℝ} {Λ : AddSubgroup (ℝ × ℝ)} (hΛ : IsLattice Λ) :
    (normSet A B Λ).Nonempty := by
  obtain ⟨w, hw, hw0⟩ := hΛ.exists_ne_zero
  exact ⟨boxNorm A B w, mem_normSet.mpr ⟨w, hw, hw0, rfl⟩⟩

/-- A box-norm ball meets `Λ` in a finite set. -/
theorem IsBasis.finite_setOf_boxNorm_le {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    {Λ : AddSubgroup (ℝ × ℝ)} {v u : ℝ × ℝ} (hb : IsBasis Λ v u) (r : ℝ) :
    {x : ℝ × ℝ | x ∈ Λ ∧ boxNorm A B x ≤ r}.Finite := by
  have hdpos : 0 < |v.1 * u.2 - v.2 * u.1| := abs_pos.mpr hb.det_ne_zero
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ x ∈ {x : ℝ × ℝ | x ∈ Λ ∧ boxNorm A B x ≤ r},
      ∀ ab : ℤ × ℤ, x = (ab.1 : ℝ) • v + (ab.2 : ℝ) • u →
        |(ab.1 : ℝ)| ≤ M ∧ |(ab.2 : ℝ)| ≤ M := by
    refine ⟨(|r| * A * |u.2| + |r| * B * |u.1| + |r| * B * |v.1| + |r| * A * |v.2|) /
      |v.1 * u.2 - v.2 * u.1|, ?_⟩
    rintro x ⟨-, hxr⟩ ab hx
    obtain ⟨hx1, hx2⟩ := abs_le_of_boxNorm_le hA hB hxr
    have hx1' : |x.1| ≤ |r| * A :=
      hx1.trans (mul_le_mul_of_nonneg_right (le_abs_self r) hA.le)
    have hx2' : |x.2| ≤ |r| * B :=
      hx2.trans (mul_le_mul_of_nonneg_right (le_abs_self r) hB.le)
    have e1 : x.1 = (ab.1 : ℝ) * v.1 + (ab.2 : ℝ) * u.1 := by rw [hx]; simp
    have e2 : x.2 = (ab.1 : ℝ) * v.2 + (ab.2 : ℝ) * u.2 := by rw [hx]; simp
    have tA : |x.1| * |u.2| ≤ |r| * A * |u.2| :=
      mul_le_mul_of_nonneg_right hx1' (abs_nonneg _)
    have tB : |x.2| * |u.1| ≤ |r| * B * |u.1| :=
      mul_le_mul_of_nonneg_right hx2' (abs_nonneg _)
    have tC : |x.2| * |v.1| ≤ |r| * B * |v.1| :=
      mul_le_mul_of_nonneg_right hx2' (abs_nonneg _)
    have tD : |x.1| * |v.2| ≤ |r| * A * |v.2| :=
      mul_le_mul_of_nonneg_right hx1' (abs_nonneg _)
    have p1 : (0 : ℝ) ≤ |r| * A * |u.2| := by positivity
    have p2 : (0 : ℝ) ≤ |r| * B * |u.1| := by positivity
    have p3 : (0 : ℝ) ≤ |r| * B * |v.1| := by positivity
    have p4 : (0 : ℝ) ≤ |r| * A * |v.2| := by positivity
    constructor
    · rw [le_div_iff₀ hdpos]
      have key : |(ab.1 : ℝ)| * |v.1 * u.2 - v.2 * u.1| = |x.1 * u.2 - x.2 * u.1| := by
        rw [← abs_mul]; congr 1; rw [e1, e2]; ring
      rw [key]
      calc |x.1 * u.2 - x.2 * u.1| ≤ |x.1 * u.2| + |x.2 * u.1| := abs_sub _ _
        _ = |x.1| * |u.2| + |x.2| * |u.1| := by rw [abs_mul, abs_mul]
        _ ≤ _ := by linarith
    · rw [le_div_iff₀ hdpos]
      have key : |(ab.2 : ℝ)| * |v.1 * u.2 - v.2 * u.1| = |x.2 * v.1 - x.1 * v.2| := by
        rw [← abs_mul]; congr 1; rw [e1, e2]; ring
      rw [key]
      calc |x.2 * v.1 - x.1 * v.2| ≤ |x.2 * v.1| + |x.1 * v.2| := abs_sub _ _
        _ = |x.2| * |v.1| + |x.1| * |v.2| := by rw [abs_mul, abs_mul]
        _ ≤ _ := by linarith
  refine Set.Finite.subset
    (((Set.finite_Icc (-⌈M⌉) ⌈M⌉).prod (Set.finite_Icc (-⌈M⌉) ⌈M⌉)).image
      fun ab : ℤ × ℤ => (ab.1 : ℝ) • v + (ab.2 : ℝ) • u) ?_
  intro x hx
  obtain ⟨ab, hab⟩ := hb.exists_rep hx.1
  obtain ⟨h1, h2⟩ := hM x hx ab hab
  have hceil : ∀ c : ℤ, |(c : ℝ)| ≤ M → c ∈ Set.Icc (-⌈M⌉) ⌈M⌉ := by
    intro c hc
    have : ((|c| : ℤ) : ℝ) ≤ ((⌈M⌉ : ℤ) : ℝ) := by
      rw [Int.cast_abs]; exact hc.trans (Int.le_ceil M)
    exact Set.mem_Icc.mpr (abs_le.mp (by exact_mod_cast this))
  exact ⟨ab, ⟨hceil _ h1, hceil _ h2⟩, hab.symm⟩

/-- The infimum defining `λ_{A,B}(Λ)` is attained at a nonzero lattice point. -/
theorem exists_boxNorm_eq_lambdaMin {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    {Λ : AddSubgroup (ℝ × ℝ)} (hΛ : IsLattice Λ) :
    ∃ w ∈ Λ, w ≠ 0 ∧ boxNorm A B w = lambdaMin A B Λ := by
  have hne : (normSet A B Λ).Nonempty := normSet_nonempty hΛ
  obtain ⟨v, u, hb⟩ := hΛ
  obtain ⟨s, hs, hslt⟩ : ∃ s ∈ normSet A B Λ, s < lambdaMin A B Λ + 1 :=
    exists_lt_of_csInf_lt hne (lt_add_one _)
  obtain ⟨w₀, hw₀, hw₀0, rfl⟩ := mem_normSet.mp hs
  have hfin : {x : ℝ × ℝ | x ∈ Λ ∧ x ≠ 0 ∧
      boxNorm A B x ≤ lambdaMin A B Λ + 1}.Finite :=
    (hb.finite_setOf_boxNorm_le hA hB (lambdaMin A B Λ + 1)).subset
      fun _ hx => ⟨hx.1, hx.2.2⟩
  obtain ⟨w, ⟨hwΛ, hw0, -⟩, hwmin⟩ :=
    Set.exists_min_image _ (boxNorm A B) hfin ⟨w₀, hw₀, hw₀0, hslt.le⟩
  refine ⟨w, hwΛ, hw0, le_antisymm (le_lambdaMin hne ?_) (lambdaMin_le hA B hwΛ hw0)⟩
  intro y hy hy0
  rcases le_or_gt (boxNorm A B y) (lambdaMin A B Λ + 1) with h | h
  · exact hwmin y ⟨hy, hy0, h⟩
  · exact (hwmin w₀ ⟨hw₀, hw₀0, hslt.le⟩).trans (hslt.le.trans h.le)

end Paucity
