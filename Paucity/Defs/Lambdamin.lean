/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Paucity.Defs.Boxnorm
public import Paucity.Defs.Lattice

/-!
# The box-norm minimum

For reals `A, B` and a subgroup `Λ` of `ℝ × ℝ`, the infimum
`λ_{A,B}(Λ) = inf {‖w‖_{A,B} : w ∈ Λ, w ≠ 0}` of the box norms of the nonzero points of `Λ`. On
`Λ = ⊥` the set is empty and the infimum is `0`.

## Main definitions

* `normSet`: the set of box norms of the nonzero points of `Λ`.
* `lambdaMin`: the infimum of `normSet A B Λ`.

## Main results

* `bddBelow_normSet`: for `0 < A` the set `normSet A B Λ` is bounded below.
* `lambdaMin_le`: `lambdaMin A B Λ` is at most the box norm of any nonzero point of `Λ`.
* `le_lambdaMin`: a lower bound for the box norms of the nonzero points of `Λ` bounds
  `lambdaMin A B Λ`, provided `normSet A B Λ` is nonempty.
* `lambdaMin_nonneg`: `lambdaMin A B Λ` is nonnegative.
-/

@[expose] public section

namespace Paucity

/-- The set of box norms of the nonzero points of `Λ`, the set whose infimum is `lambdaMin`. -/
def normSet (A B : ℝ) (Λ : AddSubgroup (ℝ × ℝ)) : Set ℝ :=
  (fun w => boxNorm A B w) '' {w : ℝ × ℝ | w ∈ Λ ∧ w ≠ 0}

/-- `lambdaMin A B Λ`, the quantity `λ_{A,B}(Λ)`: the infimum of `‖·‖_{A,B}` over the nonzero
points of `Λ`. -/
noncomputable def lambdaMin (A B : ℝ) (Λ : AddSubgroup (ℝ × ℝ)) : ℝ :=
  sInf (normSet A B Λ)

theorem mem_normSet {A B : ℝ} {Λ : AddSubgroup (ℝ × ℝ)} {r : ℝ} :
    r ∈ normSet A B Λ ↔ ∃ w ∈ Λ, w ≠ 0 ∧ boxNorm A B w = r := by
  unfold normSet
  constructor
  · rintro ⟨w, ⟨hw, hw0⟩, rfl⟩; exact ⟨w, hw, hw0, rfl⟩
  · rintro ⟨w, hw, hw0, rfl⟩; exact ⟨w, ⟨hw, hw0⟩, rfl⟩

/-- The box norms of the nonzero points of `Λ` are bounded below by `0`. -/
theorem bddBelow_normSet {A : ℝ} (hA : 0 < A) (B : ℝ) (Λ : AddSubgroup (ℝ × ℝ)) :
    BddBelow (normSet A B Λ) := by
  refine ⟨0, ?_⟩
  rintro r hr
  obtain ⟨w, -, -, rfl⟩ := mem_normSet.mp hr
  exact boxNorm_nonneg hA B w

/-- `lambdaMin` is a lower bound for the box norm of every nonzero point of `Λ`. -/
theorem lambdaMin_le {A : ℝ} (hA : 0 < A) (B : ℝ) {Λ : AddSubgroup (ℝ × ℝ)}
    {w : ℝ × ℝ} (hw : w ∈ Λ) (hw0 : w ≠ 0) :
    lambdaMin A B Λ ≤ boxNorm A B w :=
  csInf_le (bddBelow_normSet hA B Λ) (mem_normSet.mpr ⟨w, hw, hw0, rfl⟩)

/-- Any lower bound for the box norms of the nonzero points of `Λ` bounds `lambdaMin`, provided
there is at least one such point. -/
theorem le_lambdaMin {A B c : ℝ} {Λ : AddSubgroup (ℝ × ℝ)}
    (hne : (normSet A B Λ).Nonempty)
    (h : ∀ w ∈ Λ, w ≠ 0 → c ≤ boxNorm A B w) :
    c ≤ lambdaMin A B Λ := by
  refine le_csInf hne ?_
  rintro r hr
  obtain ⟨w, hw, hw0, rfl⟩ := mem_normSet.mp hr
  exact h w hw hw0

/-- `lambdaMin` is nonnegative; on the empty set `Real.sInf` is `0`. -/
theorem lambdaMin_nonneg {A : ℝ} (hA : 0 < A) (B : ℝ) (Λ : AddSubgroup (ℝ × ℝ)) :
    0 ≤ lambdaMin A B Λ := by
  rcases Set.eq_empty_or_nonempty (normSet A B Λ) with hempty | hne
  · unfold lambdaMin
    rw [hempty, Real.sInf_empty]
  · exact le_lambdaMin hne fun w _ _ => boxNorm_nonneg hA B w

end Paucity
