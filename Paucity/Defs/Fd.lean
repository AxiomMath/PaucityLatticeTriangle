/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Data.Int.Interval

/-!
# Symmetric residue representatives

The representatives of `ZMod d` of least absolute value,
$\mathcal F_d = \{j \in \mathbb Z : -d < 2j \le d\}$. For `j` in this set `|j|` is the distance
from `j` to `0` modulo `d`.

## Main definitions

* `F`: the representatives of `ZMod d` of least absolute value.

## Main results

* `two_mul_abs_le_of_mem_F`: elements of `F d` satisfy `2 * |j| ≤ d`.
* `F_zero`: `F 0 = ∅`.
* `F_one`: `F 1 = {0}`.
-/

@[expose] public section

namespace Paucity

open Finset

/-- `F d`, the set $\mathcal F_d$: the representatives of `ZMod d` of least absolute value,
`-d < 2j ≤ d`. -/
def F (d : ℕ) : Finset ℤ :=
  (Icc (-(d : ℤ)) (d : ℤ)).filter fun j => -(d : ℤ) < 2 * j ∧ 2 * j ≤ (d : ℤ)

@[simp] theorem mem_F {d : ℕ} {j : ℤ} :
    j ∈ F d ↔ -(d : ℤ) < 2 * j ∧ 2 * j ≤ (d : ℤ) := by
  unfold F
  simp only [mem_filter, mem_Icc]
  constructor
  · rintro ⟨_, h⟩; exact h
  · rintro ⟨h1, h2⟩; exact ⟨⟨by omega, by omega⟩, h1, h2⟩

/-- Elements of `F d` have absolute value at most `d / 2`, so `|j|` is the distance from `j` to `0`
modulo `d`. -/
theorem two_mul_abs_le_of_mem_F {d : ℕ} {j : ℤ} (hj : j ∈ F d) : 2 * |j| ≤ (d : ℤ) := by
  rw [mem_F] at hj
  by_cases hpos : 0 ≤ j
  · rw [abs_of_nonneg hpos]; omega
  · rw [abs_of_neg (not_le.mp hpos)]; omega

theorem F_zero : F 0 = ∅ := by
  apply eq_empty_of_forall_notMem
  intro j hj
  rw [mem_F] at hj
  omega

theorem zero_mem_F {d : ℕ} (hd : 0 < d) : (0 : ℤ) ∈ F d := by
  rw [mem_F]
  omega

theorem F_one : F 1 = {0} := by
  ext j
  rw [mem_F, mem_singleton]
  omega

end Paucity
