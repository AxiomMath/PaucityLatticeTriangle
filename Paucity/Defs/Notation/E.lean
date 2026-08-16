/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Tactic.LinearCombination

/-!
# The additive character `e`

The standard additive character $e(x) = \exp(2\pi i x)$ of `ℝ`, as a complex-valued function
`ℝ → ℂ`. It is a homomorphism from addition to multiplication, has constant modulus `1`, and is
trivial exactly on the integers.

## Main definitions

* `e`: the additive character $e(x) = \exp(2\pi i x)$.

## Main results

* `e_add`: `e (x + y) = e x * e y`.
* `e_intCast`: `e` is trivial on the integers.
* `norm_e`: `‖e x‖ = 1`.
* `e_nsmul`: `e ((n : ℝ) * x) = e x ^ n`.
* `e_eq_one_iff`: `e x = 1` if and only if `x` is an integer.
* `e_intCast_div_eq_one_iff`: `e (m / d) = 1` if and only if `d ∣ m`.
-/

@[expose] public section

namespace Paucity

open Real Complex

/-- `e x = exp(2πix)`, the standard additive character of `ℝ`, complex-valued. -/
noncomputable def e (x : ℝ) : ℂ := Complex.exp (2 * π * I * x)

@[simp] theorem e_zero : e 0 = 1 := by simp [e]

/-- `e` is a character: it carries addition to multiplication. -/
theorem e_add (x y : ℝ) : e (x + y) = e x * e y := by
  unfold e
  rw [← Complex.exp_add]
  push_cast
  ring_nf

/-- `e` is trivial on the integers. -/
@[simp] theorem e_intCast (k : ℤ) : e (k : ℝ) = 1 := by
  unfold e
  rw [show (2 * (π : ℂ) * I * (k : ℝ)) = (k : ℂ) * (2 * π * I) by push_cast; ring]
  exact Complex.exp_int_mul_two_pi_mul_I k

@[simp] theorem norm_e (x : ℝ) : ‖e x‖ = 1 := by
  unfold e
  rw [Complex.norm_exp]
  simp

/-- Natural-number multiples of the argument come out as powers. -/
theorem e_nsmul (n : ℕ) (x : ℝ) : e ((n : ℝ) * x) = e x ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
    have : ((k : ℝ) + 1) * x = (k : ℝ) * x + x := by ring
    push_cast
    rw [this, e_add, ih, pow_succ]

/-- `e` is trivial **exactly** on the integers. -/
theorem e_eq_one_iff {x : ℝ} : e x = 1 ↔ ∃ k : ℤ, x = k := by
  unfold e
  rw [Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨k, hk⟩
    have h2 : (2 * (π : ℂ) * I) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    refine ⟨k, ?_⟩
    have hx : ((x : ℝ) : ℂ) = (k : ℂ) :=
      mul_left_cancel₀ h2 (by linear_combination hk)
    exact_mod_cast hx
  · rintro ⟨k, rfl⟩
    exact ⟨k, by push_cast; ring⟩

/-- `e (m/d) = 1` if and only if `d ∣ m`. -/
theorem e_intCast_div_eq_one_iff {d : ℕ} (hd : 0 < d) (m : ℤ) :
    e ((m : ℝ) / (d : ℝ)) = 1 ↔ (d : ℤ) ∣ m := by
  have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  rw [e_eq_one_iff]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have : (m : ℝ) = (d : ℝ) * (k : ℝ) := by field_simp at hk; linarith [hk]
    exact_mod_cast this
  · rintro ⟨k, rfl⟩
    exact ⟨k, by push_cast; field_simp⟩

end Paucity
