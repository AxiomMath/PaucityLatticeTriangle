/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.Field.GeomSum
public import Paucity.Defs.Lambda
public import Paucity.Defs.Notation.E

/-!
# Orthogonality on `ℤ/dℤ`

Summing the additive character `e(bm/d)` over a full period `b ∈ [1, d]` detects
divisibility: the sum is `d` when `d ∣ m` and `0` otherwise. At `m = kp + ℓq` this turns
membership of `(k, ℓ)` in the dual lattice `dualLattice d p q` into a character sum.

## Main results

* `sum_e_intCast_div`: `∑_{b=1}^{d} e(bm/d)` is `d` when `d ∣ m` and `0` otherwise.
* `sum_e_eq_ite`: the same sum at `m = kp + ℓq`, detecting `dualLattice d p q`.
-/

@[expose] public section

namespace Paucity

open Finset

/-- Orthogonality in its general form: summing `e (b m / d)` over a full period detects
`d ∣ m`, the sum being `d` when `d ∣ m` and `0` otherwise. -/
theorem sum_e_intCast_div {d : ℕ} (hd : 0 < d) (m : ℤ) :
    ∑ b ∈ Icc 1 d, e ((b : ℝ) * (m : ℝ) / (d : ℝ))
      = if (d : ℤ) ∣ m then (d : ℂ) else 0 := by
  have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  set ζ := e ((m : ℝ) / (d : ℝ)) with hζdef
  have hterm : ∀ b : ℕ, e ((b : ℝ) * (m : ℝ) / (d : ℝ)) = ζ ^ b := fun b => by
    rw [hζdef, ← e_nsmul]
    congr 1
    ring
  rw [sum_congr rfl fun b _ => hterm b]
  by_cases hdvd : (d : ℤ) ∣ m
  · have hz : ζ = 1 := by rw [hζdef]; exact (e_intCast_div_eq_one_iff hd m).mpr hdvd
    rw [if_pos hdvd, hz]
    simp [Nat.card_Icc]
  · rw [if_neg hdvd]
    have hζ1 : ζ ≠ 1 := fun h => hdvd ((e_intCast_div_eq_one_iff hd m).mp h)
    have hζd : ζ ^ d = 1 := by
      rw [hζdef, ← e_nsmul, show (d : ℝ) * ((m : ℝ) / (d : ℝ)) = (m : ℝ) by field_simp]
      exact e_intCast m
    have hshift : ∑ b ∈ Icc 1 d, ζ ^ b = ζ * ∑ i ∈ range d, ζ ^ i := by
      rw [← Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range, Nat.add_sub_cancel, mul_sum]
      exact sum_congr rfl fun i _ => by rw [pow_add, pow_one]
    rw [hshift, geom_sum_eq hζ1 d, hζd]
    simp

/-- The dual lattice is detected by a character sum: `∑_{b=1}^{d} e(b(kp + ℓq)/d)` is `d`
when `(k, ℓ) ∈ dualLattice d p q` and `0` otherwise. -/
theorem sum_e_eq_ite {d p q : ℕ} (hd : 0 < d) (kl : ℤ × ℤ) :
    ∑ b ∈ Icc 1 d, e ((b : ℝ) * ((kl.1 * p + kl.2 * q : ℤ) : ℝ) / (d : ℝ))
      = if kl ∈ dualLattice d p q then (d : ℂ) else 0 := by
  by_cases h : kl ∈ dualLattice d p q
  · rw [if_pos h, sum_e_intCast_div hd, if_pos (mem_dualLattice.mp h)]
  · rw [if_neg h, sum_e_intCast_div hd, if_neg fun hc => h (mem_dualLattice.mpr hc)]

end Paucity
