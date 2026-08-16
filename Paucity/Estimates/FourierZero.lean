/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Paucity.Defs.Fourier
public import Paucity.Defs.Ind

/-!
# The zeroth Fourier coefficient of the window indicator

For `1 ≤ d` and `H ≤ d - 1` the zeroth Fourier coefficient of the indicator of the window
`{1, …, H}` in `ℤ/dℤ` is `H/d`.

## Main results

* `res_eq_self`: on `0 ≤ x < d` the least nonnegative residue of `x` modulo `d` is `x`.
* `filter_eq_Icc`: the window condition cuts `Icc 1 d` down to `Icc 1 H`.
* `dft_ind_zero`: the zeroth Fourier coefficient of the window indicator is `H/d`.
-/

@[expose] public section

namespace Paucity

open Finset

/-- On `0 ≤ x < d` the least nonnegative residue is `x` itself. -/
theorem res_eq_self {x : ℤ} {d : ℕ} (h0 : 0 ≤ x) (hx : x < (d : ℤ)) :
    ((res x d : ℕ) : ℤ) = x := by
  unfold res
  rw [Int.emod_eq_of_lt h0 hx, Int.toNat_of_nonneg h0]

/-- The window picks out exactly `Icc 1 H`. -/
theorem filter_eq_Icc {d H : ℕ} (hd : 1 ≤ d) (hH : H ≤ d - 1) :
    ((Icc (1 : ℤ) (d : ℤ)).filter fun x => 1 ≤ res x d ∧ res x d ≤ H)
      = Icc (1 : ℤ) (H : ℤ) := by
  ext x
  simp only [mem_filter, mem_Icc]
  constructor
  · rintro ⟨⟨hx1, hxd⟩, hr1, hrH⟩
    have hxlt : x < (d : ℤ) := by
      rcases lt_or_eq_of_le hxd with h | h
      · exact h
      · rw [h] at hr1 ⊢
        simp only [res] at hr1
        rw [Int.emod_self] at hr1
        simp at hr1
    have hres : ((res x d : ℕ) : ℤ) = x := res_eq_self (by omega) hxlt
    refine ⟨hx1, ?_⟩
    omega
  · rintro ⟨hx1, hxH⟩
    have hHd : (H : ℤ) < (d : ℤ) := by
      have : H < d := by omega
      exact_mod_cast this
    have hxlt : x < (d : ℤ) := by omega
    have hres : ((res x d : ℕ) : ℤ) = x := res_eq_self (by omega) hxlt
    refine ⟨⟨hx1, by omega⟩, ?_, ?_⟩ <;> omega

/-- The zeroth Fourier coefficient of the window indicator is `H/d`. -/
theorem dft_ind_zero {d H : ℕ} (hd : 1 ≤ d) (hH : H ≤ d - 1) :
    dft d (fun x => (ind d H x : ℂ)) 0 = (H : ℂ) / (d : ℂ) := by
  rw [dft_zero]
  have hcount : ∑ x ∈ Icc (1 : ℤ) (d : ℤ), ind d H x = H := by
    unfold ind
    rw [← card_filter]
    rw [filter_eq_Icc hd hH, Int.card_Icc]
    simp
  have hsum : ∑ x ∈ Icc (1 : ℤ) (d : ℤ), ((ind d H x : ℕ) : ℂ) = (H : ℂ) := by
    rw [← Nat.cast_sum, hcount]
  rw [hsum]
  rw [one_div, inv_mul_eq_div]

end Paucity
