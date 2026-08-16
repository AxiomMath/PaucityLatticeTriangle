/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Paucity.Defs.Dn
public import Paucity.Defs.Hn
public import Paucity.Defs.Wd
public import Paucity.Majorant.NdFourier
public import Paucity.Estimates.FourierBound
public import Paucity.Estimates.FourierZero
public import Paucity.Counting.HSumLt

/-!
# The majorant at a single divisor

For `n ≥ 5`, `(p, q) ∈ H n` and `d ∈ D n`, the divisor-level count `Nd n d p q` differs
from the main term `Hd n d p * Hd n d q / d` by at most the majorant `W n d p q`. The main
term is the `(0, 0)` frequency of the Fourier expansion of `Nd n d p q`, and the remaining
frequencies are dominated coefficient by coefficient by the majorant weights `nu`. The
divisor `d = 1`, which occurs whenever `n` is squarefree, is included: there all three
quantities vanish and the assertion reads `|0 - 0| ≤ 0`.

## Main results

* `Hd_le_sub_one`: `Hd n d t ≤ d - 1` when `h t < n`.
* `Hd_one_eq_zero`, `Nd_one_eq_zero`, `W_one_eq_zero`: the window, the count and the
  majorant all vanish at `d = 1`.
* `norm_dft_ind_le_nu_div`: the Fourier coefficients of the window indicator are bounded
  by `nu d H k / d` at every `k ∈ F d`.
* `filter_eq_erase_zero`: the punctured lattice box is the lattice box with the origin
  erased.
* `abs_Nd_sub_le_W`: `|Nd n d p q - Hd n d p * Hd n d q / d| ≤ W n d p q`.
-/

@[expose] public section

namespace Paucity

open Finset

/-- The window length is at most `d - 1` when `h t < n`: from `h t * d < n * d` it follows
that `⌊h(t)d/n⌋ < d`. -/
theorem Hd_le_sub_one {n d t : ℕ} (hd : 0 < d) (ht : h t < n) : Hd n d t ≤ d - 1 := by
  have hlt : h t * d < n * d := mul_lt_mul_of_pos_right ht hd
  have hdiv : h t * d / n < d := Nat.div_lt_of_lt_mul hlt
  unfold Hd
  omega

/-- At `d = 1` the window is empty: `⌊h(t)/n⌋ = 0` since `h t < n`. -/
theorem Hd_one_eq_zero {n t : ℕ} (ht : h t < n) : Hd n 1 t = 0 := by
  have := Hd_le_sub_one (n := n) (d := 1) (t := t) Nat.one_pos ht
  omega

/-- At `d = 1` the count vanishes: the defining condition asks for
`1 ≤ [bp]_1`, but every residue mod `1` is `0`. -/
theorem Nd_one_eq_zero (n p q : ℕ) : Nd n 1 p q = 0 := by
  unfold Nd
  rw [card_eq_zero, filter_eq_empty_iff]
  intro b _
  have hres : res ((b : ℤ) * p) 1 = 0 := Nat.lt_one_iff.mp (res_lt Nat.one_pos)
  rw [hres]
  omega

/-- At `d = 1` the majorant vanishes: `F 1 = {0}`, so every point of
`latticeBox 1 p q` is the origin and the punctured index set is empty. -/
theorem W_one_eq_zero (n p q : ℕ) : W n 1 p q = 0 := by
  have hempty : ((latticeBox 1 p q).filter fun kl => kl ≠ (0, 0)) = ∅ := by
    rw [filter_eq_empty_iff]
    intro kl hkl
    obtain ⟨⟨h1, h2⟩, -⟩ := mem_latticeBox.mp hkl
    rw [F_one, mem_singleton] at h1 h2
    simp only [ne_eq, not_not, Prod.ext_iff]
    exact ⟨h1, h2⟩
  unfold W
  rw [hempty, sum_empty, mul_zero]

/-- The uniform coefficient bound `‖χ̂_{d,H}^{(d)}(k)‖ ≤ ν_{d,H}(k)/d`, valid at every
`k ∈ F d`. It is an equality at `k = 0`, where `nu d H 0 = H`, and away from `0` the right
side is `1/(2|k|)`. -/
theorem norm_dft_ind_le_nu_div {d H : ℕ} (hd : 2 ≤ d) (hH : H ≤ d - 1) {k : ℤ}
    (hk : k ∈ F d) :
    ‖dft d (fun x => (ind d H x : ℂ)) k‖ ≤ nu d H k / (d : ℝ) := by
  have hd0 : 0 < d := by omega
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
  by_cases hk0 : k = 0
  · subst hk0
    rw [dft_ind_zero hd0 hH, nu_zero, norm_div, Complex.norm_natCast, Complex.norm_natCast]
  · rw [nu_of_ne_zero hk0]
    calc ‖dft d (fun x => (ind d H x : ℂ)) k‖
        ≤ 1 / (2 * |(k : ℝ)|) := norm_dft_ind_le hd hH hk hk0
      _ = (d : ℝ) / (2 * |(k : ℝ)|) / (d : ℝ) := by
          rw [div_right_comm, div_self hdR.ne']

/-- The punctured index set of `W` is the lattice box with the origin erased. -/
theorem filter_eq_erase_zero (d p q : ℕ) :
    ((latticeBox d p q).filter fun kl => kl ≠ (0, 0)) = (latticeBox d p q).erase (0, 0) := by
  ext kl
  rw [mem_filter, mem_erase]
  exact and_comm

/-- The majorant bound at a single divisor: for `n ≥ 5`, `(p, q) ∈ H n` and `d ∈ D n`,

    |Nd n d p q - Hd n d p * Hd n d q / d| ≤ W n d p q,

the subtracted term being the `(0, 0)` frequency of the Fourier expansion of
`Nd n d p q`. The divisor `d = 1` is included, where all three quantities are `0`. -/
theorem abs_Nd_sub_le_W {n p q d : ℕ} (hn : 5 ≤ n) (hpq : (p, q) ∈ H n) (hd : d ∈ D n) :
    |(Nd n d p q : ℝ) - (Hd n d p : ℝ) * (Hd n d q : ℝ) / (d : ℝ)| ≤ W n d p q := by
  have hn0 : 0 < n := by omega
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos (dvd_of_mem_D hd) hn0
  have hsum : h p + h q < n := h_add_h_lt (H_subset_T n hpq)
  have hHp : Hd n d p ≤ d - 1 := Hd_le_sub_one hd0 (by omega)
  have hHq : Hd n d q ≤ d - 1 := Hd_le_sub_one hd0 (by omega)
  by_cases hd2 : 2 ≤ d
  · have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
    have hdC : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd0.ne'
    have hzero :
        dft d (fun x => (ind d (Hd n d p) x : ℂ)) ((0, 0) : ℤ × ℤ).1 *
            dft d (fun x => (ind d (Hd n d q) x : ℂ)) ((0, 0) : ℤ × ℤ).2
          = (Hd n d p : ℂ) * (Hd n d q : ℂ) / ((d : ℂ) * (d : ℂ)) := by
      change dft d (fun x => (ind d (Hd n d p) x : ℂ)) 0 *
          dft d (fun x => (ind d (Hd n d q) x : ℂ)) 0 = _
      rw [dft_ind_zero hd0 hHp, dft_ind_zero hd0 hHq, div_mul_div_comm]
    have hsplit :
        (Nd n d p q : ℂ) - (Hd n d p : ℂ) * (Hd n d q : ℂ) / (d : ℂ)
          = (d : ℂ) * ∑ kl ∈ (latticeBox d p q).filter fun kl => kl ≠ (0, 0),
              dft d (fun x => (ind d (Hd n d p) x : ℂ)) kl.1 *
                dft d (fun x => (ind d (Hd n d q) x : ℂ)) kl.2 := by
      rw [filter_eq_erase_zero, Nd_eq_fourier hd2,
        ← Finset.add_sum_erase _ _ (zero_mem_latticeBox hd0), hzero]
      field_simp
      ring
    have habs : |(Nd n d p q : ℝ) - (Hd n d p : ℝ) * (Hd n d q : ℝ) / (d : ℝ)|
        = ‖(Nd n d p q : ℂ) - (Hd n d p : ℂ) * (Hd n d q : ℂ) / (d : ℂ)‖ := by
      rw [show ((Nd n d p q : ℂ) - (Hd n d p : ℂ) * (Hd n d q : ℂ) / (d : ℂ))
            = (((Nd n d p q : ℝ) - (Hd n d p : ℝ) * (Hd n d q : ℝ) / (d : ℝ) : ℝ) : ℂ) by
          push_cast
          ring,
        Complex.norm_real, Real.norm_eq_abs]
    rw [habs, hsplit, norm_mul, Complex.norm_natCast]
    unfold W
    calc (d : ℝ) * ‖∑ kl ∈ (latticeBox d p q).filter fun kl => kl ≠ (0, 0),
              dft d (fun x => (ind d (Hd n d p) x : ℂ)) kl.1 *
                dft d (fun x => (ind d (Hd n d q) x : ℂ)) kl.2‖
        ≤ (d : ℝ) * ∑ kl ∈ (latticeBox d p q).filter fun kl => kl ≠ (0, 0),
              ‖dft d (fun x => (ind d (Hd n d p) x : ℂ)) kl.1 *
                dft d (fun x => (ind d (Hd n d q) x : ℂ)) kl.2‖ :=
          mul_le_mul_of_nonneg_left (norm_sum_le _ _) hdR.le
      _ ≤ (d : ℝ) * ∑ kl ∈ (latticeBox d p q).filter fun kl => kl ≠ (0, 0),
              nu d (Hd n d p) kl.1 / (d : ℝ) * (nu d (Hd n d q) kl.2 / (d : ℝ)) := by
          refine mul_le_mul_of_nonneg_left (sum_le_sum fun kl hkl => ?_) hdR.le
          obtain ⟨⟨hk1, hk2⟩, -⟩ := mem_latticeBox.mp (mem_of_mem_filter kl hkl)
          rw [norm_mul]
          exact mul_le_mul (norm_dft_ind_le_nu_div hd2 hHp hk1)
            (norm_dft_ind_le_nu_div hd2 hHq hk2) (norm_nonneg _)
            (div_nonneg (nu_nonneg _ _ _) hdR.le)
      _ = 1 / (d : ℝ) * ∑ kl ∈ (latticeBox d p q).filter fun kl => kl ≠ (0, 0),
              nu d (Hd n d p) kl.1 * nu d (Hd n d q) kl.2 := by
          rw [mul_sum, mul_sum]
          refine sum_congr rfl fun kl _ => ?_
          field_simp
  · have hd1 : d = 1 := by omega
    subst hd1
    rw [W_one_eq_zero, Nd_one_eq_zero, Hd_one_eq_zero (by omega),
      Hd_one_eq_zero (n := n) (t := q) (by omega)]
    simp

end Paucity
