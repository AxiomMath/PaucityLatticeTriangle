/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Paucity.Defs.Fd
public import Paucity.Defs.Fourier
public import Paucity.Defs.Ind
public import Paucity.Estimates.FourierZero
public import Paucity.Estimates.GeomSum
public import Paucity.Estimates.SinLower

/-!
# The nonzero Fourier coefficients of the window indicator

For `d ≥ 2` and `H ≤ d - 1`, the Fourier coefficients of the indicator of the window `{1, …, H}` in
`ℤ/dℤ` are bounded by `1 / (2 |k|)` at every nonzero frequency `k` with `2 |k| ≤ d`.

## Main results

* `abs_sin_abs`: the sine may be evaluated at `|y|` once absolute values are taken.
* `dft_ind_eq`: the transform of the window indicator is the character sum
  `(1 / d) * ∑_{x=1}^{H} e(-kx/d)`.
* `norm_dft_ind_le`: the coefficient at a nonzero `k ∈ F d` has norm at most `1 / (2 |k|)`.
-/

@[expose] public section

namespace Paucity

open Finset Real

/-- Absolute values inside and outside the sine agree: `abs (sin |y|) = |sin y|`. -/
theorem abs_sin_abs (y : ℝ) : abs (Real.sin |y|) = |Real.sin y| := by
  rcases abs_choice y with h | h
  · rw [h]
  · rw [h, Real.sin_neg, abs_neg]

/-- The transform of the window indicator is a pure character sum over the window:
`χ̂_{d,H}^{(d)}(k) = (1/d) ∑_{x=1}^{H} e(-kx/d)`. -/
theorem dft_ind_eq {d H : ℕ} (hd : 1 ≤ d) (hH : H ≤ d - 1) (k : ℤ) :
    dft d (fun x => (ind d H x : ℂ)) k
      = (1 / (d : ℂ)) * ∑ x ∈ Icc (1 : ℤ) (H : ℤ), e (-((k * x : ℤ) : ℝ) / (d : ℝ)) := by
  unfold dft
  congr 1
  rw [← filter_eq_Icc hd hH, sum_filter]
  refine sum_congr rfl fun x _ => ?_
  by_cases hx : 1 ≤ res x d ∧ res x d ≤ H <;> simp [ind, hx]

/-- Away from `k = 0` the Fourier coefficients of the window indicator are bounded by `1/(2|k|)`,
uniformly in the window length `H`.

Lemma 3.2 of *On the paucity of lattice triangles* asserts at these frequencies the stronger bound
`min (H/d) (w_d(k))`, where `w_d(k) = 1 / (2 min(k, d-k))`; only the `w_d(k)` half is stated here.
-/
theorem norm_dft_ind_le {d H : ℕ} (hd : 2 ≤ d) (hH : H ≤ d - 1) {k : ℤ}
    (hk : k ∈ F d) (hk0 : k ≠ 0) :
    ‖dft d (fun x => (ind d H x : ℂ)) k‖ ≤ 1 / (2 * |(k : ℝ)|) := by
  have hdR : (0 : ℝ) < (d : ℝ) := by
    have : 0 < d := by omega
    exact_mod_cast this
  have habs : 2 * |k| ≤ (d : ℤ) := two_mul_abs_le_of_mem_F hk
  have habsR : 2 * |(k : ℝ)| ≤ (d : ℝ) := by exact_mod_cast habs
  have hkposR : 0 < |(k : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr hk0)
  have hdvd : ¬ ((d : ℤ) ∣ k) := by
    intro hc
    have := Int.le_of_dvd (abs_pos.mpr hk0) ((dvd_abs _ _).mpr hc)
    omega
  have hkey : 2 * |(k : ℝ)| ≤ (d : ℝ) * |Real.sin (π * (k : ℝ) / (d : ℝ))| := by
    have hx0 : 0 ≤ |(k : ℝ)| / (d : ℝ) := by positivity
    have hxhalf : |(k : ℝ)| / (d : ℝ) ≤ 1 / 2 := by
      rw [div_le_iff₀ hdR]; linarith
    have hmin : min (|(k : ℝ)| / (d : ℝ)) (1 - |(k : ℝ)| / (d : ℝ))
        = |(k : ℝ)| / (d : ℝ) := min_eq_left (by linarith)
    have hsin := two_mul_min_le_abs_sin hx0 (by linarith)
    rw [hmin] at hsin
    have harg : π * (|(k : ℝ)| / (d : ℝ)) = |π * (k : ℝ) / (d : ℝ)| := by
      rw [abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hdR, mul_div_assoc]
    rw [harg, abs_sin_abs] at hsin
    calc 2 * |(k : ℝ)| = (d : ℝ) * (2 * (|(k : ℝ)| / (d : ℝ))) := by
          field_simp
      _ ≤ (d : ℝ) * |Real.sin (π * (k : ℝ) / (d : ℝ))| :=
          mul_le_mul_of_nonneg_left hsin hdR.le
  rw [dft_ind_eq (by omega) hH k, norm_mul, norm_div, norm_one, Complex.norm_natCast]
  calc 1 / (d : ℝ) * ‖∑ x ∈ Icc (1 : ℤ) (H : ℤ), e (-((k * x : ℤ) : ℝ) / (d : ℝ))‖
      ≤ 1 / (d : ℝ) * (1 / |Real.sin (π * (k : ℝ) / (d : ℝ))|) :=
        mul_le_mul_of_nonneg_left (norm_sum_e_le_one_div_abs_sin hd H hdvd) (by positivity)
    _ = 1 / ((d : ℝ) * |Real.sin (π * (k : ℝ) / (d : ℝ))|) := by
        rw [div_mul_div_comm]; norm_num
    _ ≤ 1 / (2 * |(k : ℝ)|) := one_div_le_one_div_of_le (by linarith) hkey

end Paucity
