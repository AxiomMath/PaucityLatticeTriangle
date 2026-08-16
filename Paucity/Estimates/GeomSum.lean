/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.Field.GeomSum
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Data.Int.Interval
public import Mathlib.Tactic.GCongr
public import Paucity.Defs.Notation.E

/-!
# The geometric-series bound

For `d ≥ 2` and an integer `k` not divisible by `d`, the incomplete character sum
`∑_{x=1}^{H} e(-kx/d)` has norm at most `1 / |sin (π k / d)|`, uniformly in `H`.

## Main results

* `norm_sum_pow_succ_le_two_div`: `‖∑_{i<H} z^{i+1}‖ ≤ 2 / ‖z - 1‖` for `‖z‖ = 1` and `z ≠ 1`.
* `norm_e_sub_one`: `‖e x - 1‖ = 2 |sin (π x)|`.
* `norm_sum_e_le_one_div_abs_sin`: the incomplete character sum above is bounded by
  `1 / |sin (π k / d)|`.
-/

@[expose] public section

namespace Paucity

open Finset Real Complex

/-- The geometric-series bound at a ratio of unit modulus: if `‖z‖ = 1` and `z ≠ 1` then
`‖∑_{i<H} z^{i+1}‖ ≤ 2 / ‖z - 1‖`. -/
theorem norm_sum_pow_succ_le_two_div {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) (H : ℕ) :
    ‖∑ i ∈ range H, z ^ (i + 1)‖ ≤ 2 / ‖z - 1‖ := by
  have hsub : (0 : ℝ) < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero_of_ne hz1)
  have hsum : ∑ i ∈ range H, z ^ (i + 1) = z * ((z ^ H - 1) / (z - 1)) := by
    rw [← geom_sum_eq hz1 H, mul_sum]
    exact sum_congr rfl fun i _ => by ring
  have hnum : ‖z ^ H - 1‖ ≤ 2 :=
    calc ‖z ^ H - 1‖ ≤ ‖z ^ H‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, hz]; norm_num
  rw [hsum, norm_mul, hz, one_mul, norm_div]
  gcongr

/-- The distance from `e x` to `1`, in terms of the sine: `‖e x - 1‖ = 2 |sin (π x)|`. -/
theorem norm_e_sub_one (x : ℝ) : ‖e x - 1‖ = 2 * |Real.sin (π * x)| := by
  have h : e x = Complex.exp (I * ((2 * π * x : ℝ) : ℂ)) := by
    unfold e
    congr 1
    push_cast
    ring
  rw [h, Complex.norm_exp_I_mul_ofReal_sub_one, show 2 * π * x / 2 = π * x by ring,
    Real.norm_eq_abs, abs_mul]
  norm_num

/-- The incomplete geometric sum of the character `e (-kx/d)` over `1 ≤ x ≤ H` is bounded by
`1 / |sin (π k / d)|`, uniformly in `H`.

The hypothesis `d ∤ k` forces `sin (π k / d) ≠ 0`, so the right-hand side is finite. -/
theorem norm_sum_e_le_one_div_abs_sin {d : ℕ} (hd : 2 ≤ d) (H : ℕ) {k : ℤ}
    (hk : ¬ ((d : ℤ) ∣ k)) :
    ‖∑ x ∈ Icc (1 : ℤ) (H : ℤ), e (-((k * x : ℤ) : ℝ) / (d : ℝ))‖
      ≤ 1 / |Real.sin (π * (k : ℝ) / (d : ℝ))| := by
  have hdpos : 0 < d := by omega
  have hz1 : e (-(k : ℝ) / (d : ℝ)) ≠ 1 := by
    intro hc
    refine hk (dvd_neg.mp ((e_intCast_div_eq_one_iff hdpos (-k)).mp ?_))
    rwa [Int.cast_neg]
  have hre : ∑ x ∈ Icc (1 : ℤ) (H : ℤ), e (-((k * x : ℤ) : ℝ) / (d : ℝ))
      = ∑ i ∈ range H, e (-(k : ℝ) / (d : ℝ)) ^ (i + 1) := by
    have himg : Icc (1 : ℤ) (H : ℤ) = (range H).image (fun i : ℕ => (i : ℤ) + 1) := by
      ext x
      simp only [mem_Icc, mem_image, mem_range]
      constructor
      · intro hx
        obtain ⟨hx1, hx2⟩ := hx
        exact ⟨(x - 1).toNat, by omega, by omega⟩
      · rintro ⟨i, hi, rfl⟩
        omega
    have hinj : ∀ a ∈ range H, ∀ b ∈ range H, ((a : ℤ) + 1) = ((b : ℤ) + 1) → a = b := by
      intro a _ b _ hab
      omega
    rw [himg, sum_image hinj]
    refine sum_congr rfl fun i _ => ?_
    rw [← e_nsmul]
    congr 1
    push_cast
    ring
  rw [hre]
  calc ‖∑ i ∈ range H, e (-(k : ℝ) / (d : ℝ)) ^ (i + 1)‖
      ≤ 2 / ‖e (-(k : ℝ) / (d : ℝ)) - 1‖ :=
        norm_sum_pow_succ_le_two_div (norm_e _) hz1 H
    _ = 1 / |Real.sin (π * (k : ℝ) / (d : ℝ))| := by
        rw [norm_e_sub_one, show π * (-(k : ℝ) / (d : ℝ)) = -(π * (k : ℝ) / (d : ℝ)) by ring,
          Real.sin_neg, abs_neg, ← div_div]
        norm_num

end Paucity
