/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Paucity.Defs.Q
public import Paucity.Estimates.DivisorBound
public import Paucity.Estimates.TauGeTwoOmega

/-!
# `Q n ≤ C(ε) * n ^ ε`

For every `ε > 0` the divisor-density factor `Q n = 2 ^ ω(n) * (1 + log n) ^ 4` is at most
`C(ε) * n ^ ε` for every `n ≥ 2`.

## Main results

* `log_le_rpow_div`: `log x ≤ x ^ δ / δ` for `1 ≤ x` and `δ > 0`.
* `Q_small`: for every `ε > 0` there is `C > 0` with `Q n ≤ C * n ^ ε` for every `n ≥ 2`.
-/

@[expose] public section

namespace Paucity

/-- `log x ≤ x ^ δ / δ` for `1 ≤ x` and `δ > 0`. -/
theorem log_le_rpow_div {x δ : ℝ} (hx : 1 ≤ x) (hδ : 0 < δ) :
    Real.log x ≤ x ^ δ / δ := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hstep : δ * Real.log x ≤ x ^ δ := by
    have h1 : Real.log (x ^ δ) ≤ x ^ δ - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_rpow hx0] at h1
    linarith
  rw [le_div_iff₀ hδ, mul_comm]
  exact hstep

/-- `Q n ≤ C(ε) * n ^ ε` for every `n ≥ 2`, with a constant depending only on `ε > 0`. -/
theorem Q_small {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n → Q n ≤ C * (n : ℝ) ^ ε := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := divisor_bound (ε := ε / 2) (by linarith)
  set δ : ℝ := ε / 8 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  refine ⟨C₁ * (1 + 1 / δ) ^ 4, by positivity, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := by omega
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hrpow : (1 : ℝ) ≤ (n : ℝ) ^ δ := Real.one_le_rpow hnR (le_of_lt hδ)
  have hfac1 : (2 : ℝ) ^ n.primeFactors.card ≤ C₁ * (n : ℝ) ^ (ε / 2) := by
    have h1 : ((2 ^ n.primeFactors.card : ℕ) : ℝ) ≤ ((n.divisors.card : ℕ) : ℝ) := by
      exact_mod_cast two_pow_omega_le_card_divisors (by omega : n ≠ 0)
    have h2 : (n.divisors.card : ℝ) ≤ C₁ * (n : ℝ) ^ (ε / 2) := hC₁ n hn1
    push_cast at h1
    linarith
  have hlogle : Real.log n ≤ (n : ℝ) ^ δ / δ := log_le_rpow_div hnR hδ
  have hlin : 1 + Real.log n ≤ (1 + 1 / δ) * (n : ℝ) ^ δ := by
    have : (1 : ℝ) + (n : ℝ) ^ δ / δ ≤ (1 + 1 / δ) * (n : ℝ) ^ δ := by
      rw [add_mul, one_mul, one_div, inv_mul_eq_div]
      linarith
    linarith
  have hnn : (0 : ℝ) ≤ 1 + Real.log n := by
    have := Real.log_natCast_nonneg n; linarith
  have hfac2 : (1 + Real.log n) ^ 4 ≤ (1 + 1 / δ) ^ 4 * (n : ℝ) ^ (ε / 2) := by
    have hp : (1 + Real.log n) ^ 4 ≤ ((1 + 1 / δ) * (n : ℝ) ^ δ) ^ 4 :=
      pow_le_pow_left₀ hnn hlin 4
    have hδ4 : δ * ((4 : ℕ) : ℝ) = ε / 2 := by rw [hδdef]; push_cast; ring
    have hexp : ((1 + 1 / δ) * (n : ℝ) ^ δ) ^ 4
        = (1 + 1 / δ) ^ 4 * (n : ℝ) ^ (ε / 2) := by
      rw [mul_pow, ← Real.rpow_natCast ((n : ℝ) ^ δ) 4,
        ← Real.rpow_mul (le_of_lt hn0), hδ4]
    rw [hexp] at hp
    exact hp
  have hfold : (n : ℝ) ^ (ε / 2) * (n : ℝ) ^ (ε / 2) = (n : ℝ) ^ ε := by
    rw [← Real.rpow_add hn0]; ring_nf
  unfold Q
  calc (2 : ℝ) ^ n.primeFactors.card * (1 + Real.log n) ^ 4
      ≤ (C₁ * (n : ℝ) ^ (ε / 2)) * ((1 + 1 / δ) ^ 4 * (n : ℝ) ^ (ε / 2)) := by
        apply mul_le_mul hfac1 hfac2 (by positivity) (by positivity)
    _ = C₁ * (1 + 1 / δ) ^ 4 * ((n : ℝ) ^ (ε / 2) * (n : ℝ) ^ (ε / 2)) := by ring
    _ = C₁ * (1 + 1 / δ) ^ 4 * (n : ℝ) ^ ε := by rw [hfold]

end Paucity
