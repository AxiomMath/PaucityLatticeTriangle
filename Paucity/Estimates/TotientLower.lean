/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Paucity.Estimates.DivisorBound
public import Paucity.Estimates.NOverPhi
public import Paucity.Estimates.TauGeTwoOmega

/-!
# The totient lower bound

For every `ε > 0` there is `c(ε) > 0` with `n² ≤ c(ε) * n ^ (1 + ε) * φ(n)` for every `n ≥ 1`.

## Main results

* `totient_lower`: for every `ε > 0` there is `c > 0` with `n² ≤ c * n ^ (1 + ε) * n.totient` for
  every `n ≥ 1`.
-/

@[expose] public section

namespace Paucity

/-- `n² ≤ c(ε) * n ^ (1 + ε) * φ(n)` for every `n ≥ 1`, with `c` depending only on `ε > 0`.

This is weaker than the Rosser–Schoenfeld bound `n / φ(n) < e^γ log log n + 3 / log log n`, which
is what *On the paucity of lattice triangles* uses at this step: no `log log` occurs here. -/
theorem totient_lower {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
      (n : ℝ) ^ 2 ≤ c * (n : ℝ) ^ (1 + ε) * (n.totient : ℝ) := by
  obtain ⟨C, hC0, hC⟩ := divisor_bound hε
  refine ⟨C, hC0, fun n hn => ?_⟩
  have hn0 : n ≠ 0 := by omega
  have hnR : (0 : ℝ) < (n : ℝ) := by positivity
  have h1 : (n : ℝ) ≤ (2 ^ n.primeFactors.card : ℕ) * (n.totient : ℝ) := by
    have := le_two_pow_omega_mul_totient n
    exact_mod_cast this
  have h2 : ((2 ^ n.primeFactors.card : ℕ) : ℝ) ≤ (n.divisors.card : ℝ) := by
    exact_mod_cast two_pow_omega_le_card_divisors hn0
  have h3 : (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ ε := hC n hn
  have htot : (0 : ℝ) ≤ (n.totient : ℝ) := by positivity
  have hchain : (n : ℝ) ≤ (C * (n : ℝ) ^ ε) * (n.totient : ℝ) := by
    calc (n : ℝ) ≤ ((2 ^ n.primeFactors.card : ℕ) : ℝ) * (n.totient : ℝ) := h1
      _ ≤ (n.divisors.card : ℝ) * (n.totient : ℝ) := mul_le_mul_of_nonneg_right h2 htot
      _ ≤ (C * (n : ℝ) ^ ε) * (n.totient : ℝ) := mul_le_mul_of_nonneg_right h3 htot
  have hmul : (n : ℝ) * (n : ℝ) ≤ (n : ℝ) * ((C * (n : ℝ) ^ ε) * (n.totient : ℝ)) :=
    mul_le_mul_of_nonneg_left hchain (le_of_lt hnR)
  have hfold : (n : ℝ) ^ (1 + ε) = (n : ℝ) * (n : ℝ) ^ ε := by
    rw [Real.rpow_add hnR, Real.rpow_one]
  calc (n : ℝ) ^ 2 = (n : ℝ) * (n : ℝ) := by ring
    _ ≤ (n : ℝ) * ((C * (n : ℝ) ^ ε) * (n.totient : ℝ)) := hmul
    _ = C * ((n : ℝ) * (n : ℝ) ^ ε) * (n.totient : ℝ) := by ring
    _ = C * (n : ℝ) ^ (1 + ε) * (n.totient : ℝ) := by rw [hfold]

end Paucity
