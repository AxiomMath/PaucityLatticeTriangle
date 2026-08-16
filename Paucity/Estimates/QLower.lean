/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Paucity.Defs.Q

/-!
# `2 ≤ Q n`

The divisor-density factor `Q n = 2 ^ ω(n) * (1 + log n) ^ 4` is at least `2` for `n ≥ 2`.

## Main results

* `two_le_Q`: `2 ≤ Q n` for `n ≥ 2`.
-/

@[expose] public section

namespace Paucity

/-- `2 ≤ Q n` for `n ≥ 2`. -/
theorem two_le_Q {n : ℕ} (hn : 2 ≤ n) : 2 ≤ Q n := by
  have h2 : (2 : ℝ) ≤ 2 ^ n.primeFactors.card := by
    calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ n.primeFactors.card :=
          pow_le_pow_right₀ one_le_two
            (Finset.card_pos.mpr (Nat.nonempty_primeFactors.mpr hn))
  have h1 : (1 : ℝ) ≤ (1 + Real.log n) ^ 4 :=
    one_le_pow₀ (by linarith [Real.log_natCast_nonneg n])
  rw [Q]
  calc (2 : ℝ) = 2 * 1 := by ring
    _ ≤ 2 ^ n.primeFactors.card * (1 + Real.log n) ^ 4 :=
        mul_le_mul h2 h1 zero_le_one (by positivity)

end Paucity
