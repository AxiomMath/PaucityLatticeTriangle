/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.MeanInequalitiesPow

/-!
# The small-prime factor of the divisor bound

For every `ε > 0` there is a constant `B ≥ 1` with `a + 1 ≤ B * 2 ^ (aε)` for every `a`.

## Main results

* `tau_factor_small`: existence of `B ≥ 1` with `a + 1 ≤ B * 2 ^ (aε)` for every `a : ℕ`.
-/

@[expose] public section

namespace Paucity

/-- For `ε > 0` there is `B ≥ 1` with `a + 1 ≤ B * 2 ^ (aε)` for every `a : ℕ`. -/
theorem tau_factor_small {ε : ℝ} (hε : 0 < ε) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ a : ℕ, (a + 1 : ℝ) ≤ B * (2 : ℝ) ^ ((a : ℝ) * ε) := by
  have hβ1 : (1 : ℝ) < (2 : ℝ) ^ ε := by
    apply Real.one_lt_rpow_iff_of_pos (by norm_num) |>.mpr
    exact Or.inl ⟨by norm_num, hε⟩
  set β : ℝ := (2 : ℝ) ^ ε with hβdef
  have hpos : 0 < β - 1 := by linarith
  refine ⟨max 1 (1 / (β - 1)), le_max_left _ _, fun a => ?_⟩
  have hrw : (2 : ℝ) ^ ((a : ℝ) * ε) = β ^ a := by
    rw [hβdef, mul_comm, ← Real.rpow_natCast ((2 : ℝ) ^ ε) a,
      ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  rw [hrw]
  have hbern : 1 + (a : ℝ) * (β - 1) ≤ β ^ a := by
    have h := one_add_mul_le_pow (a := β - 1) (by linarith) a
    simpa using h
  have hB1 : (1 : ℝ) ≤ max 1 (1 / (β - 1)) := le_max_left _ _
  have hB2 : (1 : ℝ) ≤ max 1 (1 / (β - 1)) * (β - 1) := by
    have : 1 / (β - 1) ≤ max 1 (1 / (β - 1)) := le_max_right _ _
    calc (1 : ℝ) = (1 / (β - 1)) * (β - 1) := by field_simp
      _ ≤ max 1 (1 / (β - 1)) * (β - 1) := by
          exact mul_le_mul_of_nonneg_right this (le_of_lt hpos)
  have hstep : (a : ℝ) + 1 ≤ max 1 (1 / (β - 1)) * (1 + (a : ℝ) * (β - 1)) := by
    have hexp : max 1 (1 / (β - 1)) * (1 + (a : ℝ) * (β - 1))
        = max 1 (1 / (β - 1)) + (a : ℝ) * (max 1 (1 / (β - 1)) * (β - 1)) := by ring
    rw [hexp]
    have : (a : ℝ) * 1 ≤ (a : ℝ) * (max 1 (1 / (β - 1)) * (β - 1)) :=
      mul_le_mul_of_nonneg_left hB2 (Nat.cast_nonneg a)
    linarith
  have hBnn : (0 : ℝ) ≤ max 1 (1 / (β - 1)) := by linarith
  calc (a : ℝ) + 1 ≤ max 1 (1 / (β - 1)) * (1 + (a : ℝ) * (β - 1)) := hstep
    _ ≤ max 1 (1 / (β - 1)) * β ^ a := mul_le_mul_of_nonneg_left hbern hBnn

end Paucity
