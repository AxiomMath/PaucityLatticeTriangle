/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The large-prime factor of the divisor bound

For a prime `p` with `p ^ ε ≥ 2`, the divisor-counting factor of the prime power `p ^ a` satisfies
`a + 1 ≤ p ^ (aε)`.

## Main results

* `succ_le_two_pow`: `a + 1 ≤ 2 ^ a`.
* `tau_factor_large`: `a + 1 ≤ p ^ (aε)` for `2 ≤ p` and `2 ≤ p ^ ε`.
-/

@[expose] public section

namespace Paucity

/-- `a + 1 ≤ 2 ^ a` over `ℕ`. -/
theorem succ_le_two_pow (a : ℕ) : a + 1 ≤ 2 ^ a := by
  induction a with
  | zero => simp
  | succ k ih =>
    have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    calc k + 1 + 1 ≤ 2 ^ k + 1 := by omega
      _ ≤ 2 ^ k + 2 ^ k := by omega
      _ = 2 ^ (k + 1) := by ring

/-- Once `p ^ ε ≥ 2`, the per-prime factor `(a + 1) / p ^ (aε)` is at most `1`. -/
theorem tau_factor_large {ε : ℝ} {p : ℕ} (hp : 2 ≤ p)
    (hpe : (2 : ℝ) ≤ (p : ℝ) ^ ε) (a : ℕ) :
    (a + 1 : ℝ) ≤ (p : ℝ) ^ ((a : ℝ) * ε) := by
  have hp0 : (0 : ℝ) ≤ (p : ℝ) := by positivity
  have hrw : (p : ℝ) ^ ((a : ℝ) * ε) = ((p : ℝ) ^ ε) ^ a := by
    rw [mul_comm, ← Real.rpow_natCast ((p : ℝ) ^ ε) a, ← Real.rpow_mul hp0]
  rw [hrw]
  have h2a : (2 : ℝ) ^ a ≤ ((p : ℝ) ^ ε) ^ a :=
    pow_le_pow_left₀ (by norm_num) hpe a
  have hcast : (a : ℝ) + 1 ≤ (2 : ℝ) ^ a := by
    have := succ_le_two_pow a
    have hc : ((a + 1 : ℕ) : ℝ) ≤ ((2 ^ a : ℕ) : ℝ) := Nat.cast_le.mpr this
    push_cast at hc
    exact hc
  linarith

end Paucity
