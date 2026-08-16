/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.Divisors

/-!
# The divisor-density factor `Q`

`Q n = 2 ^ ω(n) * (1 + log n) ^ 4`, where `ω(n)` is the number of distinct prime factors of `n`.

## Main definitions

* `Q`: the divisor-density factor $\mathcal{Q}(n)$.

## Main results

* `Q_pos`: `Q` is positive at every `n`.
-/

@[expose] public section

namespace Paucity

/-- `Q n = 2 ^ ω(n) * (1 + log n) ^ 4`, the divisor-density factor $\mathcal{Q}(n)$. -/
noncomputable def Q (n : ℕ) : ℝ :=
  2 ^ n.primeFactors.card * (1 + Real.log n) ^ 4

theorem Q_pos (n : ℕ) : 0 < Q n := by
  have hlog : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  unfold Q
  positivity

end Paucity
