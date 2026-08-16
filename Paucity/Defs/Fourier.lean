/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Int.Interval
public import Paucity.Defs.Notation.E

/-!
# The discrete Fourier transform

For `f : ℤ → ℂ` and a modulus `d`, the `k`-th discrete Fourier coefficient
`f̂^{(d)}(k) = (1/d) ∑_{x=1}^{d} f(x) e(-kx/d)`. At `d = 0` the sum is empty and the coefficient is
`0`.

## Main definitions

* `dft`: the `k`-th discrete Fourier coefficient of `f` at modulus `d`.

## Main results

* `dft_zero`: the coefficient at `k = 0` is the mean of `f` over a period.
* `dft_add`: `dft d` is additive in `f`.
-/

@[expose] public section

namespace Paucity

open Finset

/-- `dft d f k`, the coefficient `f̂^{(d)}(k)`: the `k`-th discrete Fourier coefficient of a
`d`-periodic `f`, `(1/d) ∑_{x=1}^{d} f(x) e(-kx/d)`. -/
noncomputable def dft (d : ℕ) (f : ℤ → ℂ) (k : ℤ) : ℂ :=
  (1 / (d : ℂ)) * ∑ x ∈ Icc (1 : ℤ) (d : ℤ), f x * e (-((k * x : ℤ) : ℝ) / (d : ℝ))

/-- At `k = 0` every `e`-factor is `1`, so the transform is the mean of `f` over a period. -/
theorem dft_zero (d : ℕ) (f : ℤ → ℂ) :
    dft d f 0 = (1 / (d : ℂ)) * ∑ x ∈ Icc (1 : ℤ) (d : ℤ), f x := by
  unfold dft
  simp

/-- `dft` is additive in the function. -/
theorem dft_add (d : ℕ) (f g : ℤ → ℂ) (k : ℤ) :
    dft d (f + g) k = dft d f k + dft d g k := by
  unfold dft
  rw [← mul_add, ← sum_add_distrib]
  congr 1
  refine sum_congr rfl fun x _ => ?_
  simp [add_mul]

end Paucity
