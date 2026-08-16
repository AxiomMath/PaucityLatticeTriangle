/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# `n ≤ 2 ^ ω(n) * φ(n)`

The ratio `n / φ(n)` is at most `2 ^ ω(n)`, where `ω(n)` counts the distinct primes dividing `n`,
in the multiplication-free form `n ≤ 2 ^ ω(n) * φ(n)`.

## Main results

* `le_two_pow_omega_mul_totient`: `n ≤ 2 ^ n.primeFactors.card * n.totient`.
-/

@[expose] public section

namespace Paucity

open Finset

/-- `n ≤ 2 ^ ω(n) * φ(n)`, the multiplication-free form of `n / φ(n) ≤ 2 ^ ω(n)`. -/
theorem le_two_pow_omega_mul_totient (n : ℕ) :
    n ≤ 2 ^ n.primeFactors.card * n.totient := by
  have key := Nat.totient_mul_prod_primeFactors n
  have hstep : ∀ p ∈ n.primeFactors, p ≤ 2 * (p - 1) := fun p hp => by
    have := (Nat.prime_of_mem_primeFactors hp).two_le
    omega
  have hprod : ∏ p ∈ n.primeFactors, p
      ≤ 2 ^ n.primeFactors.card * ∏ p ∈ n.primeFactors, (p - 1) := by
    calc ∏ p ∈ n.primeFactors, p
        ≤ ∏ p ∈ n.primeFactors, 2 * (p - 1) := Finset.prod_le_prod' hstep
      _ = 2 ^ n.primeFactors.card * ∏ p ∈ n.primeFactors, (p - 1) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const]
  have hpos : 0 < ∏ p ∈ n.primeFactors, (p - 1) := by
    refine Finset.prod_pos fun p hp => ?_
    have := (Nat.prime_of_mem_primeFactors hp).two_le
    omega
  have main : n * ∏ p ∈ n.primeFactors, (p - 1)
      ≤ 2 ^ n.primeFactors.card * n.totient * ∏ p ∈ n.primeFactors, (p - 1) := by
    calc n * ∏ p ∈ n.primeFactors, (p - 1)
        = n.totient * ∏ p ∈ n.primeFactors, p := key.symm
      _ ≤ n.totient * (2 ^ n.primeFactors.card * ∏ p ∈ n.primeFactors, (p - 1)) :=
          Nat.mul_le_mul_left _ hprod
      _ = 2 ^ n.primeFactors.card * n.totient * ∏ p ∈ n.primeFactors, (p - 1) := by ring
  exact Nat.le_of_mul_le_mul_right main hpos

end Paucity
