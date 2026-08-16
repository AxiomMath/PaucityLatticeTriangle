/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# `2 ^ ω(m) ≤ τ(m)`

A nonzero natural number `m` has at least `2 ^ ω(m)` divisors, where `ω(m)` counts the distinct
primes dividing `m`.

## Main results

* `two_pow_omega_le_card_divisors`: `2 ^ m.primeFactors.card ≤ #m.divisors` for `m ≠ 0`.
-/

@[expose] public section

namespace Paucity

open Finset

/-- `2 ^ ω(m) ≤ τ(m)` for `m ≠ 0`. -/
theorem two_pow_omega_le_card_divisors {m : ℕ} (hm : m ≠ 0) :
    2 ^ m.primeFactors.card ≤ #m.divisors := by
  rw [Nat.card_divisors hm, ← Finset.prod_const]
  refine Finset.prod_le_prod' fun p hp => ?_
  have hne : m.factorization p ≠ 0 := by
    rw [← Finsupp.mem_support_iff, Nat.support_factorization]
    exact hp
  omega

end Paucity
