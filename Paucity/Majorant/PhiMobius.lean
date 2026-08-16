/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.Data.Nat.Totient

/-!
# `φ` as a Möbius transform

The totient is the Möbius transform of the identity: `∑_{d ∣ n} μ(n/d) · d = φ(n)` for
every `0 < n`.

## Main results

* `sum_moebius_mul_eq_totient`: `∑ d ∈ n.divisors, μ(n/d) * d = φ(n)`.
-/

@[expose] public section

namespace Paucity

open ArithmeticFunction

/-- `∑_{d ∣ n} μ(n/d) · d = φ(n)`. -/
theorem sum_moebius_mul_eq_totient {n : ℕ} (hn : 0 < n) :
    ∑ d ∈ n.divisors, moebius (n / d) * (d : ℤ) = (n.totient : ℤ) := by
  have hforward : ∀ m : ℕ, 0 < m → ∑ i ∈ m.divisors, ((i.totient : ℤ)) = (m : ℤ) := by
    intro m _
    have := Nat.sum_totient m
    calc ∑ i ∈ m.divisors, ((i.totient : ℤ)) = ((∑ i ∈ m.divisors, i.totient : ℕ) : ℤ) := by
          push_cast; ring
      _ = (m : ℤ) := by rw [this]
  have hinv := (sum_eq_iff_sum_smul_moebius_eq
    (f := fun i => ((i.totient : ℤ))) (g := fun m => (m : ℤ))).mp hforward n hn
  rw [Nat.sum_divisorsAntidiagonal (f := fun a b => moebius a • ((b : ℕ) : ℤ))] at hinv
  have hflip : ∑ d ∈ n.divisors, moebius (n / d) * (d : ℤ)
      = ∑ d ∈ n.divisors, moebius d * ((n / d : ℕ) : ℤ) := by
    rw [← Nat.sum_div_divisors n (fun d => moebius d * ((n / d : ℕ) : ℤ))]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [Nat.div_div_self (Nat.mem_divisors.mp hd).1 (by omega)]
  rw [hflip]
  simpa [smul_eq_mul] using hinv

end Paucity
