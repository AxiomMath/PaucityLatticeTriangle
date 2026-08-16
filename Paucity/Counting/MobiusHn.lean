/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.Tactic.Ring
public import Paucity.Defs.Hn
public import Paucity.Counting.CountTnDiv

/-!
# Möbius expansion of `#(H n)`

The primitive obtuse region `H n`, cut out of `T n` by the condition `gcd(p, q, n) = 1`, is
counted by a divisor sum: `#(H n) = ∑_{e ∣ n} μ(e) · C((n - 1) / (2 * e), 2)` for `0 < n`.

## Main results

* `sum_moebius_divisors`: `∑_{e ∣ m} μ(e)` is `1` at `m = 1` and `0` otherwise.
* `card_H_eq_sum_moebius`: `#(H n) = ∑_{e ∣ n} μ(e) · C((n - 1) / (2 * e), 2)` for `0 < n`.
-/

@[expose] public section

namespace Paucity

open Finset ArithmeticFunction

/-- `∑_{e ∣ m} μ(e)` is `1` at `m = 1` and `0` otherwise. -/
theorem sum_moebius_divisors {m : ℕ} (hm : m ≠ 0) :
    ∑ e ∈ m.divisors, (moebius e : ℤ) = if m = 1 then 1 else 0 := by
  have h : ((moebius * zeta : ArithmeticFunction ℤ)) m = (1 : ArithmeticFunction ℤ) m := by
    rw [moebius_mul_coe_zeta]
  have hsplit := Nat.sum_divisorsAntidiagonal
    (f := fun a b => (moebius a : ℤ) * (zeta : ArithmeticFunction ℤ) b) (n := m)
  rw [ArithmeticFunction.mul_apply, ArithmeticFunction.one_apply, hsplit] at h
  rw [← h]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd0 : m / d ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hm) (Nat.dvd_of_mem_divisors hd))
      (Nat.pos_of_mem_divisors hd)).ne'
  rw [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply_ne hd0, Nat.cast_one,
    mul_one]

/-- The primitive obtuse region, counted by Möbius inversion. -/
theorem card_H_eq_sum_moebius {n : ℕ} (hn : 0 < n) :
    ((H n).card : ℤ)
      = ∑ e ∈ n.divisors, (moebius e : ℤ) * (((n - 1) / (2 * e)).choose 2 : ℤ) := by
  classical
  have h1 : ((H n).card : ℤ)
      = ∑ pq ∈ T n, (if Nat.gcd (Nat.gcd pq.1 pq.2) n = 1 then (1 : ℤ) else 0) := by
    have hcard : (H n).card
        = ∑ pq ∈ T n, (if Nat.gcd (Nat.gcd pq.1 pq.2) n = 1 then 1 else 0) := by
      unfold H
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [hcard, Nat.cast_sum]
    exact Finset.sum_congr rfl fun pq _ => by split <;> simp
  have h2 : ∀ pq : ℕ × ℕ,
      (if Nat.gcd (Nat.gcd pq.1 pq.2) n = 1 then (1 : ℤ) else 0)
        = ∑ e ∈ n.divisors.filter (fun e => e ∣ pq.1 ∧ e ∣ pq.2), (moebius e : ℤ) := by
    intro pq
    have hg0 : Nat.gcd (Nat.gcd pq.1 pq.2) n ≠ 0 := fun h =>
      hn.ne' (Nat.gcd_eq_zero_iff.mp h).2
    have hdiv : (Nat.gcd (Nat.gcd pq.1 pq.2) n).divisors
        = n.divisors.filter (fun e => e ∣ pq.1 ∧ e ∣ pq.2) := by
      ext e
      simp only [Nat.mem_divisors, Finset.mem_filter]
      constructor
      · rintro ⟨he, -⟩
        exact ⟨⟨he.trans (Nat.gcd_dvd_right _ _), hn.ne'⟩,
          (he.trans (Nat.gcd_dvd_left _ _)).trans (Nat.gcd_dvd_left _ _),
          (he.trans (Nat.gcd_dvd_left _ _)).trans (Nat.gcd_dvd_right _ _)⟩
      · rintro ⟨⟨hen, -⟩, hep, heq⟩
        exact ⟨Nat.dvd_gcd (Nat.dvd_gcd hep heq) hen, hg0⟩
    rw [← hdiv, sum_moebius_divisors hg0]
  rw [h1, Finset.sum_congr rfl fun pq _ => h2 pq]
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e he => ?_
  rw [← Finset.sum_filter, Finset.sum_const, card_T_filter_dvd (Nat.pos_of_mem_divisors he),
    nsmul_eq_mul]
  ring

end Paucity
