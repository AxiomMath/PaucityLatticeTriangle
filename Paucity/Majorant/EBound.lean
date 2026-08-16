/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Paucity.Defs.E
public import Paucity.Majorant.DivDecomp
public import Paucity.Lattice.FamilyCount
public import Paucity.Majorant.Majd
public import Paucity.Majorant.PhiMobius

/-!
# The global discrepancy bound

For `n ≥ 5` and `(p, q) ∈ H n`, the discrepancy `E n p q` between the witness count
`S n p q` and its expected value `M n p q` satisfies

    |E n p q| ≤ 2 ^ (ω(n) + 1) + ∑ d ∈ D n, W n d p q,

where `ω(n) = #n.primeFactors`. The Möbius expansions of `S n p q` and of `M n p q` over
`D n` are subtracted termwise, the discrepancy at each divisor is bounded by its majorant,
and rounding `h(t)d/n` down to `Hd n d t` costs at most `2` per divisor, over at most
`2^(ω(n))` divisors.

## Main results

* `abs_Hd_mul_Hd_div_sub_le_two`: the rounding error at one divisor is at most `2`.
* `abs_E_le`: `|E n p q| ≤ 2^(ω(n)+1) + ∑ d ∈ D n, W n d p q`.
-/

@[expose] public section

namespace Paucity

open ArithmeticFunction

/-- The rounding error at one divisor: for `0 < n`, `0 < d` and `h p + h q < n`,

    |Hd n d p * Hd n d q / d - h p * h q * d / n ^ 2| ≤ 2. -/
theorem abs_Hd_mul_Hd_div_sub_le_two {n p q d : ℕ} (hn : 0 < n) (hd : 0 < d)
    (hsum : h p + h q < n) :
    |(Hd n d p : ℝ) * (Hd n d q : ℝ) / (d : ℝ)
      - (h p : ℝ) * (h q : ℝ) * (d : ℝ) / (n : ℝ) ^ 2| ≤ 2 := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hpN : n * Hd n d p + h p * d % n = h p * d := by unfold Hd; exact Nat.div_add_mod _ _
  have hqN : n * Hd n d q + h q * d % n = h q * d := by unfold Hd; exact Nat.div_add_mod _ _
  have hpR : (n : ℝ) * (Hd n d p : ℝ) + ((h p * d % n : ℕ) : ℝ) = (h p : ℝ) * (d : ℝ) := by
    exact_mod_cast hpN
  have hqR : (n : ℝ) * (Hd n d q : ℝ) + ((h q * d % n : ℕ) : ℝ) = (h q : ℝ) * (d : ℝ) := by
    exact_mod_cast hqN
  have hA : (Hd n d p : ℝ) = ((h p : ℝ) * (d : ℝ) - ((h p * d % n : ℕ) : ℝ)) / (n : ℝ) := by
    field_simp
    linarith
  have hB : (Hd n d q : ℝ) = ((h q : ℝ) * (d : ℝ) - ((h q * d % n : ℕ) : ℝ)) / (n : ℝ) := by
    field_simp
    linarith
  have key : (Hd n d p : ℝ) * (Hd n d q : ℝ) / (d : ℝ)
        - (h p : ℝ) * (h q : ℝ) * (d : ℝ) / (n : ℝ) ^ 2
      = (-((h p : ℝ) * (d : ℝ) * ((h q * d % n : ℕ) : ℝ))
          - ((h p * d % n : ℕ) : ℝ) * (h q : ℝ) * (d : ℝ)
          + ((h p * d % n : ℕ) : ℝ) * ((h q * d % n : ℕ) : ℝ)) / ((n : ℝ) ^ 2 * (d : ℝ)) := by
    rw [hA, hB]
    field_simp
    ring
  have hp0 : (0 : ℝ) ≤ (h p : ℝ) := Nat.cast_nonneg _
  have hq0 : (0 : ℝ) ≤ (h q : ℝ) := Nat.cast_nonneg _
  have hrp0 : (0 : ℝ) ≤ ((h p * d % n : ℕ) : ℝ) := Nat.cast_nonneg _
  have hrq0 : (0 : ℝ) ≤ ((h q * d % n : ℕ) : ℝ) := Nat.cast_nonneg _
  have hrpn : ((h p * d % n : ℕ) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (Nat.mod_lt _ hn).le
  have hrqn : ((h q * d % n : ℕ) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (Nat.mod_lt _ hn).le
  have hsumR : (h p : ℝ) + (h q : ℝ) ≤ (n : ℝ) := by exact_mod_cast hsum.le
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hden : (0 : ℝ) < (n : ℝ) ^ 2 * (d : ℝ) := by positivity
  rw [key, abs_le]
  refine ⟨?_, ?_⟩
  · rw [le_div_iff₀ hden]
    nlinarith [mul_le_mul_of_nonneg_left hrqn (mul_nonneg hp0 hdR.le),
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hrpn hq0) hdR.le,
      mul_nonneg hrp0 hrq0,
      mul_le_mul_of_nonneg_left hsumR (mul_nonneg hdR.le hnR.le),
      mul_le_mul_of_nonneg_left hd1 (sq_nonneg (n : ℝ))]
  · rw [div_le_iff₀ hden]
    nlinarith [mul_nonneg (mul_nonneg hp0 hdR.le) hrq0,
      mul_nonneg (mul_nonneg hrp0 hq0) hdR.le,
      mul_le_mul hrpn hrqn hrq0 hnR.le,
      mul_le_mul_of_nonneg_left hd1 (sq_nonneg (n : ℝ))]

/-- The global discrepancy bound: for `n ≥ 5` and `(p, q) ∈ H n`,

    |E n p q| ≤ 2 ^ (ω(n) + 1) + ∑ d ∈ D n, W n d p q,

with `ω(n) = #n.primeFactors` the number of distinct prime factors of `n`. -/
theorem abs_E_le {n p q : ℕ} (hn : 5 ≤ n) (hpq : (p, q) ∈ H n) :
    |E n p q| ≤ 2 ^ (n.primeFactors.card + 1) + ∑ d ∈ D n, W n d p q := by
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
  have hsum : h p + h q < n := h_add_h_lt (H_subset_T n hpq)
  have hS : (S n p q : ℝ) = ∑ d ∈ D n, ((moebius (n / d) : ℤ) : ℝ) * (Nd n d p q : ℝ) := by
    have h0 : (S n p q : ℤ) = ∑ d ∈ D n, (moebius (n / d) : ℤ) * (Nd n d p q : ℤ) :=
      S_eq_sum_moebius_Nd hn (H_subset_T n hpq)
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) h0
  have hphiZ : ∑ d ∈ D n, (moebius (n / d) : ℤ) * (d : ℤ) = (n.totient : ℤ) := by
    rw [← sum_moebius_mul_eq_totient hn0]
    exact Finset.sum_subset (D_subset_divisors n) fun d hd hnd => by
      rw [moebius_eq_zero_of_not_squarefree fun hs => hnd (mem_D.mpr ⟨hd, hs⟩), zero_mul]
  have hphiR : ∑ d ∈ D n, ((moebius (n / d) : ℤ) : ℝ) * (d : ℝ) = (n.totient : ℝ) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) hphiZ
  have hM : M n p q
      = ∑ d ∈ D n, ((moebius (n / d) : ℤ) : ℝ)
          * ((h p : ℝ) * (h q : ℝ) * (d : ℝ) / (n : ℝ) ^ 2) := by
    unfold M
    rw [← hphiR, Finset.mul_sum, Finset.sum_div]
    exact Finset.sum_congr rfl fun d _ => by ring
  have hE : E n p q = ∑ d ∈ D n, ((moebius (n / d) : ℤ) : ℝ)
      * ((Nd n d p q : ℝ) - (h p : ℝ) * (h q : ℝ) * (d : ℝ) / (n : ℝ) ^ 2) := by
    unfold E
    rw [hS, hM, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun d _ => by ring
  have hterm : ∀ d ∈ D n, |((moebius (n / d) : ℤ) : ℝ)
      * ((Nd n d p q : ℝ) - (h p : ℝ) * (h q : ℝ) * (d : ℝ) / (n : ℝ) ^ 2)|
      ≤ 2 + W n d p q := by
    intro d hd
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos (dvd_of_mem_D hd) hn0
    have hmu : |((moebius (n / d) : ℤ) : ℝ)| ≤ 1 := by
      rw [← Int.cast_abs]
      exact_mod_cast abs_moebius_le_one
    rw [abs_mul]
    calc |((moebius (n / d) : ℤ) : ℝ)|
          * |(Nd n d p q : ℝ) - (h p : ℝ) * (h q : ℝ) * (d : ℝ) / (n : ℝ) ^ 2|
        ≤ 1 * |(Nd n d p q : ℝ) - (h p : ℝ) * (h q : ℝ) * (d : ℝ) / (n : ℝ) ^ 2| :=
          mul_le_mul_of_nonneg_right hmu (abs_nonneg _)
      _ = |(Nd n d p q : ℝ) - (h p : ℝ) * (h q : ℝ) * (d : ℝ) / (n : ℝ) ^ 2| := one_mul _
      _ ≤ |(Nd n d p q : ℝ) - (Hd n d p : ℝ) * (Hd n d q : ℝ) / (d : ℝ)|
            + |(Hd n d p : ℝ) * (Hd n d q : ℝ) / (d : ℝ)
              - (h p : ℝ) * (h q : ℝ) * (d : ℝ) / (n : ℝ) ^ 2| := abs_sub_le _ _ _
      _ ≤ W n d p q + 2 :=
          add_le_add (abs_Nd_sub_le_W hn hpq hd) (abs_Hd_mul_Hd_div_sub_le_two hn0 hd0 hsum)
      _ = 2 + W n d p q := add_comm _ _
  have hcard : ((D n).card : ℝ) ≤ 2 ^ n.primeFactors.card := by
    exact_mod_cast card_D_le hn0.ne'
  calc |E n p q|
      = |∑ d ∈ D n, ((moebius (n / d) : ℤ) : ℝ)
          * ((Nd n d p q : ℝ) - (h p : ℝ) * (h q : ℝ) * (d : ℝ) / (n : ℝ) ^ 2)| := by rw [hE]
    _ ≤ ∑ d ∈ D n, |((moebius (n / d) : ℤ) : ℝ)
          * ((Nd n d p q : ℝ) - (h p : ℝ) * (h q : ℝ) * (d : ℝ) / (n : ℝ) ^ 2)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ D n, (2 + W n d p q) := Finset.sum_le_sum hterm
    _ = 2 * ((D n).card : ℝ) + ∑ d ∈ D n, W n d p q := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
        ring
    _ ≤ 2 ^ (n.primeFactors.card + 1) + ∑ d ∈ D n, W n d p q := by
        have : 2 * ((D n).card : ℝ) ≤ 2 * 2 ^ n.primeFactors.card := by linarith
        rw [pow_succ]
        linarith

end Paucity
