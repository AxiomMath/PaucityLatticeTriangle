/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Paucity.Estimates.TauFactorLarge
public import Paucity.Estimates.TauFactorSmall

/-!
# The divisor bound

For every `ε > 0` the number of divisors satisfies `τ(m) ≤ C(ε) * m ^ ε` for every `m ≥ 1`, with a
constant `C(ε)` depending only on `ε`.

## Main results

* `prod_rpow_of_nonneg`: a real power of a product of nonnegative reals is the product of the
  powers.
* `divisor_bound`: for every `ε > 0` there is `C > 0` with `#m.divisors ≤ C * m ^ ε` for every
  `m ≥ 1`.
-/

@[expose] public section

namespace Paucity

open Finset

/-- `(∏ i ∈ s, f i) ^ z = ∏ i ∈ s, f i ^ z` for `f` nonnegative on `s`, over `ℝ`. -/
theorem prod_rpow_of_nonneg {s : Finset ℕ} {f : ℕ → ℝ} (hf : ∀ i ∈ s, 0 ≤ f i)
    (z : ℝ) : (∏ i ∈ s, f i) ^ z = ∏ i ∈ s, (f i) ^ z := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a t ha ih =>
      have hfa : 0 ≤ f a := hf a (mem_insert_self a t)
      have hft : ∀ i ∈ t, 0 ≤ f i := fun i hi => hf i (mem_insert_of_mem hi)
      have hprod : 0 ≤ ∏ i ∈ t, f i := Finset.prod_nonneg hft
      rw [Finset.prod_insert ha, Finset.prod_insert ha,
        Real.mul_rpow hfa hprod, ih hft]

/-- `τ(m) ≤ C(ε) * m ^ ε` for every `m ≥ 1`, with a constant depending only on `ε > 0`. -/
theorem divisor_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m → (#m.divisors : ℝ) ≤ C * (m : ℝ) ^ ε := by
  obtain ⟨B, hB1, hB⟩ := tau_factor_small hε
  set P : ℕ := ⌈(2 : ℝ) ^ (1 / ε)⌉₊ with hP
  refine ⟨B ^ P, by positivity, fun m hm => ?_⟩
  have hm0 : m ≠ 0 := by omega
  rw [Nat.card_divisors hm0]
  have hm_eq : ((m : ℝ)) = ∏ p ∈ m.primeFactors, ((p : ℝ) ^ (m.factorization p)) := by
    calc ((m : ℝ)) = ((∏ p ∈ m.primeFactors, p ^ (m.factorization p) : ℕ) : ℝ) := by
          rw [← Nat.prod_primeFactors_pow_factorization hm0]
      _ = ∏ p ∈ m.primeFactors, ((p : ℝ) ^ (m.factorization p)) := by push_cast; ring
  have hmrpow : (m : ℝ) ^ ε = ∏ p ∈ m.primeFactors, ((p : ℝ) ^ (m.factorization p)) ^ ε := by
    rw [hm_eq, prod_rpow_of_nonneg (fun i _ => by positivity)]
  have hterm : ∀ p ∈ m.primeFactors,
      ((p : ℝ) ^ (m.factorization p)) ^ ε = (p : ℝ) ^ ((m.factorization p : ℝ) * ε) := by
    intro p _
    rw [← Real.rpow_natCast (p : ℝ) (m.factorization p), ← Real.rpow_mul (by positivity)]
  classical
  set S := m.primeFactors.filter (fun p : ℕ => ((p : ℝ) ^ ε < 2)) with hS
  have hScard : S.card ≤ P := by
    have hsub : S ⊆ Finset.range P := by
      intro p hp
      rw [hS, mem_filter] at hp
      obtain ⟨hpm, hplt⟩ := hp
      have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hpm).two_le
      have hp0 : (0 : ℝ) < (p : ℝ) := by positivity
      have : (p : ℝ) < (2 : ℝ) ^ (1 / ε) := by
        have h1 : ((p : ℝ) ^ ε) ^ (1 / ε) < (2 : ℝ) ^ (1 / ε) :=
          Real.rpow_lt_rpow (by positivity) hplt (by positivity)
        rwa [← Real.rpow_mul (le_of_lt hp0), mul_one_div, div_self (ne_of_gt hε),
          Real.rpow_one] at h1
      rw [Finset.mem_range, hP]
      exact Nat.lt_ceil.mpr this
    calc S.card ≤ (Finset.range P).card := Finset.card_le_card hsub
      _ = P := Finset.card_range P
  have hbound : ∀ p ∈ m.primeFactors,
      ((m.factorization p : ℝ) + 1)
        ≤ (if ((p : ℝ) ^ ε < 2) then B else 1)
            * ((p : ℝ) ^ ((m.factorization p : ℝ) * ε)) := by
    intro p hpm
    have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hpm).two_le
    have hp2R : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
    by_cases hps : ((p : ℝ) ^ ε < 2)
    · rw [if_pos hps]
      have h2 : (2 : ℝ) ^ ((m.factorization p : ℝ) * ε)
          ≤ (p : ℝ) ^ ((m.factorization p : ℝ) * ε) :=
        Real.rpow_le_rpow (by norm_num) hp2R (by positivity)
      calc ((m.factorization p : ℝ) + 1)
          ≤ B * (2 : ℝ) ^ ((m.factorization p : ℝ) * ε) := hB _
        _ ≤ B * (p : ℝ) ^ ((m.factorization p : ℝ) * ε) :=
            mul_le_mul_of_nonneg_left h2 (by linarith)
    · rw [if_neg hps, one_mul]
      exact tau_factor_large hp2 (not_lt.mp hps) (m.factorization p)
  have hprod_le : ((∏ p ∈ m.primeFactors, (m.factorization p + 1) : ℕ) : ℝ)
      ≤ ∏ p ∈ m.primeFactors,
          ((if ((p : ℝ) ^ ε < 2) then B else 1)
            * ((p : ℝ) ^ ((m.factorization p : ℝ) * ε))) := by
    push_cast
    refine Finset.prod_le_prod (fun i _ => by positivity) ?_
    exact fun i hi => hbound i hi
  have hsplit : (∏ p ∈ m.primeFactors,
      ((if ((p : ℝ) ^ ε < 2) then B else 1)
        * ((p : ℝ) ^ ((m.factorization p : ℝ) * ε))))
      = (∏ p ∈ m.primeFactors, (if ((p : ℝ) ^ ε < 2) then B else 1))
        * (∏ p ∈ m.primeFactors, ((p : ℝ) ^ ((m.factorization p : ℝ) * ε))) :=
    Finset.prod_mul_distrib
  have hconst : (∏ p ∈ m.primeFactors, (if ((p : ℝ) ^ ε < 2) then B else 1)) = B ^ S.card := by
    rw [← Finset.prod_filter, hS, Finset.prod_const]
  have hmε : (∏ p ∈ m.primeFactors, ((p : ℝ) ^ ((m.factorization p : ℝ) * ε))) = (m : ℝ) ^ ε := by
    rw [hmrpow]
    exact (Finset.prod_congr rfl hterm).symm
  have hBP : B ^ S.card ≤ B ^ P := pow_le_pow_right₀ hB1 hScard
  have hmεnn : (0 : ℝ) ≤ (m : ℝ) ^ ε := by positivity
  calc ((∏ p ∈ m.primeFactors, (m.factorization p + 1) : ℕ) : ℝ)
      ≤ _ := hprod_le
    _ = B ^ S.card * (m : ℝ) ^ ε := by rw [hsplit, hconst, hmε]
    _ ≤ B ^ P * (m : ℝ) ^ ε := mul_le_mul_of_nonneg_right hBP hmεnn

end Paucity
