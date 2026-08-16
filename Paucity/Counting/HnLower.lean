/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Paucity.Counting.MobiusHn

/-!
# The primitive obtuse region is quadratically large

There is an absolute constant `c₀ > 0` with `c₀ · n² ≤ #(H n)` for every `n ≥ 5`, and
`c₀ = 1/2304` works. The intermediate estimates bound the terms of the Möbius expansion of
`#(H n)`: its `e = 1` term is `C((n-1)/2, 2)`, and the tail over `2 ≤ e ≤ n` is at most
`3n²/32`.

## Main results

* `sum_one_div_sq_Icc_le`: `∑_{e = 2}^{N} 1/e² ≤ 3/4 - 1/N` for `N ≥ 2`.
* `choose_two_scale_le`: `C((n-1)/(2e), 2) ≤ n²/(8e²)` for `1 ≤ e`.
* `sum_choose_two_tail_le`: `∑_{e = 2}^{n} C((n-1)/(2e), 2) ≤ 3n²/32` for `n ≥ 2`.
* `card_H_ge_head_sub_tail`: `#(H n)` is at least `C((n-1)/2, 2)` minus that tail.
* `choose_two_head_ge`: `C((n-1)/2, 2) ≥ (n-2)(n-4)/8` for `n ≥ 5`.
* `card_H_lower_of_five_le`: `n²/2304 ≤ #(H n)` for every `n ≥ 5`.
* `exists_card_H_lower`: an absolute `c₀ > 0` with `c₀ · n² ≤ #(H n)` for every `n ≥ 5`.
-/

@[expose] public section

namespace Paucity

open Finset ArithmeticFunction

/-- `∑_{e = 2}^{N} 1/e² ≤ 3/4 - 1/N` for `N ≥ 2`. -/
theorem sum_one_div_sq_Icc_le {N : ℕ} (hN : 2 ≤ N) :
    ∑ e ∈ Finset.Icc 2 N, (1 / (e : ℝ) ^ 2) ≤ 3 / 4 - 1 / (N : ℝ) := by
  induction N, hN using Nat.le_induction with
  | base => norm_num
  | succ N hN ih =>
    have hN2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
    rw [Finset.sum_Icc_succ_top (by omega)]
    push_cast
    have key : 1 / ((N : ℝ) + 1) ^ 2 ≤ 1 / (N : ℝ) - 1 / ((N : ℝ) + 1) := by
      rw [div_sub_div _ _ hN0.ne' (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
      ring_nf
      nlinarith
    linarith

/-- `C(K_e, 2) ≤ n²/(8e²)` for `K_e = (n-1)/(2e)`. -/
theorem choose_two_scale_le (n : ℕ) {e : ℕ} (he : 1 ≤ e) :
    (((n - 1) / (2 * e)).choose 2 : ℝ) ≤ (n : ℝ) ^ 2 / (8 * (e : ℝ) ^ 2) := by
  set K := (n - 1) / (2 * e) with hKdef
  have hKn : K * (2 * e) ≤ n := le_trans (Nat.div_mul_le_self _ _) (Nat.sub_le n 1)
  have hK : (K : ℝ) * (2 * (e : ℝ)) ≤ (n : ℝ) := by exact_mod_cast hKn
  have he' : (1 : ℝ) ≤ (e : ℝ) := by exact_mod_cast he
  have hK0 : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg _
  have ha : (0 : ℝ) ≤ 2 * (e : ℝ) * (K : ℝ) := by positivity
  have hb : 2 * (e : ℝ) * (K : ℝ) ≤ (n : ℝ) := by linarith
  have hsq : (2 * (e : ℝ) * K) ^ 2 ≤ (n : ℝ) ^ 2 := by
    nlinarith [mul_self_le_mul_self ha hb]
  rw [Nat.cast_choose_two, div_le_div_iff₀ (by norm_num) (by positivity)]
  nlinarith [mul_nonneg (mul_nonneg (le_of_lt (by positivity : (0 : ℝ) < 8)) (sq_nonneg (e : ℝ)))
    hK0]

/-- The tail of the Möbius sum, widened to every `e ∈ [2, n]`, is at most `3n²/32`. -/
theorem sum_choose_two_tail_le {n : ℕ} (hn : 2 ≤ n) :
    ∑ e ∈ Finset.Icc 2 n, (((n - 1) / (2 * e)).choose 2 : ℝ) ≤ 3 * (n : ℝ) ^ 2 / 32 := by
  have hstep : ∀ e ∈ Finset.Icc 2 n,
      (((n - 1) / (2 * e)).choose 2 : ℝ) ≤ (n : ℝ) ^ 2 / 8 * (1 / (e : ℝ) ^ 2) := by
    intro e he
    rw [Finset.mem_Icc] at he
    have h := choose_two_scale_le n (by omega : 1 ≤ e)
    have hrw : (n : ℝ) ^ 2 / (8 * (e : ℝ) ^ 2) = (n : ℝ) ^ 2 / 8 * (1 / (e : ℝ) ^ 2) := by ring
    rw [hrw] at h
    exact h
  have hsum := Finset.sum_le_sum hstep
  rw [← Finset.mul_sum] at hsum
  have hharm : ∑ e ∈ Finset.Icc 2 n, (1 / (e : ℝ) ^ 2) ≤ 3 / 4 := by
    have h := sum_one_div_sq_Icc_le hn
    have hpos : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
    linarith
  have hn2 : (0 : ℝ) ≤ (n : ℝ) ^ 2 / 8 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hharm hn2]

/-- `#(H n)` is at least its `e = 1` Möbius term minus the widened tail. -/
theorem card_H_ge_head_sub_tail {n : ℕ} (hn : 0 < n) :
    (((n - 1) / 2).choose 2 : ℝ) - (∑ e ∈ Finset.Icc 2 n, (((n - 1) / (2 * e)).choose 2 : ℝ))
      ≤ ((H n).card : ℝ) := by
  classical
  have hid := card_H_eq_sum_moebius hn
  have hR : ((H n).card : ℝ)
      = ∑ e ∈ n.divisors, ((moebius e : ℤ) : ℝ) * (((n - 1) / (2 * e)).choose 2 : ℝ) := by
    exact_mod_cast hid
  have h1 : (1 : ℕ) ∈ n.divisors := Nat.one_mem_divisors.mpr hn.ne'
  rw [← Finset.sum_erase_add _ _ h1] at hR
  have hterm : ((moebius 1 : ℤ) : ℝ) * (((n - 1) / (2 * 1)).choose 2 : ℝ)
      = (((n - 1) / 2).choose 2 : ℝ) := by simp
  rw [hterm] at hR
  have hlow : ∀ e ∈ n.divisors.erase 1,
      -(((n - 1) / (2 * e)).choose 2 : ℝ)
        ≤ ((moebius e : ℤ) : ℝ) * (((n - 1) / (2 * e)).choose 2 : ℝ) := by
    intro e _
    have hm : (-1 : ℝ) ≤ ((moebius e : ℤ) : ℝ) := by
      have h' : (-1 : ℤ) ≤ moebius e := (abs_le.mp (abs_moebius_le_one (n := e))).1
      exact_mod_cast h'
    have hc : (0 : ℝ) ≤ (((n - 1) / (2 * e)).choose 2 : ℝ) := Nat.cast_nonneg _
    nlinarith
  have h2 := Finset.sum_le_sum hlow
  rw [Finset.sum_neg_distrib] at h2
  have h3 : ∑ e ∈ n.divisors.erase 1, (((n - 1) / (2 * e)).choose 2 : ℝ)
      ≤ ∑ e ∈ Finset.Icc 2 n, (((n - 1) / (2 * e)).choose 2 : ℝ) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => Nat.cast_nonneg _
    intro e he
    rw [Finset.mem_erase, Nat.mem_divisors] at he
    have hpos : 0 < e := Nat.pos_of_dvd_of_pos he.2.1 hn
    rw [Finset.mem_Icc]
    exact ⟨by omega, Nat.le_of_dvd hn he.2.1⟩
  linarith

/-- The main term: `C((n-1)/2, 2) ≥ (n-2)(n-4)/8` for `n ≥ 5`. -/
theorem choose_two_head_ge {n : ℕ} (hn : 5 ≤ n) :
    ((n : ℝ) - 2) * ((n : ℝ) - 4) / 8 ≤ (((n - 1) / 2).choose 2 : ℝ) := by
  set K := (n - 1) / 2 with hK
  have hK2 : 2 ≤ K := by omega
  have hKn : n ≤ 2 * K + 2 := by omega
  have hK2' : (2 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK2
  have hKn' : (n : ℝ) ≤ 2 * (K : ℝ) + 2 := by exact_mod_cast hKn
  have hn' : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  rw [Nat.cast_choose_two]
  nlinarith [hKn', hK2', hn']

/-- The bound with the constant made explicit: `n²/2304 ≤ #(H n)` for every `n ≥ 5`. -/
theorem card_H_lower_of_five_le {n : ℕ} (hn : 5 ≤ n) :
    (1 / 2304 : ℝ) * (n : ℝ) ^ 2 ≤ ((H n).card : ℝ) := by
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
  rcases Nat.lt_or_ge n 48 with h | h
  · have h1 : 1 ≤ ((H n).card : ℝ) := by
      have hpos : 0 < (H n).card := Finset.card_pos.mpr (H_nonempty hn)
      exact_mod_cast hpos
    have hn' : (n : ℝ) ≤ 47 := by exact_mod_cast (by omega : n ≤ 47)
    nlinarith
  · have h1 := card_H_ge_head_sub_tail (n := n) (by omega)
    have h2 := sum_choose_two_tail_le (n := n) (by omega)
    have h3 := choose_two_head_ge hn
    have hn' : (48 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
    nlinarith [mul_nonneg (sub_nonneg.mpr hn') hn0]

/-- There is an absolute constant `c₀ > 0` with `c₀ · n² ≤ #(H n)` for every `n ≥ 5`. The
constant is quantified outside the `∀ n`, so it does not depend on `n`. -/
theorem exists_card_H_lower :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ n : ℕ, 5 ≤ n → c₀ * (n : ℝ) ^ 2 ≤ ((H n).card : ℝ) :=
  ⟨1 / 2304, by norm_num, fun _ hn => card_H_lower_of_five_le hn⟩

end Paucity
