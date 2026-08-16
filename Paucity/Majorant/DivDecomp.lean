/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Ring
public import Paucity.Defs.Dn
public import Paucity.Defs.Nd
public import Paucity.Counting.SIdentity
public import Paucity.Counting.MobiusHn

/-!
# The divisor decomposition

For `n ≥ 5` and `(p, q) ∈ T n`, the witness count `S n p q` decomposes over the divisors of
`n` as `∑ d ∈ D n, μ(n/d) Nd n d p q`, an identity in `ℤ`. It trades a count of units
modulo `n`, which no orthogonality relation sees, for counts over full residue systems
modulo the divisors of `n`.

## Main results

* `res_mul_left`: `[cx]_{cd} = c [x]_d`.
* `Hd_eq_div`: `Hd n d t = ⌊h(t)/c⌋` when `n = cd`.
* `ind_of_mul`: at a multiple `a = cb`, the window `[1, h t]` modulo `n` is the window
  `[1, Hd n d t]` modulo `d`.
* `sum_ind_eq_Nd`: the inner count of the Möbius expansion is `Nd n d p q`.
* `S_eq_sum_moebius_Nd`: `S n p q = ∑ d ∈ D n, μ(n/d) Nd n d p q`.
-/

@[expose] public section

namespace Paucity

open Finset ArithmeticFunction

/-- `[cx]_{cd} = c · [x]_d`: scaling the modulus scales the least nonnegative
residue. -/
theorem res_mul_left {c d : ℕ} (hc : 0 < c) (hd : 0 < d) (x : ℤ) :
    res ((c : ℤ) * x) (c * d) = c * res x d := by
  have hc' : (0 : ℤ) < (c : ℤ) := by exact_mod_cast hc
  have hnn : 0 ≤ x % (d : ℤ) := Int.emod_nonneg x (by exact_mod_cast hd.ne')
  obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le hnn
  unfold res
  rw [Nat.cast_mul, Int.mul_emod_mul_of_pos _ _ hc', hk, ← Int.natCast_mul,
    Int.toNat_natCast, Int.toNat_natCast]

/-- `Hd n d t = ⌊h(t)/c⌋` when `n = cd`. -/
theorem Hd_eq_div {n c d t : ℕ} (hd : 0 < d) (hn : n = c * d) : Hd n d t = h t / c := by
  unfold Hd
  rw [hn, Nat.mul_div_mul_right (h t) c hd]

/-- Rescaling one indicator: at a multiple `a = cb`, the window `[1, h t]` modulo `n` is
the window `[1, Hd n d t]` modulo `d`. -/
theorem ind_of_mul {n c d t : ℕ} (hc : 0 < c) (hd : 0 < d) (hn : n = c * d) (b : ℕ) :
    ind n (h t) (((c * b : ℕ) : ℤ) * (t : ℤ)) = ind d (Hd n d t) ((b : ℤ) * (t : ℤ)) := by
  have hres : res (((c * b : ℕ) : ℤ) * (t : ℤ)) n = c * res ((b : ℤ) * (t : ℤ)) d := by
    have hrw : ((c * b : ℕ) : ℤ) * (t : ℤ) = (c : ℤ) * ((b : ℤ) * (t : ℤ)) := by
      push_cast; ring
    rw [hrw, hn, res_mul_left hc hd]
  have hiff : ∀ r : ℕ, (1 ≤ c * r ∧ c * r ≤ h t) ↔ (1 ≤ r ∧ r ≤ h t / c) := by
    intro r
    rw [Nat.le_div_iff_mul_le hc]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · rcases Nat.eq_zero_or_pos r with hr | hr
        · rw [hr, Nat.mul_zero] at h1; omega
        · exact hr
      · rw [Nat.mul_comm r c]; exact h2
    · rintro ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · have hle : c * 1 ≤ c * r := Nat.mul_le_mul_left c h1
        omega
      · rw [Nat.mul_comm c r]; exact h2
  unfold ind
  rw [hres, Hd_eq_div hd hn]
  simp only [hiff]


/-- The inner count of the Möbius expansion is `Nd n d p q`: for `n = cd`, summing the
product of the two windows modulo `n` over the multiples of `c` in `[1, n]` counts the
pairs of windows modulo `d`. -/
theorem sum_ind_eq_Nd {n c d p q : ℕ} (hc : 0 < c) (hd : 0 < d) (hn : n = c * d) :
    ∑ a ∈ Icc 1 n,
        (if c ∣ a then ind n (h p) ((a : ℤ) * p) * ind n (h q) ((a : ℤ) * q) else 0)
      = Nd n d p q := by
  rw [← Finset.sum_filter]
  have himg : ((Icc 1 n).filter fun a => c ∣ a) = (Icc 1 d).image fun b => c * b := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨ha1, ha2⟩, b, rfl⟩
      refine ⟨b, ⟨?_, ?_⟩, rfl⟩
      · rcases Nat.eq_zero_or_pos b with hb | hb
        · rw [hb, Nat.mul_zero] at ha1; omega
        · exact hb
      · exact Nat.le_of_mul_le_mul_left (by rw [← hn]; exact ha2) hc
    · rintro ⟨b, ⟨hb1, hb2⟩, rfl⟩
      refine ⟨⟨?_, ?_⟩, Dvd.intro b rfl⟩
      · have hle : c * 1 ≤ c * b := Nat.mul_le_mul_left c hb1
        omega
      · rw [hn]; exact Nat.mul_le_mul_left c hb2
  rw [himg, Finset.sum_image (fun x _ y _ hxy => Nat.eq_of_mul_eq_mul_left hc hxy)]
  rw [Finset.sum_congr rfl fun b _ => by
    rw [ind_of_mul hc hd hn (t := p) b, ind_of_mul hc hd hn (t := q) b]]
  exact (Nd_eq_sum_ind _ _ _ _).symm

/-- The witness count, decomposed over the divisors of `n`:
`S n p q = ∑ d ∈ D n, μ(n/d) Nd n d p q`, as an identity in `ℤ`. -/
theorem S_eq_sum_moebius_Nd {n : ℕ} (hn : 5 ≤ n) {pq : ℕ × ℕ} (hpq : pq ∈ T n) :
    (S n pq.1 pq.2 : ℤ)
      = ∑ d ∈ D n, (moebius (n / d) : ℤ) * (Nd n d pq.1 pq.2 : ℤ) := by
  have hn0 : 0 < n := by omega
  have hgcd : ∀ a : ℕ, (if Nat.gcd a n = 1 then (1 : ℤ) else 0)
      = ∑ e ∈ n.divisors.filter fun e => e ∣ a, (moebius e : ℤ) := by
    intro a
    have hg0 : Nat.gcd a n ≠ 0 := fun hh => hn0.ne' (Nat.gcd_eq_zero_iff.mp hh).2
    have hdiv : (Nat.gcd a n).divisors = n.divisors.filter fun e => e ∣ a := by
      ext e
      simp only [Nat.mem_divisors, Finset.mem_filter]
      constructor
      · rintro ⟨he, -⟩
        exact ⟨⟨he.trans (Nat.gcd_dvd_right _ _), hn0.ne'⟩, he.trans (Nat.gcd_dvd_left _ _)⟩
      · rintro ⟨⟨hen, -⟩, hea⟩
        exact ⟨Nat.dvd_gcd hea hen, hg0⟩
    rw [← hdiv, sum_moebius_divisors hg0]
  have hstep : (S n pq.1 pq.2 : ℤ)
      = ∑ e ∈ n.divisors, (moebius e : ℤ) * (Nd n (n / e) pq.1 pq.2 : ℤ) := by
    rw [S_eq_sum_ind hpq, Nat.cast_sum]
    have h1 : ∑ a ∈ U n,
          ((ind n (h pq.1) ((a : ℤ) * pq.1) * ind n (h pq.2) ((a : ℤ) * pq.2) : ℕ) : ℤ)
        = ∑ a ∈ Icc 1 n, (∑ e ∈ n.divisors.filter fun e => e ∣ a, (moebius e : ℤ))
            * ((ind n (h pq.1) ((a : ℤ) * pq.1) * ind n (h pq.2) ((a : ℤ) * pq.2) : ℕ) : ℤ) := by
      unfold U
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← hgcd a]
      split_ifs <;> simp
    rw [h1]
    simp_rw [Finset.sum_filter, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e he => ?_
    have he0 : 0 < e := Nat.pos_of_mem_divisors he
    have hed : e ∣ n := Nat.dvd_of_mem_divisors he
    have hd0 : 0 < n / e := Nat.div_pos (Nat.le_of_dvd hn0 hed) he0
    have hne : n = e * (n / e) := (Nat.mul_div_cancel' hed).symm
    have hpull : ∀ a : ℕ, (if e ∣ a then (moebius e : ℤ) else 0)
          * ((ind n (h pq.1) ((a : ℤ) * pq.1) * ind n (h pq.2) ((a : ℤ) * pq.2) : ℕ) : ℤ)
        = (moebius e : ℤ) * (((if e ∣ a then
              ind n (h pq.1) ((a : ℤ) * pq.1) * ind n (h pq.2) ((a : ℤ) * pq.2)
            else 0 : ℕ) : ℤ)) := by
      intro a
      split_ifs <;> simp
    rw [Finset.sum_congr rfl fun a _ => hpull a, ← Finset.mul_sum, ← Nat.cast_sum,
      sum_ind_eq_Nd he0 hd0 hne]
  have hreindex : ∑ e ∈ n.divisors, (moebius e : ℤ) * (Nd n (n / e) pq.1 pq.2 : ℤ)
      = ∑ d ∈ n.divisors, (moebius (n / d) : ℤ) * (Nd n d pq.1 pq.2 : ℤ) := by
    refine Eq.trans (Finset.sum_congr rfl fun e he => ?_)
      (Nat.sum_div_divisors n fun d => (moebius (n / d) : ℤ) * (Nd n d pq.1 pq.2 : ℤ))
    rw [Nat.div_div_self (Nat.dvd_of_mem_divisors he) hn0.ne']
  have hrestrict : ∑ d ∈ D n, (moebius (n / d) : ℤ) * (Nd n d pq.1 pq.2 : ℤ)
      = ∑ d ∈ n.divisors, (moebius (n / d) : ℤ) * (Nd n d pq.1 pq.2 : ℤ) :=
    Finset.sum_subset (D_subset_divisors n) fun d hd hnd => by
      rw [moebius_eq_zero_of_not_squarefree fun hs => hnd (mem_D.mpr ⟨hd, hs⟩), zero_mul]
  rw [hstep, hreindex, hrestrict]

end Paucity
