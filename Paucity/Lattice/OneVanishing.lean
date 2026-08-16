/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Data.Int.Interval
public import Mathlib.RingTheory.Int.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring
public import Paucity.Defs.LambdaKL

/-!
# A vanishing coordinate bounds a dyadic class

For `d ≥ 1`, `(p,q) ∈ ℤ²` and reals `K, L ≥ 1`, if some nonzero integer `k'` has `|k'| ≤ 8K` and
`(k',0) ∈ Λ_d(p,q)`, then

    #Λ_d(K,L;p,q) ≤ 24 K L gcd(p,d) / d.

## Main results

* `div_gcd_dvd_of_dvd_mul`: if `d ∣ x p` then `d / gcd(p,d) ∣ x`.
* `card_le_of_pairwise_congr`: integers in `(-2K, 2K)` that are pairwise congruent modulo `m`
  number at most `8K/m`, as soon as `1 ≤ m ≤ 8K`.
* `card_le_of_mem_annulus`: the integers of the annulus `L ≤ |l| < 2L` number at most `3L`.
* `card_dyadicBox_le_of_axis_point`: the bound on `#Λ_d(K,L;p,q)` above.
-/

@[expose] public section

namespace Paucity

open Finset

/-- If `d ∣ x p` then `d / gcd(p,d) ∣ x`. -/
theorem div_gcd_dvd_of_dvd_mul {p d : ℕ} (hd : 0 < d) {x : ℤ}
    (h : (d : ℤ) ∣ x * (p : ℤ)) : ((d / Nat.gcd p d : ℕ) : ℤ) ∣ x := by
  have hg : 0 < Nat.gcd p d := Nat.gcd_pos_of_pos_right p hd
  have hpg : Nat.gcd p d ∣ p := Nat.gcd_dvd_left p d
  have hdg : Nat.gcd p d ∣ d := Nat.gcd_dvd_right p d
  have hcop : Nat.Coprime (p / Nat.gcd p d) (d / Nat.gcd p d) :=
    Nat.coprime_div_gcd_div_gcd hg
  have hgne : ((Nat.gcd p d : ℕ) : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hg.ne'
  have hd' : (d : ℤ) = ((Nat.gcd p d : ℕ) : ℤ) * ((d / Nat.gcd p d : ℕ) : ℤ) := by
    rw [← Nat.cast_mul, Nat.mul_div_cancel' hdg]
  have hp' : (p : ℤ) = ((Nat.gcd p d : ℕ) : ℤ) * ((p / Nat.gcd p d : ℕ) : ℤ) := by
    rw [← Nat.cast_mul, Nat.mul_div_cancel' hpg]
  rw [hd', hp'] at h
  have h2 : ((d / Nat.gcd p d : ℕ) : ℤ) ∣ x * ((p / Nat.gcd p d : ℕ) : ℤ) := by
    refine (mul_dvd_mul_iff_left hgne).mp ?_
    rw [show ((Nat.gcd p d : ℕ) : ℤ) * (x * ((p / Nat.gcd p d : ℕ) : ℤ))
        = x * (((Nat.gcd p d : ℕ) : ℤ) * ((p / Nat.gcd p d : ℕ) : ℤ)) by ring]
    exact h
  exact (Nat.isCoprime_iff_coprime.mpr hcop.symm).dvd_of_dvd_mul_right h2

/-- Integers that lie in the interval `(-2K, 2K)` and are pairwise congruent modulo `m` number at
most `8K/m`, as soon as `1 ≤ m ≤ 8K`. -/
theorem card_le_of_pairwise_congr {m : ℕ} (hm : 0 < m) {K : ℝ} (hmK : (m : ℝ) ≤ 8 * K)
    {S : Finset ℤ} (hbd : ∀ k ∈ S, |(k : ℝ)| < 2 * K)
    (hcong : ∀ k₁ ∈ S, ∀ k₂ ∈ S, (m : ℤ) ∣ k₁ - k₂) :
    (S.card : ℝ) ≤ 8 * K / m := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hK : 0 < K := by linarith
  have hdiv : ∀ a b : ℝ, a ≤ b → a / (m : ℝ) ≤ b / (m : ℝ) := by
    intro a b hab
    have h := mul_le_mul_of_nonneg_right hab (le_of_lt (inv_pos.mpr hm0))
    simpa [div_eq_mul_inv] using h
  have hone : (1 : ℝ) ≤ 8 * K / (m : ℝ) := by
    have h := hdiv (m : ℝ) (8 * K) hmK
    rwa [div_self hm0.ne'] at h
  have hsplit : 8 * K / (m : ℝ) = 4 * K / (m : ℝ) + 4 * K / (m : ℝ) := by
    field_simp
    ring
  have hcrude : (S.card : ℝ) ≤ 4 * K / (m : ℝ) + 1 := by
    rcases S.eq_empty_or_nonempty with rfl | ⟨c, hc⟩
    · have h : (0 : ℝ) ≤ 4 * K / (m : ℝ) := by positivity
      simp only [Finset.card_empty, Nat.cast_zero]
      linarith
    · have hrep : ∀ k ∈ S, (m : ℤ) * ((k - c) / (m : ℤ)) = k - c := fun k hk =>
        Int.mul_ediv_cancel' (hcong k hk c hc)
      have hval : ∀ k ∈ S, ((((k - c) / (m : ℤ) : ℤ)) : ℝ) = ((k : ℝ) - (c : ℝ)) / (m : ℝ) := by
        intro k hk
        have h : ((m : ℝ)) * ((((k - c) / (m : ℤ) : ℤ)) : ℝ) = (k : ℝ) - (c : ℝ) := by
          exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) (hrep k hk)
        field_simp
        linarith
      have hmemIcc : ∀ k ∈ S, ((k - c) / (m : ℤ) : ℤ) ∈
          Finset.Icc ⌈(-(2 * K) - (c : ℝ)) / (m : ℝ)⌉ ⌊(2 * K - (c : ℝ)) / (m : ℝ)⌋ := by
        intro k hk
        obtain ⟨h1, h2⟩ := abs_lt.mp (hbd k hk)
        rw [Finset.mem_Icc]
        refine ⟨Int.ceil_le.mpr ?_, Int.le_floor.mpr ?_⟩
        · rw [hval k hk]; exact hdiv _ _ (by linarith)
        · rw [hval k hk]; exact hdiv _ _ (by linarith)
      have hinj : Set.InjOn (fun k : ℤ => (k - c) / (m : ℤ)) S := by
        intro a ha b hb hab
        have h1 := hrep a ha
        have h2 := hrep b hb
        simp only at hab
        rw [hab] at h1
        omega
      have hcard := Finset.card_le_card_of_injOn _ hmemIcc hinj
      rw [Int.card_Icc] at hcard
      have hlo : ((-(2 * K) - (c : ℝ)) / (m : ℝ)) ≤
          ((⌈(-(2 * K) - (c : ℝ)) / (m : ℝ)⌉ : ℤ) : ℝ) := Int.le_ceil _
      have hhi : ((⌊(2 * K - (c : ℝ)) / (m : ℝ)⌋ : ℤ) : ℝ) ≤ (2 * K - (c : ℝ)) / (m : ℝ) :=
        Int.floor_le _
      have hle : ⌈(-(2 * K) - (c : ℝ)) / (m : ℝ)⌉ ≤ ⌊(2 * K - (c : ℝ)) / (m : ℝ)⌋ := by
        have h := hmemIcc c hc
        rw [Finset.mem_Icc] at h
        omega
      have hcardZ : (S.card : ℤ) ≤
          ⌊(2 * K - (c : ℝ)) / (m : ℝ)⌋ + 1 - ⌈(-(2 * K) - (c : ℝ)) / (m : ℝ)⌉ := by
        omega
      have hcardR : (S.card : ℝ) ≤
          ((⌊(2 * K - (c : ℝ)) / (m : ℝ)⌋ : ℤ) : ℝ) + 1
            - ((⌈(-(2 * K) - (c : ℝ)) / (m : ℝ)⌉ : ℤ) : ℝ) := by
        have h : ((S.card : ℤ) : ℝ) ≤
            ((⌊(2 * K - (c : ℝ)) / (m : ℝ)⌋ + 1
              - ⌈(-(2 * K) - (c : ℝ)) / (m : ℝ)⌉ : ℤ) : ℝ) := Int.cast_le.mpr hcardZ
        push_cast at h
        linarith
      have hlen : (2 * K - (c : ℝ)) / (m : ℝ) - (-(2 * K) - (c : ℝ)) / (m : ℝ)
          = 4 * K / (m : ℝ) := by
        field_simp
        ring
      linarith
  rcases le_or_gt 1 (4 * K / (m : ℝ)) with h | h
  · linarith
  · have hcard1 : S.card ≤ 1 := by
      by_contra hcon
      have h2 : 2 ≤ S.card := by omega
      have h2R : (2 : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast h2
      linarith
    have h1 : (S.card : ℝ) ≤ 1 := by exact_mod_cast hcard1
    linarith

/-- The integers of the annulus `L ≤ |l| < 2L` number at most `3L`, for every real `L ≥ 1`. -/
theorem card_le_of_mem_annulus {L : ℝ} (hL : 1 ≤ L) {T : Finset ℤ}
    (hT : ∀ l ∈ T, L ≤ |(l : ℝ)| ∧ |(l : ℝ)| < 2 * L) :
    (T.card : ℝ) ≤ 3 * L := by
  have hceil : ⌈L⌉ ≤ ⌈2 * L⌉ := Int.ceil_le_ceil (by linarith)
  have hAB : ∀ (U : Finset ℤ) (f : ℤ → ℤ), Set.InjOn f U →
      (∀ l ∈ U, L ≤ ((f l : ℤ) : ℝ) ∧ ((f l : ℤ) : ℝ) < 2 * L) →
      (U.card : ℤ) ≤ ⌈2 * L⌉ - ⌈L⌉ := by
    intro U f hinj hmem
    have hsub : ∀ l ∈ U, f l ∈ Finset.Ico ⌈L⌉ ⌈2 * L⌉ := by
      intro l hl
      obtain ⟨h1, h2⟩ := hmem l hl
      rw [Finset.mem_Ico]
      exact ⟨Int.ceil_le.mpr h1, Int.lt_ceil.mpr h2⟩
    have h := Finset.card_le_card_of_injOn f hsub hinj
    rw [Int.card_Ico] at h
    omega
  have hpos : ((T.filter fun l => 0 < l).card : ℤ) ≤ ⌈2 * L⌉ - ⌈L⌉ := by
    refine hAB _ (fun l => l) (fun _ _ _ _ h => h) ?_
    intro l hl
    rw [Finset.mem_filter] at hl
    obtain ⟨h1, h2⟩ := hT l hl.1
    have hl0 : (0 : ℝ) < (l : ℝ) := by exact_mod_cast hl.2
    rw [abs_of_pos hl0] at h1 h2
    exact ⟨h1, h2⟩
  have hneg : ((T.filter fun l => ¬ 0 < l).card : ℤ) ≤ ⌈2 * L⌉ - ⌈L⌉ := by
    refine hAB _ (fun l => -l) (fun _ _ _ _ h => neg_injective h) ?_
    intro l hl
    rw [Finset.mem_filter] at hl
    obtain ⟨h1, h2⟩ := hT l hl.1
    have hl0 : (l : ℝ) < 0 := by
      rcases lt_trichotomy l 0 with h | h | h
      · exact_mod_cast h
      · rw [h] at h1; simp only [Int.cast_zero, abs_zero] at h1; linarith
      · exact absurd h hl.2
    rw [abs_of_neg hl0] at h1 h2
    push_cast
    exact ⟨h1, h2⟩
  have hsum : (T.filter fun l => 0 < l).card + (T.filter fun l => ¬ 0 < l).card = T.card :=
    Finset.card_filter_add_card_filter_not (fun l : ℤ => 0 < l)
  have hcardZ : (T.card : ℤ) ≤ 2 * (⌈2 * L⌉ - ⌈L⌉) := by omega
  have hcardR : (T.card : ℝ) ≤ 2 * ((⌈2 * L⌉ : ℤ) : ℝ) - 2 * ((⌈L⌉ : ℤ) : ℝ) := by
    have h : ((T.card : ℤ) : ℝ) ≤ ((2 * (⌈2 * L⌉ - ⌈L⌉) : ℤ) : ℝ) := Int.cast_le.mpr hcardZ
    push_cast at h
    linarith
  have hAle : L ≤ ((⌈L⌉ : ℤ) : ℝ) := Int.le_ceil L
  have hBlt : ((⌈2 * L⌉ : ℤ) : ℝ) < 2 * L + 1 := Int.ceil_lt_add_one (2 * L)
  have hA1 : (1 : ℤ) ≤ ⌈L⌉ := by
    have h : (0 : ℤ) < ⌈L⌉ := Int.lt_ceil.mpr (by push_cast; linarith)
    omega
  have hA1R : (1 : ℝ) ≤ ((⌈L⌉ : ℤ) : ℝ) := by exact_mod_cast hA1
  rcases le_or_gt (⌈2 * L⌉ - ⌈L⌉) 1 with hc | hc
  · have hcR : ((⌈2 * L⌉ : ℤ) : ℝ) - ((⌈L⌉ : ℤ) : ℝ) ≤ 1 := by exact_mod_cast hc
    linarith
  · have hBA : ((⌈L⌉ : ℤ) : ℝ) + 2 ≤ ((⌈2 * L⌉ : ℤ) : ℝ) := by
      have h : ⌈L⌉ + 2 ≤ ⌈2 * L⌉ := by omega
      exact_mod_cast h
    have hL1 : 1 < L := by linarith
    have hA2 : (2 : ℤ) ≤ ⌈L⌉ := by
      have h : (1 : ℤ) < ⌈L⌉ := Int.lt_ceil.mpr (by push_cast; linarith)
      omega
    have hA2R : (2 : ℝ) ≤ ((⌈L⌉ : ℤ) : ℝ) := by exact_mod_cast hA2
    rcases le_or_gt L 2 with hL2 | hL2
    · linarith
    · linarith

/-- If the dual lattice `Λ_d(p,q)` contains a nonzero point `(k', 0)` on the horizontal axis with
`|k'| ≤ 8K`, then the dyadic block `Λ_d(K,L;p,q)` is small:

    #Λ_d(K,L;p,q) ≤ 24 K L gcd(p,d) / d.
-/
theorem card_dyadicBox_le_of_axis_point {d p q : ℕ} (hd : 1 ≤ d) {K L : ℝ}
    (hK : 1 ≤ K) (hL : 1 ≤ L) {k' : ℤ} (hk'0 : k' ≠ 0) (hk'K : |(k' : ℝ)| ≤ 8 * K)
    (hk'mem : ((k', 0) : ℤ × ℤ) ∈ dualLattice d p q) :
    ((dyadicBox d K L p q).card : ℝ) ≤ 24 * K * L * (Nat.gcd p d : ℝ) / (d : ℝ) := by
  have hd0 : 0 < d := hd
  have hg : 0 < Nat.gcd p d := Nat.gcd_pos_of_pos_right p hd0
  have hdg : Nat.gcd p d ∣ d := Nat.gcd_dvd_right p d
  set m := d / Nat.gcd p d with hm_def
  have hgm : Nat.gcd p d * m = d := Nat.mul_div_cancel' hdg
  have hm : 0 < m := Nat.div_pos (Nat.le_of_dvd hd0 hdg) hg
  have hdvdk' : (d : ℤ) ∣ k' * (p : ℤ) := by
    have h := mem_dualLattice.mp hk'mem
    simpa using h
  have hmk' : (m : ℤ) ∣ k' := div_gcd_dvd_of_dvd_mul hd0 hdvdk'
  have hmabs : (m : ℤ) ≤ |k'| := by
    refine Int.le_of_dvd (abs_pos.mpr hk'0) ?_
    rcases abs_choice k' with h | h
    · rw [h]; exact hmk'
    · rw [h]; exact dvd_neg.mpr hmk'
  have hmK : (m : ℝ) ≤ 8 * K := by
    have h1 : ((m : ℤ) : ℝ) ≤ ((|k'| : ℤ) : ℝ) := Int.cast_le.mpr hmabs
    rw [Int.cast_abs] at h1
    push_cast at h1
    linarith
  have hfib : (dyadicBox d K L p q).card
      = ∑ l ∈ (dyadicBox d K L p q).image Prod.snd,
        ((dyadicBox d K L p q).filter fun x => x.2 = l).card :=
    Finset.card_eq_sum_card_fiberwise fun x hx => Finset.mem_image_of_mem _ hx
  have hfibbd : ∀ l ∈ (dyadicBox d K L p q).image Prod.snd,
      (((dyadicBox d K L p q).filter fun x => x.2 = l).card : ℝ) ≤ 8 * K / (m : ℝ) := by
    intro l _
    have hinj : Set.InjOn (Prod.fst : ℤ × ℤ → ℤ)
        ((dyadicBox d K L p q).filter fun x => x.2 = l) := by
      intro a ha b hb hab
      rw [Finset.mem_coe, Finset.mem_filter] at ha hb
      exact Prod.ext hab (by rw [ha.2, hb.2])
    rw [← Finset.card_image_of_injOn hinj]
    refine card_le_of_pairwise_congr hm hmK ?_ ?_
    · intro k hk
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hk
      rw [Finset.mem_filter] at hx
      exact (mem_dyadicBox.mp hx.1).2.2.1
    · intro k₁ hk₁ k₂ hk₂
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hk₁
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hk₂
      rw [Finset.mem_filter] at hx hy
      have h1 : (d : ℤ) ∣ x.1 * (p : ℤ) + x.2 * (q : ℤ) :=
        mem_dualLattice.mp (mem_latticeBox.mp (mem_dyadicBox.mp hx.1).1).2
      have h2 : (d : ℤ) ∣ y.1 * (p : ℤ) + y.2 * (q : ℤ) :=
        mem_dualLattice.mp (mem_latticeBox.mp (mem_dyadicBox.mp hy.1).1).2
      have hsnd : x.2 = y.2 := by rw [hx.2, hy.2]
      refine div_gcd_dvd_of_dvd_mul hd0 ?_
      have hsub := dvd_sub h1 h2
      have heq : (x.1 * (p : ℤ) + x.2 * (q : ℤ)) - (y.1 * (p : ℤ) + y.2 * (q : ℤ))
          = (x.1 - y.1) * (p : ℤ) := by rw [hsnd]; ring
      rwa [heq] at hsub
  have hTcard : (((dyadicBox d K L p q).image Prod.snd).card : ℝ) ≤ 3 * L := by
    refine card_le_of_mem_annulus hL ?_
    intro l hl
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hl
    have h := mem_dyadicBox.mp hx
    exact ⟨h.2.2.2.1, h.2.2.2.2⟩
  have h8 : (0 : ℝ) ≤ 8 * K / (m : ℝ) := by
    have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    have hK0 : (0 : ℝ) < K := by linarith
    positivity
  calc ((dyadicBox d K L p q).card : ℝ)
      = ∑ l ∈ (dyadicBox d K L p q).image Prod.snd,
          (((dyadicBox d K L p q).filter fun x => x.2 = l).card : ℝ) := by
        rw [hfib]; push_cast; ring
    _ ≤ ∑ _l ∈ (dyadicBox d K L p q).image Prod.snd, (8 * K / (m : ℝ)) :=
        Finset.sum_le_sum hfibbd
    _ = (((dyadicBox d K L p q).image Prod.snd).card : ℝ) * (8 * K / (m : ℝ)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (3 * L) * (8 * K / (m : ℝ)) := mul_le_mul_of_nonneg_right hTcard h8
    _ = 24 * K * L * (Nat.gcd p d : ℝ) / (d : ℝ) := by
        have hgR : ((Nat.gcd p d : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hg.ne'
        have hmR : ((m : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
        have hdR : (d : ℝ) = (Nat.gcd p d : ℝ) * (m : ℝ) := by exact_mod_cast hgm.symm
        rw [hdR]
        field_simp
        ring

end Paucity
