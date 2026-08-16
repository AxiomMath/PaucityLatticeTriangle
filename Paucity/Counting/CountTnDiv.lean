/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Tactic.Ring
public import Paucity.Defs.Tn

/-!
# Counting the dilates of `T n`

The pairs of the obtuse triangle `T n` whose two coordinates are both divisible by `e` are
counted by the binomial coefficient `C((n - 1) / (2 * e), 2)`, in ordinary `Nat` division.

## Main results

* `card_filter_lt_prod`: the pairs from a finset `s` in strictly increasing order number
  `C(#s, 2)`.
* `card_T_filter_dvd`: `#{(p, q) ∈ T n : e ∣ p, e ∣ q} = C((n - 1) / (2 * e), 2)` for `0 < e`.
-/

@[expose] public section

namespace Paucity

open Finset

/-- The ordered pairs from `s` in increasing order number `C(#s, 2)`. -/
theorem card_filter_lt_prod {α : Type*} [LinearOrder α] (s : Finset α) :
    ((s ×ˢ s).filter fun x : α × α => x.1 < x.2).card = s.card.choose 2 := by
  classical
  set L := (s ×ˢ s).filter fun x : α × α => x.1 < x.2 with hL
  set G := (s ×ˢ s).filter fun x : α × α => x.2 < x.1 with hG
  have hcardG : G.card = L.card := by
    refine card_nbij' Prod.swap Prod.swap (fun x hx => ?_) (fun x hx => ?_)
      (fun _ _ => Prod.swap_swap _) (fun _ _ => Prod.swap_swap _)
    · simp only [mem_coe, hG, hL, mem_filter, mem_product, Prod.fst_swap, Prod.snd_swap] at hx ⊢
      exact ⟨⟨hx.1.2, hx.1.1⟩, hx.2⟩
    · simp only [mem_coe, hG, hL, mem_filter, mem_product, Prod.fst_swap, Prod.snd_swap] at hx ⊢
      exact ⟨⟨hx.1.2, hx.1.1⟩, hx.2⟩
  have hdisj : Disjoint L G := by
    rw [Finset.disjoint_left]
    intro x hxL hxG
    rw [hL, mem_filter] at hxL
    rw [hG, mem_filter] at hxG
    exact absurd hxG.2 (not_lt.mpr hxL.2.le)
  have hunion : s.offDiag = L ∪ G := by
    ext x
    simp only [mem_offDiag, mem_union, hL, hG, mem_filter, mem_product]
    constructor
    · rintro ⟨h1, h2, hne⟩
      rcases lt_or_gt_of_ne hne with h | h
      · exact Or.inl ⟨⟨h1, h2⟩, h⟩
      · exact Or.inr ⟨⟨h1, h2⟩, h⟩
    · rintro (⟨⟨h1, h2⟩, h⟩ | ⟨⟨h1, h2⟩, h⟩)
      · exact ⟨h1, h2, ne_of_lt h⟩
      · exact ⟨h1, h2, (ne_of_lt h).symm⟩
  have htwo : L.card * 2 = s.card * (s.card - 1) := by
    have h := offDiag_card (s := s)
    rw [hunion, card_union_of_disjoint hdisj, hcardG] at h
    have hs : s.card * s.card - s.card = s.card * (s.card - 1) := by
      cases Nat.eq_zero_or_pos s.card with
      | inl h0 => simp [h0]
      | inr h0 => rw [Nat.mul_sub, Nat.mul_one]
    omega
  rw [Nat.choose_two_right, ← htwo, Nat.mul_div_cancel _ (by omega)]

/-- The pairs of `T n` divisible by `e` are counted by a binomial coefficient. -/
theorem card_T_filter_dvd {n e : ℕ} (he : 0 < e) :
    ((T n).filter fun pq => e ∣ pq.1 ∧ e ∣ pq.2).card
      = ((n - 1) / (2 * e)).choose 2 := by
  have he2 : 0 < 2 * e := by omega
  set K := (n - 1) / (2 * e) with hK
  have htarget :
      ((Icc 1 K ×ˢ Icc 1 K).filter fun x : ℕ × ℕ => x.1 < x.2).card = K.choose 2 := by
    rw [card_filter_lt_prod, Nat.card_Icc, Nat.add_sub_cancel]
  rw [← htarget]
  refine card_nbij' (fun pq => (pq.1 / e, (pq.1 + pq.2) / e))
      (fun as => (e * as.1, e * (as.2 - as.1))) ?_ ?_ ?_ ?_
  · rintro ⟨p, q⟩ hpq
    rw [mem_coe, mem_filter, mem_T] at hpq
    obtain ⟨⟨hp, hq, hsum⟩, hep, heq⟩ := hpq
    obtain ⟨a, rfl⟩ := hep
    obtain ⟨b, rfl⟩ := heq
    have ha : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr (by rintro rfl; simp at hp)
    have hb : 1 ≤ b := Nat.one_le_iff_ne_zero.mpr (by rintro rfl; simp at hq)
    have hdiv1 : e * a / e = a := Nat.mul_div_cancel_left a he
    have hdiv2 : (e * a + e * b) / e = a + b := by
      rw [← Nat.mul_add, Nat.mul_div_cancel_left _ he]
    have hsK : a + b ≤ K := by
      rw [hK, Nat.le_div_iff_mul_le he2]
      calc (a + b) * (2 * e) = 2 * (e * a + e * b) := by ring
        _ ≤ n - 1 := by omega
    simp only [mem_coe, mem_filter, mem_product, mem_Icc, hdiv1, hdiv2]
    exact ⟨⟨⟨ha, by omega⟩, ⟨by omega, hsK⟩⟩, by omega⟩
  · rintro ⟨a, s⟩ has
    simp only [mem_coe, mem_filter, mem_product, mem_Icc] at has
    obtain ⟨⟨⟨ha, -⟩, hs, hsK⟩, hlt⟩ := has
    have hcollapse : e * a + e * (s - a) = s * e := by
      rw [← Nat.mul_add, Nat.add_sub_cancel' hlt.le, Nat.mul_comm]
    have hle : s * (2 * e) ≤ n - 1 := by rw [hK] at hsK; exact (Nat.le_div_iff_mul_le he2).mp hsK
    have hpos : 0 < s * (2 * e) := Nat.mul_pos (by omega) he2
    have hlin : s * (2 * e) = 2 * (s * e) := by ring
    rw [mem_coe, mem_filter, mem_T]
    refine ⟨⟨Nat.mul_pos he ha, Nat.mul_pos he (by omega), ?_⟩,
      Dvd.intro a rfl, Dvd.intro (s - a) rfl⟩
    rw [hcollapse]
    omega
  · rintro ⟨p, q⟩ hpq
    rw [mem_coe, mem_filter] at hpq
    obtain ⟨-, hep, heq⟩ := hpq
    obtain ⟨a, rfl⟩ := hep
    obtain ⟨b, rfl⟩ := heq
    have hdiv1 : e * a / e = a := Nat.mul_div_cancel_left a he
    have hdiv2 : (e * a + e * b) / e = a + b := by
      rw [← Nat.mul_add, Nat.mul_div_cancel_left _ he]
    simp [hdiv1, hdiv2]
  · rintro ⟨a, s⟩ has
    simp only [mem_coe, mem_filter, mem_product, mem_Icc] at has
    obtain ⟨⟨-, -⟩, hlt⟩ := has
    have hdiv1 : e * a / e = a := Nat.mul_div_cancel_left a he
    have hcollapse : e * a + e * (s - a) = e * s := by
      rw [← Nat.mul_add, Nat.add_sub_cancel' hlt.le]
    simp [hdiv1, hcollapse, Nat.mul_div_cancel_left _ he]

end Paucity
