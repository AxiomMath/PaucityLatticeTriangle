/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Paucity.Defs.E
public import Paucity.Defs.Hn
public import Paucity.Defs.Ln
public import Paucity.Defs.M
public import Paucity.Defs.Q
public import Paucity.Defs.S
public import Paucity.Defs.Degenerate
public import Paucity.Defs.Lat
public import Paucity.Defs.Resonant
public import Paucity.Counting.HnLower
public import Paucity.Counting.LSubset
public import Paucity.Estimates.QLower
public import Paucity.Main.CountDegen
public import Paucity.Main.CountResonant
public import Paucity.Main.CountSmallM
public import Paucity.External.Lnz
public import Paucity.Lattice.Reduction

/-!
# Paucity of lattice triangles

For a lattice predicate `P` satisfying the Larsen–Norton–Zykoski criterion `LNZ P`, the
proportion `#(L P n) / #(H n)` of lattice triangles among the primitive obtuse rational
triangles with denominator `n` is at most `c(ε) / n^(1-ε)`.

## Main results

* `card_L_div_card_H_le`: assuming `LNZ P`, for every `ε > 0` there is `c > 0` with
  `#(L P n) / #(H n) ≤ c / n^(1-ε)` for every `n ≥ 5`.
-/

@[expose] public section

namespace Paucity

open Finset

/-- Paucity of lattice triangles: for a lattice predicate `P` satisfying the
Larsen–Norton–Zykoski criterion `LNZ P`, and every `ε > 0`, there is `c > 0` such that

    #(L P n) / #(H n) ≤ c / n ^ (1 - ε)

for every `n ≥ 5`. The constant `c` depends only on `ε` and is quantified before `n`.

The conclusion is conditional on `LNZ P`, which is assumed rather than proved. -/
theorem card_L_div_card_H_le {P : LatPred} (hLNZ : LNZ P) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 5 ≤ n →
      ((L P n).card : ℝ) / ((H n).card : ℝ) ≤ c / (n : ℝ) ^ (1 - ε) := by
  obtain ⟨c₀, hc₀, hH⟩ := exists_card_H_lower
  obtain ⟨Ca, hCa, hsmallM⟩ := card_smallM_le hε
  obtain ⟨Cb, hCb, hdegen⟩ := card_degenerate_le hε
  obtain ⟨Cc, hCc, hreson⟩ := card_resonant_le hε
  refine ⟨(Ca + Cb + Cc) / c₀, by positivity, fun n hn => ?_⟩
  have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hsub : L P n ⊆ ((H n).filter fun pq => M n pq.1 pq.2 < 1000 * Q n)
      ∪ ((H n).filter fun pq => Degenerate n pq.1 pq.2)
      ∪ ((H n).filter fun pq => Resonant n pq.1 pq.2) := by
    rintro ⟨p, q⟩ hpqL
    obtain ⟨hpqH, hS⟩ := mem_filter.mp (L_subset_witnesses_le_two hLNZ hn hpqL)
    rcases lt_or_ge (M n p q) (1000 * Q n) with hsmall | hbig
    · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hpqH, hsmall⟩))
    · have hQ2 : (2 : ℝ) ≤ Q n := two_le_Q (by omega)
      have hSr : ((S n p q : ℕ) : ℝ) ≤ 2 := by exact_mod_cast hS
      have hE : M n p q / 2 ≤ |E n p q| := by
        have habs := neg_le_abs (E n p q)
        have hSME := S_eq_M_add_E n p q
        linarith
      rcases resonant_or_degenerate hn hpqH hbig hE with hres | hdeg
      · exact mem_union_right _ (mem_filter.mpr ⟨hpqH, hres⟩)
      · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hpqH, hdeg⟩))
  have hcard : (L P n).card
      ≤ ((H n).filter fun pq => M n pq.1 pq.2 < 1000 * Q n).card
        + ((H n).filter fun pq => Degenerate n pq.1 pq.2).card
        + ((H n).filter fun pq => Resonant n pq.1 pq.2).card :=
    (card_le_card hsub).trans <|
      (card_union_le _ _).trans (Nat.add_le_add_right (card_union_le _ _) _)
  have hLbound : ((L P n).card : ℝ) ≤ (Ca + Cb + Cc) * (n : ℝ) ^ (1 + ε) := by
    have ha := hsmallM n hn
    have hb := hdegen n hn
    have hc := hreson n hn
    have hcast := (Nat.cast_le (α := ℝ)).mpr hcard
    push_cast at hcast
    rw [add_mul, add_mul]
    linarith
  have hHlow : c₀ * (n : ℝ) ^ 2 ≤ ((H n).card : ℝ) := hH n hn
  have hH0 : (0 : ℝ) < ((H n).card : ℝ) := lt_of_lt_of_le (by positivity) hHlow
  have hrpow0 : (0 : ℝ) < (n : ℝ) ^ (1 - ε) := Real.rpow_pos_of_pos hn0 _
  have hpow : (n : ℝ) ^ (1 + ε) * (n : ℝ) ^ (1 - ε) = (n : ℝ) ^ 2 := by
    rw [← Real.rpow_natCast (n : ℝ) 2, ← Real.rpow_add hn0]
    norm_num
  rw [div_le_div_iff₀ hH0 hrpow0]
  calc ((L P n).card : ℝ) * (n : ℝ) ^ (1 - ε)
      ≤ (Ca + Cb + Cc) * (n : ℝ) ^ (1 + ε) * (n : ℝ) ^ (1 - ε) :=
        mul_le_mul_of_nonneg_right hLbound hrpow0.le
    _ = (Ca + Cb + Cc) * (n : ℝ) ^ 2 := by rw [mul_assoc, hpow]
    _ ≤ (Ca + Cb + Cc) / c₀ * ((H n).card : ℝ) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hc₀]
        linarith [mul_le_mul_of_nonneg_left hHlow (by positivity : (0 : ℝ) ≤ Ca + Cb + Cc)]

end Paucity
