/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Paucity.Defs.Hn
public import Paucity.Defs.Degenerate
public import Paucity.Main.CountSmallM
public import Paucity.Estimates.DivisorBound

/-!
# Degenerate pairs are few

For every `ε > 0`, the pairs `(p, q) ∈ H n` that are degenerate for `n` — those with
`M n p q ≤ 1000 Q n max(gcd(p, n), gcd(q, n))` — number at most `C(ε) n^(1+ε)`, with `C`
depending only on `ε`. The `max` is attained at one of its two arguments, so the count
reduces to the one-sided count and its transpose.

## Main results

* `exists_card_smallSecond_le`: the one-sided count, with the `max` replaced by
  `gcd(q, n)`.
* `card_degenerate_le`: for every `ε > 0` there is `C > 0` bounding the number of pairs of
  `H n` that are degenerate for `n` by `C n^(1+ε)`, for every `n ≥ 5`.
-/

@[expose] public section

namespace Paucity

open Finset

/-- For every `ε > 0` there is `C > 0` such that the pairs of `H n` with
`M n p q ≤ 1000 Q n gcd(q, n)` — degeneracy with the `max` replaced by its second
argument — number at most `C n^(1+ε)`, for every `n ≥ 5`.

The constant is `(1 + 1/δ) C₃ K^(1+δ)` with `δ = min (ε/5) (1/5)`, `K` the constant of
`exists_bound_of_le_thousand_Q` and `C₃` that of `divisor_bound`, both at `δ`. -/
theorem exists_card_smallSecond_le {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 5 ≤ n →
      (((H n).filter fun pq =>
          M n pq.1 pq.2 ≤ 1000 * Q n * (Nat.gcd pq.2 n : ℝ)).card : ℝ)
        ≤ C * (n : ℝ) ^ (1 + ε) := by
  set δ : ℝ := min (ε / 5) (1 / 5)
  have hδ0 : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδ5 : δ ≤ 1 / 5 := min_le_right _ _
  have hδε : 5 * δ ≤ ε := by
    have : δ ≤ ε / 5 := min_le_left _ _
    linarith
  obtain ⟨K, hK1, hK⟩ := exists_bound_of_le_thousand_Q hδ0
  obtain ⟨C₃, hC₃0, hC₃⟩ := divisor_bound hδ0
  have hK0 : (0 : ℝ) < K := one_pos.trans_le hK1
  have hC2pos : (0 : ℝ) < 1 + 1 / δ := by positivity
  refine ⟨(1 + 1 / δ) * C₃ * K ^ (1 + δ),
    mul_pos (mul_pos hC2pos hC₃0) (Real.rpow_pos_of_pos hK0 _), fun n hn => ?_⟩
  have hn0 : n ≠ 0 := by omega
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  set X : ℝ := K * (n : ℝ) ^ (1 + 2 * δ) with hXdef
  have hX1 : (1 : ℝ) ≤ X := by
    rw [hXdef]
    exact hK1.trans (le_mul_of_one_le_right hK0.le (Real.one_le_rpow hn1 (by linarith)))
  set S : Finset (ℕ × ℕ) :=
    (H n).filter fun pq => M n pq.1 pq.2 ≤ 1000 * Q n * (Nat.gcd pq.2 n : ℝ) with hSdef
  set f : ℕ × ℕ → (ℕ × ℕ) × ℕ := fun pq => ((pq.1, pq.2 / Nat.gcd pq.2 n), Nat.gcd pq.2 n)
    with hfdef
  have hmaps : Set.MapsTo f ↑S ↑(hyperBox X ×ˢ n.divisors) := by
    rintro ⟨p, q⟩ hpq
    simp only [Finset.mem_coe, hSdef, mem_filter, mem_H, mem_T] at hpq
    obtain ⟨⟨⟨hp1, hq1, -⟩, -⟩, hM⟩ := hpq
    have hgdvd : Nat.gcd q n ∣ q := Nat.gcd_dvd_left _ _
    have hg0 : 0 < Nat.gcd q n := Nat.gcd_pos_of_pos_right _ (by omega)
    have hgR : (0 : ℝ) < (Nat.gcd q n : ℝ) := by exact_mod_cast hg0
    have hq'1 : 1 ≤ q / Nat.gcd q n :=
      (Nat.one_le_div_iff hg0).mpr (Nat.le_of_dvd (by omega) hgdvd)
    have hhq : (Nat.gcd q n : ℝ) * ((q / Nat.gcd q n : ℕ) : ℝ) ≤ (h q : ℝ) := by
      have hcast : Nat.gcd q n * (q / Nat.gcd q n) ≤ h q := by
        rw [Nat.mul_div_cancel' hgdvd]; exact le_h hq1
      exact_mod_cast hcast
    have key : (h p : ℝ) * ((q / Nat.gcd q n : ℕ) : ℝ) * (n.totient : ℝ) / (n : ℝ) ^ 2
        ≤ 1000 * Q n := by
      have hMu : (h p : ℝ) * (h q : ℝ) * (n.totient : ℝ) / (n : ℝ) ^ 2
          ≤ 1000 * Q n * (Nat.gcd q n : ℝ) := hM
      refine le_of_mul_le_mul_left ?_ hgR
      calc (Nat.gcd q n : ℝ) *
            ((h p : ℝ) * ((q / Nat.gcd q n : ℕ) : ℝ) * (n.totient : ℝ) / (n : ℝ) ^ 2)
          = (h p : ℝ) * ((Nat.gcd q n : ℝ) * ((q / Nat.gcd q n : ℕ) : ℝ)) * (n.totient : ℝ)
              / (n : ℝ) ^ 2 := by ring
        _ ≤ (h p : ℝ) * (h q : ℝ) * (n.totient : ℝ) / (n : ℝ) ^ 2 := by gcongr
        _ ≤ 1000 * Q n * (Nat.gcd q n : ℝ) := hMu
        _ = (Nat.gcd q n : ℝ) * (1000 * Q n) := by ring
    have hple : (p : ℝ) ≤ (h p : ℝ) := by exact_mod_cast le_h hp1
    have hprod : (p : ℝ) * ((q / Nat.gcd q n : ℕ) : ℝ) ≤ X :=
      (mul_le_mul_of_nonneg_right hple (by positivity)).trans
        (hK n hn _ (by positivity) key)
    simp only [Finset.mem_coe, hfdef, mem_product]
    exact ⟨mem_hyperBox hp1 hq'1 hprod, Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right _ _, hn0⟩⟩
  have hinj : Set.InjOn f ↑S := by
    intro a _ b _ hab
    simp only [hfdef, Prod.mk.injEq] at hab
    obtain ⟨⟨hfst, hquot⟩, hgcd⟩ := hab
    refine Prod.ext hfst ?_
    rw [← Nat.mul_div_cancel' (Nat.gcd_dvd_left a.2 n),
      ← Nat.mul_div_cancel' (Nat.gcd_dvd_left b.2 n), hquot, hgcd]
  have hcard : (S.card : ℝ) ≤ ((hyperBox X).card : ℝ) * ((n.divisors).card : ℝ) := by
    exact_mod_cast (Finset.card_le_card_of_injOn f hmaps hinj).trans_eq
      (Finset.card_product _ _)
  have hexp : (1 + 2 * δ) * (1 + δ) + δ ≤ 1 + ε := by
    nlinarith [mul_le_mul_of_nonneg_left hδ5 hδ0.le]
  calc (S.card : ℝ)
      ≤ ((hyperBox X).card : ℝ) * ((n.divisors).card : ℝ) := hcard
    _ ≤ (1 + 1 / δ) * X ^ (1 + δ) * (C₃ * (n : ℝ) ^ δ) :=
        mul_le_mul (card_hyperBox_le hδ0 hX1) (hC₃ n (by omega)) (by positivity) (by positivity)
    _ = (1 + 1 / δ) * C₃ * K ^ (1 + δ) * (n : ℝ) ^ ((1 + 2 * δ) * (1 + δ) + δ) := by
        rw [Real.rpow_add (by positivity) ((1 + 2 * δ) * (1 + δ)) δ, hXdef,
          Real.mul_rpow hK0.le (by positivity), ← Real.rpow_mul (Nat.cast_nonneg n)]
        ring
    _ ≤ (1 + 1 / δ) * C₃ * K ^ (1 + δ) * (n : ℝ) ^ (1 + ε) := by
        have hKpos := Real.rpow_pos_of_pos hK0 (1 + δ)
        exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn1 hexp)
          (by positivity)

/-- For every `ε > 0` there is `C > 0` such that the pairs of `H n` that are degenerate
for `n` number at most `C n^(1+ε)`, for every `n ≥ 5`.

The constant is `2 (1 + 1/δ) C₃ K^(1+δ)` with `δ = min (ε/5) (1/5)`, twice the constant of
`exists_card_smallSecond_le`. -/
theorem card_degenerate_le {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 5 ≤ n →
      (((H n).filter fun pq => Degenerate n pq.1 pq.2).card : ℝ)
        ≤ C * (n : ℝ) ^ (1 + ε) := by
  obtain ⟨C, hC0, hC⟩ := exists_card_smallSecond_le hε
  refine ⟨2 * C, by linarith, fun n hn => ?_⟩
  set S : Finset (ℕ × ℕ) :=
    (H n).filter fun pq => M n pq.1 pq.2 ≤ 1000 * Q n * (Nat.gcd pq.2 n : ℝ) with hSdef
  have hsub : ((H n).filter fun pq => Degenerate n pq.1 pq.2) ⊆ S ∪ S.image Prod.swap := by
    intro pq hpq
    obtain ⟨hHn, hdeg⟩ := mem_filter.mp hpq
    rw [degenerate_iff] at hdeg
    rcases max_choice ((Nat.gcd pq.1 n : ℝ)) ((Nat.gcd pq.2 n : ℝ)) with hmax | hmax
    · rw [hmax] at hdeg
      refine mem_union_right _ (mem_image.mpr ⟨pq.swap, ?_, Prod.swap_swap pq⟩)
      rw [hSdef, mem_filter, Prod.fst_swap, Prod.snd_swap, M_symm]
      exact ⟨swap_mem_H hHn, hdeg⟩
    · rw [hmax] at hdeg
      refine mem_union_left _ ?_
      rw [hSdef, mem_filter]
      exact ⟨hHn, hdeg⟩
  have hcardN : ((H n).filter fun pq => Degenerate n pq.1 pq.2).card ≤ 2 * S.card := by
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le S (S.image Prod.swap)
    have h3 := Finset.card_image_le (f := Prod.swap) (s := S)
    omega
  have hSC : (S.card : ℝ) ≤ C * (n : ℝ) ^ (1 + ε) := by rw [hSdef]; exact hC n hn
  calc (((H n).filter fun pq => Degenerate n pq.1 pq.2).card : ℝ)
      ≤ 2 * (S.card : ℝ) := by exact_mod_cast hcardN
    _ ≤ 2 * C * (n : ℝ) ^ (1 + ε) := by linarith

end Paucity
