/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Paucity.Defs.Ad
public import Paucity.Defs.Dn
public import Paucity.Defs.Degenerate
public import Paucity.Defs.Hd
public import Paucity.Defs.Hn
public import Paucity.Defs.Maj
public import Paucity.Counting.HSumLt
public import Paucity.Estimates.WeightSum
public import Paucity.Defs.Notation.Res

/-!
# A dominant axis family forces degeneracy

For `n ≥ 5`, `(p,q) ∈ H_n` and `d ∈ D_n`, if

    (1/d) ∑_{(0,ℓ) ∈ A_d(p,q)} ν_{d,H^{(d)}_n(p)}(0) · ν_{d,H^{(d)}_n(q)}(ℓ)
      ≥ (1 + log n) M_n(p,q) / (20 Q(n)),

then `(p,q)` is degenerate for `n`. The first of the two axis strata of `W` can be large without
any resonance, since `ν` is constant along the vanishing coordinate and the family contributes
`H^{(d)}_n(p)/d` times a harmonic sum; the only way for it to dominate is for `gcd(q,d)` to be
large, which is exactly `Degenerate`.

## Main results

* `res_eq_of_symm_repr`: the least nonnegative residue of a symmetric representative `j` mod `g` is
  `j` for `j ≥ 0` and `j + g` for `j < 0`.
* `sum_inv_abs_le`: the axis harmonic sum `∑_{(0,ℓ) ∈ A_d(p,q)} 1/(2|ℓ|)` is at most
  `g(1 + log g)/d` for `g = gcd(q,d)`.
* `degenerate_of_axis_sum`: a first axis family contributing at least
  `(1 + log n) M_n(p,q) / (20 Q(n))` forces `(p,q)` to be degenerate for `n`.
* `mem_H_fifteen`, `mem_D_fifteen`: `(2,5) ∈ H 15` and `5 ∈ D 15`.
-/

@[expose] public section

namespace Paucity

open Finset

/-- The least nonnegative residue of a symmetric representative `j` mod `g` (`-g < 2j ≤ g`, i.e.
`j ∈ F g`) is `j` when `j ≥ 0` and `j + g` when `j < 0`. -/
theorem res_eq_of_symm_repr {g : ℕ} {j : ℤ} (h1 : -(g : ℤ) < 2 * j) (h2 : 2 * j ≤ (g : ℤ))
    (hg : 0 < g) :
    ((res j g : ℤ) = j ∧ 0 ≤ j) ∨ ((res j g : ℤ) = j + (g : ℤ) ∧ j < 0) := by
  unfold res
  rcases le_or_gt 0 j with hj | hj
  · exact Or.inl ⟨by rw [Int.emod_eq_of_lt hj (by omega), Int.toNat_of_nonneg hj], hj⟩
  · refine Or.inr ⟨?_, hj⟩
    have hb : 0 ≤ j + (g : ℤ) := by omega
    rw [← Int.add_emod_right j (g : ℤ), Int.emod_eq_of_lt hb (by omega),
      Int.toNat_of_nonneg hb]

/-- The axis harmonic sum `∑_{(0,ℓ) ∈ A_d(p,q)} 1/(2|ℓ|)` is at most `g(1 + log g)/d`, where
`g = gcd(q,d)` and `d = g m`. -/
theorem sum_inv_abs_le {d p q g m : ℕ} (hg : Nat.gcd q d = g) (hdm : d = g * m)
    (hg0 : 0 < g) (hm0 : 0 < m) :
    ∑ kl ∈ A d p q, 1 / (2 * |(kl.2 : ℝ)|) ≤ (g : ℝ) * (1 + Real.log g) / (d : ℝ) := by
  have hmZ : (0 : ℤ) < (m : ℤ) := by exact_mod_cast hm0
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm0
  have hgR : (0 : ℝ) < (g : ℝ) := by exact_mod_cast hg0
  have hdmZ : (d : ℤ) = (g : ℤ) * (m : ℤ) := by exact_mod_cast hdm
  have hdmR : (d : ℝ) = (g : ℝ) * (m : ℝ) := by exact_mod_cast hdm
  have hshape : ∀ kl ∈ A d p q,
      kl.2 = (m : ℤ) * (kl.2 / (m : ℤ)) ∧ kl.2 / (m : ℤ) ≠ 0 ∧
        -(g : ℤ) < 2 * (kl.2 / (m : ℤ)) ∧ 2 * (kl.2 / (m : ℤ)) ≤ (g : ℤ) := by
    intro kl hkl
    obtain ⟨hbox, hk1, hk2⟩ := mem_A.mp hkl
    obtain ⟨⟨-, hF⟩, hlat⟩ := mem_latticeBox.mp hbox
    obtain ⟨hF1, hF2⟩ := mem_F.mp hF
    have hdvdq : (d : ℤ) ∣ kl.2 * (q : ℤ) := by
      simpa [hk1] using mem_dualLattice.mp hlat
    have hmd : (m : ℤ) ∣ kl.2 := by
      obtain ⟨q', hq'⟩ : g ∣ q := hg ▸ Nat.gcd_dvd_left q d
      have hcop : Nat.Coprime m q' := by
        have hc := Nat.coprime_div_gcd_div_gcd (m := q) (n := d) (hg ▸ hg0)
        rw [hg, hq', Nat.mul_div_cancel_left _ hg0, hdm,
          Nat.mul_div_cancel_left _ hg0] at hc
        exact hc.symm
      have hnat : g * m ∣ g * (kl.2.natAbs * q') := by
        have hh := Int.natAbs_dvd_natAbs.mpr hdvdq
        rw [Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_natCast, hq'] at hh
        rwa [← hdm, show g * (kl.2.natAbs * q') = kl.2.natAbs * (g * q') from by ring]
      rw [← Int.natAbs_dvd_natAbs, Int.natAbs_natCast]
      exact hcop.dvd_of_dvd_mul_right ((mul_dvd_mul_iff_left hg0.ne').mp hnat)
    have heq : kl.2 = (m : ℤ) * (kl.2 / (m : ℤ)) := (Int.mul_ediv_cancel' hmd).symm
    rw [heq, hdmZ] at hF1 hF2
    refine ⟨heq, fun h0 => hk2 (by rw [heq, h0, mul_zero]), ?_, ?_⟩
    · exact lt_of_mul_lt_mul_right (by linarith) hmZ.le
    · exact le_of_mul_le_mul_right (by linarith) hmZ
  have hmem : ∀ kl ∈ A d p q, res (kl.2 / (m : ℤ)) g ∈ Finset.Icc 1 (g - 1) := by
    intro kl hkl
    obtain ⟨-, h0, h1, h2⟩ := hshape kl hkl
    rw [Finset.mem_Icc]
    rcases res_eq_of_symm_repr h1 h2 hg0 with ⟨e, s⟩ | ⟨e, s⟩ <;> omega
  have hinj : ∀ a ∈ A d p q, ∀ b ∈ A d p q,
      res (a.2 / (m : ℤ)) g = res (b.2 / (m : ℤ)) g → a = b := by
    intro a ha b hb hab
    obtain ⟨hae, ha0, ha1, ha2⟩ := hshape a ha
    obtain ⟨hbe, hb0, hb1, hb2⟩ := hshape b hb
    have hj : a.2 / (m : ℤ) = b.2 / (m : ℤ) := by
      rcases res_eq_of_symm_repr ha1 ha2 hg0 with ⟨ea, sa⟩ | ⟨ea, sa⟩ <;>
        rcases res_eq_of_symm_repr hb1 hb2 hg0 with ⟨eb, sb⟩ | ⟨eb, sb⟩ <;> omega
    exact Prod.ext (((mem_A.mp ha).2.1).trans ((mem_A.mp hb).2.1).symm)
      (by rw [hae, hj, ← hbe])
  have hpoint : ∀ kl ∈ A d p q,
      (m : ℝ) * (1 / (2 * |(kl.2 : ℝ)|)) = w g (res (kl.2 / (m : ℤ)) g) := by
    intro kl hkl
    obtain ⟨he, h0, h1, h2⟩ := hshape kl hkl
    have hmin : min (res (kl.2 / (m : ℤ)) g) (g - res (kl.2 / (m : ℤ)) g)
        = (kl.2 / (m : ℤ)).natAbs := by
      rcases res_eq_of_symm_repr h1 h2 hg0 with ⟨e, s⟩ | ⟨e, s⟩ <;> omega
    have hnat : (0 : ℝ) < ((kl.2 / (m : ℤ)).natAbs : ℝ) := by
      exact_mod_cast Int.natAbs_pos.mpr h0
    have habs : |(kl.2 : ℝ)| = (m : ℝ) * (((kl.2 / (m : ℤ)).natAbs : ℕ) : ℝ) := by
      rw [show (kl.2 : ℝ) = (m : ℝ) * ((kl.2 / (m : ℤ) : ℤ) : ℝ) from by exact_mod_cast he,
        abs_mul, abs_of_pos hmR, Nat.cast_natAbs, Int.cast_abs]
    unfold w
    rw [hmin, habs]
    field_simp
  have hws : ∑ k ∈ Finset.Icc 1 (g - 1), w g k ≤ 1 + Real.log g := by
    rcases Nat.lt_or_ge g 2 with hlt | hge
    · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
      linarith [Real.log_natCast_nonneg g]
    · exact sum_w_le_one_add_log hge
  have hmain : (m : ℝ) * ∑ kl ∈ A d p q, 1 / (2 * |(kl.2 : ℝ)|) ≤ 1 + Real.log g :=
    calc (m : ℝ) * ∑ kl ∈ A d p q, 1 / (2 * |(kl.2 : ℝ)|)
        = ∑ kl ∈ A d p q, w g (res (kl.2 / (m : ℤ)) g) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl hpoint
      _ = ∑ k ∈ (A d p q).image fun kl => res (kl.2 / (m : ℤ)) g, w g k :=
          (Finset.sum_image hinj).symm
      _ ≤ ∑ k ∈ Finset.Icc 1 (g - 1), w g k :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (fun k hk => by
              obtain ⟨kl, hkl, rfl⟩ := Finset.mem_image.mp hk
              exact hmem kl hkl)
            fun k _ _ => w_nonneg g k
      _ ≤ 1 + Real.log g := hws
  calc ∑ kl ∈ A d p q, 1 / (2 * |(kl.2 : ℝ)|)
      ≤ (1 + Real.log g) / (m : ℝ) := (le_div_iff₀ hmR).mpr (by linarith)
    _ = (g : ℝ) * (1 + Real.log g) / (d : ℝ) := by
        rw [hdmR, mul_div_mul_left _ _ hgR.ne']

/-- If the first axis family of the majorant contributes at least
`(1 + log n) M_n(p,q) / (20 Q(n))`, then `(p,q)` is degenerate for `n`. -/
theorem degenerate_of_axis_sum {n d : ℕ} (hn : 5 ≤ n) {pq : ℕ × ℕ} (hpq : pq ∈ H n)
    (hd : d ∈ D n)
    (hsum : (1 + Real.log n) * M n pq.1 pq.2 / (20 * Q n)
      ≤ (1 / (d : ℝ)) * ∑ kl ∈ A d pq.1 pq.2,
          nu d (Hd n d pq.1) kl.1 * nu d (Hd n d pq.2) kl.2) :
    Degenerate n pq.1 pq.2 := by
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
  have hdn : d ∣ n := dvd_of_mem_D hd
  have hd0 : 0 < d := Nat.pos_of_mem_divisors (mem_D.mp hd).1
  have hgd : Nat.gcd pq.2 d ∣ d := Nat.gcd_dvd_right pq.2 d
  have hg0 : 0 < Nat.gcd pq.2 d := Nat.gcd_pos_of_pos_right pq.2 hd0
  have hm0 : 0 < d / Nat.gcd pq.2 d := Nat.div_pos (Nat.le_of_dvd hd0 hgd) hg0
  have hdm : d = Nat.gcd pq.2 d * (d / Nat.gcd pq.2 d) := (Nat.mul_div_cancel' hgd).symm
  have hgR : (0 : ℝ) < (Nat.gcd pq.2 d : ℝ) := by exact_mod_cast hg0
  have hlogpos : (0 : ℝ) < 1 + Real.log n := by linarith [Real.log_natCast_nonneg n]
  have hterm : ∀ kl ∈ A d pq.1 pq.2,
      nu d (Hd n d pq.1) kl.1 * nu d (Hd n d pq.2) kl.2
        = (Hd n d pq.1 : ℝ) * ((d : ℝ) * (1 / (2 * |(kl.2 : ℝ)|))) := by
    intro kl hkl
    obtain ⟨-, h1, h2⟩ := mem_A.mp hkl
    rw [h1, nu_zero, nu_of_ne_zero h2]
    ring
  have hHd : (Hd n d pq.1 : ℝ) ≤ (h pq.1 : ℝ) * (d : ℝ) / (n : ℝ) := by
    rw [Hd, show (h pq.1 : ℝ) * (d : ℝ) = ((h pq.1 * d : ℕ) : ℝ) from by push_cast; ring]
    exact Nat.cast_div_le
  have hhp : (h pq.1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (h_lt (H_subset_T n hpq)).le
  have hgn : Real.log (Nat.gcd pq.2 d) ≤ Real.log n :=
    Real.log_le_log hgR (by exact_mod_cast Nat.le_of_dvd hn0 (hgd.trans hdn))
  have hbound : (1 / (d : ℝ)) * ∑ kl ∈ A d pq.1 pq.2,
      nu d (Hd n d pq.1) kl.1 * nu d (Hd n d pq.2) kl.2
        ≤ (Nat.gcd pq.2 d : ℝ) * (1 + Real.log n) :=
    calc (1 / (d : ℝ)) * ∑ kl ∈ A d pq.1 pq.2,
          nu d (Hd n d pq.1) kl.1 * nu d (Hd n d pq.2) kl.2
        = (Hd n d pq.1 : ℝ) * ∑ kl ∈ A d pq.1 pq.2, 1 / (2 * |(kl.2 : ℝ)|) := by
          rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← Finset.mul_sum]
          field_simp
      _ ≤ (Hd n d pq.1 : ℝ)
            * ((Nat.gcd pq.2 d : ℝ) * (1 + Real.log (Nat.gcd pq.2 d)) / (d : ℝ)) :=
          mul_le_mul_of_nonneg_left (sum_inv_abs_le rfl hdm hg0 hm0) (by positivity)
      _ ≤ ((h pq.1 : ℝ) * (d : ℝ) / (n : ℝ))
            * ((Nat.gcd pq.2 d : ℝ) * (1 + Real.log (Nat.gcd pq.2 d)) / (d : ℝ)) :=
          mul_le_mul_of_nonneg_right hHd (by positivity)
      _ = ((h pq.1 : ℝ) / (n : ℝ))
            * ((Nat.gcd pq.2 d : ℝ) * (1 + Real.log (Nat.gcd pq.2 d))) := by
          field_simp
      _ ≤ 1 * ((Nat.gcd pq.2 d : ℝ) * (1 + Real.log n)) :=
          mul_le_mul ((div_le_one hnR).mpr hhp)
            (mul_le_mul_of_nonneg_left (by linarith) hgR.le) (by positivity) zero_le_one
      _ = (Nat.gcd pq.2 d : ℝ) * (1 + Real.log n) := one_mul _
  have h20Q : (0 : ℝ) < 20 * Q n := by linarith [Q_pos n]
  have hchain := hsum.trans hbound
  rw [div_le_iff₀ h20Q] at hchain
  have hM : M n pq.1 pq.2 ≤ (Nat.gcd pq.2 d : ℝ) * (20 * Q n) :=
    le_of_mul_le_mul_left (by linarith) hlogpos
  have hmax : (Nat.gcd pq.2 d : ℝ)
      ≤ (max (Nat.gcd pq.1 n) (Nat.gcd pq.2 n) : ℝ) := by
    have hle : Nat.gcd pq.2 d ≤ Nat.gcd pq.2 n :=
      Nat.le_of_dvd (Nat.gcd_pos_of_pos_right pq.2 hn0)
        (Nat.dvd_gcd (Nat.gcd_dvd_left pq.2 d) (hgd.trans hdn))
    exact le_trans (by exact_mod_cast hle) (le_max_right _ _)
  rw [degenerate_iff]
  nlinarith [hM, hmax, hgR.le, Q_pos n]

theorem mem_H_fifteen : ((2, 5) : ℕ × ℕ) ∈ H 15 := by decide

theorem mem_D_fifteen : 5 ∈ D 15 := by
  rw [mem_D, show (15 : ℕ) / 5 = 3 from by norm_num]
  exact ⟨Nat.mem_divisors.mpr ⟨by norm_num, by norm_num⟩, Nat.prime_three.squarefree⟩

end Paucity
