/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Set.Card
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring
public import Paucity.Lattice.FamilyCover
public import Paucity.Defs.E
public import Paucity.Defs.Degenerate
public import Paucity.Defs.Resonant
public import Paucity.Defs.Wd
public import Paucity.Majorant.EBound
public import Paucity.Lattice.BdSwap
public import Paucity.Estimates.QLower
public import Paucity.Lattice.AxisBound
public import Paucity.Majorant.DetLambda
public import Paucity.Lattice.LatticeAlt
public import Paucity.Lattice.FamilyCount
public import Paucity.Lattice.OneVanishing
public import Paucity.Defs.Hn
public import Paucity.Defs.Lambda
public import Paucity.Defs.LambdaKL
public import Paucity.Defs.M
public import Paucity.Defs.Q

/-!
# Large discrepancy forces resonance or degeneracy

For `n ≥ 5` and `(p,q) ∈ H(n)` with `M_n(p,q) ≥ 1000 Q(n)` and `|E_n(p,q)| ≥ M_n(p,q)/2`, the pair
`(p,q)` is resonant or degenerate.

## Main definitions

* `contrib`: the `ν`-weighted contribution of the family labelled by a pair `(d, X)`, normalized by
  `1/d`.

## Main results

* `sum_W_le_sum_contrib`: the majorant total `∑_{d ∈ D(n)} W_d(n,p,q)` is at most the sum of the
  contributions of the labelled families.
* `exists_family_contrib_ge`: some labelled family contributes at least
  `(1 + log n) M_n(p,q) / (20 Q(n))`.
* `resonant_or_degenerate_of_dyadic`: a dyadic class carrying a contribution of at least
  `M_n(p,q) / (20 Q(n))` forces `(p,q)` to be resonant or degenerate.
* `resonant_or_degenerate`: a pair with `M_n(p,q) ≥ 1000 Q(n)` and `|E_n(p,q)| ≥ M_n(p,q)/2` is
  resonant or degenerate.
-/

@[expose] public section

namespace Paucity

open Finset

/-- A symmetric representative has least absolute value in its residue class. -/
theorem abs_le_abs_of_mem_F {d : ℕ} {a a' : ℤ} (ha' : a' ∈ F d) (hdvd : (d : ℤ) ∣ a - a') :
    |a'| ≤ |a| := by
  rcases eq_or_ne a a' with rfl | hne
  · exact le_rfl
  · have hd : (d : ℤ) ≤ |a - a'| :=
      Int.le_of_dvd (abs_pos.mpr (sub_ne_zero.mpr hne)) ((dvd_abs _ _).mpr hdvd)
    linarith [two_mul_abs_le_of_mem_F ha', abs_sub a a']

/-- Every integer has a symmetric representative mod `d` of no larger absolute value. -/
theorem exists_mem_F_abs_le {d : ℕ} (hd : 0 < d) (a : ℤ) :
    ∃ a' ∈ F d, (d : ℤ) ∣ a - a' ∧ |a'| ≤ |a| := by
  have hd0 : (0 : ℤ) < (d : ℤ) := by exact_mod_cast hd
  have hr0 : 0 ≤ a % (d : ℤ) := Int.emod_nonneg a hd0.ne'
  have hrd : a % (d : ℤ) < (d : ℤ) := Int.emod_lt_of_pos a hd0
  have hq : a % (d : ℤ) = a - (d : ℤ) * (a / (d : ℤ)) := by rw [Int.emod_def]
  obtain ⟨a', hmem, hdvd⟩ : ∃ a' ∈ F d, (d : ℤ) ∣ a - a' := by
    rcases le_or_gt (2 * (a % (d : ℤ))) (d : ℤ) with hle | hgt
    · exact ⟨a % (d : ℤ), mem_F.mpr ⟨by omega, hle⟩, a / (d : ℤ), by linear_combination -hq⟩
    · exact ⟨a % (d : ℤ) - (d : ℤ), mem_F.mpr ⟨by omega, by omega⟩,
        a / (d : ℤ) + 1, by linear_combination -hq⟩
  exact ⟨a', hmem, hdvd, abs_le_abs_of_mem_F hmem hdvd⟩

/-- The contribution of one labelled family. -/
noncomputable def contrib (n p q : ℕ) (x : ℕ × (Bool ⊕ ℕ × ℕ)) : ℝ :=
  (1 / (x.1 : ℝ)) * ∑ kl ∈ familyOf p q x.1 x.2,
    nu x.1 (Hd n x.1 p) kl.1 * nu x.1 (Hd n x.1 q) kl.2

/-- Reorganisation of the majorant total as a sum over the labelled families. -/
theorem sum_W_le_sum_contrib (n p q : ℕ) :
    ∑ d ∈ D n, W n d p q ≤ ∑ x ∈ familyIndex n, contrib n p q x := by
  have hcov : ∀ d, d ∈ D n → ∀ kl : ℤ × ℤ,
      kl ∈ (latticeBox d p q).filter (fun kl => kl ≠ (0, 0)) →
      ∃ X, (d, X) ∈ familyIndex n ∧ kl ∈ familyOf p q d X := by
    intro d hd kl hkl
    rw [Finset.mem_filter] at hkl
    rcases exists_family_mem hkl.1 hkl.2 with hA | hB | ⟨K, L, hK2, hL2, hKd, hLd, hmem⟩
    · exact ⟨Sum.inl false, mem_familyIndex.mpr ⟨hd, Or.inl rfl⟩, hA⟩
    · exact ⟨Sum.inl true, mem_familyIndex.mpr ⟨hd, Or.inr (Or.inl rfl)⟩, hB⟩
    · exact ⟨Sum.inr (K, L), mem_familyIndex.mpr ⟨hd, Or.inr (Or.inr
        ⟨K, L, mem_scales.mpr ⟨hK2, hKd⟩, mem_scales.mpr ⟨hL2, hLd⟩, rfl⟩)⟩, hmem⟩
  choose! label hlab1 hlab2 using hcov
  have hfib : ∑ d ∈ D n, ∑ x ∈ (familyIndex n).filter (fun x => x.1 = d), contrib n p q x
      = ∑ x ∈ familyIndex n, contrib n p q x :=
    Finset.sum_fiberwise_of_maps_to (fun x hx => (mem_familyIndex.mp hx).1) _
  rw [← hfib]
  refine Finset.sum_le_sum fun d hd => ?_
  have hmaps : ∀ kl ∈ (latticeBox d p q).filter (fun kl => kl ≠ (0, 0)),
      (d, label d kl) ∈ (familyIndex n).filter (fun x => x.1 = d) :=
    fun kl hkl => Finset.mem_filter.mpr ⟨hlab1 d hd kl hkl, rfl⟩
  have hinner := Finset.sum_fiberwise_of_maps_to hmaps
    (fun kl : ℤ × ℤ => nu d (Hd n d p) kl.1 * nu d (Hd n d q) kl.2)
  have hstep : ∀ x ∈ (familyIndex n).filter (fun x => x.1 = d),
      ∑ kl ∈ ((latticeBox d p q).filter (fun kl => kl ≠ (0, 0))).filter
          (fun kl => (d, label d kl) = x),
        nu d (Hd n d p) kl.1 * nu d (Hd n d q) kl.2
      ≤ ∑ kl ∈ familyOf p q x.1 x.2,
          nu x.1 (Hd n x.1 p) kl.1 * nu x.1 (Hd n x.1 q) kl.2 := by
    intro x hx
    obtain ⟨d', X⟩ := x
    obtain ⟨-, rfl⟩ := Finset.mem_filter.mp hx
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_
      (fun kl _ _ => mul_nonneg (nu_nonneg _ _ _) (nu_nonneg _ _ _))
    intro kl hkl
    obtain ⟨hkl1, hkl2⟩ := Finset.mem_filter.mp hkl
    obtain rfl : label d' kl = X := congrArg Prod.snd hkl2
    exact hlab2 d' hd kl hkl1
  unfold W
  calc (1 / (d : ℝ)) * ∑ kl ∈ (latticeBox d p q).filter (fun kl => kl ≠ (0, 0)),
        nu d (Hd n d p) kl.1 * nu d (Hd n d q) kl.2
      = (1 / (d : ℝ)) * ∑ x ∈ (familyIndex n).filter (fun x => x.1 = d),
          ∑ kl ∈ ((latticeBox d p q).filter (fun kl => kl ≠ (0, 0))).filter
              (fun kl => (d, label d kl) = x),
            nu d (Hd n d p) kl.1 * nu d (Hd n d q) kl.2 := by rw [hinner]
    _ ≤ (1 / (d : ℝ)) * ∑ x ∈ (familyIndex n).filter (fun x => x.1 = d),
          ∑ kl ∈ familyOf p q x.1 x.2,
            nu x.1 (Hd n x.1 p) kl.1 * nu x.1 (Hd n x.1 q) kl.2 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hstep) (by positivity)
    _ = ∑ x ∈ (familyIndex n).filter (fun x => x.1 = d), contrib n p q x := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x hx => ?_
        obtain ⟨-, hx1⟩ := Finset.mem_filter.mp hx
        rw [contrib, hx1]

/-- The majorant weight at a point of absolute value at least `K` is at most `d/(2K)`. -/
theorem nu_le_div_of_le_abs {d H : ℕ} {K : ℝ} (hK : 0 < K) {k : ℤ}
    (hk : K ≤ |(k : ℝ)|) : nu d H k ≤ (d : ℝ) / (2 * K) := by
  have hk0 : k ≠ 0 := by rintro rfl; simp only [Int.cast_zero, abs_zero] at hk; linarith
  rw [nu_of_ne_zero hk0]
  exact div_le_div_of_nonneg_left (Nat.cast_nonneg d) (by linarith) (by linarith)

/-- On a dyadic class both weights are bounded by the class scales, so the family's contribution is
at most `d·J/(4KL)` with `J` the class cardinality. -/
theorem contrib_inr_le {n p q d K L : ℕ} (hd : 0 < d) (hK : 1 ≤ K) (hL : 1 ≤ L) :
    contrib n p q (d, Sum.inr (K, L))
      ≤ (d : ℝ) * ((dyadicBox d (K : ℝ) (L : ℝ) p q).card : ℝ) / (4 * (K : ℝ) * (L : ℝ)) := by
  have hK0 : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hL0 : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hsum := Finset.sum_le_card_nsmul (dyadicBox d (K : ℝ) (L : ℝ) p q)
    (fun kl => nu d (Hd n d p) kl.1 * nu d (Hd n d q) kl.2)
    ((d : ℝ) / (2 * (K : ℝ)) * ((d : ℝ) / (2 * (L : ℝ)))) fun kl hkl => by
      rw [mem_dyadicBox] at hkl
      exact mul_le_mul (nu_le_div_of_le_abs hK0 hkl.2.1)
        (nu_le_div_of_le_abs hL0 hkl.2.2.2.1) (nu_nonneg _ _ _) (by positivity)
  rw [nsmul_eq_mul] at hsum
  change (1 / (d : ℝ)) * ∑ kl ∈ dyadicBox d (K : ℝ) (L : ℝ) p q,
      nu d (Hd n d p) kl.1 * nu d (Hd n d q) kl.2 ≤ _
  refine (mul_le_mul_of_nonneg_left hsum (by positivity)).trans_eq ?_
  field_simp
  ring

/-- A dyadic class sits inside the nonzero points of the dual lattice in the box `|x| ≤ 2K`,
`|y| ≤ 2L`. -/
theorem card_dyadicBox_le_ncard {d p q K L : ℕ} (hK : 1 ≤ K) (hL : 1 ≤ L) :
    ((dyadicBox d (K : ℝ) (L : ℝ) p q).card : ℕ)
      ≤ {v : ℤ × ℤ | v ∈ dualLattice d p q ∧ v ≠ 0 ∧
          |(v.1 : ℝ)| ≤ 2 * (K : ℝ) ∧ |(v.2 : ℝ)| ≤ 2 * (L : ℝ)}.ncard := by
  have hK1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have _hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  rw [← Set.ncard_coe_finset]
  refine Set.ncard_le_ncard (fun kl hkl => ?_) (finite_setOf_mem_abs_le _ _ _)
  rw [Finset.mem_coe] at hkl
  have hkl' := mem_dyadicBox.mp hkl
  exact ⟨(mem_latticeBox.mp hkl'.1).2, fun h => fst_ne_zero hK1 hkl (congrArg Prod.fst h),
    hkl'.2.2.1.le, hkl'.2.2.2.2.le⟩

/-- Unfolding of `contrib` at the first axis label. -/
theorem contrib_inl_false (n p q d : ℕ) :
    contrib n p q (d, Sum.inl false)
      = (1 / (d : ℝ)) * ∑ kl ∈ A d p q, nu d (Hd n d p) kl.1 * nu d (Hd n d q) kl.2 := rfl

/-- Unfolding of `contrib` at the second axis label. -/
theorem contrib_inl_true (n p q d : ℕ) :
    contrib n p q (d, Sum.inl true)
      = (1 / (d : ℝ)) * ∑ kl ∈ B d p q, nu d (Hd n d p) kl.1 * nu d (Hd n d q) kl.2 := rfl

/-- The class-size inequality `M·4KL ≤ dJ·20Q`, together with any upper bound `dJ ≤ c·KL` on the
class, forces `M ≤ 5c·Q`. -/
theorem le_of_class_bound {MM QQ KK LL dJ c : ℝ} (hK : 0 < KK) (hL : 0 < LL) (hQ : 0 < QQ)
    (hkey : MM * (4 * KK * LL) ≤ dJ * (20 * QQ)) (hdJ : dJ ≤ c * (KK * LL)) :
    MM ≤ 5 * c * QQ := by
  have hKL : (0 : ℝ) < KK * LL := mul_pos hK hL
  have h : MM * (4 * (KK * LL)) ≤ 5 * c * QQ * (4 * (KK * LL)) := by
    linarith [mul_le_mul_of_nonneg_right hdJ (by linarith : (0 : ℝ) ≤ 20 * QQ)]
  exact le_of_mul_le_mul_right h (by linarith)

/-- A short dual vector whose two coordinates both survive reduction satisfies
`|k₀'ℓ₀'|·M ≤ 1000·d·Q`. -/
theorem resonance_bound {MM QQ KK LL dd JJ a b : ℝ} (hM : 0 < MM) (hQ : 0 < QQ)
    (hK : 0 < KK) (hd : 0 < dd) (hJ : 1 ≤ JJ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (haJ : a * JJ ≤ 8 * KK) (hbJ : b * JJ ≤ 8 * LL)
    (hkey : MM * (4 * KK * LL) ≤ dd * JJ * (20 * QQ)) :
    a * b * MM ≤ 1000 * dd * QQ := by
  have hJ0 : (0 : ℝ) < JJ := by linarith
  have hprod : a * b * (JJ * JJ) ≤ 64 * (KK * LL) := by
    linarith [mul_le_mul haJ hbJ (mul_nonneg hb hJ0.le) (by linarith : (0 : ℝ) ≤ 8 * KK)]
  have hcancel : MM * (a * b) * JJ * JJ ≤ 320 * dd * QQ * JJ := by
    linarith [mul_le_mul_of_nonneg_left hprod hM.le]
  linarith [le_of_mul_le_mul_right hcancel hJ0, mul_pos hd hQ,
    mul_nonneg (mul_nonneg hM.le (mul_nonneg ha hb)) (by linarith : (0 : ℝ) ≤ JJ - 1)]

/-- Some labelled family contributes at least `(1 + log n) M_n(p,q) / (20 Q(n))`. -/
theorem exists_family_contrib_ge {n : ℕ} (hn : 5 ≤ n) {p q : ℕ} (hpq : (p, q) ∈ H n)
    (hM : 1000 * Q n ≤ M n p q) (hE : M n p q / 2 ≤ |E n p q|) :
    ∃ x ∈ familyIndex n, (1 + Real.log n) * M n p q / (20 * Q n) ≤ contrib n p q x := by
  have hQ : 0 < Q n := Q_pos n
  have hM0 : 0 < M n p q := by linarith
  have hLg : (1 : ℝ) ≤ 1 + Real.log n := by linarith [Real.log_natCast_nonneg n]
  have homega : (2 : ℝ) ^ (n.primeFactors.card + 1) ≤ M n p q / 4 := by
    have h1 : (2 : ℝ) ^ n.primeFactors.card ≤ Q n := by
      unfold Q
      exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ hLg)
    rw [pow_succ]
    linarith
  have hW : M n p q / 4 ≤ ∑ d ∈ D n, W n d p q := by linarith [abs_E_le hn hpq]
  have hcontribsum := hW.trans (sum_W_le_sum_contrib n p q)
  by_contra hno
  push Not at hno
  have hcard : ((familyIndex n).card : ℝ) ≤ 5 * Q n / (1 + Real.log n) ^ 2 :=
    card_familyIndex_le (by omega)
  rcases Finset.eq_empty_or_nonempty (familyIndex n) with hempty | hne
  · rw [hempty, Finset.sum_empty] at hcontribsum; linarith
  have hlt : ∑ x ∈ familyIndex n, contrib n p q x
      < ∑ _x ∈ familyIndex n, (1 + Real.log n) * M n p q / (20 * Q n) :=
    Finset.sum_lt_sum_of_nonempty hne hno
  rw [Finset.sum_const, nsmul_eq_mul] at hlt
  have hc0 : 0 < (1 + Real.log n) * M n p q / (20 * Q n) :=
    div_pos (mul_pos (by linarith) hM0) (by linarith)
  have hb := mul_le_mul_of_nonneg_right hcard hc0.le
  have heq : (5 * Q n / (1 + Real.log n) ^ 2) * ((1 + Real.log n) * M n p q / (20 * Q n))
      = M n p q / (4 * (1 + Real.log n)) := by
    field_simp; ring
  rw [heq] at hb
  have hlast : M n p q / (4 * (1 + Real.log n)) ≤ M n p q / 4 :=
    div_le_div_of_nonneg_left hM0.le (by norm_num) (by linarith)
  linarith

/-- A bound `M_n(p,q) ≤ 120 g Q(n)` with `0 ≤ g ≤ max (gcd p n) (gcd q n)` makes `(p,q)` degenerate
for `n`. -/
theorem degenerate_of_gcd_bound {n p q : ℕ} {g : ℝ} (hQ : 0 < Q n) (hg0 : 0 ≤ g)
    (hbound : M n p q ≤ 5 * (24 * g) * Q n)
    (hg : g ≤ (max (Nat.gcd p n) (Nat.gcd q n) : ℝ)) :
    Degenerate n p q := by
  rw [degenerate_iff]
  linarith [mul_nonneg (sub_nonneg.mpr hg) hQ.le, mul_nonneg (hg0.trans hg) hQ.le]

/-- If a dyadic class at admissible scales `K, L` carries a contribution of at least
`M_n(p,q) / (20 Q(n))`, then `(p,q)` is resonant or degenerate. -/
theorem resonant_or_degenerate_of_dyadic {n p q : ℕ} (hpq : (p, q) ∈ H n)
    (hM : 1000 * Q n ≤ M n p q) {d K L : ℕ} (hd : d ∈ D n)
    (hK : K ∈ scales d) (hL : L ∈ scales d)
    (hxc : M n p q / (20 * Q n) ≤ contrib n p q (d, Sum.inr (K, L))) :
    Resonant n p q ∨ Degenerate n p q := by
  have hQ : 0 < Q n := Q_pos n
  have hM0 : 0 < M n p q := by linarith
  have hddiv := Nat.mem_divisors.mp (D_subset_divisors n hd)
  have hd0 : 0 < d := Nat.pos_of_mem_divisors (D_subset_divisors n hd)
  have hn0 : 0 < n := Nat.pos_of_ne_zero hddiv.2
  have hdn : d ∣ n := hddiv.1
  have hdr : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
  have hK1 : 1 ≤ K := by obtain ⟨_, rfl⟩ := (mem_scales.mp hK).1; exact Nat.one_le_two_pow
  have hL1 : 1 ≤ L := by obtain ⟨_, rfl⟩ := (mem_scales.mp hL).1; exact Nat.one_le_two_pow
  have hKr1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK1
  have hLr1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL1
  have hK0 : (0 : ℝ) < (K : ℝ) := by linarith
  have hL0 : (0 : ℝ) < (L : ℝ) := by linarith
  obtain ⟨J, hJdef⟩ : ∃ J, (dyadicBox d (K : ℝ) (L : ℝ) p q).card = J := ⟨_, rfl⟩
  have hub := contrib_inr_le (n := n) (p := p) (q := q) hd0 hK1 hL1
  rw [hJdef] at hub
  have hJ1 : 1 ≤ J := by
    rcases Nat.eq_zero_or_pos J with hJ0 | hJpos
    · have hc0 : contrib n p q (d, Sum.inr (K, L)) = 0 := by
        change (1 / (d : ℝ)) * ∑ kl ∈ dyadicBox d (K : ℝ) (L : ℝ) p q,
          nu d (Hd n d p) kl.1 * nu d (Hd n d q) kl.2 = 0
        rw [Finset.card_eq_zero.mp (hJdef.trans hJ0), Finset.sum_empty, mul_zero]
      rw [hc0] at hxc
      exact absurd hxc (not_le.mpr (div_pos hM0 (by linarith)))
    · exact hJpos
  have hJr0 : (0 : ℝ) < (J : ℝ) := by exact_mod_cast hJ1
  have hJ1r : (1 : ℝ) ≤ (J : ℝ) := by exact_mod_cast hJ1
  have hkey : M n p q / (20 * Q n) ≤ (d : ℝ) * (J : ℝ) / (4 * (K : ℝ) * (L : ℝ)) :=
    hxc.trans hub
  rw [div_le_div_iff₀ (by linarith) (by positivity)] at hkey
  have hncard : J ≤ {v : ℤ × ℤ | v ∈ dualLattice d p q ∧ v ≠ 0 ∧
      |(v.1 : ℝ)| ≤ 2 * (K : ℝ) ∧ |(v.2 : ℝ)| ≤ 2 * (L : ℝ)}.ncard := by
    rw [← hJdef]; exact card_dyadicBox_le_ncard hK1 hL1
  have hindex : (dualLattice d p q).index = d := index_dualLattice hd0 hdn hpq
  rcases lt_or_exists_short_vector (A := 2 * (K : ℝ)) (B := 2 * (L : ℝ))
      (by linarith) (by linarith) hindex (by omega) hJ1 hncard with hsmall | hshort
  · exfalso
    have hdJ : (d : ℝ) * (J : ℝ) ≤ 96 * ((K : ℝ) * (L : ℝ)) := by
      linarith [(lt_div_iff₀ hdr).mp hsmall]
    linarith [le_of_class_bound hK0 hL0 hQ hkey hdJ]
  · obtain ⟨w, hwmem, hw0, hw1, hw2⟩ := hshort
    have hw1' : |(w.1 : ℝ)| * (J : ℝ) ≤ 8 * (K : ℝ) := by
      have := (le_div_iff₀ hJr0).mp hw1; linarith
    have hw2' : |(w.2 : ℝ)| * (J : ℝ) ≤ 8 * (L : ℝ) := by
      have := (le_div_iff₀ hJr0).mp hw2; linarith
    obtain ⟨k0', hk0'F, hk0'dvd, hk0'abs⟩ := exists_mem_F_abs_le hd0 w.1
    obtain ⟨l0', hl0'F, hl0'dvd, hl0'abs⟩ := exists_mem_F_abs_le hd0 w.2
    have hk0'absR : |(k0' : ℝ)| ≤ |(w.1 : ℝ)| := by exact_mod_cast hk0'abs
    have hl0'absR : |(l0' : ℝ)| ≤ |(w.2 : ℝ)| := by exact_mod_cast hl0'abs
    have hmem' : ((k0', l0') : ℤ × ℤ) ∈ dualLattice d p q := by
      rw [mem_dualLattice]
      obtain ⟨s, hs⟩ := hk0'dvd
      obtain ⟨t, ht⟩ := hl0'dvd
      obtain ⟨u, hu⟩ := mem_dualLattice.mp hwmem
      exact ⟨u - s * (p : ℤ) - t * (q : ℤ), by
        linear_combination hu - (p : ℤ) * hs - (q : ℤ) * ht⟩
    have ha0 : (0 : ℝ) ≤ |(k0' : ℝ)| := abs_nonneg _
    have hb0 : (0 : ℝ) ≤ |(l0' : ℝ)| := abs_nonneg _
    rcases eq_or_ne k0' 0 with hk0e | hk0ne
    · rcases eq_or_ne l0' 0 with hl0e | hl0ne
      · exfalso
        have hdvd1 : (d : ℤ) ∣ w.1 := by simpa [hk0e] using hk0'dvd
        have hdvd2 : (d : ℤ) ∣ w.2 := by simpa [hl0e] using hl0'dvd
        have hdle : ∀ x : ℤ, x ≠ 0 → (d : ℤ) ∣ x → (d : ℝ) ≤ |(x : ℝ)| := fun x hx hdx => by
          exact_mod_cast Int.le_of_dvd (abs_pos.mpr hx) ((dvd_abs _ _).mpr hdx)
        have hdJ : (d : ℝ) * (J : ℝ) ≤ 8 * ((K : ℝ) * (L : ℝ)) := by
          rcases eq_or_ne w.1 0 with h1 | h1
          · have h2 : w.2 ≠ 0 := fun h2 => hw0 (Prod.ext h1 h2)
            linarith [mul_nonneg (sub_nonneg.mpr (hdle _ h2 hdvd2)) hJr0.le,
              mul_nonneg (by linarith : (0 : ℝ) ≤ 8 * (L : ℝ))
                (by linarith : (0 : ℝ) ≤ (K : ℝ) - 1)]
          · linarith [mul_nonneg (sub_nonneg.mpr (hdle _ h1 hdvd1)) hJr0.le,
              mul_nonneg (by linarith : (0 : ℝ) ≤ 8 * (K : ℝ))
                (by linarith : (0 : ℝ) ≤ (L : ℝ) - 1)]
        linarith [le_of_class_bound hK0 hL0 hQ hkey hdJ]
      · right
        have hlJ : |(l0' : ℝ)| ≤ 8 * (L : ℝ) := by
          linarith [mul_nonneg hb0 (by linarith : (0 : ℝ) ≤ (J : ℝ) - 1),
            mul_nonneg (sub_nonneg.mpr hl0'absR) hJr0.le]
        have hswapmem : ((l0', 0) : ℤ × ℤ) ∈ dualLattice d q p := by
          have h := (swap_mem_dualLattice (d := d) (p := p) (q := q)
            (kl := ((k0', l0') : ℤ × ℤ))).mpr hmem'
          simpa [hk0e, Prod.swap] using h
        have hcardq := card_dyadicBox_le_of_axis_point (d := d) (p := q) (q := p)
          hd0 hLr1 hKr1 hl0ne hlJ hswapmem
        rw [← card_dyadicBox_swap d (K : ℝ) (L : ℝ) p q, hJdef] at hcardq
        have hgcd : (Nat.gcd q d : ℝ) ≤ (Nat.gcd q n : ℝ) := by
          exact_mod_cast Nat.le_of_dvd (Nat.gcd_pos_of_pos_right q hn0)
            (Nat.gcd_dvd_gcd_of_dvd_right q hdn)
        have hdJ : (d : ℝ) * (J : ℝ)
            ≤ (24 * (Nat.gcd q d : ℝ)) * ((K : ℝ) * (L : ℝ)) := by
          linarith [(le_div_iff₀ hdr).mp hcardq]
        exact degenerate_of_gcd_bound hQ (Nat.cast_nonneg _)
          (le_of_class_bound hK0 hL0 hQ hkey hdJ) (hgcd.trans (le_max_right _ _))
    · rcases eq_or_ne l0' 0 with hl0e | hl0ne
      · right
        have hkJ : |(k0' : ℝ)| ≤ 8 * (K : ℝ) := by
          linarith [mul_nonneg ha0 (by linarith : (0 : ℝ) ≤ (J : ℝ) - 1),
            mul_nonneg (sub_nonneg.mpr hk0'absR) hJr0.le]
        have hcardp := card_dyadicBox_le_of_axis_point (d := d) (p := p) (q := q)
          hd0 hKr1 hLr1 hk0ne hkJ (by simpa [hl0e] using hmem')
        rw [hJdef] at hcardp
        have hgcd : (Nat.gcd p d : ℝ) ≤ (Nat.gcd p n : ℝ) := by
          exact_mod_cast Nat.le_of_dvd (Nat.gcd_pos_of_pos_right p hn0)
            (Nat.gcd_dvd_gcd_of_dvd_right p hdn)
        have hdJ : (d : ℝ) * (J : ℝ)
            ≤ (24 * (Nat.gcd p d : ℝ)) * ((K : ℝ) * (L : ℝ)) := by
          linarith [(le_div_iff₀ hdr).mp hcardp]
        exact degenerate_of_gcd_bound hQ (Nat.cast_nonneg _)
          (le_of_class_bound hK0 hL0 hQ hkey hdJ) (hgcd.trans (le_max_left _ _))
      · left
        refine resonant_of_mem hd (kl := ((k0', l0') : ℤ × ℤ)) ?_ hk0ne hl0ne ?_
        · rw [mem_latticeBox]; exact ⟨⟨hk0'F, hl0'F⟩, hmem'⟩
        · have haJ : |(k0' : ℝ)| * (J : ℝ) ≤ 8 * (K : ℝ) := by
            linarith [mul_nonneg (sub_nonneg.mpr hk0'absR) hJr0.le]
          have hbJ : |(l0' : ℝ)| * (J : ℝ) ≤ 8 * (L : ℝ) := by
            linarith [mul_nonneg (sub_nonneg.mpr hl0'absR) hJr0.le]
          change |((k0' * l0' : ℤ) : ℝ)| * M n p q ≤ 1000 * (d : ℝ) * Q n
          rw [Int.cast_mul, abs_mul]
          exact resonance_bound hM0 hQ hK0 hdr hJ1r ha0 hb0 haJ hbJ hkey

/-- For `n ≥ 5` and `(p,q) ∈ H n` with `M_n(p,q) ≥ 1000 Q(n)` and `|E_n(p,q)| ≥ M_n(p,q)/2`, the
pair `(p,q)` is resonant or degenerate. -/
theorem resonant_or_degenerate {n : ℕ} (hn : 5 ≤ n) {p q : ℕ} (hpq : (p, q) ∈ H n)
    (hM : 1000 * Q n ≤ M n p q) (hE : M n p q / 2 ≤ |E n p q|) :
    Resonant n p q ∨ Degenerate n p q := by
  have hQ : 0 < Q n := Q_pos n
  have hM0 : 0 < M n p q := by linarith
  have hLg : (1 : ℝ) ≤ 1 + Real.log n := by linarith [Real.log_natCast_nonneg n]
  obtain ⟨x, hx, hxc⟩ := exists_family_contrib_ge hn hpq hM hE
  obtain ⟨d, X⟩ := x
  obtain ⟨hd, hX⟩ := mem_familyIndex.mp hx
  have hxc' : M n p q / (20 * Q n) ≤ contrib n p q (d, X) := by
    refine le_trans ?_ hxc
    rw [mul_div_assoc]
    exact le_mul_of_one_le_left (div_nonneg hM0.le (by linarith)) hLg
  rcases hX with rfl | rfl | ⟨K, L, hK, hL, rfl⟩
  · rw [contrib_inl_false] at hxc
    exact Or.inr (degenerate_of_axis_sum (pq := (p, q)) hn hpq hd hxc)
  · rw [contrib_inl_true, M_symm n p q, sum_nu_B_eq_sum_nu_A n d p q] at hxc
    exact Or.inr (degenerate_symm.mp
      (degenerate_of_axis_sum (pq := (q, p)) hn (swap_mem_H hpq) hd hxc))
  · exact resonant_or_degenerate_of_dyadic hpq hM hd hK hL hxc'

end Paucity
