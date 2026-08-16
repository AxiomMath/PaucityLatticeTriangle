/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Tactic.Linarith
public import Paucity.Defs.LatticeBox
public import Paucity.Defs.Nd
public import Paucity.Defs.Fourier
public import Paucity.Defs.Ind
public import Paucity.Majorant.Orthogonality

/-!
# The Fourier expansion of `Nd`

For `d ≥ 2` the divisor-level count `Nd n d p q` equals `d` times the sum, over the lattice
box `latticeBox d p q = Λ_d(p,q) ∩ (F d × F d)`, of the products of the Fourier
coefficients of the two window indicators. The identity is exact, and it comes from
orthogonality on `ℤ/dℤ` together with Fourier inversion over the symmetric representatives
`F d`.

## Main results

* `res_eq_of_dvd_sub`, `ind_eq_of_dvd_sub`: `d`-periodicity of the least nonnegative
  residue and of the window indicator.
* `F_eq_image`: `F d` is a complete set of representatives modulo `d`.
* `sum_e_over_F`: orthogonality over `F d`.
* `dft_ind_inversion`: Fourier inversion for the window indicator.
* `Nd_eq_sum_ind_cast`: the `ℂ`-valued form of `Nd_eq_sum_ind`.
* `sum_ind_mul_ind_eq`: the period sum of a product of two indicators, at arbitrary window
  lengths.
* `Nd_eq_fourier`: the Fourier expansion of `Nd n d p q`.
-/

@[expose] public section

namespace Paucity

open Finset Real

/-- The least nonnegative residue is `d`-periodic: `res x d = res y d` whenever
`d ∣ x - y`. -/
theorem res_eq_of_dvd_sub {d : ℕ} {x y : ℤ} (h : (d : ℤ) ∣ x - y) :
    res x d = res y d := by
  have hxy : x % (d : ℤ) = y % (d : ℤ) := Int.ModEq.symm (Int.modEq_iff_dvd.mpr h)
  unfold res
  rw [hxy]

/-- The window indicator is `d`-periodic: `ind d H x = ind d H y` whenever `d ∣ x - y`. -/
theorem ind_eq_of_dvd_sub {d H : ℕ} {x y : ℤ} (h : (d : ℤ) ∣ x - y) :
    ind d H x = ind d H y := by
  unfold ind
  rw [res_eq_of_dvd_sub h]

/-- `F d` is a complete set of representatives modulo `d`, exhibited as the image of
`[1, d]` under the shift that folds `(d/2, d]` down to the negative half. -/
theorem F_eq_image {d : ℕ} (hd : 0 < d) :
    F d = (Icc 1 d).image fun b : ℕ => if 2 * b ≤ d then (b : ℤ) else (b : ℤ) - (d : ℤ) := by
  ext k
  simp only [mem_F, mem_image, mem_Icc]
  constructor
  · intro hk
    by_cases hpos : 1 ≤ k
    · exact ⟨k.toNat, by omega, by rw [if_pos (by omega)]; omega⟩
    · exact ⟨(k + (d : ℤ)).toNat, by omega, by rw [if_neg (by omega)]; omega⟩
  · rintro ⟨b, hb, rfl⟩
    split_ifs with h2 <;> omega

/-- Orthogonality over the symmetric representatives: `∑_{k ∈ F d} e(km/d)` is `d` when
`d ∣ m` and `0` otherwise. -/
theorem sum_e_over_F {d : ℕ} (hd : 0 < d) (m : ℤ) :
    ∑ k ∈ F d, e ((k : ℝ) * (m : ℝ) / (d : ℝ)) = if (d : ℤ) ∣ m then (d : ℂ) else 0 := by
  have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  have hinj : Set.InjOn (fun b : ℕ => if 2 * b ≤ d then (b : ℤ) else (b : ℤ) - (d : ℤ))
      (Icc 1 d : Finset ℕ) := by
    intro a ha b hb hab
    simp only [Finset.coe_Icc, Set.mem_Icc] at ha hb
    simp only at hab
    split_ifs at hab <;> omega
  rw [← sum_e_intCast_div hd m, F_eq_image hd, sum_image hinj]
  refine sum_congr rfl fun b _ => ?_
  split_ifs with h2
  · norm_num
  · rw [show (((b : ℤ) - (d : ℤ) : ℤ) : ℝ) * (m : ℝ) / (d : ℝ)
        = (b : ℝ) * (m : ℝ) / (d : ℝ) + ((-m : ℤ) : ℝ) by push_cast; field_simp; ring,
      e_add, e_intCast, mul_one]

/-- Fourier inversion for the window indicator:
`χ(x) = ∑_{k ∈ F d} χ̂^{(d)}(k) e(kx/d)`, at every `x : ℤ` and every window length
`H`. -/
theorem dft_ind_inversion {d H : ℕ} (hd : 0 < d) (x : ℤ) :
    ∑ k ∈ F d, dft d (fun y => (ind d H y : ℂ)) k * e ((k : ℝ) * (x : ℝ) / (d : ℝ))
      = (ind d H x : ℂ) := by
  have hdC : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  have hdZ : (0 : ℤ) < (d : ℤ) := by exact_mod_cast hd
  have step1 : ∀ k ∈ F d,
      dft d (fun y => (ind d H y : ℂ)) k * e ((k : ℝ) * (x : ℝ) / (d : ℝ))
        = (1 / (d : ℂ)) * ∑ y ∈ Icc (1 : ℤ) (d : ℤ),
            (ind d H y : ℂ) * e ((k : ℝ) * ((x - y : ℤ) : ℝ) / (d : ℝ)) := by
    intro k _
    unfold dft
    rw [mul_assoc, sum_mul]
    congr 1
    refine sum_congr rfl fun y _ => ?_
    rw [mul_assoc, ← e_add,
      show -((k * y : ℤ) : ℝ) / (d : ℝ) + (k : ℝ) * (x : ℝ) / (d : ℝ)
        = (k : ℝ) * ((x - y : ℤ) : ℝ) / (d : ℝ) by push_cast; ring]
  rw [sum_congr rfl step1, ← mul_sum, sum_comm]
  have step2 : ∀ y ∈ Icc (1 : ℤ) (d : ℤ),
      ∑ k ∈ F d, (ind d H y : ℂ) * e ((k : ℝ) * ((x - y : ℤ) : ℝ) / (d : ℝ))
        = (ind d H y : ℂ) * (if (d : ℤ) ∣ x - y then (d : ℂ) else 0) := by
    intro y _
    rw [← mul_sum, sum_e_over_F hd]
  rw [sum_congr rfl step2]
  have hlt : (x - 1) % (d : ℤ) < (d : ℤ) := Int.emod_lt_of_pos _ hdZ
  have hnn : 0 ≤ (x - 1) % (d : ℤ) := Int.emod_nonneg _ hdZ.ne'
  have hmem : (x - 1) % (d : ℤ) + 1 ∈ Icc (1 : ℤ) (d : ℤ) := by
    rw [mem_Icc]; omega
  have hdvd : (d : ℤ) ∣ x - ((x - 1) % (d : ℤ) + 1) := by
    have h : (d : ℤ) ∣ (x - 1) - (x - 1) % (d : ℤ) :=
      Int.modEq_iff_dvd.mp (Int.emod_emod_of_dvd _ dvd_rfl)
    have hrw : x - ((x - 1) % (d : ℤ) + 1) = (x - 1) - (x - 1) % (d : ℤ) := by ring
    rw [hrw]
    exact h
  rw [sum_eq_single_of_mem _ hmem, if_pos hdvd, ind_eq_of_dvd_sub hdvd]
  · field_simp
  · intro y hy hne
    rw [mem_Icc] at hy
    have hnd : ¬ ((d : ℤ) ∣ x - y) := by
      intro hc
      have hsub : (d : ℤ) ∣ ((x - 1) % (d : ℤ) + 1) - y := by
        have : ((x - 1) % (d : ℤ) + 1) - y = (x - y) - (x - ((x - 1) % (d : ℤ) + 1)) := by ring
        rw [this]
        exact dvd_sub hc hdvd
      have hne' : ((x - 1) % (d : ℤ) + 1) - y ≠ 0 := by omega
      have hle := Int.le_of_dvd (abs_pos.mpr hne') ((dvd_abs _ _).mpr hsub)
      rcases abs_cases (((x - 1) % (d : ℤ) + 1) - y) with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
    rw [if_neg hnd, mul_zero]

/-- The `ℂ`-valued form of `Nd_eq_sum_ind`: `Nd n d p q` is the sum over `b ∈ [1, d]` of
the product of the two window indicators at `bp` and `bq`. -/
theorem Nd_eq_sum_ind_cast (n d p q : ℕ) :
    (Nd n d p q : ℂ) = ∑ b ∈ Icc 1 d,
      (ind d (Hd n d p) ((b : ℤ) * p) : ℂ) * (ind d (Hd n d q) ((b : ℤ) * q) : ℂ) := by
  rw [Nd_eq_sum_ind]
  push_cast
  ring

/-- The period sum of a product of two window indicators, at arbitrary window lengths: it
is `d` times the sum over `latticeBox d p q` of the products of their Fourier
coefficients. -/
theorem sum_ind_mul_ind_eq {d : ℕ} (hd : 0 < d) (Hp Hq p q : ℕ) :
    ∑ b ∈ Icc 1 d, (ind d Hp ((b : ℤ) * p) : ℂ) * (ind d Hq ((b : ℤ) * q) : ℂ)
      = (d : ℂ) * ∑ kl ∈ latticeBox d p q,
          dft d (fun x => (ind d Hp x : ℂ)) kl.1 * dft d (fun x => (ind d Hq x : ℂ)) kl.2 := by
  have h1 : ∀ b ∈ Icc 1 d,
      (ind d Hp ((b : ℤ) * p) : ℂ) * (ind d Hq ((b : ℤ) * q) : ℂ)
        = ∑ kl ∈ F d ×ˢ F d,
            (dft d (fun x => (ind d Hp x : ℂ)) kl.1 * dft d (fun x => (ind d Hq x : ℂ)) kl.2)
              * e ((b : ℝ) * ((kl.1 * p + kl.2 * q : ℤ) : ℝ) / (d : ℝ)) := by
    intro b _
    rw [← dft_ind_inversion hd ((b : ℤ) * p), ← dft_ind_inversion hd ((b : ℤ) * q),
      sum_mul_sum, ← sum_product']
    refine sum_congr rfl fun kl _ => ?_
    rw [mul_mul_mul_comm]
    congr 1
    rw [← e_add]
    congr 1
    push_cast
    ring
  rw [sum_congr rfl h1, sum_comm]
  have h2 : ∀ kl ∈ F d ×ˢ F d,
      ∑ b ∈ Icc 1 d,
          (dft d (fun x => (ind d Hp x : ℂ)) kl.1 * dft d (fun x => (ind d Hq x : ℂ)) kl.2)
            * e ((b : ℝ) * ((kl.1 * p + kl.2 * q : ℤ) : ℝ) / (d : ℝ))
        = (dft d (fun x => (ind d Hp x : ℂ)) kl.1 * dft d (fun x => (ind d Hq x : ℂ)) kl.2)
            * (if kl ∈ dualLattice d p q then (d : ℂ) else 0) := by
    intro kl _
    rw [← mul_sum, sum_e_eq_ite hd kl]
  rw [sum_congr rfl h2, mul_sum]
  unfold latticeBox
  rw [sum_filter]
  refine sum_congr rfl fun kl _ => ?_
  split_ifs <;> ring

/-- The Fourier expansion of the divisor-level count: for `d ≥ 2`, `Nd n d p q` is `d`
times the sum over `latticeBox d p q = Λ_d(p,q) ∩ (F d × F d)` of the products of the
Fourier coefficients of the two window indicators. The identity is exact. -/
theorem Nd_eq_fourier {n d p q : ℕ} (hd : 2 ≤ d) :
    (Nd n d p q : ℂ) = (d : ℂ) * ∑ kl ∈ latticeBox d p q,
      dft d (fun x => (ind d (Hd n d p) x : ℂ)) kl.1 *
        dft d (fun x => (ind d (Hd n d q) x : ℂ)) kl.2 := by
  rw [Nd_eq_sum_ind_cast, sum_ind_mul_ind_eq (by omega)]

end Paucity
