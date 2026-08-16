/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Set.Card
public import Mathlib.LinearAlgebra.Basis.Fin
public import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
public import Mathlib.Tactic.FieldSimp
public import Paucity.Lattice.FiniteIndexLattice
public import Paucity.Lattice.MinAttained
public import Paucity.Lattice.MinPrimitive
public import Paucity.Lattice.PrimitiveBasis

/-!
# Few lattice points, or a short vector

For reals `A, B > 0`, a subgroup `Λ ⊆ ℤ²` of finite index `m`, and an integer `J ≥ 1` with
`J ≤ #{(x,y) ∈ Λ \ {0} : |x| ≤ A, |y| ≤ B}`, either `J < 24AB/m`, or `Λ` has a nonzero element
`w = (w₁,w₂)` with `|w₁| ≤ 4A/J` and `|w₂| ≤ 4B/J`.

## Main results

* `boxNorm_le_of_abs_le`: the coordinate bounds `|v₁| ≤ rA`, `|v₂| ≤ rB` give `‖v‖_{A,B} ≤ r`.
* `boxNorm_sub_le`: `‖x - y‖_{A,B} ≤ ‖x‖_{A,B} + ‖y‖_{A,B}`.
* `card_le_one_add_of_abs_sub_le`: a finite set of integers that are pairwise within `D` of each
  other has at most `1 + D` elements.
* `index_eq_natAbs_det_of_repr`: if `P, Q ∈ Λ ≤ ℤ²` represent every element of `Λ` uniquely as
  `a P + b Q`, then `[ℤ² : Λ] = |det (P, Q)|`.
* `finite_setOf_mem_abs_le`: the nonzero points of `Λ ⊆ ℤ²` in a box form a finite set.
* `lt_or_exists_short_vector`: the alternative above.
-/

@[expose] public section

namespace Paucity

open Module

/-- Coordinate bounds `|v₁| ≤ rA` and `|v₂| ≤ rB` give the box-norm bound `‖v‖_{A,B} ≤ r`. -/
theorem boxNorm_le_of_abs_le {A B r : ℝ} (hA : 0 < A) (hB : 0 < B) {v : ℝ × ℝ}
    (h1 : |v.1| ≤ r * A) (h2 : |v.2| ≤ r * B) : boxNorm A B v ≤ r := by
  unfold boxNorm
  exact max_le ((div_le_iff₀ hA).mpr h1) ((div_le_iff₀ hB).mpr h2)

/-- Subadditivity of the box norm on a difference: `‖x - y‖_{A,B} ≤ ‖x‖_{A,B} + ‖y‖_{A,B}`. -/
theorem boxNorm_sub_le {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (x y : ℝ × ℝ) :
    boxNorm A B (x - y) ≤ boxNorm A B x + boxNorm A B y := by
  obtain ⟨h1, h2⟩ := abs_le_of_boxNorm_le hA hB (le_refl (boxNorm A B x))
  obtain ⟨k1, k2⟩ := abs_le_of_boxNorm_le hA hB (le_refl (boxNorm A B y))
  refine boxNorm_le_of_abs_le hA hB ?_ ?_
  · calc |(x - y).1| = |x.1 - y.1| := rfl
      _ ≤ |x.1| + |y.1| := abs_sub _ _
      _ ≤ (boxNorm A B x + boxNorm A B y) * A := by nlinarith
  · calc |(x - y).2| = |x.2 - y.2| := rfl
      _ ≤ |x.2| + |y.2| := abs_sub _ _
      _ ≤ (boxNorm A B x + boxNorm A B y) * B := by nlinarith

/-- **Integers in an interval.** A finite set of integers whose elements are pairwise within `D` of
each other has at most `1 + D` elements. -/
theorem card_le_one_add_of_abs_sub_le (s : Finset ℤ) {D : ℝ} (hD : 0 ≤ D)
    (h : ∀ x ∈ s, ∀ y ∈ s, |(x : ℝ) - (y : ℝ)| ≤ D) : (s.card : ℝ) ≤ 1 + D := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simp only [Finset.card_empty, Nat.cast_zero]
    linarith
  have hlo := s.min'_le _ (s.max'_mem hne)
  have hsub : s ⊆ Finset.Icc (s.min' hne) (s.max' hne) := fun x hx =>
    Finset.mem_Icc.mpr ⟨s.min'_le x hx, s.le_max' x hx⟩
  have hcard : (s.card : ℤ) ≤ s.max' hne + 1 - s.min' hne := by
    rw [← Int.card_Icc_of_le (s.min' hne) (s.max' hne) (by omega)]
    exact_mod_cast Finset.card_le_card hsub
  have hcardR : (s.card : ℝ) ≤ ((s.max' hne : ℝ) + 1 - (s.min' hne : ℝ)) := by
    have h := (Int.cast_le (R := ℝ)).mpr hcard
    push_cast at h
    linarith
  have hspread : (s.max' hne : ℝ) - (s.min' hne : ℝ) ≤ D := by
    have hle := h _ (s.max'_mem hne) _ (s.min'_mem hne)
    have hnn : (0 : ℝ) ≤ (s.max' hne : ℝ) - (s.min' hne : ℝ) := by
      have h' : ((s.min' hne : ℤ) : ℝ) ≤ ((s.max' hne : ℤ) : ℝ) := by exact_mod_cast hlo
      linarith
    rwa [abs_of_nonneg hnn] at hle
  linarith

/-- **Index equals determinant.** If `P, Q ∈ Λ ≤ ℤ²` represent every element of `Λ` uniquely as
`a P + b Q` with `(a,b) ∈ ℤ²`, then `[ℤ² : Λ] = |det (P, Q)|`. -/
theorem index_eq_natAbs_det_of_repr {Λ : AddSubgroup (ℤ × ℤ)} {P Q : ℤ × ℤ}
    (hP : P ∈ Λ) (hQ : Q ∈ Λ)
    (hrep : ∀ y ∈ Λ, ∃! ab : ℤ × ℤ, y = ab.1 • P + ab.2 • Q) :
    Λ.index = (P.1 * Q.2 - P.2 * Q.1).natAbs := by
  have hmem : ∀ ab : ℤ × ℤ, ab.1 • P + ab.2 • Q ∈ Λ := fun ab =>
    Λ.add_mem (Λ.zsmul_mem hP _) (Λ.zsmul_mem hQ _)
  set g : (ℤ × ℤ) →+ ↥Λ :=
    { toFun := fun ab => ⟨ab.1 • P + ab.2 • Q, hmem ab⟩
      map_zero' := Subtype.ext (by simp)
      map_add' := fun x y => Subtype.ext (by simp [add_smul]; abel) } with hg
  have hgcoe : ∀ ab : ℤ × ℤ, ((g ab : ↥Λ) : ℤ × ℤ) = ab.1 • P + ab.2 • Q := fun _ => rfl
  have hinj : Function.Injective g := by
    intro x y hxy
    refine (hrep _ (hmem x)).unique rfl ?_
    have h := congrArg (fun z : ↥Λ => (z : ℤ × ℤ)) hxy
    rw [hgcoe, hgcoe] at h
    exact h
  have hsurj : Function.Surjective g := fun y => by
    obtain ⟨ab, hab, -⟩ := hrep (y : ℤ × ℤ) y.2
    exact ⟨ab, Subtype.ext (by rw [hgcoe]; exact hab.symm)⟩
  set e : (ℤ × ℤ) ≃ₗ[ℤ] ↥Λ := LinearEquiv.ofBijective g.toIntLinearMap ⟨hinj, hsurj⟩ with he
  have hcoe : ∀ ab : ℤ × ℤ, ((e ab : ↥Λ) : ℤ × ℤ) = ab.1 • P + ab.2 • Q := fun _ => rfl
  have hdet : (Basis.finTwoProd ℤ).det ![P, Q] = P.1 * Q.2 - P.2 * Q.1 := by
    rw [Basis.det_apply, Matrix.det_fin_two]
    simp only [Basis.toMatrix_apply, Basis.coe_finTwoProd_repr, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    ring
  rw [AddSubgroup.index_eq_natAbs_det (Basis.finTwoProd ℤ) Λ ((Basis.finTwoProd ℤ).map e)]
  congr 1
  have hfun : (fun i => ((((Basis.finTwoProd ℤ).map e) i : ↥Λ) : ℤ × ℤ)) = ![P, Q] := by
    funext i
    fin_cases i <;> simp [Basis.map_apply, hcoe]
  rw [hfun, hdet]

/-- The nonzero points of `Λ ⊆ ℤ²` in the box `|x| ≤ A`, `|y| ≤ B` form a finite set. -/
theorem finite_setOf_mem_abs_le (A B : ℝ) (Λ : AddSubgroup (ℤ × ℤ)) :
    {p : ℤ × ℤ | p ∈ Λ ∧ p ≠ 0 ∧ |(p.1 : ℝ)| ≤ A ∧ |(p.2 : ℝ)| ≤ B}.Finite := by
  have hceil : ∀ (c : ℤ) (r : ℝ), |(c : ℝ)| ≤ r → c ∈ Set.Icc (-⌈r⌉) ⌈r⌉ := by
    intro c r hc
    have h : ((|c| : ℤ) : ℝ) ≤ ((⌈r⌉ : ℤ) : ℝ) := by
      rw [Int.cast_abs]; exact hc.trans (Int.le_ceil r)
    exact Set.mem_Icc.mpr (abs_le.mp (by exact_mod_cast h))
  refine ((Set.finite_Icc (-⌈A⌉) ⌈A⌉).prod (Set.finite_Icc (-⌈B⌉) ⌈B⌉)).subset ?_
  exact fun p hp => ⟨hceil _ _ hp.2.2.1, hceil _ _ hp.2.2.2⟩

/-- **Few lattice points, or a short vector.** Let `A, B > 0` be reals, let `Λ ⊆ ℤ²` be a subgroup
of finite index `m`, and let `J ≥ 1` be an integer with
`J ≤ #{(x,y) ∈ Λ \ {0} : |x| ≤ A, |y| ≤ B}`. Then `J < 24AB/m`, or there is `w = (w₁,w₂) ∈ Λ \ {0}`
with `|w₁| ≤ 4A/J` and `|w₂| ≤ 4B/J`.

Here `Λ.index = m` with `m ≠ 0` says that the index is `m` and finite: in Mathlib `Λ.index = 0`
means the index is infinite.
-/
theorem lt_or_exists_short_vector {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    {Λ : AddSubgroup (ℤ × ℤ)} {m : ℕ} (hm : Λ.index = m) (hm0 : m ≠ 0)
    {J : ℕ} (hJ1 : 1 ≤ J)
    (hJ : J ≤ {p : ℤ × ℤ | p ∈ Λ ∧ p ≠ 0 ∧ |(p.1 : ℝ)| ≤ A ∧ |(p.2 : ℝ)| ≤ B}.ncard) :
    (J : ℝ) < 24 * A * B / (m : ℝ) ∨
      ∃ w ∈ Λ, w ≠ 0 ∧ |(w.1 : ℝ)| ≤ 4 * A / (J : ℝ) ∧ |(w.2 : ℝ)| ≤ 4 * B / (J : ℝ) := by
  rcases lt_or_ge (J : ℝ) (24 * A * B / (m : ℝ)) with h24 | h24
  · exact Or.inl h24
  right
  have hmpos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm0)
  have hJpos : (0 : ℝ) < (J : ℝ) := Nat.cast_pos.mpr hJ1
  set S := {p : ℤ × ℤ | p ∈ Λ ∧ p ≠ 0 ∧ |(p.1 : ℝ)| ≤ A ∧ |(p.2 : ℝ)| ≤ B} with hS
  have hmemS : ∀ p : ℤ × ℤ,
      p ∈ S ↔ p ∈ Λ ∧ p ≠ 0 ∧ |(p.1 : ℝ)| ≤ A ∧ |(p.2 : ℝ)| ≤ B := fun p => by
    rw [hS]; exact Iff.rfl
  have hSfin : S.Finite := by rw [hS]; exact finite_setOf_mem_abs_le A B Λ
  have hlat : IsLattice (Λ.map intPairCast) :=
    isLattice_map_intPairCast Λ (by rw [hm]; exact hm0)
  obtain ⟨w, hwΛ, hw0, hwmin⟩ := exists_boxNorm_eq_lambdaMin hA hB hlat
  obtain ⟨w', hb⟩ := exists_isBasis_of_not_proper_multiple hlat hwΛ hw0
    (not_proper_multiple_of_boxNorm_eq_lambdaMin hA hB hwΛ hw0 hwmin)
  obtain ⟨P, hPΛ, hPw⟩ := AddSubgroup.mem_map.mp hwΛ
  obtain ⟨Q, hQΛ, hQw⟩ := AddSubgroup.mem_map.mp hb.mem_right
  set lam := lambdaMin A B (Λ.map intPairCast) with hlamdef
  have hlampos : 0 < lam := by
    rw [← hwmin]
    rcases (boxNorm_nonneg hA B w).lt_or_eq with h | h
    · exact h
    · exact absurd ((boxNorm_eq_zero_iff hA hB).mp h.symm) hw0
  obtain ⟨hw1, hw2⟩ := abs_le_of_boxNorm_le hA hB (le_of_eq hwmin)
  have hw1e : w.1 = (P.1 : ℝ) := by rw [← hPw]; rfl
  have hw2e : w.2 = (P.2 : ℝ) := by rw [← hPw]; rfl
  have hw1e' : w'.1 = (Q.1 : ℝ) := by rw [← hQw]; rfl
  have hw2e' : w'.2 = (Q.2 : ℝ) := by rw [← hQw]; rfl
  have hP0 : P ≠ 0 := fun h => hw0 (by rw [← hPw, h, map_zero])
  have hlam1 : lam ≤ 1 := by
    obtain ⟨p, hp⟩ := Set.nonempty_of_ncard_ne_zero (s := S) (by omega)
    obtain ⟨hpΛ, hp0, hp1, hp2⟩ := (hmemS p).mp hp
    have hne : intPairCast p ≠ 0 := fun h =>
      hp0 (intPairCast_injective (by rw [h, map_zero]))
    rw [hlamdef]
    refine (lambdaMin_le hA B (AddSubgroup.mem_map_of_mem intPairCast hpΛ) hne).trans
      (boxNorm_le_of_abs_le hA hB ?_ ?_)
    · simpa [intPairCast_apply] using hp1
    · simpa [intPairCast_apply] using hp2
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = A * B / (m : ℝ) := ⟨_, rfl⟩
  have htpos : 0 < t := ht ▸ div_pos (mul_pos hA hB) hmpos
  have h24' : 24 * t ≤ (J : ℝ) := by
    have h : 24 * t = 24 * A * B / (m : ℝ) := by rw [ht]; ring
    rw [h]; exact h24
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = 2 / lam := ⟨_, rfl⟩
  have hulam : lam * u = 2 := by rw [hu]; field_simp
  have hu0 : 0 ≤ u := hu ▸ div_nonneg (by norm_num) hlampos.le
  have hcast : ∀ ab : ℤ × ℤ,
      intPairCast (ab.1 • P + ab.2 • Q) = (ab.1 : ℝ) • w + (ab.2 : ℝ) • w' := by
    intro ab
    rw [map_add, map_zsmul, map_zsmul, hPw, hQw, Int.cast_smul_eq_zsmul,
      Int.cast_smul_eq_zsmul]
  have hrepZ : ∀ y ∈ Λ, ∃! ab : ℤ × ℤ, y = ab.1 • P + ab.2 • Q := by
    intro y hy
    obtain ⟨ab, hab, huniq⟩ := hb.unique_rep (intPairCast y) (AddSubgroup.mem_map_of_mem _ hy)
    exact ⟨ab, intPairCast_injective (by rw [hcast]; exact hab),
      fun cd hcd => huniq cd (by rw [hcd, hcast])⟩
  have hmabs : (m : ℝ) = |w.1 * w'.2 - w.2 * w'.1| := by
    have hmnat : m = (P.1 * Q.2 - P.2 * Q.1).natAbs := by
      rw [← hm]; exact index_eq_natAbs_det_of_repr hPΛ hQΛ hrepZ
    have hD : w.1 * w'.2 - w.2 * w'.1 = ((P.1 * Q.2 - P.2 * Q.1 : ℤ) : ℝ) := by
      rw [hw1e, hw2e, hw1e', hw2e']; push_cast; ring
    rw [hD, hmnat, Nat.cast_natAbs, Int.cast_abs]
  set C : Set (ℤ × ℤ) :=
    {ab : ℤ × ℤ | boxNorm A B ((ab.1 : ℝ) • w + (ab.2 : ℝ) • w') ≤ 1} with hC
  have hmemC : ∀ ab : ℤ × ℤ,
      ab ∈ C ↔ boxNorm A B ((ab.1 : ℝ) • w + (ab.2 : ℝ) • w') ≤ 1 := fun ab => by
    rw [hC]; exact Iff.rfl
  have himg : ((fun ab : ℤ × ℤ => (ab.1 : ℝ) • w + (ab.2 : ℝ) • w') '' C).Finite := by
    refine (hb.finite_setOf_boxNorm_le hA hB 1).subset ?_
    rintro x ⟨ab, habC, rfl⟩
    exact ⟨intCast_smul_add_intCast_smul_mem hb.mem_left hb.mem_right ab.1 ab.2,
      (hmemC ab).mp habC⟩
  have hCfin : C.Finite := by
    refine himg.of_finite_image ?_
    intro ab _ cd _ h
    obtain ⟨h1, h2⟩ := coords_injective hb.indep h
    exact Prod.ext h1 h2
  have hkey : ∀ p : ℤ × ℤ, p ∈ Λ → |(p.1 : ℝ)| ≤ A → |(p.2 : ℝ)| ≤ B →
      p ∈ (fun ab : ℤ × ℤ => ab.1 • P + ab.2 • Q) '' C := by
    intro p hpΛ h1 h2
    obtain ⟨ab, hab⟩ := hb.exists_rep (AddSubgroup.mem_map_of_mem intPairCast hpΛ)
    refine ⟨ab, ?_, ?_⟩
    · rw [hmemC ab, ← hab]
      exact boxNorm_le_of_abs_le hA hB (by simpa [intPairCast_apply] using h1)
        (by simpa [intPairCast_apply] using h2)
    · change ab.1 • P + ab.2 • Q = p
      exact intPairCast_injective (by rw [hcast]; exact hab.symm)
  have hJC : (J : ℝ) + 1 ≤ (C.ncard : ℝ) := by
    have hsub : insert (0 : ℤ × ℤ) S ⊆ (fun ab : ℤ × ℤ => ab.1 • P + ab.2 • Q) '' C := by
      intro p hp
      rcases hp with rfl | hp
      · exact hkey 0 Λ.zero_mem (by simpa using hA.le) (by simpa using hB.le)
      · obtain ⟨hpΛ, -, h1, h2⟩ := (hmemS p).mp hp
        exact hkey p hpΛ h1 h2
    have h : S.ncard + 1 ≤ C.ncard := by
      rw [← Set.ncard_insert_of_notMem (fun h => ((hmemS 0).mp h).2.1 rfl) hSfin]
      exact (Set.ncard_le_ncard hsub (hCfin.image _)).trans (Set.ncard_image_le hCfin)
    have h' : J + 1 ≤ C.ncard := by omega
    exact_mod_cast h'
  have hbnd2 : ∀ ab : ℤ × ℤ, ab ∈ C → |(ab.2 : ℝ)| ≤ 2 * lam * t := by
    intro ab habC
    obtain ⟨hx1, hx2⟩ := abs_le_of_boxNorm_le hA hB ((hmemC ab).mp habC)
    set X : ℝ × ℝ := (ab.1 : ℝ) • w + (ab.2 : ℝ) • w' with hX
    have e1 : X.1 = (ab.1 : ℝ) * w.1 + (ab.2 : ℝ) * w'.1 := by rw [hX]; simp
    have e2 : X.2 = (ab.1 : ℝ) * w.2 + (ab.2 : ℝ) * w'.2 := by rw [hX]; simp
    have hb1 : |X.1| ≤ A := by simpa using hx1
    have hb2 : |X.2| ≤ B := by simpa using hx2
    have t1 : |X.2| * |w.1| ≤ B * (lam * A) := mul_le_mul hb2 hw1 (abs_nonneg _) hB.le
    have t2 : |X.1| * |w.2| ≤ A * (lam * B) := mul_le_mul hb1 hw2 (abs_nonneg _) hA.le
    have hkeyid : |(ab.2 : ℝ)| * (m : ℝ) = |X.2 * w.1 - X.1 * w.2| := by
      rw [hmabs, ← abs_mul]
      congr 1
      rw [e1, e2]; ring
    have hshape : 2 * lam * t = 2 * lam * A * B / (m : ℝ) := by rw [ht]; ring
    rw [hshape]
    refine (le_div_iff₀ hmpos).mpr ?_
    rw [hkeyid]
    calc |X.2 * w.1 - X.1 * w.2| ≤ |X.2 * w.1| + |X.1 * w.2| := abs_sub _ _
      _ = |X.2| * |w.1| + |X.1| * |w.2| := by rw [abs_mul, abs_mul]
      _ ≤ 2 * lam * A * B := by linarith
  have hFib : ∀ ab cd : ℤ × ℤ, ab ∈ C → cd ∈ C → ab.2 = cd.2 →
      |(ab.1 : ℝ) - (cd.1 : ℝ)| ≤ u := by
    intro ab cd habC hcdC heq
    have hx := (hmemC ab).mp habC
    have hx' := (hmemC cd).mp hcdC
    rw [heq] at hx
    have hdiff : ((ab.1 : ℝ) • w + (cd.2 : ℝ) • w') - ((cd.1 : ℝ) • w + (cd.2 : ℝ) • w')
        = ((ab.1 : ℝ) - (cd.1 : ℝ)) • w := by module
    have h2 : boxNorm A B (((ab.1 : ℝ) - (cd.1 : ℝ)) • w) ≤ 2 := by
      rw [← hdiff]
      linarith [boxNorm_sub_le hA hB ((ab.1 : ℝ) • w + (cd.2 : ℝ) • w')
        ((cd.1 : ℝ) • w + (cd.2 : ℝ) • w')]
    rw [boxNorm_smul, hwmin] at h2
    rw [hu, le_div_iff₀ hlampos]
    linarith
  have hCcard : (C.ncard : ℝ) ≤ (1 + 4 * lam * t) * (1 + u) := by
    have hsplit := Finset.card_eq_sum_card_image (Prod.snd : ℤ × ℤ → ℤ) hCfin.toFinset
    have hfibb : ∀ b ∈ hCfin.toFinset.image Prod.snd,
        (((hCfin.toFinset.filter fun ab => ab.2 = b).card : ℕ) : ℝ) ≤ 1 + u := by
      intro b _
      have hinj : Set.InjOn Prod.fst
          ((hCfin.toFinset.filter fun ab : ℤ × ℤ => ab.2 = b) : Set (ℤ × ℤ)) := by
        intro x hx y hy hxy
        simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hx hy
        exact Prod.ext hxy (hx.2.trans hy.2.symm)
      rw [← Finset.card_image_of_injOn hinj]
      refine card_le_one_add_of_abs_sub_le _ hu0 ?_
      intro x hx y hy
      simp only [Finset.mem_image, Finset.mem_filter, Set.Finite.mem_toFinset] at hx hy
      obtain ⟨p, ⟨hpC, hpb⟩, rfl⟩ := hx
      obtain ⟨q, ⟨hqC, hqb⟩, rfl⟩ := hy
      exact hFib p q hpC hqC (by rw [hpb, hqb])
    have hBs : ((hCfin.toFinset.image Prod.snd).card : ℝ) ≤ 1 + 4 * lam * t := by
      refine card_le_one_add_of_abs_sub_le _
        (mul_nonneg (mul_nonneg (by norm_num) hlampos.le) htpos.le) ?_
      intro x hx y hy
      simp only [Finset.mem_image, Set.Finite.mem_toFinset] at hx hy
      obtain ⟨p, hpC, rfl⟩ := hx
      obtain ⟨q, hqC, rfl⟩ := hy
      have h1 := hbnd2 p hpC
      have h2 := hbnd2 q hqC
      calc |((p.2 : ℤ) : ℝ) - ((q.2 : ℤ) : ℝ)| ≤ |((p.2 : ℤ) : ℝ)| + |((q.2 : ℤ) : ℝ)| :=
            abs_sub _ _
        _ ≤ 4 * lam * t := by linarith
    calc (C.ncard : ℝ) = (hCfin.toFinset.card : ℝ) := by
          rw [Set.ncard_eq_toFinset_card C hCfin]
      _ = ∑ b ∈ hCfin.toFinset.image Prod.snd,
            (((hCfin.toFinset.filter fun ab => ab.2 = b).card : ℕ) : ℝ) := by
          rw [hsplit, Nat.cast_sum]
      _ ≤ ∑ _b ∈ hCfin.toFinset.image Prod.snd, (1 + u) := Finset.sum_le_sum hfibb
      _ = ((hCfin.toFinset.image Prod.snd).card : ℝ) * (1 + u) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (1 + 4 * lam * t) * (1 + u) :=
          mul_le_mul_of_nonneg_right hBs (by linarith)
  have hexp : lam * ((1 + 4 * lam * t) * (1 + u))
      = lam + 2 + 4 * lam * lam * t + 8 * lam * t := by
    linear_combination (1 + 4 * lam * t) * hulam
  have e1 : lam * ((J : ℝ) + 1) ≤ lam + 2 + 4 * lam * lam * t + 8 * lam * t := by
    rw [← hexp]
    exact mul_le_mul_of_nonneg_left (hJC.trans hCcard) hlampos.le
  have e2 : 0 ≤ (1 - lam) * (lam * t) :=
    mul_nonneg (by linarith) (mul_pos hlampos htpos).le
  have e3 : lam * (24 * t) ≤ lam * (J : ℝ) := mul_le_mul_of_nonneg_left h24' hlampos.le
  have hlam4 : lam ≤ 4 / (J : ℝ) := (le_div_iff₀ hJpos).mpr (by linarith)
  refine ⟨P, hPΛ, hP0, ?_, ?_⟩
  · calc |(P.1 : ℝ)| = |w.1| := by rw [hw1e]
      _ ≤ lam * A := hw1
      _ ≤ 4 / (J : ℝ) * A := mul_le_mul_of_nonneg_right hlam4 hA.le
      _ = 4 * A / (J : ℝ) := by ring
  · calc |(P.2 : ℝ)| = |w.2| := by rw [hw2e]
      _ ≤ lam * B := hw2
      _ ≤ 4 / (J : ℝ) * B := mul_le_mul_of_nonneg_right hlam4 hB.le
      _ = 4 * B / (J : ℝ) := by ring

end Paucity
