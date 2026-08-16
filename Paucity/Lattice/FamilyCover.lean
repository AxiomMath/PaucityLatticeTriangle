/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Tactic.Linarith
public import Paucity.Lattice.FamilyCount

/-!
# The families cover the punctured lattice box

Every point `(k,ℓ) ≠ (0,0)` of the lattice box at level `d` lies in the vertical axis family
`A_d(p,q)` when `k = 0`, in the horizontal axis family `B_d(p,q)` when `ℓ = 0`, and otherwise in
the dyadic class `Λ_d(K,L;p,q)` at the scales `K = 2^⌊log₂|k|⌋` and `L = 2^⌊log₂|ℓ|⌋`, which
satisfy `2K ≤ d` and `2L ≤ d`.

## Main definitions

* `dyadicScale`: the dyadic scale `2 ^ ⌊log₂ |k|⌋` of an integer `k`.

## Main results

* `dyadicScale_le_abs`: the scale of a nonzero `k` is at most `|k|`.
* `abs_lt_two_mul_dyadicScale`: `|k|` is below twice the scale.
* `two_mul_dyadicScale_le`: twice the scale of a nonzero coordinate of a point of the box is at
  most `d`.
* `exists_family_mem`: every point of the box other than the origin lies in one of the three kinds
  of family.
-/

@[expose] public section

namespace Paucity

open Finset

/-- The dyadic scale of a nonzero integer: `2 ^ ⌊log₂ |k|⌋`. -/
def dyadicScale (k : ℤ) : ℕ := 2 ^ Nat.log 2 k.natAbs

theorem dyadicScale_isPow (k : ℤ) : ∃ i, dyadicScale k = 2 ^ i :=
  ⟨Nat.log 2 k.natAbs, rfl⟩

theorem dyadicScale_pos (k : ℤ) : 0 < dyadicScale k :=
  pow_pos (by norm_num) _

/-- `|k|` as a real, from the natural absolute value. -/
theorem natAbs_cast_eq_abs (k : ℤ) : ((k.natAbs : ℕ) : ℝ) = |(k : ℝ)| := by
  rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]

/-- The scale is at most `|k|`. -/
theorem dyadicScale_le_abs {k : ℤ} (hk : k ≠ 0) : (dyadicScale k : ℝ) ≤ |(k : ℝ)| := by
  have hnat : dyadicScale k ≤ k.natAbs :=
    Nat.pow_log_le_self 2 (Int.natAbs_ne_zero.mpr hk)
  calc (dyadicScale k : ℝ) ≤ (k.natAbs : ℝ) := by exact_mod_cast hnat
    _ = |(k : ℝ)| := natAbs_cast_eq_abs k

/-- `|k|` is below twice the scale. -/
theorem abs_lt_two_mul_dyadicScale (k : ℤ) :
    |(k : ℝ)| < 2 * (dyadicScale k : ℝ) := by
  have hnat : k.natAbs < 2 * dyadicScale k := by
    have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) k.natAbs
    unfold dyadicScale
    calc k.natAbs < 2 ^ (Nat.log 2 k.natAbs + 1) := this
      _ = 2 * 2 ^ Nat.log 2 k.natAbs := by rw [pow_succ]; ring
  rw [← natAbs_cast_eq_abs k]
  exact_mod_cast hnat

/-- Twice the scale fits inside `d`, for a coordinate of a point of the box. -/
theorem two_mul_dyadicScale_le {d : ℕ} {k : ℤ} (hk : k ∈ F d) (hk0 : k ≠ 0) :
    2 * dyadicScale k ≤ d := by
  have h2 : 2 * |k| ≤ (d : ℤ) := two_mul_abs_le_of_mem_F hk
  have hle : (dyadicScale k : ℤ) ≤ |k| := by
    have : dyadicScale k ≤ k.natAbs := Nat.pow_log_le_self 2 (Int.natAbs_ne_zero.mpr hk0)
    calc (dyadicScale k : ℤ) ≤ (k.natAbs : ℤ) := by exact_mod_cast this
      _ = |k| := Int.natCast_natAbs k
  have : (2 * dyadicScale k : ℤ) ≤ (d : ℤ) := by linarith
  exact_mod_cast this

/-- Every point of the lattice box other than the origin lies in one of the labelled families: the
vertical axis family `A_d`, the horizontal axis family `B_d`, or the dyadic class at the scales of
its two coordinates. -/
theorem exists_family_mem {d p q : ℕ} {kl : ℤ × ℤ}
    (hmem : kl ∈ latticeBox d p q) (hne : kl ≠ (0, 0)) :
    kl ∈ A d p q ∨ kl ∈ B d p q ∨
      ∃ K L : ℕ, (∃ i, K = 2 ^ i) ∧ (∃ j, L = 2 ^ j) ∧ 2 * K ≤ d ∧ 2 * L ≤ d ∧
        kl ∈ dyadicBox d (K : ℝ) (L : ℝ) p q := by
  obtain ⟨⟨hkF, hlF⟩, -⟩ := mem_latticeBox.mp hmem
  rcases eq_or_ne kl.1 0 with hk0 | hk0
  · refine Or.inl (mem_A.mpr ⟨hmem, hk0, ?_⟩)
    intro hl0
    exact hne (Prod.ext hk0 hl0)
  rcases eq_or_ne kl.2 0 with hl0 | hl0
  · exact Or.inr (Or.inl (mem_B.mpr ⟨hmem, hl0, hk0⟩))
  refine Or.inr (Or.inr ⟨dyadicScale kl.1, dyadicScale kl.2,
    dyadicScale_isPow _, dyadicScale_isPow _,
    two_mul_dyadicScale_le hkF hk0, two_mul_dyadicScale_le hlF hl0, ?_⟩)
  exact mem_dyadicBox.mpr ⟨hmem,
    dyadicScale_le_abs hk0, abs_lt_two_mul_dyadicScale _,
    dyadicScale_le_abs hl0, abs_lt_two_mul_dyadicScale _⟩

end Paucity
