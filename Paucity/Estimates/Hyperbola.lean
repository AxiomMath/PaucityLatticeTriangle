/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.Data.Finset.Prod
public import Mathlib.Order.Interval.Finset.Nat

/-!
# The hyperbola count

The lattice points `(a, b)` with `a, b ≥ 1` and `ab ≤ N` number at most `N (1 + log N)`.

## Main results

* `hyperbola_fibre_card`: for fixed `a ≥ 1`, the `b ∈ [1, N]` with `ab ≤ N` number at most `N / a`.
* `hyperbola_card_le`: the pairs `(a, b) ∈ [1, N] × [1, N]` with `ab ≤ N` number at most
  `N (1 + log N)`.
-/

@[expose] public section

namespace Paucity

open Finset

/-- For `1 ≤ a`, the `b ∈ [1, N]` with `ab ≤ N` number at most `N / a`. -/
theorem hyperbola_fibre_card {N a : ℕ} (ha : 1 ≤ a) :
    ((Icc 1 N).filter fun b => a * b ≤ N).card ≤ N / a := by
  have hsub : ((Icc 1 N).filter fun b => a * b ≤ N) ⊆ Icc 1 (N / a) := by
    intro b hb
    rw [mem_filter, mem_Icc] at hb
    rw [mem_Icc]
    refine ⟨hb.1.1, ?_⟩
    exact Nat.le_div_iff_mul_le (by omega) |>.mpr (by rw [mul_comm]; exact hb.2)
  calc ((Icc 1 N).filter fun b => a * b ≤ N).card ≤ (Icc 1 (N / a)).card :=
        Finset.card_le_card hsub
    _ = N / a := by simp

/-- The lattice points under a hyperbola: the pairs `(a, b) ∈ [1, N] × [1, N]` with `ab ≤ N` number
at most `N (1 + log N)`. -/
theorem hyperbola_card_le (N : ℕ) :
    ((((Icc 1 N) ×ˢ (Icc 1 N)).filter fun ab => ab.1 * ab.2 ≤ N).card : ℝ)
      ≤ (N : ℝ) * (1 + Real.log N) := by
  classical
  have hcover : ((Icc 1 N) ×ˢ (Icc 1 N)).filter (fun ab => ab.1 * ab.2 ≤ N)
      ⊆ (Icc 1 N).biUnion fun a => {a} ×ˢ ((Icc 1 N).filter fun b => a * b ≤ N) := by
    intro ab hab
    rw [mem_filter, mem_product] at hab
    rw [mem_biUnion]
    exact ⟨ab.1, hab.1.1, by
      rw [mem_product, mem_singleton, mem_filter]
      exact ⟨rfl, hab.1.2, hab.2⟩⟩
  have hnat : (((Icc 1 N) ×ˢ (Icc 1 N)).filter fun ab => ab.1 * ab.2 ≤ N).card
      ≤ ∑ a ∈ Icc 1 N, N / a := by
    calc (((Icc 1 N) ×ˢ (Icc 1 N)).filter fun ab => ab.1 * ab.2 ≤ N).card
        ≤ ((Icc 1 N).biUnion fun a => {a} ×ˢ ((Icc 1 N).filter fun b => a * b ≤ N)).card :=
          Finset.card_le_card hcover
      _ ≤ ∑ a ∈ Icc 1 N, ({a} ×ˢ ((Icc 1 N).filter fun b => a * b ≤ N)).card :=
          Finset.card_biUnion_le
      _ = ∑ a ∈ Icc 1 N, ((Icc 1 N).filter fun b => a * b ≤ N).card := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.card_product, Finset.card_singleton, one_mul]
      _ ≤ ∑ a ∈ Icc 1 N, N / a := by
          refine Finset.sum_le_sum fun a ha => ?_
          exact hyperbola_fibre_card (mem_Icc.mp ha).1
  have hreal : ((∑ a ∈ Icc 1 N, N / a : ℕ) : ℝ) ≤ (N : ℝ) * (1 + Real.log N) := by
    have hstep : ((∑ a ∈ Icc 1 N, N / a : ℕ) : ℝ)
        ≤ ∑ a ∈ Icc 1 N, (N : ℝ) * ((a : ℝ))⁻¹ := by
      push_cast
      refine Finset.sum_le_sum fun a ha => ?_
      rw [← div_eq_mul_inv]
      exact Nat.cast_div_le
    have hharm : ∑ a ∈ Icc 1 N, (N : ℝ) * ((a : ℝ))⁻¹
        = (N : ℝ) * ((harmonic N : ℚ) : ℝ) := by
      rw [← Finset.mul_sum, harmonic_eq_sum_Icc]
      push_cast
      ring
    have hbound : ((harmonic N : ℚ) : ℝ) ≤ 1 + Real.log N := harmonic_le_one_add_log N
    have hNnn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    calc ((∑ a ∈ Icc 1 N, N / a : ℕ) : ℝ)
        ≤ ∑ a ∈ Icc 1 N, (N : ℝ) * ((a : ℝ))⁻¹ := hstep
      _ = (N : ℝ) * ((harmonic N : ℚ) : ℝ) := hharm
      _ ≤ (N : ℝ) * (1 + Real.log N) := mul_le_mul_of_nonneg_left hbound hNnn
  exact le_trans (by exact_mod_cast hnat) hreal

end Paucity
