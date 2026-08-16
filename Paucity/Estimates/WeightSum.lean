/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.Tactic.Linarith
public import Paucity.Defs.Weight

/-!
# The weight sum bound

For `N ≥ 2` the circle weights `w N k = 1 / (2 min(k, N - k))` satisfy
`∑_{k=1}^{N-1} w N k ≤ 1 + log N`.

## Main results

* `sum_w_le_one_add_log`: `∑ k ∈ Icc 1 (N - 1), w N k ≤ 1 + log N` for `N ≥ 2`.
-/

@[expose] public section

namespace Paucity

/-- The circle weights sum to at most `1 + log N`: `∑_{k=1}^{N-1} w N k ≤ 1 + log N` for `N ≥ 2`.

Weaker by the additive constant `1` than Lemma 3.1 of *On the paucity of lattice triangles*, which
gives `∑_{k=1}^{N-1} w N k ≤ log N`. -/
theorem sum_w_le_one_add_log {N : ℕ} (hN : 2 ≤ N) :
    ∑ k ∈ Finset.Icc 1 (N - 1), w N k ≤ 1 + Real.log N := by
  have hN1 : (0 : ℝ) < ((N - 1 : ℕ) : ℝ) := by
    have h : 0 < N - 1 := by omega
    exact_mod_cast h
  have hpt : ∀ k ∈ Finset.Icc 1 (N - 1),
      w N k ≤ 2⁻¹ * (k : ℝ)⁻¹ + 2⁻¹ * ((N - k : ℕ) : ℝ)⁻¹ := by
    intro k _
    have h₁ : (0 : ℝ) ≤ 2⁻¹ * (k : ℝ)⁻¹ := by positivity
    have h₂ : (0 : ℝ) ≤ 2⁻¹ * ((N - k : ℕ) : ℝ)⁻¹ := by positivity
    unfold w
    rw [one_div, mul_inv]
    rcases le_total k (N - k) with h | h
    · rw [min_eq_left h]; linarith
    · rw [min_eq_right h]; linarith
  have hrefl : ∑ k ∈ Finset.Icc 1 (N - 1), ((N - k : ℕ) : ℝ)⁻¹
      = ∑ k ∈ Finset.Icc 1 (N - 1), (k : ℝ)⁻¹ :=
    Finset.sum_nbij' (fun k => N - k) (fun k => N - k)
      (fun a ha => by simp only [Finset.mem_Icc] at ha ⊢; omega)
      (fun a ha => by simp only [Finset.mem_Icc] at ha ⊢; omega)
      (fun a ha => by simp only [Finset.mem_Icc] at ha; omega)
      (fun a ha => by simp only [Finset.mem_Icc] at ha; omega)
      (fun _ _ => rfl)
  have hmono : ((N - 1 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.sub_le N 1
  calc ∑ k ∈ Finset.Icc 1 (N - 1), w N k
      ≤ ∑ k ∈ Finset.Icc 1 (N - 1), (2⁻¹ * (k : ℝ)⁻¹ + 2⁻¹ * ((N - k : ℕ) : ℝ)⁻¹) :=
        Finset.sum_le_sum hpt
    _ = ∑ k ∈ Finset.Icc 1 (N - 1), (k : ℝ)⁻¹ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hrefl]; ring
    _ = (harmonic (N - 1) : ℝ) := by push_cast [harmonic_eq_sum_Icc]; ring
    _ ≤ 1 + Real.log ((N - 1 : ℕ) : ℝ) := harmonic_le_one_add_log _
    _ ≤ 1 + Real.log (N : ℝ) := by linarith [Real.log_le_log hN1 hmono]

end Paucity
