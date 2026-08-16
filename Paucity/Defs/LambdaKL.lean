/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith
public import Paucity.Defs.LatticeBox

/-!
# Dyadic blocks of the dual lattice

The dual-lattice points of the box lying in a dyadic annulus,
`Λ_d(K,L;p,q) = {(k,ℓ) ∈ Λ_d(p,q) ∩ (F_d × F_d) : K ≤ |k| < 2K, L ≤ |ℓ| < 2L}`, with `K` and `L`
real. For `K ≤ 0` the upper bound `|k| < 2K` fails for every `k`, so the block is empty.

## Main definitions

* `dyadicBox`: the dual-lattice points of the box with `K ≤ |k| < 2K` and `L ≤ |ℓ| < 2L`.

## Main results

* `dyadicBox_subset`: a dyadic block is contained in `latticeBox d p q`.
* `fst_ne_zero`, `snd_ne_zero`: for `1 ≤ K` and `1 ≤ L` neither coordinate vanishes.
* `swap_mem_dyadicBox`, `card_dyadicBox_swap`: transposing pairs exchanges `p` with `q` and `K`
  with `L`, and the two blocks have equal cardinality.
-/

@[expose] public section

namespace Paucity

open Finset

/-- `dyadicBox d K L p q`, the set `Λ_d(K,L;p,q)`: the dual-lattice points of the box lying in the
dyadic annulus `K ≤ |k| < 2K`, `L ≤ |ℓ| < 2L`. -/
noncomputable def dyadicBox (d : ℕ) (K L : ℝ) (p q : ℕ) : Finset (ℤ × ℤ) :=
  (latticeBox d p q).filter fun kl =>
    K ≤ |(kl.1 : ℝ)| ∧ |(kl.1 : ℝ)| < 2 * K ∧ L ≤ |(kl.2 : ℝ)| ∧ |(kl.2 : ℝ)| < 2 * L

@[simp] theorem mem_dyadicBox {d : ℕ} {K L : ℝ} {p q : ℕ} {kl : ℤ × ℤ} :
    kl ∈ dyadicBox d K L p q ↔ kl ∈ latticeBox d p q ∧
      K ≤ |(kl.1 : ℝ)| ∧ |(kl.1 : ℝ)| < 2 * K ∧ L ≤ |(kl.2 : ℝ)| ∧ |(kl.2 : ℝ)| < 2 * L := by
  unfold dyadicBox; exact mem_filter

/-- A dyadic block is contained in the box it was cut from. -/
theorem dyadicBox_subset (d : ℕ) (K L : ℝ) (p q : ℕ) :
    dyadicBox d K L p q ⊆ latticeBox d p q := by
  unfold dyadicBox; exact filter_subset _ _

/-- With `K ≥ 1` the first coordinate cannot vanish. -/
theorem fst_ne_zero {d : ℕ} {K L : ℝ} {p q : ℕ} (hK : 1 ≤ K) {kl : ℤ × ℤ}
    (h : kl ∈ dyadicBox d K L p q) : kl.1 ≠ 0 := by
  rw [mem_dyadicBox] at h
  intro h0
  rw [h0] at h
  norm_num at h
  linarith [h.1]

/-- With `L ≥ 1` the second coordinate cannot vanish. -/
theorem snd_ne_zero {d : ℕ} {K L : ℝ} {p q : ℕ} (hL : 1 ≤ L) {kl : ℤ × ℤ}
    (h : kl ∈ dyadicBox d K L p q) : kl.2 ≠ 0 := by
  rw [mem_dyadicBox] at h
  intro h0
  rw [h0] at h
  norm_num at h
  linarith [h.2.2.1]

/-- Transposing the pair swaps the roles of `p, q` and of `K, L`. -/
theorem swap_mem_dyadicBox {d : ℕ} {K L : ℝ} {p q : ℕ} {kl : ℤ × ℤ} :
    kl.swap ∈ dyadicBox d L K q p ↔ kl ∈ dyadicBox d K L p q := by
  rw [mem_dyadicBox, mem_dyadicBox, mem_latticeBox, mem_latticeBox]
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [swap_mem_dualLattice]
  tauto

/-- Transposition is a bijection between the two blocks, so they have the same cardinality. -/
theorem card_dyadicBox_swap (d : ℕ) (K L : ℝ) (p q : ℕ) :
    (dyadicBox d K L p q).card = (dyadicBox d L K q p).card := by
  refine Finset.card_bij' (fun a _ => a.swap) (fun b _ => b.swap) ?_ ?_ ?_ ?_
  · intro a ha; exact swap_mem_dyadicBox.mpr ha
  · intro b hb; exact swap_mem_dyadicBox.mpr hb
  · intro a _; exact Prod.swap_swap a
  · intro b _; exact Prod.swap_swap b

end Paucity
