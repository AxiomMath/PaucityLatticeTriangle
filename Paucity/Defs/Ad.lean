/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Paucity.Defs.LatticeBox

/-!
# The first axis family

The nonzero dual-lattice points of the box that lie on the vertical axis,
$$\mathcal A_d(p,q) = \{(0,\ell) \in \Lambda_d(p,q) \cap (\mathcal F_d \times
\mathcal F_d) : \ell \ne 0\}.$$

## Main definitions

* `A`: the nonzero dual-lattice points on the vertical axis inside the box.

## Main results

* `mem_A_iff`: `(0, ℓ)` lies in `A d p q` exactly when `ℓ` is a nonzero element of `F d` with
  `d ∣ ℓq`.
* `A_subset_latticeBox`: `A d p q` is contained in `latticeBox d p q`.
-/

@[expose] public section

namespace Paucity

open Finset

/-- `A d p q`, the set $\mathcal A_d(p,q)$: the nonzero dual-lattice points on the vertical axis
inside the box. -/
def A (d p q : ℕ) : Finset (ℤ × ℤ) :=
  (latticeBox d p q).filter fun kl => kl.1 = 0 ∧ kl.2 ≠ 0

@[simp] theorem mem_A {d p q : ℕ} {kl : ℤ × ℤ} :
    kl ∈ A d p q ↔ kl ∈ latticeBox d p q ∧ kl.1 = 0 ∧ kl.2 ≠ 0 := by
  unfold A; exact mem_filter

/-- On the first axis the lattice condition forgets `p`: `(0, ℓ)` lies in `A d p q` exactly when
`ℓ` is a nonzero element of `F d` with `d ∣ ℓq`. -/
theorem mem_A_iff {d p q : ℕ} {l : ℤ} :
    ((0, l) : ℤ × ℤ) ∈ A d p q ↔ l ∈ F d ∧ l ≠ 0 ∧ (d : ℤ) ∣ l * q := by
  rw [mem_A, mem_latticeBox, mem_dualLattice]
  simp only [zero_mul, zero_add]
  constructor
  · rintro ⟨⟨⟨-, hl⟩, hdvd⟩, -, hl0⟩; exact ⟨hl, hl0, hdvd⟩
  · rintro ⟨hl, hl0, hdvd⟩
    obtain ⟨h1, h2⟩ := mem_F.mp hl
    exact ⟨⟨⟨mem_F.mpr ⟨by omega, by omega⟩, hl⟩, hdvd⟩, trivial, hl0⟩

theorem A_subset_latticeBox (d p q : ℕ) : A d p q ⊆ latticeBox d p q :=
  filter_subset _ _

theorem zero_notMem_A (d p q : ℕ) : ((0, 0) : ℤ × ℤ) ∉ A d p q := by
  simp

end Paucity
