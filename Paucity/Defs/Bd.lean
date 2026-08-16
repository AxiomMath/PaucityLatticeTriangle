/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Paucity.Defs.Ad

/-!
# The second axis family

The nonzero dual-lattice points of the box that lie on the horizontal axis,
$$\mathcal B_d(p,q) = \{(k,0) \in \Lambda_d(p,q) \cap (\mathcal F_d \times
\mathcal F_d) : k \ne 0\}.$$
It is the image of the first axis family under transposition of the pair.

## Main definitions

* `B`: the nonzero dual-lattice points on the horizontal axis inside the box.

## Main results

* `mem_B_iff`: `(k, 0)` lies in `B d p q` exactly when `k` is a nonzero element of `F d` with
  `d ∣ kp`.
* `mem_B_iff_swap_mem_A`: a pair lies in `B d p q` exactly when its transpose lies in `A d q p`.
* `card_B_eq_card_A`: `B d p q` and `A d q p` have the same cardinality.
-/

@[expose] public section

namespace Paucity

open Finset

/-- `B d p q`, the set $\mathcal B_d(p,q)$: the nonzero dual-lattice points on the horizontal axis
inside the box. -/
def B (d p q : ℕ) : Finset (ℤ × ℤ) :=
  (latticeBox d p q).filter fun kl => kl.2 = 0 ∧ kl.1 ≠ 0

@[simp] theorem mem_B {d p q : ℕ} {kl : ℤ × ℤ} :
    kl ∈ B d p q ↔ kl ∈ latticeBox d p q ∧ kl.2 = 0 ∧ kl.1 ≠ 0 := by
  unfold B; exact mem_filter

/-- On the second axis the lattice condition forgets `q`: `(k, 0)` lies in `B d p q` exactly when
`k` is a nonzero element of `F d` with `d ∣ kp`. -/
theorem mem_B_iff {d p q : ℕ} {k : ℤ} :
    ((k, 0) : ℤ × ℤ) ∈ B d p q ↔ k ∈ F d ∧ k ≠ 0 ∧ (d : ℤ) ∣ k * p := by
  rw [mem_B, mem_latticeBox, mem_dualLattice]
  simp only [zero_mul, add_zero]
  constructor
  · rintro ⟨⟨⟨hk, -⟩, hdvd⟩, -, hk0⟩; exact ⟨hk, hk0, hdvd⟩
  · rintro ⟨hk, hk0, hdvd⟩
    obtain ⟨h1, h2⟩ := mem_F.mp hk
    exact ⟨⟨⟨hk, mem_F.mpr ⟨by omega, by omega⟩⟩, hdvd⟩, trivial, hk0⟩

/-- The second axis family is the first one with the pair transposed. -/
theorem mem_B_iff_swap_mem_A {d p q : ℕ} {kl : ℤ × ℤ} :
    kl ∈ B d p q ↔ kl.swap ∈ A d q p := by
  rw [mem_B, mem_A, mem_latticeBox, mem_latticeBox, Prod.fst_swap, Prod.snd_swap,
    swap_mem_dualLattice]
  tauto

theorem card_B_eq_card_A (d p q : ℕ) : (B d p q).card = (A d q p).card := by
  refine card_nbij' Prod.swap Prod.swap (fun kl hkl => ?_) (fun kl hkl => ?_)
    (fun _ _ => Prod.swap_swap _) (fun _ _ => Prod.swap_swap _)
  · exact mem_B_iff_swap_mem_A.mp hkl
  · exact mem_B_iff_swap_mem_A.mpr (by rwa [Prod.swap_swap])

end Paucity
