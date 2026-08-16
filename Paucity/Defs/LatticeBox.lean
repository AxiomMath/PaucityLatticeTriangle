/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Paucity.Defs.Fd
public import Paucity.Defs.Lambda

/-!
# The lattice box `Λ_d(p,q) ∩ (F_d × F_d)`

The points of the dual lattice `Λ_d(p,q)` both of whose coordinates are least-absolute-value
residues modulo `d`, as a `Finset (ℤ × ℤ)`. Finiteness comes from the box `F d`, not from the
lattice.

## Main definitions

* `latticeBox`: the intersection `Λ_d(p,q) ∩ (F_d × F_d)`.

## Main results

* `mem_latticeBox`: membership in the box, unfolded into its two conditions.
* `zero_mem_latticeBox`: the origin lies in the box whenever `d ≥ 1`.
-/

@[expose] public section

namespace Paucity

open Finset

/-- `latticeBox d p q = Λ_d(p,q) ∩ (F_d × F_d)`: the dual-lattice points whose
coordinates are least-absolute-value residues. -/
def latticeBox (d p q : ℕ) : Finset (ℤ × ℤ) :=
  ((F d) ×ˢ (F d)).filter fun kl => kl ∈ dualLattice d p q

@[simp] theorem mem_latticeBox {d p q : ℕ} {kl : ℤ × ℤ} :
    kl ∈ latticeBox d p q ↔
      (kl.1 ∈ F d ∧ kl.2 ∈ F d) ∧ kl ∈ dualLattice d p q := by
  unfold latticeBox
  rw [mem_filter, mem_product]

/-- The origin lies in the box for `d ≥ 1`. -/
theorem zero_mem_latticeBox {d p q : ℕ} (hd : 0 < d) :
    ((0, 0) : ℤ × ℤ) ∈ latticeBox d p q := by
  rw [mem_latticeBox]
  refine ⟨⟨?_, ?_⟩, ?_⟩ <;> simp [mem_F, dualLattice] <;> omega

end Paucity
