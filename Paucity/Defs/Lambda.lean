/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Push

/-!
# The dual lattice

The subgroup $\Lambda_d(p,q) = \{(k,\ell) \in \mathbb Z^2 : kp + \ell q \equiv 0 \pmod d\}$ of
`ℤ × ℤ`, realized as the kernel of the evaluation homomorphism `(k, ℓ) ↦ kp + ℓq` into `ZMod d`.

## Main definitions

* `dualHom`: the homomorphism `(k, ℓ) ↦ kp + ℓq` from `ℤ × ℤ` to `ZMod d`.
* `dualLattice`: the kernel of `dualHom d p q`.

## Main results

* `mem_dualLattice`: `(k, ℓ)` lies in `dualLattice d p q` exactly when `(d : ℤ) ∣ kp + ℓq`.
* `swap_mem_dualLattice`: transposing a pair exchanges the roles of `p` and `q`.
-/

@[expose] public section

namespace Paucity

/-- The evaluation hom `(k, ℓ) ↦ kp + ℓq` from `ℤ²` to `ZMod d`, with kernel the dual lattice. -/
def dualHom (d p q : ℕ) : ℤ × ℤ →+ ZMod d where
  toFun kl := (kl.1 : ZMod d) * (p : ZMod d) + (kl.2 : ZMod d) * (q : ZMod d)
  map_zero' := by simp
  map_add' := by
    intro a b
    simp only [Prod.fst_add, Prod.snd_add, Int.cast_add]
    ring

@[simp] theorem dualHom_apply (d p q : ℕ) (kl : ℤ × ℤ) :
    dualHom d p q kl = (kl.1 : ZMod d) * (p : ZMod d) + (kl.2 : ZMod d) * (q : ZMod d) :=
  rfl

/-- `dualLattice d p q`, the subgroup $\Lambda_d(p,q)$: the characters of `(ℤ/dℤ)²` trivial on
`{([bp]_d, [bq]_d)}`. -/
def dualLattice (d p q : ℕ) : AddSubgroup (ℤ × ℤ) := (dualHom d p q).ker

/-- Membership in the dual lattice as a divisibility in `ℤ`, with no `ZMod` in sight. -/
theorem mem_dualLattice {d p q : ℕ} {kl : ℤ × ℤ} :
    kl ∈ dualLattice d p q ↔ (d : ℤ) ∣ kl.1 * p + kl.2 * q := by
  unfold dualLattice
  rw [AddMonoidHom.mem_ker, dualHom_apply]
  rw [show ((kl.1 : ZMod d) * (p : ZMod d) + (kl.2 : ZMod d) * (q : ZMod d))
      = ((kl.1 * (p : ℤ) + kl.2 * (q : ℤ) : ℤ) : ZMod d) by
        simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast]]
  exact ZMod.intCast_zmod_eq_zero_iff_dvd _ _

instance decidableMemDualLattice (d p q : ℕ) (kl : ℤ × ℤ) :
    Decidable (kl ∈ dualLattice d p q) :=
  decidable_of_iff _ mem_dualLattice.symm

/-- Transposing the pair swaps the roles of `p` and `q`. -/
theorem swap_mem_dualLattice {d p q : ℕ} {kl : ℤ × ℤ} :
    kl.swap ∈ dualLattice d q p ↔ kl ∈ dualLattice d p q := by
  rw [mem_dualLattice, mem_dualLattice, Prod.fst_swap, Prod.snd_swap, add_comm]

end Paucity
