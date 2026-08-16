/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Paucity.Defs.LatticeBox
public import Paucity.Defs.Dn
public import Paucity.Defs.M
public import Paucity.Defs.Q

/-!
# Resonant pairs

`(p,q)` is resonant for `n` when there are `d ∈ D_n` and `(k,ℓ) ∈ Λ_d(p,q) ∩ (F_d × F_d)` with
`kℓ ≠ 0` and `|kℓ| M_n(p,q) ≤ 1000 d Q(n)`.

## Main definitions

* `Resonant`: the pair `(p,q)` is resonant for `n`.

## Main results

* `resonant_of_mem`: introduction rule for `Resonant`, with the off-axis condition split into
  `k ≠ 0` and `ℓ ≠ 0`.
-/

@[expose] public section

namespace Paucity

open Finset

/-- `Resonant n p q`: some `d ∈ D_n` admits an off-axis dual-lattice point of the box whose
coordinate product is small against `M_n(p,q)`. -/
noncomputable def Resonant (n p q : ℕ) : Prop :=
  ∃ d ∈ D n, ∃ kl ∈ latticeBox d p q, kl.1 * kl.2 ≠ 0 ∧
    |((kl.1 * kl.2 : ℤ) : ℝ)| * M n p q ≤ 1000 * (d : ℝ) * Q n

/-- The introduction rule, with the off-axis condition in its split form. -/
theorem resonant_of_mem {n p q d : ℕ} (hd : d ∈ D n) {kl : ℤ × ℤ}
    (hkl : kl ∈ latticeBox d p q) (hk : kl.1 ≠ 0) (hl : kl.2 ≠ 0)
    (hle : |((kl.1 * kl.2 : ℤ) : ℝ)| * M n p q ≤ 1000 * (d : ℝ) * Q n) :
    Resonant n p q :=
  ⟨d, hd, kl, hkl, mul_ne_zero hk hl, hle⟩

noncomputable instance decidableResonant (n p q : ℕ) : Decidable (Resonant n p q) :=
  Classical.propDecidable _

end Paucity
