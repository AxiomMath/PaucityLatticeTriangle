/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Paucity.Defs.LatticeBox
public import Paucity.Defs.Hd
public import Paucity.Defs.Maj

/-!
# The majorant sum `W`

`W_d(n,p,q) = (1/d) ∑_{(k,ℓ) ∈ Λ_d(p,q) ∩ (F_d × F_d), (k,ℓ) ≠ (0,0)}
  ν_{d,H^{(d)}_n(p)}(k) ν_{d,H^{(d)}_n(q)}(ℓ)`, a sum of nonnegative reals over the lattice box
with the origin removed.

## Main definitions

* `W`: the majorant sum `W_d(n,p,q)`.

## Main results

* `W_nonneg`: `W` is nonnegative.
-/

@[expose] public section

namespace Paucity

open Finset

/-- `W n d p q`, the majorant sum `W_d(n,p,q)`: the sum over the punctured lattice box, weighting
each coordinate by `nu`. -/
noncomputable def W (n d p q : ℕ) : ℝ :=
  (1 / (d : ℝ)) * ∑ kl ∈ (latticeBox d p q).filter fun kl => kl ≠ (0, 0),
    nu d (Hd n d p) kl.1 * nu d (Hd n d q) kl.2

theorem W_nonneg (n d p q : ℕ) : 0 ≤ W n d p q := by
  unfold W
  have hd : (0 : ℝ) ≤ 1 / (d : ℝ) := by positivity
  refine mul_nonneg hd (sum_nonneg fun kl _ => ?_)
  exact mul_nonneg (nu_nonneg _ _ _) (nu_nonneg _ _ _)

end Paucity
