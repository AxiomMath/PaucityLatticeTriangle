/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Paucity.Defs.Bd
public import Paucity.Defs.Hd
public import Paucity.Defs.Maj

/-!
# The two axis families of the majorant are transposes

For all `n`, `d`, `p` and `q`,

    (1/d) ∑_{(k,0) ∈ B_d(p,q)} ν_{d,H^{(d)}_n(p)}(k) ν_{d,H^{(d)}_n(q)}(0)
  = (1/d) ∑_{(0,ℓ) ∈ A_d(q,p)} ν_{d,H^{(d)}_n(q)}(0) ν_{d,H^{(d)}_n(p)}(ℓ).

## Main results

* `sum_nu_B_eq_sum_nu_A`: the `ν`-weighted contribution of the horizontal axis family `B_d(p,q)`
  equals that of the vertical axis family `A_d(q,p)` of the transposed pair.
-/

@[expose] public section

namespace Paucity

open Finset

/-- The `ν`-weighted contribution of the horizontal axis family `B_d(p,q)` equals the `ν`-weighted
contribution of the vertical axis family `A_d(q,p)` of the transposed pair,

    (1/d) ∑_{(k,0) ∈ B_d(p,q)} ν_{d,H^{(d)}_n(p)}(k) ν_{d,H^{(d)}_n(q)}(0)
  = (1/d) ∑_{(0,ℓ) ∈ A_d(q,p)} ν_{d,H^{(d)}_n(q)}(0) ν_{d,H^{(d)}_n(p)}(ℓ).
-/
theorem sum_nu_B_eq_sum_nu_A (n d p q : ℕ) :
    (1 / (d : ℝ)) * ∑ kl ∈ B d p q, nu d (Hd n d p) kl.1 * nu d (Hd n d q) kl.2 =
      (1 / (d : ℝ)) * ∑ kl ∈ A d q p, nu d (Hd n d q) kl.1 * nu d (Hd n d p) kl.2 := by
  congr 1
  exact sum_equiv (Equiv.prodComm ℤ ℤ) (fun _ => mem_B_iff_swap_mem_A) fun _ _ => mul_comm _ _

end Paucity
