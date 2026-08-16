/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Nat.Totient
public import Paucity.Defs.H

/-!
# The expected witness count `M`

`M_n(p,q) = h(p) h(q) φ(n) / n²`, the real number the witness count would equal if the pairs of
residues it counts were equidistributed.

## Main definitions

* `M`: the expected witness count `M_n(p,q)`.

## Main results

* `M_symm`: `M` is symmetric in `p` and `q`.
-/

@[expose] public section

namespace Paucity

/-- `M n p q = h(p) h(q) φ(n) / n²`, the expected witness count $M_n(p,q)$. -/
noncomputable def M (n p q : ℕ) : ℝ :=
  (h p : ℝ) * (h q : ℝ) * (n.totient : ℝ) / (n : ℝ) ^ 2

/-- `M` is symmetric in its two arguments. -/
theorem M_symm (n p q : ℕ) : M n p q = M n q p := by
  unfold M; ring

end Paucity
