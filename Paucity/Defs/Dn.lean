/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.NumberTheory.Divisors
public import Mathlib.Data.Nat.Squarefree

/-!
# Divisors with squarefree cofactor

For `n : ℕ`, the divisors `d` of `n` whose cofactor `n / d` is squarefree. These are exactly the
divisors at which the Möbius coefficient `μ(n / d)` is nonzero.

## Main definitions

* `D`: the divisors of `n` with squarefree cofactor.
-/

@[expose] public section

namespace Paucity

open Finset

/-- `D n`, the set $\mathcal{D}_n$: the divisors of `n` with squarefree cofactor. -/
def D (n : ℕ) : Finset ℕ := n.divisors.filter fun d => Squarefree (n / d)

@[simp] theorem mem_D {n d : ℕ} : d ∈ D n ↔ d ∈ n.divisors ∧ Squarefree (n / d) := by
  unfold D; exact mem_filter

theorem D_subset_divisors (n : ℕ) : D n ⊆ n.divisors := filter_subset _ _

theorem dvd_of_mem_D {n d : ℕ} (hd : d ∈ D n) : d ∣ n :=
  (Nat.mem_divisors.mp (mem_D.mp hd).1).1

end Paucity
