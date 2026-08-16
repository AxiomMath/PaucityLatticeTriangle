/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Paucity.Defs.Tn

/-!
# The primitive obtuse region

The pairs of the obtuse region `T n` that are primitive for `n`,
$\mathcal H_n = \{(p,q) \in \mathcal T_n : \gcd(p,q,n) = 1\}$, with the ternary gcd written as
`Nat.gcd (Nat.gcd p q) n`.

## Main definitions

* `H`: the primitive pairs of `T n`.

## Main results

* `H_subset_T`: `H n` is contained in `T n`.
* `swap_mem_H`: `H n` is invariant under swapping the two coordinates.
* `H_nonempty`: `H n` is nonempty for `5 ≤ n`.
-/

@[expose] public section

namespace Paucity

open Finset

/-- `H n`, the set $\mathcal H_n$: the pairs of `T n` that are primitive for `n`. -/
def H (n : ℕ) : Finset (ℕ × ℕ) :=
  (T n).filter fun pq => Nat.gcd (Nat.gcd pq.1 pq.2) n = 1

@[simp] theorem mem_H {n : ℕ} {pq : ℕ × ℕ} :
    pq ∈ H n ↔ pq ∈ T n ∧ Nat.gcd (Nat.gcd pq.1 pq.2) n = 1 := by
  unfold H; exact mem_filter

theorem H_subset_T (n : ℕ) : H n ⊆ T n := filter_subset _ _

/-- `H n` is invariant under swapping the two coordinates. -/
theorem swap_mem_H {n : ℕ} {pq : ℕ × ℕ} (hpq : pq ∈ H n) : pq.swap ∈ H n := by
  rw [mem_H] at hpq ⊢
  refine ⟨swap_mem_T hpq.1, ?_⟩
  rw [Prod.fst_swap, Prod.snd_swap, Nat.gcd_comm pq.2 pq.1]
  exact hpq.2

theorem one_one_mem_H {n : ℕ} (hn : 5 ≤ n) : ((1, 1) : ℕ × ℕ) ∈ H n := by
  rw [mem_H, mem_T]
  refine ⟨⟨le_refl 1, le_refl 1, by omega⟩, ?_⟩
  simp

theorem H_nonempty {n : ℕ} (hn : 5 ≤ n) : (H n).Nonempty :=
  ⟨(1, 1), one_one_mem_H hn⟩

end Paucity
