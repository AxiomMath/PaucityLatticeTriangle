/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Data.Finset.Prod
public import Mathlib.Order.Interval.Finset.Nat

/-!
# The obtuse index set `T n`

$\mathcal T_n = \{(p,q) : p,q \ge 1,\ 2(p+q) < n\}$, as a `Finset (ℕ × ℕ)`. It is realized as a
filter of the box $[1,n] \times [1,n]$, which encloses it since $2(p+q) < n$ and $q \ge 1$ already
force $p < n$.

## Main definitions

* `T`: the obtuse index set $\mathcal T_n$.

## Main results

* `mem_T`: membership in `T n`, stated without the enclosing box.
* `swap_mem_T`: `T n` is invariant under swapping the two coordinates.
* `T_eq_empty_of_lt_five`: `T n` is empty for `n < 5`.
-/

@[expose] public section

namespace Paucity

open Finset

/-- `T n`, the obtuse index set $\mathcal T_n$: pairs of positive integers with
$2(p+q) < n$. -/
def T (n : ℕ) : Finset (ℕ × ℕ) :=
  (Icc 1 n ×ˢ Icc 1 n).filter fun pq => 2 * (pq.1 + pq.2) < n

/-- Membership in `T n`, stated without the enclosing box that `T` is built from. -/
@[simp] theorem mem_T {n : ℕ} {pq : ℕ × ℕ} :
    pq ∈ T n ↔ 1 ≤ pq.1 ∧ 1 ≤ pq.2 ∧ 2 * (pq.1 + pq.2) < n := by
  unfold T
  simp only [mem_filter, mem_product, mem_Icc]
  constructor
  · rintro ⟨⟨⟨h1, _⟩, ⟨h2, _⟩⟩, h3⟩; exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨⟨h1, ?_⟩, ⟨h2, ?_⟩⟩, h3⟩ <;> omega

/-- `T n` is invariant under swapping the two coordinates. -/
theorem swap_mem_T {n : ℕ} {pq : ℕ × ℕ} (hpq : pq ∈ T n) : pq.swap ∈ T n := by
  simp only [mem_T, Prod.fst_swap, Prod.snd_swap] at *
  omega

/-- `T n` is empty below `5`: `p, q ≥ 1` already forces `2(p+q) ≥ 4`. -/
theorem T_eq_empty_of_lt_five {n : ℕ} (hn : n < 5) : T n = ∅ := by
  apply eq_empty_of_forall_notMem
  intro pq hpq
  rw [mem_T] at hpq
  omega

end Paucity
