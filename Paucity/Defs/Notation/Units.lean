/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Data.Nat.GCD.Basic

/-!
# The units `U n`

`U_n = {a : 1 ≤ a ≤ n, gcd(a,n) = 1}`, the units modulo `n` as a `Finset ℕ`, represented by the
residues in `[1,n]` rather than `[0,n-1]`. The two conventions agree, since `a = n` is coprime to
`n` only when `n = 1`.

## Main definitions

* `U`: the units $U_n$ modulo `n`.

## Main results

* `mem_U`: membership in `U n`, unfolded into its two conditions.
* `one_mem_U`: `1 ∈ U n` for `n ≥ 1`.
* `pos_of_mem_U`, `coprime_of_mem_U`: the two conditions satisfied by an element of `U n`.
-/

@[expose] public section

namespace Paucity

open Finset

/-- `U n`, the units $U_n$ modulo `n`, as residues in `[1,n]`. -/
def U (n : ℕ) : Finset ℕ := (Icc 1 n).filter fun a => Nat.gcd a n = 1

@[simp] theorem mem_U {n a : ℕ} : a ∈ U n ↔ (1 ≤ a ∧ a ≤ n) ∧ Nat.gcd a n = 1 := by
  unfold U; rw [mem_filter, mem_Icc]

theorem one_mem_U {n : ℕ} (hn : 1 ≤ n) : 1 ∈ U n := by
  rw [mem_U]; exact ⟨⟨le_refl 1, hn⟩, by simp⟩

theorem pos_of_mem_U {n a : ℕ} (ha : a ∈ U n) : 1 ≤ a := (mem_U.mp ha).1.1

theorem coprime_of_mem_U {n a : ℕ} (ha : a ∈ U n) : Nat.gcd a n = 1 := (mem_U.mp ha).2

end Paucity
