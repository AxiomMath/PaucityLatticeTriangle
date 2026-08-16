/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Paucity.Counting.Nonusable
public import Paucity.External.Lnz

/-!
# `L_n` has few witnesses

Under the hypothesis `LNZ P`, for `n ≥ 5` every pair of `L P n` lies in `H n` and has at most two
witnesses.

## Main definitions

* `witnesses`: the units of `U n` satisfying both residue inequalities `ResLt n a p` and
  `ResLt n a q`.

## Main results

* `S_eq_card_witnesses`: `S n p q` is the number of witnesses.
* `exists_usable_witness`: three witnesses force a usable one.
* `L_subset_witnesses_le_two`: under `LNZ P` and for `n ≥ 5`,
  `L P n ⊆ {(p, q) ∈ H n : S n p q ≤ 2}`.
-/

@[expose] public section

namespace Paucity

open Finset

/-- The units of `U n` satisfying both residue inequalities `ResLt n a p` and `ResLt n a q`. -/
def witnesses (n p q : ℕ) : Finset ℕ :=
  (U n).filter fun a => ResLt n a p ∧ ResLt n a q

/-- `S n p q` is the number of witnesses. -/
theorem S_eq_card_witnesses (n p q : ℕ) : S n p q = (witnesses n p q).card := rfl

/-- Three witnesses force a usable one. -/
theorem exists_usable_witness {n p q : ℕ} (h : 3 ≤ (witnesses n p q).card) :
    ∃ a ∈ witnesses n p q, Usable n a := by
  by_contra hno
  have hsub : witnesses n p q ⊆ unusable n := fun a ha =>
    mem_unusable.mpr ⟨(mem_filter.mp ha).1, fun hu => hno ⟨a, ha, hu⟩⟩
  have := (card_le_card hsub).trans (card_unusable_le_two n)
  omega

/-- Under `LNZ P` and for `n ≥ 5`, every pair of `L P n` lies in `H n` and has at most two
witnesses. -/
theorem L_subset_witnesses_le_two {P : LatPred} (hLNZ : LNZ P) {n : ℕ} (hn : 5 ≤ n) :
    L P n ⊆ (H n).filter fun pq => S n pq.1 pq.2 ≤ 2 := by
  intro ⟨p, q⟩ hpqL
  obtain ⟨hH, -⟩ := mem_L.mp hpqL
  refine mem_filter.mpr ⟨hH, ?_⟩
  change S n p q ≤ 2
  by_contra hgt
  rw [S_eq_card_witnesses] at hgt
  obtain ⟨a, ha, hu⟩ := exists_usable_witness (n := n) (p := p) (q := q) (by omega)
  obtain ⟨haU, hp, hq⟩ := mem_filter.mp ha
  exact hLNZ.first_two hn hH haU hu hp hq hpqL

end Paucity
