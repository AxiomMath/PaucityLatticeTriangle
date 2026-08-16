/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Paucity.Defs.Ln
public import Paucity.Defs.S
public import Paucity.Defs.Usable

/-!
# The Larsen–Norton–Zykoski criterion

The one input this development takes from the literature: Larsen–Norton–Zykoski,
Proposition 2.1, itself a consequence of Mirzakhani–Wright. It is stated here as a
`Prop`-valued definition, carrying the lattice predicate as a parameter, and is assumed as
an explicit hypothesis wherever it is used rather than asserted as an axiom.

## Main definitions

* `ResLt`: the residue condition `[at]_n < [2t]_n`.
* `LNZ`: for `n ≥ 5` and `(p, q) ∈ H n`, if some usable `a ∈ U n` satisfies at least two of
  `ResLt n a p`, `ResLt n a q` and `ResLt n a (n - p - q)`, then `(p, q) ∉ L P n`.

## Main results

* `lnz_satisfiable`: some lattice predicate satisfies `LNZ`.
* `lnz_not_universal`: not every lattice predicate satisfies `LNZ`.
* `LNZ.first_two`: `LNZ` specialized to the first two of its three residue conditions.
-/

@[expose] public section

namespace Paucity

/-- `ResLt n a t`: the residue condition `[at]_n < [2t]_n`. -/
def ResLt (n a t : ℕ) : Prop := res ((a : ℤ) * t) n < res (2 * (t : ℤ)) n

instance (n a t : ℕ) : Decidable (ResLt n a t) := by unfold ResLt; infer_instance

/-- The Larsen–Norton–Zykoski criterion (Larsen–Norton–Zykoski, Proposition 2.1) for the
lattice predicate `P`: for `n ≥ 5` and `(p, q) ∈ H n`, if some usable `a ∈ U n` satisfies
at least two of `[ap]_n < [2p]_n`, `[aq]_n < [2q]_n` and `[ar]_n < [2r]_n`, where
`r = n - p - q`, then `(p, q) ∉ L P n`.

This is assumed, not proved: it is the one input taken from the literature, and it is
carried as an explicit hypothesis by every result that rests on it. -/
def LNZ (P : LatPred) : Prop :=
  ∀ n : ℕ, 5 ≤ n → ∀ p q : ℕ, (p, q) ∈ H n →
    (∃ a ∈ U n, Usable n a ∧
      ((ResLt n a p ∧ ResLt n a q) ∨
       (ResLt n a p ∧ ResLt n a (n - p - q)) ∨
       (ResLt n a q ∧ ResLt n a (n - p - q)))) →
    (p, q) ∉ L P n

/-- `LNZ` is satisfiable: the class of lattice predicates satisfying it is nonempty. -/
theorem lnz_satisfiable : ∃ P : LatPred, LNZ P :=
  ⟨⟨fun _ _ _ => False⟩, fun _ _ _ _ _ _ hmem => (mem_L.mp hmem).2⟩

/-- `LNZ` is not satisfied by every lattice predicate: it fails for the constantly true
predicate, for which `L P n = H n`, as witnessed by `(2, 2) ∈ H 11`. -/
theorem lnz_not_universal : ¬ ∀ P : LatPred, LNZ P := by
  intro h
  have h2 : ((2, 2) : ℕ × ℕ) ∈ H 11 := by decide
  exact h ⟨fun _ _ _ => True⟩ 11 (by omega) 2 2 h2 (by decide) (mem_L.mpr ⟨h2, trivial⟩)

/-- `LNZ` at the first two of its three residue conditions: if `a ∈ U n` is usable and
satisfies `ResLt n a p` and `ResLt n a q`, then `(p, q) ∉ L P n`. -/
theorem LNZ.first_two {P : LatPred} (h : LNZ P) {n : ℕ} (hn : 5 ≤ n) {p q : ℕ}
    (hpq : (p, q) ∈ H n) {a : ℕ} (ha : a ∈ U n) (hu : Usable n a)
    (hp : ResLt n a p) (hq : ResLt n a q) :
    (p, q) ∉ L P n :=
  h n hn p q hpq ⟨a, ha, hu, Or.inl ⟨hp, hq⟩⟩

end Paucity
