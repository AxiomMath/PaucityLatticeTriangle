/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # The formal challenge file, written by humans

This is a human-written file certifying the formal statements that this repository proves.

-/

@[expose] public section

namespace Paucity

open Finset

/-- The least *nonnegative* residue `[x]_d` of `x` modulo `d`, as a natural number. Not
symmetric, and `res x 0 = x.toNat` by the convention `x % 0 = x`. -/
def res (x : ℤ) (d : ℕ) : ℕ := (x % (d : ℤ)).toNat

/-- The units mod `n`, as representatives in `[1, n]`, inclusive at both ends. -/
def U (n : ℕ) : Finset ℕ := (Icc 1 n).filter fun a => Nat.gcd a n = 1

/-- `a` is *usable* for `n`: `2a ≢ 2 (mod n)`. -/
def Usable (n a : ℕ) : Prop := ((2 * a : ℕ) : ZMod n) ≠ ((2 : ℕ) : ZMod n)

/-- The obtuse-angle triples with denominator `n`, indexed by their first two angle
numerators. The inequality is **strict**, which is obtuseness: the third angle
`(n - p - q)π/n` exceeds `π/2`, and `≤` would admit the right-angled case. -/
def T (n : ℕ) : Finset (ℕ × ℕ) :=
  (Icc 1 n ×ˢ Icc 1 n).filter fun pq => 2 * (pq.1 + pq.2) < n

/-- The *primitive* pairs of `T n`: the gcd is taken of all three of `p`, `q` and `n`, not
of `p` and `q` alone. -/
def H (n : ℕ) : Finset (ℕ × ℕ) :=
  (T n).filter fun pq => Nat.gcd (Nat.gcd pq.1 pq.2) n = 1

/-- The data of a *lattice predicate*: `Lat n p q` says the triangle with angles
`(pπ/n, qπ/n, (n-p-q)π/n)` unfolds to a translation surface whose Veech group is a lattice
in `SL₂(ℝ)`. -/
structure LatPred where
  /-- The predicate itself, carried as a parameter and never unfolded. -/
  Lat : ℕ → ℕ → ℕ → Prop

open scoped Classical in
/-- The *lattice pairs*: the pairs of `H n` whose triangle has lattice Veech group. -/
noncomputable def L (P : LatPred) (n : ℕ) : Finset (ℕ × ℕ) :=
  (H n).filter fun pq => P.Lat n pq.1 pq.2

/-- The residue comparison `[at]_n < [2t]_n`. -/
def ResLt (n a t : ℕ) : Prop := res ((a : ℤ) * t) n < res (2 * (t : ℤ)) n

/-! ## Larsen–Norton–Zykoski's Proposition 2.1 as hypothesis

A. Larsen, C. Norton and B. Zykoski, *Strongly obtuse rational lattice triangles*,
Trans. Amer. Math. Soc. **374** (2021), no. 10, 7119–7142, **Proposition 2.1**: the
Mirzakhani–Wright rank obstruction recast as a condition in modular arithmetic. It is the one
external input this statement assumes. -/

/-- **Larsen–Norton–Zykoski, Proposition 2.1.** If some usable unit `a` satisfies at least
two of the three residue inequalities at `p`, `q` and `r = n - p - q`, then `(p, q)` is not a
lattice pair. The subtraction is truncated but exact here, since `2(p+q) < n` on `T n`. -/
def LNZ (P : LatPred) : Prop :=
  ∀ n : ℕ, 5 ≤ n → ∀ p q : ℕ, (p, q) ∈ H n →
    (∃ a ∈ U n, Usable n a ∧
      ((ResLt n a p ∧ ResLt n a q) ∨
       (ResLt n a p ∧ ResLt n a (n - p - q)) ∨
       (ResLt n a q ∧ ResLt n a (n - p - q)))) →
    (p, q) ∉ L P n

end Paucity

namespace Paucity.Challenge

/-- **`thm_main` — the main theorem.** Theorem 1.1 of *On the paucity of lattice triangles*,
given Larsen–Norton–Zykoski: for every `ε > 0` there is `c > 0` with
`#(L P n) / #(H n) ≤ c / n ^ (1 - ε)` for every `n ≥ 5`, where `c` is chosen before `n`. -/
theorem thm_main (P : LatPred) (hLNZ : LNZ P) :
    ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 5 ≤ n →
      ((L P n).card : ℝ) / ((H n).card : ℝ) ≤ c / (n : ℝ) ^ (1 - ε) := by
  sorry

end Paucity.Challenge
