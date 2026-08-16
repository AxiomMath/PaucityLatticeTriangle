/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Data.Int.GCD
public import Mathlib.RingTheory.Int.Basic
public import Mathlib.Tactic.LinearCombination
public import Paucity.Defs.Hn
public import Paucity.Defs.Lambda

/-!
# Index of the dual lattice

For `0 < d` with `d ∣ n` and `(p, q) ∈ H n`, the dual lattice `dualLattice d p q` has index
exactly `d` in `ℤ²`. Equivalently the homomorphism `dualHom d p q`, sending
`(k, ℓ) ↦ kp + ℓq` into `ZMod d`, is onto, which holds because primitivity of `(p, q)`
modulo `n` gives `gcd(gcd(p, q), d) = 1`.

## Main results

* `exists_intCast_combo_eq_one`: `1` is an integer combination of `p` and `q` modulo `d`
  when `gcd(gcd(p, q), d) = 1`.
* `dualHom_surjective`: `dualHom d p q` is surjective under the same hypothesis.
* `gcd_gcd_eq_one_of_mem_H`: primitivity modulo `n` descends to any divisor of `n`.
* `index_dualLattice`: `(dualLattice d p q).index = d`.
-/

@[expose] public section

namespace Paucity

/-- Bézout in `ZMod d`: if `gcd(p, q, d) = 1` then `1` is an integer combination of
`p` and `q` mod `d`. -/
theorem exists_intCast_combo_eq_one {p q d : ℕ} (h : Nat.gcd (Nat.gcd p q) d = 1) :
    ∃ c₁ c₂ : ℤ, (c₁ : ZMod d) * (p : ZMod d) + (c₂ : ZMod d) * (q : ZMod d) = 1 := by
  obtain ⟨u, v, huv⟩ : IsCoprime ((Nat.gcd p q : ℕ) : ℤ) ((d : ℕ) : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr h
  refine ⟨u * Nat.gcdA p q, u * Nat.gcdB p q, ?_⟩
  have hgcd : ((Nat.gcd p q : ℕ) : ℤ) = (p : ℤ) * Nat.gcdA p q + (q : ℤ) * Nat.gcdB p q :=
    Nat.gcd_eq_gcd_ab p q
  have key : (u * Nat.gcdA p q) * (p : ℤ) + (u * Nat.gcdB p q) * (q : ℤ)
      = 1 - v * (d : ℤ) := by linear_combination huv - u * hgcd
  have hcast := congrArg (fun z : ℤ => (z : ZMod d)) key
  push_cast at hcast
  simpa using hcast

/-- `dualHom d p q` is onto `ZMod d` as soon as `gcd(p, q, d) = 1`. -/
theorem dualHom_surjective {p q d : ℕ} (h : Nat.gcd (Nat.gcd p q) d = 1) :
    Function.Surjective (dualHom d p q) := by
  obtain ⟨c₁, c₂, hc⟩ := exists_intCast_combo_eq_one h
  intro t
  refine ⟨(ZMod.cast t * c₁, ZMod.cast t * c₂), ?_⟩
  simp only [dualHom_apply]
  push_cast
  linear_combination t * hc

/-- Primitivity mod `n` descends to any divisor of `n`. -/
theorem gcd_gcd_eq_one_of_mem_H {n d p q : ℕ} (hdn : d ∣ n) (hpq : (p, q) ∈ H n) :
    Nat.gcd (Nat.gcd p q) d = 1 := by
  have h : Nat.gcd (Nat.gcd p q) n = 1 := (mem_H.mp hpq).2
  exact Nat.eq_one_of_dvd_one (h ▸ Nat.gcd_dvd_gcd_of_dvd_right _ hdn)

/-- The dual lattice has index exactly `d` in `ℤ²`. -/
theorem index_dualLattice {n d p q : ℕ} (hd : 0 < d) (hdn : d ∣ n)
    (hpq : (p, q) ∈ H n) : (dualLattice d p q).index = d := by
  haveI : NeZero d := ⟨hd.ne'⟩
  have hrange : (dualHom d p q).range = ⊤ :=
    AddMonoidHom.range_eq_top_of_surjective _ (dualHom_surjective (gcd_gcd_eq_one_of_mem_H hdn hpq))
  rw [dualLattice, AddSubgroup.index_ker, hrange,
    Nat.card_congr (AddSubgroup.topEquiv (G := ZMod d)).toEquiv, Nat.card_eq_fintype_card,
    ZMod.card]

end Paucity
