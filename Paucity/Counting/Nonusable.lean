/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Data.Nat.ModEq
public import Paucity.Defs.Usable

/-!
# Few unusable units

An unusable unit modulo `n` is `1` or `1 + n / 2`, so at most two units of `U n` are unusable,
for every `n`.

## Main definitions

* `unusable`: the units of `U n` that are not `Usable n`.

## Main results

* `eq_one_or_eq_one_add_half_of_mem_unusable`: an unusable unit is `1` or `1 + n / 2`.
* `card_unusable_le_two`: `#(unusable n) ≤ 2` for every `n`.
-/

@[expose] public section

namespace Paucity

open Finset

/-- The unusable units of `U n`. -/
def unusable (n : ℕ) : Finset ℕ := (U n).filter fun a => ¬ Usable n a

@[simp] theorem mem_unusable {n a : ℕ} :
    a ∈ unusable n ↔ a ∈ U n ∧ ¬ Usable n a := mem_filter

/-- An unusable unit is `1` or `1 + n/2`. -/
theorem eq_one_or_eq_one_add_half_of_mem_unusable {n a : ℕ}
    (ha : a ∈ unusable n) : a = 1 ∨ a = 1 + n / 2 := by
  rw [mem_unusable, mem_U] at ha
  obtain ⟨⟨⟨ha1, ha2⟩, -⟩, hu⟩ := ha
  have hmod : 2 * a ≡ 2 [MOD n] :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mp (not_not.mp hu)
  obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd' (by omega)).mp hmod.symm
  have hk2 : k < 2 := Nat.lt_of_mul_lt_mul_left (show n * k < n * 2 by omega)
  rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl <;> omega

/-- At most two units of `U n` are unusable. -/
theorem card_unusable_le_two (n : ℕ) : (unusable n).card ≤ 2 :=
  calc (unusable n).card
      ≤ ({1, 1 + n / 2} : Finset ℕ).card :=
        card_le_card fun a ha => by
          simpa using eq_one_or_eq_one_add_half_of_mem_unusable ha
    _ ≤ 2 := (card_insert_le _ _).trans (by simp)

end Paucity
