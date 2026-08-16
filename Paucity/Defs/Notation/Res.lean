/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Data.Int.GCD

/-!
# Least nonnegative residue `res`

`[x]_d`, the least nonnegative residue of `x : ℤ` modulo `d : ℕ`, realized as `(x % d).toNat`.

## Main definitions

* `res`: the least nonnegative residue `[x]_d`.

## Main results

* `res_natCast`: on naturals `res` agrees with `%`.
* `res_lt`: `[x]_d < d` for `d > 0`.
* `res_eq_zero_iff`: `[x]_d = 0` if and only if `d ∣ x`.
-/

@[expose] public section

namespace Paucity

/-- `res x d = [x]_d`, the least nonnegative residue. -/
def res (x : ℤ) (d : ℕ) : ℕ := (x % (d : ℤ)).toNat

@[simp] theorem res_natCast (n d : ℕ) : res (n : ℤ) d = n % d := by
  unfold res
  rw [← Int.natCast_mod, Int.toNat_natCast]

theorem res_lt {x : ℤ} {d : ℕ} (hd : 0 < d) : res x d < d := by
  unfold res
  have h1 : x % (d : ℤ) < (d : ℤ) := Int.emod_lt_of_pos x (by exact_mod_cast hd)
  have h2 : 0 ≤ x % (d : ℤ) := Int.emod_nonneg x (by exact_mod_cast hd.ne')
  omega

theorem res_eq_zero_iff {x : ℤ} {d : ℕ} (hd : 0 < d) : res x d = 0 ↔ (d : ℤ) ∣ x := by
  unfold res
  have h2 : 0 ≤ x % (d : ℤ) := Int.emod_nonneg x (by exact_mod_cast hd.ne')
  rw [Int.toNat_eq_zero]
  constructor
  · intro h; exact Int.dvd_of_emod_eq_zero (by omega)
  · intro h
    have := Int.emod_eq_zero_of_dvd h
    omega

end Paucity
