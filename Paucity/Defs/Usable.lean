/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Data.ZMod.Basic
public import Paucity.Defs.Notation.Units

/-!
# Usable units

A unit `a ∈ U n` is *usable* when `2a ≢ 2 (mod n)`.

## Main definitions

* `Usable`: the usability condition on a residue `a` modulo `n`.
-/

@[expose] public section

namespace Paucity

/-- `Usable n a`: the usability condition `2a ≢ 2 (mod n)`, stated in `ZMod n`. -/
def Usable (n a : ℕ) : Prop := ((2 * a : ℕ) : ZMod n) ≠ ((2 : ℕ) : ZMod n)

instance (n a : ℕ) : Decidable (Usable n a) := by
  unfold Usable; infer_instance

end Paucity
