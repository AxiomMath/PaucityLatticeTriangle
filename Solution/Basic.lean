/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Paucity.Main.LatticeTriangles

/-! # Satisfying the formal challenge -/

@[expose] public section

namespace Paucity.Challenge

/-- **`thm_main` — the main theorem.** Theorem 1.1 of *On the paucity of lattice triangles*,
given Larsen–Norton–Zykoski: for every `ε > 0` there is `c > 0` with
`#(L P n) / #(H n) ≤ c / n ^ (1 - ε)` for every `n ≥ 5`, where `c` is chosen before `n`. -/
theorem thm_main (P : LatPred) (hLNZ : LNZ P) :
    ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 5 ≤ n →
      ((L P n).card : ℝ) / ((H n).card : ℝ) ≤ c / (n : ℝ) ^ (1 - ε) :=
  fun _ hε => card_L_div_card_H_le hLNZ hε

end Paucity.Challenge
