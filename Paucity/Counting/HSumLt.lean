/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Paucity.Defs.Tn
public import Paucity.Defs.H

/-!
# The two intervals fit inside `[1, n]`

For an obtuse pair `(p, q) ∈ T n`, the interval lengths `h p` and `h q` sum to less than the
modulus `n`.

## Main results

* `h_add_h_lt`: `h p + h q < n` for `(p, q) ∈ T n`.
* `h_lt`: `h p < n` for `(p, q) ∈ T n`.
-/

@[expose] public section

namespace Paucity

/-- For an obtuse pair, the two interval lengths sum to less than the modulus. -/
theorem h_add_h_lt {n : ℕ} {pq : ℕ × ℕ} (hpq : pq ∈ T n) : h pq.1 + h pq.2 < n := by
  rw [mem_T] at hpq
  unfold h
  omega

/-- For an obtuse pair, a single interval length is less than the modulus. -/
theorem h_lt {n : ℕ} {pq : ℕ × ℕ} (hpq : pq ∈ T n) : h pq.1 < n := by
  have h2 := h_add_h_lt hpq
  omega

end Paucity
