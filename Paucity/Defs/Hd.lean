/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Paucity.Defs.H

/-!
# The scaled interval length

The `ℕ`-valued quantity $H^{(d)}_n(t) = \lfloor h(t) d / n \rfloor$, where the floor is ordinary
`Nat` division.

## Main definitions

* `Hd`: the quantity `h t * d / n`.
-/

@[expose] public section

namespace Paucity

/-- `Hd n d t = ⌊h(t) d / n⌋`, the quantity $H^{(d)}_n(t)$. -/
def Hd (n d t : ℕ) : ℕ := h t * d / n

end Paucity
