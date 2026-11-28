/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Data.ENat.Basic

/-!
# The smoothness exponent `∞` is not zero

Smoothness exponents live in `WithTop ℕ∞` (written `ℕ∞ω`), where `∞` is the image of the top
element `⊤ : ℕ∞` and `ω` is the top element of `WithTop ℕ∞`. Several constructions on smooth
embeddings of class `C^∞`, such as the normal space and its bundle, take a proof of `∞ ≠ 0` as an
explicit argument; this file gives that proof a name.

## Main results

* `ENat.coe_top_ne_zero`: `((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0`, that is, `(∞ : ℕ∞ω) ≠ 0`.
-/

public section

namespace ENat

/-- The smoothness exponent `∞`, the image of `⊤ : ℕ∞` in `WithTop ℕ∞`, is not zero. -/
theorem coe_top_ne_zero : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 :=
  WithTop.coe_ne_zero.2 top_ne_zero

end ENat

end
