/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Tactic.Ring

/-!
# An example

A placeholder that shows the conventions of `AGENTS.md`. Delete it once the library has files
of its own.

## Main definitions

* `Project.double n`: twice the natural number `n`.

## Main results

* `Project.double_add`: `double` is additive.
-/

public section

namespace Project

/-- Twice a natural number. -/
def double (n : ℕ) : ℕ := 2 * n

theorem double_def (n : ℕ) : double n = 2 * n := (rfl)

/-- `double` is additive. -/
theorem double_add (m n : ℕ) : double (m + n) = double m + double n := by
  simp only [double_def]
  ring

end Project

end
