/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.LinearAlgebra.Complex.Finrank

/-!
# The real dimension of a complex vector space of complex dimension `r + 1`

A complex vector space of complex dimension `r + 1` has real dimension `2 r + 2`. Index types
of real orientations and degrees of cohomology classes of such spaces, and of complex vector
bundles and manifolds modelled on them, are often written `Fin (2 * r + 1 + 1)` and `2 * r + 2`,
so this file states the dimension in the form `2 * r + 1 + 1`:

* `finrank_real_of_finrank_complex_eq_add_one`: from `finrank ℂ V = r + 1`, for any real
  structure on `V` compatible with the complex one, `finrank ℝ V = 2 * r + 1 + 1`.

It is Tau Ceti's `TauCeti.finrank_real_eq_two_mul_finrank_complex` in complex dimension `r + 1`.
-/

public section

open Module

/-- A complex vector space of complex dimension `r + 1`, with a compatible real structure, has
real dimension `2 r + 2`, written `2 * r + 1 + 1`. -/
theorem finrank_real_of_finrank_complex_eq_add_one {V : Type*} [AddCommGroup V] [Module ℝ V]
    [Module ℂ V] [IsScalarTower ℝ ℂ V] {r : ℕ} (hV : finrank ℂ V = r + 1) :
    finrank ℝ V = 2 * r + 1 + 1 := by
  rw [TauCeti.finrank_real_eq_two_mul_finrank_complex, hV]; ring

end
