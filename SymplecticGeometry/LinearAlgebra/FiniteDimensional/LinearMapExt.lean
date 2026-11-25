/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Linear maps out of a space of dimension one

A nonzero vector `v` of a vector space `V` of dimension one spans `V`
(`finrank_eq_one_iff_of_ne_zero`), so a linear map out of `V` is determined by its value at `v`
(`LinearMap.ext_of_finrank_eq_one`).
-/

public section

open Module

namespace LinearMap

/-- Two linear maps out of a vector space of dimension one that agree at a nonzero vector are
equal. -/
theorem ext_of_finrank_eq_one {K V M : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
    [AddCommMonoid M] [Module K M] (hV : finrank K V = 1) {v : V} (hv : v ≠ 0)
    {f g : V →ₗ[K] M} (h : f v = g v) : f = g :=
  ext_on ((finrank_eq_one_iff_of_ne_zero v hv).mp hV) (by simpa using h)

end LinearMap

end
