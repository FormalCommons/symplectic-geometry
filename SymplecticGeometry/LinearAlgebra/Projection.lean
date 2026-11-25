/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.Projection

/-!
# Linear maps out of a sum of complementary submodules

For complementary submodules `p` and `q` of `E`, Mathlib's
`LinearMap.ofIsComplProdEquiv h : ((p →ₗ F) × (q →ₗ F)) ≃ₗ (E →ₗ F)` glues a pair of linear
maps on `p` and on `q` into one on `E`. This file gives its value,
`LinearMap.ofIsComplProdEquiv_apply`: the equivalence sends `(φ, ψ)` to `ofIsCompl h φ ψ`, the
map that is `φ` on `p` and `ψ` on `q`.
-/

public section

namespace LinearMap

variable {R : Type*} [CommRing R] {E : Type*} [AddCommGroup E] [Module R E]
  {F : Type*} [AddCommGroup F] [Module R F] {p q : Submodule R E}

/-- The equivalence `LinearMap.ofIsComplProdEquiv` glues a pair of linear maps on complementary
submodules into the linear map `ofIsCompl h φ.1 φ.2`. -/
@[simp]
theorem ofIsComplProdEquiv_apply (h : IsCompl p q) (φ : (p →ₗ[R] F) × (q →ₗ[R] F)) :
    ofIsComplProdEquiv h φ = ofIsCompl h φ.1 φ.2 :=
  rfl

end LinearMap

end
