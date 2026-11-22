/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Equiv.Submodule

/-!
# Restricting a continuous linear map with a left inverse to a submodule

A continuous linear map `f : M →L[R] M₂` with a continuous left inverse `g` restricts, on every
submodule `p` of `M`, to a continuous linear equivalence of `p` onto its image
(`ContinuousLinearMap.equivMapOfLeftInverse`), whose inverse is the restriction of `g`. This is the
continuous counterpart of Mathlib's `Submodule.equivMapOfInjective`; the continuity of the
inverse is what the left inverse provides.

## Main definitions

* `ContinuousLinearMap.equivMapOfLeftInverse f g h p : p ≃L[R] p.map f`.
-/

public section

namespace ContinuousLinearMap

variable {R M M₂ : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [TopologicalSpace M]
  [AddCommMonoid M₂] [Module R M₂] [TopologicalSpace M₂]

/-- A continuous linear map `f` with a continuous left inverse `g` restricts to a continuous
linear equivalence of a submodule `p` onto its image; the inverse is the restriction of `g`. -/
def equivMapOfLeftInverse (f : M →L[R] M₂) (g : M₂ →L[R] M) (h : Function.LeftInverse g f)
    (p : Submodule R M) : p ≃L[R] p.map (f : M →ₗ[R] M₂) where
  toFun v := ⟨f v, Submodule.mem_map_of_mem v.property⟩
  invFun w := ⟨g w, (Submodule.mem_map.1 w.property).elim fun u ⟨hu, hw⟩ ↦ by
    rwa [← hw, coe_coe, h u]⟩
  map_add' v w := by ext; simp
  map_smul' c v := by ext; simp
  left_inv v := Subtype.ext (h v)
  right_inv := by
    rintro ⟨_, u, -, rfl⟩
    exact Subtype.ext (congrArg f (h u))
  continuous_toFun := (f.continuous.comp continuous_subtypeVal).subtype_mk _
  continuous_invFun := (g.continuous.comp continuous_subtypeVal).subtype_mk _

@[simp]
theorem coe_equivMapOfLeftInverse_apply (f : M →L[R] M₂) (g : M₂ →L[R] M)
    (h : Function.LeftInverse g f) (p : Submodule R M) (v : p) :
    (f.equivMapOfLeftInverse g h p v : M₂) = f v :=
  (rfl)

@[simp]
theorem coe_equivMapOfLeftInverse_symm_apply (f : M →L[R] M₂) (g : M₂ →L[R] M)
    (h : Function.LeftInverse g f) (p : Submodule R M) (w : p.map (f : M →ₗ[R] M₂)) :
    ((f.equivMapOfLeftInverse g h p).symm w : M) = g w :=
  (rfl)

end ContinuousLinearMap

end
