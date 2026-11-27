/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import TauCeti.Geometry.Symplectic.Duality
import TauCeti.Geometry.Symplectic.CompatibleMetric

/-!
# Symplectic forms given by an inner product and an almost complex structure

Let `V` be a finite-dimensional real inner product space, `ω` a symplectic form on `V` and `J` an
almost complex structure with `ω(v, w) = ⟪J v, w⟫` for all `v` and `w`. This file makes Tau
Ceti's isomorphism `TauCeti.SymplecticForm.flatEquiv`, `ω♭ : v ↦ ω(v, ·)`, explicit in that
case.

* `TauCeti.SymplecticForm.apply_apply_eq_inner_of_apply_eq_inner`: `ω(v, J w) = ⟪v, w⟫`, so
  that the inner product is the metric `ω(·, J ·)` and Tau Ceti's lemmas for that case apply;
  in particular `J` preserves norms (`TauCeti.SymplecticForm.norm_apply_of_apply_eq_inner`).
* `TauCeti.SymplecticForm.flatEquiv_symm_apply_of_apply_eq_inner`: the inverse `ω♭⁻¹` sends `φ`
  to `-J φ'`, where `φ'` is the vector dual to `φ` for the inner product
  (`InnerProductSpace.toDual`).
* `TauCeti.SymplecticForm.norm_flatEquiv_symm_apply_of_apply_eq_inner`: `ω♭⁻¹` preserves norms.

The standard form `ω₀` on `ℝ²ⁿ` with `J₀` is the model case.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017]
-/

public section

namespace TauCeti.SymplecticForm

open scoped RealInnerProductSpace

section InnerProductSpace

variable {V : Type*} [SeminormedAddCommGroup V] [InnerProductSpace ℝ V]
  {ω : SymplecticForm V} {J : AlmostComplexStructure V}

/-- If `ω(v, w) = ⟪J v, w⟫` for all `v` and `w`, then the inner product is the metric
`ω(·, J ·)`: `ω(v, J w) = ⟪v, w⟫`. -/
theorem apply_apply_eq_inner_of_apply_eq_inner (h : ∀ v w, ω v w = ⟪J v, w⟫) (v w : V) :
    ω v (J w) = ⟪v, w⟫ := by
  rw [← ω.neg_eq, h, J.apply_apply, inner_neg_left, neg_neg, real_inner_comm]

/-- If `ω(v, w) = ⟪J v, w⟫` for all `v` and `w`, then `J` preserves norms. -/
theorem norm_apply_of_apply_eq_inner (h : ∀ v w, ω v w = ⟪J v, w⟫) (v : V) : ‖J v‖ = ‖v‖ :=
  ω.norm_apply_eq_norm_of_apply_apply_self_eq_inner
    (fun v ↦ apply_apply_eq_inner_of_apply_eq_inner h v v) v

end InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {J : AlmostComplexStructure V}

/-- If `ω(v, w) = ⟪J v, w⟫` for all `v` and `w`, then the inverse of `ω♭ : v ↦ ω(v, ·)` sends
`φ` to `-J φ'`, where `φ'` is the vector dual to `φ` for the inner product. -/
theorem flatEquiv_symm_apply_of_apply_eq_inner (h : ∀ v w, ω v w = ⟪J v, w⟫)
    (φ : V →L[ℝ] ℝ) :
    ω.flatEquiv.symm φ = -J ((InnerProductSpace.toDual ℝ V).symm φ) := by
  rw [ContinuousLinearEquiv.symm_apply_eq]
  ext v
  rw [flatEquiv_apply, h, map_neg, J.apply_apply, neg_neg, InnerProductSpace.toDual_symm_apply]

/-- If `ω(v, w) = ⟪J v, w⟫` for all `v` and `w`, then the inverse of `ω♭ : v ↦ ω(v, ·)` preserves
norms. -/
theorem norm_flatEquiv_symm_apply_of_apply_eq_inner (h : ∀ v w, ω v w = ⟪J v, w⟫)
    (φ : V →L[ℝ] ℝ) : ‖ω.flatEquiv.symm φ‖ = ‖φ‖ := by
  rw [flatEquiv_symm_apply_of_apply_eq_inner h, norm_neg, norm_apply_of_apply_eq_inner h,
    LinearIsometryEquiv.norm_map]

end TauCeti.SymplecticForm

end
