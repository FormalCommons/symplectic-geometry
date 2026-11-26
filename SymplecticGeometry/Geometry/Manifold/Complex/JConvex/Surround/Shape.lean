/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic
public import TauCeti.LinearAlgebra.TotallyReal.Euclidean

/-!
# The model of the J-convex surrounding

This file sets up the model in which Cieliebak and Eliashberg compute the shapes of `i`-convex
hypersurfaces near an attached disc. The ambient space is
`V = EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)`, a complex manifold modelled on
itself, with points written `p = (x + i y, w)`.

## The model disc

The disc is the inclusion `ι₀ : ℝᵏ → V`, `x ↦ (x, 0)`, of the real points of the first factor,
that is the locus `y = 0`, `w = 0`.

* `SymplecticGeometry.modelDisc k m`: the inclusion `ι₀`, as a real continuous linear map
  (`SymplecticGeometry.modelDisc_apply`);
* `SymplecticGeometry.isSmoothEmbedding_modelDisc`: `ι₀` is a smooth embedding, by Tau Ceti's
  `ContinuousLinearMap.isSmoothEmbedding_of_injective`;
* `SymplecticGeometry.mfderiv_modelDisc`: its differential at every point is `ι₀` itself;
* `SymplecticGeometry.isTotallyReal_range_mfderiv_modelDisc`: its tangent images are totally
  real for the complex structure of `V` (Tau Ceti's `TauCeti.IsTotallyReal`), since they lie in
  `ℝᵏ × 0`, the product of Tau Ceti's `TauCeti.realSubspace` with the zero subspace.

When `m ≠ 0` the image has less than half the real dimension of `V`, so `ι₀` is not
a totally real embedding in Tau Ceti's stronger sense `TauCeti.IsTotallyRealEmbedding`, and the
weak form above is the one the surrounding uses.

## References

* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  Chapter 4 (shapes of `i`-convex hypersurfaces).
-/

public section

noncomputable section

open Manifold
open scoped ContDiff

namespace SymplecticGeometry

open TauCeti

variable (k m : ℕ)

/-- The model disc `ι₀ : ℝᵏ → ℂᵏ × ℂᵐ`, `x ↦ (x, 0)`: the inclusion of the real points of the
first factor, as a real continuous linear map. -/
def modelDisc :
    EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m) :=
  LinearMap.toContinuousLinearMap
    { toFun x := (WithLp.toLp 2 fun j ↦ (x j : ℂ), 0)
      map_add' x y := by ext j <;> simp
      map_smul' c x := by ext j <;> simp [Complex.real_smul] }

variable {k m}

/-- The model disc sends `x` to the point with coordinates `(x j : ℂ)` in the first factor and
`0` in the second. -/
theorem modelDisc_apply (x : EuclideanSpace ℝ (Fin k)) :
    modelDisc k m x = (WithLp.toLp 2 fun j ↦ (x j : ℂ), 0) :=
  (rfl)

/-- The `j`-th coordinate of the first component of `ι₀ x` is `x j`. -/
@[simp]
theorem modelDisc_apply_fst_apply (x : EuclideanSpace ℝ (Fin k)) (j : Fin k) :
    (modelDisc k m x).1 j = x j := by
  simp [modelDisc_apply]

/-- The second component of `ι₀ x` is `0`. -/
@[simp]
theorem modelDisc_apply_snd (x : EuclideanSpace ℝ (Fin k)) : (modelDisc k m x).2 = 0 := by
  simp [modelDisc_apply]

/-- The model disc is injective: `x` is the real part of the first component of `ι₀ x`. -/
theorem modelDisc_injective : Function.Injective (modelDisc k m) := by
  intro x y h
  ext j
  simpa using congrArg (fun p ↦ (p.1 j).re) h

/-- The image of the model disc is the product of the real subspace `ℝᵏ ⊆ ℂᵏ` with `0`. -/
theorem range_modelDisc :
    LinearMap.range (modelDisc k m).toLinearMap = (realSubspace (Fin k)).prod ⊥ := by
  ext ⟨z, w⟩
  simp only [LinearMap.mem_range, ContinuousLinearMap.coe_coe, Submodule.mem_prod,
    mem_realSubspace, Submodule.mem_bot]
  constructor
  · rintro ⟨x, hx⟩
    rw [modelDisc_apply, Prod.mk.injEq] at hx
    obtain ⟨rfl, rfl⟩ := hx
    simp
  · rintro ⟨hz, rfl⟩
    refine ⟨WithLp.toLp 2 fun j ↦ (z j).re, ?_⟩
    rw [modelDisc_apply]
    ext j
    · apply Complex.ext <;> simp [hz j]
    · simp

/-- The model disc is a smooth embedding, of any regularity. -/
theorem isSmoothEmbedding_modelDisc (n : WithTop ℕ∞) :
    IsSmoothEmbedding 𝓘(ℝ, EuclideanSpace ℝ (Fin k))
      𝓘(ℝ, EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) n (modelDisc k m) :=
  (modelDisc k m).isSmoothEmbedding_of_injective modelDisc_injective

/-- The differential of the linear map `ι₀` is `ι₀` at every point. -/
theorem mfderiv_modelDisc (x : EuclideanSpace ℝ (Fin k)) :
    mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin k))
      𝓘(ℝ, EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) (modelDisc k m) x =
      modelDisc k m :=
  (modelDisc k m).mfderiv_eq

/-- The tangent images of the model disc are totally real for the complex structure of
`ℂᵏ × ℂᵐ`, multiplication by `i`. -/
theorem isTotallyReal_range_mfderiv_modelDisc (x : EuclideanSpace ℝ (Fin k)) :
    IsTotallyReal
      ((SmoothAlmostComplexStructure.ofComplexManifold
        (EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m))
        (EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m))).toEndomorphism
          (modelDisc k m x)).toLinearMap
      (LinearMap.range (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin k))
        𝓘(ℝ, EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) (modelDisc k m)
          x).toLinearMap) := by
  rw [isTotallyReal_iff, Submodule.disjoint_def]
  rintro _ ⟨(y : EuclideanSpace ℝ (Fin k)), rfl⟩ ⟨_, ⟨(z : EuclideanSpace ℝ (Fin k)), rfl⟩, h⟩
  rw [mfderiv_modelDisc, SmoothAlmostComplexStructure.toEndomorphism_ofComplexManifold] at h
  rw [mfderiv_modelDisc]
  -- The tangent spaces of `ℝᵏ` and `V` are these spaces themselves: restate the goal and `h`
  -- on them, where the coordinate lemmas of `modelDisc` apply.
  change modelDisc k m y = 0
  have h' : Complex.I • modelDisc k m z = modelDisc k m y := h
  refine Prod.ext ?_ (modelDisc_apply_snd _)
  ext j
  simpa using (congrArg (fun p ↦ (p.1 j).re) h').symm

end SymplecticGeometry

end
