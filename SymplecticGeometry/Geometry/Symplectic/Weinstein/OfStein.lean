/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Complex.Plurisubharmonic
public import SymplecticGeometry.Geometry.Manifold.Morse.GradientLike
public import TauCeti.Geometry.Symplectic.Hamiltonian.SymplecticVectorField
public import TauCeti.Geometry.Symplectic.Liouville.VectorField
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.CompatibleMetric
public import TauCeti.Geometry.Symplectic.Manifold.Flat

/-!
# The Liouville field of a Stein function

Let `M` be a complex manifold modelled on `E`, seen as a real manifold, with complex structure
`J = ofComplexManifold E M`. For a smooth real function `φ`, write `λ_φ = -dφ ∘ J`, Tau Ceti's
`J.covectorComplexStructure (mextDerivₗ 𝓘(ℝ, E) 0 (SmoothForm.ofFunction φ))`, and
`ω_φ = dλ_φ`. The vector field `dCLiouvilleField φ` is `(ω_φ♭)⁻¹ λ_φ`, the vector field `X`
with `ι_X ω_φ = λ_φ` wherever `ω_φ` is nondegenerate, and zero at the points where the flat
map of `ω_φ` is not invertible.

For `φ` strictly plurisubharmonic at every point, as a Stein function is, `ω_φ` is a Kähler
form, so `X` is smooth, it is a Liouville field of `ω_φ` (`L_X ω_φ = dλ_φ = ω_φ`), and it
is the gradient of `φ` for the Kähler metric `g(u, w) = ω_φ(u, J w)`: indeed
`g(X, w) = ω_φ(X, J w) = λ_φ(J w) = -dφ(J J w) = dφ(w)`. Hence it is
gradient-like for `φ`, with `δ = 1 / 2`. This is the Weinstein manifold of a Stein function of
Cieliebak–Eliashberg, §11.5, before the reparametrization that makes the field complete.

## Main declarations

* `SymplecticGeometry.dCLiouvilleField`: the field `(ω_φ♭)⁻¹ λ_φ`, with
  `SymplecticGeometry.dCLiouvilleField_def`.
* `SymplecticGeometry.apply_dCLiouvilleField_of_isInvertible`: `ω_φ(X, w) = λ_φ(w)` at a point
  where the flat map of `ω_φ` is invertible.
* `SymplecticGeometry.interior_dCLiouvilleField`: `ι_X ω_φ = λ_φ` when `ω_φ` is nondegenerate,
  as it is for a Stein function by `SymplecticGeometry.IsSteinFunction.isSymplectic`.
* `SymplecticGeometry.contMDiff_dCLiouvilleField`: the field is smooth when `ω_φ` is
  nondegenerate.
* `SymplecticGeometry.isLiouvilleVectorField_dCLiouvilleField`: when `ω_φ` is nondegenerate,
  the field is a Liouville field of `ω_φ`, by Tau Ceti's
  `TauCeti.SmoothTwoForm.IsSymplectic.mlieDerivForm_interiorEquiv_symm`.
* `SymplecticGeometry.dCLiouvilleField_eq_mgradient`: for `φ` strictly plurisubharmonic at
  every point, the field is the gradient of `φ` for the metric of the compatible pair `(ω_φ, J)`.
* `SymplecticGeometry.isGradientLike_dCLiouvilleField`: for `φ` strictly plurisubharmonic at
  every point, the field is gradient-like for `φ`, by `TauCeti.isGradientLike_mgradient`.

## Implementation notes

The field is defined pointwise with `ContinuousLinearMap.inverse`, as Tau Ceti's
`TauCeti.SmoothTwoForm.hamiltonianVectorField`, rather than through Tau Ceti's
`TauCeti.SmoothTwoForm.IsNondegenerate.interiorEquiv`, which needs nondegeneracy everywhere to
be stated. Where `ω_φ` is nondegenerate the two agree
(`SymplecticGeometry.dCLiouvilleField_eq_interiorEquiv_symm`), which gives the contraction
identity and the smoothness.

## References

* [K. Cieliebak, Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  §11.5
-/

public section

noncomputable section

open Bundle
open scoped Manifold ContDiff TauCeti.ComplexManifold

namespace SymplecticGeometry

open TauCeti TauCeti.Manifold TauCeti.SmoothAlmostComplexStructure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]

/-- The **Liouville field of a function** `φ` on a complex manifold: the vector field
`X = (ω_φ♭)⁻¹ λ_φ`, where `λ_φ = -dφ ∘ J` and `ω_φ = dλ_φ`. Where the flat map of `ω_φ` is
invertible, `X` is the vector with `ι_X ω_φ = λ_φ`; elsewhere it is `0`. -/
def dCLiouvilleField (φ : C^∞⟮𝓘(ℝ, E), M; ℝ⟯) (x : M) : TangentSpace 𝓘(ℝ, E) x :=
  (SmoothTwoForm.flat (mextDerivₗ 𝓘(ℝ, E) 1
      ((ofComplexManifold E M).covectorComplexStructure
        (mextDerivₗ 𝓘(ℝ, E) 0 (SmoothForm.ofFunction φ)))) x).inverse
    (SmoothForm.degreeOneEquiv ((ofComplexManifold E M).covectorComplexStructure
      (mextDerivₗ 𝓘(ℝ, E) 0 (SmoothForm.ofFunction φ))) x)

/-- The Liouville field of `φ` unfolds as the inverse flat map of `ω_φ` applied to `λ_φ`. -/
theorem dCLiouvilleField_def (φ : C^∞⟮𝓘(ℝ, E), M; ℝ⟯) (x : M) :
    dCLiouvilleField φ x =
      (SmoothTwoForm.flat (mextDerivₗ 𝓘(ℝ, E) 1
          ((ofComplexManifold E M).covectorComplexStructure
            (mextDerivₗ 𝓘(ℝ, E) 0 (SmoothForm.ofFunction φ)))) x).inverse
        (SmoothForm.degreeOneEquiv ((ofComplexManifold E M).covectorComplexStructure
          (mextDerivₗ 𝓘(ℝ, E) 0 (SmoothForm.ofFunction φ))) x) :=
  (rfl)

/-- At a point where the flat map of `ω_φ` is invertible, `ω_φ(X, w) = λ_φ(w)` for the
Liouville field `X` of `φ`. -/
theorem apply_dCLiouvilleField_of_isInvertible (φ : C^∞⟮𝓘(ℝ, E), M; ℝ⟯) {x : M}
    (hx : (SmoothTwoForm.flat (mextDerivₗ 𝓘(ℝ, E) 1
      ((ofComplexManifold E M).covectorComplexStructure
        (mextDerivₗ 𝓘(ℝ, E) 0 (SmoothForm.ofFunction φ)))) x).IsInvertible)
    (w : TangentSpace 𝓘(ℝ, E) x) :
    (mextDerivₗ 𝓘(ℝ, E) 1 ((ofComplexManifold E M).covectorComplexStructure
        (mextDerivₗ 𝓘(ℝ, E) 0 (SmoothForm.ofFunction φ)))).val x ![dCLiouvilleField φ x, w] =
      ((ofComplexManifold E M).covectorComplexStructure
        (mextDerivₗ 𝓘(ℝ, E) 0 (SmoothForm.ofFunction φ))).val x ![w] := by
  rw [← SmoothBundleForm.eval₂_apply, ← SmoothTwoForm.flat_apply, dCLiouvilleField_def,
    hx.self_apply_inverse, SmoothForm.degreeOneEquiv_apply_apply_vec]

variable [FiniteDimensional ℂ E]

/-- Where `ω_φ` is nondegenerate, the Liouville field of `φ` is the vector field that Tau Ceti's
contraction equivalence `TauCeti.SmoothTwoForm.IsNondegenerate.interiorEquiv` assigns to
`λ_φ`. -/
theorem dCLiouvilleField_eq_interiorEquiv_symm (φ : C^∞⟮𝓘(ℝ, E), M; ℝ⟯)
    (hω : SmoothTwoForm.IsNondegenerate (mextDerivₗ 𝓘(ℝ, E) 1
      ((ofComplexManifold E M).covectorComplexStructure
        (mextDerivₗ 𝓘(ℝ, E) 0 (SmoothForm.ofFunction φ))))) :
    dCLiouvilleField φ = ⇑(hω.interiorEquiv.symm ((ofComplexManifold E M).covectorComplexStructure
      (mextDerivₗ 𝓘(ℝ, E) 0 (SmoothForm.ofFunction φ)))) :=
  funext fun x ↦ by
    rw [dCLiouvilleField_def, SmoothTwoForm.IsNondegenerate.interiorEquiv_symm_apply]

/-- Where `ω_φ` is nondegenerate, the Liouville field `X` of `φ` satisfies `ι_X ω_φ = λ_φ`. -/
theorem interior_dCLiouvilleField (φ : C^∞⟮𝓘(ℝ, E), M; ℝ⟯)
    (hω : SmoothTwoForm.IsNondegenerate (mextDerivₗ 𝓘(ℝ, E) 1
      ((ofComplexManifold E M).covectorComplexStructure
        (mextDerivₗ 𝓘(ℝ, E) 0 (SmoothForm.ofFunction φ))))) :
    RoughForm.interior (dCLiouvilleField φ) (mextDerivₗ 𝓘(ℝ, E) 1
        ((ofComplexManifold E M).covectorComplexStructure
          (mextDerivₗ 𝓘(ℝ, E) 0 (SmoothForm.ofFunction φ)))).val =
      ((ofComplexManifold E M).covectorComplexStructure
        (mextDerivₗ 𝓘(ℝ, E) 0 (SmoothForm.ofFunction φ))).val := by
  rw [dCLiouvilleField_eq_interiorEquiv_symm φ hω,
    SmoothTwoForm.IsNondegenerate.interior_interiorEquiv_symm]

/-- Where `ω_φ` is nondegenerate, the Liouville field of `φ` is smooth. -/
theorem contMDiff_dCLiouvilleField (φ : C^∞⟮𝓘(ℝ, E), M; ℝ⟯)
    (hω : SmoothTwoForm.IsNondegenerate (mextDerivₗ 𝓘(ℝ, E) 1
      ((ofComplexManifold E M).covectorComplexStructure
        (mextDerivₗ 𝓘(ℝ, E) 0 (SmoothForm.ofFunction φ))))) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent ∞ (T% (dCLiouvilleField φ)) := by
  rw [dCLiouvilleField_eq_interiorEquiv_symm φ hω]
  exact ContMDiffSection.contMDiff _

variable {φ : C^∞⟮𝓘(ℝ, E), M; ℝ⟯}

/-- **The Liouville field of `φ` is a Liouville field** where `ω_φ` is nondegenerate:
`L_X ω_φ = ω_φ`. -/
theorem isLiouvilleVectorField_dCLiouvilleField
    (hω : SmoothTwoForm.IsNondegenerate (mextDerivₗ 𝓘(ℝ, E) 1
      ((ofComplexManifold E M).covectorComplexStructure
        (mextDerivₗ 𝓘(ℝ, E) 0 (SmoothForm.ofFunction φ))))) :
    IsLiouvilleVectorField (mextDerivₗ 𝓘(ℝ, E) 1 ((ofComplexManifold E M).covectorComplexStructure
      (mextDerivₗ 𝓘(ℝ, E) 0 (SmoothForm.ofFunction φ)))).val (dCLiouvilleField φ) := by
  have hσ : SmoothTwoForm.IsSymplectic (mextDerivₗ 𝓘(ℝ, E) 1
      ((ofComplexManifold E M).covectorComplexStructure
        (mextDerivₗ 𝓘(ℝ, E) 0 (SmoothForm.ofFunction φ)))) :=
    ⟨SmoothForm.isClosed_mextDerivₗ _, hω⟩
  rw [isLiouvilleVectorField_iff, dCLiouvilleField_eq_interiorEquiv_symm φ hω,
    hσ.mlieDerivForm_interiorEquiv_symm, mextDerivₗ_apply]

/-- **The Liouville field of a strictly plurisubharmonic function is a gradient.** If `φ` is
strictly plurisubharmonic at every point, the Liouville field of `φ` is the gradient of `φ` for
the Kähler metric `g(u, w) = ω_φ(u, J w)` of the compatible pair `(ω_φ, J)`. -/
theorem dCLiouvilleField_eq_mgradient (hφ : ∀ x, IsManifoldStrictlyPlurisubharmonicAt E φ x) :
    letI : RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) :=
      ⟨(isKahler_mextDerivₗ_covectorComplexStructure hφ).compatible.metric.toRiemannianMetric⟩
    dCLiouvilleField φ = mgradient 𝓘(ℝ, E) φ := by
  have hK := isKahler_mextDerivₗ_covectorComplexStructure hφ
  let : RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) :=
    ⟨hK.compatible.metric.toRiemannianMetric⟩
  funext x
  refine eq_mgradient_iff.2 fun v ↦ ?_
  -- `g(X, v) = ω_φ(X, J v) = λ_φ(J v) = -dφ(J J v) = dφ(v)`
  rw [hK.compatible.inner_eq_eval₂, SmoothBundleForm.eval₂_apply,
    apply_dCLiouvilleField_of_isInvertible φ (hK.isSymplectic.isNondegenerate.isInvertible_flat x),
    covectorComplexStructure_apply_vec, SmoothAlmostComplexStructure.apply_apply,
    mextDerivₗ_zero_apply, SmoothForm.ofFunction_apply_zero, map_neg, _root_.neg_neg]

/-- **The Liouville field of a strictly plurisubharmonic function is gradient-like** for the
function. -/
theorem isGradientLike_dCLiouvilleField (hφ : ∀ x, IsManifoldStrictlyPlurisubharmonicAt E φ x) :
    IsGradientLike φ (dCLiouvilleField φ) := by
  rw [dCLiouvilleField_eq_mgradient hφ]
  exact isGradientLike_mgradient _ _

end SymplecticGeometry

end
