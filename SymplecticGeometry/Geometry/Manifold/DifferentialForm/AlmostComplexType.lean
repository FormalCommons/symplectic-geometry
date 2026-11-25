/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.VectorBundle.Riemannian
public import TauCeti.Geometry.Manifold.DifferentialForm.AlmostComplexType
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Complexification
import SymplecticGeometry.Analysis.Normed.Module.Alternating.Derivation

/-!
# The real derivation of smooth forms along an endomorphism field, and type projections

Tau Ceti's `ContMDiffSection.realAlternatingDerivation` lets a smooth endomorphism field `A` of the
tangent bundle act on smooth real forms. This file identifies its value at each point with the
derivation `ContinuousAlternatingMap.fderivCompContinuousLinearMap` of the value of the form, at
the identity and in the direction `A x`. That derivation needs a norm on the tangent spaces,
which a `RiemannianBundle` metric supplies. It also relates the real derivation to the derivation
of complex-valued forms, and describes the range of Tau Ceti's type projections.

## Main results

* `ContMDiffSection.coe_realAlternatingDerivation`: the value of `𝒜 φ` at `x` is
  `(φ x).fderivCompContinuousLinearMap (id) (A x)`.
* `ContMDiffSection.realAlternatingDerivation_fin_zero`: the derivation vanishes on functions.
* `ContMDiffSection.realAlternatingDerivation_funSMulₗ`: the derivation commutes with
  multiplication by smooth functions.
* `ContMDiffSection.alternatingDerivation_mapCoeff_ofRealCLM`: on real forms, the complex
  derivation is the real one.
* `ContMDiffSection.alternatingDerivation_eq_complexifyₗ`: on complex forms, the derivation is
  the complexification of the real derivation.
* `TauCeti.SmoothForm.complexifyₗ_alternatingDerivation`: if a real-linear map of real forms
  commutes with the real derivation, its complexification commutes with the complex one.
* `TauCeti.SmoothAlmostComplexStructure.mem_range_typeProjection_iff`: the range of the
  type-`(p,q)` projection is the forms of type `(p,q)`.
* `TauCeti.SmoothAlmostComplexStructure.typeProjection_eq_aeval`: the type projection is a
  polynomial in the derivation of complex forms along `J`.
-/

public section

noncomputable section

open Bundle TauCeti
open scoped Manifold ContDiff

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] {k : ℕ}

namespace ContMDiffSection

/-- At each point, the real derivation of a smooth form along an endomorphism field `A` is the
derivation `ContinuousAlternatingMap.fderivCompContinuousLinearMap` of the value at the identity in
the direction `A x`. The metric only supplies the norm on the tangent spaces that
`fderivCompContinuousLinearMap` requires. -/
theorem coe_realAlternatingDerivation
    (A : ContMDiffSection I (E →L[ℝ] E) ∞ fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
    (φ : SmoothForm I M ℝ k) :
    (A.realAlternatingDerivation φ).val =
      fun x ↦ (φ.val x).fderivCompContinuousLinearMap (.id ℝ (TangentSpace I x)) (A x) := by
  ext x v
  rw [realAlternatingDerivation_apply,
    ContinuousAlternatingMap.fderivCompContinuousLinearMap_id_apply]

omit [RiemannianBundle (fun x : M ↦ TangentSpace I x)] in
/-- The real derivation of smooth forms along an endomorphism field vanishes on smooth functions,
the `0`-forms: at each point it is a sum over the arguments of the form, and there are none. -/
@[simp]
theorem realAlternatingDerivation_fin_zero
    (A : ContMDiffSection I (E →L[ℝ] E) ∞ fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
    (f : SmoothForm I M ℝ 0) : A.realAlternatingDerivation f = 0 := by
  ext x v
  simp

omit [RiemannianBundle (fun x : M ↦ TangentSpace I x)] in
/-- The real derivation of smooth forms along an endomorphism field is linear over smooth
functions: it commutes with multiplication by a smooth function `g`. -/
@[simp]
theorem realAlternatingDerivation_funSMulₗ
    (A : ContMDiffSection I (E →L[ℝ] E) ∞ fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
    (g : C^∞⟮I, M; ℝ⟯) (φ : SmoothForm I M ℝ k) :
    A.realAlternatingDerivation (SmoothForm.funSMulₗ g φ) =
      SmoothForm.funSMulₗ g (A.realAlternatingDerivation φ) := by
  ext x v
  simp [SmoothForm.coe_funSMulₗ, Finset.mul_sum]

omit [RiemannianBundle (fun x : M ↦ TangentSpace I x)] in
/-- On real forms, the derivation of complex-valued forms along an endomorphism field is the real
derivation: `𝒜 (α : ℂ) = (𝒜 α : ℂ)`. -/
@[simp]
theorem alternatingDerivation_mapCoeff_ofRealCLM
    (A : ContMDiffSection I (E →L[ℝ] E) ∞ fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
    (α : SmoothForm I M ℝ k) :
    A.alternatingDerivation (SmoothForm.mapCoeff Complex.ofRealCLM α) =
      SmoothForm.mapCoeff Complex.ofRealCLM (A.realAlternatingDerivation α) := by
  ext x v
  simp [RoughForm.mapCoeff_apply, ContinuousLinearMap.alternatingDerivation_apply]

omit [RiemannianBundle (fun x : M ↦ TangentSpace I x)] in
/-- On complex forms, the derivation along an endomorphism field is the complexification of the
real derivation along it. -/
theorem alternatingDerivation_eq_complexifyₗ
    (A : ContMDiffSection I (E →L[ℝ] E) ∞ fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) :
    A.alternatingDerivation (F := ℂ) (k := k) =
      SmoothForm.complexifyₗ A.realAlternatingDerivation :=
  (SmoothForm.eq_complexifyₗ_iff _ _).2 (alternatingDerivation_mapCoeff_ofRealCLM A)

end ContMDiffSection

namespace TauCeti.SmoothForm

omit [RiemannianBundle (fun x : M ↦ TangentSpace I x)] in
/-- If a real-linear map `f` of real forms commutes with the real derivation along an
endomorphism field `A`, then its complexification commutes with the derivation along `A` of
complex forms. -/
theorem complexifyₗ_alternatingDerivation {l : ℕ}
    (A : ContMDiffSection I (E →L[ℝ] E) ∞ fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
    {f : SmoothForm I M ℝ k →ₗ[ℝ] SmoothForm I M ℝ l}
    (hf : ∀ α, f (A.realAlternatingDerivation α) = A.realAlternatingDerivation (f α))
    (φ : SmoothForm I M ℂ k) :
    complexifyₗ f (A.alternatingDerivation φ) = A.alternatingDerivation (complexifyₗ f φ) := by
  have h : f ∘ₗ A.realAlternatingDerivation = A.realAlternatingDerivation ∘ₗ f := LinearMap.ext hf
  simp only [ContMDiffSection.alternatingDerivation_eq_complexifyₗ, ← LinearMap.comp_apply,
    ← complexifyₗ_comp, h]

end TauCeti.SmoothForm

namespace TauCeti.SmoothAlmostComplexStructure

variable [IsManifold I ∞ M] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

omit [RiemannianBundle (fun x : M ↦ TangentSpace I x)] in
/-- For `p + q = k`, the range of the type-`(p,q)` projection of smooth `k`-forms consists of the
forms of type `(p,q)`. -/
theorem mem_range_typeProjection_iff (J : SmoothAlmostComplexStructure I M) {p q : ℕ}
    (hpq : p + q = k) (φ : SmoothForm I M F k) :
    φ ∈ LinearMap.range (J.typeProjection p q) ↔ φ.IsOfType J p q :=
  ⟨fun ⟨ψ, hψ⟩ ↦ hψ ▸ J.isOfType_typeProjection hpq ψ, fun h ↦ ⟨φ, h.typeProjection_self⟩⟩

omit [IsManifold I 1 M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)] in
/-- The type-`(p,q)` projection of smooth `k`-forms is the type polynomial evaluated at the
derivation `J.toEndomorphism.alternatingDerivation`. -/
theorem typeProjection_eq_aeval (J : SmoothAlmostComplexStructure I M) (p q : ℕ) :
    J.typeProjection (F := F) (k := k) p q =
      Polynomial.aeval J.toEndomorphism.alternatingDerivation
        (ContinuousLinearMap.typePolynomial k p q) := by
  refine LinearMap.ext fun φ ↦ Subtype.ext <| funext fun x ↦ ?_
  simp only [coe_typeProjection, ContMDiffSection.aeval_alternatingDerivation_apply,
    ContinuousLinearMap.typeProjection_eq_aeval]

end TauCeti.SmoothAlmostComplexStructure

end
