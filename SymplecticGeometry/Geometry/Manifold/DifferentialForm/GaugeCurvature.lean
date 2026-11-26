/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.GaugeCurvature
public import TauCeti.Geometry.Manifold.DifferentialForm.MapCoeff
public import TauCeti.Geometry.Manifold.DifferentialForm.VectorField
import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Naturality of the curvature of a one-form

Tau Ceti's `TauCeti.gaugeCurvature β A = d A + ½ [A ∧ A]` is the curvature of a `𝔨`-valued
one-form `A`, for a bracket on `𝔨` given as a continuous bilinear map
`β : 𝔨 →L[ℝ] 𝔨 →L[ℝ] 𝔨`. This file proves how it behaves under pull-back, under linear maps of
`𝔨` and on horizontal vector fields. As in Tau Ceti's file, each statement assumes only the
identities of `β` that it uses.

## Main results

* `TauCeti.mpullback_gaugeCurvature`: the curvature commutes with pull-back by smooth maps,
  `f^* F_A = F_{f^* A}`.
* `TauCeti.gaugeCurvature_mapCoeff`: the curvature commutes with every linear map `L : 𝔨 → 𝔨'`
  that carries the bracket `β` to the bracket `β'`, `F_{L ∘ A} = L ∘ F_A`.
* `TauCeti.gaugeCurvature_mapCoeff_toSpanSingleton`: for a real one-form `α` and `ξ ∈ 𝔨` with
  `β ξ ξ = 0`, the curvature of `α ξ` is `(d α) ξ`.
* `TauCeti.gaugeCurvature_apply_horizontal`: for a skew-symmetric bracket, the structure equation
  `F_A(X, Y) = -A([X, Y])` at a point near which `A` vanishes on the vector fields `X` and `Y`.
  The bracket `[X, Y]` is Mathlib's `VectorField.mlieBracket`, as in Guillemin–Lerman–Sternberg.
  McDuff–Salamon's bracket of vector fields is its negative, so their structure equation has no
  minus sign; the formula `F_A = d A + ½ [A ∧ A]` is the same in both conventions.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §6.3
  (connection forms on principal bundles and their curvature).
* [V. Guillemin, E. Lerman, S. Sternberg, *Symplectic Fibrations and Multiplicity
  Diagrams*][GuilleminLermanSternberg1996], §1.3 (the sign of the bracket of vector fields).
* S. Kobayashi and K. Nomizu, *Foundations of Differential Geometry*, Vol. I, Interscience, 1963,
  Chapter II, §5 (the curvature form and the structure equation).
-/

public section

noncomputable section

open VectorField Filter
open scoped Manifold ContDiff Topology

namespace TauCeti

variable {E H M 𝔨 : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 2 M] [NormedAddCommGroup 𝔨] [NormedSpace ℝ 𝔨]
  (β : 𝔨 →L[ℝ] 𝔨 →L[ℝ] 𝔨)

/-- The curvature commutes with pull-back by smooth maps: `f^* F_A = F_{f^* A}`. -/
theorem mpullback_gaugeCurvature {E' H' M' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace M']
    [ChartedSpace H' M'] [IsManifold I' 2 M'] (f : M → M') (hf : ContMDiff I I' ∞ f)
    (A : SmoothForm I' M' 𝔨 1) :
    SmoothForm.mpullback f hf (gaugeCurvature β A) =
      gaugeCurvature β (SmoothForm.mpullback f hf A) := by
  rw [gaugeCurvature_def, gaugeCurvature_def, map_add, map_smul,
    ← SmoothForm.mextDerivₗ_mpullback]
  congr 2
  exact SmoothForm.mpullback_wedgeWith β f hf A A

/-- The curvature commutes with every linear map `L` that carries the bracket `β` to the bracket
`β'`: `F_{L ∘ A} = L ∘ F_A`. -/
theorem gaugeCurvature_mapCoeff {𝔨' : Type*} [NormedAddCommGroup 𝔨'] [NormedSpace ℝ 𝔨']
    (β' : 𝔨' →L[ℝ] 𝔨' →L[ℝ] 𝔨') (L : 𝔨 →L[ℝ] 𝔨') (hL : ∀ a b, L (β a b) = β' (L a) (L b))
    (A : SmoothForm I M 𝔨 1) :
    gaugeCurvature β' (SmoothForm.mapCoeff L A) = SmoothForm.mapCoeff L (gaugeCurvature β A) := by
  rw [gaugeCurvature_def, gaugeCurvature_def, map_add, map_smul, SmoothForm.mextDerivₗ_mapCoeff,
    SmoothForm.mapCoeff_wedgeWith β β' L L L hL A A]

/-- The curvature of the `𝔨`-valued form `α ξ`, for a real one-form `α` and `ξ ∈ 𝔨` with
`β ξ ξ = 0`, is `(d α) ξ`: the bracket term vanishes, since `β (a • ξ) (b • ξ) = 0`. -/
theorem gaugeCurvature_mapCoeff_toSpanSingleton {ξ : 𝔨} (hξ : β ξ ξ = 0)
    (α : SmoothForm I M ℝ 1) :
    gaugeCurvature β (SmoothForm.mapCoeff (ContinuousLinearMap.toSpanSingleton ℝ ξ) α) =
      SmoothForm.mapCoeff (ContinuousLinearMap.toSpanSingleton ℝ ξ) (mextDerivₗ I 1 α) := by
  have hwedge : SmoothForm.wedgeWith β
      (SmoothForm.mapCoeff (ContinuousLinearMap.toSpanSingleton ℝ ξ) α)
      (SmoothForm.mapCoeff (ContinuousLinearMap.toSpanSingleton ℝ ξ) α) = 0 := by
    rw [← SmoothForm.mapCoeff_wedgeWith (ContinuousLinearMap.mul ℝ ℝ) _ _ _ 0
      fun a b ↦ by simp [hξ]]
    ext x v
    simp [SmoothForm.coe_mapCoeff, RoughForm.mapCoeff_apply]
  rw [gaugeCurvature_def, hwedge, smul_zero, add_zero, SmoothForm.mextDerivₗ_mapCoeff]

/-- **The structure equation.** For a skew-symmetric bracket `β`, if the vector fields `X` and
`Y` are differentiable at `x` and `A` vanishes on them near `x`, then the curvature of `A` on
them at `x` is `-A([X, Y](x))`. Here `[X, Y]` is the usual bracket, Mathlib's `mlieBracket`, as
in Guillemin–Lerman–Sternberg; McDuff–Salamon's bracket is its negative, so their structure
equation has no minus sign. -/
theorem gaugeCurvature_apply_horizontal (hβ : ∀ a b, β a b = -β b a) (A : SmoothForm I M 𝔨 1)
    {X Y : (y : M) → TangentSpace I y} {x : M}
    (hX : MDifferentiableAt I I.tangent (fun y ↦ (X y : TangentBundle I M)) x)
    (hY : MDifferentiableAt I I.tangent (fun y ↦ (Y y : TangentBundle I M)) x)
    (hXh : ∀ᶠ y in 𝓝 x, A.val y ![X y] = 0) (hYh : ∀ᶠ y in 𝓝 x, A.val y ![Y y] = 0) :
    (gaugeCurvature β A).val x ![X x, Y x] = -A.val x ![mlieBracket I X Y x] := by
  rw [gaugeCurvature_val β hβ, SmoothForm.mextDeriv_apply_one hX hY, hXh.self_of_nhds,
    hYh.self_of_nhds, map_zero, add_zero,
    Filter.EventuallyEq.mvfderiv_eq (f := fun _ ↦ (0 : 𝔨)) hYh,
    Filter.EventuallyEq.mvfderiv_eq (f := fun _ ↦ (0 : 𝔨)) hXh, mvfderiv_const]
  simp

end TauCeti

end
