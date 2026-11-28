/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.MapCoeff

/-!
# Coefficient maps of differential forms: injectivity, smooth functions and pull-backs

Tau Ceti's `TauCeti.RoughForm.mapCoeff L` and `TauCeti.SmoothForm.mapCoeff L` apply a continuous
linear map `L : F →L[ℝ] G` of coefficient spaces to the values of a form. This file shows that
they are injective when `L` is, and that the coefficient map of smooth forms commutes with
multiplication by a smooth real function. It also says when the pull-back of a form by a smooth
map is the image of a form under a coefficient map, pointwise.

## Main results

* `TauCeti.RoughForm.mapCoeff_injective`, `TauCeti.SmoothForm.mapCoeff_injective`: the coefficient
  map along an injective continuous linear map is injective, on rough and on smooth forms.
* `TauCeti.SmoothForm.mapCoeff_funSMulₗ`: the coefficient map of smooth forms commutes with
  `TauCeti.SmoothForm.funSMulₗ g`, multiplication by a smooth real function `g`.
* `TauCeti.SmoothForm.mpullback_eq_mapCoeff_iff`: `f^* φ = L ∘ ψ` holds as forms exactly when it
  holds at every point on all tangent vectors; `TauCeti.SmoothForm.mpullback_eq_mapCoeff_iff_one`
  says the same for one-forms, on single tangent vectors.
-/

public section

open scoped Manifold ContDiff

namespace TauCeti

variable {E H M F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G] {k : ℕ}

/-- The coefficient map of rough forms along an injective continuous linear map is injective. -/
theorem RoughForm.mapCoeff_injective {L : F →L[ℝ] G} (hL : Function.Injective L) :
    Function.Injective (mapCoeff (I := I) (M := M) (k := k) L) := fun φ ψ h ↦ by
  ext x v
  exact hL (by simpa using congrArg (fun φ ↦ φ x v) h)

namespace SmoothForm

variable [IsManifold I 1 M]

/-- The coefficient map of smooth forms along an injective continuous linear map is
injective. -/
theorem mapCoeff_injective {L : F →L[ℝ] G} (hL : Function.Injective L) :
    Function.Injective (mapCoeff (I := I) (M := M) (k := k) L) := fun _ _ h ↦
  Subtype.ext <| RoughForm.mapCoeff_injective hL <| by
    simpa only [coe_mapCoeff] using congrArg Subtype.val h

/-- The coefficient map of smooth forms along a continuous linear map `L` commutes with
multiplication by a smooth real function `g`: `L (g φ) = g (L φ)`. -/
@[simp]
theorem mapCoeff_funSMulₗ (L : F →L[ℝ] G) (g : C^∞⟮I, M; ℝ⟯) (φ : SmoothForm I M F k) :
    mapCoeff L (funSMulₗ g φ) = funSMulₗ g (mapCoeff L φ) := by
  ext x v
  simp [RoughForm.mapCoeff_apply]

section Pullback

variable {E' H' M' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  [TopologicalSpace M'] [ChartedSpace H' M'] {I' : ModelWithCorners ℝ E' H'} [IsManifold I' 1 M']

/-- The pull-back of a smooth form `φ` by a smooth map `f` is the image of a smooth form `ψ`
under the coefficient map `L` exactly when `φ_{f x}(df_x v₁, …, df_x v_k) = L (ψ_x(v₁, …, v_k))`
at every point `x` and for all tangent vectors `vᵢ` at `x`. -/
theorem mpullback_eq_mapCoeff_iff {f : M → M'} (hf : ContMDiff I I' ∞ f) {L : F →L[ℝ] G}
    {φ : SmoothForm I' M' G k} {ψ : SmoothForm I M F k} :
    mpullback f hf φ = mapCoeff L ψ ↔
      ∀ (x : M) (v : Fin k → TangentSpace I x),
        φ.val (f x) (fun i ↦ mfderiv I I' f x (v i)) = L (ψ.val x v) := by
  refine ⟨fun h x v ↦ ?_, fun h ↦ SmoothBundleForm.ext fun x v ↦ ?_⟩
  · rw [← mpullback_apply f hf, h, coe_mapCoeff, RoughForm.mapCoeff_apply]
  · rw [mpullback_apply, coe_mapCoeff, RoughForm.mapCoeff_apply, h]

/-- The pull-back of a smooth one-form `φ` by a smooth map `f` is the image of a smooth one-form
`ψ` under `L` exactly when `φ_{f x}(df_x v) = L (ψ_x v)` for every tangent vector `v` at every
point `x`. -/
theorem mpullback_eq_mapCoeff_iff_one {f : M → M'} (hf : ContMDiff I I' ∞ f) {L : F →L[ℝ] G}
    {φ : SmoothForm I' M' G 1} {ψ : SmoothForm I M F 1} :
    mpullback f hf φ = mapCoeff L ψ ↔
      ∀ (x : M) (v : TangentSpace I x), φ.val (f x) ![mfderiv I I' f x v] = L (ψ.val x ![v]) := by
  rw [SmoothBundleForm.ext_eval₁_iff]
  simp only [mpullback_apply_one, coe_mapCoeff, RoughForm.mapCoeff_apply]

end Pullback

end SmoothForm

end TauCeti

end
