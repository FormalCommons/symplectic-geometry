/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import TauCeti.Geometry.Manifold.DifferentialForm.Regularity
import SymplecticGeometry.Geometry.Manifold.MFDeriv.Prod
import TauCeti.Geometry.Manifold.DifferentialForm.ExtDeriv
import TauCeti.Geometry.Manifold.DifferentialForm.Naturality

/-!
# Pullback of forms: its value at a point, negation and constant maps

At a point `x`, the pullback of a form `φ` along `f` is the value of `φ` at `f x` composed with
the differential of `f` at `x` (`TauCeti.mpullback_apply_eq_compContinuousLinearMap`). The
statement is on the tangent spaces, so that Mathlib's bound
`ContinuousAlternatingMap.norm_compContinuousLinearMap_le` applies with their norms, such as
Riemannian ones. Tau Ceti's `TauCeti.mpullback_apply_eq_compContinuousLinearMapCLM` states the
same equality on the model spaces.
So two maps with the same value and the same differential at `x` pull every form back to the
same value at `x` (`TauCeti.mpullback_apply_eq_of_mfderiv_eq`). With Tau Ceti's locality and
naturality of the exterior derivative, it gives `dθ` at `x` for a smooth form `θ` that agrees
near `x` with a pullback (`TauCeti.mextDerivₗ_apply_eq_of_eventuallyEq_mpullback`).
With naturality alone, when `f` maps `s` into `t`, a form that is exact on a neighbourhood of `t`
pulls back to one that is exact on a neighbourhood of `s`
(`TauCeti.SmoothForm.exists_mem_nhdsSet_mextDerivₗ_mpullback_eq`).

If `f : M → M` preserves a function `ρ`, and the pullback of `φ` along `f` agrees with `φ` where
`ρ` does not vanish, then `f` pulls `ρ • φ` back to itself
(`TauCeti.mpullback_fun_smul_eq_self`): a form cut off by an invariant function is invariant as
soon as it is so on the support of the cut-off.

Pulling a form back commutes with negation (`TauCeti.mpullback_neg`), as Tau Ceti's
`TauCeti.mpullback_sub` says for subtraction.

Pulling a smooth form of positive degree back along a constant map gives the zero form
(`TauCeti.SmoothForm.mpullback_const`, the smooth case of Tau Ceti's
`TauCeti.mpullback_const`). So the slice
`x ↦ (x, p)` of the pullback of such a form along the projection `M × M' → M'` is zero
(`TauCeti.SmoothForm.mpullback_prodMk_left_mpullback_snd`).

For a map `f : M × M₂ → M'`, the slice `z ↦ f (s, z)` is `f` composed with the inclusion
`z ↦ (s, z)`, whose differential is `w ↦ (0, w)`
(`TauCeti.Manifold.tangentSpaceProdEquiv_mfderiv_prodMk_right`). By the chain
rule `TauCeti.mpullback_comp_at`, the pullback along the slice at `z` is the pullback along `f` at
`(s, z)` on the vectors `(0, m i)` (`TauCeti.mpullback_comp_prodMk_apply`). When both factors are
normed spaces with their own models, `𝓘(ℝ, E₁ × E₂)` is not syntactically the product model, so
`TauCeti.mpullback_comp_prodMk_apply_modelSpace` states the same identity for that model.

## Main results

* `TauCeti.mpullback_apply_eq_compContinuousLinearMap`: the pullback at `x` is
  `(φ (f x)).compContinuousLinearMap (mfderiv I I' f x)`.
* `TauCeti.mpullback_apply_eq_of_mfderiv_eq`: the pullback at `x` depends only on the value and
  the differential of the map at `x`.
* `TauCeti.mextDerivₗ_apply_eq_of_eventuallyEq_mpullback`: if a smooth form agrees near `x` with
  `f^* α`, its exterior derivative at `x` is `dα` at `f x` composed with `mfderiv f x`.
* `TauCeti.SmoothForm.exists_mem_nhdsSet_mextDerivₗ_mpullback_eq`: a form exact near `t` pulls
  back along a map from `s` into `t` to a form exact near `s`.
* `TauCeti.mpullback_fun_smul_eq_self`: a form multiplied by a function `ρ` is invariant under a
  map that preserves `ρ`, if the form is so where `ρ` does not vanish.
* `TauCeti.mpullback_neg`: the pullback of `-φ` is minus the pullback of `φ`.
* `TauCeti.SmoothForm.mpullback_const`: the pullback of a smooth `(k + 1)`-form along a constant
  map is `0`.
* `TauCeti.SmoothForm.mpullback_prodMk_left_mpullback_snd`: the slice `x ↦ (x, p)` of the
  pullback of a smooth `(k + 1)`-form along `Prod.snd` is `0`.
* `TauCeti.mpullback_comp_prodMk_apply`: the pullback along a slice `z ↦ f (s, z)` of a map on a
  product, as the pullback along `f` on the vectors `(0, m i)`.
* `TauCeti.mpullback_comp_prodMk_apply_modelSpace`: the same, for a map on a product of normed
  spaces with the model `𝓘(ℝ, E₁ × E₂)`.
* `TauCeti.SmoothForm.contDiff_apply_mfderiv`: along a smooth map `γ` from a normed space, a
  smooth form evaluated on the images under `dγ` of fixed vectors is a smooth function, with
  `TauCeti.SmoothForm.contDiff_apply_one_mfderiv` and
  `TauCeti.SmoothForm.differentiable_apply_one_mfderiv` for one-forms.
-/

public section

open scoped Manifold ContDiff Topology

namespace TauCeti

variable {E H M E' H' M' F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H}
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  [TopologicalSpace M'] [ChartedSpace H' M'] {I' : ModelWithCorners ℝ E' H'}
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

/-- At a point `x`, the pullback of `φ` along `f` is `φ (f x)` composed with the differential of
`f` at `x`, as an alternating map on the tangent space at `x`. -/
theorem mpullback_apply_eq_compContinuousLinearMap (f : M → M') (φ : RoughForm I' M' F k)
    (x : M) :
    mpullback I I' f φ x = (φ (f x)).compContinuousLinearMap (mfderiv I I' f x) :=
  ContinuousAlternatingMap.ext fun v ↦ mpullback_apply f φ x v

/-- Two maps with the same value and the same differential at `x` pull a form back to the same
value at `x`. -/
theorem mpullback_apply_eq_of_mfderiv_eq {f g : M → M'} {x : M} (h : f x = g x)
    (hd : mfderiv I I' f x = mfderiv I I' g x) (φ : RoughForm I' M' F k) :
    mpullback I I' f φ x = mpullback I I' g φ x := by
  rw [mpullback_apply_eq_compContinuousLinearMap, mpullback_apply_eq_compContinuousLinearMap, hd,
    h]

/-- If a smooth form `θ` on `M` agrees near `x` with the pullback `f^* α` of a smooth form `α` on
`M'` along a map `f` that is `C²` at `x`, then the exterior derivative `dθ` at `x` is `dα` at `f x`
composed with the differential of `f` at `x`. -/
theorem mextDerivₗ_apply_eq_of_eventuallyEq_mpullback [IsManifold I 2 M] [IsManifold I' 2 M']
    {f : M → M'} {x : M} (hf : ContMDiffAt I I' 2 f x) {θ : SmoothForm I M F k}
    {α : SmoothForm I' M' F k} (hθ : ∀ᶠ y in 𝓝 x, θ.val y = mpullback I I' f α.val y) :
    (mextDerivₗ I k θ).val x =
      ((mextDerivₗ I' k α).val (f x)).compContinuousLinearMap (mfderiv I I' f x) := by
  rw [mextDerivₗ_apply, mextDerivₗ_apply, mextDeriv_congr_of_eventuallyEq hθ,
    ← mpullback_mextDeriv_at hf ((α.contMDiff _).of_le (by simp)),
    mpullback_apply_eq_compContinuousLinearMap]

/-- Let `f : M → M` preserve `ρ : M → ℝ`, and let the pullback of a form `φ` along `f` agree with
`φ` wherever `ρ` does not vanish. Then the pullback of `ρ • φ` along `f` is `ρ • φ`. -/
theorem mpullback_fun_smul_eq_self {f : M → M} {ρ : M → ℝ} {φ : RoughForm I M F k}
    (hρ : ∀ x, ρ (f x) = ρ x) (hφ : ∀ x, ρ x ≠ 0 → mpullback I I f φ x = φ x) :
    mpullback I I f (fun x ↦ ρ x • φ x) = fun x ↦ ρ x • φ x := by
  rw [mpullback_fun_smul]
  funext x
  rw [hρ]
  by_cases hx : ρ x = 0
  · simp [hx]
  · rw [hφ x hx]

/-- Pullback commutes with negation. -/
@[simp]
theorem mpullback_neg (f : M → M') (φ : RoughForm I' M' F k) :
    mpullback I I' f (-φ) = -mpullback I I' f φ := by
  funext x
  ext v
  simp [mpullback_apply]

/-- Let `f : M × M₂ → M'` be differentiable at `(s, z)`. The pullback of `φ` along the slice
`z ↦ f (s, z)`, at `z` on vectors `m i`, is the pullback of `φ` along `f`, at `(s, z)` on the
vectors `(0, m i)`. -/
theorem mpullback_comp_prodMk_apply {E₂ H₂ M₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
    [TopologicalSpace H₂] [TopologicalSpace M₂] [ChartedSpace H₂ M₂]
    {I₂ : ModelWithCorners ℝ E₂ H₂} {f : M × M₂ → M'} {s : M} {z : M₂}
    (hf : MDifferentiableAt (I.prod I₂) I' f (s, z)) (φ : RoughForm I' M' F k)
    (m : Fin k → TangentSpace I₂ z) :
    mpullback I₂ I' (fun z ↦ f (s, z)) φ z m =
      mpullback (I.prod I₂) I' f φ (s, z) fun i ↦ ((0 : E), m i) := by
  -- The slice is `f ∘ Prod.mk s` by definition.
  refine (DFunLike.congr_fun (mpullback_comp_at (f := Prod.mk s) (g := f)
    (mdifferentiableAt_const.prodMk mdifferentiableAt_id) hf φ) m).trans ?_
  rw [mpullback_apply]
  exact congrArg _ (funext fun i ↦ mfderiv_prodMk_right_apply (m i))

/-- Let `f : E₁ × E₂ → M'`, on a product of normed spaces, be differentiable at `(s, z)` for the
model `𝓘(ℝ, E₁ × E₂)`. The pullback of `φ` along the slice `z ↦ f (s, z)`, at `z` on vectors
`m i`, is the pullback of `φ` along `f`, at `(s, z)` on the vectors `(0, m i)`. -/
theorem mpullback_comp_prodMk_apply_modelSpace {E₁ E₂ : Type*} [NormedAddCommGroup E₁]
    [NormedSpace ℝ E₁] [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] {f : E₁ × E₂ → M'} {s : E₁}
    {z : E₂} (hf : MDifferentiableAt 𝓘(ℝ, E₁ × E₂) I' f (s, z)) (φ : RoughForm I' M' F k)
    (m : Fin k → E₂) :
    mpullback 𝓘(ℝ, E₂) I' (fun z ↦ f (s, z)) φ z m =
      mpullback 𝓘(ℝ, E₁ × E₂) I' f φ (s, z) fun i ↦ ((0 : E₁), m i) := by
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod] at hf ⊢
  exact mpullback_comp_prodMk_apply hf φ m

namespace SmoothForm

variable [IsManifold I 1 M] [IsManifold I' 1 M']

/-- The pullback of a smooth form of positive degree along a constant map is zero. -/
@[simp]
theorem mpullback_const (c : M') (hc : ContMDiff I I' ∞ fun _ : M ↦ c)
    (φ : SmoothForm I' M' F (k + 1)) : mpullback (fun _ : M ↦ c) hc φ = 0 := by
  refine Subtype.ext ?_
  rw [coe_mpullback, TauCeti.mpullback_const k.succ_ne_zero, ZeroMemClass.coe_zero]

/-- The slice `x ↦ (x, p)` of the pullback of a smooth `(k + 1)`-form `β` on `M'` along the
projection `M × M' → M'` is zero, since the projection is constant on the slice. -/
@[simp]
theorem mpullback_prodMk_left_mpullback_snd (p : M') (β : SmoothForm I' M' F (k + 1)) :
    mpullback (fun x : M ↦ (x, p)) (contMDiff_id.prodMk contMDiff_const)
      (mpullback Prod.snd contMDiff_snd β : SmoothForm (I.prod I') (M × M') F (k + 1)) = 0 := by
  simp [mpullback_mpullback, Function.comp_def]

/-- Let `γ : E → M'` be a smooth map from a normed space. Evaluating a smooth `k`-form `η` at
`γ y` on the images under `dγ_y` of fixed vectors `v i` gives a smooth function of `y`. -/
theorem contDiff_apply_mfderiv (η : SmoothForm I' M' F k) {γ : E → M'}
    (hγ : ContMDiff 𝓘(ℝ, E) I' ∞ γ) (v : Fin k → E) :
    ContDiff ℝ ∞ fun y ↦ η.val (γ y) fun i ↦ mfderiv 𝓘(ℝ, E) I' γ y (v i) := by
  have h := isSmoothForm_modelSpace_iff.1 (mpullback γ hγ η).isSmoothForm
  convert (ContinuousAlternatingMap.apply ℝ E F v).contDiff.comp h using 1
  funext y
  exact (mpullback_apply γ hγ η y v).symm

/-- Let `γ : E → M'` be a smooth map from a normed space. Evaluating a smooth one-form `η` at
`γ y` on `dγ_y w`, for a fixed vector `w`, gives a smooth function of `y`. -/
theorem contDiff_apply_one_mfderiv (η : SmoothForm I' M' F 1) {γ : E → M'}
    (hγ : ContMDiff 𝓘(ℝ, E) I' ∞ γ) (w : E) :
    ContDiff ℝ ∞ fun y ↦ η.val (γ y) ![mfderiv 𝓘(ℝ, E) I' γ y w] := by
  convert contDiff_apply_mfderiv η hγ ![w] using 3 with y
  ext i
  fin_cases i
  rfl

/-- Let `γ : E → M'` be a smooth map from a normed space. Evaluating a smooth one-form `η` at
`γ y` on `dγ_y w`, for a fixed vector `w`, gives a differentiable function of `y`. -/
theorem differentiable_apply_one_mfderiv (η : SmoothForm I' M' F 1) {γ : E → M'}
    (hγ : ContMDiff 𝓘(ℝ, E) I' ∞ γ) (w : E) :
    Differentiable ℝ fun y ↦ η.val (γ y) ![mfderiv 𝓘(ℝ, E) I' γ y w] :=
  (contDiff_apply_one_mfderiv η hγ w).differentiable (by simp)

end SmoothForm

namespace SmoothForm

variable [IsManifold I 2 M] [IsManifold I' 2 M']

/-- Let `f` map `s` into `t`. If `dγ` is `τ` on a neighbourhood of `t`, then `d (f^* γ)` is
`f^* τ` on a neighbourhood of `s`: a form exact near `t` pulls back to a form exact near `s`. -/
theorem exists_mem_nhdsSet_mextDerivₗ_mpullback_eq {f : M → M'} (hf : ContMDiff I I' ∞ f)
    {s : Set M} {t : Set M'} (hst : Set.MapsTo f s t) {γ : SmoothForm I' M' F k}
    {τ : SmoothForm I' M' F (k + 1)} {V : Set M'} (hV : V ∈ 𝓝ˢ t)
    (hγ : ∀ y ∈ V, (mextDerivₗ I' k γ).val y = τ.val y) :
    ∃ V' ∈ 𝓝ˢ s, ∀ x ∈ V', (mextDerivₗ I k (mpullback f hf γ)).val x = (mpullback f hf τ).val x :=
  ⟨f ⁻¹' V, hf.continuous.tendsto_nhdsSet hst hV, fun _ hx ↦ by
    rw [mextDerivₗ_mpullback, coe_mpullback, coe_mpullback]
    exact mpullback_apply_congr (hγ _ hx)⟩

end SmoothForm

end TauCeti
