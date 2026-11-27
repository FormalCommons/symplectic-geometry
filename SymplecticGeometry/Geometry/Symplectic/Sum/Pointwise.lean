/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.SmoothFamily.Graph
import TauCeti.Geometry.Symplectic.Manifold.Opens
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Opens
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Pullback.Smooth
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.OpenSubset
public import Mathlib.Geometry.Manifold.Instances.Sphere
public import TauCeti.Geometry.Manifold.ConnectedSum.Basic
import SymplecticGeometry.Geometry.Manifold.ConnectedSum.ComplementaryBall
import TauCeti.Geometry.Euclidean.Inversion

/-!
# Nondegenerate forms that follow a homotopy outside a ball

This file holds the pointwise obstruction to symplectic connected sums
[McDuffSalamon2017, Lemma 7.2.2], up to the input about almost complex structures on spheres.

Its one-chart step: a nondegenerate two-form `η` near a ball is joined, through a
homotopy `β` of nondegenerate forms on the complement of a smaller ball ending at `η`, to the
start `β 0` of the homotopy far out. The form is `η` near the ball and, on the complement, the
slice `SymplecticGeometry.IsSmoothFamily.sliceAlong` of `β` along a cut-off function of the
point.

## Main results

* `SymplecticGeometry.exists_isNondegenerate_eq_sliceAlong`: on a manifold covered by open sets
  `W` and `V`, for a nondegenerate form `η`, a smooth family `β` of two-forms on `V`,
  nondegenerate for `t ∈ [0, 1]`, with `β 1` the restriction of `η`, and a smooth
  `χ : V → [0, 1]` equal to `1` on `W`, there is a nondegenerate form equal to `η` on `W` whose
  restriction to `V` is the slice of `β` along `χ`.
* `SymplecticGeometry.exists_isNondegenerate_eq_of_lt_norm`: on a real normed space
  with smooth bump functions, such as a finite-dimensional one, with `0 ≤ ρ < R`,
  `V` containing `{w | ρ < ‖w‖}` and `β` as above, there is a nondegenerate form equal
  to `η` near the closed ball of radius `ρ` and to `β 0` where `R < ‖w‖`. The
  cut-off is a `ContDiffBump` between two radii in `(ρ, R)`.
* `SymplecticGeometry.exists_isNondegenerate_sphere_of_connectedSum`: a two-form `σ` on the
  connected sum `TauCeti.ConnectedSum e₁ e₂` of two `2n`-manifolds with nondegenerate forms
  `α₁`, `α₂`, joined to `αᵢ` on each punctured summand, outside the balls of radius `ρᵢ`
  with `ρ₁ * ρ₂ < 1`, by a homotopy of nondegenerate forms, gives a nondegenerate two-form on
  the round sphere of dimension `2n`. In the chart `eᵢ` the one-chart step gives a
  nondegenerate form that is the pull-back of `σ` beyond a radius `Rᵢ > ρᵢ`, where
  `R₁ * R₂ < 1`. Since `inl (e₁ w) = inr (e₂ (inversion 0 1 w))` for `w ≠ 0`, the two forms
  correspond through the inversion on the shell `R₁ < ‖w‖ < R₂⁻¹`, and
  `TauCeti.IsComplementaryBall.exists_isNondegenerate_mpullback_eq` glues them along the
  stereographic balls `TauCeti.sphereBall v` and `w ↦ -TauCeti.sphereBall v (-w)`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §7.2
  (Lemma 7.2.2).
-/

public section

noncomputable section

open Set Filter TopologicalSpace Metric TauCeti
open scoped Manifold ContDiff Topology

namespace SymplecticGeometry

section Manifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Let `M` be covered by an open set `W` and an open set `V`. Take a nondegenerate
two-form `η` on `M`, and let `β` be a smooth family of two-forms on `V` over `ℝ`,
nondegenerate for `t ∈ [0, 1]`, with `β 1` the restriction of `η` to `V`. For a smooth
`χ : V → [0, 1]` equal to `1` at the points of `W`, there is a nondegenerate two-form on `M` that
is `η` on `W` and whose restriction to `V` is the slice of `β` along `χ`. -/
theorem exists_isNondegenerate_eq_sliceAlong {V : Opens M} {W : Set M} (hW : IsOpen W)
    (hWV : W ∪ V = univ) {η : SmoothTwoForm I M} (hη : η.IsNondegenerate)
    {β : ℝ → SmoothTwoForm I V} (hβ : IsSmoothFamily 𝓘(ℝ, ℝ) β)
    (hβ₁ : β 1 = SmoothForm.mpullback Subtype.val contMDiff_subtypeVal η)
    (hβnd : ∀ t ∈ Icc (0 : ℝ) 1, (β t).IsNondegenerate) {χ : V → ℝ}
    (hχ : ContMDiff I 𝓘(ℝ, ℝ) ∞ χ) (hχI : ∀ x, χ x ∈ Icc (0 : ℝ) 1)
    (hχW : ∀ x : V, (x : M) ∈ W → χ x = 1) :
    ∃ τ : SmoothTwoForm I M, τ.IsNondegenerate ∧ (∀ x ∈ W, τ.val x = η.val x) ∧
      SmoothForm.mpullback Subtype.val contMDiff_subtypeVal τ = hβ.sliceAlong χ hχ := by
  classical
  set σ := hβ.sliceAlong χ hχ
  -- On `V ∩ W` the slice is `β 1`, the restriction of `η`.
  have hσ : ∀ x : V, (x : M) ∈ W → σ.val x = η.val x := fun x hx ↦ by
    rw [IsSmoothFamily.sliceAlong_val, hχW x hx, hβ₁, SmoothForm.coe_mpullback,
      mpullback_subtype_val_apply]
  let γ : RoughForm I M ℝ 2 := fun y ↦ if hy : y ∈ V then σ.val ⟨y, hy⟩ else η.val y
  have hγW : ∀ y ∈ W, γ y = η.val y := fun y hyW ↦ by
    by_cases hy : y ∈ V
    · exact (dite_eq_left hy).trans (hσ ⟨y, hy⟩ hyW)
    · exact dite_eq_right hy
  have hγV : mpullback I I (Subtype.val : V → M) γ = σ.val :=
    funext fun x ↦ (mpullback_subtype_val_apply γ x).trans (dite_eq_left x.property)
  have hγ : IsSmoothForm I ∞ γ := by
    rw [isSmoothForm_def]
    intro y
    by_cases hy : y ∈ V
    · exact (contMDiffAt_mpullback_subtype_val_iff γ ⟨y, hy⟩).1 (hγV ▸ σ.contMDiff ⟨y, hy⟩)
    · have hyW : y ∈ W := (hWV.symm.subset (mem_univ y)).resolve_right hy
      refine (η.contMDiff y).congr_of_eventuallyEq ?_
      filter_upwards [hW.mem_nhds hyW] with z hz
      rw [hγW z hz]
  let τ : SmoothTwoForm I M := ⟨γ, hγ.mem_smoothBundleForms⟩
  have hτV : SmoothForm.mpullback Subtype.val contMDiff_subtypeVal τ = σ :=
    (SmoothForm.mpullback_eq_iff _).2 hγV
  have hnd : ∀ y, (τ.bilinFormAt y).Nondegenerate := fun y ↦ by
    by_cases hy : y ∈ V
    · have hσnd : SmoothTwoForm.IsNondegenerate σ := hβ.isNondegenerate_sliceAlong hχ hχI hβnd
      exact (SmoothTwoForm.nondegenerate_bilinFormAt_mpullback_subtype_val_iff ⟨y, hy⟩).1
        (hτV ▸ hσnd.nondegenerate_bilinFormAt ⟨y, hy⟩)
    · have hyW : y ∈ W := (hWV.symm.subset (mem_univ y)).resolve_right hy
      have : τ.bilinFormAt y = η.bilinFormAt y := LinearMap.ext₂ fun v w ↦ by
        rw [SmoothForm.bilinFormAt_apply, SmoothForm.bilinFormAt_apply,
          SmoothBundleForm.eval₂_apply, SmoothBundleForm.eval₂_apply]
        exact congrArg (fun a ↦ a ![v, w]) (hγW y hyW)
      exact this ▸ hη.nondegenerate_bilinFormAt y
  exact ⟨τ, SmoothTwoForm.isNondegenerate_iff_forall_ker_bilinFormAt_eq_bot.2 fun y ↦
    (hnd y).ker_eq_bot, hγW, hτV⟩

end Manifold

section BumpFunction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [HasContDiffBump E]

/-- Let `0 ≤ ρ < R` and let `V` be an open set in a real normed space `E` with smooth bump
functions (`HasContDiffBump E`, as for every finite-dimensional `E`) that contains every `w`
with `ρ < ‖w‖`. Let `η` be a nondegenerate two-form on `E`, and
`β` a smooth family of two-forms on `V` over `ℝ`, nondegenerate for `t ∈ [0, 1]`, with `β 1` the
restriction of `η` to `V`. Then there is a nondegenerate two-form on `E` equal to `η` near the
closed ball of radius `ρ` and whose restriction to `V` is `β 0` at the points with
`R < ‖w‖`. -/
theorem exists_isNondegenerate_eq_of_lt_norm {ρ R : ℝ} (hρ : 0 ≤ ρ) (hρR : ρ < R)
    {V : Opens E} (hV : ∀ w, ρ < ‖w‖ → w ∈ V) {η : SmoothTwoForm 𝓘(ℝ, E) E}
    (hη : η.IsNondegenerate) {β : ℝ → SmoothTwoForm 𝓘(ℝ, E) V}
    (hβ : IsSmoothFamily 𝓘(ℝ, ℝ) β)
    (hβ₁ : β 1 = SmoothForm.mpullback Subtype.val contMDiff_subtypeVal η)
    (hβnd : ∀ t ∈ Icc (0 : ℝ) 1, (β t).IsNondegenerate) :
    ∃ τ : SmoothTwoForm 𝓘(ℝ, E) E, τ.IsNondegenerate ∧
      (∀ᶠ x in 𝓝ˢ (closedBall (0 : E) ρ), τ.val x = η.val x) ∧
      ∀ x : V, R < ‖(x : E)‖ →
        (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal τ).val x = (β 0).val x := by
  -- A bump function equal to `1` within `(2ρ + R) / 3` and `0` from `R` on.
  let f : ContDiffBump (0 : E) :=
    ⟨(2 * ρ + R) / 3, R, by linarith, by linarith⟩
  have hχ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (fun x : V ↦ f x) :=
    f.contDiff.contMDiff.comp contMDiff_subtypeVal
  have hball : IsOpen (ball (0 : E) ((2 * ρ + R) / 3)) := isOpen_ball
  obtain ⟨τ, hτ, hτW, hτV⟩ := exists_isNondegenerate_eq_sliceAlong hball
    (eq_univ_of_forall fun w ↦ by
      by_cases hw : ‖w‖ < (2 * ρ + R) / 3
      · exact Or.inl (mem_ball_zero_iff.2 hw)
      · exact Or.inr (hV w (by linarith [not_lt.1 hw])))
    hη hβ hβ₁ hβnd hχ (fun x ↦ ⟨f.nonneg, f.le_one⟩)
    (fun x hx ↦ f.one_of_mem_closedBall (ball_subset_closedBall hx))
  refine ⟨τ, hτ, ?_, fun x hx ↦ ?_⟩
  · refine eventually_of_mem (hball.mem_nhdsSet.2 (closedBall_subset_ball ?_)) hτW
    linarith
  · have h0 : f x = 0 := f.zero_of_le_dist (by rw [dist_zero_right]; exact hx.le)
    rw [hτV, IsSmoothFamily.sliceAlong_val]
    simp only [h0]

end BumpFunction

section Chart

variable {E H M X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [HasContDiffBump E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]

/-- The chart step of `exists_isNondegenerate_sphere_of_connectedSum`, read through a coordinate
ball `e : E → M`: a homotopy `β` on `V ⊆ M` from the pull-back of `σ` along `g : V → X` to `α`
gives a nondegenerate form on `E` which, beyond the radius `R`, is the pull-back of `σ` along any
map `G : E → X` that is `g ∘ e` where `e` lands in `V`. -/
private theorem exists_isNondegenerate_chart {e : E → M} (de : IsLocalDiffeomorph 𝓘(ℝ, E) I ∞ e)
    {V : Opens M} {ρ R : ℝ} (hρ : 0 ≤ ρ) (hρR : ρ < R) (hV : ∀ w, ρ < ‖w‖ → e w ∈ V)
    {α : SmoothTwoForm I M} (hα : α.IsNondegenerate) (σ : SmoothTwoForm I X) {g : V → X}
    (hg : ContMDiff I I ∞ g) {β : ℝ → SmoothTwoForm I V} (hβ : IsSmoothFamily 𝓘(ℝ, ℝ) β)
    (hβnd : ∀ t ∈ Icc (0 : ℝ) 1, (β t).IsNondegenerate)
    (hβ₀ : β 0 = SmoothForm.mpullback g hg σ)
    (hβ₁ : β 1 = SmoothForm.mpullback Subtype.val contMDiff_subtypeVal α) :
    ∃ τ : SmoothTwoForm 𝓘(ℝ, E) E, τ.IsNondegenerate ∧
      ∀ G : E → X, (∀ w (hw : e w ∈ V), G w = g ⟨e w, hw⟩) → ∀ w, R < ‖w‖ →
        ContMDiffAt 𝓘(ℝ, E) I ∞ G w ∧ τ.val w = mpullback 𝓘(ℝ, E) I G σ.val w := by
  let W : Opens E := ⟨{w | ρ < ‖w‖}, isOpen_lt continuous_const continuous_norm⟩
  -- The ball `e` on `W`, as a map into `V`.
  let k : W → V := fun x ↦ ⟨e x, hV x x.property⟩
  have hvk : Subtype.val ∘ k = e ∘ Subtype.val := rfl
  have dk : IsLocalDiffeomorph 𝓘(ℝ, E) I ∞ k := TauCeti.isLocalDiffeomorph_subtypeVal_comp_iff.1
    (hvk ▸ fun x ↦ (TauCeti.isLocalDiffeomorph_subtype_val x).comp (hg := de x))
  have hk : ContMDiff 𝓘(ℝ, E) I ∞ k := dk.contMDiff
  obtain ⟨τ, hτ, -, hτR⟩ := exists_isNondegenerate_eq_of_lt_norm hρ hρR (V := W)
    (fun w hw ↦ hw) (hα.isNondegenerate_mpullback_of_isLocalDiffeomorph de)
    (hβ.mpullback k hk)
    (by rw [hβ₁]; exact SmoothForm.mpullback_mpullback_of_comp_eq _ _ _ _ hvk α)
    (fun t ht ↦ (hβnd t ht).isNondegenerate_mpullback_of_isLocalDiffeomorph dk)
  refine ⟨τ, hτ, fun G hG w hw ↦ ?_⟩
  have hwW : w ∈ W := hρR.trans hw
  have hGk : (fun x : W ↦ G x) = g ∘ k := funext fun x ↦ hG x _
  have hGw : ContMDiffAt 𝓘(ℝ, E) I ∞ G w :=
    contMDiffAt_subtype_iff (x := ⟨w, hwW⟩) |>.1 (hGk ▸ (hg.comp hk) _)
  refine ⟨hGw, ?_⟩
  have h := hτR ⟨w, hwW⟩ hw
  rw [SmoothForm.coe_mpullback, mpullback_subtype_val_apply, hβ₀,
    SmoothForm.mpullback_mpullback, SmoothForm.coe_mpullback, ← hGk] at h
  -- The restriction of `G` to `W` is `G ∘ Subtype.val`, by definition of composition.
  rw [h, show (fun x : W ↦ G x) = G ∘ Subtype.val from rfl,
    mpullback_comp_at ((contMDiff_subtypeVal (n := 1)).mdifferentiableAt one_ne_zero)
      (hGw.mdifferentiableAt (by simp)), mpullback_subtype_val_apply]

end Chart

section ConnectedSum

open ConnectedSum EuclideanGeometry

variable {n : ℕ} {H M₁ M₂ : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin (2 * n))) H}
  [TopologicalSpace M₁] [T1Space M₁] [ChartedSpace H M₁] [IsManifold I ∞ M₁]
  [TopologicalSpace M₂] [T1Space M₂] [ChartedSpace H M₂] [IsManifold I ∞ M₂]
  {e₁ : EuclideanSpace ℝ (Fin (2 * n)) → M₁} {e₂ : EuclideanSpace ℝ (Fin (2 * n)) → M₂}
  [ChartedSpace H (ConnectedSum e₁ e₂)] [IsManifold I ∞ (ConnectedSum e₁ e₂)]

/-- **A nondegenerate two-form on the sphere from one on a connected sum.** Let
`E = EuclideanSpace ℝ (Fin (2 * n))` and let `e₁ : E → M₁`, `e₂ : E → M₂` be coordinate balls
which are smooth local diffeomorphisms. Give the connected sum `TauCeti.ConnectedSum e₁ e₂` a
manifold structure for which `inl` and `inr` are smooth, such as Tau Ceti's
`TauCeti.ConnectedSum.chartedSpace` with `TauCeti.ConnectedSum.isManifold`. Let `α₁`, `α₂` be
nondegenerate two-forms on `M₁`, `M₂`, let `σ` be a two-form on the connected sum, and let
`0 < ρ₁`, `0 < ρ₂` with `ρ₁ * ρ₂ < 1`. For `i = 1, 2`, let `Vᵢ` be an open subset of the
punctured summand `Mᵢ ∖ {eᵢ 0}` that contains `eᵢ w` whenever `ρᵢ < ‖w‖`, such as
`Mᵢ ∖ eᵢ '' closedBall 0 ρᵢ`, and let `βᵢ` be a smooth family of two-forms on `Vᵢ`, nondegenerate
for `t ∈ [0, 1]`, with `βᵢ 0` the pull-back of `σ` along `inl` (for `i = 1`) or `inr` (for
`i = 2`) and `βᵢ 1` the restriction of `αᵢ`. Then the round sphere of dimension `2 * n`
carries a nondegenerate two-form.

Only `β₁ 0` and `β₂ 0` see `σ`, so `σ` need not be assumed nondegenerate. -/
theorem exists_isNondegenerate_sphere_of_connectedSum
    (d₁ : IsLocalDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * n))) I ∞ e₁)
    (d₂ : IsLocalDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * n))) I ∞ e₂)
    (hinl : ContMDiff I I ∞ (inl e₁ e₂)) (hinr : ContMDiff I I ∞ (inr e₁ e₂))
    {ρ₁ ρ₂ : ℝ} (hρ₁ : 0 < ρ₁) (hρ₂ : 0 < ρ₂) (hρ : ρ₁ * ρ₂ < 1)
    {α₁ : SmoothTwoForm I M₁} {α₂ : SmoothTwoForm I M₂} (hα₁ : α₁.IsNondegenerate)
    (hα₂ : α₂.IsNondegenerate) (σ : SmoothTwoForm I (ConnectedSum e₁ e₂))
    {V₁ : Opens M₁} {V₂ : Opens M₂} (hV₁ : V₁ ≤ puncture e₁) (hV₂ : V₂ ≤ puncture e₂)
    (hρV₁ : ∀ w, ρ₁ < ‖w‖ → e₁ w ∈ V₁) (hρV₂ : ∀ w, ρ₂ < ‖w‖ → e₂ w ∈ V₂)
    {β₁ : ℝ → SmoothTwoForm I V₁} {β₂ : ℝ → SmoothTwoForm I V₂}
    (hβ₁ : IsSmoothFamily 𝓘(ℝ, ℝ) β₁) (hβ₂ : IsSmoothFamily 𝓘(ℝ, ℝ) β₂)
    (hβ₁nd : ∀ t ∈ Icc (0 : ℝ) 1, (β₁ t).IsNondegenerate)
    (hβ₂nd : ∀ t ∈ Icc (0 : ℝ) 1, (β₂ t).IsNondegenerate)
    (hβ₁₀ : β₁ 0 = SmoothForm.mpullback (inl e₁ e₂ ∘ Opens.inclusion hV₁)
      (hinl.comp (contMDiff_inclusion hV₁)) σ)
    (hβ₂₀ : β₂ 0 = SmoothForm.mpullback (inr e₁ e₂ ∘ Opens.inclusion hV₂)
      (hinr.comp (contMDiff_inclusion hV₂)) σ)
    (hβ₁₁ : β₁ 1 = SmoothForm.mpullback Subtype.val contMDiff_subtypeVal α₁)
    (hβ₂₁ : β₂ 1 = SmoothForm.mpullback Subtype.val contMDiff_subtypeVal α₂) :
    ∃ α : SmoothTwoForm (𝓡 (2 * n)) (sphere (0 : EuclideanSpace ℝ (Fin (2 * n + 1))) 1),
      α.IsNondegenerate := by
  classical
  -- Radii `ρ₁ < R₁` and `ρ₂ < R₂` with `R₁ * R₂ < 1`.
  obtain ⟨R₁, hρR₁, hR₁⟩ := exists_between (show ρ₁ < ρ₂⁻¹ by
    rw [lt_inv_comm₀ hρ₁ hρ₂, inv_eq_one_div, lt_div_iff₀ hρ₁, mul_comm]; exact hρ)
  have hR₁0 : 0 < R₁ := hρ₁.trans hρR₁
  obtain ⟨R₂, hρR₂, hR₂⟩ := exists_between ((lt_inv_comm₀ hR₁0 hρ₂).1 hR₁)
  have hR₂0 : 0 < R₂ := hρ₂.trans hρR₂
  have hR : R₁ * R₂ < 1 := by
    have := mul_lt_mul_of_pos_left hR₂ hR₁0
    rwa [mul_inv_cancel₀ hR₁0.ne'] at this
  obtain ⟨τ₁, hτ₁, hG₁⟩ := exists_isNondegenerate_chart d₁ hρ₁.le hρR₁ hρV₁ hα₁ σ _ hβ₁ hβ₁nd
    hβ₁₀ hβ₁₁
  obtain ⟨τ₂, hτ₂, hG₂⟩ := exists_isNondegenerate_chart d₂ hρ₂.le hρR₂ hρV₂ hα₂ σ _ hβ₂ hβ₂nd
    hβ₂₀ hβ₂₁
  have : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (2 * n + 1))) = 2 * n + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  let v : sphere (0 : EuclideanSpace ℝ (Fin (2 * n + 1))) 1 :=
    ⟨EuclideanSpace.single 0 1, by simp⟩
  -- On the shell, `τ₁` and `τ₂` are both read from `σ`, through `w ↦ inl (e₁ w)` and
  -- `w ↦ inr (e₂ w)`, which the inversion relates.
  have hshell : ∀ w : EuclideanSpace ℝ (Fin (2 * n)), R₁ < ‖w‖ → ‖w‖ < R₂⁻¹ →
      mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * n))) 𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * n)))
        (inversion 0 1) τ₂.val w = τ₁.val w := by
    intro w hw₁ hw₂
    have hw : ρ₁ < ‖w‖ := hρR₁.trans hw₁
    let p : ConnectedSum e₁ e₂ := inl e₁ e₂ ⟨e₁ w, hV₁ (hρV₁ w hw)⟩
    let G₁ : EuclideanSpace ℝ (Fin (2 * n)) → ConnectedSum e₁ e₂ := fun y ↦
      if hy : e₁ y ∈ V₁ then inl e₁ e₂ ⟨e₁ y, hV₁ hy⟩ else p
    let G₂ : EuclideanSpace ℝ (Fin (2 * n)) → ConnectedSum e₁ e₂ := fun y ↦
      if hy : e₂ y ∈ V₂ then inr e₁ e₂ ⟨e₂ y, hV₂ hy⟩ else p
    have hw0 : w ≠ 0 := norm_pos_iff.1 (hρ₁.trans hw)
    have hiw : R₂ < ‖inversion (0 : EuclideanSpace ℝ (Fin (2 * n))) 1 w‖ := by
      rw [norm_inversion_zero_one]
      exact lt_inv_of_lt_inv₀ (norm_pos_iff.2 hw0) hw₂
    obtain ⟨-, h₁⟩ := hG₁ G₁ (fun y hy ↦ dite_eq_left hy) w hw₁
    obtain ⟨hG₂d, h₂⟩ := hG₂ G₂ (fun y hy ↦ dite_eq_left hy) _ hiw
    have hev : G₂ ∘ inversion 0 1 =ᶠ[𝓝 w] G₁ := by
      have hs : IsOpen {y : EuclideanSpace ℝ (Fin (2 * n)) | ρ₁ < ‖y‖ ∧ ‖y‖ < ρ₂⁻¹} :=
        (isOpen_lt continuous_const continuous_norm).inter
          (isOpen_lt continuous_norm continuous_const)
      filter_upwards [hs.mem_nhds ⟨hw, hw₂.trans (inv_strictAnti₀ hρ₂ hρR₂)⟩] with y ⟨hy₁, hy₂⟩
      have hy0 : y ≠ 0 := norm_pos_iff.1 (hρ₁.trans hy₁)
      have hiy : ρ₂ < ‖inversion (0 : EuclideanSpace ℝ (Fin (2 * n))) 1 y‖ := by
        rw [norm_inversion_zero_one]
        exact lt_inv_of_lt_inv₀ (norm_pos_iff.2 hy0) hy₂
      simp only [Function.comp_apply, G₁, G₂, dite_eq_left (hρV₁ y hy₁), dite_eq_left (hρV₂ _ hiy)]
      exact (inl_eq_inr y _ _).symm
    have hinvd : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * n)))
        𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * n))) (inversion 0 1) w :=
      mdifferentiableAt_iff_differentiableAt.2
        ((contDiffAt_inversion (n := 1) hw0).differentiableAt one_ne_zero)
    rw [h₁, ← hev.mpullback_eq, mpullback_comp_at hinvd (hG₂d.mdifferentiableAt (by simp))]
    exact mpullback_apply_congr h₂
  obtain ⟨α, hα, -⟩ := (isComplementaryBall_sphereBall v).exists_isNondegenerate_mpullback_eq
    (isLocalDiffeomorph_sphereBall v ∞) (isLocalDiffeomorph_neg_sphereBall_neg v ∞) hR₁0 hR₂0 hR
    hτ₁ hτ₂ hshell
  exact ⟨α, hα⟩

end ConnectedSum

end SymplecticGeometry

end
