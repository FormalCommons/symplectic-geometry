/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.ConnectedSum.Oriented
public import TauCeti.Geometry.Manifold.ConnectedSum.Orientation
import TauCeti.Analysis.InnerProductSpace.Reflection
import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Orientation
import TauCeti.Geometry.Euclidean.Inversion
import TauCeti.Geometry.Manifold.SmoothEmbedding.LocalDiffeomorph

/-!
# Test
-/

public section

noncomputable section

open Set Filter Function Topology TopologicalSpace Metric EuclideanGeometry
open scoped Manifold ContDiff

namespace TauCeti.SmoothEmbedding

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {ι : Type*} [Fintype ι]

/-- On a connected oriented manifold, two smooth embeddings of `E` which preserve the orientations
`o` of `E` and `oM` of `M` at the origin agree near the origin after an orientation-preserving
diffeomorphism of `M`. -/
theorem exists_diffeomorph_comp_eventuallyEq_and_isOrientationPreservingAt [T2Space M]
    [PreconnectedSpace M] (f g : SmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ E M)
    (o : Manifold.Orientation 𝓘(ℝ, E) E ι) (oM : Manifold.Orientation 𝓘(ℝ, E) M ι)
    (hf : o.IsOrientationPreservingAt oM f 0) (hg : o.IsOrientationPreservingAt oM g 0) :
    ∃ φ : M ≃ₘ^∞⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ M, φ ∘ f =ᶠ[𝓝 0] g ∧
      ∀ x, oM.IsOrientationPreservingAt oM φ x := by
  obtain ⟨Φ, -, -, -, hΦ⟩ := f.exists_diffeotopy_eqOn_of_isOrientationPreservingAt g o oM hf hg
    (isCompact_closedBall (0 : E) 1)
  exact ⟨Φ.final, hΦ.eventuallyEq_of_mem (closedBall_mem_nhds 0 one_pos),
    Φ.isOrientationPreservingAt_final (by simp) oM⟩

end TauCeti.SmoothEmbedding

namespace TauCeti.ConnectedSum

open Manifold.Orientation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T1Space M] [ChartedSpace H M] [IsManifold I 1 M]
  {N : Type*} [TopologicalSpace N] [T1Space N] [ChartedSpace H N] [IsManifold I 1 N]
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I 1 X]
  {e₁ : E → M} {e₂ : E → N} {ι : Type*} [Fintype ι]
  {h₁ : IsOpenEmbedding e₁} {h₂ : IsOpenEmbedding e₂}
  {d₁ : IsLocalDiffeomorph 𝓘(ℝ, E) I 1 e₁} {d₂ : IsLocalDiffeomorph 𝓘(ℝ, E) I 1 e₂}
  {o₁ : Manifold.Orientation I M ι} {o₂ : Manifold.Orientation I N ι}
  {oE : Manifold.Orientation 𝓘(ℝ, E) E ι}
  {he₁ : ∀ v ≠ 0, IsOrientationPreservingAt oE o₁ e₁ v}
  {he₂ : ∀ v ≠ 0, IsOrientationReversingAt oE o₂ e₂ v}

private local instance : NeZero ((1 : ℕ∞) : WithTop ℕ∞) := ⟨one_ne_zero⟩

omit [FiniteDimensional ℝ E] in
/-- Every point of the connected sum lies in the first punctured summand, or is a point of the
second punctured summand outside the image of a given closed ball. -/
theorem exists_eq_inl_or_exists_eq_inr_of_notMem_image_closedBall (he₁ : Injective e₁) (r : ℝ)
    (p : ConnectedSum e₁ e₂) :
    (∃ x, inl e₁ e₂ x = p) ∨ ∃ y : puncture e₂, (y : N) ∉ e₂ '' closedBall 0 r ∧
      inr e₁ e₂ y = p := by
  obtain ⟨x | ⟨y, hy⟩, rfl⟩ := mk_surjective e₁ e₂ p
  · exact .inl ⟨x, (mk_inl e₁ e₂ x).symm⟩
  by_cases hyr : y ∈ e₂ '' closedBall 0 r
  · obtain ⟨w, -, rfl⟩ := hyr
    exact .inl ⟨⟨e₁ (inversion 0 1 w),
      apply_inversion_mem_puncture he₁ (ne_zero_of_apply_mem_puncture hy)⟩,
      (inl_inversion_eq_inr _ hy).trans (mk_inr e₁ e₂ _).symm⟩
  · exact .inr ⟨⟨y, hy⟩, hyr, (mk_inr e₁ e₂ _).symm⟩

/-- A local diffeomorphism `f` from the oriented connected sum to an oriented manifold `X`
preserves orientation everywhere once its composite with the inclusion of the punctured first
summand does, and its composite with the inclusion of the punctured second summand does outside the
image of a closed ball under `e₂`. -/
theorem isOrientationPreservingAt_of_comp_inl_of_comp_inr
    {f : letI := chartedSpace (H := H) h₁ h₂; ConnectedSum e₁ e₂ → X}
    (hf : letI := chartedSpace (H := H) h₁ h₂; IsLocalDiffeomorph I I 1 f)
    (o : Manifold.Orientation I X ι) (r : ℝ)
    (hl : letI := chartedSpace (H := H) h₁ h₂
      haveI := isManifold (n := 1) h₁ h₂ d₁ d₂
      ∀ x, IsOrientationPreservingAt (o₁.restrict (puncture e₁)) o (f ∘ inl e₁ e₂) x)
    (hr : letI := chartedSpace (H := H) h₁ h₂
      haveI := isManifold (n := 1) h₁ h₂ d₁ d₂
      ∀ y : puncture e₂, (y : N) ∉ e₂ '' closedBall 0 r →
        IsOrientationPreservingAt (o₂.restrict (puncture e₂)) o (f ∘ inr e₁ e₂) y)
    (p : ConnectedSum e₁ e₂) :
    letI := chartedSpace (H := H) h₁ h₂
    haveI := isManifold (n := 1) h₁ h₂ d₁ d₂
    IsOrientationPreservingAt (orientation h₁ h₂ d₁ d₂ o₁ o₂ oE he₁ he₂) o f p := by
  let := chartedSpace (H := H) h₁ h₂
  have := isManifold (n := 1) h₁ h₂ d₁ d₂
  let o' := o.pullback hf.contMDiff (fun p ↦ (hf p).isInvertible_mfderiv one_ne_zero) o.card_eq
  suffices orientation h₁ h₂ d₁ d₂ o₁ o₂ oE he₁ he₂ = o' from
    this ▸ isOrientationPreservingAt_pullback _ _ _ _ p
  ext q
  obtain ⟨x, rfl⟩ | ⟨y, hy, rfl⟩ :=
    exists_eq_inl_or_exists_eq_inr_of_notMem_image_closedBall h₁.injective r q
  · exact (isOrientationPreservingAt_inl h₁ h₂ d₁ d₂ he₁ he₂
      (isOrientationPreservingAt_restrict o₁ _ x)).orientationAt_eq
      ((isOrientationPreservingAt_pullback _ _ _ _ _).of_comp (hl x)
        ((isLocalDiffeomorph_inl h₁ h₂ d₁ d₂ x).mdifferentiableAt one_ne_zero))
  · exact (isOrientationPreservingAt_inr h₁ h₂ d₁ d₂ he₁ he₂
      (isOrientationPreservingAt_restrict o₂ _ y)).orientationAt_eq
      ((isOrientationPreservingAt_pullback _ _ _ _ _).of_comp (hr y hy)
        ((isLocalDiffeomorph_inr h₁ h₂ d₁ d₂ y).mdifferentiableAt one_ne_zero))

include he₁ he₂ in
/-- The exchange of the summands preserves the orientations of the two connected sums. -/
theorem isOrientationPreservingAt_commHomeomorph {oE' : Manifold.Orientation 𝓘(ℝ, E) E ι}
    {he₂' : ∀ v ≠ 0, IsOrientationPreservingAt oE' o₂ e₂ v}
    {he₁' : ∀ v ≠ 0, IsOrientationReversingAt oE' o₁ e₁ v} (p : ConnectedSum e₁ e₂) :
    letI := chartedSpace (H := H) h₁ h₂
    letI := chartedSpace (H := H) h₂ h₁
    haveI := isManifold (n := 1) h₁ h₂ d₁ d₂
    haveI := isManifold (n := 1) h₂ h₁ d₂ d₁
    IsOrientationPreservingAt (orientation h₁ h₂ d₁ d₂ o₁ o₂ oE he₁ he₂)
      (orientation h₂ h₁ d₂ d₁ o₂ o₁ oE' he₂' he₁') (commHomeomorph e₁ e₂) p := by
  let := chartedSpace (H := H) h₁ h₂
  let := chartedSpace (H := H) h₂ h₁
  have := isManifold (n := 1) h₁ h₂ d₁ d₂
  have := isManifold (n := 1) h₂ h₁ d₂ d₁
  rw [← coe_commDiffeomorph (n := 1) h₁ h₂ d₁ d₂]
  refine isOrientationPreservingAt_of_comp_inl_of_comp_inr (d₁ := d₁) (d₂ := d₂) (he₁ := he₁)
    (he₂ := he₂)
    (commDiffeomorph h₁ h₂ d₁ d₂).isLocalDiffeomorph
    (orientation h₂ h₁ d₂ d₁ o₂ o₁ oE' he₂' he₁') 0 (fun x ↦ ?_) (fun y _ ↦ ?_) p
  · have : commHomeomorph e₁ e₂ ∘ inl e₁ e₂ = inr e₂ e₁ := funext (commHomeomorph_inl e₁ e₂)
    rw [coe_commDiffeomorph, this]
    exact isOrientationPreservingAt_inr h₂ h₁ d₂ d₁ he₂' he₁'
      (isOrientationPreservingAt_restrict o₁ _ x)
  · have : commHomeomorph e₁ e₂ ∘ inr e₁ e₂ = inl e₂ e₁ := funext (commHomeomorph_inr e₁ e₂)
    rw [coe_commDiffeomorph, this]
    exact isOrientationPreservingAt_inl h₂ h₁ d₂ d₁ he₂' he₁'
      (isOrientationPreservingAt_restrict o₂ _ y)

include he₁ he₂ in
/-- Rotating both balls by a linear isometry of `E` preserves the orientations of the two
connected sums. -/
theorem isOrientationPreservingAt_compLinearIsometryEquivHomeomorph (R : E ≃ₗᵢ[ℝ] E)
    {oE' : Manifold.Orientation 𝓘(ℝ, E) E ι}
    {he₁' : ∀ v ≠ 0, IsOrientationPreservingAt oE' o₁ (e₁ ∘ R) v}
    {he₂' : ∀ v ≠ 0, IsOrientationReversingAt oE' o₂ (e₂ ∘ R) v} (p : ConnectedSum e₁ e₂) :
    letI := chartedSpace (H := H) h₁ h₂
    letI := chartedSpace (H := H) (h₁.comp_linearIsometryEquiv R) (h₂.comp_linearIsometryEquiv R)
    haveI := isManifold (n := 1) h₁ h₂ d₁ d₂
    haveI := isManifold (n := 1) (h₁.comp_linearIsometryEquiv R) (h₂.comp_linearIsometryEquiv R)
      (d₁.comp_linearIsometryEquiv R) (d₂.comp_linearIsometryEquiv R)
    IsOrientationPreservingAt (orientation h₁ h₂ d₁ d₂ o₁ o₂ oE he₁ he₂)
      (orientation (h₁.comp_linearIsometryEquiv R) (h₂.comp_linearIsometryEquiv R)
        (d₁.comp_linearIsometryEquiv R) (d₂.comp_linearIsometryEquiv R) o₁ o₂ oE' he₁' he₂')
      (compLinearIsometryEquivHomeomorph R e₁ e₂) p := by
  let h₁R := h₁.comp_linearIsometryEquiv R
  let h₂R := h₂.comp_linearIsometryEquiv R
  let d₁R := d₁.comp_linearIsometryEquiv R
  let d₂R := d₂.comp_linearIsometryEquiv R
  let := chartedSpace (H := H) h₁ h₂
  let := chartedSpace (H := H) h₁R h₂R
  have := isManifold (n := 1) h₁ h₂ d₁ d₂
  have := isManifold (n := 1) h₁R h₂R d₁R d₂R
  rw [← coe_compLinearIsometryEquivDiffeomorph (n := 1) R h₁ h₂ d₁ d₂]
  refine isOrientationPreservingAt_of_comp_inl_of_comp_inr (d₁ := d₁) (d₂ := d₂) (he₁ := he₁)
    (he₂ := he₂)
    (compLinearIsometryEquivDiffeomorph R h₁ h₂ d₁ d₂).isLocalDiffeomorph
    (orientation h₁R h₂R d₁R d₂R o₁ o₂ oE' he₁' he₂') 0 (fun x ↦ ?_)
    (fun y _ ↦ ?_) p
  · have : compLinearIsometryEquivHomeomorph R e₁ e₂ ∘ inl e₁ e₂ = inl (e₁ ∘ R) (e₂ ∘ R) ∘
        Opens.inclusion (puncture_comp_linearIsometryEquiv R e₁).ge :=
      funext fun x ↦ compLinearIsometryEquivHomeomorph_inl R e₁ e₂ x
    rw [coe_compLinearIsometryEquivDiffeomorph, this]
    exact (isOrientationPreservingAt_inl h₁R h₂R d₁R d₂R he₁' he₂'
      (isOrientationPreservingAt_restrict o₁ _ _)).comp
      (isOrientationPreservingAt_restrict_inclusion o₁ _ x)
  · have : compLinearIsometryEquivHomeomorph R e₁ e₂ ∘ inr e₁ e₂ = inr (e₁ ∘ R) (e₂ ∘ R) ∘
        Opens.inclusion (puncture_comp_linearIsometryEquiv R e₂).ge :=
      funext fun y ↦ compLinearIsometryEquivHomeomorph_inr R e₁ e₂ y
    rw [coe_compLinearIsometryEquivDiffeomorph, this]
    exact (isOrientationPreservingAt_inr h₁R h₂R d₁R d₂R he₁' he₂'
      (isOrientationPreservingAt_restrict o₂ _ _)).comp
      (isOrientationPreservingAt_restrict_inclusion o₂ _ y)

end TauCeti.ConnectedSum
