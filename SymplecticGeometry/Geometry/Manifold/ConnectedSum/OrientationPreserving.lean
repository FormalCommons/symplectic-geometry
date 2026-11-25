/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.ConnectedSum.Oriented
public import TauCeti.Geometry.Manifold.ConnectedSum.Orientation
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions
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

namespace TauCeti.Manifold.Orientation

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [FiniteDimensional ℝ E] [IsManifold I 1 M]
  {E' H' M' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  [TopologicalSpace M'] [ChartedSpace H' M'] [FiniteDimensional ℝ E'] [IsManifold I' 1 M']
  {ι : Type*} [Fintype ι]

/-- Preserving orientations at a point depends only on the germ of the map there. -/
theorem IsOrientationPreservingAt.congr_of_eventuallyEq {o : Manifold.Orientation I M ι}
    {o' : Manifold.Orientation I' M' ι} {f g : M → M'} {x : M}
    (h : IsOrientationPreservingAt o o' f x) (hg : g =ᶠ[𝓝 x] f) :
    IsOrientationPreservingAt o o' g x := by
  have hx : g x = f x := hg.eq_of_nhds
  obtain ⟨e, he, ho⟩ := (isOrientationPreservingAt_iff _ _ _ _).1 h
  exact (isOrientationPreservingAt_iff _ _ _ _).2
    ⟨e, (hg.mfderiv_eq (I := I) (I' := I')).symm ▸ he, ho.trans (hx ▸ rfl)⟩

end TauCeti.Manifold.Orientation

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

open Manifold.Orientation ENat

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


section CongrLeft

variable {M' : Type*} [TopologicalSpace M'] [T1Space M'] [ChartedSpace H M'] [IsManifold I 1 M']
  {e₁' : E → M'} {h₁' : IsOpenEmbedding e₁'} {d₁' : IsLocalDiffeomorph 𝓘(ℝ, E) I 1 e₁'}
  {o₁' : Manifold.Orientation I M' ι} {oE' : Manifold.Orientation 𝓘(ℝ, E) E ι}
  {he₁' : ∀ v ≠ 0, IsOrientationPreservingAt oE' o₁' e₁' v}
  {he₂' : ∀ v ≠ 0, IsOrientationReversingAt oE' o₂ e₂ v}

omit [ChartedSpace H M] [IsManifold I 1 M] [ChartedSpace H N] [IsManifold I 1 N]
  [ChartedSpace H M'] [IsManifold I 1 M'] in
/-- Far out along the ball `e₂`, the homeomorphism `TauCeti.ConnectedSum.congrLeftHomeomorph` is
the identity of the second punctured summand. -/
theorem exists_congrLeftHomeomorph_inr_eq [T2Space N] (φ : M ≃ₜ M') (hφ : φ ∘ e₁ =ᶠ[𝓝 0] e₁')
    (h₁ : IsOpenEmbedding e₁) (h₁' : IsOpenEmbedding e₁') (h₂ : IsOpenEmbedding e₂) :
    ∃ r, ∀ y : puncture e₂, (y : N) ∉ e₂ '' closedBall 0 r →
      congrLeftHomeomorph φ hφ h₁ h₁' h₂ (inr e₁ e₂ y) = inr e₁' e₂ y := by
  obtain ⟨ε, hε, hεφ⟩ := Metric.eventually_nhds_iff.1 hφ
  refine ⟨ε⁻¹, fun ⟨y, hy⟩ hyr ↦ ?_⟩
  by_cases h : y ∈ range e₂
  · obtain ⟨w, rfl⟩ := h
    have hw : ε⁻¹ < ‖w‖ := not_le.1 fun hw ↦ hyr ⟨w, mem_closedBall_zero_iff.2 hw, rfl⟩
    have hw0 : w ≠ 0 := norm_pos_iff.1 ((inv_pos.2 hε).trans hw)
    have hdist : dist (inversion 0 1 w) 0 < ε := by
      rw [dist_inversion_center, one_pow, dist_zero_right, one_div_lt (norm_pos_iff.2 hw0) hε,
        one_div]
      exact hw
    have hx : e₁' (inversion 0 1 w) ∈ puncture e₁' := by
      rw [← hεφ hdist]
      exact apply_mem_puncture φ.injective hφ.eq_of_nhds
        (apply_inversion_mem_puncture h₁.injective hw0)
    rw [congrLeftHomeomorph_inr_apply]
    exact (congrArg (inl e₁' e₂) (Subtype.ext (hεφ hdist))).trans (inl_inversion_eq_inr hx hy)
  · exact congrLeftHomeomorph_inr_of_notMem φ hφ h₁ h₁' h₂ h

include he₁ he₂ he₁' he₂' in
/-- Moving the first ball by an orientation-preserving `C¹` diffeomorphism `φ` of the first
summand preserves the orientations of the two connected sums. -/
theorem isOrientationPreservingAt_congrLeftHomeomorph [T2Space N] (φ : M ≃ₜ M')
    (hφ : φ ∘ e₁ =ᶠ[𝓝 0] e₁') (hφs : ContMDiff I I 1 φ) (hφs' : ContMDiff I I 1 φ.symm)
    (hφo : ∀ x, IsOrientationPreservingAt o₁ o₁' φ x) (p : ConnectedSum e₁ e₂) :
    letI := chartedSpace (H := H) h₁ h₂
    letI := chartedSpace (H := H) h₁' h₂
    haveI := isManifold (n := 1) h₁ h₂ d₁ d₂
    haveI := isManifold (n := 1) h₁' h₂ d₁' d₂
    IsOrientationPreservingAt (orientation h₁ h₂ d₁ d₂ o₁ o₂ oE he₁ he₂)
      (orientation h₁' h₂ d₁' d₂ o₁' o₂ oE' he₁' he₂') (congrLeftHomeomorph φ hφ h₁ h₁' h₂) p := by
  let := chartedSpace (H := H) h₁ h₂
  let := chartedSpace (H := H) h₁' h₂
  have := isManifold (n := 1) h₁ h₂ d₁ d₂
  have := isManifold (n := 1) h₁' h₂ d₁' d₂
  let φ' : M ≃ₘ^1⟮I, I⟯ M' :=
    { toEquiv := φ.toEquiv, contMDiff_toFun := hφs, contMDiff_invFun := hφs' }
  have hloc : IsLocalDiffeomorph I I 1 (congrLeftHomeomorph φ hφ h₁ h₁' h₂) := by
    have := (congrLeftDiffeomorph h₁ h₁' h₂ d₁ d₁' d₂ φ' hφ).isLocalDiffeomorph
    rwa [coe_congrLeftDiffeomorph] at this
  obtain ⟨r, hr⟩ := exists_congrLeftHomeomorph_inr_eq φ hφ h₁ h₁' h₂
  have hK : IsClosed (e₂ '' closedBall 0 r) :=
    ((isCompact_closedBall 0 r).image h₂.continuous).isClosed
  refine isOrientationPreservingAt_of_comp_inl_of_comp_inr (d₁ := d₁) (d₂ := d₂) (he₁ := he₁)
    (he₂ := he₂) hloc (orientation h₁' h₂ d₁' d₂ o₁' o₂ oE' he₁' he₂') r (fun x ↦ ?_)
    (fun y hy ↦ ?_) p
  · have : congrLeftHomeomorph φ hφ h₁ h₁' h₂ ∘ inl e₁ e₂ =
        inl e₁' e₂ ∘ punctureMap φ φ.injective hφ.eq_of_nhds :=
      funext fun x ↦ (congrLeftHomeomorph_inl φ hφ h₁ h₁' h₂ x).trans
        (congrArg _ (Subtype.ext (coe_punctureMap _ _ _).symm))
    rw [this]
    refine (isOrientationPreservingAt_inl h₁' h₂ d₁' d₂ he₁' he₂'
      (isOrientationPreservingAt_restrict o₁' _ _)).comp
      ((isOrientationPreservingAt_restrict o₁' _ _).of_comp ?_ ?_)
    · rw [subtypeVal_comp_punctureMap]
      exact (hφo x).comp (isOrientationPreservingAt_restrict o₁ _ x)
    · exact ((ContMDiff.subtypeVal_comp_iff _ _).1 (by
        rw [subtypeVal_comp_punctureMap]; exact hφs.comp contMDiff_subtypeVal)).mdifferentiableAt
          one_ne_zero
  · refine (isOrientationPreservingAt_inr h₁' h₂ d₁' d₂ he₁' he₂'
      (isOrientationPreservingAt_restrict o₂ _ y)).congr_of_eventuallyEq ?_
    filter_upwards [(hK.isOpen_compl.preimage continuous_subtypeVal).mem_nhds hy] with y' hy'
    exact hr y' hy'

end CongrLeft

end TauCeti.ConnectedSum

namespace TauCeti.ConnectedSum

open Manifold.Orientation ENat

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [T2Space M] [PreconnectedSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {N : Type*} [TopologicalSpace N] [T2Space N] [PreconnectedSpace N]
  [ChartedSpace E N] [IsManifold 𝓘(ℝ, E) ∞ N]
  {ι : Type*} [Fintype ι]

/-- Oriented connected sums along two pairs of balls which preserve and reverse the orientations
from the same orientation `o` of `E` are diffeomorphic by an orientation-preserving
diffeomorphism. -/
theorem exists_diffeomorph_isOrientationPreservingAt_of_eq {e₁ e₁' : E → M} {e₂ e₂' : E → N}
    (h₁ : IsOpenEmbedding e₁) (h₂ : IsOpenEmbedding e₂) (h₁' : IsOpenEmbedding e₁')
    (h₂' : IsOpenEmbedding e₂') (d₁ : IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ e₁)
    (d₂ : IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ e₂)
    (d₁' : IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ e₁')
    (d₂' : IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ e₂')
    (o : Manifold.Orientation 𝓘(ℝ, E) E ι) (oM : Manifold.Orientation 𝓘(ℝ, E) M ι)
    (oN : Manifold.Orientation 𝓘(ℝ, E) N ι) (hf₁ : ∀ v, o.IsOrientationPreservingAt oM e₁ v)
    (hf₂ : ∀ v, o.IsOrientationReversingAt oN e₂ v)
    (hf₁' : ∀ v, o.IsOrientationPreservingAt oM e₁' v)
    (hf₂' : ∀ v, o.IsOrientationReversingAt oN e₂' v) :
    letI := chartedSpace (H := E) h₁ h₂
    letI := chartedSpace (H := E) h₁' h₂'
    haveI := isManifold h₁ h₂ d₁ d₂
    haveI := isManifold h₁' h₂' d₁' d₂'
    ∃ Φ : ConnectedSum e₁ e₂ ≃ₘ^∞⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ ConnectedSum e₁' e₂', ∀ p,
      IsOrientationPreservingAt
        (orientation h₁ h₂ (IsLocalDiffeomorph.of_le d₁ LEInfty.out)
          (IsLocalDiffeomorph.of_le d₂ LEInfty.out) oM oN o (fun v _ ↦ hf₁ v) (fun v _ ↦ hf₂ v))
        (orientation h₁' h₂' (IsLocalDiffeomorph.of_le d₁' LEInfty.out)
          (IsLocalDiffeomorph.of_le d₂' LEInfty.out) oM oN o (fun v _ ↦ hf₁' v)
          (fun v _ ↦ hf₂' v)) Φ p := by
  -- The balls agree near `0` after orientation-preserving diffeomorphisms of the summands.
  obtain ⟨φ, hφ, hφo⟩ :=
    SmoothEmbedding.exists_diffeomorph_comp_eventuallyEq_and_isOrientationPreservingAt
      (SmoothEmbedding.id.compLocalDiffeomorph e₁ d₁ h₁.isEmbedding)
      (SmoothEmbedding.id.compLocalDiffeomorph e₁' d₁' h₁'.isEmbedding) o oM
      (by simpa using hf₁ 0) (by simpa using hf₁' 0)
  obtain ⟨ψ, hψ, hψo⟩ :=
    SmoothEmbedding.exists_diffeomorph_comp_eventuallyEq_and_isOrientationPreservingAt
      (SmoothEmbedding.id.compLocalDiffeomorph e₂ d₂ h₂.isEmbedding)
      (SmoothEmbedding.id.compLocalDiffeomorph e₂' d₂' h₂'.isEmbedding) o (-oN)
      (by simpa using hf₂ 0) (by simpa using hf₂' 0)
  replace hφ : φ ∘ e₁ =ᶠ[𝓝 0] e₁' := by simpa using hφ
  replace hψ : ψ ∘ e₂ =ᶠ[𝓝 0] e₂' := by simpa using hψ
  replace hψo : ∀ y, oN.IsOrientationPreservingAt oN ψ y := fun y ↦ by simpa using hψo y
  have k₁ : ∀ v ≠ 0, (-o).IsOrientationReversingAt oM e₁' v := fun v _ ↦ by simpa using hf₁' v
  have k₂ : ∀ v ≠ 0, (-o).IsOrientationPreservingAt oN e₂ v := fun v _ ↦ by simpa using hf₂ v
  have k₂' : ∀ v ≠ 0, (-o).IsOrientationPreservingAt oN e₂' v := fun v _ ↦ by simpa using hf₂' v
  let := chartedSpace (H := E) h₁ h₂
  let := chartedSpace (H := E) h₁' h₂
  let := chartedSpace (H := E) h₂ h₁'
  let := chartedSpace (H := E) h₂' h₁'
  let := chartedSpace (H := E) h₁' h₂'
  have := isManifold h₁ h₂ d₁ d₂
  have := isManifold h₁' h₂ d₁' d₂
  have := isManifold h₂ h₁' d₂ d₁'
  have := isManifold h₂' h₁' d₂' d₁'
  have := isManifold h₁' h₂' d₁' d₂'
  refine ⟨(congrLeftDiffeomorph h₁ h₁' h₂ d₁ d₁' d₂ φ hφ).trans <|
    (commDiffeomorph h₁' h₂ d₁' d₂).trans <|
    (congrLeftDiffeomorph h₂ h₂' h₁' d₂ d₂' d₁' ψ hψ).trans (commDiffeomorph h₂' h₁' d₂' d₁'),
    fun p ↦ ?_⟩
  simp only [Diffeomorph.coe_trans, coe_congrLeftDiffeomorph, coe_commDiffeomorph]
  exact (isOrientationPreservingAt_commHomeomorph (he₁ := k₂') (he₂ := k₁) _).comp <|
    (isOrientationPreservingAt_congrLeftHomeomorph (he₁ := k₂) (he₂ := k₁) (he₁' := k₂')
      (he₂' := k₁) ψ.toHomeomorph hψ (ψ.contMDiff.of_le LEInfty.out)
      (ψ.symm.contMDiff.of_le LEInfty.out) hψo _).comp <|
    (isOrientationPreservingAt_commHomeomorph (he₁ := fun v _ ↦ hf₁' v)
      (he₂ := fun v _ ↦ hf₂ v) _).comp <|
    isOrientationPreservingAt_congrLeftHomeomorph (he₁ := fun v _ ↦ hf₁ v)
      (he₂ := fun v _ ↦ hf₂ v) (he₁' := fun v _ ↦ hf₁' v) (he₂' := fun v _ ↦ hf₂ v)
      φ.toHomeomorph hφ (φ.contMDiff.of_le LEInfty.out) (φ.symm.contMDiff.of_le LEInfty.out)
      hφo p

/-- **The oriented connected sum does not depend on its balls, up to orientation-preserving
diffeomorphism.** Let `M` and `N` be connected Hausdorff smooth manifolds without boundary,
modelled on a nontrivial finite-dimensional real inner product space `E`, with orientations `oM`
and `oN`. Let `e₁ : E → M` and `e₂ : E → N` be balls, open embeddings and smooth local
diffeomorphisms, which respectively preserve and reverse orientation from an orientation `o` of
`E`, and let `e₁'` and `e₂'` be another such pair, for an orientation `o'` of `E`. Then some
diffeomorphism from the connected sum along `e₁` and `e₂` to the connected sum along `e₁'` and
`e₂'` preserves their orientations `TauCeti.ConnectedSum.orientation`. -/
theorem exists_diffeomorph_isOrientationPreservingAt [Nontrivial E] {e₁ e₁' : E → M}
    {e₂ e₂' : E → N} (h₁ : IsOpenEmbedding e₁) (h₂ : IsOpenEmbedding e₂)
    (h₁' : IsOpenEmbedding e₁') (h₂' : IsOpenEmbedding e₂')
    (d₁ : IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ e₁) (d₂ : IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ e₂)
    (d₁' : IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ e₁')
    (d₂' : IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ e₂')
    (o o' : Manifold.Orientation 𝓘(ℝ, E) E ι) (oM : Manifold.Orientation 𝓘(ℝ, E) M ι)
    (oN : Manifold.Orientation 𝓘(ℝ, E) N ι) (hf₁ : ∀ v, o.IsOrientationPreservingAt oM e₁ v)
    (hf₂ : ∀ v, o.IsOrientationReversingAt oN e₂ v)
    (hf₁' : ∀ v, o'.IsOrientationPreservingAt oM e₁' v)
    (hf₂' : ∀ v, o'.IsOrientationReversingAt oN e₂' v) :
    letI := chartedSpace (H := E) h₁ h₂
    letI := chartedSpace (H := E) h₁' h₂'
    haveI := isManifold h₁ h₂ d₁ d₂
    haveI := isManifold h₁' h₂' d₁' d₂'
    ∃ Φ : ConnectedSum e₁ e₂ ≃ₘ^∞⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ ConnectedSum e₁' e₂', ∀ p,
      IsOrientationPreservingAt
        (orientation h₁ h₂ (IsLocalDiffeomorph.of_le d₁ LEInfty.out)
          (IsLocalDiffeomorph.of_le d₂ LEInfty.out) oM oN o (fun v _ ↦ hf₁ v) (fun v _ ↦ hf₂ v))
        (orientation h₁' h₂' (IsLocalDiffeomorph.of_le d₁' LEInfty.out)
          (IsLocalDiffeomorph.of_le d₂' LEInfty.out) oM oN o' (fun v _ ↦ hf₁' v)
          (fun v _ ↦ hf₂' v)) Φ p := by
  rcases o'.eq_or_eq_neg o with rfl | rfl
  · exact exists_diffeomorph_isOrientationPreservingAt_of_eq h₁ h₂ h₁' h₂' d₁ d₂ d₁' d₂' o' oM oN
      hf₁ hf₂ hf₁' hf₂'
  -- The second pair of balls induces the opposite orientation of `E`: rotate it by a reflection.
  obtain ⟨R, hR⟩ := exists_det_neg (F := E)
  have h₁R := h₁'.comp_linearIsometryEquiv R
  have h₂R := h₂'.comp_linearIsometryEquiv R
  have hg₁ : ∀ v, o.IsOrientationPreservingAt oM (e₁' ∘ R) v := fun v ↦
    isOrientationPreservingAt_comp_of_det_neg (by simpa using hf₁' (R v)) hR
  have hg₂ : ∀ v, o.IsOrientationReversingAt oN (e₂' ∘ R) v := fun v ↦
    isOrientationReversingAt_comp_of_det_neg (by simpa using hf₂' (R v)) hR
  let := chartedSpace (H := E) h₁ h₂
  let := chartedSpace (H := E) h₁' h₂'
  let := chartedSpace (H := E) h₁R h₂R
  have := isManifold h₁ h₂ d₁ d₂
  have := isManifold h₁' h₂' d₁' d₂'
  have := isManifold h₁R h₂R (d₁'.comp_linearIsometryEquiv R) (d₂'.comp_linearIsometryEquiv R)
  obtain ⟨Φ, hΦ⟩ := exists_diffeomorph_isOrientationPreservingAt_of_eq h₁ h₂ h₁R h₂R d₁ d₂
    (d₁'.comp_linearIsometryEquiv R) (d₂'.comp_linearIsometryEquiv R) o oM oN hf₁ hf₂ hg₁ hg₂
  refine ⟨Φ.trans (compLinearIsometryEquivDiffeomorph R h₁' h₂' d₁' d₂').symm, fun p ↦ ?_⟩
  rw [Diffeomorph.coe_trans]
  refine IsOrientationPreservingAt.comp ?_ (hΦ p)
  refine IsOrientationPreservingAt.diffeomorph_symm ?_ (by simp)
  rw [coe_compLinearIsometryEquivDiffeomorph]
  exact isOrientationPreservingAt_compLinearIsometryEquivHomeomorph (he₁ := fun v _ ↦ hf₁' v)
    (he₂ := fun v _ ↦ hf₂' v) R _

end TauCeti.ConnectedSum
