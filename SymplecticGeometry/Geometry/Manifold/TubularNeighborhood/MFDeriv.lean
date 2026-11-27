/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

import TauCeti.Geometry.Manifold.TubularNeighborhood.PrescribedDifferential
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Pullback
import SymplecticGeometry.Geometry.Manifold.Diffeomorph.Basic
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import SymplecticGeometry.Topology.Sets.Opens.Basic
import SymplecticGeometry.Geometry.Manifold.IsManifold.SecondCountable
import SymplecticGeometry.Geometry.Manifold.VectorBundle.Tangent.Opens
import TauCeti.Geometry.Manifold.ContMDiff.Subtype
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset

/-!
# Diffeomorphisms of neighbourhoods with a prescribed derivative

Let `f₀ : Q → M₀` and `f₁ : Q → M₁` be smooth embeddings of the same manifold, and let `A` be a
smooth family of linear isomorphisms `A q : T_{f₀ q} M₀ ≃ T_{f₁ q} M₁`, a section over `Q` of the
bundle of linear maps between the pull-backs `f₀ *ᵖ TM₀` and `f₁ *ᵖ TM₁`, with
`A q ∘ df₀ q = df₁ q`. Then `exists_diffeomorph_opens_mfderiv_eq` gives a diffeomorphism `ψ`
between open neighbourhoods of `f₀ (Q)` and of `f₁ (Q)` with `ψ ∘ f₀ = f₁` and derivative `A q` at
every `f₀ q`. Neither compactness of `Q` nor closedness of the images is assumed.

This is the step of the proofs of the neighbourhood theorems of McDuff–Salamon, §3.4, in which a
bundle isomorphism along the submanifold is realized as the derivative of a diffeomorphism of
neighbourhoods, before the relative Moser theorem corrects the symplectic forms.

The theorem is Tau Ceti's `TauCeti.SmoothEmbedding.exists_partialDiffeomorph_mfderiv_eq`, in
the form `exists_partialDiffeomorph_mfderiv_eq'` below, which drops second countability of the
target, and in the form that `Tubular.lean` uses: the partial diffeomorphism is read as a
diffeomorphism between its source and target, and the smoothness of `A` is that of a section of
the hom bundle of the pull-backs, which gives Tau Ceti's smoothness in tangent coordinates through
`Bundle.Pullback.contMDiffAt_inCoordinates_of_contMDiffAt`.

Tau Ceti's theorem asks both manifolds to be second countable. Only the source `M` needs to be
(`TauCeti.SmoothEmbedding.exists_partialDiffeomorph_mfderiv_eq'`): `Q` embeds in `M`, so it is
second countable, and the image of `g` has a second countable open neighbourhood `U` in `N`
(`IsLindelof.exists_opens_secondCountableTopology`). Tau Ceti's theorem applies with `U` as
target, since `A` read in the tangent coordinates of `U` is `A` read in those of `N`
(`TauCeti.Manifold.inTangentCoordinates_subtypeVal_comp_eventuallyEq`), and the partial
diffeomorphism it gives, followed by the inclusion of `U`, is the one sought.

## Main results

* `TauCeti.SmoothEmbedding.exists_diffeomorph_opens_mfderiv_eq`: the diffeomorphism of open
  neighbourhoods with prescribed derivative along the embedded manifold.
* `TauCeti.SmoothEmbedding.exists_partialDiffeomorph_mfderiv_eq'`: the partial diffeomorphism
  with prescribed derivative along an embedded manifold, into a target that need not be second
  countable.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §3.4.
* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Theorem 6.24.
-/

public section

noncomputable section

open Bundle Manifold Set Function TopologicalSpace Topology
open scoped ContDiff Manifold Bundle

namespace TauCeti.SmoothEmbedding

section NonSecondCountable

variable {E V F H G H' Q M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ V G} {K : ModelWithCorners ℝ F H'}
  [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
  [TopologicalSpace M] [ChartedSpace G M] [IsManifold J ∞ M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold K ∞ N]

/-- **Extension with a prescribed ambient differential, into any manifold.** Tau Ceti's
`exists_partialDiffeomorph_mfderiv_eq` without second countability of the target `N`. Let
`i : Q → M` be a smooth embedding into a second countable Hausdorff manifold and `g : Q → N` a
smooth map inducing the topology of `Q` into a Hausdorff manifold, both without boundary and
finite-dimensional, with `Q` nonempty. Let `A q : T_{i q} M → T_{g q} N` be linear isomorphisms,
smooth in tangent coordinates, with `A q ∘ d i_q = d g_q`. Then there is a smooth partial
diffeomorphism `Ψ` from `M` to `N` whose source contains the image of `i` and lies in a given open
neighbourhood `O` of it, whose target lies in a given open neighbourhood `O'` of the image of
`g`, with `Ψ (i q) = g q` and `d Ψ_{i q} = A q` for every `q`. -/
theorem exists_partialDiffeomorph_mfderiv_eq' [I.Boundaryless] [J.Boundaryless]
    [K.Boundaryless] [T2Space M] [T2Space N] [Nonempty Q] [SecondCountableTopology M]
    (i : SmoothEmbedding I J ∞ Q M) {g : Q → N}
    (hg : ContMDiff I K ∞ g) (hgi : IsInducing g)
    {A : ∀ q, TangentSpace J (i q) →L[ℝ] TangentSpace K (g q)}
    (hA : ∀ q, ContMDiffAt I 𝓘(ℝ, V →L[ℝ] F) ∞ (inTangentCoordinates J K i g A q) q)
    (hAinv : ∀ q, (A q).IsInvertible)
    (hAi : ∀ q, (A q).comp (mfderiv I J i q) = mfderiv I K g q)
    {O : Set M} (hO : IsOpen O) (hiO : range i ⊆ O)
    {O' : Set N} (hO' : IsOpen O') (hgO' : range g ⊆ O') :
    ∃ Ψ : PartialDiffeomorph J K M N ∞, range i ⊆ Ψ.source ∧ Ψ.source ⊆ O ∧
      Ψ.target ⊆ O' ∧ (∀ q, Ψ (i q) = g q) ∧ ∀ q, mfderiv J K Ψ (i q) = A q := by
  -- `Q` embeds in `M`, so it is second countable and the image of `g` is Lindelöf: it has a
  -- second countable open neighbourhood `U ⊆ O'`.
  have : SecondCountableTopology Q := i.isEmbedding.secondCountableTopology
  have : SecondCountableTopology H' := K.secondCountableTopology
  obtain ⟨U, hgU, hUO', hU⟩ :=
    (isLindelof_range hg.continuous).exists_opens_secondCountableTopology (H := H') hO' hgO'
  -- The data `g` and `A`, read into the open submanifold `U`.
  let g' (q : Q) : U := ⟨g q, hgU (mem_range_self q)⟩
  have hg'c : Continuous g' := hg.continuous.subtype_mk _
  have hA' (q : Q) : ContMDiffAt I 𝓘(ℝ, V →L[ℝ] F) ∞ (inTangentCoordinates J K i g' A q) q :=
    (hA q).congr_of_eventuallyEq
      (TauCeti.Manifold.inTangentCoordinates_subtypeVal_comp_eventuallyEq A hg'c.continuousAt)
  have hAi' (q : Q) : (A q).comp (mfderiv I J i q) = mfderiv I K g' q :=
    ContinuousLinearMap.ext fun v ↦ (DFunLike.congr_fun (hAi q) v).trans
      (TauCeti.Manifold.mfderiv_subtype_val_comp_apply (f := g') v)
  obtain ⟨Ψ, hsrc, hsO, -, hΨg, hΨd⟩ := i.exists_partialDiffeomorph_mfderiv_eq
    ((TauCeti.ContMDiff.subtypeVal_comp_iff U g').1 hg)
    ((IsInducing.of_comp_iff IsInducing.subtypeVal).1 hgi) hA' hAinv hAi' hO hiO isOpen_univ
    (subset_univ _)
  -- Follow `Ψ` by the inclusion of `U` into `N`.
  let ι := PartialDiffeomorph.subtypeVal K ∞ U ⟨g' (Classical.arbitrary Q)⟩
  have hsrc' : (Ψ.trans ι).source = Ψ.source := by
    rw [PartialDiffeomorph.trans_source, PartialDiffeomorph.subtypeVal_source, preimage_univ,
      inter_univ]
  refine ⟨Ψ.trans ι, hsrc' ▸ hsrc, hsrc' ▸ hsO, ?_, fun q ↦ ?_, fun q ↦ ?_⟩
  · rw [PartialDiffeomorph.trans_target, PartialDiffeomorph.subtypeVal_target]
    exact inter_subset_left.trans hUO'
  · rw [PartialDiffeomorph.coe_trans, comp_apply, PartialDiffeomorph.coe_subtypeVal, hΨg]
  · refine ContinuousLinearMap.ext fun v ↦ ?_
    rw [PartialDiffeomorph.coe_trans, PartialDiffeomorph.coe_subtypeVal,
      TauCeti.Manifold.mfderiv_subtype_val_comp_apply]
    exact DFunLike.congr_fun (hΨd q) v

end NonSecondCountable

variable {EQ E₀ E₁ HQ H₀ H₁ Q M₀ M₁ : Type*}
  [NormedAddCommGroup EQ] [NormedSpace ℝ EQ] [FiniteDimensional ℝ EQ]
  [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀]
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
  [TopologicalSpace HQ] [TopologicalSpace H₀] [TopologicalSpace H₁]
  {J : ModelWithCorners ℝ EQ HQ} {I₀ : ModelWithCorners ℝ E₀ H₀}
  {I₁ : ModelWithCorners ℝ E₁ H₁}
  [J.Boundaryless] [I₀.Boundaryless] [I₁.Boundaryless]
  [TopologicalSpace Q] [ChartedSpace HQ Q] [IsManifold J ∞ Q]
  [TopologicalSpace M₀] [ChartedSpace H₀ M₀] [IsManifold I₀ ∞ M₀] [T2Space M₀]
  [TopologicalSpace M₁] [ChartedSpace H₁ M₁] [IsManifold I₁ ∞ M₁] [T2Space M₁]

/-- **Diffeomorphisms of neighbourhoods with a prescribed derivative.** Let `f₀ : Q → M₀` and
`f₁ : Q → M₁` be smooth embeddings into Hausdorff manifolds without boundary, `M₀` second
countable, and let `A q : T_{f₀ q} M₀ ≃L[ℝ] T_{f₁ q} M₁` be linear isomorphisms forming a smooth
section over `Q` of the bundle of linear maps between the pull-backs `f₀ *ᵖ TM₀` and
`f₁ *ᵖ TM₁`, with `A q (df₀ q v) = df₁ q v`. Then there are open sets `U₀ ⊆ M₀` and `U₁ ⊆ M₁`
and a diffeomorphism `ψ : U₀ ≃ U₁` such that, for every `q`, `f₀ q ∈ U₀`, `ψ (f₀ q) = f₁ q`
and the derivative of `ψ` at `f₀ q` is `A q`. Neither compactness of `Q` nor closedness of the
images is assumed. -/
theorem exists_diffeomorph_opens_mfderiv_eq [SecondCountableTopology M₀]
    (f₀ : SmoothEmbedding J I₀ ∞ Q M₀) (f₁ : SmoothEmbedding J I₁ ∞ Q M₁)
    (A : ∀ q, TangentSpace I₀ (f₀ q) ≃L[ℝ] TangentSpace I₁ (f₁ q))
    (hA : ContMDiff J (J.prod 𝓘(ℝ, E₀ →L[ℝ] E₁)) ∞ (fun q ↦ TotalSpace.mk' (E₀ →L[ℝ] E₁)
      (E := fun q ↦ ((f₀ : Q → M₀) *ᵖ (TangentSpace I₀)) q →L[ℝ]
        ((f₁ : Q → M₁) *ᵖ (TangentSpace I₁)) q) q
        (A q : TangentSpace I₀ (f₀ q) →L[ℝ] TangentSpace I₁ (f₁ q))))
    (hAf : ∀ q v, A q (mfderiv J I₀ f₀ q v) = mfderiv J I₁ f₁ q v) :
    ∃ (U₀ : Opens M₀) (U₁ : Opens M₁) (ψ : U₀ ≃ₘ⟮I₀, I₁⟯ U₁),
      ∀ q, ∃ h : f₀ q ∈ U₀, (ψ ⟨f₀ q, h⟩ : M₁) = f₁ q ∧
        mfderiv I₀ I₁ ψ ⟨f₀ q, h⟩ =
          (A q : TangentSpace I₀ (f₀ q) →L[ℝ] TangentSpace I₁ (f₁ q)) := by
  cases isEmpty_or_nonempty Q with
  | inl hQ =>
    exact ⟨⊥, ⊥, Diffeomorph.ofIsEmpty, fun q ↦ (hQ.false q).elim⟩
  | inr hQ =>
    -- The section `A` applied to the vectors of `f₀ *ᵖ TM₀`, as a map into `TM₁`.
    have hAv : ContMDiff (J.prod 𝓘(ℝ, E₀)) (I₁.prod 𝓘(ℝ, E₁)) ∞
        (fun p : TotalSpace E₀ ((f₀ : Q → M₀) *ᵖ (TangentSpace I₀)) ↦
          TotalSpace.mk' E₁ (E := TangentSpace I₁) (f₁ p.proj) (A p.proj p.snd)) :=
      (Pullback.contMDiff_lift (E := TangentSpace I₁) f₁ f₁.contMDiff).comp
        (ContMDiff.clm_bundle_apply
          (hA.comp (contMDiff_proj (F := E₀) ((f₀ : Q → M₀) *ᵖ (TangentSpace I₀))))
          contMDiff_id)
    obtain ⟨Ψ, hsrc, -, -, hΨf, hΨd⟩ := f₀.exists_partialDiffeomorph_mfderiv_eq'
      f₁.contMDiff f₁.isEmbedding.isInducing
      (A := fun q ↦ (A q : TangentSpace I₀ (f₀ q) →L[ℝ] TangentSpace I₁ (f₁ q)))
      -- `inTangentCoordinates` is by definition the `inCoordinates` of the tangent bundles.
      (fun q ↦ Bundle.Pullback.contMDiffAt_inCoordinates_of_contMDiffAt f₀ f₁
        f₁.contMDiff.contMDiffAt _ fun _ ↦ hAv _)
      (fun q ↦ ⟨A q, rfl⟩) (fun q ↦ ContinuousLinearMap.ext (hAf q))
      isOpen_univ (subset_univ _) isOpen_univ (subset_univ _)
    refine ⟨⟨Ψ.source, Ψ.open_source⟩, ⟨Ψ.target, Ψ.open_target⟩, Ψ.toDiffeomorphSourceTarget,
      fun q ↦ ⟨hsrc (mem_range_self q), ?_, ?_⟩⟩
    · rw [PartialDiffeomorph.toDiffeomorphSourceTarget_apply_coe, hΨf]
    · refine ContinuousLinearMap.ext fun v ↦ ?_
      -- The derivative of `ψ` is that of `Ψ`, read through the inclusions.
      rw [Ψ.mfderiv_toDiffeomorphSourceTarget_apply _ v, hΨd]
      exact (ContinuousLinearEquiv.coe_apply (A q) v).symm

end TauCeti.SmoothEmbedding

end
