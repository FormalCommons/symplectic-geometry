/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.LinearAlgebra.Symplectic.Extension
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Pullback
public import TauCeti.Geometry.Symplectic.Manifold.Flat
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm
public import TauCeti.Geometry.Manifold.VectorBundle.Subbundle
import SymplecticGeometry.Geometry.Manifold.VectorBundle.Subbundle
import SymplecticGeometry.Geometry.Symplectic.Manifold.Flat
import SymplecticGeometry.Geometry.Manifold.VectorBundle.Orthogonal
import SymplecticGeometry.Geometry.Manifold.VectorBundle.Pullback
import TauCeti.Geometry.Manifold.Distribution.VectorBundle
import TauCeti.Geometry.Manifold.TwoForm.Kernel
import TauCeti.Geometry.Symplectic.Lagrangian.Presymplectic
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Subbundle

/-!
# Smooth frames of the splitting along a submanifold

Let `f : Q → M` be a smooth embedding into a manifold with a smooth two-form `σ` and a smooth
almost complex structure `J` compatible with `σ`, and suppose that the pulled-back form `f^* σ`
has kernels of constant dimension `k`. At `q ∈ Q`, write `ω` for the symplectic form `σ_{f q}`,
`g = ω(·, J ·)` for the associated metric, `W = df_q(T_q Q)` for the tangent image and
`K = W ∩ W^ω` for its radical. The linear algebra of
`SymplecticGeometry/LinearAlgebra/Symplectic/Extension.lean` splits `T_{f q} M` into the pieces

* `W` and `J K`, with `W ⊕ J K` symplectic;
* `H = W ∩ K^{⊥g}` (`TauCeti.SymplecticForm.radicalComplement`), with `W = H ⊕ K`;
* `E = (W ⊕ J K)^ω` (`TauCeti.SymplecticForm.normalComplement`), with
  `T_{f q} M = (W ⊕ J K) ⊕ E`.

This file shows that, as `q` varies, each piece is a smooth subbundle of the pull-back
`f *ᵖ TM` over `Q`: it has `C^∞` local frames (`TauCeti.HasLocalContMDiffSubbundleFrames`) of the
expected size. It also shows that the projections along the splittings used by the formula
`TauCeti.SymplecticForm.Compatible.extendAlong_def` for the linear extension are smooth maps of
total spaces. These are the smoothness facts that the extension along a submanifold, in
`Neighborhood/Extension.lean`, is built from.

## Construction

* `W` is the range of the derivative of the immersion `f`; its frames are
  Tau Ceti's `Manifold.IsImmersion.hasLocalContMDiffSubbundleFrames_range_mfderiv`.
* `K` is the image under `df` of the kernels of `f^* σ`, the preimages of `W^ω`
  (`TauCeti.SmoothTwoForm.IsNondegenerate.ker_bilinFormAt_mpullback_eq_comap_orthogonal` of Tau
  Ceti), which form a smooth distribution by Tau Ceti's
  `TauCeti.SmoothForm.isContMDiffDistribution_ker_bilinFormAt`. Its image `J K` is the image
  under the smooth bundle map `J`. Images of frames under injective
  bundle maps are frames (`TauCeti.HasLocalContMDiffSubbundleFrames.map`), and so are frames of
  two summands meeting in `0` put together (`TauCeti.HasLocalContMDiffSubbundleFrames.sup_fin`).
* `E` and `K^{⊥g}` are orthogonal complements of smooth subbundles for smooth fields of
  bilinear forms, `σ` and `σ(J ·, ·)`, so
  `TauCeti.HasLocalContMDiffSubbundleFrames.orthogonal_of_isCompl` applies. The orthogonal for
  `σ` is the symplectic complement, and that for `σ(J ·, ·)` is the `g`-orthogonal, by
  `TauCeti.SmoothTwoForm.IsNondegenerate.orthogonal_flat` and
  `TauCeti.SmoothTwoForm.Compatible.orthogonal_flatComp`
  (`SymplecticGeometry/Geometry/Symplectic/Manifold/Flat.lean`).
* `H` is the image of `W` under the projection onto `K^{⊥g}` along `K`
  (`TauCeti.SymplecticForm.Compatible.map_projection_orthogonal_eq_radicalComplement`), a smooth
  fibrewise map of constant rank: that projection is smooth by
  `TauCeti.HasLocalContMDiffSubbundleFrames.contMDiff_totalSpace_projection_of_isCompl`, applied
  to the frames of `K^{⊥g}` and `K` above.
* The projections onto the pieces along complementary pieces are smooth by Tau Ceti's
  `TauCeti.HasLocalContMDiffSubbundleFrames.contMDiff_totalSpace_projectionOnto_of_isCompl`.

## Main results

* `TauCeti.SmoothEmbedding.hasLocalContMDiffSubbundleFrames_radical`,
  `TauCeti.SmoothEmbedding.hasLocalContMDiffSubbundleFrames_map_radical`: frames of `K` and `J K`.
* `TauCeti.SmoothEmbedding.hasLocalContMDiffSubbundleFrames_sup_map_radical`: frames of
  `W ⊕ J K`.
* `TauCeti.SmoothEmbedding.hasLocalContMDiffSubbundleFrames_radicalComplement`,
  `TauCeti.SmoothEmbedding.hasLocalContMDiffSubbundleFrames_normalComplement`: frames of `H` and
  `E`.
* `TauCeti.SmoothEmbedding.hasLocalContMDiffSubbundleFrames_orthogonal_radical`,
  `TauCeti.SmoothEmbedding.hasLocalContMDiffSubbundleFrames_map_radical_sup_normalComplement`,
  `TauCeti.SmoothEmbedding.hasLocalContMDiffSubbundleFrames_sup_normalComplement`: frames of
  `K^{⊥g}`, `J K ⊕ E` and `W ⊕ E`.
* `TauCeti.SmoothEmbedding.contMDiff_totalSpace_projection_range_mfderiv`,
  `TauCeti.SmoothEmbedding.contMDiff_totalSpace_projection_map_radical`,
  `TauCeti.SmoothEmbedding.contMDiff_totalSpace_projection_normalComplement`,
  `TauCeti.SmoothEmbedding.contMDiff_totalSpace_projection_radical`: the projections onto
  `W` along `J K ⊕ E`, onto `J K` along `W ⊕ E`, onto `E` along `W ⊕ J K`, and onto `K` along
  `K^{⊥g}` are smooth.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §3.4,
  where these splittings along a submanifold are used in the proofs of the neighbourhood
  theorems.
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Lemma 10.32,
  the local frame criterion for subbundles.
-/

public section

open Bundle Module Set
open scoped Manifold ContDiff Bundle

namespace TauCeti.SmoothEmbedding

variable {E E' H H' M Q : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [TopologicalSpace Q] [ChartedSpace H' Q]
  [IsManifold J ∞ Q]
  (f : SmoothEmbedding J I ∞ Q M)

variable {σ : SmoothTwoForm I M} {Jc : SmoothAlmostComplexStructure I M} {k : ℕ}

omit [FiniteDimensional ℝ E] in
/-- **Frames of the radical.** If the kernels of `f^* σ` all have dimension `k`, the radicals
`W ∩ W^ω` of the tangent images `W = df_q(T_q Q)`, for `ω = σ_{f q}`, have `C^∞` local frames of
size `k` in the pull-back `f *ᵖ TM`. -/
theorem hasLocalContMDiffSubbundleFrames_radical (hω : σ.IsNondegenerate)
    (hk : ∀ q, finrank ℝ (LinearMap.ker ((SmoothForm.mpullback f f.contMDiff σ).bilinFormAt q)) =
      k) :
    HasLocalContMDiffSubbundleFrames J ∞ E (Fin k) (E := (f : Q → M) *ᵖ (TangentSpace I))
      fun q ↦ (mfderiv J I f q).range ⊓
        (hω.symplecticFormAt (f q)).orthogonal (mfderiv J I f q).range := by
  have h := ((SmoothForm.mpullback f f.contMDiff σ).isContMDiffDistribution_ker_bilinFormAt
    (n := ∞) hk).hasLocalContMDiffSubbundleFrames.map (E₂ := (f : Q → M) *ᵖ (TangentSpace I))
    (P := fun q ↦ (mfderiv J I f q : TangentSpace J q →ₗ[ℝ] TangentSpace I (f q)))
    (Bundle.Pullback.contMDiff_totalSpace_mfderiv f f.contMDiff) fun q ↦ by
      have h : LinearMap.ker (mfderiv J I f q : TangentSpace J q →ₗ[ℝ] TangentSpace I (f q)) = ⊥ :=
        LinearMap.ker_eq_bot.mpr (f.isImmersion.mfderiv_injective (by simp) q)
      exact h ▸ disjoint_bot_right
  convert h using 1
  refine funext fun q ↦ ?_
  -- `df` maps the kernel of `f^* σ`, the preimage of `W^ω`, onto `W ∩ W^ω`.
  rw [hω.ker_bilinFormAt_mpullback_eq_comap_orthogonal f.contMDiff]
  exact (Submodule.map_comap_eq _ _).symm

omit [FiniteDimensional ℝ E] in
/-- **Frames of the image of the radical under `J`.** If the kernels of `f^* σ` all have
dimension `k`, the images `J (W ∩ W^ω)` of the radicals of the tangent images have `C^∞` local
frames of size `k` in the pull-back `f *ᵖ TM`. -/
theorem hasLocalContMDiffSubbundleFrames_map_radical (hω : σ.IsNondegenerate)
    (hk : ∀ q, finrank ℝ (LinearMap.ker ((SmoothForm.mpullback f f.contMDiff σ).bilinFormAt q)) =
      k) :
    HasLocalContMDiffSubbundleFrames J ∞ E (Fin k) (E := (f : Q → M) *ᵖ (TangentSpace I))
      fun q ↦ ((mfderiv J I f q).range ⊓
        (hω.symplecticFormAt (f q)).orthogonal (mfderiv J I f q).range).map
          (Jc.almostComplexStructureAt (f q)).toLinearMap := by
  -- Applying `J` is a smooth map of the total space of the pull-back.
  have hJ : ContMDiff (J.prod 𝓘(ℝ, E)) (J.prod 𝓘(ℝ, E)) ∞
      (fun p : TotalSpace E ((f : Q → M) *ᵖ (TangentSpace I)) ↦
        (⟨p.proj, (Jc.almostComplexStructureAt (f p.proj)).toLinearMap p.snd⟩ :
          TotalSpace E ((f : Q → M) *ᵖ (TangentSpace I)))) := by
    simp only [SmoothAlmostComplexStructure.almostComplexStructureAt_toLinearMap,
      ContinuousLinearMap.coe_coe]
    exact Bundle.Pullback.contMDiff_fiberwise (fun x v ↦ Jc x v)
      ((Jc.toEndomorphism.contMDiff.comp (contMDiff_proj _)).clm_bundle_apply contMDiff_id)
      f f.contMDiff
  refine (f.hasLocalContMDiffSubbundleFrames_radical hω hk).map
    (E := (f : Q → M) *ᵖ (TangentSpace I)) (E₂ := (f : Q → M) *ᵖ (TangentSpace I))
    (P := fun q ↦ (Jc.almostComplexStructureAt (f q)).toLinearMap) hJ fun q ↦ ?_
  have h : LinearMap.ker (Jc.almostComplexStructureAt (f q)).toLinearMap = ⊥ :=
    LinearMap.ker_eq_bot.mpr (Jc.almostComplexStructureAt (f q)).injective
  exact h ▸ disjoint_bot_right

omit [FiniteDimensional ℝ E] in
/-- **Frames of `W ⊕ J K`.** If the kernels of `f^* σ` all have dimension `k`, the sums
`W ⊕ J K` of the tangent images `W` and the images under `J` of their radicals `K` have `C^∞`
local frames of size `dim Q + k` in the pull-back `f *ᵖ TM`. -/
theorem hasLocalContMDiffSubbundleFrames_sup_map_radical (hc : σ.Compatible Jc)
    (hk : ∀ q, finrank ℝ (LinearMap.ker ((SmoothForm.mpullback f f.contMDiff σ).bilinFormAt q)) =
      k) :
    HasLocalContMDiffSubbundleFrames J ∞ E (Fin (finrank ℝ E' + k))
      (E := (f : Q → M) *ᵖ (TangentSpace I))
      fun q ↦ (mfderiv J I f q).range ⊔ ((mfderiv J I f q).range ⊓
        (hc.isNondegenerate.symplecticFormAt (f q)).orthogonal (mfderiv J I f q).range).map
          (Jc.almostComplexStructureAt (f q)).toLinearMap :=
  (f.isImmersion.hasLocalContMDiffSubbundleFrames_range_mfderiv (by simp) (by simp)).sup_fin
    (f.hasLocalContMDiffSubbundleFrames_map_radical hc.isNondegenerate hk) fun q ↦
      (hc.compatibleAt (f q)).disjoint_map

/-- **Frames of the normal complement.** If the kernels of `f^* σ` all have dimension `k`, the
normal complements `E = (W ⊕ J K)^ω` of the tangent images `W`, for `ω = σ_{f q}`, have `C^∞`
local frames of size `dim M - (dim Q + k)` in the pull-back `f *ᵖ TM`. -/
theorem hasLocalContMDiffSubbundleFrames_normalComplement (hc : σ.Compatible Jc)
    (hk : ∀ q, finrank ℝ (LinearMap.ker ((SmoothForm.mpullback f f.contMDiff σ).bilinFormAt q)) =
      k) :
    HasLocalContMDiffSubbundleFrames J ∞ E (Fin (finrank ℝ E - (finrank ℝ E' + k)))
      (E := (f : Q → M) *ᵖ (TangentSpace I))
      fun q ↦ (hc.isNondegenerate.symplecticFormAt (f q)).normalComplement
        (Jc.almostComplexStructureAt (f q)) (mfderiv J I f q).range := by
  have : ContMDiffVectorBundle ∞ E ((f : Q → M) *ᵖ (TangentSpace I)) J :=
    Bundle.Pullback.contMDiffVectorBundle (E := TangentSpace I) f.contMDiff
  have h := (f.hasLocalContMDiffSubbundleFrames_sup_map_radical hc hk).orthogonal_of_isCompl
    (E := (f : Q → M) *ᵖ (TangentSpace I)) (β := fun q ↦ σ.flat (f q))
    (SmoothTwoForm.contMDiff_flat_pullback σ f f.contMDiff) fun q ↦ by
      have h := (hc.compatibleAt (f q)).isCompl_sup_map_normalComplement
        (W := (mfderiv J I f q).range)
      rw [SymplecticForm.normalComplement_def,
        ← hc.isNondegenerate.orthogonal_flat (f q) (_ ⊔ _)] at h
      exact h
  -- The fibres of the pull-back are the tangent spaces of `M` under another name, so the
  -- family is rewritten as the family of `h` before it is closed by `h`.
  have hfun : (fun q ↦ (hc.isNondegenerate.symplecticFormAt (f q)).normalComplement
      (Jc.almostComplexStructureAt (f q)) (mfderiv J I f q).range) = fun q ↦
      LinearMap.BilinForm.orthogonal (σ.flat (f q)).toLinearMap₁₂
        ((mfderiv J I f q).range ⊔ ((mfderiv J I f q).range ⊓
          (hc.isNondegenerate.symplecticFormAt (f q)).orthogonal (mfderiv J I f q).range).map
            (Jc.almostComplexStructureAt (f q)).toLinearMap) := funext fun q ↦ by
    rw [SymplecticForm.normalComplement_def, hc.isNondegenerate.orthogonal_flat]
  rw [hfun]
  exact h

/-- **Frames of the metric complement of the radical.** If the kernels of `f^* σ` all have
dimension `k`, the orthogonal complements `K^{⊥g}` of the radicals `K` of the tangent images,
for the metrics `g = σ(·, J ·)`, have `C^∞` local frames of size `dim M - k` in the pull-back
`f *ᵖ TM`. -/
theorem hasLocalContMDiffSubbundleFrames_orthogonal_radical (hc : σ.Compatible Jc)
    (hk : ∀ q, finrank ℝ (LinearMap.ker ((SmoothForm.mpullback f f.contMDiff σ).bilinFormAt q)) =
      k) :
    HasLocalContMDiffSubbundleFrames J ∞ E (Fin (finrank ℝ E - k))
      (E := (f : Q → M) *ᵖ (TangentSpace I))
      fun q ↦ ((hc.isNondegenerate.symplecticFormAt (f q)).associatedBilinForm
        (Jc.almostComplexStructureAt (f q))).orthogonal ((mfderiv J I f q).range ⊓
          (hc.isNondegenerate.symplecticFormAt (f q)).orthogonal (mfderiv J I f q).range) := by
  have : ContMDiffVectorBundle ∞ E ((f : Q → M) *ᵖ (TangentSpace I)) J :=
    Bundle.Pullback.contMDiffVectorBundle (E := TangentSpace I) f.contMDiff
  have h := (f.hasLocalContMDiffSubbundleFrames_radical hc.isNondegenerate hk).orthogonal_of_isCompl
    (E := (f : Q → M) *ᵖ (TangentSpace I)) (β := fun q ↦ σ.flatComp Jc.toEndomorphism (f q))
    (SmoothTwoForm.contMDiff_flatComp_pullback σ Jc.toEndomorphism f
      f.contMDiff) fun q ↦ by
      have h := (hc.compatibleAt (f q)).isCompl_orthogonal_associatedBilinForm
        ((mfderiv J I f q).range ⊓
          (hc.isNondegenerate.symplecticFormAt (f q)).orthogonal (mfderiv J I f q).range)
      rw [← hc.orthogonal_flatComp] at h
      exact h
  -- As for `hasLocalContMDiffSubbundleFrames_normalComplement`, the family is rewritten as that
  -- of `h`.
  have hfun : (fun q ↦ ((hc.isNondegenerate.symplecticFormAt (f q)).associatedBilinForm
      (Jc.almostComplexStructureAt (f q))).orthogonal ((mfderiv J I f q).range ⊓
        (hc.isNondegenerate.symplecticFormAt (f q)).orthogonal (mfderiv J I f q).range)) =
      fun q ↦ LinearMap.BilinForm.orthogonal (σ.flatComp Jc.toEndomorphism (f q)).toLinearMap₁₂
        ((mfderiv J I f q).range ⊓
          (hc.isNondegenerate.symplecticFormAt (f q)).orthogonal (mfderiv J I f q).range) :=
    funext fun q ↦ (hc.orthogonal_flatComp _ _).symm
  rw [hfun]
  exact h

/-- **Frames of the radical complement.** If the kernels of `f^* σ` all have dimension `k`, the
radical complements `H = W ∩ K^{⊥g}` of the tangent images `W`, for `ω = σ_{f q}` and
`g = ω(·, J ·)`, have `C^∞` local frames of size `dim Q - k` in the pull-back `f *ᵖ TM`. -/
theorem hasLocalContMDiffSubbundleFrames_radicalComplement (hc : σ.Compatible Jc)
    (hk : ∀ q, finrank ℝ (LinearMap.ker ((SmoothForm.mpullback f f.contMDiff σ).bilinFormAt q)) =
      k) :
    HasLocalContMDiffSubbundleFrames J ∞ E (Fin (finrank ℝ E' - k))
      (E := (f : Q → M) *ᵖ (TangentSpace I))
      fun q ↦ (hc.isNondegenerate.symplecticFormAt (f q)).radicalComplement
        (Jc.almostComplexStructureAt (f q)) (mfderiv J I f q).range := by
  have : ContMDiffVectorBundle ∞ E ((f : Q → M) *ᵖ (TangentSpace I)) J :=
    Bundle.Pullback.contMDiffVectorBundle (E := TangentSpace I) f.contMDiff
  -- The radical `K` and its orthogonal `S = K^{⊥g}` for the metric `g = σ(·, J ·)`.
  let K : Π q, Submodule ℝ (TangentSpace I (f q)) := fun q ↦ (mfderiv J I f q).range ⊓
    (hc.isNondegenerate.symplecticFormAt (f q)).orthogonal (mfderiv J I f q).range
  let S : Π q, Submodule ℝ (TangentSpace I (f q)) := fun q ↦
    ((hc.isNondegenerate.symplecticFormAt (f q)).associatedBilinForm
      (Jc.almostComplexStructureAt (f q))).orthogonal (K q)
  have hKS (q : Q) : IsCompl (K q) (S q) :=
    (hc.compatibleAt (f q)).isCompl_orthogonal_associatedBilinForm (K q)
  -- The projection onto `S` along `K` is smooth, as both are smooth subbundles.
  have hQ := (f.hasLocalContMDiffSubbundleFrames_orthogonal_radical hc hk)
    |>.contMDiff_totalSpace_projection_of_isCompl
      (f.hasLocalContMDiffSubbundleFrames_radical hc.isNondegenerate hk) fun q ↦ (hKS q).symm
  refine hasLocalContMDiffSubbundleFrames_of_contMDiff_totalSpace_range
    (E₂ := (f : Q → M) *ᵖ (TangentSpace I))
    (fun q ↦ (S q).projection (K q) (hKS q).symm ∘ₗ
      (mfderiv J I f q : TangentSpace J q →ₗ[ℝ] TangentSpace I (f q)))
    (hQ.comp (Pullback.contMDiff_totalSpace_mfderiv f f.contMDiff)) (fun q ↦ ?_) fun q ↦ ?_
  · -- The ranges are stated as subspaces of the tangent spaces of `M`, of which the fibres of
    -- the pull-back are another name.
    have h : LinearMap.range ((S q).projection (K q) (hKS q).symm ∘ₗ
        (mfderiv J I f q : TangentSpace J q →ₗ[ℝ] TangentSpace I (f q))) =
        (hc.isNondegenerate.symplecticFormAt (f q)).radicalComplement
          (Jc.almostComplexStructureAt (f q)) (mfderiv J I f q).range := by
      rw [LinearMap.range_comp,
        (hc.compatibleAt (f q)).map_projection_orthogonal_eq_radicalComplement]
    exact h
  · -- `W = H ⊕ K`, with `dim W = dim Q` and `dim K = k`.
    have hW : finrank ℝ (mfderiv J I f q).range = finrank ℝ E' := by
      have h := (f.isImmersion.hasLocalContMDiffSubbundleFrames_range_mfderiv (m := ∞)
        (by simp) (by simp)).hasLocalSubbundleFrames.finrank_eq q
      rw [Fintype.card_fin] at h
      exact h
    have hK : finrank ℝ (K q) = k := by
      have h := (f.hasLocalContMDiffSubbundleFrames_radical hc.isNondegenerate hk)
        |>.hasLocalSubbundleFrames.finrank_eq q
      rw [Fintype.card_fin] at h
      exact h
    have h := Submodule.finrank_sup_add_finrank_inf_eq
      ((hc.isNondegenerate.symplecticFormAt (f q)).radicalComplement
        (Jc.almostComplexStructureAt (f q)) (mfderiv J I f q).range) (K q)
    rw [(hc.compatibleAt (f q)).radicalComplement_sup_inf,
      (hc.compatibleAt (f q)).disjoint_radicalComplement_inf.eq_bot, finrank_bot] at h
    have h' : finrank ℝ ((hc.isNondegenerate.symplecticFormAt (f q)).radicalComplement
        (Jc.almostComplexStructureAt (f q)) (mfderiv J I f q).range) = finrank ℝ E' - k := by
      omega
    exact h'

/-- **Frames of `J K ⊕ E`.** If the kernels of `f^* σ` all have dimension `k`, the sums of the
images `J K` of the radicals of the tangent images and of the normal complements `E` have `C^∞`
local frames of size `k + (dim M - (dim Q + k))` in the pull-back `f *ᵖ TM`. -/
theorem hasLocalContMDiffSubbundleFrames_map_radical_sup_normalComplement (hc : σ.Compatible Jc)
    (hk : ∀ q, finrank ℝ (LinearMap.ker ((SmoothForm.mpullback f f.contMDiff σ).bilinFormAt q)) =
      k) :
    HasLocalContMDiffSubbundleFrames J ∞ E (Fin (k + (finrank ℝ E - (finrank ℝ E' + k))))
      (E := (f : Q → M) *ᵖ (TangentSpace I))
      fun q ↦ ((mfderiv J I f q).range ⊓
        (hc.isNondegenerate.symplecticFormAt (f q)).orthogonal (mfderiv J I f q).range).map
          (Jc.almostComplexStructureAt (f q)).toLinearMap ⊔
        (hc.isNondegenerate.symplecticFormAt (f q)).normalComplement
          (Jc.almostComplexStructureAt (f q)) (mfderiv J I f q).range :=
  (f.hasLocalContMDiffSubbundleFrames_map_radical hc.isNondegenerate hk).sup_fin
    (f.hasLocalContMDiffSubbundleFrames_normalComplement hc hk) fun q ↦
      (hc.compatibleAt (f q)).isCompl_sup_map_normalComplement.disjoint.mono_left le_sup_right

/-- **Frames of `W ⊕ E`.** If the kernels of `f^* σ` all have dimension `k`, the sums of the
tangent images `W` and of their normal complements `E` have `C^∞` local frames of size
`dim Q + (dim M - (dim Q + k))` in the pull-back `f *ᵖ TM`. -/
theorem hasLocalContMDiffSubbundleFrames_sup_normalComplement (hc : σ.Compatible Jc)
    (hk : ∀ q, finrank ℝ (LinearMap.ker ((SmoothForm.mpullback f f.contMDiff σ).bilinFormAt q)) =
      k) :
    HasLocalContMDiffSubbundleFrames J ∞ E (Fin (finrank ℝ E' + (finrank ℝ E - (finrank ℝ E' + k))))
      (E := (f : Q → M) *ᵖ (TangentSpace I))
      fun q ↦ (mfderiv J I f q).range ⊔
        (hc.isNondegenerate.symplecticFormAt (f q)).normalComplement
          (Jc.almostComplexStructureAt (f q)) (mfderiv J I f q).range :=
  (f.isImmersion.hasLocalContMDiffSubbundleFrames_range_mfderiv (by simp) (by simp)).sup_fin
    (f.hasLocalContMDiffSubbundleFrames_normalComplement hc hk) fun q ↦
      (hc.compatibleAt (f q)).isCompl_sup_map_normalComplement.disjoint.mono_left le_sup_left

/-- **The projection onto the tangent image along `J K ⊕ E` is smooth.** If the kernels of
`f^* σ` all have dimension `k`, the projection of the pull-back `f *ᵖ TM` onto the tangent
images `W` along `J K ⊕ E` is a smooth map from the total space of `f *ᵖ TM` to itself. -/
theorem contMDiff_totalSpace_projection_range_mfderiv (hc : σ.Compatible Jc)
    (hk : ∀ q, finrank ℝ (LinearMap.ker ((SmoothForm.mpullback f f.contMDiff σ).bilinFormAt q)) =
      k) :
    ContMDiff (J.prod 𝓘(ℝ, E)) (J.prod 𝓘(ℝ, E)) ∞
      (fun w : TotalSpace E ((f : Q → M) *ᵖ (TangentSpace I)) ↦
        (⟨w.proj, (mfderiv J I f w.proj).range.projection _
          (hc.compatibleAt (f w.proj)).isCompl_map_sup_normalComplement w.snd⟩ :
          TotalSpace E ((f : Q → M) *ᵖ (TangentSpace I)))) := by
  have : ContMDiffVectorBundle ∞ E ((f : Q → M) *ᵖ (TangentSpace I)) J :=
    Bundle.Pullback.contMDiffVectorBundle (E := TangentSpace I) f.contMDiff
  exact (f.isImmersion.hasLocalContMDiffSubbundleFrames_range_mfderiv (by simp) (by simp))
    |>.contMDiff_totalSpace_projection_of_isCompl
      (f.hasLocalContMDiffSubbundleFrames_map_radical_sup_normalComplement hc hk) fun q ↦
        (hc.compatibleAt (f q)).isCompl_map_sup_normalComplement

/-- **The projection onto `J K` along `W ⊕ E` is smooth.** If the kernels of `f^* σ` all have
dimension `k`, the projection of the pull-back `f *ᵖ TM` onto the images `J K` of the radicals
of the tangent images `W`, along `W ⊕ E`, is a smooth map from the total space of `f *ᵖ TM` to
itself. -/
theorem contMDiff_totalSpace_projection_map_radical (hc : σ.Compatible Jc)
    (hk : ∀ q, finrank ℝ (LinearMap.ker ((SmoothForm.mpullback f f.contMDiff σ).bilinFormAt q)) =
      k) :
    ContMDiff (J.prod 𝓘(ℝ, E)) (J.prod 𝓘(ℝ, E)) ∞
      (fun w : TotalSpace E ((f : Q → M) *ᵖ (TangentSpace I)) ↦
        (⟨w.proj, (((mfderiv J I f w.proj).range ⊓
          (hc.isNondegenerate.symplecticFormAt (f w.proj)).orthogonal
            (mfderiv J I f w.proj).range).map
              (Jc.almostComplexStructureAt (f w.proj)).toLinearMap).projection _
          (hc.compatibleAt (f w.proj)).isCompl_map_self_sup_normalComplement w.snd⟩ :
          TotalSpace E ((f : Q → M) *ᵖ (TangentSpace I)))) := by
  have : ContMDiffVectorBundle ∞ E ((f : Q → M) *ᵖ (TangentSpace I)) J :=
    Bundle.Pullback.contMDiffVectorBundle (E := TangentSpace I) f.contMDiff
  exact (f.hasLocalContMDiffSubbundleFrames_map_radical hc.isNondegenerate hk)
    |>.contMDiff_totalSpace_projection_of_isCompl
      (f.hasLocalContMDiffSubbundleFrames_sup_normalComplement hc hk) fun q ↦
        (hc.compatibleAt (f q)).isCompl_map_self_sup_normalComplement

/-- **The projection onto the normal complement along `W ⊕ J K` is smooth.** If the kernels of
`f^* σ` all have dimension `k`, the projection of the pull-back `f *ᵖ TM` onto the normal
complements `E` of the tangent images `W`, along `W ⊕ J K`, is a smooth map from the total
space of `f *ᵖ TM` to itself. -/
theorem contMDiff_totalSpace_projection_normalComplement (hc : σ.Compatible Jc)
    (hk : ∀ q, finrank ℝ (LinearMap.ker ((SmoothForm.mpullback f f.contMDiff σ).bilinFormAt q)) =
      k) :
    ContMDiff (J.prod 𝓘(ℝ, E)) (J.prod 𝓘(ℝ, E)) ∞
      (fun w : TotalSpace E ((f : Q → M) *ᵖ (TangentSpace I)) ↦
        (⟨w.proj, ((hc.isNondegenerate.symplecticFormAt (f w.proj)).normalComplement
          (Jc.almostComplexStructureAt (f w.proj)) (mfderiv J I f w.proj).range).projection _
          (hc.compatibleAt (f w.proj)).isCompl_sup_map_normalComplement.symm w.snd⟩ :
          TotalSpace E ((f : Q → M) *ᵖ (TangentSpace I)))) := by
  have : ContMDiffVectorBundle ∞ E ((f : Q → M) *ᵖ (TangentSpace I)) J :=
    Bundle.Pullback.contMDiffVectorBundle (E := TangentSpace I) f.contMDiff
  exact (f.hasLocalContMDiffSubbundleFrames_normalComplement hc hk)
    |>.contMDiff_totalSpace_projection_of_isCompl
      (f.hasLocalContMDiffSubbundleFrames_sup_map_radical hc hk) fun q ↦
        (hc.compatibleAt (f q)).isCompl_sup_map_normalComplement.symm

/-- **The metric projection onto the radical is smooth.** If the kernels of `f^* σ` all have
dimension `k`, the projection of the pull-back `f *ᵖ TM` onto the radicals `K` of the tangent
images along their orthogonal complements `K^{⊥g}`, for the metrics `g = σ(·, J ·)`, is a smooth
map from the total space of `f *ᵖ TM` to itself. -/
theorem contMDiff_totalSpace_projection_radical (hc : σ.Compatible Jc)
    (hk : ∀ q, finrank ℝ (LinearMap.ker ((SmoothForm.mpullback f f.contMDiff σ).bilinFormAt q)) =
      k) :
    ContMDiff (J.prod 𝓘(ℝ, E)) (J.prod 𝓘(ℝ, E)) ∞
      (fun w : TotalSpace E ((f : Q → M) *ᵖ (TangentSpace I)) ↦
        (⟨w.proj, ((mfderiv J I f w.proj).range ⊓
          (hc.isNondegenerate.symplecticFormAt (f w.proj)).orthogonal
            (mfderiv J I f w.proj).range).projection _
          ((hc.compatibleAt (f w.proj)).isCompl_orthogonal_associatedBilinForm _) w.snd⟩ :
          TotalSpace E ((f : Q → M) *ᵖ (TangentSpace I)))) := by
  have : ContMDiffVectorBundle ∞ E ((f : Q → M) *ᵖ (TangentSpace I)) J :=
    Bundle.Pullback.contMDiffVectorBundle (E := TangentSpace I) f.contMDiff
  exact (f.hasLocalContMDiffSubbundleFrames_radical hc.isNondegenerate hk)
    |>.contMDiff_totalSpace_projection_of_isCompl
      (f.hasLocalContMDiffSubbundleFrames_orthogonal_radical hc hk) fun q ↦
        (hc.compatibleAt (f q)).isCompl_orthogonal_associatedBilinForm _

end TauCeti.SmoothEmbedding

end
