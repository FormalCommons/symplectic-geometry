/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.LinearAlgebra.Range
public import SymplecticGeometry.LinearAlgebra.Symplectic.Extension
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic
public import TauCeti.Topology.VectorBundle.Pullback
import SymplecticGeometry.Geometry.Manifold.VectorBundle.Adjoint
import SymplecticGeometry.Geometry.Symplectic.Neighborhood.Frames
import SymplecticGeometry.Geometry.Symplectic.Manifold.Flat
import SymplecticGeometry.Geometry.Manifold.VectorBundle.Pullback
import SymplecticGeometry.Topology.VectorBundle.Pullback
import SymplecticGeometry.Geometry.Manifold.IsManifold.Basic
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Smooth

/-!
# The linear symplectic extension along a submanifold

Let `f₀ : Q → M₀` and `f₁ : Q → M₁` be smooth embeddings of the same manifold into manifolds with
two-forms `σ₀`, `σ₁` and compatible almost complex structures `J₀`, `J₁`, such that
`f₁^* σ₁ = f₀^* σ₀`, and with `dim M₀ = dim M₁`. Write `ωⱼ` for the symplectic form `σⱼ` at
`fⱼ q`, `Wⱼ = d(fⱼ)_q(T_q Q)` for the tangent images and `Wⱼ^ω` for their symplectic complements.
Let `L q : T_{f₀ q} M₀ → T_{f₁ q} M₁` be linear maps that carry `W₀^ω` into `W₁^ω` and preserve
`ω` there.

At each `q`, the linear algebra of
`SymplecticGeometry/LinearAlgebra/Symplectic/Extension.lean` gives the linear symplectomorphism
`TauCeti.SymplecticForm.Compatible.extendAlong` for `b = df₁ ∘ df₀⁻¹ : W₀ ≃ W₁`
(`TauCeti.SmoothEmbedding.mfderivRangeEquiv`) and `L q`. This file collects these maps into
`TauCeti.SmoothEmbedding.smoothExtendAlong`, written `A` below, and shows that

* it extends the derivatives: `A_q ∘ d(f₀)_q = d(f₁)_q`
  (`TauCeti.SmoothEmbedding.smoothExtendAlong_comp_mfderiv`);
* it is a linear symplectomorphism at every point
  (`TauCeti.SmoothEmbedding.isSymplectomorphism_smoothExtendAlong`);
* it induces the same map as `L` on the reduced normal spaces: `A_q v - L_q v ∈ W₁` for
  `v ∈ W₀^ω` (`TauCeti.SmoothEmbedding.smoothExtendAlong_sub_mem`);
* if the kernels of `f₀^* σ₀` have constant dimension and `L` is a smooth section of the bundle
  of linear maps between the pull-backs `f₀ *ᵖ TM₀` and `f₁ *ᵖ TM₁`, then so is `A`
  (`TauCeti.SmoothEmbedding.contMDiff_smoothExtendAlong`).

## Smoothness

The formula `TauCeti.SymplecticForm.Compatible.extendAlong_def` is built from three kinds of
steps, each smooth in `q`:

* projections along the splittings `T_{f q} M = W ⊕ J K ⊕ E` and `T_{f q} M = K ⊕ K^{⊥g}`, which
  `SymplecticGeometry/Geometry/Symplectic/Neighborhood/Frames.lean` shows smooth as maps of total
  spaces, and Tau Ceti's `TauCeti.contMDiff_hom_bundle_iff` turns into smooth sections of the
  bundle of endomorphisms;
* `b` and `b⁻¹`, which agree on `W₀` and `W₁` with `df₁ ∘ S₀` and `df₀ ∘ S₁` for smooth left
  inverses `Sⱼ` of the derivatives (`TauCeti.SmoothEmbedding.exists_contMDiff_leftInverse_mfderiv`,
  which is `Manifold.IsImmersion.exists_contMDiff_leftInverse_mfderiv` of
  `SymplecticGeometry/Geometry/Manifold/VectorBundle/Adjoint.lean` for the form `σ(J ·, ·)`,
  definite by `TauCeti.SmoothTwoForm.Tames.flatComp_apply_self_eq_zero_iff`);
* the adjoint `(ω₁^♭)⁻¹ ∘ T^* ∘ ω₀^♭` of `T = b⁻¹ ∘ (projection onto W₁)`, smooth by
  `ContMDiff.clm_bundle_bilinAdjoint`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §3.4,
  where such extensions along a submanifold are used in the proofs of the neighbourhood theorems.
-/

public section

open Bundle Module Set
open scoped Manifold ContDiff Bundle

namespace TauCeti.SmoothEmbedding

section Pieces

variable {E E' H H' M Q : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [TopologicalSpace Q] [ChartedSpace H' Q]
  [IsManifold J ∞ Q]
  (f : SmoothEmbedding J I ∞ Q M) {σ : SmoothTwoForm I M} {Jc : SmoothAlmostComplexStructure I M}

/-- **A smooth left inverse of the derivative.** For a smooth embedding `f` into a manifold with
a two-form `σ` and an almost complex structure `J` tamed by `σ`, there is a smooth section `S` of
the bundle of linear maps from the pull-back `f *ᵖ TM` to `TQ` with `S_q ∘ df_q = id` at every
`q`: `Manifold.IsImmersion.exists_contMDiff_leftInverse_mfderiv` for the form `σ(J ·, ·)`. -/
theorem exists_contMDiff_leftInverse_mfderiv (h : σ.Tames Jc) :
    ∃ S : ∀ q, TangentSpace I (f q) →L[ℝ] TangentSpace J q,
      ContMDiff J (J.prod 𝓘(ℝ, E →L[ℝ] E')) ∞ (fun q ↦ TotalSpace.mk' (E →L[ℝ] E')
        (E := fun q ↦ ((f : Q → M) *ᵖ (TangentSpace I)) q →L[ℝ] TangentSpace J q) q (S q)) ∧
      ∀ q, Function.LeftInverse (S q) (mfderiv J I f q) :=
  f.isImmersion.exists_contMDiff_leftInverse_mfderiv (σ.flatComp Jc.toEndomorphism).contMDiff
    fun _ _ ↦ h.flatComp_apply_self_eq_zero_iff.1

variable [FiniteDimensional ℝ E]

/-- The projection onto the tangent image `W` along `J K ⊕ E`. -/
private noncomputable def projRange (hc : σ.Compatible Jc) (q : Q) :
    TangentSpace I (f q) →L[ℝ] TangentSpace I (f q) :=
  LinearMap.toContinuousLinearMap ((mfderiv J I f q).range.projection _
    (hc.compatibleAt (f q)).isCompl_map_sup_normalComplement)

/-- The projection onto `J K` along `W ⊕ E`. -/
private noncomputable def projMapRadical (hc : σ.Compatible Jc) (q : Q) :
    TangentSpace I (f q) →L[ℝ] TangentSpace I (f q) :=
  LinearMap.toContinuousLinearMap ((((mfderiv J I f q).range ⊓
    (hc.isNondegenerate.symplecticFormAt (f q)).orthogonal (mfderiv J I f q).range).map
      (Jc.almostComplexStructureAt (f q)).toLinearMap).projection _
    (hc.compatibleAt (f q)).isCompl_map_self_sup_normalComplement)

/-- The projection onto the normal complement `E` along `W ⊕ J K`. -/
private noncomputable def projNormalComplement (hc : σ.Compatible Jc) (q : Q) :
    TangentSpace I (f q) →L[ℝ] TangentSpace I (f q) :=
  LinearMap.toContinuousLinearMap (((hc.isNondegenerate.symplecticFormAt (f q)).normalComplement
    (Jc.almostComplexStructureAt (f q)) (mfderiv J I f q).range).projection _
    (hc.compatibleAt (f q)).isCompl_sup_map_normalComplement.symm)

/-- The projection onto the radical `K` along `K^{⊥g}`. -/
private noncomputable def projRadical (hc : σ.Compatible Jc) (q : Q) :
    TangentSpace I (f q) →L[ℝ] TangentSpace I (f q) :=
  LinearMap.toContinuousLinearMap (((mfderiv J I f q).range ⊓
    (hc.isNondegenerate.symplecticFormAt (f q)).orthogonal (mfderiv J I f q).range).projection _
    ((hc.compatibleAt (f q)).isCompl_orthogonal_associatedBilinForm _))

/-- If the kernels of `f^* σ` have constant dimension, the projection onto the tangent image is
a smooth section of the bundle of endomorphisms of `f *ᵖ TM`. -/
private theorem contMDiff_projRange (hc : σ.Compatible Jc) {k : ℕ}
    (hk : ∀ q, finrank ℝ (LinearMap.ker ((SmoothForm.mpullback f f.contMDiff σ).bilinFormAt q)) =
      k) :
    ContMDiff J (J.prod 𝓘(ℝ, E →L[ℝ] E)) ∞ (fun q ↦ TotalSpace.mk' (E →L[ℝ] E)
      (E := fun q ↦ ((f : Q → M) *ᵖ (TangentSpace I)) q →L[ℝ]
        ((f : Q → M) *ᵖ (TangentSpace I)) q) q (projRange f hc q)) := by
  unfold projRange
  exact (contMDiff_hom_bundle_iff (E₁ := (f : Q → M) *ᵖ (TangentSpace I))
    (E₂ := (f : Q → M) *ᵖ (TangentSpace I)) _).2
      (f.contMDiff_totalSpace_projection_range_mfderiv hc hk)

/-- If the kernels of `f^* σ` have constant dimension, the projection onto `J K` is a smooth
section of the bundle of endomorphisms of `f *ᵖ TM`. -/
private theorem contMDiff_projMapRadical (hc : σ.Compatible Jc) {k : ℕ}
    (hk : ∀ q, finrank ℝ (LinearMap.ker ((SmoothForm.mpullback f f.contMDiff σ).bilinFormAt q)) =
      k) :
    ContMDiff J (J.prod 𝓘(ℝ, E →L[ℝ] E)) ∞ (fun q ↦ TotalSpace.mk' (E →L[ℝ] E)
      (E := fun q ↦ ((f : Q → M) *ᵖ (TangentSpace I)) q →L[ℝ]
        ((f : Q → M) *ᵖ (TangentSpace I)) q) q (projMapRadical f hc q)) := by
  unfold projMapRadical
  exact (contMDiff_hom_bundle_iff (E₁ := (f : Q → M) *ᵖ (TangentSpace I))
    (E₂ := (f : Q → M) *ᵖ (TangentSpace I)) _).2
      (f.contMDiff_totalSpace_projection_map_radical hc hk)

/-- If the kernels of `f^* σ` have constant dimension, the projection onto the normal complement
is a smooth section of the bundle of endomorphisms of `f *ᵖ TM`. -/
private theorem contMDiff_projNormalComplement (hc : σ.Compatible Jc) {k : ℕ}
    (hk : ∀ q, finrank ℝ (LinearMap.ker ((SmoothForm.mpullback f f.contMDiff σ).bilinFormAt q)) =
      k) :
    ContMDiff J (J.prod 𝓘(ℝ, E →L[ℝ] E)) ∞ (fun q ↦ TotalSpace.mk' (E →L[ℝ] E)
      (E := fun q ↦ ((f : Q → M) *ᵖ (TangentSpace I)) q →L[ℝ]
        ((f : Q → M) *ᵖ (TangentSpace I)) q) q (projNormalComplement f hc q)) := by
  unfold projNormalComplement
  exact (contMDiff_hom_bundle_iff (E₁ := (f : Q → M) *ᵖ (TangentSpace I))
    (E₂ := (f : Q → M) *ᵖ (TangentSpace I)) _).2
      (f.contMDiff_totalSpace_projection_normalComplement hc hk)

/-- If the kernels of `f^* σ` have constant dimension, the projection onto the radical is a smooth
section of the bundle of endomorphisms of `f *ᵖ TM`. -/
private theorem contMDiff_projRadical (hc : σ.Compatible Jc) {k : ℕ}
    (hk : ∀ q, finrank ℝ (LinearMap.ker ((SmoothForm.mpullback f f.contMDiff σ).bilinFormAt q)) =
      k) :
    ContMDiff J (J.prod 𝓘(ℝ, E →L[ℝ] E)) ∞ (fun q ↦ TotalSpace.mk' (E →L[ℝ] E)
      (E := fun q ↦ ((f : Q → M) *ᵖ (TangentSpace I)) q →L[ℝ]
        ((f : Q → M) *ᵖ (TangentSpace I)) q) q (projRadical f hc q)) := by
  unfold projRadical
  exact (contMDiff_hom_bundle_iff (E₁ := (f : Q → M) *ᵖ (TangentSpace I))
    (E₂ := (f : Q → M) *ᵖ (TangentSpace I)) _).2
      (f.contMDiff_totalSpace_projection_radical hc hk)


end Pieces

section Extension

variable {E₀ E₁ E' H₀ H₁ H' M₀ M₁ Q : Type*}
  [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀]
  [TopologicalSpace H₀] {I₀ : ModelWithCorners ℝ E₀ H₀} [TopologicalSpace M₀]
  [ChartedSpace H₀ M₀] [IsManifold I₀ ∞ M₀]
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
  [TopologicalSpace H₁] {I₁ : ModelWithCorners ℝ E₁ H₁} [TopologicalSpace M₁]
  [ChartedSpace H₁ M₁] [IsManifold I₁ ∞ M₁]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [TopologicalSpace Q] [ChartedSpace H' Q]
  [IsManifold J ∞ Q]
  {f₀ : SmoothEmbedding J I₀ ∞ Q M₀} {f₁ : SmoothEmbedding J I₁ ∞ Q M₁}
  {σ₀ : SmoothTwoForm I₀ M₀} {σ₁ : SmoothTwoForm I₁ M₁}
  {Jc₀ : SmoothAlmostComplexStructure I₀ M₀} {Jc₁ : SmoothAlmostComplexStructure I₁ M₁}

variable (f₀ f₁) in
/-- The isomorphism `df₁ ∘ df₀⁻¹` from the tangent image of the immersion `f₀` at `q` to that of
`f₁`. -/
noncomputable def mfderivRangeEquiv (q : Q) :
    (mfderiv J I₀ f₀ q).range ≃ₗ[ℝ] (mfderiv J I₁ f₁ q).range :=
  LinearEquiv.ofInjectiveRange _ _ (f₀.isImmersion.mfderiv_injective (by simp) q)
    (f₁.isImmersion.mfderiv_injective (by simp) q)

omit [FiniteDimensional ℝ E₀] [FiniteDimensional ℝ E₁] [IsManifold I₀ ∞ M₀] [IsManifold I₁ ∞ M₁]
  [IsManifold J ∞ Q] in
/-- `df₁ ∘ df₀⁻¹` sends `df₀ v` to `df₁ v`. -/
@[simp]
theorem mfderivRangeEquiv_apply_mfderiv (q : Q) (v : TangentSpace J q) :
    (mfderivRangeEquiv f₀ f₁ q ⟨mfderiv J I₀ f₀ q v, LinearMap.mem_range_self _ v⟩ :
      TangentSpace I₁ (f₁ q)) = mfderiv J I₁ f₁ q v := by
  rw [mfderivRangeEquiv]
  simpa using congrArg Subtype.val (LinearEquiv.ofInjectiveRange_apply _ _
    (f₀.isImmersion.mfderiv_injective (by simp) q) (f₁.isImmersion.mfderiv_injective (by simp) q) v
    (LinearMap.mem_range_self _ v))

omit [FiniteDimensional ℝ E₀] [FiniteDimensional ℝ E₁] [IsManifold I₀ ∞ M₀] [IsManifold I₁ ∞ M₁]
  [IsManifold J ∞ Q] in
/-- The inverse of `df₁ ∘ df₀⁻¹` is `df₀ ∘ df₁⁻¹`. -/
theorem mfderivRangeEquiv_symm (q : Q) :
    (mfderivRangeEquiv f₀ f₁ q).symm = mfderivRangeEquiv f₁ f₀ q := by
  rw [mfderivRangeEquiv, mfderivRangeEquiv, LinearEquiv.ofInjectiveRange_symm]

omit [FiniteDimensional ℝ E₀] [FiniteDimensional ℝ E₁] [IsManifold I₀ ∞ M₀] [IsManifold I₁ ∞ M₁]
  [IsManifold J ∞ Q] in
/-- The inverse of `df₁ ∘ df₀⁻¹` sends `df₁ v` to `df₀ v`. -/
@[simp]
theorem mfderivRangeEquiv_symm_apply_mfderiv (q : Q) (v : TangentSpace J q) :
    ((mfderivRangeEquiv f₀ f₁ q).symm ⟨mfderiv J I₁ f₁ q v, LinearMap.mem_range_self _ v⟩ :
      TangentSpace I₀ (f₀ q)) = mfderiv J I₀ f₀ q v := by
  rw [mfderivRangeEquiv_symm, mfderivRangeEquiv_apply_mfderiv]

omit [FiniteDimensional ℝ E₀] [FiniteDimensional ℝ E₁] [IsManifold I₀ ∞ M₀] [IsManifold I₁ ∞ M₁]
  [IsManifold J ∞ Q] in
/-- For any left inverse `S` of `df₀`, `df₁ ∘ df₀⁻¹` is `df₁ ∘ S` on the tangent image of `f₀`. -/
theorem mfderivRangeEquiv_apply_of_leftInverse (q : Q)
    {S : TangentSpace I₀ (f₀ q) → TangentSpace J q}
    (hS : Function.LeftInverse S (mfderiv J I₀ f₀ q)) (w : (mfderiv J I₀ f₀ q).range) :
    (mfderivRangeEquiv f₀ f₁ q w : TangentSpace I₁ (f₁ q)) = mfderiv J I₁ f₁ q (S w) := by
  obtain ⟨_, u, rfl⟩ := w
  simp [hS u]

omit [FiniteDimensional ℝ E₀] [FiniteDimensional ℝ E₁] in
/-- If `f₀` and `f₁` pull `σ₀` and `σ₁` back to the same form, then `df₁ ∘ df₀⁻¹` carries the
restriction of `σ₀` to the tangent image of `f₀` to the restriction of `σ₁` to that of `f₁`. -/
theorem symplecticFormAt_mfderivRangeEquiv (hω₀ : σ₀.IsNondegenerate)
    (hω₁ : σ₁.IsNondegenerate)
    (hσ : SmoothForm.mpullback f₁ f₁.contMDiff σ₁ = SmoothForm.mpullback f₀ f₀.contMDiff σ₀)
    (q : Q) (x y : (mfderiv J I₀ f₀ q).range) :
    hω₁.symplecticFormAt (f₁ q) (mfderivRangeEquiv f₀ f₁ q x) (mfderivRangeEquiv f₀ f₁ q y) =
      hω₀.symplecticFormAt (f₀ q) x y := by
  obtain ⟨_, u, rfl⟩ := x
  obtain ⟨_, v, rfl⟩ := y
  simpa [SmoothTwoForm.IsNondegenerate.symplecticFormAt_apply] using
    congr(SmoothForm.bilinFormAt $hσ q u v)

variable (hc₀ : σ₀.Compatible Jc₀) (hc₁ : σ₁.Compatible Jc₁)
  (hσ : SmoothForm.mpullback f₁ f₁.contMDiff σ₁ = SmoothForm.mpullback f₀ f₀.contMDiff σ₀)
  (L : ∀ q, TangentSpace I₀ (f₀ q) →L[ℝ] TangentSpace I₁ (f₁ q))
  (hL : ∀ q, ∀ v ∈ (hc₀.isNondegenerate.symplecticFormAt (f₀ q)).orthogonal
    (mfderiv J I₀ f₀ q).range,
      L q v ∈ (hc₁.isNondegenerate.symplecticFormAt (f₁ q)).orthogonal (mfderiv J I₁ f₁ q).range)
  (hLω : ∀ q, ∀ v ∈ (hc₀.isNondegenerate.symplecticFormAt (f₀ q)).orthogonal
    (mfderiv J I₀ f₀ q).range, ∀ w ∈ (hc₀.isNondegenerate.symplecticFormAt (f₀ q)).orthogonal
      (mfderiv J I₀ f₀ q).range,
      hc₁.isNondegenerate.symplecticFormAt (f₁ q) (L q v) (L q w) =
        hc₀.isNondegenerate.symplecticFormAt (f₀ q) v w)
  (hdim : finrank ℝ E₀ = finrank ℝ E₁)

/-- **The linear symplectic extension along a submanifold.** For smooth embeddings `f₀`, `f₁`
with `f₁^* σ₁ = f₀^* σ₀`, compatible almost complex structures, `dim M₀ = dim M₁`, and linear
maps `L q` carrying the symplectic complement `W₀^ω` of the tangent image `W₀` into `W₁^ω` and
preserving `ω` there, this is, at each `q`, the linear symplectomorphism
`TauCeti.SymplecticForm.Compatible.extendAlong` of `T_{f₀ q} M₀` onto `T_{f₁ q} M₁` for
`b = df₁ ∘ df₀⁻¹ : W₀ ≃ W₁` and `L q`. -/
noncomputable def smoothExtendAlong (q : Q) :
    TangentSpace I₀ (f₀ q) ≃L[ℝ] TangentSpace I₁ (f₁ q) :=
  ((hc₀.compatibleAt (f₀ q)).extendAlong (hc₁.compatibleAt (f₁ q)) (mfderivRangeEquiv f₀ f₁ q)
    (symplecticFormAt_mfderivRangeEquiv hc₀.isNondegenerate hc₁.isNondegenerate hσ q)
    (L q : TangentSpace I₀ (f₀ q) →ₗ[ℝ] TangentSpace I₁ (f₁ q)) (hL q) (hLω q)
    hdim).toContinuousLinearEquiv

theorem smoothExtendAlong_def (q : Q) :
    smoothExtendAlong hc₀ hc₁ hσ L hL hLω hdim q =
      ((hc₀.compatibleAt (f₀ q)).extendAlong (hc₁.compatibleAt (f₁ q))
        (mfderivRangeEquiv f₀ f₁ q)
        (symplecticFormAt_mfderivRangeEquiv hc₀.isNondegenerate hc₁.isNondegenerate hσ q)
        (L q : TangentSpace I₀ (f₀ q) →ₗ[ℝ] TangentSpace I₁ (f₁ q)) (hL q) (hLω q)
        hdim).toContinuousLinearEquiv :=
  (rfl)

/-- The extension sends `df₀ v` to `df₁ v`. -/
@[simp]
theorem smoothExtendAlong_apply_mfderiv (q : Q) (v : TangentSpace J q) :
    smoothExtendAlong hc₀ hc₁ hσ L hL hLω hdim q (mfderiv J I₀ f₀ q v) =
      mfderiv J I₁ f₁ q v := by
  have h := (hc₀.compatibleAt (f₀ q)).extendAlong_apply_coe (hc₁.compatibleAt (f₁ q))
    (mfderivRangeEquiv f₀ f₁ q)
    (symplecticFormAt_mfderivRangeEquiv hc₀.isNondegenerate hc₁.isNondegenerate hσ q)
    (L q : TangentSpace I₀ (f₀ q) →ₗ[ℝ] TangentSpace I₁ (f₁ q)) (hL q) (hLω q) hdim
    ⟨mfderiv J I₀ f₀ q v, LinearMap.mem_range_self _ v⟩
  rw [mfderivRangeEquiv_apply_mfderiv] at h
  rw [smoothExtendAlong_def, LinearEquiv.coe_toContinuousLinearEquiv', ← h]

/-- The extension extends the derivatives: `A_q ∘ d(f₀)_q = d(f₁)_q`. -/
theorem smoothExtendAlong_comp_mfderiv (q : Q) :
    (smoothExtendAlong hc₀ hc₁ hσ L hL hLω hdim q : TangentSpace I₀ (f₀ q) →L[ℝ]
      TangentSpace I₁ (f₁ q)).comp (mfderiv J I₀ f₀ q) = mfderiv J I₁ f₁ q :=
  ContinuousLinearMap.ext (smoothExtendAlong_apply_mfderiv hc₀ hc₁ hσ L hL hLω hdim q)

/-- The extension is a linear symplectomorphism at every point. -/
theorem isSymplectomorphism_smoothExtendAlong (q : Q) :
    (hc₀.isNondegenerate.symplecticFormAt (f₀ q)).IsSymplectomorphism
      (hc₁.isNondegenerate.symplecticFormAt (f₁ q))
      (smoothExtendAlong hc₀ hc₁ hσ L hL hLω hdim q).toLinearEquiv :=
  (hc₀.compatibleAt (f₀ q)).isSymplectomorphism_extendAlong (hc₁.compatibleAt (f₁ q)) _ _ _ _ _ _

/-- The extension induces the same map as `L` on the reduced normal spaces: `A_q v - L_q v` lies
in the tangent image of `f₁` for `v` in the symplectic complement of that of `f₀`. -/
theorem smoothExtendAlong_sub_mem (q : Q) {v : TangentSpace I₀ (f₀ q)}
    (hv : v ∈ (hc₀.isNondegenerate.symplecticFormAt (f₀ q)).orthogonal
      (mfderiv J I₀ f₀ q).range) :
    smoothExtendAlong hc₀ hc₁ hσ L hL hLω hdim q v - L q v ∈ (mfderiv J I₁ f₁ q).range :=
  (hc₀.compatibleAt (f₀ q)).extendAlong_sub_mem (hc₁.compatibleAt (f₁ q)) _ _ _ _ _ _ hv

/-- `b⁻¹` after the projection onto `W₁`, with `b⁻¹ = df₀ ∘ S₁` on `W₁`. -/
private noncomputable def backMap (S₁ : ∀ q, TangentSpace I₁ (f₁ q) →L[ℝ] TangentSpace J q)
    (q : Q) : TangentSpace I₁ (f₁ q) →L[ℝ] TangentSpace I₀ (f₀ q) :=
  (mfderiv J I₀ f₀ q).comp ((S₁ q).comp (projRange f₁ hc₁ q))

variable (σ₀) in
/-- The map `x ↦ u` with `ω₁(u, y) = ω₀(x, backMap y)` for all `y`. -/
private noncomputable def pairMap (S₁ : ∀ q, TangentSpace I₁ (f₁ q) →L[ℝ] TangentSpace J q)
    (q : Q) : TangentSpace I₀ (f₀ q) →L[ℝ] TangentSpace I₁ (f₁ q) :=
  ContinuousLinearMap.bilinAdjoint (σ₀.flat (f₀ q)) (σ₁.flat (f₁ q)) (backMap hc₁ S₁ q)

/-- The formula of `TauCeti.SymplecticForm.Compatible.extendAlong_def`, with `b = df₁ ∘ S₀` and
`b⁻¹ = df₀ ∘ S₁`. -/
private noncomputable def extendFormula
    (S₀ : ∀ q, TangentSpace I₀ (f₀ q) →L[ℝ] TangentSpace J q)
    (S₁ : ∀ q, TangentSpace I₁ (f₁ q) →L[ℝ] TangentSpace J q) (q : Q) :
    TangentSpace I₀ (f₀ q) →L[ℝ] TangentSpace I₁ (f₁ q) :=
  (mfderiv J I₁ f₁ q).comp ((S₀ q).comp (projRange f₀ hc₀ q)) +
    (pairMap σ₀ hc₁ S₁ q - (2⁻¹ : ℝ) • (mfderiv J I₁ f₁ q).comp ((S₀ q).comp
      ((projRadical f₀ hc₀ q).comp ((backMap hc₁ S₁ q).comp (pairMap σ₀ hc₁ S₁ q))))).comp
      (projMapRadical f₀ hc₀ q) +
    (projNormalComplement f₁ hc₁ q).comp ((L q).comp (projNormalComplement f₀ hc₀ q))

/-- The extension is given by `extendFormula`, for any left inverses `S₀`, `S₁` of the
derivatives. -/
private theorem smoothExtendAlong_eq_extendFormula
    {S₀ : ∀ q, TangentSpace I₀ (f₀ q) →L[ℝ] TangentSpace J q}
    {S₁ : ∀ q, TangentSpace I₁ (f₁ q) →L[ℝ] TangentSpace J q}
    (hS₀ : ∀ q, Function.LeftInverse (S₀ q) (mfderiv J I₀ f₀ q))
    (hS₁ : ∀ q, Function.LeftInverse (S₁ q) (mfderiv J I₁ f₁ q)) (q : Q) :
    (smoothExtendAlong hc₀ hc₁ hσ L hL hLω hdim q : TangentSpace I₀ (f₀ q) →L[ℝ]
      TangentSpace I₁ (f₁ q)) = extendFormula hc₀ hc₁ L S₀ S₁ q := by
  set b := mfderivRangeEquiv f₀ f₁ q
  have hb (w : (mfderiv J I₀ f₀ q).range) :
      (b w : TangentSpace I₁ (f₁ q)) = mfderiv J I₁ f₁ q (S₀ q w) :=
    mfderivRangeEquiv_apply_of_leftInverse q (hS₀ q) w
  have hb' (w : (mfderiv J I₁ f₁ q).range) :
      (b.symm w : TangentSpace I₀ (f₀ q)) = mfderiv J I₀ f₀ q (S₁ q w) := by
    simp only [b, mfderivRangeEquiv_symm]
    exact mfderivRangeEquiv_apply_of_leftInverse q (hS₁ q) w
  -- The adjoint step of the formula is `pairMap`.
  have hpair (x : TangentSpace I₀ (f₀ q)) :
      ((hc₁.isNondegenerate.symplecticFormAt (f₁ q)).toBilinForm.toDual
        (hc₁.isNondegenerate.symplecticFormAt (f₁ q)).nondegenerate).symm
        (((mfderiv J I₀ f₀ q).range.subtype ∘ₗ b.symm.toLinearMap ∘ₗ
          (mfderiv J I₁ f₁ q).range.projectionOnto _
            (hc₁.compatibleAt (f₁ q)).isCompl_map_sup_normalComplement).dualMap
          ((hc₀.isNondegenerate.symplecticFormAt (f₀ q)).toBilinForm x)) =
        pairMap σ₀ hc₁ S₁ q x := by
    rw [← sub_eq_zero]
    refine (hc₁.isNondegenerate.symplecticFormAt (f₁ q)).separatingLeft _ fun y ↦ ?_
    have h := ContinuousLinearMap.apply_bilinAdjoint_apply (β₀ := σ₀.flat (f₀ q))
      (hc₁.isNondegenerate.isInvertible_flat (f₁ q)) (backMap hc₁ S₁ q) x y
    simp only [SmoothTwoForm.flat_apply, backMap, projRange, ContinuousLinearMap.comp_apply,
      LinearMap.coe_toContinuousLinearMap'] at h
    simp only [map_sub, LinearMap.sub_apply, LinearMap.BilinForm.apply_toDual_symm_apply,
      LinearMap.dualMap_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      Submodule.subtype_apply, hb', Submodule.coe_projectionOnto_apply,
      SmoothTwoForm.IsNondegenerate.toBilinForm_symplecticFormAt, SmoothForm.bilinFormAt_apply]
    rw [pairMap, sub_eq_zero]
    exact h.symm
  refine ContinuousLinearMap.ext fun v ↦ ?_
  have h := LinearMap.congr_fun ((hc₀.compatibleAt (f₀ q)).extendAlong_def
    (hc₁.compatibleAt (f₁ q)) b
    (symplecticFormAt_mfderivRangeEquiv hc₀.isNondegenerate hc₁.isNondegenerate hσ q)
    (L q : TangentSpace I₀ (f₀ q) →ₗ[ℝ] TangentSpace I₁ (f₁ q)) (hL q) (hLω q) hdim) v
  -- The sums in this instance of `extendAlong_def` match `LinearMap.add_apply` only up to
  -- unfolding instances, which `erw` allows and `rw` and `simp` do not.
  erw [LinearMap.add_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply,
    LinearMap.smul_apply] at h
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.subtype_apply,
    Submodule.coe_inclusion, hb, hb', Submodule.coe_projectionOnto_apply] at h
  rw [ContinuousLinearEquiv.coe_coe, smoothExtendAlong_def,
    LinearEquiv.coe_toContinuousLinearEquiv',
    h, hpair]
  simp only [extendFormula, backMap, projRange, projMapRadical, projNormalComplement, projRadical,
    add_apply, sub_apply, ContinuousLinearMap.comp_apply,
    smul_apply, LinearMap.coe_toContinuousLinearMap',
    ContinuousLinearMap.coe_coe]

variable [FiniteDimensional ℝ E']

include hσ in
/-- `extendFormula` is a smooth section of the bundle of linear maps between the pull-backs, if
`L`, `S₀` and `S₁` are smooth and the kernels of `f₀^* σ₀` have constant dimension. -/
private theorem contMDiff_extendFormula {k : ℕ}
    (hk : ∀ q, finrank ℝ (LinearMap.ker
      ((SmoothForm.mpullback f₀ f₀.contMDiff σ₀).bilinFormAt q)) = k)
    (hLs : ContMDiff J (J.prod 𝓘(ℝ, E₀ →L[ℝ] E₁)) ∞ (fun q ↦ TotalSpace.mk' (E₀ →L[ℝ] E₁)
      (E := fun q ↦ ((f₀ : Q → M₀) *ᵖ (TangentSpace I₀)) q →L[ℝ]
        ((f₁ : Q → M₁) *ᵖ (TangentSpace I₁)) q) q (L q)))
    {S₀ : ∀ q, TangentSpace I₀ (f₀ q) →L[ℝ] TangentSpace J q}
    {S₁ : ∀ q, TangentSpace I₁ (f₁ q) →L[ℝ] TangentSpace J q}
    (hS₀ : ContMDiff J (J.prod 𝓘(ℝ, E₀ →L[ℝ] E')) ∞ (fun q ↦ TotalSpace.mk' (E₀ →L[ℝ] E')
      (E := fun q ↦ ((f₀ : Q → M₀) *ᵖ (TangentSpace I₀)) q →L[ℝ] TangentSpace J q) q (S₀ q)))
    (hS₁ : ContMDiff J (J.prod 𝓘(ℝ, E₁ →L[ℝ] E')) ∞ (fun q ↦ TotalSpace.mk' (E₁ →L[ℝ] E')
      (E := fun q ↦ ((f₁ : Q → M₁) *ᵖ (TangentSpace I₁)) q →L[ℝ] TangentSpace J q) q (S₁ q))) :
    ContMDiff J (J.prod 𝓘(ℝ, E₀ →L[ℝ] E₁)) ∞ (fun q ↦ TotalSpace.mk' (E₀ →L[ℝ] E₁)
      (E := fun q ↦ ((f₀ : Q → M₀) *ᵖ (TangentSpace I₀)) q →L[ℝ]
        ((f₁ : Q → M₁) *ᵖ (TangentSpace I₁)) q) q (extendFormula hc₀ hc₁ L S₀ S₁ q)) := by
  have : ContMDiffVectorBundle ∞ E₀ ((f₀ : Q → M₀) *ᵖ (TangentSpace I₀)) J :=
    Bundle.Pullback.contMDiffVectorBundle (E := TangentSpace I₀) f₀.contMDiff
  have : ContMDiffVectorBundle ∞ E₁ ((f₁ : Q → M₁) *ᵖ (TangentSpace I₁)) J :=
    Bundle.Pullback.contMDiffVectorBundle (E := TangentSpace I₁) f₁.contMDiff
  have hk₁ (q : Q) : finrank ℝ (LinearMap.ker
      ((SmoothForm.mpullback f₁ f₁.contMDiff σ₁).bilinFormAt q)) = k := hσ ▸ hk q
  -- The derivatives and the projections, as smooth sections of bundles of linear maps.
  have hT₀ : ContMDiff J (J.prod 𝓘(ℝ, E' →L[ℝ] E₀)) ∞ (fun q ↦ TotalSpace.mk' (E' →L[ℝ] E₀)
      (E := fun q ↦ TangentSpace J q →L[ℝ] ((f₀ : Q → M₀) *ᵖ (TangentSpace I₀)) q) q
      (mfderiv J I₀ f₀ q)) :=
    (contMDiff_hom_bundle_iff (E₂ := (f₀ : Q → M₀) *ᵖ (TangentSpace I₀)) _).2
      (Pullback.contMDiff_totalSpace_mfderiv f₀ f₀.contMDiff)
  have hT₁ : ContMDiff J (J.prod 𝓘(ℝ, E' →L[ℝ] E₁)) ∞ (fun q ↦ TotalSpace.mk' (E' →L[ℝ] E₁)
      (E := fun q ↦ TangentSpace J q →L[ℝ] ((f₁ : Q → M₁) *ᵖ (TangentSpace I₁)) q) q
      (mfderiv J I₁ f₁ q)) :=
    (contMDiff_hom_bundle_iff (E₂ := (f₁ : Q → M₁) *ᵖ (TangentSpace I₁)) _).2
      (Pullback.contMDiff_totalSpace_mfderiv f₁ f₁.contMDiff)
  have hW₀ := contMDiff_projRange f₀ hc₀ hk
  have hW₁ := contMDiff_projRange f₁ hc₁ hk₁
  have hJK₀ := contMDiff_projMapRadical f₀ hc₀ hk
  have hE₀ := contMDiff_projNormalComplement f₀ hc₀ hk
  have hE₁ := contMDiff_projNormalComplement f₁ hc₁ hk₁
  have hK₀ := contMDiff_projRadical f₀ hc₀ hk
  -- `backMap`, and its adjoint `pairMap` for `σ₀` and `σ₁`.
  have hB := hT₀.clm_bundle_comp (IB := J) (V₁ := (f₁ : Q → M₁) *ᵖ (TangentSpace I₁))
    (V₂ := TangentSpace J) (V₃ := (f₀ : Q → M₀) *ᵖ (TangentSpace I₀))
    (hS₁.clm_bundle_comp (IB := J) (V₁ := (f₁ : Q → M₁) *ᵖ (TangentSpace I₁))
      (V₂ := (f₁ : Q → M₁) *ᵖ (TangentSpace I₁)) (V₃ := TangentSpace J) hW₁)
  have hP := ContMDiff.clm_bundle_bilinAdjoint (E₀ := (f₀ : Q → M₀) *ᵖ (TangentSpace I₀))
    (E₁ := (f₁ : Q → M₁) *ᵖ (TangentSpace I₁))
    (SmoothTwoForm.contMDiff_flat_pullback σ₀ f₀ f₀.contMDiff)
    (SmoothTwoForm.contMDiff_flat_pullback σ₁ f₁ f₁.contMDiff) hB
    (fun q ↦ hc₁.isNondegenerate.isInvertible_flat (f₁ q))
  -- The three terms of the formula.
  have hW := hT₁.clm_bundle_comp (IB := J) (V₁ := (f₀ : Q → M₀) *ᵖ (TangentSpace I₀))
    (V₂ := TangentSpace J) (V₃ := (f₁ : Q → M₁) *ᵖ (TangentSpace I₁))
    (hS₀.clm_bundle_comp (IB := J) (V₁ := (f₀ : Q → M₀) *ᵖ (TangentSpace I₀))
      (V₂ := (f₀ : Q → M₀) *ᵖ (TangentSpace I₀)) (V₃ := TangentSpace J) hW₀)
  have hBP := hB.clm_bundle_comp (IB := J) (V₁ := (f₀ : Q → M₀) *ᵖ (TangentSpace I₀))
    (V₂ := (f₁ : Q → M₁) *ᵖ (TangentSpace I₁)) (V₃ := (f₀ : Q → M₀) *ᵖ (TangentSpace I₀)) hP
  have hKBP := hK₀.clm_bundle_comp (IB := J) (V₁ := (f₀ : Q → M₀) *ᵖ (TangentSpace I₀))
    (V₂ := (f₀ : Q → M₀) *ᵖ (TangentSpace I₀)) (V₃ := (f₀ : Q → M₀) *ᵖ (TangentSpace I₀)) hBP
  have hC := hT₁.clm_bundle_comp (IB := J) (V₁ := (f₀ : Q → M₀) *ᵖ (TangentSpace I₀))
    (V₂ := TangentSpace J) (V₃ := (f₁ : Q → M₁) *ᵖ (TangentSpace I₁))
    (hS₀.clm_bundle_comp (IB := J) (V₁ := (f₀ : Q → M₀) *ᵖ (TangentSpace I₀))
      (V₂ := (f₀ : Q → M₀) *ᵖ (TangentSpace I₀)) (V₃ := TangentSpace J) hKBP)
  have hJK := (hP.sub_section (hC.const_smul_section (a := (2⁻¹ : ℝ)))).clm_bundle_comp (IB := J)
    (V₁ := (f₀ : Q → M₀) *ᵖ (TangentSpace I₀)) (V₂ := (f₀ : Q → M₀) *ᵖ (TangentSpace I₀))
    (V₃ := (f₁ : Q → M₁) *ᵖ (TangentSpace I₁)) hJK₀
  have hE := hE₁.clm_bundle_comp (IB := J) (V₁ := (f₀ : Q → M₀) *ᵖ (TangentSpace I₀))
    (V₂ := (f₁ : Q → M₁) *ᵖ (TangentSpace I₁)) (V₃ := (f₁ : Q → M₁) *ᵖ (TangentSpace I₁))
    (hLs.clm_bundle_comp (IB := J) (V₁ := (f₀ : Q → M₀) *ᵖ (TangentSpace I₀))
      (V₂ := (f₀ : Q → M₀) *ᵖ (TangentSpace I₀)) (V₃ := (f₁ : Q → M₁) *ᵖ (TangentSpace I₁)) hE₀)
  simp only [extendFormula, pairMap, backMap]
  exact (hW.add_section hJK).add_section hE

/-- **The extension is smooth.** If the kernels of `f₀^* σ₀` all have the same dimension and `L`
is a smooth section of the bundle of linear maps between the pull-backs `f₀ *ᵖ TM₀` and
`f₁ *ᵖ TM₁`, then so is the extension. -/
theorem contMDiff_smoothExtendAlong {k : ℕ}
    (hk : ∀ q, finrank ℝ (LinearMap.ker
      ((SmoothForm.mpullback f₀ f₀.contMDiff σ₀).bilinFormAt q)) = k)
    (hLs : ContMDiff J (J.prod 𝓘(ℝ, E₀ →L[ℝ] E₁)) ∞ (fun q ↦ TotalSpace.mk' (E₀ →L[ℝ] E₁)
      (E := fun q ↦ ((f₀ : Q → M₀) *ᵖ (TangentSpace I₀)) q →L[ℝ]
        ((f₁ : Q → M₁) *ᵖ (TangentSpace I₁)) q) q (L q))) :
    ContMDiff J (J.prod 𝓘(ℝ, E₀ →L[ℝ] E₁)) ∞ (fun q ↦ TotalSpace.mk' (E₀ →L[ℝ] E₁)
      (E := fun q ↦ ((f₀ : Q → M₀) *ᵖ (TangentSpace I₀)) q →L[ℝ]
        ((f₁ : Q → M₁) *ᵖ (TangentSpace I₁)) q) q
      (smoothExtendAlong hc₀ hc₁ hσ L hL hLω hdim q :
        TangentSpace I₀ (f₀ q) →L[ℝ] TangentSpace I₁ (f₁ q))) := by
  obtain ⟨S₀, hS₀, hS₀f⟩ := f₀.exists_contMDiff_leftInverse_mfderiv hc₀.tames
  obtain ⟨S₁, hS₁, hS₁f⟩ := f₁.exists_contMDiff_leftInverse_mfderiv hc₁.tames
  simp only [smoothExtendAlong_eq_extendFormula hc₀ hc₁ hσ L hL hLω hdim hS₀f hS₁f]
  exact contMDiff_extendFormula hc₀ hc₁ hσ L hk hLs hS₀ hS₁

end Extension

end TauCeti.SmoothEmbedding

end
