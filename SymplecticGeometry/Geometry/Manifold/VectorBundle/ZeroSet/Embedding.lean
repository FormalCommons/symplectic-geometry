/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Section.SmoothZero

import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Topology.VectorBundle.FiniteDimensional
import TauCeti.Geometry.Manifold.ModelTransport.Immersion
import TauCeti.Geometry.Manifold.PullbackGroupoid
import TauCeti.Geometry.Manifold.Immersion.Basic
import SymplecticGeometry.Topology.VectorBundle.ZeroSet

/-!
# Zero sets of transverse sections as embedded submanifolds

Let `E' → X` be a `C^m` vector bundle, `m ≠ 0`, with finite-dimensional model fibre `F'`, over a
manifold `X` modelled on a boundaryless model `J` over a finite-dimensional space `V`, and let
`s` be a `C^m` section of `E'` transverse to the zero section: at each zero `x` of `s`, the
intrinsic linearization `TauCeti.sectionLinearization J id s x : T_x X → E'_x` is onto. Then the
zero set `{x | s x = 0}` is a closed embedded submanifold of `X` of dimension
`dim V - dim F'`.

The atlas is Tau Ceti's section-zero atlas
(`TauCeti.exists_isManifold_sectionZero_of_contMDiff_of_closedComplemented`). That construction
is stated for a source modelled directly on a normed space, so the section is first read on the
self-modelled copy `TauCeti.BoundarylessModel J X`, and its atlas is then carried to the zero set
in `X` along the identity of points. The model of the zero set is any finite-dimensional space
`E` with `dim E + dim F' = dim V`; the identifications of the kernels of the linearization with
`E` are chosen once from transversality.

This transport adapts Tau Ceti's construction for regular levels, in
`TauCeti/Geometry/Manifold/RegularValue/Level.lean`, from level sets of maps to zero sets of
sections: the private `TransverseZeroSet.sec`, `TransverseZeroSet.zeroHomeomorph` and
`TransverseZeroSet.coe_zeroHomeomorph_symm` follow `TauCeti.RegularLevel.sec`,
`TauCeti.RegularLevel.zeroHomeomorph` and `TauCeti.RegularLevel.coe_zeroHomeomorph_symm`;
`transverseZeroSetChartedSpace` is the pullback form of `TauCeti.regularLevelChartedSpace`
(`TauCeti.regularLevelChartedSpace_eq_pullbackChartedSpace`); `isManifold_transverseZeroSet`
follows `TauCeti.isManifold_regularLevel`; and `isImmersionOfComplement_coe_transverseZeroSet`
follows `TauCeti.isImmersionOfComplement_coe_regularLevel`.

## Main declarations

* `SymplecticGeometry.finrank_le_of_surjective_sectionLinearization`: if the linearization of `s` at
  a point is onto, the rank of `E'` is at most the dimension of `V`.
* `SymplecticGeometry.transverseZeroSetChartedSpace`: the atlas of the zero set of a transverse
  section, modelled on `E`.
* `SymplecticGeometry.isManifold_transverseZeroSet`: for it, the zero set is a `C^m` manifold.
* `SymplecticGeometry.isImmersionOfComplement_coe_transverseZeroSet`: the inclusion is a `C^m`
  immersion with complement `F'`.
* `SymplecticGeometry.range_mfderiv_coe_transverseZeroSet`: the tangent space of the zero set at
  `z` is the kernel of the linearization of `s` at `z`.
* `TauCeti.SmoothEmbedding.ofTransverseSection`: the inclusion of the zero set as a bundled
  smooth embedding, and `TauCeti.SmoothEmbedding.isClosed_range_ofTransverseSection`: its range
  is closed. Off that range the section does not vanish
  (`TauCeti.SmoothEmbedding.snd_ne_zero_of_notMem_range_ofTransverseSection`).

## References

* [R. Bott, L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982], §6
* [D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*][McDuffSalamon2012],
  Appendix A.3
-/

public section

open Bundle Function Module Set
open scoped ContDiff Manifold Topology

open TauCeti

variable {𝕜 V G X F' E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]
  [TopologicalSpace G] {J : ModelWithCorners 𝕜 V G} [J.Boundaryless]
  [TopologicalSpace X] [ChartedSpace G X]
  [NormedAddCommGroup F'] [NormedSpace 𝕜 F'] [FiniteDimensional 𝕜 F']
  {E' : X → Type*} [TopologicalSpace (TotalSpace F' E')] [∀ x, AddCommGroup (E' x)]
  [∀ x, Module 𝕜 (E' x)] [∀ x, TopologicalSpace (E' x)] [FiberBundle F' E']
  [VectorBundle 𝕜 F' E']
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {m : ℕ∞ω} [IsManifold J m X] [ContMDiffVectorBundle m F' E' J] {s : ∀ x, E' x}

-- Finite-dimensional completeness is not a global instance over a variable scalar field.
local instance instCompleteSpaceModel : CompleteSpace V := FiniteDimensional.completeSpace 𝕜 V
local instance instCompleteSpaceFiber : CompleteSpace F' := FiniteDimensional.completeSpace 𝕜 F'

variable (hm : m ≠ 0) (hsm : ContMDiff J (J.prod 𝓘(𝕜, F')) m fun x ↦ TotalSpace.mk' F' x (s x))
  (hs : ∀ x, s x = 0 → Surjective (sectionLinearization (F := F') J _root_.id s x))
  (hE : finrank 𝕜 E + finrank 𝕜 F' = finrank 𝕜 V)

namespace SymplecticGeometry

omit [FiniteDimensional 𝕜 F'] [J.Boundaryless] in
/-- **Transversality bounds the rank.** If the linearization of a section `s` at a point `x` maps
`T_x X` onto the fibre `E'_x`, then the rank of `E'` is at most the dimension of the model `V`
of `X`. -/
theorem finrank_le_of_surjective_sectionLinearization {x : X}
    (h : Surjective (sectionLinearization (F := F') J _root_.id s x)) :
    finrank 𝕜 F' ≤ finrank 𝕜 V := by
  rw [← VectorBundle.finrank_eq 𝕜 F' E' x]
  exact LinearMap.finrank_le_finrank_of_surjective
    (f := (sectionLinearization (F := F') J _root_.id s x).toLinearMap) h

namespace TransverseZeroSet

variable (J s) in
/-- The section `s`, read on the self-modelled copy of `X`. -/
private noncomputable def sec (y : BoundarylessModel J X) :
    E' ((BoundarylessModel.homeomorph J X).symm y) :=
  s ((BoundarylessModel.homeomorph J X).symm y)

variable (J s) in
/-- The zero set of `s` on the self-modelled copy is the zero set of `s` in `X`. -/
private noncomputable def zeroHomeomorph :
    ↥{y : BoundarylessModel J X | sec J s y = 0} ≃ₜ ↥{x : X | s x = 0} :=
  (BoundarylessModel.homeomorph J X).symm.subtype fun _ ↦ Iff.rfl

omit [FiniteDimensional 𝕜 V] [J.Boundaryless] [ChartedSpace G X] [∀ x, Module 𝕜 (E' x)]
  [∀ x, TopologicalSpace (E' x)] in
private theorem coe_zeroHomeomorph_symm (x : ↥{x : X | s x = 0}) :
    ((zeroHomeomorph J s).symm x).val = BoundarylessModel.homeomorph J X x.val :=
  (rfl)

/-- Tau Ceti's section-zero atlas on the zero set in the self-modelled copy. -/
private theorem exists_chartedSpace (hm : m ≠ 0)
    (hsm : ContMDiff J (J.prod 𝓘(𝕜, F')) m fun x ↦ TotalSpace.mk' F' x (s x))
    (hs : ∀ x, s x = 0 → Surjective (sectionLinearization (F := F') J _root_.id s x))
    (hE : finrank 𝕜 E + finrank 𝕜 F' = finrank 𝕜 V) :
    ∃ cs : ChartedSpace E ↥{y : BoundarylessModel J X | sec J s y = 0},
      letI := cs
      IsManifold 𝓘(𝕜, E) m ↥{y : BoundarylessModel J X | sec J s y = 0} ∧
        Manifold.IsImmersionOfComplement F' 𝓘(𝕜, E) 𝓘(𝕜, V) m
          (Subtype.val : ↥{y : BoundarylessModel J X | sec J s y = 0} → _) := by
  set b := (BoundarylessModel.homeomorph J X).symm
  have hb : ⇑b = ⇑(BoundarylessModel.diffeomorph J (M := X) m).symm :=
    (BoundarylessModel.coe_diffeomorph_symm J m).symm
  -- The linearization on the copy is that of `s` composed with the derivative of the identity.
  have hlin (y : BoundarylessModel J X) :
      sectionLinearization (F := F') 𝓘(𝕜, V) b (sec J s) y =
        (sectionLinearization (F := F') J _root_.id s (b y)).comp (mfderiv 𝓘(𝕜, V) J b y) := by
    have hd : MDifferentiableAt 𝓘(𝕜, V) J b y := by
      rw [hb]
      exact ((BoundarylessModel.diffeomorph J m).symm.mdifferentiable hm) y
    have he := (trivializationAt F' E' (b y)).contMDiffAt_iff (n := m) (IM := J) (IB := J)
      (f := fun x ↦ TotalSpace.mk' F' x (s x)) (x₀ := b y)
      ((trivializationAt F' E' (b y)).mem_source.2 (mem_baseSet_trivializationAt F' E' (b y)))
    exact sectionLinearization_comp (b := _root_.id) (s := s) hd
      ((he.1 (hsm _)).2.mdifferentiableAt hm)
  have hsurj (y : BoundarylessModel J X) (hy : sec J s y = 0) :
      Surjective (sectionLinearization (F := F') 𝓘(𝕜, V) b (sec J s) y) := by
    rw [hlin]
    refine (hs _ hy).comp ?_
    rw [hb]
    exact ((BoundarylessModel.diffeomorph J m).symm.isInvertible_mfderiv hm).surjective
  refine (exists_isManifold_sectionZero_of_contMDiff_of_closedComplemented hm
    (fun y _ ↦ (BoundarylessModel.contMDiffAt_source_iff J (J.prod 𝓘(𝕜, F'))
      (fun x ↦ TotalSpace.mk' F' x (s x)) y).2 (hsm _)) hsurj (fun y _ ↦ ?_)
      (fun y hy ↦ ?_)).imp fun _ h ↦ ⟨h.1, h.2.1⟩
  · -- The tangent space of the copy is `V`, whose instances the kernel needs.
    let : PolynormableSpace 𝕜 (TangentSpace 𝓘(𝕜, V) y) := inferInstanceAs (PolynormableSpace 𝕜 V)
    exact Submodule.ClosedComplemented.of_finiteDimensional _
  · -- The kernel of a surjection onto a fibre of dimension `dim F'` has dimension `dim E`.
    have h : finrank 𝕜 (sectionLinearization (F := F') 𝓘(𝕜, V) b (sec J s) y).ker +
        finrank 𝕜 F' = finrank 𝕜 V := by
      have := (ContinuousLinearMap.index_of_surjective _ (hsurj y hy)).symm.trans
        ((ContinuousLinearMap.index_def _).trans index_sectionLinearization_of_finiteDimensional)
      omega
    exact ⟨ContinuousLinearEquiv.ofFinrankEq (Nat.add_right_cancel (h.trans hE.symm))⟩

end TransverseZeroSet

open TransverseZeroSet

/-- The atlas of the zero set of a `C^m` section `s` transverse to the zero section, modelled on
a space `E` of dimension `dim V - dim F'`: Tau Ceti's section-zero atlas of `s`, read on the
self-modelled copy of `X` and carried to the zero set in `X`. -/
@[instance_reducible]
noncomputable def transverseZeroSetChartedSpace : ChartedSpace E ↥{x : X | s x = 0} :=
  letI := (exists_chartedSpace hm hsm hs hE).choose
  (zeroHomeomorph J s).symm.pullbackChartedSpace

/-- The zero set of a transverse section is a `C^m` manifold for its atlas
`SymplecticGeometry.transverseZeroSetChartedSpace`. -/
theorem isManifold_transverseZeroSet :
    letI := transverseZeroSetChartedSpace hm hsm hs hE
    IsManifold 𝓘(𝕜, E) m ↥{x : X | s x = 0} :=
  letI := (exists_chartedSpace hm hsm hs hE).choose
  haveI := (exists_chartedSpace hm hsm hs hE).choose_spec.1
  (zeroHomeomorph J s).symm.pullback_isManifold _ m

/-- The inclusion of the zero set of a transverse section is a `C^m` immersion with complement
`F'`, for the atlas `SymplecticGeometry.transverseZeroSetChartedSpace`. -/
theorem isImmersionOfComplement_coe_transverseZeroSet :
    letI := transverseZeroSetChartedSpace hm hsm hs hE
    Manifold.IsImmersionOfComplement F' 𝓘(𝕜, E) J m (Subtype.val : ↥{x : X | s x = 0} → X) := by
  let := (exists_chartedSpace hm hsm hs hE).choose
  have := (exists_chartedSpace hm hsm hs hE).choose_spec.1
  have hZ := (exists_chartedSpace hm hsm hs hE).choose_spec.2
  let := (zeroHomeomorph J s).symm.pullbackChartedSpace (H := E)
  have := (zeroHomeomorph J s).symm.pullback_isManifold 𝓘(𝕜, E) m
  refine BoundarylessModel.isImmersionOfComplement_target_iff.1 ?_
  -- Read in the self-modelled copy, the inclusion is the inclusion of the zero set there,
  -- precomposed with the pulled-back diffeomorphism.
  have hcomp : BoundarylessModel.homeomorph J X ∘ (Subtype.val : ↥{x : X | s x = 0} → X) =
      Subtype.val ∘ (zeroHomeomorph J s).symm.pullbackDiffeomorph 𝓘(𝕜, E) m := by
    funext x
    rw [comp_apply, comp_apply, Homeomorph.coe_pullbackDiffeomorph, coe_zeroHomeomorph_symm]
  rw [hcomp]
  exact isImmersionOfComplement_comp_diffeomorph _ hZ

/-- **The tangent space of the zero set of a transverse section.** At a zero `z` of `s`, the
range of the differential of the inclusion of the zero set, for the atlas
`SymplecticGeometry.transverseZeroSetChartedSpace`, is the kernel of the linearization of `s`
at `z`. -/
theorem range_mfderiv_coe_transverseZeroSet (z : ↥{x : X | s x = 0}) :
    letI := transverseZeroSetChartedSpace hm hsm hs hE
    (mfderiv 𝓘(𝕜, E) J (Subtype.val : ↥{x : X | s x = 0} → X) z).range =
      (sectionLinearization (F := F') J _root_.id s z).ker := by
  let := transverseZeroSetChartedSpace hm hsm hs hE
  have := isManifold_transverseZeroSet hm hsm hs hE
  have himm := isImmersionOfComplement_coe_transverseZeroSet hm hsm hs hE z
  have hd : MDifferentiableAt 𝓘(𝕜, E) J (Subtype.val : ↥{x : X | s x = 0} → X) z :=
    himm.contMDiffAt.mdifferentiableAt hm
  have he := (trivializationAt F' E' z).contMDiffAt_iff (n := m) (IM := J) (IB := J)
    (f := fun x ↦ TotalSpace.mk' F' x (s x)) (x₀ := z)
    ((trivializationAt F' E' z).mem_source.2 (mem_baseSet_trivializationAt F' E' z.val))
  -- `s` vanishes on the zero set, so `L ∘ dι`, the linearization of its restriction, is zero.
  have hcomp := sectionLinearization_comp (b := _root_.id) (s := s) hd
    ((he.1 (hsm _)).2.mdifferentiableAt hm)
  have h0 : (fun w : ↥{x : X | s x = 0} ↦ s (w : X)) = fun w ↦ 0 := funext fun w ↦ w.property
  rw [h0, sectionLinearization_zero (b := _root_.id ∘ Subtype.val)
    continuous_subtypeVal.continuousAt] at hcomp
  have hle : (mfderiv 𝓘(𝕜, E) J (Subtype.val : ↥{x : X | s x = 0} → X) z).range ≤
      (sectionLinearization (F := F') J _root_.id s z).ker := by
    rintro _ ⟨v, rfl⟩
    exact (DFunLike.congr_fun hcomp v).symm
  refine Submodule.eq_of_le_of_finrank_eq hle ?_
  -- Both have dimension `dim E`: the differential of an immersion is injective.
  have h := (ContinuousLinearMap.index_of_surjective _ (hs z z.property)).symm.trans
    ((ContinuousLinearMap.index_def _).trans index_sectionLinearization_of_finiteDimensional)
  rw [LinearMap.finrank_range_of_inj (himm.mfderiv_injective hm)]
  have hdim : finrank 𝕜 (TangentSpace 𝓘(𝕜, E) z) = finrank 𝕜 E := rfl
  omega

end SymplecticGeometry

namespace TauCeti.SmoothEmbedding

open SymplecticGeometry

/-- **The zero set of a transverse section is an embedded submanifold.** The inclusion of the
zero set of a `C^m` section `s` transverse to the zero section, with the atlas
`SymplecticGeometry.transverseZeroSetChartedSpace` modelled on `E`, as a `C^m` smooth embedding
into `X`. -/
noncomputable def ofTransverseSection :
    letI := transverseZeroSetChartedSpace hm hsm hs hE
    SmoothEmbedding 𝓘(𝕜, E) J m ↥{x : X | s x = 0} X :=
  letI := transverseZeroSetChartedSpace hm hsm hs hE
  ofIsSmoothEmbedding Subtype.val
    ⟨(isImmersionOfComplement_coe_transverseZeroSet hm hsm hs hE).isImmersion,
      Topology.IsEmbedding.subtypeVal⟩

/-- The inclusion of the zero set of a transverse section is `Subtype.val`. -/
@[simp]
theorem coe_ofTransverseSection :
    letI := transverseZeroSetChartedSpace hm hsm hs hE
    ⇑(ofTransverseSection hm hsm hs hE) = Subtype.val := by
  let := transverseZeroSetChartedSpace hm hsm hs hE
  exact coe_ofIsSmoothEmbedding _ _

/-- The range of the inclusion of the zero set of a transverse section is the zero set. -/
theorem range_ofTransverseSection :
    letI := transverseZeroSetChartedSpace hm hsm hs hE
    range (ofTransverseSection hm hsm hs hE) = {x | s x = 0} := by
  rw [coe_ofTransverseSection, Subtype.range_coe]

/-- Off the zero set of a transverse section, the section does not vanish. -/
theorem snd_ne_zero_of_notMem_range_ofTransverseSection (x : X)
    (hx : letI := transverseZeroSetChartedSpace hm hsm hs hE
      x ∉ range (ofTransverseSection hm hsm hs hE)) :
    (TotalSpace.mk' F' x (s x)).snd ≠ 0 := fun h ↦ hx <| by
  rw [range_ofTransverseSection]
  exact h

/-- A point of the zero set of a transverse section is a zero of the section. -/
theorem ofTransverseSection_apply_eq_zero (z : ↥{x : X | s x = 0}) :
    letI := transverseZeroSetChartedSpace hm hsm hs hE
    s (ofTransverseSection hm hsm hs hE z) = 0 := by
  let := transverseZeroSetChartedSpace hm hsm hs hE
  rw [coe_ofTransverseSection]
  exact z.property

/-- The zero set of a transverse section is a closed embedded submanifold. -/
theorem isClosed_range_ofTransverseSection :
    letI := transverseZeroSetChartedSpace hm hsm hs hE
    IsClosed (range (ofTransverseSection hm hsm hs hE)) := by
  rw [range_ofTransverseSection]
  exact VectorBundle.isClosed_setOfPred_eq_zero 𝕜 (b := _root_.id) hsm.continuous

end TauCeti.SmoothEmbedding

end
