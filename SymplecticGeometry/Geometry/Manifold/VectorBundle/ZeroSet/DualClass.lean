/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.NormalSpace.DualClass.Slice
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.ZeroSet.NormalSpace
public import SymplecticGeometry.Topology.VectorBundle.Orientation.ThomClass
public import TauCeti.Topology.VectorBundle.Orientation.Complex.EulerClass

import SymplecticGeometry.AlgebraicTopology.Cohomology.Local.Restrict
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# The dual class of the zero set of a transverse section

Let `s` be a smooth section of a real vector bundle `E' → X` of rank `r = finrank ℝ F'`,
transverse to the zero section, and let `f = TauCeti.SmoothEmbedding.ofTransverseSection` be the
inclusion of its zero set `Z`, a closed embedded submanifold whose normal bundle is identified
with the restriction of `E'` by the linearization of `s`
(`SymplecticGeometry.normalSpaceEquivOfTransverseSection`). Since `s` vanishes only on `Z`, it is
a map of pairs `(X, X ∖ Z) ⟶ (E', E'₀)` (`TauCeti.thomPairMapOfNeZero`). This file shows that it
pulls each class `u` of degree `r` of the Thom pair of `E'` back to the relative class
`relDualClassOf` of `Z` for the pull-back of `u` to the normal bundle along that identification,
and in particular pulls the canonical Thom class of an orientation `o'` of `E'` back to the
relative dual class of `Z` with the normal orientation
`SymplecticGeometry.normalOrientationOfSection o'`. Since `s` is homotopic to the zero section
through `t • s`, the image of this class in absolute cohomology is the Euler class of `E'`
(`TauCeti.eulerClass_eq_singularCohomologyMap_thomPairMapOfNeZero`): the dual class of the zero
set is the Euler class, in every rank, and for a complex bundle with its canonical orientation it
is `TauCeti.complexEulerClass`.

The proof is the slice criterion `TauCeti.SmoothEmbedding.eq_relDualClassOf_iff_forall_slice`.
At a point `x` of `Z`, read the normal slice of a normalized tube `Φ` through the preferred
trivialization of the normal bundle, `w ↦ Φ(x, m w)`. Since `Φ` is normalized
(`TauCeti.SmoothEmbedding.IsNormalizedTube.exists_hasMFDerivAt_apply_mk`), the chain rule, with
`TauCeti.continuousLinearMapAt_comp_sectionLinearization` and
`SymplecticGeometry.normalSpaceEquivOfTransverseSection_normalClass`, gives the derivative at `0`
of the coordinate of `s` along the slice, in the preferred trivialization of `E'` at `x`: the
isomorphism `m`, followed by the normal-space equivalence and the trivialization. The local-degree
lemma for maps into a Thom pair,
`TauCeti.singularCohomologyMap_ofSubsetMap_eq_complZeroPairIso_inv_of_hasFDerivAt`, then shows
that `s` along the slice pulls classes back as the normal-space equivalence followed by the fibre
inclusion of `E'` (`TauCeti.SmoothEmbedding.singularCohomologyMap_normalSlice_thomPairMapOfNeZero`).
For the oriented class,
`TauCeti.VectorBundleOrientation.singularCohomologyMap_thomPairMapOfFiberwise_canonicalThomClass`
identifies the pull-back of the canonical Thom class of `o'` to the normal bundle with that of
`normalOrientationOfSection o'`. This follows the proof of
`TauCeti.SmoothEmbedding.relDualClass_transDiffeomorph`, and through the local-degree lemma the
linearization argument of Tau Ceti's
`TauCeti.VectorBundleOrientation.sectionIndex_eq_sign_det_of_hasFDerivAt`.

## Main results

* `TauCeti.SmoothEmbedding.singularCohomologyMap_normalSlice_thomPairMapOfNeZero`: along a normal
  slice of a normalized tube, `s` pulls classes back as the normal-space equivalence followed by
  the fibre inclusion.
* `TauCeti.SmoothEmbedding.relDualClassOf_ofTransverseSection`: the pull-back along `s` of a
  class of degree `r` is a relative class `relDualClassOf` of the zero set.
* `TauCeti.SmoothEmbedding.relDualClass_ofTransverseSection`: the pull-back along `s` of the
  canonical Thom class of `o'` is the relative dual class of the zero set with the normal
  orientation `normalOrientationOfSection o'`, in every rank.
* `TauCeti.SmoothEmbedding.dualClass_ofTransverseSection`: the dual class of the zero set is the
  Euler class of the canonical Thom class of `o'`, in every rank;
  `TauCeti.SmoothEmbedding.dualClass_ofTransverseSection_eq_eulerClass`, its form in positive
  rank with `VectorBundleOrientation.eulerClass o'`.
* `TauCeti.SmoothEmbedding.dualClass_ofTransverseSection_eq_complexEulerClass`: for a complex
  bundle, such as a complex line bundle, the dual class of the zero set is
  `TauCeti.complexEulerClass`.

## References

* [R. Bott, L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982], §6
  (Proposition 6.24)
-/

public section

noncomputable section

open Bundle CategoryTheory Function Module Set Topology
open scoped Manifold ContDiff

open TauCeti SymplecticGeometry

universe w

namespace TauCeti.SmoothEmbedding

variable {G E : Type*} {V X F' : Type w}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace G] {J : ModelWithCorners ℝ V G} [J.Boundaryless]
  [TopologicalSpace X] [ChartedSpace G X] [IsManifold J ∞ X]
  [NormedAddCommGroup F'] [NormedSpace ℝ F'] [FiniteDimensional ℝ F']
  {E' : X → Type w} [TopologicalSpace (TotalSpace F' E')] [∀ x, AddCommGroup (E' x)]
  [∀ x, Module ℝ (E' x)] [∀ x, TopologicalSpace (E' x)] [FiberBundle F' E']
  [VectorBundle ℝ F' E'] [ContMDiffVectorBundle ∞ F' E' J]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {s : ∀ x, E' x}
  (hm : (∞ : ℕ∞ω) ≠ 0)
  (hsm : ContMDiff J (J.prod 𝓘(ℝ, F')) ∞ fun x ↦ TotalSpace.mk' F' x (s x))
  (hs : ∀ x, s x = 0 → Surjective (sectionLinearization (F := F') J _root_.id s x))
  (hE : finrank ℝ E + finrank ℝ F' = finrank ℝ V)

section LocalDegree

variable {C : Type*} [Category C] [Limits.HasCoproducts.{w} C] [Abelian C] {R : C}
  {k : Type*} [Ring k] [Linear k C] {M : C}

/-- **The section along a normal slice.** At a point `x` of the zero set, the normal slice of a
normalized tube `Φ` followed by the section `s`, as a map of pairs into the Thom pair of `E'`,
pulls every class back as the normal-space equivalence of `s` at `x` followed by the inclusion of
the fibre of `E'` over `x`, in every degree. -/
theorem singularCohomologyMap_normalSlice_thomPairMapOfNeZero
    {W : TopologicalSpace.Opens X}
    {Φ : letI := transverseZeroSetChartedSpace hm hsm hs hE
      haveI := isManifold_transverseZeroSet hm hsm hs hE
      letI := (ofTransverseSection hm hsm hs hE).normalSpaceFiberBundle hm
        (Nat.eq_sub_of_add_eq' hE)
      TotalSpace F' (fun x ↦ (ofTransverseSection hm hsm hs hE).isImmersion.NormalSpace x hm)
        ≃ₘ^∞⟮𝓘(ℝ, E).prod 𝓘(ℝ, F'), J⟯ W}
    (hΦ : letI := transverseZeroSetChartedSpace hm hsm hs hE
      haveI := isManifold_transverseZeroSet hm hsm hs hE
      (ofTransverseSection hm hsm hs hE).IsNormalizedTube hm (Nat.eq_sub_of_add_eq' hE) Φ)
    (x : ↥{x : X | s x = 0}) {n : ℕ} (u : (thomPair F' E').singularCohomology R k M n) :
    letI := transverseZeroSetChartedSpace hm hsm hs hE
    haveI := isManifold_transverseZeroSet hm hsm hs hE
    TopPair.singularCohomologyMap
        ((ofTransverseSection hm hsm hs hE).normalSlice hm (Nat.eq_sub_of_add_eq' hE) Φ
            hΦ.apply_zeroSection x ≫
          thomPairMapOfNeZero ⟨_, hsm.continuous⟩
            (snd_ne_zero_of_notMem_range_ofTransverseSection hm hsm hs hE)) n u =
      TopPair.singularCohomologyMap
        ((normalSpaceEquivOfTransverseSection hm hsm hs hE x).complZeroPairIso.hom ≫
          fiberThomPairMap F' E' (ofTransverseSection hm hsm hs hE x)) n u := by
  let := transverseZeroSetChartedSpace hm hsm hs hE
  have := isManifold_transverseZeroSet hm hsm hs hE
  have := J.stronglyLocallyContractibleSpace
  have := ChartedSpace.stronglyLocallyContractibleSpace G X
  let := (ofTransverseSection hm hsm hs hE).normalSpaceFiberBundle hm (Nat.eq_sub_of_add_eq' hE)
  have := (ofTransverseSection hm hsm hs hE).normalSpaceVectorBundle hm (Nat.eq_sub_of_add_eq' hE)
  set e := trivializationAt F'
    (fun x ↦ (ofTransverseSection hm hsm hs hE).isImmersion.NormalSpace x hm) x
  have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt F' _ x
  set m := (e.continuousLinearEquivAt ℝ x hx).symm
  set ψ := normalSpaceEquivOfTransverseSection hm hsm hs hE x
  set e' := trivializationAt F' E' (ofTransverseSection hm hsm hs hE x)
  have hx' : ofTransverseSection hm hsm hs hE x ∈ e'.baseSet :=
    mem_baseSet_trivializationAt F' E' (ofTransverseSection hm hsm hs hE x)
  set ℓ := e'.continuousLinearEquivAt ℝ (ofTransverseSection hm hsm hs hE x) hx'
  set L := m.trans (ψ.trans ℓ)
  -- The normal slice `g' : w ↦ Φ(x, m w)` and the section along it, `g = s ∘ g'`.
  obtain ⟨hgc', hg0', hgf', A', hg', hA'⟩ := hΦ.exists_hasMFDerivAt_apply_mk x m
  set g' : F' → X := fun w ↦ (Φ (TotalSpace.mk' F' x (m w)) : X)
  set g : F' → TotalSpace F' E' := fun w ↦ TotalSpace.mk' F' (g' w) (s (g' w))
  have hgS : ContinuousOn g univ := (hsm.continuous.comp hgc').continuousOn
  have hzero : ∀ y, y = ofTransverseSection hm hsm hs hE x →
      TotalSpace.mk' F' y (s y) = zeroSection F' E' (ofTransverseSection hm hsm hs hE x) := by
    rintro _ rfl
    simp [zeroSection, ofTransverseSection_apply_eq_zero hm hsm hs hE x]
  have hg0 : g 0 = zeroSection F' E' (ofTransverseSection hm hsm hs hE x) := hzero _ hg0'
  have hgS0 : ∀ w ∈ univ, w ≠ 0 → (g w).snd ≠ 0 := fun w _ hw h ↦
    hw (hgf' w (by rw [range_ofTransverseSection]; exact h))
  -- The coordinate of `s` in `e'` has derivative `ℓ ∘ Ds` at `f x`.
  set c : X → F' := fun y ↦ (e' (TotalSpace.mk' F' y (s y))).2
  have hc : ∀ y, y = ofTransverseSection hm hsm hs hE x →
      HasMFDerivAt J 𝓘(ℝ, F') c y (mfderiv J 𝓘(ℝ, F') c y) := by
    rintro _ rfl
    have he := e'.contMDiffAt_iff (n := ∞) (IM := J) (IB := J)
      (f := fun x ↦ TotalSpace.mk' F' x (s x)) (x₀ := ofTransverseSection hm hsm hs hE x)
      (e'.mem_source.2 hx')
    exact ((he.1 (hsm _)).2.mdifferentiableAt hm).hasMFDerivAt
  have hcD : ∀ (y : X) (_ : y = ofTransverseSection hm hsm hs hE x) (D : TangentSpace J y),
      mfderiv J 𝓘(ℝ, F') c y D =
        ℓ (ψ ((ofTransverseSection hm hsm hs hE).isImmersion.normalClass x hm D)) := by
    rintro _ rfl D
    have h := congrArg (· D) (continuousLinearMapAt_comp_sectionLinearization continuousAt_id hx'
      (hc _ rfl).mdifferentiableAt (ofTransverseSection_apply_eq_zero hm hsm hs hE x))
    simp only [ContinuousLinearMap.comp_apply, mvfderiv_apply_eq_mfderiv_apply] at h
    rw [normalSpaceEquivOfTransverseSection_normalClass, ← ContinuousLinearEquiv.coe_coe,
      e'.coe_continuousLinearEquivAt_eq' hx']
    exact h.symm
  have hA : HasFDerivAt (fun w ↦ (e' (g w)).2) (L : F' →L[ℝ] F') 0 := by
    have h := (hc _ hg0').comp 0 hg'
    rw [hasMFDerivAt_iff_hasFDerivAt] at h
    refine h.congr_fderiv (ContinuousLinearMap.ext fun w ↦ ?_)
    refine (hcD _ hg0' (A' w)).trans ?_
    exact congrArg (fun v ↦ ℓ (ψ v))
      ((Manifold.IsImmersion.normalClassL_apply _ _ _ _).symm.trans (hA' w))
  have h1 := singularCohomologyMap_ofSubsetMap_eq_complZeroPairIso_inv_of_hasFDerivAt e' hx'
    Filter.univ_mem hgS hg0 hgS0 hA L.antilipschitzWith u
  -- Read on `(univ, univ ∖ {0})` through `m`, the normal slice followed by `s` is `g`.
  have hgi := ofSubsetMap_subtypeVal_comp_complZeroPairIso_hom_comp_normalSlice_comp _ hm
    (Nat.eq_sub_of_add_eq' hE) Φ hΦ.apply_zeroSection x m (thomPairMapOfNeZero ⟨_, hsm.continuous⟩
      (snd_ne_zero_of_notMem_range_ofTransverseSection hm hsm hs hE)) hgS
    (fun w hw ↦ mem_zeroSectionCompl.2 (hgS0 w (mem_univ w) hw))
    fun _ ↦ thomPairMapOfNeZero_fst_apply _ _ _
  -- Read in the same way, the fibre inclusion after `ψ` is `L` followed by `ℓ⁻¹`.
  have hLi : (TopPair.ofSubsetMap (X := TopCat.of (univ : Set F')) (Y := TopCat.of F')
        (TopCat.ofHom (ContinuousMap.subtypeVal univ)) (B := {⟨0, mem_univ 0⟩}ᶜ)
        (B' := {0}ᶜ) (fun _ hw h ↦ hw (Subtype.ext (Set.mem_singleton_iff.1 h))) ≫
        m.complZeroPairIso.hom) ≫ ψ.complZeroPairIso.hom ≫
        fiberThomPairMap F' E' (ofTransverseSection hm hsm hs hE x) =
      TopPair.ofSubsetMap (X := TopCat.of (univ : Set F')) (Y := TopCat.of F')
          (TopCat.ofHom ⟨fun w : (univ : Set F') ↦ (L : F' →L[ℝ] F') w,
            (L : F' →L[ℝ] F').continuous.comp continuous_subtypeVal⟩)
          (B := {⟨0, mem_univ 0⟩}ᶜ) (B' := {0}ᶜ)
          (fun w hw h ↦ hw (Subtype.ext (L.map_eq_zero_iff.1 (Set.mem_singleton_iff.1 h)))) ≫
        ℓ.complZeroPairIso.inv ≫
          fiberThomPairMap F' E' (ofTransverseSection hm hsm hs hE x) := by
    have hL : TopPair.ofSubsetMap (X := TopCat.of (univ : Set F')) (Y := TopCat.of F')
        (TopCat.ofHom (ContinuousMap.subtypeVal univ)) (B := {⟨0, mem_univ 0⟩}ᶜ)
        (B' := {0}ᶜ) (fun _ hw h ↦ hw (Subtype.ext (Set.mem_singleton_iff.1 h))) ≫
          L.complZeroPairIso.hom =
        TopPair.ofSubsetMap (X := TopCat.of (univ : Set F')) (Y := TopCat.of F')
          (TopCat.ofHom ⟨fun w : (univ : Set F') ↦ (L : F' →L[ℝ] F') w,
            (L : F' →L[ℝ] F').continuous.comp continuous_subtypeVal⟩)
          (B := {⟨0, mem_univ 0⟩}ᶜ) (B' := {0}ᶜ)
          (fun w hw h ↦ hw (Subtype.ext (L.map_eq_zero_iff.1 (Set.mem_singleton_iff.1 h)))) := by
      rw [ContinuousLinearEquiv.complZeroPairIso_hom]
      exact TopPair.ofSubsetMap_comp_ofSubsetMap_of_comp_eq _ _ _ rfl
    rw [← hL, ContinuousLinearEquiv.complZeroPairIso_trans,
      ContinuousLinearEquiv.complZeroPairIso_trans]
    simp only [Iso.trans_hom, Category.assoc, Iso.hom_inv_id_assoc]
  refine TopPair.injective_singularCohomologyMap_ofSubsetMap_subtypeVal_univ_comp R k M (0 : F')
    m.complZeroPairIso n ?_
  rw [← TopPair.singularCohomologyMap_comp_apply, ← TopPair.singularCohomologyMap_comp_apply,
    hgi, hLi, h1, TopPair.singularCohomologyMap_comp_apply,
    TopPair.singularCohomologyMap_comp_apply]

end LocalDegree

section DualClass

variable [T2Space X] [SecondCountableTopology X]

/-- **The pull-back along a transverse section is a relative dual class.** Let `s` be a smooth
section of `E'` transverse to the zero section, with zero set `Z`, and `u` a class of the Thom pair
of `E'` in the degree `r = finrank ℝ F'` of its rank, with coefficients `R, M : ModuleCat k` and
`R` projective over `k`. The pull-back of `u` along `s`, as a map of pairs
`(X, X ∖ Z) ⟶ (E', E'₀)`, is the relative class `relDualClassOf` of the inclusion of `Z` for
the pull-back of `u` to the normal bundle of `Z` along the normal-space equivalence of `s`
(`SymplecticGeometry.normalSpaceEquivOfTransverseSection`). -/
theorem relDualClassOf_ofTransverseSection {k : Type*} [CommRing k] {R M : ModuleCat.{w} k}
    [Module.Projective k R]
    (u : (thomPair F' E').singularCohomology R k M (finrank ℝ F')) :
    letI := transverseZeroSetChartedSpace hm hsm hs hE
    haveI := isManifold_transverseZeroSet hm hsm hs hE
    letI := (ofTransverseSection hm hsm hs hE).normalSpaceFiberBundle (P := F') hm
      (Nat.eq_sub_of_add_eq' hE)
    TopPair.singularCohomologyMap (thomPairMapOfNeZero ⟨_, hsm.continuous⟩
        (snd_ne_zero_of_notMem_range_ofTransverseSection hm hsm hs hE)) _ u =
      (ofTransverseSection hm hsm hs hE).relDualClassOf hm (Nat.eq_sub_of_add_eq' hE)
        (isClosed_range_ofTransverseSection hm hsm hs hE)
        (TopPair.singularCohomologyMap (thomPairMapOfFiberwise
          (g := (ofTransverseSection hm hsm hs hE).toContinuousMap)
          (continuous_normalSpaceEquivOfTransverseSection hm hsm hs hE)) _ u) := by
  let := transverseZeroSetChartedSpace hm hsm hs hE
  have := isManifold_transverseZeroSet hm hsm hs hE
  let := (ofTransverseSection hm hsm hs hE).normalSpaceFiberBundle (P := F') hm
    (Nat.eq_sub_of_add_eq' hE)
  obtain ⟨W, Φ, hΦ, -⟩ :=
    exists_isNormalizedTube_singularCohomologyMap_excisionMap_relDualClassOf (R := R) (k := k)
      (M := M) (ofTransverseSection hm hsm hs hE) hm (Nat.eq_sub_of_add_eq' hE)
      (isClosed_range_ofTransverseSection hm hsm hs hE)
  refine (eq_relDualClassOf_iff_forall_slice _ hm _ _ hΦ _ _).2 fun x ↦ ?_
  rw [← TopPair.singularCohomologyMap_comp_apply,
    singularCohomologyMap_normalSlice_thomPairMapOfNeZero hm hsm hs hE hΦ x,
    ← TopPair.singularCohomologyMap_comp_apply, fiberThomPairMap_comp_thomPairMapOfFiberwise]
  -- The fibre is over `f.toContinuousMap x`, which is `f x` by definition.
  rfl

/-- **The pull-back of the Thom class along a transverse section.** Let `s` be a smooth section,
transverse to the zero section, of a real vector bundle `E'` of rank `r` with an orientation `o'`,
and let `Z` be its zero set. The pull-back of the canonical Thom class of `o'` along `s`, as a map
of pairs `(X, X ∖ Z) ⟶ (E', E'₀)`, is the relative dual class `relDualClass` of `Z` for the
normal orientation `SymplecticGeometry.normalOrientationOfSection o'` carried from `o'` by the
linearization of `s`. Every rank is allowed, including `r = 0`. -/
theorem relDualClass_ofTransverseSection {r : ℕ} (o' : VectorBundleOrientation F' E' (Fin r))
    (hr : finrank ℝ F' = r) :
    letI := transverseZeroSetChartedSpace hm hsm hs hE
    haveI := isManifold_transverseZeroSet hm hsm hs hE
    TopPair.singularCohomologyMap (thomPairMapOfNeZero ⟨_, hsm.continuous⟩
        (snd_ne_zero_of_notMem_range_ofTransverseSection hm hsm hs hE)) r
        (o'.canonicalThomClass hr) =
      (ofTransverseSection hm hsm hs hE).relDualClass hm (Nat.eq_sub_of_add_eq' hE)
        (isClosed_range_ofTransverseSection hm hsm hs hE)
        (normalOrientationOfSection hm hsm hs hE ((Fintype.card_fin r).trans hr.symm) o') hr := by
  let := transverseZeroSetChartedSpace hm hsm hs hE
  have := isManifold_transverseZeroSet hm hsm hs hE
  let := (ofTransverseSection hm hsm hs hE).normalSpaceFiberBundle (P := F') hm
    (Nat.eq_sub_of_add_eq' hE)
  let := (ofTransverseSection hm hsm hs hE).normalSpaceVectorBundle (P := F') hm
    (Nat.eq_sub_of_add_eq' hE)
  subst hr
  have hι : Fintype.card (Fin (finrank ℝ F')) = finrank ℝ F' := Fintype.card_fin _
  have h := o'.singularCohomologyMap_thomPairMapOfFiberwise_canonicalThomClass
    (g := (ofTransverseSection hm hsm hs hE).toContinuousMap) rfl
    (normalOrientationOfSection hm hsm hs hE hι o') rfl
    (continuous_normalSpaceEquivOfTransverseSection hm hsm hs hE)
    (map_normalOrientationOfSection_apply hm hsm hs hE hι o')
  -- `relDualClassOf_ofTransverseSection` is stated for the `ℤ`-linear structure
  -- `ModuleCat.instLinear`; read the class for that structure.
  rw [relDualClass_eq_singularCohomologyLinearCongr_relDualClassOf, ← h,
    TopPair.singularCohomologyLinearCongr_naturality,
    ← relDualClassOf_ofTransverseSection hm hsm hs hE,
    TopPair.singularCohomologyLinearCongr_naturality,
    TopPair.singularCohomologyLinearCongr_apply_apply, TopPair.singularCohomologyLinearCongr_refl,
    LinearEquiv.refl_apply]


/-- **The dual class of the zero set of a transverse section is the Euler class.** Let `s` be a
smooth section, transverse to the zero section, of a real vector bundle `E'` of rank `r` with an
orientation `o'`. The dual class of its zero set, for the normal orientation
`SymplecticGeometry.normalOrientationOfSection o'`, is the Euler class of the canonical Thom class
of `o'`. Every rank is allowed, including `r = 0`. -/
theorem dualClass_ofTransverseSection {r : ℕ} (o' : VectorBundleOrientation F' E' (Fin r))
    (hr : finrank ℝ F' = r) :
    letI := transverseZeroSetChartedSpace hm hsm hs hE
    haveI := isManifold_transverseZeroSet hm hsm hs hE
    (ofTransverseSection hm hsm hs hE).dualClass hm (Nat.eq_sub_of_add_eq' hE)
        (isClosed_range_ofTransverseSection hm hsm hs hE)
        (normalOrientationOfSection hm hsm hs hE ((Fintype.card_fin r).trans hr.symm) o') hr =
      eulerClass _ _ _ F' E' r (o'.canonicalThomClass hr) := by
  let := transverseZeroSetChartedSpace hm hsm hs hE
  have := isManifold_transverseZeroSet hm hsm hs hE
  rw [dualClass_eq_singularCohomologyπ_relDualClass, ← relDualClass_ofTransverseSection,
    eulerClass_eq_singularCohomologyMap_thomPairMapOfNeZero F' E' hsm.continuous
      (snd_ne_zero_of_notMem_range_ofTransverseSection hm hsm hs hE)]
  -- The first space of the pair `(X, X ∖ Z)` is `X` only up to unfolding `TopPair.ofSubset`, so
  -- `ConcreteCategory.comp_apply` does not rewrite.
  exact (ConcreteCategory.comp_apply _ _ _).symm

/-- **The dual class of the zero set of a transverse section is the Euler class**, for an oriented
bundle `E'` of positive rank `m + 1`: the dual class of the zero set, for the normal orientation
`SymplecticGeometry.normalOrientationOfSection o'`, is the Euler class of `o'`. -/
theorem dualClass_ofTransverseSection_eq_eulerClass {m : ℕ}
    (o' : VectorBundleOrientation F' E' (Fin (m + 1))) (hr : finrank ℝ F' = m + 1) :
    letI := transverseZeroSetChartedSpace hm hsm hs hE
    haveI := isManifold_transverseZeroSet hm hsm hs hE
    (ofTransverseSection hm hsm hs hE).dualClass hm (Nat.eq_sub_of_add_eq' hE)
        (isClosed_range_ofTransverseSection hm hsm hs hE)
        (normalOrientationOfSection hm hsm hs hE ((Fintype.card_fin _).trans hr.symm) o') hr =
      o'.eulerClass hr := by
  let := transverseZeroSetChartedSpace hm hsm hs hE
  have := isManifold_transverseZeroSet hm hsm hs hE
  rw [dualClass_ofTransverseSection, VectorBundleOrientation.canonicalThomClass_eq_thomClass,
    VectorBundleOrientation.eulerClass_def]

section Complex

variable [NormedSpace ℂ F'] [IsScalarTower ℝ ℂ F'] [FiniteDimensional ℂ F']
  [∀ x, Module ℂ (E' x)] [∀ x, IsScalarTower ℝ ℂ (E' x)] [VectorBundle ℂ F' E']

/-- **Complex bundles: the dual class of a transverse zero set is `complexEulerClass`.** Let `s`
be a smooth section, transverse to the zero section, of a complex vector bundle `E'` of complex
rank `n + 1`, for instance a complex line bundle (`n = 0`). The dual class of its
zero set, for the normal orientation `SymplecticGeometry.normalOrientationOfSection` carried from
the canonical orientation `VectorBundleOrientation.complex` of `E'` (reindexed by
`Fin (2 * finrank ℂ F') ≃ Fin (2 * n + 2)`), is the Euler class `TauCeti.complexEulerClass` of
`E'`. -/
theorem dualClass_ofTransverseSection_eq_complexEulerClass {n : ℕ} (hF : finrank ℂ F' = n + 1) :
    letI := transverseZeroSetChartedSpace hm hsm hs hE
    haveI := isManifold_transverseZeroSet hm hsm hs hE
    (ofTransverseSection hm hsm hs hE).dualClass hm (Nat.eq_sub_of_add_eq' hE)
        (isClosed_range_ofTransverseSection hm hsm hs hE)
        (normalOrientationOfSection hm hsm hs hE
          (by rw [Fintype.card_fin, finrank_real_eq_two_mul_finrank_complex, hF]; ring)
          (VectorBundleOrientation.reindex
            (finCongr (by omega) : Fin (2 * finrank ℂ F') ≃ Fin (2 * n + 2))
            (VectorBundleOrientation.complex F' E')))
        (by rw [finrank_real_eq_two_mul_finrank_complex, hF]; ring) =
      complexEulerClass F' E' hF := by
  rw [complexEulerClass_def]
  exact dualClass_ofTransverseSection_eq_eulerClass hm hsm hs hE _ _

end Complex

end DualClass

end TauCeti.SmoothEmbedding

end
