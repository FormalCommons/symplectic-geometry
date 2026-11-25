/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.RingTheory.TensorProduct.Finite
public import SymplecticGeometry.Geometry.Manifold.DeRham.GoodCover.Compact
public import SymplecticGeometry.Geometry.Manifold.DeRham.SmoothFamily.Contractible
public import SymplecticGeometry.Geometry.Manifold.DeRham.SmoothFamily.MayerVietoris
public import TauCeti.Geometry.Manifold.DeRham.ComplexCoefficients
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import SymplecticGeometry.Topology.Sets.Opens.Basic

/-!
# Smooth families of primitives on manifolds with a finite good cover

A finite good cover `U` of a manifold `M` gives one cohomology splitting of `M`
(`SymplecticGeometry.IsFiniteGoodCover.smoothCohomologySplitting`), which is smooth over
parameter manifolds in all universes
(`SymplecticGeometry.IsFiniteGoodCover.isSmooth_smoothCohomologySplitting`).
It is built by a Mayer–Vietoris recursion over the cover, after Bott and Tu [BottTu1982]. For a
finset `s` of nonempty finsets of indices, write `V a = ⋂ i ∈ a, U i` and `W s = ⋃ a ∈ s, V a`.
The splitting of `W s` (`SymplecticGeometry.IsFiniteGoodCover.smoothCohomologySplittingISup`) is
defined by well-founded recursion on the number of elements of `s`:

* `W ∅` is empty, and gets the zero splitting of an empty manifold
  (`SymplecticGeometry.SmoothCohomologySplitting.ofIsEmpty`);
* otherwise, for a chosen `a ∈ s` and `s' = s.erase a`, `W s = V a ∪ W s'`, and
  `V a ∩ W s' = W s''` with `s'' = {a ∪ b | b ∈ s'}`, which has fewer elements than `s`. The set
  `V a` is empty or smoothly contractible, and gets the zero splitting or
  `SymplecticGeometry.SmoothCohomologySplitting.ofIsSmoothlyContractible`
  (`SymplecticGeometry.IsFiniteGoodCover.smoothCohomologySplittingInf`); the Mayer–Vietoris step
  `SymplecticGeometry.SmoothCohomologySplitting.sup` gives the splitting of `W s`, transported
  along the equalities of open sets above.

All choices in the recursion concern forms only, never parameter manifolds, so the splitting does
not depend on their universes, and its smoothness is proved by the same induction at every
universe triple. The cover by the singletons gives `W = ⊤`, and the splitting is carried to `M`
along `Diffeomorph.ofTop`. From the splitting follow the smooth families of primitives of exact
forms, the finite dimension of de Rham cohomology, and the smoothness of the cohomology classes of
a smooth family of closed forms; with Weil's finite good covers of compact manifolds
(`SymplecticGeometry.hasFiniteGoodCover_of_compactSpace`), de Rham cohomology of a compact
boundaryless manifold is finite-dimensional.

## Main definitions

* `SymplecticGeometry.SmoothCohomologySplitting.ofIsEmpty`: the zero splitting of an empty
  manifold.
* `SymplecticGeometry.IsFiniteGoodCover.smoothCohomologySplitting` and
  `SymplecticGeometry.HasFiniteGoodCover.smoothCohomologySplitting`: the splitting of a manifold
  with a finite good cover.

## Main results

* `SymplecticGeometry.IsFiniteGoodCover.isSmooth_smoothCohomologySplitting` and
  `SymplecticGeometry.HasFiniteGoodCover.isSmooth_smoothCohomologySplitting`: that splitting is
  smooth.
* `SymplecticGeometry.SmoothCohomologySplitting.isSmooth_eqRec_iff`: transport along an equality
  of open sets keeps smoothness.
* `SymplecticGeometry.exists_primitiveMap_of_hasFiniteGoodCover`: on such a manifold, a linear
  choice of primitives of exact forms, under which smooth families have smooth primitives.
* `SymplecticGeometry.exists_isSmoothFamily_mextDerivₗ_eq`: a smooth family of exact forms over
  any smooth parameter manifold has a smooth family of primitives.
* `SymplecticGeometry.finiteDimensional_deRhamCohomology_of_hasFiniteGoodCover`,
  `SymplecticGeometry.contMDiff_repr_mk_of_hasFiniteGoodCover`, and the instance
  `SymplecticGeometry.finiteDimensional_deRhamCohomology` on compact boundaryless manifolds, with
  its complex counterpart `TauCeti.finiteDimensional_complexDeRhamCohomology`.

## References

* [R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982], §§2–5
  (Mayer–Vietoris arguments over good covers).
* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], proof of
  Theorem 3.2.4.
* [A. Weil, *Sur les théorèmes de de Rham*][Weil1952], §1 (finite good covers of compact
  manifolds).
-/

public section

open TopologicalSpace
open scoped Manifold ContDiff

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

namespace SymplecticGeometry

open TauCeti

universe uE uH uN

variable (I M) in
/-- **The splitting of an empty manifold.** On an empty manifold every form is zero; the
splitting has the zero spaces, projections and primitives. -/
noncomputable def SmoothCohomologySplitting.ofIsEmpty [IsManifold I ∞ M] [IsEmpty M] :
    SmoothCohomologySplitting I M where
  space _ := ⊥
  space_le_closedForms _ := bot_le
  finiteDimensional_space _ := inferInstance
  proj _ := 0
  proj_mem _ _ := Submodule.zero_mem _
  proj_zero _ := Subsingleton.elim _ _
  primitive _ := 0
  mextDerivₗ_primitive _ _ := Subsingleton.elim _ _
  eq_zero_of_mem_exactForms _ _ _ _ := Subsingleton.elim _ _

/-- The splitting of an empty manifold is smooth, over parameter manifolds in all universes. -/
theorem SmoothCohomologySplitting.isSmooth_ofIsEmpty [IsManifold I ∞ M] [IsEmpty M] :
    (ofIsEmpty I M).IsSmooth.{uE, uH, uN} :=
  ⟨fun _ ↦ preservesSmoothFamilies_zero, fun _ ↦ preservesSmoothFamilies_zero⟩

/-- Transport of a splitting along an equality `W = W'` of open sets keeps and reflects
smoothness. -/
theorem SmoothCohomologySplitting.isSmooth_eqRec_iff [IsManifold I ∞ M] {W W' : Opens M}
    (h : W = W') (σ : SmoothCohomologySplitting I W) :
    (h ▸ σ : SmoothCohomologySplitting I W').IsSmooth.{uE, uH, uN} ↔ σ.IsSmooth.{uE, uH, uN} := by
  subst h
  rfl

namespace IsFiniteGoodCover

variable {ι : Type*} [Finite ι] {U : ι → Opens M}

open scoped Classical in
/-- The splitting of a member `⋂ i ∈ a, U i` of a finite good cover, for `a` nonempty: the zero
splitting if the intersection is empty, and that of a smoothly contractible manifold if not. -/
noncomputable def smoothCohomologySplittingInf [IsManifold I ∞ M] (hU : IsFiniteGoodCover I U)
    {a : Finset ι} (ha : a.Nonempty) : SmoothCohomologySplitting I (⨅ i ∈ a, U i : Opens M) :=
  if hne : ((⨅ i ∈ a, U i : Opens M) : Set M).Nonempty then
    .ofIsSmoothlyContractible I (hU.isSmoothlyContractible ha hne)
  else
    haveI : IsEmpty (⨅ i ∈ a, U i : Opens M) := ⟨fun x ↦ hne ⟨x, x.property⟩⟩
    .ofIsEmpty I _

/-- The splitting of a member of a finite good cover is smooth, over parameter manifolds in all
universes. -/
theorem isSmooth_smoothCohomologySplittingInf [IsManifold I ∞ M] (hU : IsFiniteGoodCover I U)
    {a : Finset ι} (ha : a.Nonempty) :
    (hU.smoothCohomologySplittingInf ha).IsSmooth.{uE, uH, uN} := by
  rw [smoothCohomologySplittingInf]
  split_ifs with hne
  · exact SmoothCohomologySplitting.isSmooth_ofIsSmoothlyContractible _
  · have : IsEmpty (⨅ i ∈ a, U i : Opens M) := ⟨fun x ↦ hne ⟨x, x.property⟩⟩
    exact SmoothCohomologySplitting.isSmooth_ofIsEmpty

end IsFiniteGoodCover

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  {EN HN N : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
  [TopologicalSpace N] [ChartedSpace HN N] {J : ModelWithCorners ℝ EN HN} [IsManifold J ∞ N]

namespace IsFiniteGoodCover

variable {ι : Type*} [Finite ι] {U : ι → Opens M}

open scoped Classical in
/-- **The induction over a good cover.** Let `U` be a finite good cover of `M` and `s` a finset of
nonempty finsets of indices. The splitting of the union `⋃ a ∈ s, ⋂ i ∈ a, U i` defined by
recursion on the number of elements of `s`: for `s` empty, the zero splitting; otherwise, for a
chosen `a ∈ s`, the Mayer–Vietoris step `SmoothCohomologySplitting.sup` applied to the splittings
of `⋂ i ∈ a, U i`, of the union over `s.erase a`, and of their intersection, which is the union
over the finsets `a ∪ b` with `b ∈ s.erase a`. -/
noncomputable def smoothCohomologySplittingISup (hU : IsFiniteGoodCover I U)
    (s : Finset (Finset ι)) (hs : ∀ a ∈ s, a.Nonempty) :
    SmoothCohomologySplitting I (⨆ a ∈ s, ⨅ i ∈ a, U i : Opens M) :=
  if h : s.Nonempty then
    have ha : h.choose ∈ s := h.choose_spec
    have hs' : ∀ b ∈ s.erase h.choose, b.Nonempty :=
      fun b hb ↦ hs b (Finset.mem_of_mem_erase hb)
    have hs'' : ∀ c ∈ (s.erase h.choose).image (h.choose ∪ ·), c.Nonempty := by
      simp only [Finset.mem_image]
      rintro _ ⟨b, -, rfl⟩
      exact (hs _ ha).mono Finset.subset_union_left
    have : ((s.erase h.choose).image (h.choose ∪ ·)).card < s.card :=
      Finset.card_image_le.trans_lt (Finset.card_erase_lt_of_mem ha)
    have : (s.erase h.choose).card < s.card := Finset.card_erase_lt_of_mem ha
    -- The intersection of `V a` with the union over `s.erase a` is the union over the image.
    have hinf : (⨆ c ∈ (s.erase h.choose).image (h.choose ∪ ·), ⨅ i ∈ c, U i : Opens M) =
        (⨅ i ∈ h.choose, U i) ⊓ (⨆ b ∈ s.erase h.choose, ⨅ i ∈ b, U i) := by
      rw [inf_iSup₂_eq, Finset.iSup_finset_image]
      simp only [Finset.iInf_union]
    have hsup : (⨅ i ∈ h.choose, U i) ⊔ (⨆ b ∈ s.erase h.choose, ⨅ i ∈ b, U i) =
        (⨆ b ∈ s, ⨅ i ∈ b, U i : Opens M) := by
      conv_rhs => rw [← Finset.insert_erase ha, Finset.iSup_insert]
    hsup ▸ SmoothCohomologySplitting.sup
      (MayerVietorisCutoff.nonempty _ _).some (hU.smoothCohomologySplittingInf (hs _ ha))
      (hU.smoothCohomologySplittingISup (s.erase h.choose) hs')
      (hinf ▸ hU.smoothCohomologySplittingISup ((s.erase h.choose).image (h.choose ∪ ·)) hs'')
  else
    haveI : IsEmpty (⨆ a ∈ s, ⨅ i ∈ a, U i : Opens M) := ⟨fun x ↦ by
      obtain ⟨b, hb, -⟩ : ∃ b ∈ s, _ := by simpa using x.property
      exact h ⟨b, hb⟩⟩
    .ofIsEmpty I _
termination_by s.card

/-- The splitting of a union of members of a finite good cover is smooth, over parameter
manifolds in all universes. -/
theorem isSmooth_smoothCohomologySplittingISup (hU : IsFiniteGoodCover I U)
    (s : Finset (Finset ι)) (hs : ∀ a ∈ s, a.Nonempty) :
    (hU.smoothCohomologySplittingISup s hs).IsSmooth.{uE, uH, uN} := by
  classical
  induction hn : s.card using Nat.strong_induction_on generalizing s with
  | _ n ih =>
    subst hn
    rw [smoothCohomologySplittingISup]
    split_ifs with h
    · have ha : h.choose ∈ s := h.choose_spec
      rw [SmoothCohomologySplitting.isSmooth_eqRec_iff]
      refine (isSmooth_smoothCohomologySplittingInf hU _).sup _
        (ih _ (Finset.card_erase_lt_of_mem ha) _ _ rfl) ?_
      rw [SmoothCohomologySplitting.isSmooth_eqRec_iff]
      exact ih _ (Finset.card_image_le.trans_lt (Finset.card_erase_lt_of_mem ha)) _ _ rfl
    · have : IsEmpty (⨆ a ∈ s, ⨅ i ∈ a, U i : Opens M) := ⟨fun x ↦ by
        obtain ⟨b, hb, -⟩ : ∃ b ∈ s, _ := by simpa using x.property
        exact h ⟨b, hb⟩⟩
      exact SmoothCohomologySplitting.isSmooth_ofIsEmpty

open scoped Classical in
/-- **The splitting of a manifold with a finite good cover.** The splitting of the union over the
singletons of a finite good cover `U`, which is `⊤`, carried to `M` along `Diffeomorph.ofTop`. -/
noncomputable def smoothCohomologySplitting (hU : IsFiniteGoodCover I U) :
    SmoothCohomologySplitting I M :=
  haveI := Fintype.ofFinite ι
  (hU.smoothCohomologySplittingISup (Finset.univ.image ({·} : ι → Finset ι)) (by simp))
    |>.ofDiffeomorph (Diffeomorph.ofTop _ (by
      simpa only [Finset.iSup_finset_image, Finset.iInf_singleton, Finset.mem_univ, iSup_pos]
        using hU.iSup_eq_top)).symm

/-- **Smooth cohomology splittings from a finite good cover.** On a Hausdorff σ-compact manifold,
modelled on a finite-dimensional space, the splitting given by a finite good cover is smooth, over
parameter manifolds in all universes. -/
theorem isSmooth_smoothCohomologySplitting (hU : IsFiniteGoodCover I U) :
    hU.smoothCohomologySplitting.IsSmooth.{uE, uH, uN} :=
  (hU.isSmooth_smoothCohomologySplittingISup _ _).ofDiffeomorph _

end IsFiniteGoodCover

/-- **The splitting of a manifold with a finite good cover.** The splitting given by a finite good
cover of `M` chosen from `HasFiniteGoodCover I M`. -/
noncomputable def HasFiniteGoodCover.smoothCohomologySplitting (hM : HasFiniteGoodCover I M) :
    SmoothCohomologySplitting I M :=
  (hasFiniteGoodCover_def.mp hM).choose_spec.choose_spec.smoothCohomologySplitting

/-- **Smooth cohomology splittings from a finite good cover.** On a Hausdorff σ-compact manifold,
modelled on a finite-dimensional space, that has a finite good cover, the splitting
`HasFiniteGoodCover.smoothCohomologySplitting` is smooth, over parameter manifolds in all
universes. -/
theorem HasFiniteGoodCover.isSmooth_smoothCohomologySplitting (hM : HasFiniteGoodCover I M) :
    hM.smoothCohomologySplitting.IsSmooth.{uE, uH, uN} :=
  IsFiniteGoodCover.isSmooth_smoothCohomologySplitting _

/-- **Smooth families of primitives.** On a Hausdorff σ-compact manifold, modelled on a
finite-dimensional space, that has a finite good cover, there is a linear map `P` from the exact
`(k + 1)`-forms to the `k`-forms with `d (P η) = η` for every exact form `η`, which takes smooth
families of exact forms to smooth families of forms over every smooth parameter manifold whose
model space, model and points lie in the universes `uE`, `uH` and `uN` of
`PreservesSmoothFamilies`. The map `P`, `hM.smoothCohomologySplitting.exactPrimitive k`, is the
same for all these universes.

Milestone: *Smooth families of primitives*. -/
theorem exists_primitiveMap_of_hasFiniteGoodCover (hM : HasFiniteGoodCover I M) (k : ℕ) :
    ∃ P : exactForms I M (k + 1) →ₗ[ℝ] SmoothForm I M ℝ k,
      (∀ η, mextDerivₗ I k (P η) = η) ∧ PreservesSmoothFamilies P :=
  ⟨_, hM.smoothCohomologySplitting.mextDerivₗ_exactPrimitive k,
    hM.isSmooth_smoothCohomologySplitting.preservesSmoothFamilies_exactPrimitive k⟩

/-- **Smooth families of primitives, for one family.** On a Hausdorff σ-compact manifold,
modelled on a finite-dimensional space, that has a finite good cover, a smooth family `η` of
exact `(k + 1)`-forms over a smooth parameter manifold `N`, possibly with boundary, has a smooth
family `α` of primitives: `d (α t) = η t` for every `t`. -/
theorem exists_isSmoothFamily_mextDerivₗ_eq (hM : HasFiniteGoodCover I M) {k : ℕ}
    {η : N → SmoothForm I M ℝ (k + 1)} (hη : IsSmoothFamily J η)
    (hex : ∀ t, η t ∈ exactForms I M (k + 1)) :
    ∃ α : N → SmoothForm I M ℝ k, IsSmoothFamily J α ∧ ∀ t, mextDerivₗ I k (α t) = η t :=
  ⟨fun t ↦ hM.smoothCohomologySplitting.exactPrimitive k ⟨η t, hex t⟩,
    preservesSmoothFamilies_def.mp
      (hM.isSmooth_smoothCohomologySplitting.preservesSmoothFamilies_exactPrimitive k) _ hη,
    fun _ ↦ hM.smoothCohomologySplitting.mextDerivₗ_exactPrimitive k _⟩

/-- A Hausdorff σ-compact manifold, modelled on a finite-dimensional space, that has a finite
good cover has finite-dimensional de Rham cohomology in every degree. -/
theorem finiteDimensional_deRhamCohomology_of_hasFiniteGoodCover (hM : HasFiniteGoodCover I M)
    (k : ℕ) : FiniteDimensional ℝ (deRhamCohomology I M k) :=
  hM.smoothCohomologySplitting.finiteDimensional_deRhamCohomology k
/-- **The classes of a smooth family of closed forms depend smoothly on the parameter.** On a
Hausdorff σ-compact manifold, modelled on a finite-dimensional space, that has a finite good
cover, let `b` be a basis of the de Rham cohomology in degree `k` and `z` a smooth family of
closed `k`-forms over a smooth parameter manifold `N`. Then each coordinate
`t ↦ b.repr [z t] i` is a smooth function on `N`. -/
theorem contMDiff_repr_mk_of_hasFiniteGoodCover (hM : HasFiniteGoodCover I M) {k : ℕ}
    {ι : Type*} (b : Module.Basis ι ℝ (deRhamCohomology I M k))
    {z : N → closedForms I M k}
    (hz : IsSmoothFamily J (fun t ↦ (z t : SmoothForm I M ℝ k))) (i : ι) :
    ContMDiff J 𝓘(ℝ) ∞ (fun t ↦ b.repr (deRhamCohomology.mk I k (z t)) i) :=
  hM.isSmooth_smoothCohomologySplitting.contMDiff_repr_mk b hz i

omit [SigmaCompactSpace M] in
/-- **De Rham cohomology of a compact manifold is finite-dimensional.** On a compact Hausdorff
boundaryless manifold, modelled on a finite-dimensional space, the de Rham cohomology is
finite-dimensional in every degree. -/
theorem finiteDimensional_deRhamCohomology [CompactSpace M] [BoundarylessManifold I M]
    {k : ℕ} : FiniteDimensional ℝ (deRhamCohomology I M k) :=
  finiteDimensional_deRhamCohomology_of_hasFiniteGoodCover hasFiniteGoodCover_of_compactSpace k

attribute [instance] finiteDimensional_deRhamCohomology

end SymplecticGeometry

namespace TauCeti

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
  [BoundarylessManifold I M]

/-- **Complex de Rham cohomology of a compact manifold is finite-dimensional.** On a compact
Hausdorff boundaryless manifold, modelled on a finite-dimensional space, the complex de Rham
cohomology is finite-dimensional in every degree. -/
theorem finiteDimensional_complexDeRhamCohomology {k : ℕ} :
    FiniteDimensional ℂ (complexDeRhamCohomology I M k) :=
  Module.Finite.equiv (complexDeRhamCohomology.complexificationEquiv I k)

attribute [instance] finiteDimensional_complexDeRhamCohomology

end TauCeti
