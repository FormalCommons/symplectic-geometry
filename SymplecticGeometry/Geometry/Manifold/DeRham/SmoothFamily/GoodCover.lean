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

A manifold `M` with a finite good cover `U` has a smooth cohomology splitting
(`SymplecticGeometry.IsFiniteGoodCover.exists_smoothCohomologySplitting_isSmooth`). The proof is a
Mayer–Vietoris induction over the cover, after Bott and Tu [BottTu1982]. For a finset `s` of
nonempty finsets of indices, write `V a = ⋂ i ∈ a, U i` and `W s = ⋃ a ∈ s, V a`. By strong
induction on the number of elements of `s`, every `W s` has a splitting:

* `W ∅` is empty, and an empty manifold has the zero splitting
  (`SymplecticGeometry.SmoothCohomologySplitting.exists_isSmooth_of_isEmpty`);
* for `a ∈ s` with `s = insert a s'`, `W s = V a ∪ W s'`, and `V a ∩ W s' = W s''` with
  `s'' = {a ∪ b | b ∈ s'}`, which has fewer elements than `s`. The set `V a` is empty or smoothly
  contractible, so it has a splitting by
  `SymplecticGeometry.SmoothCohomologySplitting.exists_isSmooth_of_isSmoothlyContractible`, and
  the Mayer–Vietoris step `SymplecticGeometry.SmoothCohomologySplitting.exists_isSmooth_sup`
  gives one on `W s`.

The cover by the singletons gives `W = ⊤`, and the splitting is carried to `M` along
`Diffeomorph.ofTop`. From the splitting follow the smooth families of primitives of exact forms,
the finite dimension of de Rham cohomology, and the smoothness of the cohomology classes of a
smooth family of closed forms; with Weil's finite good covers of compact manifolds
(`SymplecticGeometry.hasFiniteGoodCover_of_compactSpace`), de Rham cohomology of a compact
boundaryless manifold is finite-dimensional.

## Main results

* `SymplecticGeometry.IsFiniteGoodCover.exists_smoothCohomologySplitting_isSmooth` and
  `SymplecticGeometry.HasFiniteGoodCover.exists_smoothCohomologySplitting_isSmooth`: a manifold
  with a finite good cover has a smooth cohomology splitting.
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
/-- **The splitting of an empty manifold.** On an empty manifold every form is zero, and the
zero spaces with the zero projections and primitives form a smooth cohomology splitting. -/
theorem SmoothCohomologySplitting.exists_isSmooth_of_isEmpty [IsManifold I ∞ M] [IsEmpty M] :
    ∃ σ : SmoothCohomologySplitting I M, σ.IsSmooth.{uE, uH, uN} :=
  ⟨{ space := fun _ ↦ ⊥
     space_le_closedForms := fun _ ↦ bot_le
     finiteDimensional_space := fun _ ↦ inferInstance
     proj := fun _ ↦ 0
     proj_mem := fun _ _ ↦ Submodule.zero_mem _
     proj_zero := fun _ ↦ Subsingleton.elim _ _
     primitive := fun _ ↦ 0
     mextDerivₗ_primitive := fun _ _ ↦ Subsingleton.elim _ _
     eq_zero_of_mem_exactForms := fun _ _ _ _ ↦ Subsingleton.elim _ _ },
    ⟨fun _ ↦ preservesSmoothFamilies_zero, fun _ ↦ preservesSmoothFamilies_zero⟩⟩

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  {EN HN N : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
  [TopologicalSpace N] [ChartedSpace HN N] {J : ModelWithCorners ℝ EN HN} [IsManifold J ∞ N]

/-- **The induction over a good cover.** Let `U` be a finite good cover of `M`. For every finset
`s` of nonempty finsets of indices, the union over `a ∈ s` of the intersections
`⋂ i ∈ a, U i` has a smooth cohomology splitting. -/
theorem IsFiniteGoodCover.exists_smoothCohomologySplitting_isSmooth_iSup {ι : Type*} [Finite ι]
    {U : ι → Opens M} (hU : IsFiniteGoodCover I U) (s : Finset (Finset ι))
    (hs : ∀ a ∈ s, a.Nonempty) :
    ∃ σ : SmoothCohomologySplitting I (⨆ a ∈ s, ⨅ i ∈ a, U i : Opens M),
      σ.IsSmooth.{uE, uH, uN} := by
  classical
  induction hn : s.card using Nat.strong_induction_on generalizing s with
  | _ n ih =>
    subst hn
    rcases s.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
    · rw [show (⨆ a ∈ (∅ : Finset (Finset ι)), ⨅ i ∈ a, U i : Opens M) = ⊥ by simp]
      exact SmoothCohomologySplitting.exists_isSmooth_of_isEmpty I _
    -- The member `V a` of the union: empty, or smoothly contractible.
    have hV : ∃ σ : SmoothCohomologySplitting I (⨅ i ∈ a, U i : Opens M),
        σ.IsSmooth.{uE, uH, uN} := by
      rcases ((⨅ i ∈ a, U i : Opens M) : Set M).eq_empty_or_nonempty with he | hne
      · rw [Opens.coe_eq_empty.1 he]
        exact SmoothCohomologySplitting.exists_isSmooth_of_isEmpty I _
      · exact SmoothCohomologySplitting.exists_isSmooth_of_isSmoothlyContractible I
          (hU.isSmoothlyContractible (hs a ha) hne)
    set s' := s.erase a
    -- The intersection of `V a` with the union over `s'` is the union over `s''`.
    set s'' := s'.image (a ∪ ·)
    have hs'' : s''.card < s.card :=
      Finset.card_image_le.trans_lt (Finset.card_erase_lt_of_mem ha)
    have hinf : (⨅ i ∈ a, U i) ⊓ (⨆ b ∈ s', ⨅ i ∈ b, U i) =
        (⨆ c ∈ s'', ⨅ i ∈ c, U i : Opens M) := by
      rw [inf_iSup₂_eq, Finset.iSup_finset_image]
      simp only [Finset.iInf_union]
    have hsup : (⨅ i ∈ a, U i) ⊔ (⨆ b ∈ s', ⨅ i ∈ b, U i) =
        (⨆ b ∈ s, ⨅ i ∈ b, U i : Opens M) := by
      conv_rhs => rw [← Finset.insert_erase ha, Finset.iSup_insert]
    have hW' := ih _ (Finset.card_erase_lt_of_mem ha) s'
      (fun b hb ↦ hs b (Finset.mem_of_mem_erase hb)) rfl
    have hW'' := ih _ hs'' s'' (by
      simp only [s'', Finset.mem_image]
      rintro _ ⟨b, -, rfl⟩
      exact (hs a ha).mono Finset.subset_union_left) rfl
    rw [← hinf] at hW''
    exact hsup ▸ SmoothCohomologySplitting.exists_isSmooth_sup _ _ hV hW' hW''

/-- **Smooth cohomology splittings from a finite good cover.** A Hausdorff σ-compact manifold,
modelled on a finite-dimensional space, with a finite good cover has a smooth cohomology
splitting. -/
theorem IsFiniteGoodCover.exists_smoothCohomologySplitting_isSmooth {ι : Type*} [Finite ι]
    {U : ι → Opens M} (hU : IsFiniteGoodCover I U) :
    ∃ σ : SmoothCohomologySplitting I M, σ.IsSmooth.{uE, uH, uN} := by
  classical
  have := Fintype.ofFinite ι
  -- The union over the singletons is the whole manifold.
  have htop : (⨆ a ∈ Finset.univ.image ({·} : ι → Finset ι), ⨅ i ∈ a, U i : Opens M) = ⊤ := by
    simpa only [Finset.iSup_finset_image, Finset.iInf_singleton, Finset.mem_univ, iSup_pos] using
      hU.iSup_eq_top
  obtain ⟨σ, hσ⟩ := hU.exists_smoothCohomologySplitting_isSmooth_iSup
    (Finset.univ.image ({·} : ι → Finset ι)) (by simp)
  exact ⟨_, hσ.ofDiffeomorph (Diffeomorph.ofTop _ htop).symm⟩

/-- **Smooth cohomology splittings from a finite good cover.** A Hausdorff σ-compact manifold,
modelled on a finite-dimensional space, that has a finite good cover has a smooth cohomology
splitting. -/
theorem HasFiniteGoodCover.exists_smoothCohomologySplitting_isSmooth
    (hM : HasFiniteGoodCover I M) :
    ∃ σ : SmoothCohomologySplitting I M, σ.IsSmooth.{uE, uH, uN} :=
  let ⟨_, _, hU⟩ := hasFiniteGoodCover_def.mp hM
  hU.exists_smoothCohomologySplitting_isSmooth

/-- **Smooth families of primitives.** On a Hausdorff σ-compact manifold, modelled on a
finite-dimensional space, that has a finite good cover, there is a linear map `P` from the exact
`(k + 1)`-forms to the `k`-forms with `d (P η) = η` for every exact form `η`, which takes smooth
families of exact forms to smooth families of forms over every smooth parameter manifold whose
model space, model and points lie in the universes `uE`, `uH` and `uN` of
`PreservesSmoothFamilies`. The map `P` may depend on these universes.

Milestone: *Smooth families of primitives*. -/
theorem exists_primitiveMap_of_hasFiniteGoodCover (hM : HasFiniteGoodCover I M) (k : ℕ) :
    ∃ P : exactForms I M (k + 1) →ₗ[ℝ] SmoothForm I M ℝ k,
      (∀ η, mextDerivₗ I k (P η) = η) ∧ PreservesSmoothFamilies P :=
  let ⟨σ, hσ⟩ := hM.exists_smoothCohomologySplitting_isSmooth
  ⟨σ.exactPrimitive k, σ.mextDerivₗ_exactPrimitive k, hσ.preservesSmoothFamilies_exactPrimitive k⟩

/-- **Smooth families of primitives, for one family.** On a Hausdorff σ-compact manifold,
modelled on a finite-dimensional space, that has a finite good cover, a smooth family `η` of
exact `(k + 1)`-forms over a smooth parameter manifold `N`, possibly with boundary, has a smooth
family `α` of primitives: `d (α t) = η t` for every `t`. -/
theorem exists_isSmoothFamily_mextDerivₗ_eq (hM : HasFiniteGoodCover I M) {k : ℕ}
    {η : N → SmoothForm I M ℝ (k + 1)} (hη : IsSmoothFamily J η)
    (hex : ∀ t, η t ∈ exactForms I M (k + 1)) :
    ∃ α : N → SmoothForm I M ℝ k, IsSmoothFamily J α ∧ ∀ t, mextDerivₗ I k (α t) = η t := by
  obtain ⟨P, hP, hPs⟩ := exists_primitiveMap_of_hasFiniteGoodCover hM k
  exact ⟨fun t ↦ P ⟨η t, hex t⟩, preservesSmoothFamilies_def.mp hPs _ hη, fun t ↦ hP _⟩

/-- A Hausdorff σ-compact manifold, modelled on a finite-dimensional space, that has a finite
good cover has finite-dimensional de Rham cohomology in every degree. -/
theorem finiteDimensional_deRhamCohomology_of_hasFiniteGoodCover (hM : HasFiniteGoodCover I M)
    (k : ℕ) : FiniteDimensional ℝ (deRhamCohomology I M k) :=
  -- Any universe levels of the parameter manifolds do: only the spaces of the splitting are used.
  let ⟨σ, _⟩ : ∃ σ : SmoothCohomologySplitting I M, σ.IsSmooth.{0, 0, 0} :=
    hM.exists_smoothCohomologySplitting_isSmooth
  σ.finiteDimensional_deRhamCohomology k

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
  let ⟨_, hσ⟩ := hM.exists_smoothCohomologySplitting_isSmooth
  hσ.contMDiff_repr_mk b hz i

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
