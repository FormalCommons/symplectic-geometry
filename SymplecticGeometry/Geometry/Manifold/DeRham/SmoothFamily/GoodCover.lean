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
import SymplecticGeometry.Geometry.Manifold.Instances.Icc
import SymplecticGeometry.Topology.Sets.Opens.Basic

/-!
# Smooth families of primitives on manifolds with a finite good cover

A manifold `M` with a finite good cover `U` has a smooth cohomology splitting
(`SymplecticGeometry.IsFiniteGoodCover.nonempty_smoothCohomologySplitting`). The proof is a
Mayer–Vietoris induction over the cover, after Bott and Tu [BottTu1982]. For a finset `s` of
nonempty finsets of indices, write `V a = ⋂ i ∈ a, U i` and `W s = ⋃ a ∈ s, V a`. By strong
induction on the number of elements of `s`, every `W s` has a splitting:

* `W ∅` is empty, and an empty manifold has the zero splitting
  (`SymplecticGeometry.nonempty_smoothCohomologySplitting_of_isEmpty`);
* for `a ∈ s` with `s = insert a s'`, `W s = V a ∪ W s'`, and `V a ∩ W s' = W s''` with
  `s'' = {a ∪ b | b ∈ s'}`, which has fewer elements than `s`. The set `V a` is empty or smoothly
  contractible, so it has a splitting by
  `SymplecticGeometry.nonempty_smoothCohomologySplitting_of_isSmoothlyContractible`, and the
  Mayer–Vietoris step `SymplecticGeometry.nonempty_smoothCohomologySplitting_sup` gives one on
  `W s`.

The cover by the singletons gives `W = ⊤`, and the splitting is carried to `M` along
`Diffeomorph.ofTop`. From the splitting follow the smooth families of primitives of exact forms,
the finite dimension of de Rham cohomology, and the smoothness of the cohomology classes of a
smooth family of closed forms; with Weil's finite good covers of compact manifolds
(`SymplecticGeometry.hasFiniteGoodCover_of_compactSpace`), de Rham cohomology of a compact
boundaryless manifold is finite-dimensional.

## Main results

* `SymplecticGeometry.IsFiniteGoodCover.nonempty_smoothCohomologySplitting` and
  `SymplecticGeometry.HasFiniteGoodCover.nonempty_smoothCohomologySplitting`: a manifold with a
  finite good cover has a smooth cohomology splitting.
* `SymplecticGeometry.exists_primitiveMap_of_hasFiniteGoodCover`: on such a manifold, a linear
  choice of primitives of exact forms, under which smooth families have smooth primitives.
* `SymplecticGeometry.exists_isSmoothFamily_mextDerivₗ_eq`: a smooth family of exact forms over
  the unit interval has a smooth family of primitives.
* `SymplecticGeometry.exists_isSmoothFamily_mextDerivₗ_eq_Icc`: the same over a closed interval
  `[a, b]`, by reparametrizing along Mathlib's `iccHomeoI`.
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

variable (I M) in
/-- **The splitting of an empty manifold.** On an empty manifold every form is zero, and the
zero spaces with the zero projections and primitives form a smooth cohomology splitting. -/
theorem nonempty_smoothCohomologySplitting_of_isEmpty [IsManifold I ∞ M] [IsEmpty M] :
    Nonempty (SmoothCohomologySplitting I M) :=
  ⟨{ space := fun _ ↦ ⊥
     space_le_closedForms := fun _ ↦ bot_le
     finiteDimensional_space := fun _ ↦ inferInstance
     proj := fun _ ↦ 0
     proj_mem := fun _ _ ↦ Submodule.zero_mem _
     proj_zero := fun _ ↦ Subsingleton.elim _ _
     primitive := fun _ ↦ 0
     mextDerivₗ_primitive := fun _ _ ↦ Subsingleton.elim _ _
     eq_zero_of_mem_exactForms := fun _ _ _ _ ↦ Subsingleton.elim _ _
     preservesSmoothFamilies_proj := fun _ ↦ preservesSmoothFamilies_zero
     preservesSmoothFamilies_primitive := fun _ ↦ preservesSmoothFamilies_zero }⟩

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

/-- **The induction over a good cover.** Let `U` be a finite good cover of `M`. For every finset
`s` of nonempty finsets of indices, the union over `a ∈ s` of the intersections
`⋂ i ∈ a, U i` has a smooth cohomology splitting. -/
theorem IsFiniteGoodCover.nonempty_smoothCohomologySplitting_iSup {ι : Type*} [Finite ι]
    {U : ι → Opens M} (hU : IsFiniteGoodCover I U) (s : Finset (Finset ι))
    (hs : ∀ a ∈ s, a.Nonempty) :
    Nonempty (SmoothCohomologySplitting I (⨆ a ∈ s, ⨅ i ∈ a, U i : Opens M)) := by
  classical
  induction hn : s.card using Nat.strong_induction_on generalizing s with
  | _ n ih =>
    subst hn
    rcases s.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
    · rw [show (⨆ a ∈ (∅ : Finset (Finset ι)), ⨅ i ∈ a, U i : Opens M) = ⊥ by simp]
      exact nonempty_smoothCohomologySplitting_of_isEmpty I _
    -- The member `V a` of the union: empty, or smoothly contractible.
    have hV : Nonempty (SmoothCohomologySplitting I (⨅ i ∈ a, U i : Opens M)) := by
      rcases ((⨅ i ∈ a, U i : Opens M) : Set M).eq_empty_or_nonempty with he | hne
      · rw [Opens.coe_eq_empty.1 he]
        exact nonempty_smoothCohomologySplitting_of_isEmpty I _
      · exact nonempty_smoothCohomologySplitting_of_isSmoothlyContractible I
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
    exact hsup ▸ nonempty_smoothCohomologySplitting_sup _ _ hV hW' hW''

/-- **Smooth cohomology splittings from a finite good cover.** A Hausdorff σ-compact manifold,
modelled on a finite-dimensional space, with a finite good cover has a smooth cohomology
splitting. -/
theorem IsFiniteGoodCover.nonempty_smoothCohomologySplitting {ι : Type*} [Finite ι]
    {U : ι → Opens M} (hU : IsFiniteGoodCover I U) :
    Nonempty (SmoothCohomologySplitting I M) := by
  classical
  have := Fintype.ofFinite ι
  -- The union over the singletons is the whole manifold.
  have htop : (⨆ a ∈ Finset.univ.image ({·} : ι → Finset ι), ⨅ i ∈ a, U i : Opens M) = ⊤ := by
    simpa only [Finset.iSup_finset_image, Finset.iInf_singleton, Finset.mem_univ, iSup_pos] using
      hU.iSup_eq_top
  obtain ⟨σ⟩ := hU.nonempty_smoothCohomologySplitting_iSup (Finset.univ.image ({·} : ι → Finset ι))
    (by simp)
  exact ⟨σ.ofDiffeomorph (Diffeomorph.ofTop _ htop).symm⟩

/-- **Smooth cohomology splittings from a finite good cover.** A Hausdorff σ-compact manifold,
modelled on a finite-dimensional space, that has a finite good cover has a smooth cohomology
splitting. -/
theorem HasFiniteGoodCover.nonempty_smoothCohomologySplitting (hM : HasFiniteGoodCover I M) :
    Nonempty (SmoothCohomologySplitting I M) :=
  let ⟨_, _, hU⟩ := hasFiniteGoodCover_def.mp hM
  hU.nonempty_smoothCohomologySplitting

/-- **Smooth families of primitives.** On a Hausdorff σ-compact manifold, modelled on a
finite-dimensional space, that has a finite good cover, there is a linear map `P` from the exact
`(k + 1)`-forms to the `k`-forms with `d (P η) = η` for every exact form `η`, which takes smooth
families of exact forms over the unit interval to smooth families of forms.

Milestone: *Smooth families of primitives*. -/
theorem exists_primitiveMap_of_hasFiniteGoodCover (hM : HasFiniteGoodCover I M) (k : ℕ) :
    ∃ P : exactForms I M (k + 1) →ₗ[ℝ] SmoothForm I M ℝ k,
      (∀ η, mextDerivₗ I k (P η) = η) ∧ PreservesSmoothFamilies P :=
  let σ := hM.nonempty_smoothCohomologySplitting.some
  ⟨σ.exactPrimitive k, σ.mextDerivₗ_exactPrimitive k, σ.preservesSmoothFamilies_exactPrimitive k⟩

/-- **Smooth families of primitives, for one family.** On a Hausdorff σ-compact manifold,
modelled on a finite-dimensional space, that has a finite good cover, a smooth family `η` of
exact `(k + 1)`-forms over the unit interval has a smooth family `α` of primitives:
`d (α t) = η t` for every `t`. -/
theorem exists_isSmoothFamily_mextDerivₗ_eq (hM : HasFiniteGoodCover I M) {k : ℕ}
    {η : unitInterval → SmoothForm I M ℝ (k + 1)} (hη : IsSmoothFamily (𝓡∂ 1) η)
    (hex : ∀ t, η t ∈ exactForms I M (k + 1)) :
    ∃ α : unitInterval → SmoothForm I M ℝ k, IsSmoothFamily (𝓡∂ 1) α ∧
      ∀ t, mextDerivₗ I k (α t) = η t := by
  obtain ⟨P, hP, hPs⟩ := exists_primitiveMap_of_hasFiniteGoodCover hM k
  exact ⟨fun t ↦ P ⟨η t, hex t⟩, preservesSmoothFamilies_def.mp hPs _ hη, fun t ↦ hP _⟩

/-- **Smooth families of primitives over a closed interval.** On a Hausdorff σ-compact manifold,
modelled on a finite-dimensional space, that has a finite good cover, a smooth family `η` of
exact `(k + 1)`-forms over a closed interval `[a, b]`, `a < b`, has a smooth family `α` of
primitives: `d (α t) = η t` for every `t`. -/
theorem exists_isSmoothFamily_mextDerivₗ_eq_Icc (hM : HasFiniteGoodCover I M) {k : ℕ}
    {a b : ℝ} [hab : Fact (a < b)] {η : Set.Icc a b → SmoothForm I M ℝ (k + 1)}
    (hη : IsSmoothFamily (𝓡∂ 1) η) (hex : ∀ t, η t ∈ exactForms I M (k + 1)) :
    ∃ α : Set.Icc a b → SmoothForm I M ℝ k, IsSmoothFamily (𝓡∂ 1) α ∧
      ∀ t, mextDerivₗ I k (α t) = η t := by
  -- Reparametrize by the affine homeomorphism `e : [a, b] ≃ₜ [0, 1]`, which is smooth both ways.
  let e := iccHomeoI a b hab.out
  obtain ⟨α, hα, hdα⟩ := exists_isSmoothFamily_mextDerivₗ_eq hM
    (hη.comp e.symm (contMDiff_iccHomeoI_symm hab.out)) fun u ↦ hex (e.symm u)
  exact ⟨fun t ↦ α (e t), hα.comp e (contMDiff_iccHomeoI hab.out), fun t ↦
    (hdα (e t)).trans (congrArg η (e.symm_apply_apply t))⟩

/-- A Hausdorff σ-compact manifold, modelled on a finite-dimensional space, that has a finite
good cover has finite-dimensional de Rham cohomology in every degree. -/
theorem finiteDimensional_deRhamCohomology_of_hasFiniteGoodCover (hM : HasFiniteGoodCover I M)
    (k : ℕ) : FiniteDimensional ℝ (deRhamCohomology I M k) :=
  hM.nonempty_smoothCohomologySplitting.some.finiteDimensional_deRhamCohomology k

/-- **The classes of a smooth family of closed forms depend smoothly on the parameter.** On a
Hausdorff σ-compact manifold, modelled on a finite-dimensional space, that has a finite good
cover, let `b` be a basis of the de Rham cohomology in degree `k` and `z` a smooth family of
closed `k`-forms over the unit interval. Then each coordinate `t ↦ b.repr [z t] i` is a smooth
function. -/
theorem contMDiff_repr_mk_of_hasFiniteGoodCover (hM : HasFiniteGoodCover I M) {k : ℕ}
    {ι : Type*} (b : Module.Basis ι ℝ (deRhamCohomology I M k))
    {z : unitInterval → closedForms I M k}
    (hz : IsSmoothFamily (𝓡∂ 1) (fun t ↦ (z t : SmoothForm I M ℝ k))) (i : ι) :
    ContMDiff (𝓡∂ 1) 𝓘(ℝ) ∞ (fun t ↦ b.repr (deRhamCohomology.mk I k (z t)) i) :=
  hM.nonempty_smoothCohomologySplitting.some.contMDiff_repr_mk b hz i

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
