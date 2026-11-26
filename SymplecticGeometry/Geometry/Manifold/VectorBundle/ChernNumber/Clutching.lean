/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.DiscComplement.Basic
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.ChernNumber.Basic
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Hermitian.UnitFrame
public import TauCeti.Topology.VectorBundle.Complex.Clutching
public import TauCeti.Analysis.Matrix.SymplecticGroup.Maslov
public import TauCeti.Topology.VectorBundle.Orientation.SectionIndex
import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.ArgumentPrinciple
import SymplecticGeometry.Analysis.Matrix.SymplecticGroup.Maslov
import SymplecticGeometry.Geometry.Manifold.VectorBundle.Symplectic.ComplexStructure.UnitaryFrame
import SymplecticGeometry.Topology.VectorBundle.Complex.FirstChernClass
import SymplecticGeometry.Topology.VectorBundle.Complex.Structure
import SymplecticGeometry.Topology.VectorBundle.DetBundle.Frame
import SymplecticGeometry.Topology.VectorBundle.Orientation.SectionIndex.Radial
import SymplecticGeometry.Topology.VectorBundle.Complex.RestrictScalars
import SymplecticGeometry.Analysis.Normed.Module.Ball.Radial.Cone

/-!
# The disc clutching formula for the first Chern number

Let `φ i`, for `i` in a finite type `ι`, be coordinate discs of a surface `M` with a homological
orientation, whose closed discs are pairwise disjoint, and let `E` be a complex vector bundle over
`M` with model `G`. Suppose given a frame `Φ i` of `E` over the closed disc of `φ i` and a frame
`Φout` of `E` over the complement `discComplement φ` of the open discs, in the sense of Tau Ceti's
`Topology/VectorBundle/Complex/Clutching.lean`: continuous families of isomorphisms
`G ≃L[ℂ] E x`. On the boundary circle of the `i`-th disc they differ by the automorphism
`clutchingTransition hφ Φ Φout i ζ = (Φ i)⁻¹ ∘ Φout` of `G`.

This file builds from these frames a section of the determinant line `Λ^top E`
(Tau Ceti's `TauCeti.DetBundle ℂ G E`) that the disc clutching formula sums over:

* on the complement of the open discs, the determinant `TauCeti.DetBundle.ofFrame` of `Φout`;
* at `φ i z` with `‖z‖ < 1`, the determinant section of `Φ i` times `sphereCone uᵢ z`, for
  `uᵢ ζ = det (clutchingTransition hφ Φ Φout i ζ)` and `sphereCone` Tau Ceti's radial extension
  `r ζ ↦ r uᵢ(ζ)` of a function on the circle (read on `Circle` through
  `Circle.homeomorphSphere`).

The main result, `exists_detBundle_section_clutching`, says that this section is continuous on
total spaces, that its zeros are exactly the centres `φ i 0`, and that its local index at `φ i 0`,
for the orientation of the determinant line as a complex line, is the degree of the loop of
normalized determinants `ContinuousLinearEquiv.normalizedDet` of the transition around the `i`-th
circle.

The disc clutching formula, `chernNumber_eq_sum_degree_clutching`, follows when `M` is compact:
the first Chern number of `E` is the sum over `i` of these degrees. The first Chern class is the
Euler class of the determinant line (`firstChernClass_eq_complexEulerClass_detBundle`), and Tau
Ceti evaluates it on the fundamental class as the sum of the local indices of the section at its
zeros (`TauCeti.VectorBundleOrientation.evalFundamentalClass_eulerClass_eq_sum_sectionIndex`), as
in `chernNumber_eq_sum_sectionIndex` for line bundles; the zeros are indexed by `ι`, since distinct
discs have distinct centres. One disc is the case `ι = Unit`.

For a Hermitian line bundle, sections of its circle bundle of unitary frames give frames
`SymplecticGeometry.Bundle.unitFrame` (`Geometry/Manifold/VectorBundle/Hermitian/UnitFrame.lean`).
The clutching transition of two such frames on the `i`-th circle is multiplication by the
`Circle`-valued quotient `TauCeti.PrincipalBundle.division` of the two sections, and so is its
normalized determinant (`clutchingTransition_unitFrame_apply`,
`normalizedDet_clutchingTransition_unitFrame`).

For a symplectic vector bundle `(V, ω)` over a closed surface the formula reads, as in McDuff and
Salamon, Theorem 2.7.1: if `Φ i` and `Φout` are symplectic frames, families of linear
isomorphisms `StdSpace κ ≃ V x`, for a finite type `κ`, that carry the standard form `stdForm κ`
to `ω`, and `Ψ i` is the loop of symplectic matrices with `Φout = Φ i ∘ Ψ i` on the `i`-th circle,
then the first Chern number `symplecticChernNumber` of `(V, ω)` is the sum of the Maslov indices
`TauCeti.GLSymplectic.maslovIndex` of the loops `Ψ i`
(`symplecticChernNumber_eq_sum_maslovIndex_clutching`).

## Proof

The two descriptions agree on the boundary circles: there the section of `Φout` is that of `Φ i`
times the determinant of the transition (`TauCeti.DetBundle.ofFrame_eq_det_smul`), and the
radial extension of `uᵢ` equals `uᵢ` on the unit circle. So the section is continuous on each
closed disc and on the complement of the open discs, a finite closed cover of `M`
(`LocallyFinite.continuous`). The determinant of an isomorphism and the determinant of a frame
vanish nowhere (`TauCeti.DetBundle.ofFrame_ne_zero`), and the radial extension of a function
without zeros vanishes only at the centre (`TauCeti.sphereCone_eq_zero_iff`). The local index is
`SymplecticGeometry.CoordinateDisc.sectionIndex_eq_degree_sphereCone`.

For symplectic frames, the frames show that `ω` is nondegenerate, so it is compatible with a
complex structure `J`
(`SymplecticGeometry.Bundle.exists_compatible_symplecticChernNumber_eq_chernNumber`). Continuous
changes of frame `P i` on the discs and `P'` on the complement, with values in the symplectic
group, make the frames unitary for `J`, and read on `κ → ℂ` through
`TauCeti.complexToRealEuclidean` they become complex frames of `(V, J)`
(`ContMDiffTwoForm.Compatible.exists_continuous_GLSymplectic_complexFrame`, in the namespace
`SymplecticGeometry.Bundle`).
Their transitions are the loops `(P i)⁻¹ Ψ i P'`, which act complex-linearly on `κ → ℂ`, so that
`ρ` of them is their normalized complex determinant
(`TauCeti.Bundle.ContinuousComplexStructure.maslovPhase_inv_mul_mul_eq_normalizedDet`), and the
complex formula gives the sum of their Maslov indices. By the product axiom
(`TauCeti.GLSymplectic.maslovIndex_toBasedLoop_mul`) each is the sum of the indices of the loops
of `(P i)⁻¹`, of `Ψ i` and of `P'`. The loop of `(P i)⁻¹` contracts radially in the disc, so
its index is `0` (`SymplecticGeometry.CoordinateDisc.discContraction`), and the indices of the
loops of `P'` add up to `0` by the argument principle
`SymplecticGeometry.sum_degree_boundary_eq_zero`, applied to the Maslov phase `ρ ∘ P'` on the
complement of the open discs.

## Main definitions and results

* `SymplecticGeometry.Bundle.clutchingTransition`: the transition `(Φ i)⁻¹ ∘ Φout` on the
  `i`-th boundary circle.
* `SymplecticGeometry.Bundle.continuous_normalizedDet_clutchingTransition`: its normalized
  determinant is a continuous loop on the circle.
* `SymplecticGeometry.Bundle.exists_detBundle_section_clutching`: the section described above,
  its continuity, its zeros and its local indices.
* `SymplecticGeometry.Bundle.chernNumber_eq_sum_degree_clutching`: the first Chern number is the
  sum of the degrees of the normalized determinants of the clutching transitions.
* `SymplecticGeometry.Bundle.symplecticChernNumber_eq_sum_maslovIndex_clutching`: for symplectic
  frames, the first Chern number of a symplectic bundle adds up the Maslov indices of the
  transition loops.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.7,
  where the first Chern number of a bundle over a surface is computed from trivializations over
  discs and over their complement (Theorem 2.7.1 for symplectic trivializations and the Maslov
  index).
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §§11 and 14 (indices of sections at isolated zeros, and the first Chern class
  through the determinant line).
-/

public section

noncomputable section

open Bundle Function Module Set TauCeti

namespace SymplecticGeometry

namespace Bundle

section Clutching

variable {M : Type} [TopologicalSpace M] [T2Space M] {EM : Type} [NormedAddCommGroup EM]
  [NormedSpace ℝ EM] [FiniteDimensional ℝ EM] [ChartedSpace EM M]
  {o : HomologicalOrientation M EM 2} {ι : Type*} {φ : ι → CoordinateDisc o}
  (hφ : Pairwise (Disjoint on fun i ↦ (φ i).disc))
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
  {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)] [∀ x, TopologicalSpace (E x)]

variable (Φ : ∀ i, ∀ x : (φ i).disc, G ≃L[ℂ] E x) (Φout : ∀ x : discComplement φ, G ≃L[ℂ] E x)

/-- The **clutching transition** on the `i`-th boundary circle: for a frame `Φ i` of `E` over the
closed disc of `φ i` and a frame `Φout` over the complement of the open discs, the automorphism
`(Φ i)⁻¹ ∘ Φout` of the model `G` at the point `(φ i).boundaryCircle ζ`. -/
def clutchingTransition (i : ι) (ζ : Circle) : G ≃L[ℂ] G :=
  (Φout ⟨(φ i).boundaryCircle ζ, boundaryCircle_mem_discComplement φ hφ i ζ⟩).trans
    (Φ i ⟨(φ i).boundaryCircle ζ, (φ i).boundaryCircle_mem_disc ζ⟩).symm

theorem clutchingTransition_def (i : ι) (ζ : Circle) :
    clutchingTransition hφ Φ Φout i ζ =
      (Φout ⟨(φ i).boundaryCircle ζ, boundaryCircle_mem_discComplement φ hφ i ζ⟩).trans
        (Φ i ⟨(φ i).boundaryCircle ζ, (φ i).boundaryCircle_mem_disc ζ⟩).symm :=
  (rfl)

variable [FiniteDimensional ℂ G] [TopologicalSpace (TotalSpace G E)] [FiberBundle G E]
  [VectorBundle ℂ G E] {Φ Φout}
  (hΦ : ∀ i, Continuous fun q : (φ i).disc × G ↦ TotalSpace.mk' G (q.1 : M) (Φ i q.1 q.2))
  (hΦout : Continuous fun q : discComplement φ × G ↦ TotalSpace.mk' G (q.1 : M) (Φout q.1 q.2))

omit [FiniteDimensional ℂ G] [FiberBundle G E] [VectorBundle ℂ G E] in
include hΦ in
/-- The frame `Φ i` restricted to the `i`-th boundary circle is a frame along
`(φ i).boundaryCircle`. -/
private theorem continuous_discFrame_boundaryCircle (i : ι) :
    Continuous fun q : Circle × G ↦ TotalSpace.mk' G ((φ i).boundaryCircle q.1)
      (Φ i ⟨(φ i).boundaryCircle q.1, (φ i).boundaryCircle_mem_disc q.1⟩ q.2) :=
  (hΦ i).comp ((((φ i).boundaryCircle.continuous.comp continuous_fst).subtype_mk _).prodMk
    continuous_snd)

omit [FiniteDimensional ℂ G] [FiberBundle G E] [VectorBundle ℂ G E] in
include hΦout in
/-- The frame `Φout` restricted to the `i`-th boundary circle is a frame along
`(φ i).boundaryCircle`. -/
private theorem continuous_outFrame_boundaryCircle (i : ι) :
    Continuous fun q : Circle × G ↦ TotalSpace.mk' G ((φ i).boundaryCircle q.1)
      (Φout ⟨(φ i).boundaryCircle q.1, boundaryCircle_mem_discComplement φ hφ i q.1⟩ q.2) :=
  hΦout.comp ((((φ i).boundaryCircle.continuous.comp continuous_fst).subtype_mk _).prodMk
    continuous_snd)

include hΦ hΦout in
/-- The determinant of the clutching transition depends continuously on the point of the
circle. -/
theorem continuous_det_clutchingTransition (i : ι) :
    Continuous fun ζ ↦
      LinearMap.det ((clutchingTransition hφ Φ Φout i ζ).toLinearEquiv : G →ₗ[ℂ] G) :=
  ContinuousLinearMap.continuous_det.comp (TauCeti.continuous_trans_symm_of_continuous_frame
    (continuous_outFrame_boundaryCircle hφ hΦout i) (continuous_discFrame_boundaryCircle hΦ i))

include hΦ hΦout in
/-- The normalized determinant of the clutching transition is a continuous loop on the circle. -/
theorem continuous_normalizedDet_clutchingTransition (i : ι) :
    Continuous fun ζ ↦ (clutchingTransition hφ Φ Φout i ζ).normalizedDet :=
  continuous_normalizedDet_trans_symm (f := (φ i).boundaryCircle)
    (continuous_discFrame_boundaryCircle hΦ i) (continuous_outFrame_boundaryCircle hφ hΦout i)

/-! ### The clutching section -/

/-- The determinant of the clutching transition, as a continuous function on the circle. -/
private def clutchingDet (i : ι) : C(Circle, ℂ) :=
  ⟨fun ζ ↦ LinearMap.det ((clutchingTransition hφ Φ Φout i ζ).toLinearEquiv : G →ₗ[ℂ] G),
    continuous_det_clutchingTransition hφ hΦ hΦout i⟩

private theorem clutchingDet_apply (i : ι) (ζ : Circle) :
    clutchingDet hφ hΦ hΦout i ζ =
      LinearMap.det ((clutchingTransition hφ Φ Φout i ζ).toLinearEquiv : G →ₗ[ℂ] G) :=
  (rfl)

private theorem clutchingDet_ne_zero (i : ι) (ζ : Circle) : clutchingDet hφ hΦ hΦout i ζ ≠ 0 :=
  (clutchingTransition hφ Φ Φout i ζ).toLinearEquiv.isUnit_det'.ne_zero

/-- The radial extension of `clutchingDet` into the `i`-th disc, as a function on `M` (zero off the
chart). -/
private def radialCoeff (i : ι) : M → ℂ :=
  extend (φ i)
    (fun z ↦ sphereCone (clutchingDet hφ hΦ hΦout i ∘ Circle.homeomorphSphere.symm) (z : ℂ)) 0

private theorem radialCoeff_apply (i : ι) (z : CoordinateDisc.ball) :
    radialCoeff hφ hΦ hΦout i (φ i z) =
      sphereCone (clutchingDet hφ hΦ hΦout i ∘ Circle.homeomorphSphere.symm) (z : ℂ) :=
  (φ i).injective.extend_apply _ _ z

private theorem radialCoeff_boundaryCircle (i : ι) (ζ : Circle) :
    radialCoeff hφ hΦ hΦout i ((φ i).boundaryCircle ζ) = clutchingDet hφ hΦ hΦout i ζ := by
  rw [CoordinateDisc.boundaryCircle_apply, radialCoeff_apply,
    sphereCone_comp_homeomorphSphere_symm_coe]

private theorem continuousAt_radialCoeff (i : ι) (z : CoordinateDisc.ball) :
    ContinuousAt (radialCoeff hφ hΦ hΦout i) (φ i z) := by
  rw [← (φ i).isOpenEmbedding.continuousAt_iff, radialCoeff, extend_comp (φ i).injective]
  exact ((continuous_sphereCone_comp_homeomorphSphere_symm
    (clutchingDet hφ hΦ hΦout i).continuous).comp continuous_subtypeVal).continuousAt

/-- The determinant section of the frame `Φ i` over the `i`-th closed disc. -/
private def discSection (Φ : ∀ i, ∀ x : (φ i).disc, G ≃L[ℂ] E x) (i : ι) (y : (φ i).disc) :
    DetBundle ℂ G E y :=
  DetBundle.ofFrame (Φ i y : G ≃ₗ[ℂ] E y)

/-- The determinant section of the frame `Φout` over the complement of the open discs. -/
private def outSection (Φout : ∀ x : discComplement φ, G ≃L[ℂ] E x) (y : discComplement φ) :
    DetBundle ℂ G E y :=
  DetBundle.ofFrame (Φout y : G ≃ₗ[ℂ] E y)

omit [TopologicalSpace (TotalSpace G E)] [FiberBundle G E] [VectorBundle ℂ G E] in
private theorem discSection_ne_zero (i : ι) (y : (φ i).disc) : discSection Φ i y ≠ 0 :=
  DetBundle.ofFrame_ne_zero _

omit [TopologicalSpace (TotalSpace G E)] [FiberBundle G E] [VectorBundle ℂ G E] in
private theorem outSection_ne_zero (y : discComplement φ) : outSection Φout y ≠ 0 :=
  DetBundle.ofFrame_ne_zero _

include hΦ in
private theorem continuous_discSection (i : ι) :
    Continuous fun y : (φ i).disc ↦
      TotalSpace.mk' ℂ (E := DetBundle ℂ G E) (y : M) (discSection Φ i y) :=
  DetBundle.continuous_totalSpaceMk_ofFrame (hΦ i)

include hΦout in
private theorem continuous_outSection :
    Continuous fun y : discComplement φ ↦
      TotalSpace.mk' ℂ (E := DetBundle ℂ G E) (y : M) (outSection Φout y) :=
  DetBundle.continuous_totalSpaceMk_ofFrame hΦout

/-- On the boundary circle of the `i`-th disc, the determinant section of `Φout` is that of
`Φ i` times the determinant of the clutching transition. -/
private theorem outSection_boundaryCircle (i : ι) (ζ : Circle) :
    outSection Φout ⟨(φ i).boundaryCircle ζ, boundaryCircle_mem_discComplement φ hφ i ζ⟩ =
      clutchingDet hφ hΦ hΦout i ζ •
        discSection Φ i ⟨(φ i).boundaryCircle ζ, (φ i).boundaryCircle_mem_disc ζ⟩ := by
  rw [outSection, discSection, clutchingDet_apply, clutchingTransition_def]
  exact DetBundle.ofFrame_eq_det_smul _ _

open Classical in
/-- The clutching section: the radial extension of `clutchingDet` times the determinant section of
`Φ i` on the `i`-th open disc, and the determinant section of `Φout` elsewhere. -/
private def clutchingSection (x : M) : DetBundle ℂ G E x :=
  if h : ∃ i, x ∈ (φ i).openDisc then
    radialCoeff hφ hΦ hΦout h.choose x •
      discSection Φ h.choose ⟨x, (φ _).openDisc_subset_disc h.choose_spec⟩
  else outSection Φout ⟨x, (mem_discComplement_iff φ).2 fun i hi ↦ h ⟨i, hi⟩⟩

private theorem clutchingSection_of_mem_discComplement {x : M} (hx : x ∈ discComplement φ) :
    clutchingSection hφ hΦ hΦout x = outSection Φout ⟨x, hx⟩ := by
  rw [clutchingSection, dite_eq_right fun ⟨i, hi⟩ ↦ (mem_discComplement_iff φ).1 hx i hi]

private theorem clutchingSection_of_mem_openDisc {i : ι} {x : M} (hx : x ∈ (φ i).openDisc) :
    clutchingSection hφ hΦ hΦout x = radialCoeff hφ hΦ hΦout i x •
      discSection Φ i ⟨x, (φ i).openDisc_subset_disc hx⟩ := by
  have key : ∀ j (hj : x ∈ (φ j).openDisc), radialCoeff hφ hΦ hΦout j x •
      discSection Φ j ⟨x, (φ j).openDisc_subset_disc hj⟩ = radialCoeff hφ hΦ hΦout i x •
      discSection Φ i ⟨x, (φ i).openDisc_subset_disc hx⟩ := by
    intro j hj
    obtain rfl := eq_of_mem_openDisc_of_mem_disc φ hφ hj ((φ i).openDisc_subset_disc hx)
    rfl
  rw [clutchingSection, dite_eq_left ⟨i, hx⟩]
  exact key _ (Exists.choose_spec (⟨i, hx⟩ : ∃ j, x ∈ (φ j).openDisc))

/-- On the whole closed `i`-th disc, the clutching section is the radial extension of
`clutchingDet` times the determinant section of `Φ i`. -/
private theorem clutchingSection_of_mem_disc {i : ι} {x : M} (hx : x ∈ (φ i).disc) :
    clutchingSection hφ hΦ hΦout x = radialCoeff hφ hΦ hΦout i x • discSection Φ i ⟨x, hx⟩ := by
  by_cases ho : x ∈ (φ i).openDisc
  · exact clutchingSection_of_mem_openDisc hφ hΦ hΦout ho
  obtain ⟨ζ, rfl⟩ : x ∈ range (φ i).boundaryCircle := (φ i).disc_diff_openDisc ▸ ⟨hx, ho⟩
  rw [clutchingSection_of_mem_discComplement hφ hΦ hΦout
      (boundaryCircle_mem_discComplement φ hφ i ζ), outSection_boundaryCircle,
    radialCoeff_boundaryCircle]

/-- The clutching section is continuous on total spaces. -/
private theorem continuous_clutchingSection [Finite ι] :
    Continuous fun x ↦
      TotalSpace.mk' ℂ (E := DetBundle ℂ G E) x (clutchingSection hφ hΦ hΦout x) := by
  refine LocallyFinite.continuous (f := fun j : Option ι ↦ j.elim (discComplement φ)
    fun i ↦ (φ i).disc) (locallyFinite_of_finite _) ?_ ?_ ?_
  · refine eq_univ_of_forall fun x ↦ ?_
    by_cases hx : x ∈ discComplement φ
    · exact mem_iUnion.2 ⟨none, hx⟩
    · obtain ⟨i, hi⟩ : ∃ i, x ∈ (φ i).openDisc := by simpa using hx
      exact mem_iUnion.2 ⟨some i, (φ i).openDisc_subset_disc hi⟩
  · rintro (_ | i)
    · exact isClosed_discComplement φ
    · exact (φ i).isCompact_disc.isClosed
  · rintro (_ | i)
    · refine continuousOn_iff_continuous_domRestrict.2 ?_
      refine (continuous_outSection hΦout).congr fun y ↦ ?_
      simp only [domRestrict, clutchingSection_of_mem_discComplement hφ hΦ hΦout y.property]
    · refine continuousOn_iff_continuous_domRestrict.2 ?_
      have hc : Continuous fun y : (φ i).disc ↦ radialCoeff hφ hΦ hΦout i y := by
        refine continuous_iff_continuousAt.2 fun y ↦ ?_
        obtain ⟨z, -, hz⟩ := (φ i).mem_disc_iff.1 y.property
        exact (hz ▸ continuousAt_radialCoeff hφ hΦ hΦout i z).comp
          continuous_subtypeVal.continuousAt
      refine (hc.smul_totalSpace (continuous_discSection hΦ i)).congr fun y ↦ ?_
      simp only [domRestrict, clutchingSection_of_mem_disc hφ hΦ hΦout y.property]

/-- The zeros of the clutching section are the centres of the discs. -/
private theorem clutchingSection_eq_zero_iff {x : M} :
    clutchingSection hφ hΦ hΦout x = 0 ↔ ∃ i, φ i 0 = x := by
  by_cases hx : x ∈ discComplement φ
  · rw [clutchingSection_of_mem_discComplement hφ hΦ hΦout hx]
    refine iff_of_false (outSection_ne_zero (Φout := Φout) _) ?_
    rintro ⟨i, rfl⟩
    exact (mem_discComplement_iff φ).1 hx i (φ i).apply_zero_mem_openDisc
  obtain ⟨i, hi⟩ : ∃ i, x ∈ (φ i).openDisc := by simpa using hx
  obtain ⟨z, -, rfl⟩ := (φ i).mem_openDisc_iff.1 hi
  rw [clutchingSection_of_mem_openDisc hφ hΦ hΦout hi, smul_eq_zero,
    or_iff_left (discSection_ne_zero (Φ := Φ) i _), radialCoeff_apply,
    sphereCone_eq_zero_iff (f := clutchingDet hφ hΦ hΦout i ∘ Circle.homeomorphSphere.symm)
      fun _ ↦ clutchingDet_ne_zero hφ hΦ hΦout i _]
  constructor
  · intro hz
    exact ⟨i, congrArg (φ i) (Subtype.ext (CoordinateDisc.coe_zero.trans hz.symm))⟩
  · rintro ⟨j, hj⟩
    obtain rfl := eq_of_mem_openDisc_of_mem_disc φ hφ (φ j).apply_zero_mem_openDisc
      (hj ▸ (φ i).openDisc_subset_disc hi)
    rw [← (φ j).injective hj, CoordinateDisc.coe_zero]

end Clutching

section ClutchingIndex

/-! Tau Ceti's Euler classes and section indices take the fibres in the universe of the base, so
from here on the fibres of `E` are in `Type`. -/

variable {M : Type} [TopologicalSpace M] [T2Space M] {EM : Type} [NormedAddCommGroup EM]
  [NormedSpace ℝ EM] [FiniteDimensional ℝ EM] [ChartedSpace EM M]
  {o : HomologicalOrientation M EM 2} {ι : Type*} {φ : ι → CoordinateDisc o}
  (hφ : Pairwise (Disjoint on fun i ↦ (φ i).disc))
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
  {E : M → Type} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)] [∀ x, TopologicalSpace (E x)]
  {Φ : ∀ i, ∀ x : (φ i).disc, G ≃L[ℂ] E x} {Φout : ∀ x : discComplement φ, G ≃L[ℂ] E x}
  [FiniteDimensional ℂ G] [TopologicalSpace (TotalSpace G E)] [FiberBundle G E]
  [VectorBundle ℂ G E]
  (hΦ : ∀ i, Continuous fun q : (φ i).disc × G ↦ TotalSpace.mk' G (q.1 : M) (Φ i q.1 q.2))
  (hΦout : Continuous fun q : discComplement φ × G ↦ TotalSpace.mk' G (q.1 : M) (Φout q.1 q.2))

open scoped VectorBundle.ComplexToReal

/-- The local index of the clutching section at the centre of the `i`-th disc is the degree of
the loop of normalized determinants of the clutching transition. -/
private theorem sectionIndex_clutchingSection (hn : finrank ℝ EM = 2) (i : ι)
    (hs : Continuous fun x ↦
      TotalSpace.mk' ℂ (E := DetBundle ℂ G E) x (clutchingSection hφ hΦ hΦout x)) :
    (VectorBundleOrientation.reindex (finCongr (by simp))
        (VectorBundleOrientation.complex ℂ (DetBundle ℂ G E))).sectionIndex
        (by simp [finrank_real_eq_two_mul_finrank_complex]) o hs (φ i 0) =
      Circle.degree (ContinuousMap.mk _
        (continuous_normalizedDet_clutchingTransition hφ hΦ hΦout i)).toBasedLoop := by
  classical
  -- The frame of the determinant line given by `Φ i`, read along the chart.
  let σ : ∀ z : CoordinateDisc.ball, DetBundle ℂ G E (φ i z) := fun z ↦
    if h : φ i z ∈ (φ i).disc then discSection Φ i ⟨φ i z, h⟩ else 0
  have hσe : ∀ (z : CoordinateDisc.ball) (hz : ‖(z : ℂ)‖ ≤ 1),
      σ z = discSection Φ i ⟨φ i z, (φ i).apply_mem_disc_iff.2 hz⟩ := fun z hz ↦
    dite_eq_left ((φ i).apply_mem_disc_iff.2 hz)
  have hσ : ContinuousOn (fun z ↦ TotalSpace.mk' ℂ (E := DetBundle ℂ G E) (φ i z) (σ z))
      {z | ‖(z : ℂ)‖ < 1} := by
    refine ContinuousOn.mono (s := {z : CoordinateDisc.ball | ‖(z : ℂ)‖ ≤ 1}) ?_
      fun (z : CoordinateDisc.ball) (hz : ‖(z : ℂ)‖ < 1) ↦ (hz.le : ‖(z : ℂ)‖ ≤ 1)
    refine continuousOn_iff_continuous_domRestrict.2 ?_
    refine ((continuous_discSection hΦ i).comp (((φ i).continuous.comp
      continuous_subtypeVal).subtype_mk fun z ↦ (φ i).apply_mem_disc_iff.2 z.property)).congr
        fun z ↦ ?_
    simp only [domRestrict, Function.comp_apply, hσe z z.property]
  have hσ0 : ∀ z : CoordinateDisc.ball, ‖(z : ℂ)‖ < 1 → σ z ≠ 0 := fun z hz ↦ by
    rw [hσe z hz.le]
    exact discSection_ne_zero (Φ := Φ) i _
  have hsσ : ∀ z : CoordinateDisc.ball, ‖(z : ℂ)‖ < 1 → clutchingSection hφ hΦ hΦout (φ i z) =
      sphereCone (clutchingDet hφ hΦ hΦout i ∘ Circle.homeomorphSphere.symm) z • σ z :=
    fun z hz ↦ by
      rw [clutchingSection_of_mem_openDisc hφ hΦ hΦout ((φ i).apply_mem_openDisc_iff.2 hz),
        radialCoeff_apply, hσe z hz.le]
  rw [CoordinateDisc.sectionIndex_eq_degree_sphereCone hn (by simp) (φ i) hσ hσ0
    (clutchingDet_ne_zero hφ hΦ hΦout i) hs hsσ]
  refine congrArg (fun u : C(Circle, Circle) ↦ Circle.degree u.toBasedLoop) ?_
  ext ζ
  rw [ContinuousMap.coe_normalizeToCircle_apply, clutchingDet_apply]
  exact (ContinuousLinearEquiv.coe_normalizedDet _).symm

/-- **The clutching section of the determinant line.** Let `φ i`, for `i` in a finite type, be
coordinate discs of a surface `M` with a homological orientation `o`, with pairwise disjoint closed
discs, and let `E` be a complex vector bundle over `M` with a frame `Φ i` over each closed disc and
a frame `Φout` over the complement of the open discs. Then the determinant line `Λ^top E` has a
section `s`, continuous on total spaces, whose zeros are exactly the centres `φ i 0`, and whose
local index at `φ i 0`, for the orientation of `Λ^top E` as a complex line, is the degree of the
loop `ζ ↦ normalizedDet ((Φ i)⁻¹ ∘ Φout)` around the `i`-th boundary circle.

The section is the determinant section of `Φout` on the complement of the open discs, and the
determinant section of `Φ i` times the radial extension of `det ((Φ i)⁻¹ ∘ Φout)` on the `i`-th
open disc. -/
theorem exists_detBundle_section_clutching [Finite ι] (hn : finrank ℝ EM = 2) :
    ∃ (s : ∀ x, DetBundle ℂ G E x)
      (hs : Continuous fun x ↦ TotalSpace.mk' ℂ (E := DetBundle ℂ G E) x (s x)),
      {x | s x = 0} = range (fun i ↦ φ i 0) ∧
      ∀ i, (VectorBundleOrientation.reindex (finCongr (by simp))
          (VectorBundleOrientation.complex ℂ (DetBundle ℂ G E))).sectionIndex
          (by simp [finrank_real_eq_two_mul_finrank_complex]) o hs (φ i 0) =
        Circle.degree (ContinuousMap.mk _
          (continuous_normalizedDet_clutchingTransition hφ hΦ hΦout i)).toBasedLoop :=
  ⟨clutchingSection hφ hΦ hΦout, continuous_clutchingSection hφ hΦ hΦout,
    Set.ext fun _ ↦ clutchingSection_eq_zero_iff hφ hΦ hΦout,
    fun i ↦ sectionIndex_clutchingSection hφ hΦ hΦout hn i _⟩

/-- **The disc clutching formula for the first Chern number.** Let `φ i`, for `i` in a finite type
`ι`, be coordinate discs of a compact surface `M` with a homological orientation `o`, with pairwise
disjoint closed discs, and let `E` be a complex vector bundle over `M` with a frame `Φ i` over each
closed disc and a frame `Φout` over the complement of the open discs. Then the first Chern number
of `E` is the sum over `i` of the degrees of the loops `ζ ↦ normalizedDet ((Φ i)⁻¹ ∘ Φout)` around
the boundary circles `(φ i).boundaryCircle`. -/
theorem chernNumber_eq_sum_degree_clutching [Fintype ι] [CompactSpace M] (hn : finrank ℝ EM = 2) :
    chernNumber o hn G E = ∑ i, Circle.degree (ContinuousMap.mk _
      (continuous_normalizedDet_clutchingTransition hφ hΦ hΦout i)).toBasedLoop := by
  obtain ⟨s, hs, hZ, hind⟩ := exists_detBundle_section_clutching hφ hΦ hΦout hn
  have hfin : {x | s x = 0}.Finite := hZ ▸ finite_range _
  rw [chernNumber_def, firstChernClass_eq_complexEulerClass_detBundle, complexEulerClass_def,
    VectorBundleOrientation.evalFundamentalClass_eulerClass_eq_sum_sectionIndex _ _ o hs hn hfin]
  have hset : hfin.toFinset =
      Finset.univ.map ⟨_, injective_apply_zero_of_pairwise_disjoint φ hφ⟩ := by
    ext x
    simp [hZ]
  rw [hset, Finset.sum_map]
  exact Finset.sum_congr rfl fun i _ ↦ hind i

end ClutchingIndex

/-! ### Frames from sections of the circle bundle of a Hermitian line bundle -/

section UnitFrame

open MulOpposite OrthonormalFrameBundle PrincipalBundle

variable {M : Type} [TopologicalSpace M] [T2Space M] {EM : Type} [NormedAddCommGroup EM]
  [NormedSpace ℝ EM] [FiniteDimensional ℝ EM] [ChartedSpace EM M]
  {o : HomologicalOrientation M EM 2} {ι : Type*} {φ : ι → CoordinateDisc o}
  (hφ : Pairwise (Disjoint on fun i ↦ (φ i).disc))
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] {E : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℂ F E]
  [ContinuousFiberNorm F E] [Fact (finrank ℂ F = 1)] (e : F ≃L[ℂ] ℂ)
  (σ : ι → ∀ x, Fiber ℂ F E ℂ x) (σout : ∀ x, Fiber ℂ F E ℂ x)

/-- The clutching transition of the frames `unitFrame e (σ i x)` over the closed discs and
`unitFrame e (σout x)` over their complement is, on the `i`-th boundary circle, multiplication by
the element of the circle that carries `σ i` to `σout`. -/
theorem clutchingTransition_unitFrame_apply (i : ι) (ζ : Circle) (v : F) :
    clutchingTransition hφ (fun i x ↦ unitFrame e (σ i x)) (fun x ↦ unitFrame e (σout x)) i ζ v =
      (division Circle (σ i ((φ i).boundaryCircle ζ)) (σout ((φ i).boundaryCircle ζ)) : ℂ) • v := by
  rw [clutchingTransition_def, trans_unitFrame_symm_apply]

/-- The normalized determinant of the clutching transition of the frames `unitFrame e (σ i x)`
over the closed discs and `unitFrame e (σout x)` over their complement is, on the `i`-th boundary
circle, the element of the circle that carries `σ i` to `σout`. -/
theorem normalizedDet_clutchingTransition_unitFrame (i : ι) (ζ : Circle) :
    (clutchingTransition hφ (fun i x ↦ unitFrame e (σ i x)) (fun x ↦ unitFrame e (σout x))
      i ζ).normalizedDet =
      division Circle (σ i ((φ i).boundaryCircle ζ)) (σout ((φ i).boundaryCircle ζ)) := by
  rw [clutchingTransition_def, normalizedDet_trans_unitFrame_symm]

end UnitFrame

/-! ### Symplectic frames -/

section Symplectic

open Matrix TauCeti.GLSymplectic
open scoped Manifold

variable {M : Type} [TopologicalSpace M] [T2Space M] {EM : Type} [NormedAddCommGroup EM]
  [NormedSpace ℝ EM] [FiniteDimensional ℝ EM] [ChartedSpace EM M]
  {o : HomologicalOrientation M EM 2} {ι : Type} [Fintype ι] {φ : ι → CoordinateDisc o}
  (hφ : Pairwise (Disjoint on fun i ↦ (φ i).disc))
  {κ : Type*} [Fintype κ] [DecidableEq κ]

omit [Fintype ι] in
/-- The loop along the `i`-th boundary circle of a map on the closed `i`-th disc has Maslov
index `0`: it contracts radially onto the centre (`CoordinateDisc.discContraction`). -/
private theorem maslovIndex_boundaryCircle_disc_eq_zero (i : ι)
    {P : (φ i).disc → GLSymplectic κ ℝ} (hP : Continuous P) :
    maslovIndex (ContinuousMap.mk (fun ζ ↦ P ⟨(φ i).boundaryCircle ζ,
      (φ i).boundaryCircle_mem_disc ζ⟩) (hP.comp ((φ i).boundaryCircle.continuous.subtype_mk _))
        ).toBasedLoop = 0 := by
  refine (maslovIndex_eq_of_homotopy _
    (Path.refl (P ⟨(φ i) 0, (φ i).openDisc_subset_disc (φ i).apply_zero_mem_openDisc⟩))
    ((ContinuousMap.mk P hP).comp (φ i).discContraction) (fun t ↦ ?_) (fun t ↦ ?_)
    (fun s ↦ ?_)).trans (maslovIndex_refl _)
  · rw [ContinuousMap.comp_apply, ContinuousMap.coe_mk, CoordinateDisc.discContraction_zero,
      ContinuousMap.toBasedLoop_apply _ t]
    simp only [ContinuousMap.coe_mk]
    refine congrArg P (Subtype.ext ?_)
    rw [Subtype.coe_mk, Subtype.coe_mk, CoordinateDisc.boundaryLoop_def,
      ContinuousMap.toBasedLoop_apply]
  · rw [ContinuousMap.comp_apply, ContinuousMap.coe_mk, CoordinateDisc.discContraction_one,
      Path.refl_apply]
  · rw [ContinuousMap.comp_apply, ContinuousMap.comp_apply,
      CoordinateDisc.discContraction_apply_zero]

include hφ in
/-- The loops along the boundary circles of a map on the complement of the open discs have
Maslov indices that add up to `0`, by the argument principle applied to its Maslov phase. -/
private theorem sum_maslovIndex_boundaryCircle_discComplement_eq_zero [CompactSpace M]
    (hn : finrank ℝ EM = 2) {P : discComplement φ → GLSymplectic κ ℝ} (hP : Continuous P) :
    ∑ i, maslovIndex (ContinuousMap.mk (fun ζ ↦ P ⟨(φ i).boundaryCircle ζ,
      boundaryCircle_mem_discComplement φ hφ i ζ⟩)
        (hP.comp ((φ i).boundaryCircle.continuous.subtype_mk _))).toBasedLoop = 0 := by
  classical
  let u : M → ℂ := fun x ↦ if h : x ∈ discComplement φ then (maslovPhase (P ⟨x, h⟩) : ℂ) else 0
  have hu (y : discComplement φ) : u y = maslovPhase (P y) :=
    dite_eq_left_of_eq_true (eq_true y.prop)
  simp only [maslovIndex_def]
  refine sum_degree_boundary_eq_zero hn φ hφ (u := u) ?_ (fun x hx ↦ ?_) _ fun i t ↦ ?_
  · refine continuousOn_iff_continuous_domRestrict.2 ?_
    exact (continuous_subtypeVal.comp (continuous_maslovPhase.comp hP)).congr fun y ↦ (hu y).symm
  · rw [show x = ((⟨x, hx⟩ : discComplement φ) : M) from rfl, hu]
    exact Circle.coe_ne_zero _
  · rw [CoordinateDisc.boundaryLoop_def, ContinuousMap.toBasedLoop_apply,
      show (φ i).boundaryCircle (unitToCircle t) =
        ((⟨_, boundaryCircle_mem_discComplement φ hφ i (unitToCircle t)⟩ : discComplement φ) : M)
        from rfl, hu, Circle.norm_coe, Complex.ofReal_one, div_one, Path.map_coe,
      Function.comp_apply, ContinuousMap.toBasedLoop_apply, ContinuousMap.coe_mk]

section Frames

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  {Φ : ∀ i, ∀ x : (φ i).disc, StdSpace κ ≃L[ℝ] V x}
  {Φout : ∀ x : discComplement φ, StdSpace κ ≃L[ℝ] V x}
  (hΦ : ∀ i, Continuous fun q : (φ i).disc × StdSpace κ ↦
    TotalSpace.mk' F (q.1 : M) (Φ i q.1 q.2))
  (hΦout : Continuous fun q : discComplement φ × StdSpace κ ↦
    TotalSpace.mk' F (q.1 : M) (Φout q.1 q.2))

variable [CompactSpace M] [IsManifold 𝓘(ℝ, EM) ((⊤ : ℕ∞) : WithTop ℕ∞) M] {n : ℕ∞}
  [ContMDiffVectorBundle n F V 𝓘(ℝ, EM)] {ω : ContMDiffTwoForm 𝓘(ℝ, EM) n F V}
  (G : Type*) [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G]
  [Fact (finrank ℝ F = 2 * finrank ℂ G)]

include hφ hΦ hΦout in
/-- **The disc clutching formula for symplectic frames.** Let `φ i`, for `i` in a finite type
`ι`, be coordinate discs of a compact surface `M` with a homological orientation `o`, with
pairwise disjoint closed discs, and let `ω` be a two-form on a smooth vector bundle `V` over `M`.
Let `Φ i` be a symplectic frame of `V` over the closed `i`-th disc and `Φout` one over the
complement of the open discs: linear isomorphisms `StdSpace κ ≃ V x`, continuous as maps to
the total space, with `ω(Φ v, Φ w) = ω₀(v, w)` for the standard form `ω₀ = stdForm κ`. Let
`Ψ i` be the transition loop of symplectic matrices on the `i`-th boundary circle, with
`Φout = Φ i ∘ Ψ i` there. Then the first Chern number of `(V, ω)` is the sum over `i` of the
Maslov indices of the loops `Ψ i`. -/
theorem symplecticChernNumber_eq_sum_maslovIndex_clutching (hn : finrank ℝ EM = 2)
    (hΦω : ∀ i (x : (φ i).disc) v w, ω.bilinFormAt x (Φ i x v) (Φ i x w) = stdForm κ v w)
    (hΦoutω : ∀ (x : discComplement φ) v w,
      ω.bilinFormAt x (Φout x v) (Φout x w) = stdForm κ v w)
    (Ψ : ι → C(Circle, GLSymplectic κ ℝ))
    (hΨ : ∀ i ζ v, Φout ⟨(φ i).boundaryCircle ζ, boundaryCircle_mem_discComplement φ hφ i ζ⟩ v =
      Φ i ⟨(φ i).boundaryCircle ζ, (φ i).boundaryCircle_mem_disc ζ⟩
        (toEuclideanLin (Ψ i ζ : GL (κ ⊕ κ) ℝ) v)) :
    symplecticChernNumber o hn G ω = ∑ i, maslovIndex (Ψ i).toBasedLoop := by
  -- Every fibre carries one of the symplectic frames.
  have hframe (x : M) : ∃ Θ : StdSpace κ ≃L[ℝ] V x,
      ∀ v w, ω.bilinFormAt x (Θ v) (Θ w) = stdForm κ v w := by
    by_cases hx : x ∈ discComplement φ
    · exact ⟨Φout ⟨x, hx⟩, hΦoutω ⟨x, hx⟩⟩
    · obtain ⟨i, hi⟩ : ∃ i, x ∈ (φ i).openDisc := by simpa using hx
      exact ⟨Φ i ⟨x, (φ i).openDisc_subset_disc hi⟩, hΦω i ⟨x, (φ i).openDisc_subset_disc hi⟩⟩
  rcases isEmpty_or_nonempty M with hM | hM
  · -- Over the empty surface there are no discs, and both sides vanish.
    have : IsEmpty ι := ⟨fun i ↦ hM.elim (φ i 0)⟩
    obtain ⟨J, hJ⟩ := (ContMDiffTwoForm.isNondegenerate_of_forall_exists (stdForm κ)
      fun x ↦ (hframe x).elim fun Θ hΘ ↦ ⟨Θ.toLinearEquiv, hΘ⟩).exists_compatible
    rw [symplecticChernNumber_eq_chernNumber o hn G hJ.tames, Finset.univ_eq_empty,
      Finset.sum_empty, chernNumber_eq_sum_degree_clutching hφ (Φ := fun i ↦ isEmptyElim i)
        (Φout := fun x ↦ isEmptyElim (x : M)) (fun i ↦ isEmptyElim i)
        (continuous_of_discreteTopology) hn, Finset.univ_eq_empty, Finset.sum_empty]
  -- Otherwise `ω` is compatible with some `J`, and `κ → ℂ` is a complex model of `(V, J)`.
  obtain ⟨J, _, hJ, hJω⟩ := exists_compatible_symplecticChernNumber_eq_chernNumber o hn G hframe
  -- Complex frames of `(V, J)` from the symplectic frames, by changes of frame `P i` and `P'`.
  choose P Θ hP hΘ hΘΦ using fun i ↦
    hJ.exists_continuous_GLSymplectic_complexFrame (f := ((↑) : (φ i).disc → M)) (hΦ i) (hΦω i)
  obtain ⟨P', Θout, hP', hΘout, hΘoutΦ⟩ :=
    hJ.exists_continuous_GLSymplectic_complexFrame (f := ((↑) : discComplement φ → M)) hΦout
      hΦoutω
  -- The new transition loops `(P i)⁻¹ Ψ i P'`.
  let Pinv (i : ι) : C(Circle, GLSymplectic κ ℝ) :=
    ContinuousMap.mk (fun ζ ↦ (fun x ↦ (P i x)⁻¹)
      ⟨(φ i).boundaryCircle ζ, (φ i).boundaryCircle_mem_disc ζ⟩)
        ((hP i).inv.comp ((φ i).boundaryCircle.continuous.subtype_mk _))
  let Pout (i : ι) : C(Circle, GLSymplectic κ ℝ) :=
    ContinuousMap.mk (fun ζ ↦ P' ⟨(φ i).boundaryCircle ζ,
      boundaryCircle_mem_discComplement φ hφ i ζ⟩)
        (hP'.comp ((φ i).boundaryCircle.continuous.subtype_mk _))
  -- By the complex formula, the number adds up the Maslov indices of these loops.
  have h : chernNumber o hn (κ → ℂ) J.toContinuousComplexStructure.Fiber =
      ∑ i, maslovIndex (Pinv i * Ψ i * Pout i).toBasedLoop := by
    rw [chernNumber_eq_sum_degree_clutching hφ hΘ hΘout hn]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [maslovIndex_def]
    refine Circle.degree_congr _ _ fun t ↦ ?_
    rw [ContinuousMap.toBasedLoop_apply, Path.map_coe, Function.comp_apply,
      ContinuousMap.toBasedLoop_apply, ContinuousMap.coe_mk, clutchingTransition_def,
      ContinuousMap.mul_apply, ContinuousMap.mul_apply]
    simp only [Pinv, Pout, ContinuousMap.coe_mk]
    exact (J.toContinuousComplexStructure.maslovPhase_inv_mul_mul_eq_normalizedDet
      (hΘΦ i _) (hΘoutΦ ⟨_, boundaryCircle_mem_discComplement φ hφ i _⟩) (hΨ i _)).symm
  rw [hJω, h]
  simp only [maslovIndex_toBasedLoop_mul, Finset.sum_add_distrib, Pout,
    sum_maslovIndex_boundaryCircle_discComplement_eq_zero hφ hn hP', add_zero]
  rw [Finset.sum_eq_zero fun i _ ↦ (maslovIndex_boundaryCircle_disc_eq_zero i
    (P := fun x ↦ (P i x)⁻¹) (hP i).inv : maslovIndex (Pinv i).toBasedLoop = 0), zero_add]

end Frames

end Symplectic

end Bundle

end SymplecticGeometry
