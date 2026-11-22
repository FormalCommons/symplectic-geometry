/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.DiscComplement.Basic
public import SymplecticGeometry.Topology.VectorBundle.Determinant
public import SymplecticGeometry.Topology.VectorBundle.Orientation.SectionIndex.Radial
public import TauCeti.Topology.VectorBundle.Complex.Clutching

/-!
# The clutching section of the determinant line

Let `φ i`, for `i` in a finite type `ι`, be coordinate discs of a surface `M` with a homological
orientation, whose closed discs are pairwise disjoint, and let `E` be a complex vector bundle over
`M` with model `G`. Suppose given a frame `Φ i` of `E` over the closed disc of `φ i` and a frame
`Φout` of `E` over the complement `discComplement φ` of the open discs, in the sense of Tau Ceti's
`Topology/VectorBundle/Complex/Clutching.lean`: continuous families of isomorphisms
`G ≃L[ℂ] E x`. On the boundary circle of the `i`-th disc they differ by the automorphism
`clutchingTransition hφ Φ Φout i ζ = (Φ i)⁻¹ ∘ Φout` of `G`.

This file builds from these frames a section of the determinant line `Λ^top E`
(`SymplecticGeometry.Bundle.detCore`) that the disc clutching formula sums over:

* on the complement of the open discs, the determinant section `detCoreFrameSection` of `Φout`;
* at `φ i z` with `‖z‖ < 1`, the determinant section of `Φ i` times `sphereCone uᵢ z`, for
  `uᵢ ζ = det (clutchingTransition hφ Φ Φout i ζ)` and `sphereCone` Tau Ceti's radial extension
  `r ζ ↦ r uᵢ(ζ)` of a function on the circle (read on `Circle` through
  `Circle.homeomorphSphere`).

The main result, `exists_detCore_section_clutching`, says that this section is continuous on
total spaces, that its zeros are exactly the centres `φ i 0`, and that its local index at `φ i 0`,
for the orientation of the determinant line as a complex line, is the degree of the loop of
normalized determinants `ContinuousLinearEquiv.normalizedDet` of the transition around the `i`-th
circle.

## Proof

The two descriptions agree on the boundary circles: there the section of `Φout` is that of `Φ i`
times the determinant of the transition (`detCoreFrameSection_eq_det_smul`, after restricting both
frames to the circle by `detCoreFrameSection_comp`), and the radial extension of `uᵢ` equals `uᵢ`
on the unit circle. So the section is continuous on each closed disc and on the complement of the
open discs, a finite closed cover of `M` (`LocallyFinite.continuous`). The determinant of an
isomorphism and the determinant section of a frame vanish nowhere
(`detCoreFrameSection_ne_zero`), and the radial extension of a function without zeros vanishes
only at the centre (`TauCeti.sphereCone_eq_zero_iff`). The local index is
`SymplecticGeometry.CoordinateDisc.sectionIndex_eq_degree_sphereCone`.

## Main definitions and results

* `SymplecticGeometry.Bundle.clutchingTransition`: the transition `(Φ i)⁻¹ ∘ Φout` on the
  `i`-th boundary circle.
* `SymplecticGeometry.Bundle.continuous_normalizedDet_clutchingTransition`: its normalized
  determinant is a continuous loop on the circle.
* `SymplecticGeometry.Bundle.exists_detCore_section_clutching`: the section described above, its
  continuity, its zeros and its local indices.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.7,
  where the first Chern number of a bundle over a surface is computed from trivializations over
  discs and over their complement.
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §§11 and 14 (indices of sections at isolated zeros, and the first Chern class
  through the determinant line).
-/

public section

noncomputable section

open Bundle Function Module Set TauCeti

namespace SymplecticGeometry

namespace Bundle

variable {M : Type} [TopologicalSpace M] [T2Space M] {EM : Type} [NormedAddCommGroup EM]
  [NormedSpace ℝ EM] [FiniteDimensional ℝ EM] [ChartedSpace EM M]
  {o : HomologicalOrientation M EM 2} {ι : Type*} {φ : ι → CoordinateDisc o}
  (hφ : Pairwise (Disjoint on fun i ↦ (φ i).disc))
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
  {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)] [∀ x, TopologicalSpace (E x)]

section Transition

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
  continuous_det_trans_symm (φ i).boundaryCircle (continuous_discFrame_boundaryCircle hΦ i)
    (continuous_outFrame_boundaryCircle hφ hΦout i)

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
private def discSection (i : ι) (y : (φ i).disc) : (detCore ℂ G E).core.Fiber y :=
  detCoreFrameSection (⟨Subtype.val, continuous_subtypeVal⟩) (Φ i) (hΦ i) y

/-- The determinant section of the frame `Φout` over the complement of the open discs. -/
private def outSection (y : discComplement φ) : (detCore ℂ G E).core.Fiber y :=
  detCoreFrameSection (⟨Subtype.val, continuous_subtypeVal⟩) Φout hΦout y

private theorem discSection_ne_zero (i : ι) (y : (φ i).disc) : discSection hΦ i y ≠ 0 :=
  detCoreFrameSection_ne_zero ⟨Subtype.val, continuous_subtypeVal⟩ (hΦ i) y

private theorem outSection_ne_zero (y : discComplement φ) : outSection hΦout y ≠ 0 :=
  detCoreFrameSection_ne_zero ⟨Subtype.val, continuous_subtypeVal⟩ hΦout y

private theorem continuous_discSection (i : ι) :
    Continuous fun y : (φ i).disc ↦ TotalSpace.mk' (Fin (detCore ℂ G E).rank → ℂ)
      (E := (detCore ℂ G E).core.Fiber) (y : M) (discSection hΦ i y) :=
  continuous_totalSpaceMk_detCoreFrameSection ⟨Subtype.val, continuous_subtypeVal⟩ (hΦ i)

private theorem continuous_outSection :
    Continuous fun y : discComplement φ ↦ TotalSpace.mk' (Fin (detCore ℂ G E).rank → ℂ)
      (E := (detCore ℂ G E).core.Fiber) (y : M) (outSection hΦout y) :=
  continuous_totalSpaceMk_detCoreFrameSection ⟨Subtype.val, continuous_subtypeVal⟩ hΦout

/-- On the boundary circle of the `i`-th disc, the determinant section of `Φout` is that of
`Φ i` times the determinant of the clutching transition. -/
private theorem outSection_boundaryCircle (i : ι) (ζ : Circle) :
    outSection hΦout ⟨(φ i).boundaryCircle ζ, boundaryCircle_mem_discComplement φ hφ i ζ⟩ =
      clutchingDet hφ hΦ hΦout i ζ •
        discSection hΦ i ⟨(φ i).boundaryCircle ζ, (φ i).boundaryCircle_mem_disc ζ⟩ := by
  let gout : C(Circle, discComplement φ) :=
    ⟨fun ζ ↦ ⟨(φ i).boundaryCircle ζ, boundaryCircle_mem_discComplement φ hφ i ζ⟩,
      (φ i).boundaryCircle.continuous.subtype_mk _⟩
  let gin : C(Circle, (φ i).disc) :=
    ⟨fun ζ ↦ ⟨(φ i).boundaryCircle ζ, (φ i).boundaryCircle_mem_disc ζ⟩,
      (φ i).boundaryCircle.continuous.subtype_mk _⟩
  have h1 := detCoreFrameSection_comp (⟨Subtype.val, continuous_subtypeVal⟩) hΦout gout
    (continuous_outFrame_boundaryCircle hφ hΦout i) ζ
  have h2 := detCoreFrameSection_comp (⟨Subtype.val, continuous_subtypeVal⟩) (hΦ i) gin
    (continuous_discFrame_boundaryCircle hΦ i) ζ
  have h3 := detCoreFrameSection_eq_det_smul (φ i).boundaryCircle
    (Φ := fun ζ ↦ Φ i ⟨(φ i).boundaryCircle ζ, (φ i).boundaryCircle_mem_disc ζ⟩)
    (Ψ := fun ζ ↦ Φout ⟨(φ i).boundaryCircle ζ, boundaryCircle_mem_discComplement φ hφ i ζ⟩)
    (continuous_discFrame_boundaryCircle hΦ i) (continuous_outFrame_boundaryCircle hφ hΦout i) ζ
  -- The determinant of `Φout ∘ (Φ i)⁻¹` on the fibre is that of `(Φ i)⁻¹ ∘ Φout` on `G`.
  have hc : LinearMap.det
      (((Φ i ⟨(φ i).boundaryCircle ζ, (φ i).boundaryCircle_mem_disc ζ⟩).symm.trans
        (Φout ⟨(φ i).boundaryCircle ζ, boundaryCircle_mem_discComplement φ hφ i ζ⟩) :
          E ((φ i).boundaryCircle ζ) →ₗ[ℂ] E ((φ i).boundaryCircle ζ))) =
      clutchingDet hφ hΦ hΦout i ζ := by
    refine Eq.trans ?_ (LinearMap.det_conj _
      (Φ i ⟨(φ i).boundaryCircle ζ, (φ i).boundaryCircle_mem_disc ζ⟩).toLinearEquiv)
    congr 1
    ext v
    simp [clutchingTransition_def]
  rw [outSection, discSection]
  refine h1.symm.trans (h3.trans ?_)
  rw [hc]
  exact congrArg _ h2

open Classical in
/-- The clutching section: the radial extension of `clutchingDet` times the determinant section of
`Φ i` on the `i`-th open disc, and the determinant section of `Φout` elsewhere. -/
private def clutchingSection (x : M) : (detCore ℂ G E).core.Fiber x :=
  if h : ∃ i, x ∈ (φ i).openDisc then
    radialCoeff hφ hΦ hΦout h.choose x •
      discSection hΦ h.choose ⟨x, (φ _).openDisc_subset_disc h.choose_spec⟩
  else outSection hΦout ⟨x, (mem_discComplement_iff φ).2 fun i hi ↦ h ⟨i, hi⟩⟩

omit [FiniteDimensional ℂ G] [TopologicalSpace (TotalSpace G E)] [FiberBundle G E]
  [VectorBundle ℂ G E] in
include hφ in
private theorem eq_of_mem_openDisc_of_mem_disc {i j : ι} {x : M} (hi : x ∈ (φ i).openDisc)
    (hj : x ∈ (φ j).disc) : i = j := by
  by_contra h
  exact (hφ h).notMem_of_mem_left ((φ i).openDisc_subset_disc hi) hj

private theorem clutchingSection_of_mem_discComplement {x : M} (hx : x ∈ discComplement φ) :
    clutchingSection hφ hΦ hΦout x = outSection hΦout ⟨x, hx⟩ := by
  rw [clutchingSection, dite_eq_right fun ⟨i, hi⟩ ↦ (mem_discComplement_iff φ).1 hx i hi]

private theorem clutchingSection_of_mem_openDisc {i : ι} {x : M} (hx : x ∈ (φ i).openDisc) :
    clutchingSection hφ hΦ hΦout x = radialCoeff hφ hΦ hΦout i x •
      discSection hΦ i ⟨x, (φ i).openDisc_subset_disc hx⟩ := by
  have key : ∀ j (hj : x ∈ (φ j).openDisc), radialCoeff hφ hΦ hΦout j x •
      discSection hΦ j ⟨x, (φ j).openDisc_subset_disc hj⟩ = radialCoeff hφ hΦ hΦout i x •
      discSection hΦ i ⟨x, (φ i).openDisc_subset_disc hx⟩ := by
    intro j hj
    obtain rfl := eq_of_mem_openDisc_of_mem_disc hφ hj ((φ i).openDisc_subset_disc hx)
    rfl
  rw [clutchingSection, dite_eq_left ⟨i, hx⟩]
  exact key _ (Exists.choose_spec (⟨i, hx⟩ : ∃ j, x ∈ (φ j).openDisc))

/-- On the whole closed `i`-th disc, the clutching section is the radial extension of
`clutchingDet` times the determinant section of `Φ i`. -/
private theorem clutchingSection_of_mem_disc {i : ι} {x : M} (hx : x ∈ (φ i).disc) :
    clutchingSection hφ hΦ hΦout x = radialCoeff hφ hΦ hΦout i x • discSection hΦ i ⟨x, hx⟩ := by
  by_cases ho : x ∈ (φ i).openDisc
  · exact clutchingSection_of_mem_openDisc hφ hΦ hΦout ho
  obtain ⟨ζ, rfl⟩ : x ∈ range (φ i).boundaryCircle := (φ i).disc_diff_openDisc ▸ ⟨hx, ho⟩
  rw [clutchingSection_of_mem_discComplement hφ hΦ hΦout
      (boundaryCircle_mem_discComplement φ hφ i ζ), outSection_boundaryCircle,
    radialCoeff_boundaryCircle]

/-- The clutching section is continuous on total spaces. -/
private theorem continuous_clutchingSection [Finite ι] :
    Continuous fun x ↦ TotalSpace.mk' (Fin (detCore ℂ G E).rank → ℂ)
      (E := (detCore ℂ G E).core.Fiber) x (clutchingSection hφ hΦ hΦout x) := by
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
  have h0 : ∀ i, φ i 0 ∈ (φ i).openDisc := fun i ↦
    (φ i).apply_mem_openDisc_iff.2 (by simp [CoordinateDisc.coe_zero])
  by_cases hx : x ∈ discComplement φ
  · rw [clutchingSection_of_mem_discComplement hφ hΦ hΦout hx]
    refine iff_of_false (outSection_ne_zero hΦout _) ?_
    rintro ⟨i, rfl⟩
    exact (mem_discComplement_iff φ).1 hx i (h0 i)
  obtain ⟨i, hi⟩ : ∃ i, x ∈ (φ i).openDisc := by simpa using hx
  obtain ⟨z, -, rfl⟩ := (φ i).mem_openDisc_iff.1 hi
  rw [clutchingSection_of_mem_openDisc hφ hΦ hΦout hi, smul_eq_zero,
    or_iff_left (discSection_ne_zero hΦ i _), radialCoeff_apply,
    sphereCone_eq_zero_iff (f := clutchingDet hφ hΦ hΦout i ∘ Circle.homeomorphSphere.symm)
      fun _ ↦ clutchingDet_ne_zero hφ hΦ hΦout i _]
  constructor
  · intro hz
    exact ⟨i, congrArg (φ i) (Subtype.ext (CoordinateDisc.coe_zero.trans hz.symm))⟩
  · rintro ⟨j, hj⟩
    obtain rfl := eq_of_mem_openDisc_of_mem_disc hφ (h0 j)
      (hj ▸ (φ i).openDisc_subset_disc hi)
    rw [← (φ j).injective hj, CoordinateDisc.coe_zero]

local instance : VectorBundle ℝ (Fin (detCore ℂ G E).rank → ℂ) (detCore ℂ G E).core.Fiber :=
  VectorBundle.restrictScalars ℝ ℂ _ _

/-- The local index of the clutching section at the centre of the `i`-th disc is the degree of
the loop of normalized determinants of the clutching transition. -/
private theorem sectionIndex_clutchingSection (hn : finrank ℝ EM = 2) (i : ι)
    (hs : Continuous fun x ↦ TotalSpace.mk' (Fin (detCore ℂ G E).rank → ℂ)
      (E := (detCore ℂ G E).core.Fiber) x (clutchingSection hφ hΦ hΦout x)) :
    (VectorBundleOrientation.reindex (finCongr (by simp))
        (VectorBundleOrientation.complex (Fin (detCore ℂ G E).rank → ℂ)
          (detCore ℂ G E).core.Fiber)).sectionIndex
        (by simp [finrank_real_eq_two_mul_finrank_complex]) o hs (φ i 0) =
      Circle.degree (ContinuousMap.mk _
        (continuous_normalizedDet_clutchingTransition hφ hΦ hΦout i)).toBasedLoop := by
  classical
  -- The frame of the determinant line given by `Φ i`, read along the chart.
  let σ : ∀ z : CoordinateDisc.ball, (detCore ℂ G E).core.Fiber (φ i z) := fun z ↦
    if h : φ i z ∈ (φ i).disc then discSection hΦ i ⟨φ i z, h⟩ else 0
  have hσe : ∀ (z : CoordinateDisc.ball) (hz : ‖(z : ℂ)‖ ≤ 1),
      σ z = discSection hΦ i ⟨φ i z, (φ i).apply_mem_disc_iff.2 hz⟩ := fun z hz ↦
    dite_eq_left ((φ i).apply_mem_disc_iff.2 hz)
  have hσ : ContinuousOn (fun z ↦ TotalSpace.mk' (Fin (detCore ℂ G E).rank → ℂ)
      (E := (detCore ℂ G E).core.Fiber) (φ i z) (σ z)) {z | ‖(z : ℂ)‖ < 1} := by
    refine ContinuousOn.mono (s := {z : CoordinateDisc.ball | ‖(z : ℂ)‖ ≤ 1}) ?_
      fun (z : CoordinateDisc.ball) (hz : ‖(z : ℂ)‖ < 1) ↦ (hz.le : ‖(z : ℂ)‖ ≤ 1)
    refine continuousOn_iff_continuous_domRestrict.2 ?_
    refine ((continuous_discSection hΦ i).comp (((φ i).continuous.comp
      continuous_subtypeVal).subtype_mk fun z ↦ (φ i).apply_mem_disc_iff.2 z.property)).congr
        fun z ↦ ?_
    simp only [domRestrict, Function.comp_apply, hσe z z.property]
  have hσ0 : ∀ z : CoordinateDisc.ball, ‖(z : ℂ)‖ < 1 → σ z ≠ 0 := fun z hz ↦ by
    rw [hσe z hz.le]
    exact discSection_ne_zero hΦ i _
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
theorem exists_detCore_section_clutching [Finite ι] (hn : finrank ℝ EM = 2) :
    ∃ (s : ∀ x, (detCore ℂ G E).core.Fiber x)
      (hs : Continuous fun x ↦ TotalSpace.mk' (Fin (detCore ℂ G E).rank → ℂ)
        (E := (detCore ℂ G E).core.Fiber) x (s x)),
      {x | s x = 0} = range (fun i ↦ φ i 0) ∧
      ∀ i, (VectorBundleOrientation.reindex (finCongr (by simp))
          (VectorBundleOrientation.complex (Fin (detCore ℂ G E).rank → ℂ)
            (detCore ℂ G E).core.Fiber)).sectionIndex
          (by simp [finrank_real_eq_two_mul_finrank_complex]) o hs (φ i 0) =
        Circle.degree (ContinuousMap.mk _
          (continuous_normalizedDet_clutchingTransition hφ hΦ hΦout i)).toBasedLoop :=
  ⟨clutchingSection hφ hΦ hΦout, continuous_clutchingSection hφ hΦ hΦout,
    Set.ext fun _ ↦ clutchingSection_eq_zero_iff hφ hΦ hΦout,
    fun i ↦ sectionIndex_clutchingSection hφ hΦ hΦout hn i _⟩

end Transition

end Bundle

end SymplecticGeometry
