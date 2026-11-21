/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Topology.ComplexStructure.Orbit
public import SymplecticGeometry.Topology.ComplexStructure.Orthogonal
public import TauCeti.Analysis.Matrix.EuclideanLin
public import TauCeti.Topology.Algebra.GroupAction.Transitive
public import TauCeti.Topology.Algebra.OrthogonalGroup
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Homotopy.Equiv
public import Mathlib.Topology.Homotopy.Path

/-!
# The components of the space of complex structures and the homotopy type SO(2n)/U(n)

The special orthogonal group `SO(2n)` acts on the complex structures of `StdSpace ι = ℝ²ⁿ` by
conjugation, and preserves the orthogonal and the positively oriented ones. On the structures that
are both it acts transitively, with stabilizer of `J₀` the realified unitary group `U(n)`; since
`SO(2n)` is compact, this set is homeomorphic to `SO(2n)/U(n)`.

The positively oriented structures form a clopen set, and the polar deformation of
`SymplecticGeometry.complexStructurePolarHomotopy` joins each of them, inside that set, to an
orthogonal one, which lies in the `SO(2n)`-orbit of `J₀`. As `SO(2n)` is path-connected, the
positively oriented structures form the connected component of `J₀`, and the polar deformation
exhibits it as homotopy equivalent to `SO(2n)/U(n)`. A matrix of negative determinant carries this
component onto the remaining structures, so that in positive dimension there are exactly two
components. For `ι` empty there is a single complex structure, hence a single component.

## Main definitions

* `SymplecticGeometry.positiveOrthogonalComplexStructures`: the orthogonal positively oriented
  complex structures, as a `SubMulAction` of `SO(2n)`.
* `SymplecticGeometry.quotientUnitaryHomeomorph`: the homeomorphism from
  `SO(2n) ⧸ stabilizer J₀` onto the orthogonal positively oriented complex structures.
* `SymplecticGeometry.positivelyOrientedHomotopyEquiv`: the positively oriented complex structures
  are homotopy equivalent to `SO(2n) ⧸ stabilizer J₀`.

## Main results

* `SymplecticGeometry.map_stabilizer_specialOrthogonalGroup_stdComplexStructure`: the stabilizer
  of `J₀` in `SO(2n)` is the realified unitary group `U(n)`.
* `SymplecticGeometry.exists_specialOrthogonalGroup_smul_stdComplexStructure_eq`: every orthogonal
  positively oriented structure is `g • J₀` for some `g ∈ SO(2n)`.
* `SymplecticGeometry.isPathConnected_setOf_isPositivelyOriented`,
  `SymplecticGeometry.connectedComponent_stdComplexStructure`: the positively oriented structures
  form the path-connected component of `J₀`;
  `SymplecticGeometry.pathComponent_stdComplexStructure` is its path-component form.
* `SymplecticGeometry.nat_card_connectedComponents_almostComplexStructure_stdSpace`: in positive
  dimension the complex structures of `StdSpace ι` have two components;
  `SymplecticGeometry.nat_card_connectedComponents_almostComplexStructure_stdSpace_of_isEmpty`:
  in dimension zero they have one.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Section 2.5, Proposition 2.5.2.
-/

public section

namespace SymplecticGeometry

open TauCeti AlmostComplexStructure Matrix
open scoped unitInterval ContinuousMap

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### The action of the special orthogonal group -/

section Orthogonal

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem smul_mem_orthogonalComplexStructures (g : specialOrthogonalGroup n ℝ)
    {J : AlmostComplexStructure (EuclideanSpace ℝ n)} (hJ : J ∈ orthogonalComplexStructures n) :
    g • J ∈ orthogonalComplexStructures n := by
  rw [mem_orthogonalComplexStructures_iff_mem_orthogonalGroup] at hJ ⊢
  rw [specialOrthogonalGroup_smul_def, homeomorphMatrix_generalLinearGroup_smul]
  have hg := (mem_specialOrthogonalGroup_iff.1 g.property).1
  exact mul_mem (mul_mem hg hJ) (Unitary.star_mem hg)

/-- A special orthogonal matrix preserves and reflects orthogonality of complex structures. -/
theorem specialOrthogonalGroup_smul_mem_orthogonalComplexStructures_iff
    (g : specialOrthogonalGroup n ℝ) {J : AlmostComplexStructure (EuclideanSpace ℝ n)} :
    g • J ∈ orthogonalComplexStructures n ↔ J ∈ orthogonalComplexStructures n :=
  ⟨fun h ↦ inv_smul_smul g J ▸ smul_mem_orthogonalComplexStructures g⁻¹ h,
    smul_mem_orthogonalComplexStructures g⟩

end Orthogonal

private theorem IsPositivelyOriented.specialOrthogonalGroup_smul
    (g : specialOrthogonalGroup (ι ⊕ ι) ℝ) {J : AlmostComplexStructure (StdSpace ι)}
    (hJ : IsPositivelyOriented J) : IsPositivelyOriented (g • J) := by
  rw [specialOrthogonalGroup_smul_def]
  exact hJ.smul (by simp [(mem_specialOrthogonalGroup_iff.1 g.property).2])

/-- A special orthogonal matrix preserves and reflects positive orientation. -/
theorem isPositivelyOriented_specialOrthogonalGroup_smul_iff
    (g : specialOrthogonalGroup (ι ⊕ ι) ℝ) {J : AlmostComplexStructure (StdSpace ι)} :
    IsPositivelyOriented (g • J) ↔ IsPositivelyOriented J :=
  ⟨fun h ↦ inv_smul_smul g J ▸ h.specialOrthogonalGroup_smul g⁻¹,
    IsPositivelyOriented.specialOrthogonalGroup_smul g⟩

variable (ι) in
/-- The orthogonal positively oriented complex structures of `StdSpace ι`, a set that the
special orthogonal group `SO(2n)` preserves. -/
def positiveOrthogonalComplexStructures :
    SubMulAction (specialOrthogonalGroup (ι ⊕ ι) ℝ) (AlmostComplexStructure (StdSpace ι)) where
  carrier := {J | J ∈ orthogonalComplexStructures (ι ⊕ ι) ∧ IsPositivelyOriented J}
  smul_mem' g _ hJ := ⟨(specialOrthogonalGroup_smul_mem_orthogonalComplexStructures_iff g).2 hJ.1,
    (isPositivelyOriented_specialOrthogonalGroup_smul_iff g).2 hJ.2⟩

/-- Membership in `positiveOrthogonalComplexStructures ι`. -/
@[simp]
theorem mem_positiveOrthogonalComplexStructures {J : AlmostComplexStructure (StdSpace ι)} :
    J ∈ positiveOrthogonalComplexStructures ι ↔
      J ∈ orthogonalComplexStructures (ι ⊕ ι) ∧ IsPositivelyOriented J :=
  (Iff.rfl)

/-- `J₀` is orthogonal and positively oriented. -/
@[simp]
theorem stdComplexStructure_mem_positiveOrthogonalComplexStructures :
    stdComplexStructure ι ∈ positiveOrthogonalComplexStructures ι :=
  ⟨stdComplexStructure_mem_orthogonalComplexStructures, isPositivelyOriented_stdComplexStructure⟩

/-- A special orthogonal matrix fixes `J₀` exactly when it commutes with the matrix `J`. -/
theorem mem_stabilizer_specialOrthogonalGroup_stdComplexStructure_iff
    {g : specialOrthogonalGroup (ι ⊕ ι) ℝ} :
    g ∈ MulAction.stabilizer (specialOrthogonalGroup (ι ⊕ ι) ℝ) (stdComplexStructure ι) ↔
      Commute (J ι ℝ) (g : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) := by
  rw [MulAction.mem_stabilizer_iff, specialOrthogonalGroup_smul_def,
    generalLinearGroup_smul_stdComplexStructure_eq_iff]
  simp

variable (ι) in
/-- **The stabilizer of `J₀` in `SO(2n)` is `U(n)`**: a special orthogonal matrix fixes `J₀`
exactly when it is the realification of a unitary complex matrix. -/
theorem map_stabilizer_specialOrthogonalGroup_stdComplexStructure :
    (MulAction.stabilizer (specialOrthogonalGroup (ι ⊕ ι) ℝ)
        (stdComplexStructure ι)).toSubmonoid.map (specialOrthogonalGroup (ι ⊕ ι) ℝ).subtype =
      (unitaryGroup ι ℂ).map (realifyAlgHom ι ℂ) := by
  ext M
  refine ⟨?_, fun hM ↦ ?_⟩
  · rintro ⟨g, hg, rfl⟩
    exact mem_map_realifyAlgHom_unitaryGroup_iff.2
      ⟨mem_stabilizer_specialOrthogonalGroup_stdComplexStructure_iff.1 hg,
        (mem_specialOrthogonalGroup_iff.1 g.property).1⟩
  · obtain ⟨hJ, hO⟩ := mem_map_realifyAlgHom_unitaryGroup_iff.1 hM
    obtain ⟨A, hA, rfl⟩ := hM
    have hpos : 0 < (realifyAlgHom ι ℂ A).det := by
      rw [realifyAlgHom_apply, det_realify]
      exact RCLike.normSq_pos.2 fun h ↦ by
        simpa [h] using Unitary.star_mul_self_of_mem (det_of_mem_unitary hA)
    have hdet := (det_eq_one_or_neg_one_of_mem_orthogonalGroup hO).resolve_right (by linarith)
    exact ⟨⟨_, mem_specialOrthogonalGroup_iff.2 ⟨hO, hdet⟩⟩,
      mem_stabilizer_specialOrthogonalGroup_stdComplexStructure_iff.2 hJ, rfl⟩

/-- **`SO(2n)` acts transitively on the orthogonal positively oriented complex structures**:
each of them is `g • J₀` for a special orthogonal matrix `g`. -/
theorem exists_specialOrthogonalGroup_smul_stdComplexStructure_eq
    {J : AlmostComplexStructure (StdSpace ι)} (hJ : J ∈ orthogonalComplexStructures (ι ⊕ ι))
    (hJ' : IsPositivelyOriented J) :
    ∃ g : specialOrthogonalGroup (ι ⊕ ι) ℝ, g • stdComplexStructure ι = J := by
  -- An isometry conjugating `J₀` to `J` is the action of an orthogonal matrix `U`, whose
  -- determinant is positive since `J` is positively oriented.
  obtain ⟨Φ, hΦ⟩ := exists_linearIsometryEquiv_transport_eq (stdComplexStructure ι) J
    (mem_orthogonalComplexStructures.1 stdComplexStructure_mem_orthogonalComplexStructures)
    (mem_orthogonalComplexStructures.1 hJ) rfl
  obtain ⟨U, rfl⟩ := UnitaryGroup.toLinearIsometryEquiv_surjective Φ
  have hU : (Unitary.toUnits U : GL (ι ⊕ ι) ℝ) • stdComplexStructure ι = J := by
    rw [generalLinearGroup_smul_def, ← hΦ]
    congr 1
    refine LinearEquiv.ext fun v ↦ ?_
    simp [Matrix.toEuclideanCLE_apply, Matrix.toLpLin_apply]
  have hpos := (isPositivelyOriented_smul_stdComplexStructure_iff _).1 (hU ▸ hJ')
  have hdet := (det_eq_one_or_neg_one_of_mem_orthogonalGroup U.property).resolve_right
    (by simp only [Unitary.val_toUnits_apply] at hpos; linarith)
  exact ⟨⟨U, mem_specialOrthogonalGroup_iff.2 ⟨U.property, hdet⟩⟩, hU⟩

/-- `SO(2n)` acts transitively on the orthogonal positively oriented complex structures. -/
instance instIsPretransitivePositiveOrthogonalComplexStructures :
    MulAction.IsPretransitive (specialOrthogonalGroup (ι ⊕ ι) ℝ)
      (positiveOrthogonalComplexStructures ι) where
  exists_smul_eq J J' := by
    obtain ⟨g, hg⟩ :=
      exists_specialOrthogonalGroup_smul_stdComplexStructure_eq J.property.1 J.property.2
    obtain ⟨g', hg'⟩ :=
      exists_specialOrthogonalGroup_smul_stdComplexStructure_eq J'.property.1 J'.property.2
    refine ⟨g' * g⁻¹, Subtype.ext ?_⟩
    rw [SubMulAction.val_smul, mul_smul, ← hg, inv_smul_smul, hg']

variable (ι) in
/-- **The orthogonal positively oriented complex structures form `SO(2n)/U(n)`**: the coset of
a special orthogonal matrix `g` modulo the stabilizer of `J₀` goes to `g • J₀`. -/
noncomputable def quotientUnitaryHomeomorph :
    specialOrthogonalGroup (ι ⊕ ι) ℝ ⧸
        MulAction.stabilizer (specialOrthogonalGroup (ι ⊕ ι) ℝ) (stdComplexStructure ι) ≃ₜ
      positiveOrthogonalComplexStructures ι :=
  (Homeomorph.Quotient.congrRight fun _ _ ↦ by
      rw [SubMulAction.stabilizer_of_subMul
        ⟨_, stdComplexStructure_mem_positiveOrthogonalComplexStructures (ι := ι)⟩]).trans
    (quotientStabilizerHomeomorph _
      ⟨_, stdComplexStructure_mem_positiveOrthogonalComplexStructures⟩
      (continuous_induced_rng.2 (continuous_id.smul continuous_const)))

/-- The coset of `g` goes to `g • J₀`. -/
@[simp]
theorem coe_quotientUnitaryHomeomorph_mk (g : specialOrthogonalGroup (ι ⊕ ι) ℝ) :
    (quotientUnitaryHomeomorph ι (QuotientGroup.mk g) : AlmostComplexStructure (StdSpace ι)) =
      g • stdComplexStructure ι := by
  rw [quotientUnitaryHomeomorph, Homeomorph.trans_apply]
  exact congrArg Subtype.val (quotientStabilizerHomeomorph_mk _ _ _ g)

/-! ### The component of `J₀` -/

/-- The polar deformation keeps a positively oriented structure positively oriented, since the
positively oriented structures form a clopen set. -/
theorem isPositivelyOriented_complexStructurePolarHomotopy
    {J : AlmostComplexStructure (StdSpace ι)} (hJ : IsPositivelyOriented J) (t : I) :
    IsPositivelyOriented (complexStructurePolarHomotopy (ι ⊕ ι) (t, J)) := by
  have hc : IsClopen ((fun s : I ↦ complexStructurePolarHomotopy (ι ⊕ ι) (s, J)) ⁻¹'
      {J | IsPositivelyOriented J}) :=
    isClopen_setOf_isPositivelyOriented.preimage
      ((complexStructurePolarHomotopy (ι ⊕ ι)).continuous.comp
        (continuous_id.prodMk continuous_const))
  have h0 : (0 : I) ∈ (fun s : I ↦ complexStructurePolarHomotopy (ι ⊕ ι) (s, J)) ⁻¹'
      {J | IsPositivelyOriented J} := by
    simpa using hJ
  exact (Set.ext_iff.1 (hc.eq_univ ⟨0, h0⟩) t).2 (Set.mem_univ t)

/-- The polar retraction of a positively oriented structure is positively oriented. -/
theorem isPositivelyOriented_complexStructurePolarRetraction
    {J : AlmostComplexStructure (StdSpace ι)} (hJ : IsPositivelyOriented J) :
    IsPositivelyOriented (complexStructurePolarRetraction (ι ⊕ ι) J).val := by
  have := isPositivelyOriented_complexStructurePolarHomotopy hJ 1
  rw [(complexStructurePolarHomotopy (ι ⊕ ι)).apply_one] at this
  exact this

/-- Each positively oriented structure is joined to `J₀` by a path: the polar deformation to an
orthogonal structure, followed by the image of a path in `SO(2n)`. -/
theorem IsPositivelyOriented.joined_stdComplexStructure {J : AlmostComplexStructure (StdSpace ι)}
    (hJ : IsPositivelyOriented J) : Joined (stdComplexStructure ι) J := by
  have h₁ : Joined J (complexStructurePolarRetraction (ι ⊕ ι) J).val :=
    ⟨(complexStructurePolarHomotopy (ι ⊕ ι)).toHomotopy.evalAt J⟩
  obtain ⟨g, hg⟩ := exists_specialOrthogonalGroup_smul_stdComplexStructure_eq
    (complexStructurePolarRetraction (ι ⊕ ι) J).property
    (isPositivelyOriented_complexStructurePolarRetraction hJ)
  have h₂ : Joined (stdComplexStructure ι) (g • stdComplexStructure ι) := by
    simpa using (PathConnectedSpace.joined 1 g).map
      (f := fun g : specialOrthogonalGroup (ι ⊕ ι) ℝ ↦ g • stdComplexStructure ι)
      (continuous_id.smul continuous_const)
  exact h₂.trans (hg ▸ h₁.symm)

/-- The path component of `J₀` consists of the positively oriented complex structures. -/
theorem pathComponent_stdComplexStructure :
    pathComponent (stdComplexStructure ι) = {J | IsPositivelyOriented J} :=
  Set.Subset.antisymm
    ((pathComponent_subset_component _).trans
      (isClopen_setOf_isPositivelyOriented.connectedComponent_subset
        isPositivelyOriented_stdComplexStructure))
    fun _ hJ ↦ IsPositivelyOriented.joined_stdComplexStructure hJ

/-- The positively oriented complex structures of `StdSpace ι` form a path-connected set. -/
theorem isPathConnected_setOf_isPositivelyOriented :
    IsPathConnected {J : AlmostComplexStructure (StdSpace ι) | IsPositivelyOriented J} := by
  rw [← pathComponent_stdComplexStructure]
  exact isPathConnected_pathComponent

/-- The connected component of `J₀` consists of the positively oriented complex structures. -/
theorem connectedComponent_stdComplexStructure :
    connectedComponent (stdComplexStructure ι) = {J | IsPositivelyOriented J} :=
  Set.Subset.antisymm
    ((isClopen_setOf_isPositivelyOriented (ι := ι)).connectedComponent_subset
      isPositivelyOriented_stdComplexStructure)
    (IsPreconnected.subset_connectedComponent
      (isPathConnected_setOf_isPositivelyOriented (ι := ι)).isConnected.isPreconnected
      isPositivelyOriented_stdComplexStructure)

omit [DecidableEq ι] in
/-- **In positive dimension the complex structures of `ℝ²ⁿ` form two components**: the
positively oriented structures, and the others. -/
theorem nat_card_connectedComponents_almostComplexStructure_stdSpace [Nonempty ι] :
    Nat.card (ConnectedComponents (AlmostComplexStructure (StdSpace ι))) = 2 := by
  classical
  obtain ⟨J₁, hJ₁⟩ := exists_not_isPositivelyOriented (ι := ι)
  obtain ⟨g, rfl⟩ := exists_generalLinearGroup_smul_stdComplexStructure_eq J₁
  have hg : (g : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ).det < 0 := by
    rw [isPositivelyOriented_smul_stdComplexStructure_iff, not_lt] at hJ₁
    exact hJ₁.lt_of_ne g.det_ne_zero
  -- A structure `h • J₀` that is not positively oriented is `g • (g⁻¹ * h) • J₀`, with
  -- `(g⁻¹ * h) • J₀` positively oriented, so it lies in the component of `g • J₀`.
  have hmem (J) (hJ : ¬IsPositivelyOriented J) :
      J ∈ connectedComponent (g • stdComplexStructure ι) := by
    obtain ⟨h, rfl⟩ := exists_generalLinearGroup_smul_stdComplexStructure_eq J
    rw [isPositivelyOriented_smul_stdComplexStructure_iff, not_lt] at hJ
    have hmul : (h : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ).det =
        (g : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ).det *
          ((g⁻¹ * h : GL (ι ⊕ ι) ℝ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ).det := by
      rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel_left]
    have hpos : IsPositivelyOriented ((g⁻¹ * h) • stdComplexStructure ι) :=
      (isPositivelyOriented_smul_stdComplexStructure_iff _).2 <|
        pos_of_mul_neg_right (hmul ▸ hJ.lt_of_ne h.det_ne_zero) hg.le
    have := hpos.joined_stdComplexStructure.map (continuous_const_smul g)
    rw [smul_smul, mul_inv_cancel_left] at this
    exact pathComponent_subset_component _ this
  rw [Nat.card_eq_two_iff]
  refine ⟨ConnectedComponents.mk (stdComplexStructure ι),
    ConnectedComponents.mk (g • stdComplexStructure ι), fun h ↦ hJ₁ ?_, ?_⟩
  · have := ConnectedComponents.coe_eq_coe'.1 h.symm
    rwa [connectedComponent_stdComplexStructure] at this
  · refine Set.eq_univ_of_forall fun c ↦ ?_
    obtain ⟨J, rfl⟩ := ConnectedComponents.surjective_coe c
    by_cases hJ : IsPositivelyOriented J
    · refine Or.inl (ConnectedComponents.coe_eq_coe'.2 ?_)
      rwa [connectedComponent_stdComplexStructure]
    · exact Or.inr (ConnectedComponents.coe_eq_coe'.2 (hmem J hJ))

omit [DecidableEq ι] in
/-- In dimension zero the space of complex structures is a point (the zero map), so it has one
component, not two. -/
theorem nat_card_connectedComponents_almostComplexStructure_stdSpace_of_isEmpty [IsEmpty ι] :
    Nat.card (ConnectedComponents (AlmostComplexStructure (StdSpace ι))) = 1 := by
  classical
  have : Subsingleton (AlmostComplexStructure (StdSpace ι)) :=
    ⟨fun J J' ↦ AlmostComplexStructure.ext fun v ↦ Subsingleton.elim _ _⟩
  exact Nat.card_eq_one_iff_unique.2 ⟨ConnectedComponents.surjective_coe.subsingleton,
    ⟨ConnectedComponents.mk (stdComplexStructure ι)⟩⟩

/-! ### The homotopy type -/

variable (ι) in
/-- **The component of `J₀` has the homotopy type of `SO(2n)/U(n)`**: the polar deformation
retracts the positively oriented complex structures of `StdSpace ι` onto the orthogonal ones,
which form `SO(2n) ⧸ stabilizer J₀` by `quotientUnitaryHomeomorph`. -/
noncomputable def positivelyOrientedHomotopyEquiv :
    {J : AlmostComplexStructure (StdSpace ι) // IsPositivelyOriented J} ≃ₕ
      specialOrthogonalGroup (ι ⊕ ι) ℝ ⧸
        MulAction.stabilizer (specialOrthogonalGroup (ι ⊕ ι) ℝ) (stdComplexStructure ι) :=
  (ContinuousMap.HomotopyEquiv.ofWeakDeformationRetraction
      (A := (positiveOrthogonalComplexStructures ι : Set (AlmostComplexStructure (StdSpace ι))))
      (B := {J | IsPositivelyOriented J}) (fun _ hJ ↦ hJ.2)
      (fun p ↦ complexStructurePolarHomotopy (ι ⊕ ι) (p.1, p.2))
      ((complexStructurePolarHomotopy (ι ⊕ ι)).continuous.comp
        (continuous_fst.prodMk (continuous_subtypeVal.comp continuous_snd)))
      (fun p ↦ isPositivelyOriented_complexStructurePolarHomotopy p.2.property p.1)
      (fun J ↦ (complexStructurePolarHomotopy (ι ⊕ ι)).apply_zero J)
      (fun J ↦ (complexStructurePolarHomotopy (ι ⊕ ι)).apply_one J ▸
        ⟨(complexStructurePolarRetraction (ι ⊕ ι) J).property,
          isPositivelyOriented_complexStructurePolarRetraction J.property⟩)
      (fun t _ hJ ↦
        ((complexStructurePolarHomotopy (ι ⊕ ι)).eq_fst t hJ.1).symm ▸ hJ)).symm.trans
    (quotientUnitaryHomeomorph ι).symm.toHomotopyEquiv

/-- The homotopy inverse of `positivelyOrientedHomotopyEquiv` sends the coset of `g` to
`g • J₀`. -/
@[simp]
theorem coe_positivelyOrientedHomotopyEquiv_symm_mk (g : specialOrthogonalGroup (ι ⊕ ι) ℝ) :
    ((positivelyOrientedHomotopyEquiv ι).symm (QuotientGroup.mk g) :
      AlmostComplexStructure (StdSpace ι)) = g • stdComplexStructure ι := by
  rw [positivelyOrientedHomotopyEquiv, ContinuousMap.HomotopyEquiv.trans_symm_apply]
  exact (ContinuousMap.HomotopyEquiv.coe_ofWeakDeformationRetraction_apply ..).trans
    (coe_quotientUnitaryHomeomorph_mk g)

/-- Followed by `quotientUnitaryHomeomorph`, the homotopy equivalence
`positivelyOrientedHomotopyEquiv` sends a positively oriented structure to its polar
retraction. -/
@[simp]
theorem coe_quotientUnitaryHomeomorph_positivelyOrientedHomotopyEquiv
    (J : {J : AlmostComplexStructure (StdSpace ι) // IsPositivelyOriented J}) :
    (quotientUnitaryHomeomorph ι (positivelyOrientedHomotopyEquiv ι J) :
      AlmostComplexStructure (StdSpace ι)) = complexStructurePolarRetraction (ι ⊕ ι) J := by
  rw [positivelyOrientedHomotopyEquiv, ContinuousMap.HomotopyEquiv.trans_apply]
  exact (congrArg Subtype.val ((quotientUnitaryHomeomorph ι).apply_symm_apply _)).trans
    ((ContinuousMap.HomotopyEquiv.coe_ofWeakDeformationRetraction_symm_apply ..).trans
      ((complexStructurePolarHomotopy (ι ⊕ ι)).apply_one J))

end SymplecticGeometry

end
