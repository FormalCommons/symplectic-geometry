/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Topology.ComplexStructure.Orthogonal
public import TauCeti.Analysis.Matrix.EuclideanLin
public import TauCeti.Topology.Algebra.GroupAction.Transitive
public import TauCeti.Topology.Algebra.OrthogonalGroup
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Homotopy.Equiv
public import Mathlib.Topology.Homotopy.Path
public import SymplecticGeometry.Analysis.Quaternion
public import SymplecticGeometry.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.Homeomorph.Lemmas
public import TauCeti.Data.Fin.Sum
public import SymplecticGeometry.LinearAlgebra.ComplexStructure.Standard
import SymplecticGeometry.Topology.ComplexStructure.Orbit
import TauCeti.Geometry.Sphere.Connected
import TauCeti.Topology.PathComponent
import TauCeti.Geometry.Symplectic.Complex.InnerProductSpace
import TauCeti.Geometry.Symplectic.Complex.OrthonormalBasis
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Flat.TorsionFree

/-!
# The components of the space of complex structures, SO(2n)/U(n), and the case of ℝ⁴

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

In dimension four, identify `ℝ⁴` with the quaternions by `z ↦ x₁ + y₁ i + x₂ j + y₂ k`. Left
multiplication by a unit pure quaternion `u₀ i + u₁ j + u₂ k` is an orthogonal positively
oriented complex structure, and each such structure arises from exactly one unit vector
`u ∈ S²`: it is determined by its value on `x₁`, since on the plane orthogonal to `x₁` and
`J x₁` it is one of the two rotations by a right angle and the orientation selects one. So the
positively oriented structures on `ℝ⁴` have the homotopy type of `S²`.

The file ends with the classification theorem, which collects these results.

## Main definitions

* `SymplecticGeometry.positiveOrthogonalComplexStructures`: the orthogonal positively oriented
  complex structures, as a `SubMulAction` of `SO(2n)`.
* `SymplecticGeometry.quotientUnitaryHomeomorph`: the homeomorphism from
  `SO(2n) ⧸ stabilizer J₀` onto the orthogonal positively oriented complex structures.
* `SymplecticGeometry.positivelyOrientedHomotopyEquiv`: the positively oriented complex structures
  are homotopy equivalent to `SO(2n) ⧸ stabilizer J₀`.
* `SymplecticGeometry.stdSpaceQuaternionIsometry`: `StdSpace (Fin 2) = ℝ⁴` as the quaternions.
* `SymplecticGeometry.quaternionComplexStructure`: left multiplication by a unit pure quaternion,
  `Quaternion.pureOfEuclideanSpace u`.
* `SymplecticGeometry.sphereHomeomorphOrthogonal`: the orthogonal positively oriented complex
  structures on `ℝ⁴` form the sphere `S²`.
* `SymplecticGeometry.positivelyOrientedHomotopyEquivSphere`: the positively oriented complex
  structures on `ℝ⁴` are homotopy equivalent to `S²`.

## Main results

* `SymplecticGeometry.map_stabilizer_specialOrthogonalGroup_stdComplexStructure`: the stabilizer
  of `J₀` in `SO(2n)` is the realified unitary group `U(n)`.
* `SymplecticGeometry.exists_specialOrthogonalGroup_smul_stdComplexStructure_eq`: every orthogonal
  positively oriented structure is `g • J₀` for some `g ∈ SO(2n)`.
* `SymplecticGeometry.isPathConnected_setOfPred_isPositivelyOriented`,
  `SymplecticGeometry.connectedComponent_stdComplexStructure`: the positively oriented structures
  form the path-connected component of `J₀`;
  `SymplecticGeometry.pathComponent_stdComplexStructure` is its path-component form.
* `SymplecticGeometry.nat_card_connectedComponents_almostComplexStructure_stdSpace`: in positive
  dimension the complex structures of `StdSpace ι` have two components;
  `SymplecticGeometry.nat_card_connectedComponents_almostComplexStructure_stdSpace_of_isEmpty`:
  in dimension zero they have one.
* `SymplecticGeometry.eq_of_apply_eq_of_mem_positiveOrthogonalComplexStructures`: on `ℝ⁴`, an
  orthogonal positively oriented structure is determined by its value on one nonzero vector.
* `SymplecticGeometry.coe_positivelyOrientedHomotopyEquivSphere_symm_apply`,
  `SymplecticGeometry.quaternionComplexStructure_positivelyOrientedHomotopyEquivSphere`: the
  homotopy equivalence with `S²` sends `J` to the point of its polar retraction, and its inverse
  sends `u` to `quaternionComplexStructure u`.
* `SymplecticGeometry.complexStructures_classification`: every linear complex structure is
  standard, together with the topology of the space of complex structures on `ℝ²ⁿ`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Section 2.5, Propositions 2.5.1 and 2.5.2.
-/

public section

namespace SymplecticGeometry

open TauCeti AlmostComplexStructure Matrix Module
open scoped unitInterval ContinuousMap Quaternion

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
  obtain ⟨U, rfl⟩ := UnitaryGroup.toLinearIsometryEquiv.surjective Φ
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
    isClopen_setOfPred_isPositivelyOriented.preimage
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
    (isClopen_setOfPred_isPositivelyOriented.pathComponent_subset _
      isPositivelyOriented_stdComplexStructure)
    fun _ hJ ↦ IsPositivelyOriented.joined_stdComplexStructure hJ

/-- The positively oriented complex structures of `StdSpace ι` form a path-connected set. -/
theorem isPathConnected_setOfPred_isPositivelyOriented :
    IsPathConnected {J : AlmostComplexStructure (StdSpace ι) | IsPositivelyOriented J} := by
  rw [← pathComponent_stdComplexStructure]
  exact isPathConnected_pathComponent

/-- The connected component of `J₀` consists of the positively oriented complex structures. -/
theorem connectedComponent_stdComplexStructure :
    connectedComponent (stdComplexStructure ι) = {J | IsPositivelyOriented J} :=
  Set.Subset.antisymm
    ((isClopen_setOfPred_isPositivelyOriented (ι := ι)).connectedComponent_subset
      isPositivelyOriented_stdComplexStructure)
    (IsPreconnected.subset_connectedComponent
      (isPathConnected_setOfPred_isPositivelyOriented (ι := ι)).isConnected.isPreconnected
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

/-! ### Dimension four: quaternions -/

/-- The identification of `StdSpace (Fin 2) = ℝ⁴` with the quaternions,
`z ↦ x₁ + y₁ i + x₂ j + y₂ k`; under it `J₀` is left multiplication by `i`. -/
noncomputable def stdSpaceQuaternionIsometry : StdSpace (Fin 2) ≃ₗᵢ[ℝ] ℍ[ℝ] :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (TauCeti.finSumFinInterleaveEquiv 2)).trans
    Quaternion.linearIsometryEquivTuple.symm

/-- The coordinates of the vector of a quaternion `q`: `x₁ = re q`, `y₁ = imI q`, `x₂ = imJ q`
and `y₂ = imK q`. -/
@[simp]
theorem stdSpaceQuaternionIsometry_symm_apply (q : ℍ[ℝ]) (i : Fin 2 ⊕ Fin 2) :
    stdSpaceQuaternionIsometry.symm q i = Sum.elim ![q.re, q.imJ] ![q.imI, q.imK] i := by
  have hl (i : Fin 2) : TauCeti.finSumFinInterleaveEquiv 2 (.inl i) = ⟨2 * i, by omega⟩ :=
    Fin.ext (TauCeti.val_finSumFinInterleaveEquiv_inl i)
  have hr (i : Fin 2) : TauCeti.finSumFinInterleaveEquiv 2 (.inr i) = ⟨2 * i + 1, by omega⟩ :=
    Fin.ext (TauCeti.val_finSumFinInterleaveEquiv_inr i)
  rcases i with i | i <;> fin_cases i <;>
    simp [stdSpaceQuaternionIsometry, LinearIsometryEquiv.piLpCongrLeft_symm, hl, hr]

/-- The quaternion of `z ∈ StdSpace (Fin 2)` is `x₁ + y₁ i + x₂ j + y₂ k`. -/
@[simp]
theorem stdSpaceQuaternionIsometry_apply (z : StdSpace (Fin 2)) :
    stdSpaceQuaternionIsometry z = ⟨z (.inl 0), z (.inr 0), z (.inl 1), z (.inr 1)⟩ := by
  refine stdSpaceQuaternionIsometry.symm.injective (PiLp.ext fun i ↦ ?_)
  rcases i with i | i <;> fin_cases i <;> simp

/-- The complex structure on `ℝ⁴` given by a unit vector `u` of `ℝ³`: left multiplication by the
pure quaternion `u₀ i + u₁ j + u₂ k`, read through `stdSpaceQuaternionIsometry`. -/
noncomputable def quaternionComplexStructure (u : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    AlmostComplexStructure (StdSpace (Fin 2)) where
  toLinearMap := stdSpaceQuaternionIsometry.symm.toLinearMap ∘ₗ
    LinearMap.mulLeft ℝ (Quaternion.pureOfEuclideanSpace u) ∘ₗ
      stdSpaceQuaternionIsometry.toLinearMap
  square_neg := by
    ext z : 1
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toLinearEquiv,
      LinearMap.mulLeft_apply, LinearIsometryEquiv.apply_symm_apply, ← mul_assoc,
      Quaternion.pureOfEuclideanSpace_mul_self_of_norm_eq_one
        (mem_sphere_zero_iff_norm.1 u.property), neg_one_mul, map_neg,
      LinearIsometryEquiv.symm_apply_apply, LinearMap.neg_apply, LinearMap.id_apply]

/-- `quaternionComplexStructure u` is left multiplication by `u₀ i + u₁ j + u₂ k`. -/
@[simp]
theorem quaternionComplexStructure_apply (u : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (z : StdSpace (Fin 2)) :
    quaternionComplexStructure u z = stdSpaceQuaternionIsometry.symm
      (Quaternion.pureOfEuclideanSpace u * stdSpaceQuaternionIsometry z) :=
  (rfl)

/-- `quaternionComplexStructure u` sends the basis vector `x₁` to `u₀ y₁ + u₁ x₂ + u₂ y₂`. -/
theorem quaternionComplexStructure_apply_single
    (u : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    quaternionComplexStructure u (EuclideanSpace.single (.inl 0) 1) =
      (u : EuclideanSpace ℝ (Fin 3)) 0 • EuclideanSpace.single (.inr 0) 1 +
        (u : EuclideanSpace ℝ (Fin 3)) 1 • EuclideanSpace.single (.inl 1) 1 +
        (u : EuclideanSpace ℝ (Fin 3)) 2 • EuclideanSpace.single (.inr 1) 1 := by
  ext i <;> fin_cases i <;> simp [StdSpace.x_apply, StdSpace.y_apply]

/-- The quaternion structures are orthogonal: left multiplication by a unit quaternion is an
isometry. -/
theorem quaternionComplexStructure_mem_orthogonalComplexStructures
    (u : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    quaternionComplexStructure u ∈ orthogonalComplexStructures (Fin 2 ⊕ Fin 2) :=
  mem_orthogonalComplexStructures.2 fun z ↦ by
    rw [quaternionComplexStructure_apply, LinearIsometryEquiv.norm_map, norm_mul,
      LinearIsometry.norm_map, mem_sphere_zero_iff_norm.1 u.property, one_mul,
      LinearIsometryEquiv.norm_map]

/-- The quaternion structure depends continuously on the unit vector. -/
theorem continuous_quaternionComplexStructure : Continuous quaternionComplexStructure := by
  rw [AlmostComplexStructure.continuous_iff]
  have h : (fun u ↦ LinearMap.toContinuousLinearMap (quaternionComplexStructure u).toLinearMap) =
      fun u : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↦
        (stdSpaceQuaternionIsometry.symm.toContinuousLinearEquiv :
          ℍ[ℝ] →L[ℝ] StdSpace (Fin 2)).comp
        ((ContinuousLinearMap.mul ℝ ℍ[ℝ] (Quaternion.pureOfEuclideanSpace u)).comp
          (stdSpaceQuaternionIsometry.toContinuousLinearEquiv :
            StdSpace (Fin 2) →L[ℝ] ℍ[ℝ])) := by
    ext u z : 2
    simp only [LinearMap.coe_toContinuousLinearMap',
      quaternionComplexStructure_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      ContinuousLinearMap.mul_apply']
  rw [h]
  exact continuous_const.clm_comp (((ContinuousLinearMap.mul ℝ ℍ[ℝ]).continuous.comp
    (Quaternion.pureOfEuclideanSpace.continuous.comp continuous_subtypeVal)).clm_comp
      continuous_const)

/-- At the first basis vector `(1, 0, 0)` of `ℝ³`, the quaternion structure is `J₀`. -/
theorem quaternionComplexStructure_single_zero :
    quaternionComplexStructure ⟨EuclideanSpace.single 0 1, EuclideanSpace.single_one_mem_sphere 0⟩ =
      stdComplexStructure (Fin 2) := by
  ext z i <;> fin_cases i <;> simp [StdSpace.x_apply, StdSpace.y_apply]

/-- The quaternion structures are positively oriented: the first basis vector gives `J₀`, and the
sphere is connected. -/
theorem isPositivelyOriented_quaternionComplexStructure
    (u : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    IsPositivelyOriented (quaternionComplexStructure u) := by
  have := TauCeti.connectedSpace_euclideanSphere (ι := Fin 3) (by simp)
  have hc := (isClopen_setOfPred_isPositivelyOriented (ι := Fin 2)).preimage
    continuous_quaternionComplexStructure
  have hu := hc.eq_univ ⟨_, by
    rw [Set.mem_preimage, quaternionComplexStructure_single_zero]
    exact isPositivelyOriented_stdComplexStructure⟩
  exact (Set.ext_iff.1 hu u).2 trivial

/-- Two orthogonal positively oriented complex structures on `ℝ⁴` that agree on one nonzero
vector are equal. -/
theorem eq_of_apply_eq_of_mem_positiveOrthogonalComplexStructures
    {J J' : AlmostComplexStructure (StdSpace (Fin 2))}
    (hJ : J ∈ positiveOrthogonalComplexStructures (Fin 2))
    (hJ' : J' ∈ positiveOrthogonalComplexStructures (Fin 2)) {ξ : StdSpace (Fin 2)} (hξ : ξ ≠ 0)
    (h : J ξ = J' ξ) : J = J' := by
  have : Fact (finrank ℝ (StdSpace (Fin 2)) = 4) := ⟨by simp⟩
  have hk : finrank ℝ (StdSpace (Fin 2)) = 4 := Fact.out
  have hi := mem_orthogonalComplexStructures_iff_inner.1 hJ.1
  have hi' := mem_orthogonalComplexStructures_iff_inner.1 hJ'.1
  obtain ⟨e, he0, h0, h2⟩ := exists_unitary_orthonormalBasis_of_norm_eq_one hi
    (ξ := ‖ξ‖⁻¹ • ξ) (by simp [norm_smul, hξ])
  have h0' : J' (e 0) = e 1 := by rw [← h0, he0, J.apply_smul, J'.apply_smul, h]
  have ho {i j : Fin 4} (hij : i ≠ j) : inner ℝ (e i) (e j) = 0 := e.orthonormal.2 hij
  -- `J' (e 2)` is a unit vector orthogonal to `e 0`, `e 1` and `e 2`, so it is `± e 3`.
  have a0 : inner ℝ (e 0) (J' (e 2)) = 0 := by
    have := J'.bilinForm_apply_left_eq_neg_apply_right (g := innerₗ _) hi' (e 0) (e 2)
    simp only [innerₗ_apply_apply, h0', ho (show (1 : Fin 4) ≠ 2 by decide)] at this
    linarith
  have a1 : inner ℝ (e 1) (J' (e 2)) = 0 := by
    rw [← h0', hi']
    exact ho (by decide)
  have a2 : inner ℝ (e 2) (J' (e 2)) = 0 := J'.inner_self_apply hi' _
  have hv : J' (e 2) = inner ℝ (e 3) (J' (e 2)) • e 3 := by
    have := e.sum_repr' (J' (e 2))
    rw [Fin.sum_univ_four, a0, a1, a2] at this
    simpa using this.symm
  have hc : |inner ℝ (e 3) (J' (e 2))| = 1 := by
    have := congrArg norm hv
    rwa [J'.norm_apply hi', e.orthonormal.1, norm_smul, e.orthonormal.1, mul_one,
      Real.norm_eq_abs, eq_comm] at this
  rcases (abs_eq zero_le_one).1 hc with hc | hc
  · refine AlmostComplexStructure.toLinearMap_injective (e.toBasis.ext fun i ↦ ?_)
    rw [hc, one_smul] at hv
    have h3 : J (e 3) = J' (e 3) := by rw [← h2, J.apply_apply, h2, ← hv, J'.apply_apply]
    have h1 : J (e 1) = J' (e 1) := by rw [← h0, J.apply_apply, h0, ← h0', J'.apply_apply]
    fin_cases i
    · exact h0.trans h0'.symm
    · exact h1
    · exact h2.trans hv.symm
    · exact h3
  · -- With `J' (e 2) = -e 3`, the adapted bases of `J` and `J'` built from `e` would have
    -- opposite orientations, but both induce the symplectic orientation.
    exfalso
    rw [hc, neg_one_smul] at hv
    have hre (c : Module.Basis (Fin 4) ℝ (StdSpace (Fin 2))) :
        (c.reindex (finProdFinEquiv (m := 2) (n := 2)).symm).reindex
          (finProdFinEquiv.trans (finCongr rfl)) = c :=
      Module.Basis.eq_of_apply_eq fun i ↦ by simp
    have o := (isPositivelyOriented_iff_orientation hk J).1 hJ.2
      (e.toBasis.reindex (finProdFinEquiv (m := 2) (n := 2)).symm)
      (fun i ↦ by fin_cases i <;> simp [finProdFinEquiv, h0, h2]) rfl
    have o' := (isPositivelyOriented_iff_orientation hk J').1 hJ'.2
      ((e.toBasis.unitsSMul ![1, 1, 1, -1]).reindex (finProdFinEquiv (m := 2) (n := 2)).symm)
      (fun i ↦ by
        fin_cases i <;> simp [finProdFinEquiv, Module.Basis.unitsSMul_apply, h0', hv]) rfl
    rw [hre] at o o'
    rw [Module.Basis.orientation_unitsSMul, o] at o'
    norm_num [Fin.prod_univ_four] at o'

/-- The value `J x₁` of an orthogonal structure is a unit vector orthogonal to `x₁`. -/
private theorem apply_single_of_mem_orthogonalComplexStructures
    {J : AlmostComplexStructure (StdSpace (Fin 2))}
    (hJ : J ∈ orthogonalComplexStructures (Fin 2 ⊕ Fin 2)) :
    J (EuclideanSpace.single (.inl 0) 1) (.inl 0) = 0 ∧
      J (EuclideanSpace.single (.inl 0) 1) (.inr 0) ^ 2 +
        J (EuclideanSpace.single (.inl 0) 1) (.inl 1) ^ 2 +
        J (EuclideanSpace.single (.inl 0) 1) (.inr 1) ^ 2 = 1 := by
  have hi := mem_orthogonalComplexStructures_iff_inner.1 hJ
  have h0 : J (EuclideanSpace.single (.inl 0) 1) (.inl 0) = 0 := by
    simpa [EuclideanSpace.inner_single_right] using J.inner_apply_self hi
      (EuclideanSpace.single (.inl 0) 1)
  refine ⟨h0, ?_⟩
  have := congrArg (· ^ 2) (J.norm_apply hi (EuclideanSpace.single (.inl 0) 1))
  simp [EuclideanSpace.real_norm_sq_eq, Fintype.sum_sum_type, Fin.sum_univ_two, h0] at this
  linarith

/-- **The orthogonal positively oriented complex structures on `ℝ⁴` form a 2-sphere**: a unit
vector `u` of `ℝ³` gives left multiplication by the pure quaternion `u₀ i + u₁ j + u₂ k`, and a
structure `J` gives back the imaginary part of the quaternion of `J x₁`. -/
noncomputable def sphereHomeomorphOrthogonal :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ≃ₜ positiveOrthogonalComplexStructures (Fin 2)
    where
  toFun u := ⟨quaternionComplexStructure u,
    quaternionComplexStructure_mem_orthogonalComplexStructures u,
    isPositivelyOriented_quaternionComplexStructure u⟩
  invFun J := ⟨!₂[(stdSpaceQuaternionIsometry (J.val (EuclideanSpace.single (.inl 0) 1))).imI,
      (stdSpaceQuaternionIsometry (J.val (EuclideanSpace.single (.inl 0) 1))).imJ,
      (stdSpaceQuaternionIsometry (J.val (EuclideanSpace.single (.inl 0) 1))).imK], by
    rw [mem_sphere_zero_iff_norm, ← sq_eq_sq₀ (norm_nonneg _) zero_le_one,
      EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
    simpa using (apply_single_of_mem_orthogonalComplexStructures J.property.1).2⟩
  left_inv u := by
    ext i
    fin_cases i <;> simp
  right_inv J := by
    refine Subtype.ext (eq_of_apply_eq_of_mem_positiveOrthogonalComplexStructures
      ⟨quaternionComplexStructure_mem_orthogonalComplexStructures _,
        isPositivelyOriented_quaternionComplexStructure _⟩ J.property
      (ξ := EuclideanSpace.single (.inl 0) 1) (by simp) ?_)
    have h0 := (apply_single_of_mem_orthogonalComplexStructures J.property.1).1
    ext i <;> fin_cases i <;>
      simp [StdSpace.x_apply, StdSpace.y_apply, h0]
  continuous_toFun := continuous_quaternionComplexStructure.subtype_mk _
  continuous_invFun := by
    have h : Continuous fun J : positiveOrthogonalComplexStructures (Fin 2) ↦
        stdSpaceQuaternionIsometry (J.val (EuclideanSpace.single (.inl 0) 1)) :=
      stdSpaceQuaternionIsometry.continuous.comp
        ((AlmostComplexStructure.isEmbedding_toContinuousLinearMap.continuous.comp
          continuous_subtypeVal).clm_apply continuous_const)
    refine Continuous.subtype_mk ((PiLp.continuous_toLp _ _).comp (continuous_pi fun i ↦ ?_)) _
    fin_cases i
    · exact Quaternion.continuous_imI.comp h
    · exact Quaternion.continuous_imJ.comp h
    · exact Quaternion.continuous_imK.comp h

/-- `sphereHomeomorphOrthogonal` sends `u` to `quaternionComplexStructure u`. -/
@[simp]
theorem sphereHomeomorphOrthogonal_apply (u : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    (sphereHomeomorphOrthogonal u : AlmostComplexStructure (StdSpace (Fin 2))) =
      quaternionComplexStructure u :=
  (rfl)

/-- The inverse of `sphereHomeomorphOrthogonal` sends `J` to the imaginary part of the quaternion
of `J x₁`. -/
theorem sphereHomeomorphOrthogonal_symm_apply
    (J : positiveOrthogonalComplexStructures (Fin 2)) :
    (sphereHomeomorphOrthogonal.symm J : EuclideanSpace ℝ (Fin 3)) =
      !₂[(stdSpaceQuaternionIsometry (J.val (EuclideanSpace.single (.inl 0) 1))).imI,
        (stdSpaceQuaternionIsometry (J.val (EuclideanSpace.single (.inl 0) 1))).imJ,
        (stdSpaceQuaternionIsometry (J.val (EuclideanSpace.single (.inl 0) 1))).imK] :=
  (rfl)

/-- **The positively oriented complex structures on `ℝ⁴` have the homotopy type of the
2-sphere**: the polar deformation retracts them onto the orthogonal ones, which form a 2-sphere
by `sphereHomeomorphOrthogonal`. -/
noncomputable def positivelyOrientedHomotopyEquivSphere :
    {J : AlmostComplexStructure (StdSpace (Fin 2)) // IsPositivelyOriented J} ≃ₕ
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
  (positivelyOrientedHomotopyEquiv (Fin 2)).trans
    ((quotientUnitaryHomeomorph (Fin 2)).trans sphereHomeomorphOrthogonal.symm).toHomotopyEquiv

/-- The homotopy inverse of `positivelyOrientedHomotopyEquivSphere` sends `u` to
`quaternionComplexStructure u`. -/
@[simp]
theorem coe_positivelyOrientedHomotopyEquivSphere_symm_apply
    (u : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    (positivelyOrientedHomotopyEquivSphere.symm u : AlmostComplexStructure (StdSpace (Fin 2))) =
      quaternionComplexStructure u := by
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective
    ((quotientUnitaryHomeomorph (Fin 2)).symm (sphereHomeomorphOrthogonal u))
  rw [positivelyOrientedHomotopyEquivSphere, ContinuousMap.HomotopyEquiv.trans_symm_apply,
    ← Homeomorph.symm_toHomotopyEquiv, Homeomorph.coe_toHomotopyEquiv, Homeomorph.symm_trans_apply,
    Homeomorph.symm_symm,
    ← hg, coe_positivelyOrientedHomotopyEquiv_symm_mk, ← coe_quotientUnitaryHomeomorph_mk, hg,
    Homeomorph.apply_symm_apply, sphereHomeomorphOrthogonal_apply]

/-- The quaternionic complex structure of the point `positivelyOrientedHomotopyEquivSphere J` of
the sphere is the polar retraction of `J`. -/
@[simp]
theorem quaternionComplexStructure_positivelyOrientedHomotopyEquivSphere
    (J : {J : AlmostComplexStructure (StdSpace (Fin 2)) // IsPositivelyOriented J}) :
    quaternionComplexStructure (positivelyOrientedHomotopyEquivSphere J) =
      complexStructurePolarRetraction (Fin 2 ⊕ Fin 2) J := by
  rw [← sphereHomeomorphOrthogonal_apply, positivelyOrientedHomotopyEquivSphere,
    ContinuousMap.HomotopyEquiv.trans_apply, Homeomorph.coe_toHomotopyEquiv, Homeomorph.trans_apply,
    Homeomorph.apply_symm_apply, coe_quotientUnitaryHomeomorph_positivelyOrientedHomotopyEquiv]

/-! ### The classification of linear complex structures -/

universe u in
/-- **Linear complex structures are standard.** For every `n`:
* every complex structure on a real vector space `V` of dimension `2n` is the transport of `J₀`
  along a linear isomorphism `ℝ²ⁿ ≃ V`;
* the complex structures of `ℝ²ⁿ` form the homogeneous space `GL(2n, ℝ)/GL(n, ℂ)`;
* for `n ≠ 0` they have two connected components (for `n = 0` there is a single one, by
  `nat_card_connectedComponents_almostComplexStructure_stdSpace_of_isEmpty`, which this theorem
  does not restate);
* the component of `J₀` consists of the structures whose adapted bases
  `(v₁, J v₁, …, vₙ, J vₙ)` induce the symplectic orientation of `ω₀`;
* the stabilizer of `J₀` in `SO(2n)` is the realified unitary group `U(n)`;
* the component of `J₀` is homotopy equivalent to `SO(2n)/U(n)`;
* for `n = 2` it is homotopy equivalent to the 2-sphere.

Milestone: *Linear complex structures are standard*. -/
theorem complexStructures_classification (n : ℕ) :
    (∀ (V : Type u) [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
        (J : AlmostComplexStructure V), finrank ℝ V = 2 * n →
        ∃ Φ : StdSpace (Fin n) ≃ₗ[ℝ] V, (stdComplexStructure (Fin n)).transport Φ = J) ∧
    Nonempty (GL (Fin n ⊕ Fin n) ℝ ⧸ (Matrix.GeneralLinearGroup.realify (Fin n) ℂ).range ≃ₜ
        AlmostComplexStructure (StdSpace (Fin n))) ∧
    (n ≠ 0 → Nat.card (ConnectedComponents (AlmostComplexStructure (StdSpace (Fin n)))) = 2) ∧
    (∀ (hk : finrank ℝ (StdSpace (Fin n)) = n * 2) J,
        J ∈ connectedComponent (stdComplexStructure (Fin n)) ↔
        ∀ (b : Module.Basis (Fin n × Fin 2) ℝ (StdSpace (Fin n)))
          (_ : ∀ i, b (i, 1) = J (b (i, 0))),
          (b.reindex finProdFinEquiv).orientation = (stdForm (Fin n)).orientation hk) ∧
    (MulAction.stabilizer (specialOrthogonalGroup (Fin n ⊕ Fin n) ℝ)
        (stdComplexStructure (Fin n))).toSubmonoid.map
        (specialOrthogonalGroup (Fin n ⊕ Fin n) ℝ).subtype =
      (Matrix.unitaryGroup (Fin n) ℂ).map (Matrix.realifyAlgHom (Fin n) ℂ) ∧
    Nonempty (connectedComponent (stdComplexStructure (Fin n)) ≃ₕ
        specialOrthogonalGroup (Fin n ⊕ Fin n) ℝ ⧸
          MulAction.stabilizer (specialOrthogonalGroup (Fin n ⊕ Fin n) ℝ)
            (stdComplexStructure (Fin n))) ∧
    Nonempty (connectedComponent (stdComplexStructure (Fin 2)) ≃ₕ
        Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) := by
  refine ⟨fun V _ _ _ J hV ↦ exists_transport_stdComplexStructure_eq J (by simpa using hV),
    ⟨quotientRealifyHomeomorph (Fin n)⟩, fun hn ↦ ?_, fun hk J ↦ ?_,
    map_stabilizer_specialOrthogonalGroup_stdComplexStructure (Fin n),
    ⟨(Homeomorph.setCongr (connectedComponent_stdComplexStructure (ι := Fin n)))
        |>.toHomotopyEquiv.trans
      (positivelyOrientedHomotopyEquiv (Fin n))⟩,
    ⟨(Homeomorph.setCongr (connectedComponent_stdComplexStructure (ι := Fin 2)))
        |>.toHomotopyEquiv.trans
      positivelyOrientedHomotopyEquivSphere⟩⟩
  · have : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
    exact nat_card_connectedComponents_almostComplexStructure_stdSpace
  · rw [connectedComponent_stdComplexStructure, Set.mem_ofPred_eq,
      isPositivelyOriented_iff_orientation hk]
    refine ⟨fun H b hb ↦ by simpa using H b hb rfl, fun H m b hb h ↦ ?_⟩
    obtain rfl : m = n := by omega
    simpa using H b hb

end SymplecticGeometry

end
