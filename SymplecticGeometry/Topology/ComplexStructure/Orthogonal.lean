/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Analysis.Matrix.Polar.Deformation
public import SymplecticGeometry.LinearAlgebra.Symplectic.Standard.Basic
public import SymplecticGeometry.Topology.ComplexStructure.Basic
public import TauCeti.Topology.Algebra.UnitaryGroup
public import TauCeti.Topology.Homotopy.DeformationRetract

/-!
# The orthogonal complex structures

A complex structure `J` on `StdSpace ι = ℝ²ⁿ` is *orthogonal* if it preserves the Euclidean norm,
equivalently the inner product, equivalently if its matrix is orthogonal. The orthogonal
complex structures form a compact set, and a strong deformation retract of the space of all
complex structures.

The deformation is the polar deformation of the matrix of `J`: if `A = P U` with `P = √(A Aᵀ)`
and `U` orthogonal, then `P ^ (1 - t) U` has square `-1` for every `t`
(`Matrix.GeneralLinearGroup.polarDeformation_mul_self_of_mul_self_eq_neg_one`), it is `A` at
`t = 0`, the orthogonal factor `U` at `t = 1`, and it does not move orthogonal matrices.

## Main definitions

* `SymplecticGeometry.orthogonalComplexStructures ι`: the complex structures of `StdSpace ι`
  that preserve the norm.
* `SymplecticGeometry.complexStructurePolarRetraction ι`: the retraction sending `J` to the
  structure of the orthogonal polar factor of its matrix.
* `SymplecticGeometry.complexStructurePolarHomotopy ι`: the polar deformation, a homotopy from
  the identity to the retraction that fixes the orthogonal structures.
* `SymplecticGeometry.orthogonalComplexStructuresHomotopyEquiv ι`: the inclusion of the
  orthogonal structures is a homotopy equivalence.

## Main results

* `SymplecticGeometry.mem_orthogonalComplexStructures_iff_inner`,
  `SymplecticGeometry.mem_orthogonalComplexStructures_iff_mem_orthogonalGroup`: orthogonality in
  terms of the inner product and of the matrix.
* `SymplecticGeometry.isCompact_orthogonalComplexStructures`: the orthogonal structures form a
  compact set.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Section 2.5, Proposition 2.5.2.
-/

public section

namespace SymplecticGeometry

open TauCeti AlmostComplexStructure Matrix.GeneralLinearGroup
open scoped InnerProductSpace unitInterval MatrixOrder ContinuousMap

variable (ι : Type*) [Fintype ι]

/-- The complex structures of `StdSpace ι` compatible with the Euclidean metric: those that
preserve the norm. -/
def orthogonalComplexStructures : Set (AlmostComplexStructure (StdSpace ι)) :=
  {J | ∀ v, ‖J v‖ = ‖v‖}

variable {ι}

/-- A complex structure is orthogonal exactly when it preserves the norm. -/
theorem mem_orthogonalComplexStructures {J : AlmostComplexStructure (StdSpace ι)} :
    J ∈ orthogonalComplexStructures ι ↔ ∀ v, ‖J v‖ = ‖v‖ :=
  (Iff.rfl)

/-- A complex structure is orthogonal exactly when it preserves the inner product. -/
theorem mem_orthogonalComplexStructures_iff_inner {J : AlmostComplexStructure (StdSpace ι)} :
    J ∈ orthogonalComplexStructures ι ↔ ∀ v w, ⟪J v, J w⟫_ℝ = ⟪v, w⟫_ℝ :=
  LinearMap.norm_map_iff_inner_map_map J.toLinearMap

/-- The standard complex structure `J₀` is orthogonal. -/
@[simp]
theorem stdComplexStructure_mem_orthogonalComplexStructures :
    stdComplexStructure ι ∈ orthogonalComplexStructures ι :=
  mem_orthogonalComplexStructures_iff_inner.2 fun v w ↦ by
    rw [← stdForm_apply_eq_inner, stdForm_apply_stdComplexStructure]

variable [DecidableEq ι] in
/-- A complex structure is orthogonal exactly when its matrix is orthogonal. -/
theorem mem_orthogonalComplexStructures_iff_mem_orthogonalGroup
    {J : AlmostComplexStructure (StdSpace ι)} :
    J ∈ orthogonalComplexStructures ι ↔
      (homeomorphMatrix (ι ⊕ ι) J : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) ∈
        Matrix.orthogonalGroup (ι ⊕ ι) ℝ := by
  rw [mem_orthogonalComplexStructures_iff_inner,
    Matrix.mem_unitaryGroup_iff_inner_toEuclideanCLM, homeomorphMatrix_apply_coe,
    StarAlgEquiv.apply_symm_apply]
  rfl

/-- The orthogonal complex structures form a compact set. -/
theorem isCompact_orthogonalComplexStructures :
    IsCompact (orthogonalComplexStructures ι) := by
  classical
  have h : orthogonalComplexStructures ι = homeomorphMatrix (ι ⊕ ι) ⁻¹'
      (Subtype.val ⁻¹' (Matrix.orthogonalGroup (ι ⊕ ι) ℝ : Set (Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ))) :=
    Set.ext fun _ ↦ mem_orthogonalComplexStructures_iff_mem_orthogonalGroup
  have hclosed : IsClosed {A : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ | A * A = -1} :=
    isClosed_eq (continuous_id.mul continuous_id) continuous_const
  rw [h, Homeomorph.isCompact_preimage]
  exact hclosed.isClosedEmbedding_subtypeVal.isCompact_preimage
    TauCeti.Matrix.isCompact_unitaryGroup

variable [DecidableEq ι]

/-- The complex structure of the polar deformation at time `t` of the matrix of `J`. -/
private noncomputable def polarDeformationAux (t : ℝ) (J : AlmostComplexStructure (StdSpace ι)) :
    AlmostComplexStructure (StdSpace ι) :=
  (homeomorphMatrix (ι ⊕ ι)).symm
    ⟨polarDeformation J.toGeneralLinearGroup t,
      polarDeformation_mul_self_of_mul_self_eq_neg_one
        (by simpa using (homeomorphMatrix (ι ⊕ ι) J).property) t⟩

private theorem homeomorphMatrix_polarDeformationAux (t : ℝ)
    (J : AlmostComplexStructure (StdSpace ι)) :
    (homeomorphMatrix (ι ⊕ ι) (polarDeformationAux t J) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) =
      polarDeformation J.toGeneralLinearGroup t := by
  rw [polarDeformationAux, Homeomorph.apply_symm_apply]

private theorem continuous_polarDeformationAux :
    Continuous fun p : I × AlmostComplexStructure (StdSpace ι) ↦
      polarDeformationAux (p.1 : ℝ) p.2 := by
  have hA : Continuous fun p : I × AlmostComplexStructure (StdSpace ι) ↦
      polarDeformation p.2.toGeneralLinearGroup (p.1 : ℝ) :=
    ((polarHomotopy (ι ⊕ ι) ℝ).continuous.comp
      (continuous_fst.prodMk (continuous_toGeneralLinearGroup.comp continuous_snd))).congr
      fun p ↦ polarHomotopy_apply p.1 _
  rw [← (homeomorphMatrix (ι ⊕ ι)).comp_continuous_iff,
    Topology.IsEmbedding.subtypeVal.continuous_iff]
  exact (Units.continuous_val.comp hA).congr fun p ↦
    (homeomorphMatrix_polarDeformationAux _ p.2).symm

private theorem polarDeformationAux_zero (J : AlmostComplexStructure (StdSpace ι)) :
    polarDeformationAux 0 J = J := by
  refine (homeomorphMatrix (ι ⊕ ι)).injective <| Subtype.ext ?_
  rw [homeomorphMatrix_polarDeformationAux, polarDeformation_zero, coe_toGeneralLinearGroup]

private theorem polarDeformationAux_of_mem {J : AlmostComplexStructure (StdSpace ι)}
    (hJ : J ∈ orthogonalComplexStructures ι) (t : ℝ) :
    polarDeformationAux t J = J := by
  rw [mem_orthogonalComplexStructures_iff_mem_orthogonalGroup] at hJ
  have hU : J.toGeneralLinearGroup = Unitary.toUnits ⟨_, hJ⟩ := Units.ext (by simp)
  refine (homeomorphMatrix (ι ⊕ ι)).injective <| Subtype.ext ?_
  rw [homeomorphMatrix_polarDeformationAux, hU, polarDeformation_toUnits]
  simp

private theorem polarDeformationAux_one_mem (J : AlmostComplexStructure (StdSpace ι)) :
    polarDeformationAux 1 J ∈ orthogonalComplexStructures ι := by
  rw [mem_orthogonalComplexStructures_iff_mem_orthogonalGroup,
    homeomorphMatrix_polarDeformationAux, polarDeformation_one]
  exact (J.toGeneralLinearGroup.polarUnitary).property

variable (ι)

/-- The polar retraction of the complex structures of `StdSpace ι` onto the orthogonal ones: `J`
goes to the structure whose matrix is the orthogonal factor `U` of the polar decomposition
`A = √(A Aᵀ) U` of the matrix `A` of `J`. -/
noncomputable def complexStructurePolarRetraction :
    C(AlmostComplexStructure (StdSpace ι), orthogonalComplexStructures ι) where
  toFun J := ⟨polarDeformationAux 1 J, polarDeformationAux_one_mem J⟩
  continuous_toFun := (continuous_polarDeformationAux.comp
    (continuous_const.prodMk continuous_id :
      Continuous fun J : AlmostComplexStructure (StdSpace ι) ↦ ((1 : I), J))).subtype_mk _

variable {ι}

/-- The polar retraction fixes the orthogonal complex structures. -/
theorem complexStructurePolarRetraction_of_mem {J : AlmostComplexStructure (StdSpace ι)}
    (hJ : J ∈ orthogonalComplexStructures ι) :
    (complexStructurePolarRetraction ι J : AlmostComplexStructure (StdSpace ι)) = J :=
  polarDeformationAux_of_mem hJ 1

variable (ι)

/-- **The orthogonal complex structures are a strong deformation retract** of all complex
structures of `StdSpace ι`: at time `t`, the polar deformation sends `J` to the structure of
matrix `P ^ (1 - t) U`, where `A = P U` is the polar decomposition of the matrix `A` of `J`. It
starts at the identity, ends at the polar retraction, and fixes the orthogonal structures. -/
noncomputable def complexStructurePolarHomotopy :
    (ContinuousMap.id _).HomotopyRel
      ((ContinuousMap.subtypeVal _).comp (complexStructurePolarRetraction ι))
      (orthogonalComplexStructures ι) where
  toFun p := polarDeformationAux (p.1 : ℝ) p.2
  continuous_toFun := continuous_polarDeformationAux
  map_zero_left := polarDeformationAux_zero
  map_one_left _ := rfl
  prop' t _ hJ := polarDeformationAux_of_mem hJ t

variable {ι}

/-- The matrix of the polar homotopy at time `t` and structure `J` is the polar deformation at
time `t` of the matrix of `J`. -/
theorem complexStructurePolarHomotopy_apply (t : I) (J : AlmostComplexStructure (StdSpace ι)) :
    (homeomorphMatrix (ι ⊕ ι) (complexStructurePolarHomotopy ι (t, J)) :
        Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) =
      polarDeformation J.toGeneralLinearGroup t :=
  homeomorphMatrix_polarDeformationAux _ J

/-- The matrix of the polar retraction of `J` is the orthogonal polar factor of the matrix
of `J`. -/
theorem complexStructurePolarRetraction_apply (J : AlmostComplexStructure (StdSpace ι)) :
    (homeomorphMatrix (ι ⊕ ι) (complexStructurePolarRetraction ι J) :
        Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) =
      J.toGeneralLinearGroup.polarUnitary := by
  have h := (complexStructurePolarHomotopy ι).apply_one J
  rw [ContinuousMap.comp_apply, ContinuousMap.subtypeVal_apply] at h
  rw [← h, complexStructurePolarHomotopy_apply, Set.Icc.coe_one, polarDeformation_one,
    Unitary.val_toUnits_apply]

variable (ι)

/-- The inclusion of the orthogonal complex structures of `StdSpace ι` into all complex
structures is a homotopy equivalence, with homotopy inverse the polar retraction. -/
noncomputable def orthogonalComplexStructuresHomotopyEquiv :
    orthogonalComplexStructures ι ≃ₕ AlmostComplexStructure (StdSpace ι) :=
  ContinuousMap.HomotopyEquiv.ofDeformationRetraction (ContinuousMap.subtypeVal _)
    (complexStructurePolarRetraction ι)
    (fun J ↦ Subtype.ext (complexStructurePolarRetraction_of_mem J.property))
    ⟨(complexStructurePolarHomotopy ι).toHomotopy.symm⟩

end SymplecticGeometry

end
