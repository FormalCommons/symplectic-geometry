/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Matrix.UnitaryGroup.Torus
public import TauCeti.LinearAlgebra.Matrix.UnitaryGroup.Block
public import TauCeti.Topology.Algebra.Matrix.UnitaryGroup

/-!
# The determinant of the unitary group and a retraction onto the special unitary group

Facts about Tau Ceti's determinant `Matrix.UnitaryGroup.detCircle : U(ι) → S¹` on the complex
unitary group `U(ι) = Matrix.unitaryGroup ι ℂ`: it is unchanged by the block embedding
`B ↦ diag(1, B)` and by reindexing, and it has a continuous homomorphic section
`z ↦ diag(1, …, z, …, 1)`, with `z` in a chosen position `i₀`.

Dividing by this section gives a continuous retraction of `U(ι)` onto the special unitary group
`SU(ι) = Matrix.specialUnitaryGroup ι ℂ`, `A ↦ A · diag(1, …, (det A)⁻¹, …, 1)`.

## Main definitions

* `Matrix.UnitaryGroup.detSection`: the homomorphism `S¹ → U(ι)`, `z ↦ diag(1, …, z, …, 1)`, a
  section of `detCircle`.
* `Matrix.UnitaryGroup.toSpecialUnitary`: the retraction `U(ι) → SU(ι)`.

## Main results

* `Matrix.UnitaryGroup.detCircle_detSection`: `detSection` is a section of the determinant.
* `Matrix.UnitaryGroup.toSpecialUnitary_inclusion`: the retraction is the identity on `SU(ι)`.
* `Matrix.UnitaryGroup.continuous_toSpecialUnitary`: the retraction is continuous.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Proposition 2.2.6.
-/

public section

open TauCeti

namespace Matrix.UnitaryGroup

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The determinant of a block-diagonal unitary matrix `diag(1_r, B)` is that of `B`. -/
@[simp]
theorem detCircle_fromBlocksOne (r : ℕ) {m : ℕ} (B : unitaryGroup (Fin m) ℂ) :
    detCircle (fromBlocksOne ℂ r m B) = detCircle B := by
  refine Circle.ext ?_
  rw [coe_detCircle, coe_detCircle, coe_fromBlocksOne, det_reindex_self, det_fromBlocks_zero₂₁,
    det_one, one_mul]

/-- Reindexing a unitary matrix does not change its determinant. -/
@[simp]
theorem detCircle_unitaryReindexContinuousMulEquiv {κ : Type*} [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) (U : unitaryGroup ι ℂ) :
    detCircle (unitaryReindexContinuousMulEquiv ℂ e U) = detCircle U := by
  refine Circle.ext ?_
  rw [coe_detCircle, coe_detCircle, coe_unitaryReindexContinuousMulEquiv_apply, det_reindex_self]

/-- A special unitary matrix has determinant `1`. -/
@[simp]
theorem detCircle_inclusion_specialUnitaryGroup (A : specialUnitaryGroup ι ℂ) :
    detCircle (Submonoid.inclusion specialUnitaryGroup_le_unitaryGroup A) = 1 :=
  Circle.ext (by simpa using (mem_specialUnitaryGroup_iff.1 A.property).2)

variable (ι) in
/-- The section `S¹ → U(ι)` of the determinant that sends `z` to the diagonal matrix
`diag(1, …, z, …, 1)`, with `z` in position `i₀`. -/
noncomputable def detSection (i₀ : ι) : Circle →* unitaryGroup ι ℂ :=
  (unitaryTorusHom ι).comp (MonoidHom.mulSingle (fun _ : ι ↦ Circle) i₀)

theorem detSection_apply (i₀ : ι) (z : Circle) :
    detSection ι i₀ z = unitaryTorusHom ι (Pi.mulSingle i₀ z) :=
  (rfl)

@[simp]
theorem coe_detSection (i₀ : ι) (z : Circle) :
    (detSection ι i₀ z : Matrix ι ι ℂ) =
      diagonal fun i ↦ ((Pi.mulSingle i₀ z : ι → Circle) i : ℂ) := by
  rw [detSection_apply, coe_unitaryTorusHom]

theorem continuous_detSection (i₀ : ι) : Continuous (detSection ι i₀) :=
  continuous_unitaryTorusHom.comp (continuous_mulSingle (A := fun _ : ι ↦ Circle) i₀)

/-- `detSection` is a section of the determinant. -/
@[simp]
theorem detCircle_detSection (i₀ : ι) (z : Circle) : detCircle (detSection ι i₀ z) = z := by
  refine Circle.ext ?_
  rw [coe_detCircle, coe_detSection, det_diagonal,
    Finset.prod_eq_single i₀ (fun i _ hi ↦ by simp [Pi.mulSingle_eq_of_ne hi]) (by simp)]
  simp

/-- The retraction `U(ι) → SU(ι)`, `A ↦ A · diag(1, …, (det A)⁻¹, …, 1)`, with the correcting
entry in position `i₀`. -/
noncomputable def toSpecialUnitary (i₀ : ι) (A : unitaryGroup ι ℂ) :
    specialUnitaryGroup ι ℂ :=
  ⟨(A * detSection ι i₀ (detCircle A)⁻¹ : unitaryGroup ι ℂ),
    mem_specialUnitaryGroup_iff.2 ⟨(A * detSection ι i₀ (detCircle A)⁻¹).property, by
      rw [← coe_detCircle, map_mul, detCircle_detSection, mul_inv_cancel, Circle.coe_one]⟩⟩

@[simp]
theorem inclusion_toSpecialUnitary (i₀ : ι) (A : unitaryGroup ι ℂ) :
    Submonoid.inclusion specialUnitaryGroup_le_unitaryGroup (toSpecialUnitary i₀ A) =
      A * detSection ι i₀ (detCircle A)⁻¹ :=
  (rfl)

@[simp]
theorem coe_toSpecialUnitary (i₀ : ι) (A : unitaryGroup ι ℂ) :
    (toSpecialUnitary i₀ A : Matrix ι ι ℂ) =
      (A : Matrix ι ι ℂ) * (detSection ι i₀ (detCircle A)⁻¹ : Matrix ι ι ℂ) :=
  (rfl)

/-- The retraction `toSpecialUnitary` is the identity on `SU(ι)`. -/
@[simp]
theorem toSpecialUnitary_inclusion (i₀ : ι) (A : specialUnitaryGroup ι ℂ) :
    toSpecialUnitary i₀ (Submonoid.inclusion specialUnitaryGroup_le_unitaryGroup A) = A := by
  ext : 1
  simp

theorem continuous_toSpecialUnitary (i₀ : ι) : Continuous (toSpecialUnitary (ι := ι) i₀) :=
  ((continuous_id.mul ((continuous_detSection i₀).comp
    continuous_detCircle.inv)).subtypeVal).subtype_mk _

end Matrix.UnitaryGroup

end
