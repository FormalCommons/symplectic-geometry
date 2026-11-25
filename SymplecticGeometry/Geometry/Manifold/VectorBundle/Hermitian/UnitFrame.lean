/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Hermitian.CircleBundle
public import SymplecticGeometry.Analysis.Complex.NormalizedDeterminant
import SymplecticGeometry.GroupTheory.GroupAction.Hom

/-!
# Frames of a Hermitian line bundle from sections of its circle bundle

Let `E → B` be a complex line bundle with model fibre `F` whose fibres are complex inner product
spaces, and `P = TauCeti.OrthonormalFrameBundle.Fiber ℂ F E ℂ` its principal `Circle`-bundle of
unitary frames (`Geometry/Manifold/VectorBundle/Hermitian/CircleBundle.lean`). A point `φ` of
`P x` is a unit vector `φ 1` of `E x`, and with a fixed isomorphism `e : F ≃L[ℂ] ℂ` it gives the
frame `v ↦ e v • φ 1` of `E x` modelled on `F` (`SymplecticGeometry.Bundle.unitFrame`). This file
proves:

* a section `σ` of `P` continuous on a set `S` gives frames `unitFrame e (σ x)`, `x ∈ S`, that are
  continuous as maps `S × F → TotalSpace F E` (`SymplecticGeometry.Bundle.continuous_unitFrame`),
  the form in which `SymplecticGeometry.Bundle.chernNumber_eq_sum_degree_clutching` takes frames;
* the transition `(unitFrame e φ)⁻¹ ∘ unitFrame e ψ` between the frames of two points of the same
  fibre is multiplication by the element `TauCeti.PrincipalBundle.division Circle φ ψ` of the
  circle that carries `φ` to `ψ` (`SymplecticGeometry.Bundle.trans_unitFrame_symm_apply`), so its
  normalized determinant is that element
  (`SymplecticGeometry.Bundle.normalizedDet_trans_unitFrame_symm`).

`Geometry/Manifold/VectorBundle/ChernNumber/Clutching.lean` applies these facts to the clutching
transitions of such frames.

For smooth sections, `SymplecticGeometry.Bundle.contMDiffOn_normalizedFrame` and
`SymplecticGeometry.Bundle.exists_contMDiffOn_circleFiber` give smooth sections of `P`, and Tau
Ceti's `ContMDiffOn.division` and `ContMDiffOn.totalSpaceMk_smul` say that the division of two
smooth sections, and a smooth section acted on by a smooth map to `Circle`, are smooth.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.7
  (the first Chern number of a line bundle over a surface from the transitions of unitary
  trivializations over discs and over their complement).
-/

public section

noncomputable section

open Bundle Function MulOpposite Module TauCeti TauCeti.OrthonormalFrameBundle
  TauCeti.PrincipalBundle

namespace SymplecticGeometry.Bundle

section Frame

variable {B F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] {E : B → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℂ (E x)] (e : F ≃L[ℂ] ℂ)

/-- The frame of `E x` modelled on `F` given by a unitary frame `φ : ℂ ≃ₗᵢ[ℂ] E x` and an
isomorphism `e : F ≃L[ℂ] ℂ`: the isomorphism `v ↦ e v • φ 1` from `F` to `E x`. -/
def unitFrame {x : B} (φ : Fiber ℂ F E ℂ x) : F ≃L[ℂ] E x :=
  e.trans φ.frame.toContinuousLinearEquiv

/-- The frame `unitFrame e φ` sends `v` to `φ (e v)`. -/
@[simp]
theorem unitFrame_apply {x : B} (φ : Fiber ℂ F E ℂ x) (v : F) :
    unitFrame e φ v = φ.frame (e v) :=
  (rfl)

/-- The frame `unitFrame e φ` sends `v` to `e v • φ 1`. -/
theorem unitFrame_apply_eq_smul {x : B} (φ : Fiber ℂ F E ℂ x) (v : F) :
    unitFrame e φ v = e v • φ.frame 1 := by
  rw [unitFrame_apply, map_eq_smul_map_one]

/-- The inverse of `unitFrame e φ` sends `w` to `e⁻¹ (φ⁻¹ w)`. -/
@[simp]
theorem unitFrame_symm_apply {x : B} (φ : Fiber ℂ F E ℂ x) (w : E x) :
    (unitFrame e φ).symm w = e.symm (φ.frame.symm w) :=
  (rfl)

/-- Acting by `z : Circle` on a unitary frame multiplies its frame by `z` on the model. -/
theorem unitFrame_op_circle_smul {x : B} (z : Circle) (φ : Fiber ℂ F E ℂ x) (v : F) :
    unitFrame e (op z • φ) v = unitFrame e φ ((z : ℂ) • v) := by
  rw [unitFrame_apply, unitFrame_apply, Fiber.frame_op_circle_smul_apply, _root_.map_smul,
    smul_eq_mul]

variable [TopologicalSpace B] [TopologicalSpace (TotalSpace F E)] [FiberBundle F E]
  [VectorBundle ℂ F E] [ContinuousFiberNorm F E] [Fact (finrank ℂ F = 1)]

/-- **The transition between two frames `unitFrame`.** For two unitary frames `φ` and `ψ` of the
same fibre, `(unitFrame e φ)⁻¹ ∘ unitFrame e ψ` is multiplication by the element
`division Circle φ ψ` of the circle that carries `φ` to `ψ`. -/
theorem trans_unitFrame_symm_apply {x : B} (φ ψ : Fiber ℂ F E ℂ x) (v : F) :
    (unitFrame e ψ).trans (unitFrame e φ).symm v = (division Circle φ ψ : ℂ) • v := by
  conv_lhs => rw [← smul_division (G := Circle) φ ψ]
  rw [ContinuousLinearEquiv.trans_apply, unitFrame_op_circle_smul,
    ContinuousLinearEquiv.symm_apply_apply]

/-- The normalized determinant of the transition `(unitFrame e φ)⁻¹ ∘ unitFrame e ψ` is the
element `division Circle φ ψ` of the circle that carries `φ` to `ψ`. -/
theorem normalizedDet_trans_unitFrame_symm {x : B} (φ ψ : Fiber ℂ F E ℂ x) :
    ((unitFrame e ψ).trans (unitFrame e φ).symm).normalizedDet = division Circle φ ψ := by
  rw [ContinuousLinearEquiv.normalizedDet_eq_pow_of_apply_eq_smul _ _
    (trans_unitFrame_symm_apply e φ ψ), Fact.out (p := finrank ℂ F = 1), pow_one]

omit [ContinuousFiberNorm F E] [Fact (finrank ℂ F = 1)] in
/-- **Continuity of the frames `unitFrame`.** If `σ` is a section of the principal
`Circle`-bundle of unitary frames that is continuous on a set `S`, the frames `unitFrame e (σ x)`,
`x ∈ S`, form a continuous map `S × F → TotalSpace F E`. -/
theorem continuous_unitFrame {S : Set B} {σ : ∀ x, Fiber ℂ F E ℂ x}
    (hσ : ContinuousOn (fun x ↦ TotalSpace.mk' Circle x (σ x)) S) :
    Continuous fun q : S × F ↦ TotalSpace.mk' F (q.1 : B) (unitFrame e (σ q.1) q.2) := by
  -- `σ` read in the frame bundle with model fibre `unitary (ℂ →L[ℂ] ℂ)`.
  have hσ' : Continuous fun q : S × F ↦ TotalSpace.mk' (unitary (ℂ →L[ℂ] ℂ)) (q.1 : B) (σ q.1) :=
    (((TotalSpace.modelFiberHomeomorph isInducing_modelFiberEquiv_circleFiber).continuous
      |>.comp_continuousOn hσ).comp_continuous
      (continuous_subtypeVal.comp continuous_fst) fun q ↦ q.1.property).congr fun q ↦ by
        simp [TotalSpace.coe_modelFiberHomeomorph, TotalSpace.modelFiberEquiv_apply]
  exact continuous_totalSpace_frame_apply.comp (hσ'.prodMk (e.continuous.comp continuous_snd))

end Frame

end SymplecticGeometry.Bundle

end
