/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Topology.Algebra.Module.BilinearForm
public import TauCeti.Geometry.Symplectic.SymplecticTransport
public import TauCeti.Topology.Algebra.Module.BilinearForm
import SymplecticGeometry.LinearAlgebra.SesquilinearForm

/-!
# The space of linear symplectic forms

A symplectic form `ω` on a finite-dimensional real normed space `V` is a bilinear form, hence a
continuous bilinear form `ω.toBilinForm.toContinuousBilinearMap : V →L[ℝ] V →L[ℝ] ℝ`. The
symplectic forms carry the topology induced by this map from the operator norm, in the same way
as Tau Ceti topologizes the complex structures of `V`. Its image is the set of alternating,
nondegenerate continuous bilinear forms, and transporting forms along a continuous linear
equivalence is continuous.

## Main definitions

* The instance `TopologicalSpace (TauCeti.SymplecticForm V)`.
* `TauCeti.SymplecticForm.ofContinuousBilinearMap`: an alternating, nondegenerate continuous
  bilinear form as a symplectic form.

## Main results

* `TauCeti.SymplecticForm.isEmbedding_toContinuousBilinearMap`: the map to continuous bilinear
  forms is a topological embedding.
* `TauCeti.SymplecticForm.continuous_iff`: a map into the symplectic forms is continuous exactly
  when its continuous bilinear forms are.
* `TauCeti.SymplecticForm.range_toContinuousBilinearMap`: the image consists of the alternating,
  nondegenerate forms. With `ContinuousLinearMap.isOpen_setOf_nondegenerate_toBilinForm`, it is
  open in the alternating forms.
* `TauCeti.SymplecticForm.continuous_transport`: transport along a continuous linear equivalence
  is continuous.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.5
-/

public noncomputable section

namespace TauCeti.SymplecticForm

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W]
  [NormedSpace ℝ W]

/-- The symplectic form of an alternating, nondegenerate continuous bilinear form. -/
def ofContinuousBilinearMap (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : B.toBilinForm.IsAlt)
    (hnd : B.toBilinForm.Nondegenerate) : SymplecticForm V :=
  ⟨B.toBilinForm, hB, hnd⟩

@[simp]
theorem ofContinuousBilinearMap_apply (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : B.toBilinForm.IsAlt)
    (hnd : B.toBilinForm.Nondegenerate) (v w : V) :
    ofContinuousBilinearMap B hB hnd v w = B v w :=
  (rfl)

variable [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]

@[simp]
theorem toBilinForm_toContinuousBilinearMap_ofContinuousBilinearMap (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hB : B.toBilinForm.IsAlt) (hnd : B.toBilinForm.Nondegenerate) :
    (ofContinuousBilinearMap B hB hnd).toBilinForm.toContinuousBilinearMap = B :=
  B.toContinuousBilinearMap_toBilinForm

/-- A symplectic form is skew-symmetric: as a continuous bilinear form `B`, `B - Bᵀ = 2 • B`. -/
theorem toContinuousBilinearMap_sub_flip (ω : SymplecticForm V) :
    ω.toBilinForm.toContinuousBilinearMap - ω.toBilinForm.toContinuousBilinearMap.flip =
      (2 : ℝ) • ω.toBilinForm.toContinuousBilinearMap := by
  ext u v
  simpa [two_smul, two_nsmul] using congr($(ω.isAlt.sub_flip_eq_two_smul) u v)

/-- The skew part of the continuous bilinear form of a symplectic form is that form itself. -/
@[simp]
theorem skewSymmetrizeBilinear_toContinuousBilinearMap (ω : SymplecticForm V) :
    ω.toBilinForm.toContinuousBilinearMap.skewSymmetrizeBilinear =
      ω.toBilinForm.toContinuousBilinearMap :=
  ContinuousLinearMap.skewSymmetrizeBilinear_of_isAlt ω.isAlt

/-- The topology on the symplectic forms of a finite-dimensional real normed space induced by the
operator norm of their continuous bilinear forms. As all norms on a finite-dimensional space are
equivalent, it does not depend on the norm of `V`. -/
instance : TopologicalSpace (SymplecticForm V) :=
  .induced (fun ω ↦ ω.toBilinForm.toContinuousBilinearMap) inferInstance

/-- Sending a symplectic form to its continuous bilinear form is a topological embedding. -/
theorem isEmbedding_toContinuousBilinearMap :
    Topology.IsEmbedding fun ω : SymplecticForm V ↦ ω.toBilinForm.toContinuousBilinearMap :=
  ⟨⟨rfl⟩, fun ω₁ ω₂ h ↦ toBilinForm_injective <| by
    simpa using congrArg ContinuousLinearMap.toBilinForm h⟩

/-- A map into the symplectic forms is continuous exactly when its continuous bilinear forms are
continuous in the operator norm. -/
theorem continuous_iff {X : Type*} [TopologicalSpace X] {f : X → SymplecticForm V} :
    Continuous f ↔ Continuous fun x ↦ (f x).toBilinForm.toContinuousBilinearMap :=
  isEmbedding_toContinuousBilinearMap.continuous_iff

/-- The continuous bilinear forms of symplectic forms are exactly the alternating, nondegenerate
continuous bilinear forms. -/
theorem range_toContinuousBilinearMap :
    Set.range (fun ω : SymplecticForm V ↦ ω.toBilinForm.toContinuousBilinearMap) =
      {B : V →L[ℝ] V →L[ℝ] ℝ | B.toBilinForm.IsAlt ∧ B.toBilinForm.Nondegenerate} := by
  ext B
  refine ⟨?_, fun ⟨hB, hnd⟩ ↦ ⟨ofContinuousBilinearMap B hB hnd, by simp⟩⟩
  rintro ⟨ω, rfl⟩
  exact ⟨ω.isAlt, ω.nondegenerate⟩

/-- Transporting symplectic forms along a continuous linear equivalence is continuous. -/
theorem continuous_transport (e : V ≃L[ℝ] W) :
    Continuous fun ω : SymplecticForm V ↦ ω.transport e.toLinearEquiv := by
  have h : (fun ω : SymplecticForm V ↦
      (ω.transport e.toLinearEquiv).toBilinForm.toContinuousBilinearMap) =
      fun ω ↦ e.bilinearCongr ω.toBilinForm.toContinuousBilinearMap := by
    ext
    simp
  rw [continuous_iff, h]
  exact e.bilinearCongr.continuous.comp
    isEmbedding_toContinuousBilinearMap.continuous

end TauCeti.SymplecticForm

end
