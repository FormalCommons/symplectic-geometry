/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Projectivization
public import SymplecticGeometry.LinearAlgebra.Projectivization.Basic
public import TauCeti.Topology.Algebra.Projectivization

/-!
# Continuity of the normalized representative

The representative `Projectivization.normalizedRep φ x` of a point `x` of `ℙ K V` on which a
continuous linear form `φ` takes the value `1` depends continuously on `x`, on the open set
`Projectivization.linearProjectionDomain φ` where `φ` does not vanish
(`Projectivization.continuousOn_normalizedRep`).

For a continuous semilinear equivalence `e`, the line `e.mapProjectivization ℓ` is the image of
`ℓ` under `e` (`ContinuousLinearEquiv.submodule_mapProjectivization`), the continuous counterpart
of Tau Ceti's `LinearEquiv.submodule_mapProjectivization`.
-/

public section

open scoped LinearAlgebra.Projectivization

namespace Projectivization

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [TopologicalSpace K]
  [IsTopologicalDivisionRing K] [TopologicalSpace V] [ContinuousSMul K V]

/-- The normalized representative depends continuously on the point, where `φ` does not vanish. -/
theorem continuousOn_normalizedRep {φ : V →ₗ[K] K} (hφ : Continuous φ) :
    ContinuousOn (normalizedRep φ) (linearProjectionDomain φ) := by
  intro x hx
  refine ContinuousAt.continuousWithinAt ?_
  obtain ⟨v, rfl⟩ := isOpenQuotientMap_mk'.surjective x
  rw [← isOpenQuotientMap_mk'.continuousAt_comp_iff]
  have hv : φ v ≠ 0 := by simpa [mk'_eq_mk] using hx
  have h : normalizedRep φ ∘ mk' K = fun w : {w : V // w ≠ 0} ↦ (φ w)⁻¹ • (w : V) := by
    ext w
    simp [mk'_eq_mk]
  rw [h]
  exact ((hφ.comp continuous_subtypeVal).continuousAt.inv₀ hv).smul
    continuous_subtypeVal.continuousAt

end Projectivization

namespace ContinuousLinearEquiv

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] [TopologicalSpace V]
  {L W : Type*} [DivisionRing L] [AddCommGroup W] [Module L W] [TopologicalSpace W]
  {σ : K →+* L} {σ' : L →+* K} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]

/-- The line `e.mapProjectivization ℓ` is the image of the line `ℓ` under `e`. -/
@[simp]
theorem submodule_mapProjectivization (e : V ≃SL[σ] W) (ℓ : ℙ K V) :
    (e.mapProjectivization ℓ).submodule = ℓ.submodule.map (e : V →ₛₗ[σ] W) := by
  rw [coe_mapProjectivization, Projectivization.submodule_map]

end ContinuousLinearEquiv

end
