/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Projectivization
public import SymplecticGeometry.LinearAlgebra.Projectivization.Basic

/-!
# Continuity of the normalized representative

The representative `Projectivization.normalizedRep φ x` of a point `x` of `ℙ K V` on which a
continuous linear form `φ` takes the value `1` depends continuously on `x`, on the open set
`Projectivization.linearProjectionDomain φ` where `φ` does not vanish
(`Projectivization.continuousOn_normalizedRep`).
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

end
