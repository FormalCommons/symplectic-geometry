/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Normed.Algebra.HolomorphicFunctionalCalculus.Riesz

import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-!
# Eigenvectors in the range of a Riesz idempotent

For an operator `T` on a complex Banach space and a clopen part `K` of its spectrum, an
eigenvector of `T` that Tau Ceti's Riesz idempotent `rieszIdempotent T K` fixes has its
eigenvalue in `K` (`ContinuousLinearMap.mem_image_of_rieszIdempotent_apply_eq_self`). This
follows from Tau Ceti's `isUnit_sub_mul_rieszIdempotent_add_iff`.

## References

* T. Kato, *Perturbation Theory for Linear Operators*, Springer, 1995, §I.5.3.
-/

public section

open TauCeti TopologicalSpace

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- If a vector `v` in the range of the Riesz idempotent of a clopen part `K` of the spectrum of
`T` is an eigenvector of `T` for the eigenvalue `μ`, then `μ` lies in `K`. -/
theorem mem_image_of_rieszIdempotent_apply_eq_self {T : E →L[ℂ] E}
    (K : Clopens (spectrum ℂ T)) {v : E} (hv : v ≠ 0) (hP : rieszIdempotent T K v = v) {μ : ℂ}
    (hT : T v = μ • v) : μ ∈ ((↑) '' (K : Set (spectrum ℂ T)) : Set ℂ) := by
  by_contra hμ
  obtain ⟨u, hu⟩ := (isUnit_sub_mul_rieszIdempotent_add_iff T K μ).mpr hμ
  refine hv ?_
  have h0 : (↑u : E →L[ℂ] E) v = 0 := by
    rw [hu]
    simp [hP, hT, Algebra.algebraMap_eq_smul_one]
  have h1 := congrArg (↑u⁻¹ : E →L[ℂ] E) h0
  rwa [units_inv_apply_apply, map_zero] at h1

end ContinuousLinearMap

end
