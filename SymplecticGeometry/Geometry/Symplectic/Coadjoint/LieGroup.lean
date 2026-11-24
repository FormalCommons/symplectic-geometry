/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.Coadjoint.LieGroup

/-!
# The left-invariant covector field at the identity

For a real Lie group `G` and `μ ∈ 𝔤*`, Tau Ceti's left-invariant covector field
`Module.Dual.leftInvariantCovector μ : G → T*G` moves `μ` from the identity to each point of `G`
by the cotangent lift of left multiplication. This file computes its value at the identity: the
covector `μ` itself, read as a continuous functional on the tangent space at `1`
(`Module.Dual.leftInvariantCovector_one`). With `Module.Dual.leftInvariantCovector_mul`, this
writes the field as `g ↦ g • (1, μ)`.
-/

public section

open Bundle TauCeti
open scoped Manifold ContDiff

namespace Module.Dual

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]

/-- At the identity of `G`, the left-invariant covector field of `μ` is the covector `μ` at `1`,
read as a continuous functional on the tangent space there. -/
theorem leftInvariantCovector_one (μ : Module.Dual ℝ (GroupLieAlgebra I G)) :
    μ.leftInvariantCovector 1 =
      TotalSpace.mk' (E →L[ℝ] ℝ) (1 : G) (LinearMap.toContinuousLinearMap μ) := by
  have hid : (fun x : G ↦ 1⁻¹ * x) = id := funext fun x ↦ by simp
  refine CotangentBundle.ext (μ.proj_leftInvariantCovector 1) fun v ↦
    (μ.leftInvariantCovector_snd_apply 1 v).trans ?_
  rw [hid, mfderiv_id]
  -- The two sides are `μ v` with `v` read in the tangent spaces at `1⁻¹ * 1` and at `1`, which
  -- agree only up to unfolding, so `rw` cannot apply `ContinuousLinearMap.id_apply` or
  -- `LinearMap.coe_toContinuousLinearMap'` here; the closing step is definitional, as in Tau
  -- Ceti's proof of `Module.Dual.leftInvariantCovector_snd_apply`.
  exact congrArg μ (ContinuousLinearMap.id_apply v)

end Module.Dual

end
