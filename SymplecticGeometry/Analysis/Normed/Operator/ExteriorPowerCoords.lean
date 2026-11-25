/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Algebra.Star.LinearMap
public import TauCeti.Analysis.Normed.Operator.ExteriorPowerCoords
import TauCeti.LinearAlgebra.Matrix.ConjTranspose
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-!
# Compound matrices and entrywise conjugation

For an operator `g` between coordinate spaces over a normed field with a continuous star, the
compound matrices `g.exteriorPowerCoords j` of Tau Ceti commute with Mathlib's intrinsic star
`v ↦ star (g (star v))`, which conjugates the matrix of `g` entrywise
(`ContinuousLinearMap.exteriorPowerCoords_intrinsicStar`): the entries of a compound matrix are
minors, polynomials with integer coefficients in the entries.
-/

public section

open WithConv

namespace ContinuousLinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [StarRing 𝕜] [ContinuousStar 𝕜]

/-- The compound matrix of the entrywise conjugate of an operator is the entrywise conjugate of its
compound matrix. -/
theorem exteriorPowerCoords_intrinsicStar (j : ℕ) {m n : ℕ}
    (g : (Fin m → 𝕜) →L[𝕜] (Fin n → 𝕜)) :
    (star (toConv g)).ofConv.exteriorPowerCoords j =
      (star (toConv (g.exteriorPowerCoords j))).ofConv := by
  refine ContinuousLinearMap.pi_ext_single_one fun t ↦ ?_
  funext s
  simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.exteriorPowerCoords_apply,
    LinearMap.exteriorPowerCoords_single_apply, ContinuousLinearMap.intrinsicStar_apply,
    Pi.star_single, star_one, Pi.star_apply]
  rw [← starRingEnd_apply, RingHom.map_det, RingHom.mapMatrix_apply]
  -- The left side is `Matrix.of fun i k ↦ star _`, which is `Matrix.map _ star` by definition.
  exact congrArg Matrix.det (Matrix.map_star_eq_map_starRingEnd _).symm

end ContinuousLinearMap
