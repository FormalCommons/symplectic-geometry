/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Sphere
public import SymplecticGeometry.Geometry.Symplectic.Manifold.AlmostComplex.EulerCharacteristic
public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.Sphere

/-!
# Complex structures on the tangent bundles of spheres

Let `E` be a real inner product space of dimension `n + 1`, so that the unit sphere `S^n` of `E`
is a smooth manifold modelled on `EuclideanSpace ℝ (Fin n)`, and `J` a continuous complex
structure on its tangent bundle (Tau Ceti's `TauCeti.Bundle.ContinuousComplexStructure`). The
file assumes that `n = 2 r + 2` is even and positive; `J` then orients the sphere
(`TauCeti.Bundle.ContinuousComplexStructure.tangentOrientation`).

* `TauCeti.Bundle.ContinuousComplexStructure.evalFundamentalClass_chernClass_sphere`: the top
  Chern class `c_{r+1}` of the complex tangent bundle `J.Fiber`, evaluated on the fundamental
  class of the orientation given by `J`, is `2`, the Euler characteristic of `S^{2r+2}`. This
  is the closed-manifold statement
  `TauCeti.Bundle.ContinuousComplexStructure.evalFundamentalClass_chernClass_eq_eulerChar` with
  Tau Ceti's `TauCeti.eulerChar_sphere`.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §11 and §14.
-/

public section

open Bundle Module Metric
open scoped Manifold ContDiff VectorBundle.ComplexToReal

namespace TauCeti.Bundle.ContinuousComplexStructure

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {n : ℕ} [Fact (finrank ℝ E = n + 1)]
  {G : Type} [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G]
  [Fact (finrank ℝ (EuclideanSpace ℝ (Fin n)) = 2 * finrank ℂ G)]

/-- **The top Chern number of a complex structure on the tangent bundle of a sphere is `2`.** Let
`J` be a continuous complex structure on the tangent bundle of the unit sphere `S^n` of `E`, with
`finrank ℝ E = n + 1` and `n = 2 r + 2`, and complex model `G`. Orient the sphere by `J`
(`J.tangentOrientation hn`). Then the top Chern class `c_{r+1}` of the complex bundle `J.Fiber`,
evaluated on the fundamental class of the sphere, is `2`.

The sphere `S^0`, two points, is left out: the fundamental class is defined here only in
positive dimension. -/
theorem evalFundamentalClass_chernClass_sphere
    (J : ContinuousComplexStructure (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : sphere (0 : E) 1 → Type)) {r : ℕ}
    (hn : finrank ℝ (EuclideanSpace ℝ (Fin n)) = 2 * r + 2) :
    ((J.tangentOrientation hn).toHomologicalOrientation hn).evalFundamentalClass hn
      (ModuleCat.of ℤ ℤ) (ContinuousMap.id _)
      (SymplecticGeometry.Bundle.chernClass G J.Fiber (r + 1)) = 2 := by
  rw [J.evalFundamentalClass_chernClass_eq_eulerChar (G := G) hn,
    eulerChar_sphere (Fact.out : finrank ℝ E = n + 1)]
  obtain rfl : n = 2 * r + 2 := by simpa using hn
  rw [Even.neg_one_pow ⟨r + 1, by ring⟩]
  norm_num

end TauCeti.Bundle.ContinuousComplexStructure

end
