/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Reduced
public import TauCeti.Geometry.Manifold.SmoothSingular.Smoothing

/-!
# The smoothing isomorphism on the class of a point

This file is a part of Tau Ceti's file `TauCeti/Geometry/Manifold/SmoothSingular/Smoothing.lean`,
as of the commit `b952d20066` of Tau Ceti's main branch. It contains only the lemma that this
commit adds there, `TauCeti.ιHomology₀_smoothSingularHomologyIso_hom`: the smoothing isomorphism
`TauCeti.smoothSingularHomologyIso` sends the class of the smooth `0`-simplex at a point to the
class of that point.

It is stated under its Tau Ceti name and namespace, with Tau Ceti's statement, proof, docstring
and variables. The one change is to the imports: in place of Tau Ceti's file, this file imports the
pinned version of it, together with `TauCeti/AlgebraicTopology/Singular/Reduced.lean`, whose
public import the commit adds to Tau Ceti's file.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 18, Theorem 18.7.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace Topology
open scoped Manifold ContDiff

universe u v w

namespace TauCeti

section HomotopyEquiv

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  (M : Type u) [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ M]
  {C : Type v} [Category.{w} C] [Abelian C] [HasCoproducts.{u} C]
  [HasExactColimitsOfShape (Discrete ℕ) C] (R : C)

/-- The smoothing isomorphism sends the class in `H₀^∞(M; R)` of the smooth `0`-simplex at `x` to
the class in `H₀(M; R)` of the point `x`. -/
@[reassoc]
theorem ιHomology₀_smoothSingularHomologyIso_hom (x : M) :
    SSet.ιHomology₀ R ((SmoothSimplex.equiv₀ I M).symm x) ≫
        (smoothSingularHomologyIso I M R 0).hom =
      singularHomology₀Section R (X := TopCat.of M) x := by
  rw [smoothSingularHomologyIso_hom, SSet.ιHomology₀_homologyMap, singularHomology₀Section_def]
  exact congrArg (SSet.ιHomology₀ R) (SmoothSimplex.coe_equiv₀_symm x)

end HomotopyEquiv

end TauCeti
