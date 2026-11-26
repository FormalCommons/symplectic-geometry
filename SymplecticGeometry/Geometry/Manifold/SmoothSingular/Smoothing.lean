/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Kronecker
public import TauCeti.Geometry.Manifold.SmoothSingular.Smoothing
import SymplecticGeometry.AlgebraicTopology.SimplicialSet.Homology.Basic

/-!
# The smoothing isomorphism: coefficients and the Kronecker map

Tau Ceti's `TauCeti.smoothSingularHomologyIso` identifies the smooth singular homology of a
manifold with its singular homology, and `TauCeti.smoothSingularHomologyIso_hom_naturality` says
that it is natural in the manifold. This file adds that it is natural in the coefficient object:
`TauCeti.smoothSingularHomologyIso_hom_comp_homologyMap_coefficients` says that it commutes with
the maps on homology induced by a morphism of coefficients `R ⟶ R'`. It is
`SSet.homologyMap_coefficient_naturality` for the inclusion of the smooth singular subcomplex.

`TauCeti.homologyπ_smoothSingularHomologyIso_hom_singularKronecker_homologyπ` evaluates the
Kronecker map on the image of the class of a smooth cycle: the class of a singular cocycle `ψ`
takes there the value of `ψ` on that cycle.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 18 (smooth singular homology, Theorem 18.7).
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.1 (the Kronecker
  pairing).
-/

public section

open AlgebraicTopology CategoryTheory Limits
open scoped Manifold ContDiff

namespace TauCeti

universe u v w

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  (M : Type u) [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ M]
  {C : Type v} [Category.{w} C] [Abelian C] [HasCoproducts.{u} C]
  [HasExactColimitsOfShape (Discrete ℕ) C]

/-- The smoothing isomorphism `Hₙ^∞(M; R) ≅ Hₙ(M; R)` is natural in the coefficient object: it
commutes with the maps on homology induced by a morphism of coefficients `g : R ⟶ R'`. -/
@[reassoc]
theorem smoothSingularHomologyIso_hom_comp_homologyMap_coefficients {R R' : C} (g : R ⟶ R')
    (n : ℕ) :
    (smoothSingularHomologyIso I M R n).hom ≫
        HomologicalComplex.homologyMap
          (((SSet.chainComplexFunctor C).map g).app (TopCat.toSSet.obj (TopCat.of M))) n =
      HomologicalComplex.homologyMap
          (((SSet.chainComplexFunctor C).map g).app (smoothSingularSubcomplex I M : SSet)) n ≫
        (smoothSingularHomologyIso I M R' n).hom := by
  rw [smoothSingularHomologyIso_hom, smoothSingularHomologyIso_hom]
  exact (SSet.homologyMap_coefficient_naturality (smoothSingularSubcomplex I M).ι g n).symm

/-- The class of a singular cocycle `ψ` evaluates, under the Kronecker map, on the image under the
smoothing isomorphism of the class of a smooth cycle `z` to `ψ` on `z`. -/
theorem homologyπ_smoothSingularHomologyIso_hom_singularKronecker_homologyπ {R N : C}
    (k : Type*) [Ring k] [Linear k C] (p : ℕ)
    (ψ : ((TopCat.of M).singularCochainComplex R k N).cycles p) :
    ((smoothSingularSubcomplex I M : SSet).chainComplex R).homologyπ p ≫
        (smoothSingularHomologyIso I M R p).hom ≫
          (TopCat.of M).singularKronecker k p
            (((TopCat.of M).singularCochainComplex R k N).homologyπ p ψ) =
      ((smoothSingularSubcomplex I M : SSet).chainComplex R).iCycles p ≫
        (SSet.chainComplexMap (smoothSingularSubcomplex I M).ι R).f p ≫
          ((TopCat.of M).singularCochainComplex R k N).iCycles p ψ := by
  rw [smoothSingularHomologyIso_hom]
  -- `SSet.homologyMap` is the map on homology of `SSet.chainComplexMap`, but its codomain is
  -- written through `TopCat.toSSet`, which `rw` does not match; the squares are pasted as terms.
  refine (HomologicalComplex.homologyπ_naturality_assoc
    (SSet.chainComplexMap (smoothSingularSubcomplex I M).ι R) p _).trans ?_
  rw [TopCat.singularKronecker_homologyπ]
  exact HomologicalComplex.cyclesMap_i_assoc _ _ _

end TauCeti

end
