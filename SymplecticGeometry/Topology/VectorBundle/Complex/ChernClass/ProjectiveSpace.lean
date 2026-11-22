/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Cohomology.IntegralCohomologyULift
public import SymplecticGeometry.Topology.VectorBundle.ProjectiveBundle.Tautological
public import TauCeti.Topology.VectorBundle.Orientation.Complex.FiberwiseEquiv

/-!
# The hyperplane class of a complex projective space

For a complex normed space `V`, the hyperplane class `h ∈ H²(ℙ ℂ V; ℤ)` is minus the Euler class
of the tautological line `Projectivization.Tautological ℂ V`, read in integral cohomology through
`TopCat.uliftIntegralCohomologyIso`: it is the first Chern class of the dual of the tautological
line, in the normalization of Bott–Tu, §20.

## Main definitions and results

* `Projectivization.hyperplaneClass V`: the hyperplane class, with `hyperplaneClass_def`.
* `Projectivization.hyperplaneClass_map`: the map of projective spaces induced by an injective
  linear map `f : V →ₗ[ℂ] W`, with `V` finite-dimensional, pulls the hyperplane class of `W` back
  to that of `V`. The tautological line of `V` is the pull-back of that of `W` by the fibrewise
  isomorphisms `Projectivization.tautologicalMapEquiv`, so this is the naturality of the Euler
  class, `TauCeti.complexEulerClass_eq_singularCohomologyMap_of_fiberwise`, together with that of
  `TopCat.uliftIntegralCohomologyIso`.

## Implementation notes

The Euler class is that of a line, `r = 0`, of degree `2 * 0 + 2`, which is `2` by computation;
as in `SymplecticGeometry.Bundle.firstChernClass`, `r := 0` is given explicitly.

## References

* [R. Bott, L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982], §20 (the
  tautological line of a projective space and the class `x = -e(S)`).
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton University Press (1974), §14 (the cohomology of complex projective space).
-/

public section

noncomputable section

open Bundle Module TauCeti
open scoped LinearAlgebra.Projectivization

namespace Projectivization

variable (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- The **hyperplane class** `h ∈ H²(ℙ ℂ V; ℤ)` of a complex projective space: minus the Euler
class of the tautological line, in integral cohomology. -/
def hyperplaneClass : (TopCat.of (ℙ ℂ V)).integralCohomology 2 :=
  -((TopCat.of (ℙ ℂ V)).uliftIntegralCohomologyIso 2).hom
    (complexEulerClass (r := 0) ℂ (Tautological ℂ V) (finrank_self ℂ))

theorem hyperplaneClass_def :
    hyperplaneClass V = -((TopCat.of (ℙ ℂ V)).uliftIntegralCohomologyIso 2).hom
      (complexEulerClass (r := 0) ℂ (Tautological ℂ V) (finrank_self ℂ)) :=
  (rfl)

variable {V} {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ V]

/-- **Naturality of the hyperplane class.** The continuous map `ℙ ℂ V → ℙ ℂ W` induced by an
injective linear map `f : V →ₗ[ℂ] W` pulls the hyperplane class of `W` back to that of `V`. -/
theorem hyperplaneClass_map (f : V →ₗ[ℂ] W) (hf : Function.Injective f) :
    TopCat.singularCohomologyMap
        (TopCat.ofHom ⟨map f hf, continuous_map hf (LinearMap.continuous_of_finiteDimensional f)⟩)
        2 (hyperplaneClass W) = hyperplaneClass V := by
  have hfc := LinearMap.continuous_of_finiteDimensional f
  have h := complexEulerClass_eq_singularCohomologyMap_of_fiberwise (r := 0) (finrank_self ℂ)
    (finrank_self ℂ) (g := ⟨map f hf, continuous_map hf hfc⟩)
    (continuous_tautologicalMapEquiv f hf hfc)
  rw [hyperplaneClass_def, hyperplaneClass_def, map_neg, h]
  exact congrArg _ (CategoryTheory.ConcreteCategory.congr_hom
    (TopCat.uliftIntegralCohomologyIso_naturality _ 2) _).symm

end Projectivization
