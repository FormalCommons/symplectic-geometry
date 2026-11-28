/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Algebra.Projectivization
public import Mathlib.Algebra.Category.ModuleCat.Algebra
public import TauCeti.AlgebraicTopology.Cohomology.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Analysis.Complex.Basic
public import SymplecticGeometry.Topology.Algebra.Projectivization
import SymplecticGeometry.Algebra.Category.ModuleCat.Injective
import SymplecticGeometry.AlgebraicTopology.Cohomology.IntegralChains
import SymplecticGeometry.Topology.ComplexProjectiveSpace.SecondHomology
import TauCeti.AlgebraicTopology.Cohomology.Point
import TauCeti.LinearAlgebra.Projectivization.Basic

/-!
# Linear embeddings of complex projective spaces on real second cohomology

Let `f : V →ₗ[ℂ] W` be an injective linear map of finite-dimensional complex normed spaces with
`finrank ℂ V ≥ 2`, and let `g : ℙ ℂ V → ℙ ℂ W` be the induced map. This file shows that `g`
induces an injection on second cohomology with real coefficients. For `finrank ℂ V = 2` this
says that restricting to a projective line is injective on `H²(ℙ ℂ W; ℝ)`.

## Main results

* `Projectivization.injective_singularCohomologyMap_map_real`: `g^*` is injective on
  `H²(-; ℝ)`, the cohomology of real chains with real values.
* `Projectivization.isZero_singularCohomology_of_finrank_eq_one`: for `finrank K E = 1`, the
  point `ℙ K E` has no singular cohomology in positive degrees, for any coefficients.

## Proof

The map `g` is a bijection on integral second homology
(`Projectivization.bijective_singularHomologyMap_map_two`). As `ℝ` is a divisible, hence
injective, abelian group (`ModuleCat.injective_of_divisible`), a map that is onto
integral homology in some degree is injective on real cohomology in that degree
(`TopCat.injective_singularCohomologyMap_of_surjective`, from the universal coefficient theorem).

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 2.2 (the cellular
  homology of complex projective space) and Section 3.1 (the universal coefficient theorem).
-/

public section

noncomputable section

universe w v u

open CategoryTheory Limits AlgebraicTopology Module
open scoped LinearAlgebra.Projectivization MonoidalCategory

namespace Projectivization

variable {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W] {n : ℕ}

/-- An injective linear map `f : V →ₗ[ℂ] W` with `finrank ℂ V = n + 1` and `n ≠ 0` induces an
injective map `H²(ℙ ℂ W; ℝ) → H²(ℙ ℂ V; ℝ)` on second singular cohomology with real
coefficients. For `finrank ℂ V = 2`, restriction to a projective line is injective on
`H²(-; ℝ)`. -/
theorem injective_singularCohomologyMap_map_real (f : V →ₗ[ℂ] W) (hf : Function.Injective f)
    (hV : finrank ℂ V = n + 1) (hn : n ≠ 0) :
    Function.Injective (TopCat.singularCohomologyMap (R := ModuleCat.of ℝ ℝ) (k := ℝ)
      (M := ModuleCat.of ℝ ℝ) (TopCat.ofHom (mapContinuousMap f hf)) 2) :=
  TopCat.injective_singularCohomologyMap_of_surjective ℝ _ 2
    (bijective_singularHomologyMap_map_two f hf hV hn).2

/-- For a one-dimensional vector space `E` over a division ring `K`, the projective space `ℙ K E`
is a point, so its singular cohomology, with any coefficients, vanishes in every positive
degree. -/
theorem isZero_singularCohomology_of_finrank_eq_one {C : Type u} [Category.{v} C]
    [HasCoproducts.{w} C] [Abelian C] (R : C) (k : Type*) [Ring k] [Linear k C] (M : C)
    {K : Type*} {E : Type w} [DivisionRing K] [AddCommGroup E] [TopologicalSpace E] [Module K E]
    (hE : finrank K E = 1) (hn : n ≠ 0) :
    IsZero ((TopCat.of (ℙ K E)).singularCohomology R k M n) := by
  have : Nontrivial E := Module.nontrivial_of_finrank_eq_succ hE
  have : Module.Finite K E := Module.finite_of_finrank_eq_succ hE
  have : Subsingleton (ℙ K E) :=
    subsingleton_of_rank_le_one (by rw [← Module.finrank_eq_rank, hE]; simp)
  exact TauCeti.isZero_singularCohomology_of_contractibleSpace R k M (TopCat.of (ℙ K E)) hn

end Projectivization
