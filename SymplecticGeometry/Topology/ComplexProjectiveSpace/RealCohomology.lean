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
* `Projectivization.lineEmbedding`, `Projectivization.injective_lineEmbedding`: an injective
  linear map `(Fin 2 → K) → (Fin (m + 2) → K)`, to which the result applies for `K = ℂ`.
* `Projectivization.subsingleton_singularCohomology_real_of_finrank_eq_one`: for
  `finrank ℂ V = 1`, the point `ℙ ℂ V` has no real cohomology in positive degrees.

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

open CategoryTheory AlgebraicTopology Module
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

/-- For a one-dimensional complex vector space `V`, the projective space `ℙ ℂ V` is a point, so
its singular cohomology with real coefficients vanishes in every positive degree. -/
theorem subsingleton_singularCohomology_real_of_finrank_eq_one (hV : finrank ℂ V = 1)
    (hn : n ≠ 0) :
    Subsingleton ((TopCat.of (ℙ ℂ V)).singularCohomology (ModuleCat.of ℝ ℝ) ℝ
      (ModuleCat.of ℝ ℝ) n) := by
  have : Nontrivial V := Module.nontrivial_of_finrank_eq_succ hV
  have : Subsingleton (ℙ ℂ V) :=
    subsingleton_of_rank_le_one (by rw [← Module.finrank_eq_rank, hV]; simp)
  exact ModuleCat.subsingleton_of_isZero
    (TauCeti.isZero_singularCohomology_of_contractibleSpace (R := ModuleCat.of ℝ ℝ) (k := ℝ)
      (M := ModuleCat.of ℝ ℝ) (TopCat.of (ℙ ℂ V)) hn)

/-- The linear map `(Fin 2 → K) → (Fin (m + 2) → K)` sending `v` to `(v 0, v 1, …, v 1)`. It is
injective (`Projectivization.injective_lineEmbedding`), so for a division ring `K` it maps the
projective line `ℙ K (Fin 2 → K)` injectively into `ℙ K (Fin (m + 2) → K)`. -/
def lineEmbedding (K : Type*) [Semiring K] (m : ℕ) : (Fin 2 → K) →ₗ[K] Fin (m + 2) → K :=
  LinearMap.funLeft K K fun i ↦ if i = 0 then 0 else 1

@[simp]
theorem lineEmbedding_apply {K : Type*} [Semiring K] {m : ℕ} (v : Fin 2 → K) (i : Fin (m + 2)) :
    lineEmbedding K m v i = v (if i = 0 then 0 else 1) :=
  (rfl)

theorem injective_lineEmbedding (K : Type*) [Semiring K] (m : ℕ) :
    Function.Injective (lineEmbedding K m) :=
  LinearMap.funLeft_injective_of_surjective _ _ _
    fun j ↦ by fin_cases j <;> [exact ⟨0, rfl⟩; exact ⟨1, rfl⟩]

end Projectivization
