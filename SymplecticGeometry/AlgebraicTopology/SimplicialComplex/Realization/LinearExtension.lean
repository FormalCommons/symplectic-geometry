/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Basic

/-!
# Linear extension of vertex data over a realization

This file is a part of Tau Ceti's file
`TauCeti/AlgebraicTopology/SimplicialComplex/Realization/LinearExtension.lean`, copied from Tau
Ceti's commit `7e0204ba9998fd7943074e51919f8a1eff92d525`, which the pinned version of Tau Ceti
does not have yet. It takes only the definition `linearExtension`, the lemmas
`linearExtension_apply`, `linearExtension_eq_sum_of_support_subset`,
`linearExtension_faceInclusion` and `continuous_linearExtension`, and leaves out the rest of
that file, among it the secant maps.

Changes to Tau Ceti's code: the proof of `linearExtension_faceInclusion` gets the support
condition from `faceInclusion_val` and `StandardSimplex.support_subset`, since the pinned version
does not have `mem_range_faceInclusion_iff`. This module docstring is shortened to what the file
keeps.

A family `p : ι → E` of points of a real vector space, indexed by the vertices of an abstract
simplicial complex `K`, extends to the map `K.linearExtension p : |K| → E` sending a point with
barycentric coordinates `x` to the combination `∑ v, x v • p v`. It is linear in barycentric
coordinates on every closed simplex, and is continuous as soon as addition and real scalar
multiplication on `E` are.

## Main definitions

* `AbstractSimplicialComplex.linearExtension K p`: the extension of `p` linear in barycentric
  coordinates on every closed simplex.

## Main results

* `AbstractSimplicialComplex.linearExtension_faceInclusion`: on a closed simplex the extension is
  the combination of the values of `p` at its vertices.
* `AbstractSimplicialComplex.continuous_linearExtension`: the extension is continuous.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapter 2 (simplicial maps and their linear extensions).
-/

public section

noncomputable section

open Set Function TauCeti.SetLike

namespace AbstractSimplicialComplex

variable {ι : Type*} {E : Type*} [AddCommMonoid E] [Module ℝ E] (K : AbstractSimplicialComplex ι)

/-- The extension of vertex data `p : ι → E` over the realization of `K`, sending a point with
barycentric coordinates `x` to the combination `∑ v, x v • p v`. -/
def linearExtension (p : ι → E) (x : Realization K) : E :=
  Finsupp.linearCombination ℝ p x.val

variable {K}

/-- The linear extension evaluates the barycentric coordinates as a linear combination of the
vertex data. -/
theorem linearExtension_apply (p : ι → E) (x : Realization K) :
    K.linearExtension p x = Finsupp.linearCombination ℝ p x.val :=
  (rfl)

/-- If the barycentric support of a point lies in a finite vertex set `σ`, the linear extension
at that point is the combination of the values of `p` at the vertices of `σ`. -/
theorem linearExtension_eq_sum_of_support_subset (p : ι → E) {σ : Finset ι} {x : Realization K}
    (hx : x.val.support ⊆ σ) : K.linearExtension p x = ∑ a : σ, x.val a • p a := by
  rw [linearExtension_apply, Finsupp.linearCombination_apply_of_mem_supported ℝ hx]
  exact (Finset.sum_coe_sort σ fun a => x.val a • p a).symm

/-- On a closed simplex `σ`, the linear extension is the combination of the values of `p` at the
vertices of `σ`, weighted by the barycentric coordinates. -/
theorem linearExtension_faceInclusion (p : ι → E) (σ : Face K) (x : StandardSimplex σ.val) :
    K.linearExtension p (faceInclusion K σ x) = ∑ a : σ.val, x.val a • p a := by
  have hx : (faceInclusion K σ x).val.support ⊆ σ.val := by
    rw [faceInclusion_val]
    exact StandardSimplex.support_subset x
  rw [linearExtension_eq_sum_of_support_subset p hx, faceInclusion_val]

/-- The linear extension of vertex data into a space with continuous addition and continuous real
scalar multiplication is continuous for the weak topology on the realization. -/
theorem continuous_linearExtension [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul ℝ E]
    (p : ι → E) : Continuous (K.linearExtension p) := by
  refine continuous_iff_faceInclusion.mpr fun σ => ?_
  have hcoord (a : ι) : Continuous fun x : StandardSimplex σ.val => x.val a :=
    (continuous_apply a).comp continuous_induced_dom
  simp_rw [comp_def, linearExtension_faceInclusion]
  exact continuous_finsetSum _ fun a _ => (hcoord a).smul continuous_const

end AbstractSimplicialComplex
