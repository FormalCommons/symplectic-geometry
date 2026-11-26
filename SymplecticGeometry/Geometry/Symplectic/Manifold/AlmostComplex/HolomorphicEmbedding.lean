/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.RestrictScalars
public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Prod
import SymplecticGeometry.Geometry.Symplectic.Manifold.AlmostComplex.Prod

/-!
# Holomorphic embeddings have invariant tangent spaces

Let `f : M → N` be a holomorphic embedding of complex manifolds and `f.restrictScalars ℝ hnm hn`
its real form, a smooth embedding of the underlying real manifolds
(`TauCeti.SmoothEmbedding.restrictScalars`). The tangent ranges of the real form are the images
of complex linear maps, so they are invariant under the almost complex structure
`TauCeti.SmoothAlmostComplexStructure.ofComplexManifold` of `N`, which is multiplication by `i`
on every tangent space. The same holds for an embedding into a product `N × N'` of complex
manifolds and the product of the almost complex structures of `N` and `N'`, which is again
multiplication by `i` (`TauCeti.SmoothAlmostComplexStructure.prod_ofComplexManifold_apply`).

These are the hypotheses, written `∀ x, ∀ v ∈ f.tangentRange x hn, J (f x) v ∈ f.tangentRange x hn`,
under which `AlmostComplex/Submanifold.lean` restricts an almost complex structure and pulls back
taming forms. So a complex submanifold, such as a smooth hypersurface, is a symplectic
submanifold for every form that tames the complex structure of the ambient manifold.

## Main results

* `TauCeti.SmoothEmbedding.ofComplexManifold_mem_tangentRange_restrictScalars`: the tangent
  ranges of the real form of a holomorphic embedding are invariant under the almost complex
  structure of the target.
* `TauCeti.SmoothEmbedding.prod_ofComplexManifold_mem_tangentRange_restrictScalarsProd`: the
  same for a holomorphic embedding into a product and the product almost complex structure.

## References

* Daniel Huybrechts, *Complex Geometry: An Introduction*, Universitext, Springer, 2005,
  Section 2.6.
-/

public section

open scoped Manifold ContDiff TauCeti.ComplexManifold

namespace TauCeti.SmoothEmbedding

open SmoothAlmostComplexStructure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E'] [FiniteDimensional ℂ E']
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] {N : Type*} [TopologicalSpace N]
  [ChartedSpace E' N] [IsManifold 𝓘(ℂ, E') ∞ N] {m n : ℕ∞ω} [IsManifold 𝓘(ℝ, E) n M]
  [IsManifold 𝓘(ℝ, E') n N]

/-- The tangent ranges of the real form of a holomorphic embedding are invariant under the
almost complex structure of the target complex manifold. -/
theorem ofComplexManifold_mem_tangentRange_restrictScalars
    (f : SmoothEmbedding 𝓘(ℂ, E) 𝓘(ℂ, E') m M N) (hnm : n ≤ m) (hn : 1 ≤ n) (hn₀ : n ≠ 0)
    (x : M) (v) (hv : v ∈ (f.restrictScalars ℝ hnm hn).tangentRange x hn₀) :
    ofComplexManifold E' N (f.restrictScalars ℝ hnm hn x) v ∈
      (f.restrictScalars ℝ hnm hn).tangentRange x hn₀ := by
  -- `ofComplexManifold_apply` states `v` in `E'`, so it does not rewrite the goal directly.
  exact (ofComplexManifold_apply (E := E') (M := N) _ v).symm ▸
    f.smul_mem_tangentRange_restrictScalars hnm hn x hn₀ Complex.I hv

variable {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℂ F'] [FiniteDimensional ℂ F']
  {N' : Type*} [TopologicalSpace N'] [ChartedSpace F' N'] [IsManifold 𝓘(ℂ, F') ∞ N']
  [IsManifold 𝓘(ℝ, F') n N']

/-- The tangent ranges of the real form of a holomorphic embedding into a product `N × N'` of
complex manifolds are invariant under the product of the almost complex structures of `N` and
`N'`. -/
theorem prod_ofComplexManifold_mem_tangentRange_restrictScalarsProd
    (f : SmoothEmbedding 𝓘(ℂ, E) (𝓘(ℂ, E').prod 𝓘(ℂ, F')) m M (N × N')) (hnm : n ≤ m)
    (hn : 1 ≤ n) (hn₀ : n ≠ 0) (x : M) (v)
    (hv : v ∈ (f.restrictScalarsProd ℝ hnm hn).tangentRange x hn₀) :
    (ofComplexManifold E' N).prod (ofComplexManifold F' N') (f.restrictScalarsProd ℝ hnm hn x) v ∈
      (f.restrictScalarsProd ℝ hnm hn).tangentRange x hn₀ := by
  -- `prod_ofComplexManifold_apply` states `v` in `E' × F'`, so it does not rewrite the goal
  -- directly.
  exact (prod_ofComplexManifold_apply (M := N) (N := N') _ v).symm ▸
    f.smul_mem_tangentRange_restrictScalarsProd hnm hn x hn₀ Complex.I hv

end TauCeti.SmoothEmbedding

end
