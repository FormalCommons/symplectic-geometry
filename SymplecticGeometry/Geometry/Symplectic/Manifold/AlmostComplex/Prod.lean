/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure
public import TauCeti.Geometry.Manifold.IsManifold.Prod
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Prod

/-!
# Products of almost complex structures: taming and complex manifolds

Tau Ceti defines the product `J.prod L` of smooth almost complex structures on `P` and `M`
(`TauCeti.SmoothAlmostComplexStructure.prod`), acting by `J` and `L` on the two components of a
tangent vector of `P × M`, and proves that the product form `σ.prod τ` of compatible forms is
compatible with it (`TauCeti.SmoothAlmostComplexStructure.compatible_prod`). This file adds the
corresponding statements for tame and for invariant pairs, and relates the product to the almost
complex structure of a product of complex manifolds.

For complex manifolds `M` and `N` modelled on `𝓘(ℂ, E)` and `𝓘(ℂ, F)`, the product of their
almost complex structures `ofComplexManifold E M` and `ofComplexManifold F N` is multiplication by
`i` on every tangent space `E × F` of `M × N`. With Tau Ceti's product charts
`TauCeti.chartedSpaceProd`, which make `M × N` a complex manifold modelled on `𝓘(ℂ, E × F)`
(`TauCeti.isManifold_chartedSpaceProd`), the almost complex structure
`ofComplexManifold (E × F) (M × N)` is multiplication by `i` too. The two structures live over the
models `𝓘(ℝ, E × F)` and `𝓘(ℝ, E).prod 𝓘(ℝ, F)`, which are equal (`modelWithCornersSelf_prod`)
but not definitionally, so they are compared on tangent vectors, both tangent spaces being
`E × F`. So if `σ` and `τ` tame the complex structures of `M` and `N`, then `σ.prod τ (v, i v) > 0`
for every nonzero tangent vector `v` of `M × N`
(`TauCeti.SmoothAlmostComplexStructure.eval₂_prod_ofComplexManifold_pos`). This is a pointwise
statement, not a `Tames` statement: the form and the structure are over different models.

## Main results

* `TauCeti.SmoothAlmostComplexStructure.tames_prod`: if `σ` tames `J` and `τ` tames `L`, then
  `σ.prod τ` tames `J.prod L`.
* `TauCeti.SmoothAlmostComplexStructure.invariant_prod`: the same for invariant pairs.
* `TauCeti.SmoothAlmostComplexStructure.prod_ofComplexManifold_apply`: the product of the almost
  complex structures of two complex manifolds is multiplication by `i`.
* `TauCeti.SmoothAlmostComplexStructure.ofComplexManifold_prod_apply`: the almost complex
  structure of the product complex manifold agrees on tangent vectors with the product of the
  almost complex structures of the factors.
* `TauCeti.SmoothAlmostComplexStructure.eval₂_prod_ofComplexManifold_pos`: if forms tame the
  complex structures of two complex manifolds, their product form is positive on `(v, i v)` for
  every nonzero tangent vector `v` of the product complex manifold.

## Implementation notes

The two statements on pairs are proved on components. By `TauCeti.SmoothTwoForm.eval₂_prod` and
`TauCeti.SmoothAlmostComplexStructure.prod_apply`, the product form on `(v, (J × L) v)` is the
sum of `σ` on `(v₁, J v₁)` and `τ` on `(v₂, L v₂)` (`eval₂_prod_prod_apply`). Taming then follows
at each point from the linear `TauCeti.SymplecticForm.prod_tames`, as in Tau Ceti's
`TauCeti.SmoothAlmostComplexStructure.tames_prodFamily`, and invariance follows by `simp`.

## References

* [D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*][McDuffSalamon2012],
  §2.2 (tame and compatible almost complex structures).
-/

public section

open scoped Manifold ContDiff TauCeti.ComplexManifold

namespace TauCeti.SmoothAlmostComplexStructure

section Tames

variable {E H P F H' M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace P] [ChartedSpace H P] [IsManifold I ∞ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ F H'}
  [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M]
  {J : SmoothAlmostComplexStructure I P} {L : SmoothAlmostComplexStructure I' M}
  {σ : SmoothTwoForm I P} {τ : SmoothTwoForm I' M}

/-- The product form on a tangent vector `v` of `P × M` and its image under `J × L` is the sum of
`σ` on the first component and its image under `J` and of `τ` on the second component and its
image under `L`. -/
theorem eval₂_prod_prod_apply (σ : SmoothTwoForm I P) (τ : SmoothTwoForm I' M) (p : P × M)
    (v w : TangentSpace (I.prod I') p) :
    (σ.prod τ).eval₂ p v (prod J L p w) =
      σ.eval₂ p.1 (Manifold.tangentSpaceProdEquiv p v).1
          (J p.1 (Manifold.tangentSpaceProdEquiv p w).1) +
        τ.eval₂ p.2 (Manifold.tangentSpaceProdEquiv p v).2
          (L p.2 (Manifold.tangentSpaceProdEquiv p w).2) := by
  rw [SmoothTwoForm.eval₂_prod, prod_apply, ContinuousLinearEquiv.apply_symm_apply]

/-- **Products of tame pairs are tame.** If `σ` tames `J` and `τ` tames `L`, the product form
`pr₁^*σ + pr₂^*τ` tames `J × L`. -/
theorem tames_prod (hσ : σ.Tames J) (hτ : τ.Tames L) : (σ.prod τ).Tames (prod J L) := by
  rw [SmoothTwoForm.tames_iff]
  intro p v hv
  have h := SymplecticForm.prod_tames (hσ.isNondegenerate.tames_iff.1 hσ p.1)
    (hτ.isNondegenerate.tames_iff.1 hτ p.2) (Manifold.tangentSpaceProdEquiv p v)
    ((Manifold.tangentSpaceProdEquiv p).map_ne_zero_iff.2 hv)
  rw [SymplecticForm.prod_apply_prod_self] at h
  rw [eval₂_prod_prod_apply]
  simpa using h

/-- **Products of invariant pairs are invariant.** If `J` preserves `σ` and `L` preserves `τ`, then
`J × L` preserves the product form `pr₁^*σ + pr₂^*τ`. -/
theorem invariant_prod (hσ : σ.Invariant J) (hτ : τ.Invariant L) :
    (σ.prod τ).Invariant (prod J L) := by
  rw [SmoothTwoForm.invariant_iff] at hσ hτ ⊢
  intro p v w
  simp only [SmoothTwoForm.eval₂_prod, prod_apply, ContinuousLinearEquiv.apply_symm_apply, hσ,
    hτ]

end Tames

section ComplexManifold

variable {E F M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℂ, F) ∞ N]

/-- The product of the almost complex structures of two complex manifolds is multiplication by `i`
on every tangent space `E × F` of their product. -/
theorem prod_ofComplexManifold_apply (p : M × N) (v : E × F) :
    (ofComplexManifold E M).prod (ofComplexManifold F N) p v = Complex.I • v := by
  refine (prod_apply _ _ p v).trans ?_
  -- `Manifold.tangentSpaceProdEquiv_apply` does not rewrite directly: `v` is stated in `E × F`.
  have h : Manifold.tangentSpaceProdEquiv (I := 𝓘(ℝ, E)) (J := 𝓘(ℝ, F)) p v = v :=
    Manifold.tangentSpaceProdEquiv_apply p v
  rw [Manifold.tangentSpaceProdEquiv_symm_apply, h]
  exact Prod.ext (ofComplexManifold_apply p.1 v.1) (ofComplexManifold_apply p.2 v.2)

attribute [local instance] chartedSpaceProd isManifold_chartedSpaceProd

/-- With the product charts `TauCeti.chartedSpaceProd`, the almost complex structure of the complex
manifold `M × N` agrees on each tangent vector with the product of the almost complex structures
of `M` and `N`. The two structures are over the models `𝓘(ℝ, E × F)` and
`𝓘(ℝ, E).prod 𝓘(ℝ, F)`, whose tangent spaces are both `E × F`. -/
theorem ofComplexManifold_prod_apply (p : M × N) (v : E × F) :
    ofComplexManifold (E × F) (M × N) p v =
      (ofComplexManifold E M).prod (ofComplexManifold F N) p v :=
  (ofComplexManifold_apply p v).trans (prod_ofComplexManifold_apply p v).symm

/-- If `σ` tames the almost complex structure of the complex manifold `M` and `τ` that of `N`,
then the product form `pr₁^*σ + pr₂^*τ` is positive on `(v, J v)` for every nonzero tangent vector
`v` of `M × N`, where `J` is the almost complex structure of the complex manifold `M × N` with the
product charts `TauCeti.chartedSpaceProd`. The form and `J` are over the different models
`𝓘(ℝ, E).prod 𝓘(ℝ, F)` and `𝓘(ℝ, E × F)`, so this is not a `Tames` statement. -/
theorem eval₂_prod_ofComplexManifold_pos {σ : SmoothTwoForm 𝓘(ℝ, E) M}
    {τ : SmoothTwoForm 𝓘(ℝ, F) N} (hσ : σ.Tames (ofComplexManifold E M))
    (hτ : τ.Tames (ofComplexManifold F N)) (p : M × N) (v : E × F) (hv : v ≠ 0) :
    0 < (σ.prod τ).eval₂ p v (ofComplexManifold (E × F) (M × N) p v) := by
  rw [ofComplexManifold_prod_apply]
  exact SmoothTwoForm.tames_iff.1 (tames_prod hσ hτ) p v hv

end ComplexManifold

end TauCeti.SmoothAlmostComplexStructure

end
