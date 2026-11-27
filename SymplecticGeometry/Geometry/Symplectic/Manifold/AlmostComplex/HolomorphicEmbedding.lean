/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.RestrictScalars
public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure
public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.Level
public import SymplecticGeometry.Geometry.Symplectic.Manifold.AlmostComplex.Submanifold
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Prod
import SymplecticGeometry.Geometry.Symplectic.Manifold.AlmostComplex.Prod

/-!
# Real forms of holomorphic embeddings and almost complex structures

Let `f : M → N` be a holomorphic embedding of complex manifolds and `f.restrictScalars ℝ hnm hn`
its real form, a smooth embedding of the underlying real manifolds
(`TauCeti.SmoothEmbedding.restrictScalars`). The tangent ranges of the real form are the images
of complex linear maps, so they are invariant under the almost complex structure
`TauCeti.SmoothAlmostComplexStructure.ofComplexManifold` of `N`, which is multiplication by `i`
on every tangent space. The same holds for an embedding into a product `N × N'` of complex
manifolds and the product of the almost complex structures of `N` and `N'`, which is again
multiplication by `i` (`TauCeti.SmoothAlmostComplexStructure.prod_ofComplexManifold_apply`).

These are the hypotheses, written
`∀ x, Set.MapsTo (J (f x)) (f.isImmersion.tangentRange x hn) (f.isImmersion.tangentRange x hn)`,
under which `AlmostComplex/Submanifold.lean` restricts an almost complex structure and pulls back
taming forms. So a complex submanifold, such as a smooth hypersurface, is a symplectic
submanifold for every form that tames the complex structure of the ambient manifold.

The structure that the complex structure of `N` restricts to along the real form is the complex
structure of `M`, and likewise for the product structure on `N × N'`: by
`TauCeti.SmoothAlmostComplexStructure.eq_restrict_iff`, this asks that the real derivative of `f`
commute with multiplication by `i`, and it is the complex derivative of `f`
(`TauCeti.SmoothEmbedding.coe_mfderiv_restrictScalars`,
`TauCeti.SmoothEmbedding.coe_mfderiv_restrictScalarsProd`).

When a complex valued `g : N → V` cuts out the image of such an embedding near a point `f x`,
its real differential identifies the normal space at `x` with `V`
(`TauCeti.SmoothEmbedding.normalSpaceEquivOfLevel`). If `g` is holomorphic at `f x`, this
identification carries the complex structure that `N` induces on the normal space
(`TauCeti.SmoothEmbedding.normalComplexStructureAt`) to multiplication by `i`: the normal
complex structure is `[v] ↦ [i v]` (`TauCeti.SmoothEmbedding.normalComplexStructureAt_normalClass`),
and the real differential of `g` commutes with `i`
(`MDifferentiableAt.mfderiv_ofComplexManifold_apply`).

## Main results

* `TauCeti.SmoothEmbedding.mapsTo_ofComplexManifold_tangentRange_restrictScalars`: the
  tangent ranges of the real form of a holomorphic embedding are invariant under the almost complex
  structure of the target.
* `TauCeti.SmoothEmbedding.mapsTo_prod_ofComplexManifold_tangentRange_restrictScalarsProd`: the
  same for a holomorphic embedding into a product and the product almost complex structure.
* `TauCeti.SmoothEmbedding.normalComplexStructureAt_normalSpaceEquivOfLevel_symm`: the normal
  trivialization by the real differential of a holomorphic defining function is complex linear.
* `TauCeti.SmoothEmbedding.restrict_ofComplexManifold`: the almost complex structure of the
  target restricts along the real form to that of the source.
* `TauCeti.SmoothEmbedding.restrict_prod_ofComplexManifold`: the same for a holomorphic
  embedding into a product and the product almost complex structure.

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
theorem mapsTo_ofComplexManifold_tangentRange_restrictScalars
    (f : SmoothEmbedding 𝓘(ℂ, E) 𝓘(ℂ, E') m M N) (hnm : n ≤ m) (hn : 1 ≤ n) (hn₀ : n ≠ 0)
    (x : M) :
    Set.MapsTo (ofComplexManifold E' N (f.restrictScalars ℝ hnm hn x))
      ((f.restrictScalars ℝ hnm hn).isImmersion.tangentRange x hn₀)
      ((f.restrictScalars ℝ hnm hn).isImmersion.tangentRange x hn₀) := fun v hv ↦
  -- `ofComplexManifold_apply` states `v` in `E'`, so it does not rewrite the goal directly.
  (ofComplexManifold_apply (E := E') (M := N) _ v).symm ▸
    f.smul_mem_tangentRange_restrictScalars hnm hn x hn₀ Complex.I hv

/-- The almost complex structure that the complex structure of `N` restricts to along the real
form of a holomorphic embedding `f : M → N` is the complex structure of `M`. -/
theorem restrict_ofComplexManifold [CompleteSpace E] [IsManifold 𝓘(ℂ, E) ∞ M]
    (f : SmoothEmbedding 𝓘(ℂ, E) 𝓘(ℂ, E') m M N) (hnm : ∞ ≤ m)
    {hn₀ : (∞ : ℕ∞ω) ≠ 0} :
    (ofComplexManifold E' N).restrict (f.restrictScalars ℝ hnm (by simp)) (hn := hn₀)
        (f.mapsTo_ofComplexManifold_tangentRange_restrictScalars hnm (by simp) hn₀) =
      ofComplexManifold E M := by
  refine ((eq_restrict_iff _).2 fun x v ↦ ?_).symm
  -- `ofComplexManifold_apply` states `v` in the model space, so it does not rewrite directly.
  have hJ := ofComplexManifold_apply (E := E) x v
  have h := ofComplexManifold_apply (E := E') (f.restrictScalars ℝ hnm (by simp) x)
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E') (f.restrictScalars ℝ hnm (by simp)) x v)
  rw [hJ, h, coe_mfderiv_restrictScalars]
  exact (mfderiv _ _ f x).map_smul Complex.I v

section NormalSpaceEquivOfLevel

variable {F H : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
  {I : ModelWithCorners ℝ F H} {P : Type*} [TopologicalSpace P] [ChartedSpace H P]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

omit [IsManifold 𝓘(ℝ, E') n N] in
/-- **The normal trivialization by a holomorphic defining function is complex linear.** Let `f`
be an embedding into a complex manifold `N` whose tangent range at `x` is invariant under the
complex structure of `N`, and let `g : N → V` be constant near `x` on the image of `f`, with
onto real differential at `f x` and complementary dimension, so that its real differential
induces an isomorphism `e` of the normal space at `x` with `V`
(`TauCeti.SmoothEmbedding.normalSpaceEquivOfLevel`). If `g` is complex differentiable at `f x`,
then the complex structure that `N` induces on the normal space sends `e⁻¹ z` to `e⁻¹ (i • z)`.
This applies to the real form of a holomorphic embedding, by
`TauCeti.SmoothEmbedding.mapsTo_ofComplexManifold_tangentRange_restrictScalars`. -/
theorem normalComplexStructureAt_normalSpaceEquivOfLevel_symm
    (f : SmoothEmbedding I 𝓘(ℝ, E') n P N) (hn₀ : n ≠ 0) (x : P)
    (hJ : Set.MapsTo (ofComplexManifold E' N (f x)) (f.isImmersion.tangentRange x hn₀)
      (f.isImmersion.tangentRange x hn₀))
    {g : N → V} {c : V} (hgf : ∀ᶠ y in nhds x, g (f y) = c)
    (hsurj : IsRegularPoint 𝓘(ℝ, E') 𝓘(ℝ, V) g (f x))
    (hdim : Module.finrank ℝ F + Module.finrank ℝ V = Module.finrank ℝ E')
    (hg : MDifferentiableAt 𝓘(ℂ, E') 𝓘(ℂ, V) g (f x)) (z : V) :
    f.normalComplexStructureAt hn₀ (ofComplexManifold E' N) x hJ
        ((f.normalSpaceEquivOfLevel x hn₀ hgf hsurj hdim).symm z) =
      (f.normalSpaceEquivOfLevel x hn₀ hgf hsurj hdim).symm (Complex.I • z) := by
  obtain ⟨w, rfl⟩ := (f.normalSpaceEquivOfLevel x hn₀ hgf hsurj hdim).surjective z
  obtain ⟨v, rfl⟩ := f.isImmersion.normalClass_surjective x hn₀ w
  rw [ContinuousLinearEquiv.symm_apply_apply, normalComplexStructureAt_normalClass,
    ContinuousLinearEquiv.eq_symm_apply, normalSpaceEquivOfLevel_normalClass,
    normalSpaceEquivOfLevel_normalClass, hg.mfderiv_ofComplexManifold_apply]
  -- The structure of `V` as a complex manifold is multiplication by `i`.
  exact ofComplexManifold_apply _ _

end NormalSpaceEquivOfLevel

variable {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℂ F'] [FiniteDimensional ℂ F']
  {N' : Type*} [TopologicalSpace N'] [ChartedSpace F' N'] [IsManifold 𝓘(ℂ, F') ∞ N']
  [IsManifold 𝓘(ℝ, F') n N']

/-- The tangent ranges of the real form of a holomorphic embedding into a product `N × N'` of
complex manifolds are invariant under the product of the almost complex structures of `N` and
`N'`. -/
theorem mapsTo_prod_ofComplexManifold_tangentRange_restrictScalarsProd
    (f : SmoothEmbedding 𝓘(ℂ, E) (𝓘(ℂ, E').prod 𝓘(ℂ, F')) m M (N × N')) (hnm : n ≤ m)
    (hn : 1 ≤ n) (hn₀ : n ≠ 0) (x : M) :
    Set.MapsTo ((ofComplexManifold E' N).prod (ofComplexManifold F' N')
        (f.restrictScalarsProd ℝ hnm hn x))
      ((f.restrictScalarsProd ℝ hnm hn).isImmersion.tangentRange x hn₀)
      ((f.restrictScalarsProd ℝ hnm hn).isImmersion.tangentRange x hn₀) := fun v hv ↦
  -- `prod_ofComplexManifold_apply` states `v` in `E' × F'`, so it does not rewrite the goal
  -- directly.
  (prod_ofComplexManifold_apply (M := N) (N := N') _ v).symm ▸
    f.smul_mem_tangentRange_restrictScalarsProd hnm hn x hn₀ Complex.I hv

/-- The almost complex structure that the product of the complex structures of `N` and `N'`
restricts to along the real form of a holomorphic embedding `f : M → N × N'` is the complex
structure of `M`. -/
theorem restrict_prod_ofComplexManifold [CompleteSpace E] [IsManifold 𝓘(ℂ, E) ∞ M]
    (f : SmoothEmbedding 𝓘(ℂ, E) (𝓘(ℂ, E').prod 𝓘(ℂ, F')) m M (N × N')) (hnm : ∞ ≤ m)
    {hn₀ : (∞ : ℕ∞ω) ≠ 0} :
    ((ofComplexManifold E' N).prod (ofComplexManifold F' N')).restrict
        (f.restrictScalarsProd ℝ hnm (by simp)) (hn := hn₀)
        (f.mapsTo_prod_ofComplexManifold_tangentRange_restrictScalarsProd hnm (by simp) hn₀) =
      ofComplexManifold E M := by
  refine ((eq_restrict_iff _).2 fun x v ↦ ?_).symm
  -- `ofComplexManifold_apply` and `prod_ofComplexManifold_apply` state `v` in the model space,
  -- so they do not rewrite directly.
  have hJ := ofComplexManifold_apply (E := E) x v
  have h := prod_ofComplexManifold_apply (M := N) (N := N')
    (f.restrictScalarsProd ℝ hnm (by simp) x)
    (mfderiv 𝓘(ℝ, E) (𝓘(ℝ, E').prod 𝓘(ℝ, F')) (f.restrictScalarsProd ℝ hnm (by simp)) x v)
  rw [hJ, h, coe_mfderiv_restrictScalarsProd]
  exact (mfderiv _ _ f x).map_smul Complex.I v

end TauCeti.SmoothEmbedding

end
