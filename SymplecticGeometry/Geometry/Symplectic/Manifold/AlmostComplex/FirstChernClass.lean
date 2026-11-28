/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Manifold.AlmostComplex.NormalSplitting
public import TauCeti.Topology.VectorBundle.Orientation.Complex.FirstChernClass
public import TauCeti.Geometry.Symplectic.Manifold.JHolomorphic
import SymplecticGeometry.Geometry.Manifold.VectorBundle.FirstChernClass
import SymplecticGeometry.Geometry.Manifold.VectorBundle.Symplectic.FirstChernClass

/-!
# The first Chern class along a pseudoholomorphic embedding

Let `J` be a smooth almost complex structure on a manifold `X`, `j` one on a Hausdorff,
σ-compact manifold `M`, and `f : M → X` a smooth embedding that is pseudoholomorphic from `j`
to `J`. Its normal bundle `ν` carries the complex structure that `J` induces on it
(`TauCeti.SmoothEmbedding.normalComplexStructure`). The first Chern class of `(TX, J)` pulls
back to the sum of those of `(TM, j)` and of `ν`
(`TauCeti.SmoothEmbedding.firstChernClass_pullback_eq_add`):

`f^* c₁(TX, J) = c₁(TM, j) + c₁(ν)` in `H²(M; ℤ)`.

## Main results

* `TauCeti.SmoothEmbedding.firstChernClass_pullback_eq_add`: the formula above.

## Proof

The class `f^* c₁(TX, J)` is that of the pull-back `Jf` of `J` to `f *ᵖ TX`
(`SymplecticGeometry.Bundle.ContMDiffComplexStructure.firstChernClass_pullback`). Choose a
two-form `ω` compatible with `Jf`
(`SymplecticGeometry.Bundle.ContMDiffComplexStructure.exists_compatible`).
The splitting along the `ω`-orthogonal of the tangent images is smooth, and transports `Jf` to
the direct sum of `j` and of the normal structure
(`TauCeti.SmoothEmbedding.pushforward_pullbackComplexStructure_normalSplitting`), so these have
the same class
(`SymplecticGeometry.Bundle.ContMDiffComplexStructure.firstChernClass_pushforward`). The
complex bundle of a direct sum of structures is the direct sum of their complex bundles
(`SymplecticGeometry.Bundle.ContMDiffComplexStructure.prodFiberEquiv`), and the Whitney formula
`SymplecticGeometry.Bundle.firstChernClass_prod_of_chartedSpace` ends the proof. This is the
splitting used, at the level of Chern numbers of a surface, in
`TauCeti.SmoothEmbedding.adjunction_formula`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  Example 4.4.5.
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §14.
-/

public section

open _root_.Bundle Module
open scoped Manifold

namespace TauCeti.SmoothEmbedding

open SymplecticGeometry.Bundle

variable {E : Type} {H : Type*} {X : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace X]
  [ChartedSpace H X] [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) X]
  {E' : Type} {H' : Type*} {M : Type} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [FiniteDimensional ℝ E'] [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ((⊤ : ℕ∞) : WithTop ℕ∞) M]
  {hn : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0}
  {f : SmoothEmbedding I' I ((⊤ : ℕ∞) : WithTop ℕ∞) M X} {j : SmoothAlmostComplexStructure I' M}
  {J : SmoothAlmostComplexStructure I X}

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

/-- **The first Chern class along a pseudoholomorphic embedding.** Let `f : M → X` be a smooth
embedding of a Hausdorff, σ-compact manifold that is pseudoholomorphic from `j` to `J`, and give
its normal bundle the complex structure that `J` induces on it, with model fibre `P` of dimension
`hdim`. Then `f^* c₁(TX, J) = c₁(TM, j) + c₁(ν)` in `H²(M; ℤ)`, with any complex models `G`,
`G'`, `Gν` of the three complex bundles. -/
theorem firstChernClass_pullback_eq_add [T2Space M] [SigmaCompactSpace M]
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E') (hf : IsPseudoholomorphic j J f)
    (G : Type*) [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G]
    [Fact (finrank ℝ E = 2 * finrank ℂ G)]
    (G' : Type*) [NormedAddCommGroup G'] [NormedSpace ℂ G'] [FiniteDimensional ℂ G']
    [Fact (finrank ℝ E' = 2 * finrank ℂ G')]
    (Gν : Type*) [NormedAddCommGroup Gν] [NormedSpace ℂ Gν] [FiniteDimensional ℂ Gν]
    [Fact (finrank ℝ P = 2 * finrank ℂ Gν)] :
    letI := f.normalSpaceFiberBundle hn hdim
    letI := f.normalSpaceVectorBundle hn hdim
    TopCat.singularCohomologyMap (TopCat.ofHom (f : C(M, X))) 2
        (firstChernClass G (J.toContMDiff ⊤).toContinuousComplexStructure.Fiber) =
      firstChernClass G' (j.toContMDiff ⊤).toContinuousComplexStructure.Fiber +
        firstChernClass Gν (f.normalComplexStructure hn J hdim fun x ↦
          mapsTo_tangentRange_of_isPseudoholomorphicAt hn (hf.isPseudoholomorphicAt x)).Fiber := by
  let := f.normalSpaceFiberBundle hn hdim
  let := f.normalSpaceVectorBundle hn hdim
  let := f.normalSpaceContMDiffVectorBundle (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) hn (by simp) hdim
  have : ContMDiffVectorBundle ((⊤ : ℕ∞) : WithTop ℕ∞) E ((f : M → X) *ᵖ (TangentSpace I)) I' :=
    _root_.Bundle.Pullback.contMDiffVectorBundle (E := TangentSpace I) f.contMDiff
  have : Fact (finrank ℝ (E' × P) = 2 * finrank ℂ (G' × Gν)) :=
    ⟨by rw [finrank_prod, finrank_prod, Fact.out (p := finrank ℝ E' = 2 * finrank ℂ G'),
      Fact.out (p := finrank ℝ P = 2 * finrank ℂ Gν), mul_add]⟩
  have hJ x := mapsTo_tangentRange_of_isPseudoholomorphicAt hn (hf.isPseudoholomorphicAt x)
  obtain ⟨ω, hω⟩ := (J.pullbackComplexStructure f f.contMDiff).exists_compatible
  have hΦ := contMDiff_normalSplitting hdim hJ hω.tames
  rw [← ContMDiffComplexStructure.toContinuousComplexStructure_tangentEquiv_symm,
    ← ContMDiffComplexStructure.firstChernClass_pullback G _ f f.contMDiff,
    ← SmoothAlmostComplexStructure.pullbackComplexStructure_def,
    ← ContMDiffComplexStructure.firstChernClass_pushforward G (G' × Gν) _ hΦ,
    pushforward_pullbackComplexStructure_normalSplitting hdim hJ hf hω,
    TauCeti.firstChernClass_eq_of_fiberwise (φ := ContMDiffComplexStructure.prodFiberEquiv _ _)
      (ContMDiffComplexStructure.continuous_prodFiberEquiv _ G' Gν _ _),
    firstChernClass_prod_of_chartedSpace I',
    ContMDiffComplexStructure.toContinuousComplexStructure_tangentEquiv_symm,
    toContinuousComplexStructure_contMDiffNormalComplexStructure]

end TauCeti.SmoothEmbedding

end
