/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Manifold.AlmostComplex.SelfIntersection
public import TauCeti.AlgebraicTopology.Singular.SurfaceGenus
import SymplecticGeometry.Geometry.Manifold.VectorBundle.ChernNumber.Axioms
import SymplecticGeometry.Geometry.Symplectic.Manifold.AlmostComplex.NormalSplitting

/-!
# The adjunction formula

Let `X` be a manifold of real dimension four with a smooth almost complex structure `J`, and let
`f : M → X` embed a closed connected surface `M` so that `J` preserves its tangent planes. Orient
`M` by `J`: every frame `(u, v)` of `T_c M` with `df v = J (df u)` is positive. The **adjunction
formula** `TauCeti.SmoothEmbedding.adjunction_formula` says

`2 g - 2 = M · M - ⟨c₁(TX, J), f_*[M]⟩`,

with `g = TauCeti.surfaceGenus M` and `M · M` the Euler number of the normal bundle oriented by
the complex structure that `J` induces on it
(`TauCeti.SmoothEmbedding.selfIntersectionNumber`). With the canonical class `K = -c₁(TX, J)` it
reads `K · M + M · M = 2 g - 2`.

## Main results

* `TauCeti.SmoothEmbedding.adjunction_formula`: the adjunction formula.

## Proof

Choose a two-form `ω` on `f *ᵖ TX` compatible with the pull-back `Jf` of `J`
(`SymplecticGeometry.Bundle.ContMDiffComplexStructure.exists_compatible`; the base `M` is
compact). The evaluation `⟨c₁(TX, J), f_*[M]⟩` is the first Chern number of `(f *ᵖ TX, Jf)`
(`SymplecticGeometry.Bundle.chernNumber_pullback_complexStructure`), so that of the symplectic
bundle `(f *ᵖ TX, ω)` (`SymplecticGeometry.Bundle.symplecticChernNumber_eq_chernNumber`). The
splitting `TauCeti.SmoothEmbedding.normalSplitting` identifies `(f *ᵖ TX, ω)` with the direct sum
of `(TM, ω(df ·, df ·))` and `(ν, ω_ν)` (`TauCeti.SmoothEmbedding.pushforward_normalSplitting`),
so the number is the sum of their numbers
(`SymplecticGeometry.Bundle.symplecticChernNumber_congr`,
`SymplecticGeometry.Bundle.symplecticChernNumber_whitneySum`). The first is `2 - 2 g`
(`SymplecticGeometry.Bundle.symplecticChernNumber_tangent`), since the area form induces the
orientation of `M` (`TauCeti.SmoothEmbedding.volumeOrientation_compMFDeriv`); the second is the
self-intersection number, since `ω_ν` is compatible with the complex structure of `ν`
(`TauCeti.SmoothEmbedding.compatible_normalForm`,
`TauCeti.SmoothEmbedding.selfIntersectionNumber_eq_chernNumber`).

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

open SymplecticGeometry SymplecticGeometry.Bundle

variable {E : Type} {H : Type*} {X : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace X] [ChartedSpace H X]
  [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) X]
  {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
  [IsManifold (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) M] {hn : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0}

attribute [local instance] Complex.finrank_real_complex_eq_two_mul_finrank_fact

variable [FiniteDimensional ℝ E]

/-- **The adjunction formula.** Let `X` be a manifold of real dimension four with a smooth almost
complex structure `J`, and `f` a smooth embedding of a compact connected surface `M` whose
tangent planes `J` preserves. Orient `M` by `J`: `o` is the orientation for which every basis
`(u, v)` of `T_c M` with `df v = J (df u)` is positive. Then
`2 g - 2 = M · M - ⟨c₁(TX, J), f_*[M]⟩`, where `g` is the genus of `M`, `M · M` is
`f.selfIntersectionNumber hE J hJ o`, the Euler number of the normal bundle oriented by the
complex structure that `J` induces on it, and `c₁(TX, J)` is the first Chern class of the complex
tangent bundle of `(X, J)`, with any complex model `G`, evaluated on the image of the fundamental
class of `(M, o)`. With `K = -c₁(TX, J)` this is `K · M + M · M = 2 g - 2`.

Milestone: *Adjunction formula*. -/
theorem adjunction_formula [T2Space M] [CompactSpace M] [ConnectedSpace M]
    (hE : finrank ℝ E = 4)
    (G : Type*) [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G]
    [Fact (finrank ℝ E = 2 * finrank ℂ G)]
    (f : SmoothEmbedding (𝓡 2) I ((⊤ : ℕ∞) : WithTop ℕ∞) M X)
    (J : SmoothAlmostComplexStructure I X)
    (hJ : ∀ x, Set.MapsTo (J (f x)) (f.isImmersion.tangentRange x hn)
        (f.isImmersion.tangentRange x hn))
    (o : Manifold.Orientation (𝓡 2) M (Fin 2))
    (ho : ∀ c (b : Basis (Fin 2) ℝ (TangentSpace (𝓡 2) c)),
      mfderiv (𝓡 2) I f c (b 1) = J (f c) (mfderiv (𝓡 2) I f c (b 0)) →
        b.orientation = o.orientationAt c) :
    2 * (surfaceGenus M : ℤ) - 2 =
      f.selfIntersectionNumber hE J hJ o -
        ((o.toHomologicalOrientation finrank_euclideanSpace_fin).evalFundamentalClass
          finrank_euclideanSpace_fin (ModuleCat.of ℤ (ULift ℤ)) (f : C(M, X))
          (TauCeti.firstChernClass G
            (J.toContMDiff ⊤).toContinuousComplexStructure.Fiber)).down := by
  have hdim := finrank_real_complex_eq_sub_of_finrank_eq_four hE
  let := f.normalSpaceFiberBundle hn hdim
  let := f.normalSpaceVectorBundle hn hdim
  let := f.normalSpaceContMDiffVectorBundle (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) hn (by simp) hdim
  have : ContMDiffVectorBundle ((⊤ : ℕ∞) : WithTop ℕ∞) E ((f : M → X) *ᵖ (TangentSpace I))
      (𝓡 2) :=
    Bundle.Pullback.contMDiffVectorBundle (E := TangentSpace I) f.contMDiff
  have : Fact (finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℂ) = 2 * finrank ℂ G) :=
    ⟨by rw [finrank_prod, finrank_euclideanSpace_fin, Complex.finrank_real_complex,
      ← Fact.out (p := finrank ℝ E = 2 * finrank ℂ G), hE]⟩
  have : Fact (finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2 * finrank ℂ ℂ) :=
    ⟨by rw [finrank_euclideanSpace_fin, finrank_self]⟩
  set oₕ := o.toHomologicalOrientation finrank_euclideanSpace_fin
  obtain ⟨ω, hω⟩ := (J.pullbackComplexStructure f f.contMDiff).exists_compatible
  -- `⟨c₁(TX, J), f_*[M]⟩` is the first Chern number of `(f *ᵖ TX, ω)`.
  have h₁ : (oₕ.evalFundamentalClass finrank_euclideanSpace_fin (ModuleCat.of ℤ (ULift ℤ))
      (f : C(M, X)) (TauCeti.firstChernClass G
        (J.toContMDiff ⊤).toContinuousComplexStructure.Fiber)).down
      = symplecticChernNumber oₕ finrank_euclideanSpace_fin G ω := by
    rw [symplecticChernNumber_eq_chernNumber _ _ _ hω.tames,
      SmoothAlmostComplexStructure.pullbackComplexStructure_def,
      chernNumber_pullback_complexStructure,
      ContMDiffComplexStructure.toContinuousComplexStructure_tangentEquiv_symm]
  -- The splitting `f *ᵖ TX ≃ TM ×ᵇ ν` carries `ω` to the sum of the two forms.
  have h₂ : symplecticChernNumber oₕ finrank_euclideanSpace_fin G ω =
      symplecticChernNumber oₕ finrank_euclideanSpace_fin ℂ (ω.compMFDeriv f f.contMDiff) +
        symplecticChernNumber oₕ finrank_euclideanSpace_fin ℂ
          (f.normalForm hdim hJ ω hω.tames) := by
    rw [← symplecticChernNumber_whitneySum _ _ G ℂ ℂ (isNondegenerate_compMFDeriv hJ hω.tames)
      (compatible_normalForm hdim hJ hω).tames.isNondegenerate,
      ← pushforward_normalSplitting hdim hJ hω.tames]
    exact (symplecticChernNumber_congr _ _ G G hω.tames.isNondegenerate _
      (contMDiff_normalSplitting hdim hJ hω.tames)
      ((ContMDiffTwoForm.pushforward_eq_iff _ _).1 rfl)).symm
  -- The tangent summand has number `2 - 2 g`.
  have h₃ : symplecticChernNumber oₕ finrank_euclideanSpace_fin ℂ (ω.compMFDeriv f f.contMDiff) =
      2 - 2 * surfaceGenus M := by
    rw [← (ContMDiffTwoForm.tangentEquiv (M := M)).symm_apply_apply (ω.compMFDeriv f f.contMDiff)]
    exact symplecticChernNumber_tangent _ o ℂ _
      (volumeOrientation_compMFDeriv finrank_euclideanSpace_fin hJ hω.tames ho)
  -- The normal summand is the self-intersection number.
  have h₄ : symplecticChernNumber oₕ finrank_euclideanSpace_fin ℂ
      (f.normalForm hdim hJ ω hω.tames) = f.selfIntersectionNumber hE J hJ o := by
    rw [symplecticChernNumber_eq_chernNumber _ _ _ (compatible_normalForm hdim hJ hω).tames,
      selfIntersectionNumber_eq_chernNumber,
      toContinuousComplexStructure_contMDiffNormalComplexStructure]
  rw [h₁, h₂, h₃, h₄]
  ring

end TauCeti.SmoothEmbedding

end
