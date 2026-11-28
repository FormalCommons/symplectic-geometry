/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Manifold.AlmostComplex.NormalSplitting
public import TauCeti.Topology.VectorBundle.Orientation.Complex.FirstChernClass
public import TauCeti.Geometry.Symplectic.Manifold.JHolomorphic
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import SymplecticGeometry.Topology.VectorBundle.Complex.Structure
import SymplecticGeometry.Geometry.Manifold.VectorBundle.FirstChernClass
import SymplecticGeometry.Geometry.Manifold.VectorBundle.Symplectic.FirstChernClass

/-!
# The first Chern class along pseudoholomorphic maps

Let `J` be a smooth almost complex structure on a manifold `X`, `j` one on a Hausdorff,
σ-compact manifold `M`, and `f : M → X` a smooth embedding that is pseudoholomorphic from `j`
to `J`. Its normal bundle `ν` carries the complex structure that `J` induces on it
(`TauCeti.SmoothEmbedding.normalComplexStructure`). The first Chern class of `(TX, J)` pulls
back to the sum of those of `(TM, j)` and of `ν`
(`TauCeti.SmoothEmbedding.firstChernClass_pullback_eq_add`):

`f^* c₁(TX, J) = c₁(TM, j) + c₁(ν)` in `H²(M; ℤ)`.

The file also proves that the first Chern class is natural along a map `f : N → M`,
pseudoholomorphic from `j` to `J`, at the points where `f` is a local diffeomorphism. There
the differential of `f` is a complex-linear isomorphism of the complex tangent spaces
(`TauCeti.IsPseudoholomorphicAt.mfderivFiberEquiv`), so for a continuous map `ι : Y → N` into
that set, `ι^* c₁(TN, j) = ι^* f^* c₁(TM, J)`.

## Main results

* `TauCeti.SmoothEmbedding.firstChernClass_pullback_eq_add`: the formula above.
* `TauCeti.IsPseudoholomorphicAt.mfderivFiberEquiv`: at a point where a pseudoholomorphic map
  is a local diffeomorphism, its differential as a complex-linear isomorphism of the fibres of
  the complex tangent bundles. `TauCeti.IsPseudoholomorphicAt.continuous_mfderivFiberEquiv`:
  along a continuous map `ι` into such points, these isomorphisms are continuous on the total
  space of the pull-back by `ι`.
* `TauCeti.IsPseudoholomorphicAt.singularCohomologyMap_firstChernClass_eq`: the naturality
  `ι^* c₁(TN, j) = ι^* f^* c₁(TM, J)`, by
  `TauCeti.firstChernClass_eq_singularCohomologyMap_of_fiberwise`.

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

The fibre isomorphisms `TauCeti.IsPseudoholomorphicAt.mfderivFiberEquiv` and their continuity
adapt Tau Ceti's private `mfderivFiberEquiv` and `continuous_mfderivFiberRealEquiv`
(`TauCeti/Geometry/Symplectic/Manifold/AlmostComplex/Chern.lean`) from a diffeomorphism to a
pseudoholomorphic map at the points where it is a local diffeomorphism, and from the tangent
bundle of the source to its pull-back by `ι`.

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

namespace TauCeti.IsPseudoholomorphicAt

variable {E : Type} {H : Type*} {M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M]
  {E' : Type} {H' : Type*} {N : Type} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' ((⊤ : ℕ∞) : WithTop ℕ∞) N]
  {j : SmoothAlmostComplexStructure I' N} {J : SmoothAlmostComplexStructure I M} {f : N → M}
  {n : WithTop ℕ∞}

/-- At a point `x` where `f : N → M` is pseudoholomorphic from `j` to `J` and a local
diffeomorphism, its differential, as a real-linear isomorphism of tangent spaces, intertwines
`j x` with `J (f x)`. -/
theorem mfderivToContinuousLinearEquiv_apply_commute {x : N} (hj : IsPseudoholomorphicAt j J f x)
    (hf : IsLocalDiffeomorphAt I' I n f x) (hn : n ≠ 0) (v : TangentSpace I' x) :
    hf.mfderivToContinuousLinearEquiv hn ((j.toContMDiff ⊤).toContinuousComplexStructure x v) =
      (J.toContMDiff ⊤).toContinuousComplexStructure (f x)
        (hf.mfderivToContinuousLinearEquiv hn v) := by
  simp only [SmoothAlmostComplexStructure.toContMDiff_apply,
    ContMDiffAlmostComplexStructure.toContinuousComplexStructure_apply]
  rw [← ContinuousLinearEquiv.coe_coe, hf.mfderivToContinuousLinearEquiv_coe]
  exact hj.mfderiv_apply_commute v

/-- The differential at `x` of a map `f : N → M` that is pseudoholomorphic from `j` to `J` and a
local diffeomorphism at `x`, as a complex-linear isomorphism from the tangent space of `N` at
`x` with `j` to the tangent space of `M` at `f x` with `J`. -/
noncomputable def mfderivFiberEquiv {x : N} (hj : IsPseudoholomorphicAt j J f x)
    (hf : IsLocalDiffeomorphAt I' I n f x) (hn : n ≠ 0) :
    (j.toContMDiff ⊤).toContinuousComplexStructure.Fiber x ≃L[ℂ]
      (J.toContMDiff ⊤).toContinuousComplexStructure.Fiber (f x) :=
  _root_.TauCeti.Bundle.ContinuousComplexStructure.fiberEquivOfCommuteAt _ _
    (hf.mfderivToContinuousLinearEquiv hn) (hj.mfderivToContinuousLinearEquiv_apply_commute hf hn)

/-- On the underlying real tangent spaces, `mfderivFiberEquiv` is the differential of `f`. -/
@[simp]
theorem fiberEquiv_mfderivFiberEquiv {x : N} (hj : IsPseudoholomorphicAt j J f x)
    (hf : IsLocalDiffeomorphAt I' I n f x) (hn : n ≠ 0)
    (v : (j.toContMDiff ⊤).toContinuousComplexStructure.Fiber x) :
    (J.toContMDiff ⊤).toContinuousComplexStructure.fiberEquiv (f x)
        (hj.mfderivFiberEquiv hf hn v) =
      mfderiv I' I f x ((j.toContMDiff ⊤).toContinuousComplexStructure.fiberEquiv x v) := by
  rw [mfderivFiberEquiv,
    _root_.TauCeti.Bundle.ContinuousComplexStructure.fiberEquiv_fiberEquivOfCommuteAt,
    ← ContinuousLinearEquiv.coe_coe, hf.mfderivToContinuousLinearEquiv_coe]

variable (G : Type*) [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [Fact (finrank ℝ E = 2 * finrank ℂ G)]
  [Fact (finrank ℝ E' = 2 * finrank ℂ G)]
  {Y : Type} [TopologicalSpace Y] (ι : C(Y, N))

/-- Along a continuous map `ι : Y → N` into the points where a map `f`, pseudoholomorphic from
`j` to `J` at those points, is a local diffeomorphism, the isomorphisms `mfderivFiberEquiv`
are continuous from the total space of the pull-back by `ι` of `(TN, j)` to that of `(TM, J)`. -/
theorem continuous_mfderivFiberEquiv {f : C(N, M)}
    (hj : ∀ x, IsPseudoholomorphicAt j J f (ι x)) (hι : ∀ x, IsLocalDiffeomorphAt I' I n f (ι x))
    (hn : n ≠ 0) :
    Continuous fun v : TotalSpace G (⇑ι *ᵖ (j.toContMDiff ⊤).toContinuousComplexStructure.Fiber) ↦
      TotalSpace.mk' G (E := (J.toContMDiff ⊤).toContinuousComplexStructure.Fiber)
        (f (ι v.proj)) ((hj v.proj).mfderivFiberEquiv (hι v.proj) hn v.snd) := by
  refine _root_.TauCeti.Bundle.ContinuousComplexStructure.continuous_fiberEquivOfCommuteAt_pullback
    (G₁ := G) (G₂ := G) _ _ ι (fun x ↦ f (ι x)) _
    (fun x ↦ (hj x).mfderivToContinuousLinearEquiv_apply_commute (hι x) hn)
    ((continuous_iff_continuousAt.2 fun v ↦ ((hι v.proj).contMDiffAt.continuousAt_tangentMap
      (ENat.one_le_iff_ne_zero_withTop.2 hn)).comp
        (Pullback.continuous_lift _ _ _).continuousAt).congr fun v ↦ ?_)
  rw [Function.comp_apply]
  -- The map is `tangentMap f` after `Pullback.lift`. Neither has a lemma that reads it at `v`,
  -- and `IsLocalDiffeomorphAt.mfderivToContinuousLinearEquiv_coe` cannot be rewritten at the
  -- fibre of the pull-back that `v.snd` lies in, so all three are unfolded.
  rfl

/-- **Naturality of the first Chern class along a pseudoholomorphic local diffeomorphism.** Let
`f : N → M` be a map and `ι : Y → N` a continuous map such that, at every point `ι x`, `f`
is pseudoholomorphic from `j` to `J` and a local diffeomorphism. Then the pull-backs by `ι` of
`c₁(TN, j)` and of `f^* c₁(TM, J)` agree; both are computed with the complex model `G`. -/
theorem singularCohomologyMap_firstChernClass_eq {f : C(N, M)}
    (hj : ∀ x, IsPseudoholomorphicAt j J f (ι x)) (hι : ∀ x, IsLocalDiffeomorphAt I' I n f (ι x))
    (hn : n ≠ 0) :
    TopCat.singularCohomologyMap (TopCat.ofHom ι) 2
        (firstChernClass G (j.toContMDiff ⊤).toContinuousComplexStructure.Fiber) =
      TopCat.singularCohomologyMap (TopCat.ofHom ι) 2
        (TopCat.singularCohomologyMap (TopCat.ofHom f) 2
          (firstChernClass G (J.toContMDiff ⊤).toContinuousComplexStructure.Fiber)) := by
  have h := firstChernClass_eq_singularCohomologyMap_of_fiberwise
    (E' := ⇑ι *ᵖ (j.toContMDiff ⊤).toContinuousComplexStructure.Fiber)
    (g := f.comp ι)
    (φ := fun x ↦ (hj x).mfderivFiberEquiv (hι x) hn)
    (continuous_mfderivFiberEquiv G ι hj hι hn)
  rw [firstChernClass_pullback, TopCat.ofHom_comp, TopCat.singularCohomologyMap_comp,
    CategoryTheory.ConcreteCategory.comp_apply] at h
  exact h

end TauCeti.IsPseudoholomorphicAt

end
