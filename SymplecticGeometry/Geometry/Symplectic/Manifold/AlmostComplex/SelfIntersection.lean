/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Real
public import SymplecticGeometry.Geometry.Manifold.Complex.HomologicalOrientation
public import SymplecticGeometry.Geometry.Manifold.ModelTransport.Remodel
public import SymplecticGeometry.Geometry.Manifold.Orientation.Diffeomorph
public import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.Diffeomorph
public import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.NormalSpace.CompDiffeomorphOfBoundaryless
public import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.NormalSpace.ComplexStructure
public import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.NormalSpace.Exact
public import SymplecticGeometry.Geometry.Symplectic.Manifold.AlmostComplex.Submanifold
public import SymplecticGeometry.Topology.VectorBundle.Complex.FirstChernClass
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Smooth
public import TauCeti.LinearAlgebra.Orientation.ShortExact
public import TauCeti.Geometry.Symplectic.Manifold.JHolomorphic
import SymplecticGeometry.AlgebraicTopology.Cohomology.FundamentalClass
import SymplecticGeometry.Geometry.Manifold.Orientation.FundamentalClass
import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.NormalSpace.ThomPairMap
import SymplecticGeometry.LinearAlgebra.ComplexStructure.Orientation
import SymplecticGeometry.Topology.VectorBundle.Complex.Structure

/-!
# The self-intersection number of a `J`-invariant surface

Let `X` be a manifold of real dimension four with an almost complex structure `J`, and let
`f : M → X` embed a compact surface `M`, oriented by `o`, so that its tangent planes are
`J`-invariant. Then `J` descends to a complex structure on the normal bundle `ν` of `f`
(Tau Ceti's `TauCeti.SmoothEmbedding.normalComplexStructure`), which makes `ν` a complex line
bundle `ν_J` with model fibre `ℂ`. The number `TauCeti.SmoothEmbedding.selfIntersectionNumber`
is the evaluation on the fundamental class of `(M, o)` of Tau Ceti's Euler class
`TauCeti.complexEulerClass ℂ ν_J`: the Euler number of `ν` oriented by its complex structure.

When `o` is the orientation of `M` given by `J`, this is the **self-intersection number** `M · M`.
Then the orientations of `M` and of `ν` together give that of `X`: the short exact sequence
`0 → T_c M → T_{f c} X → ν_c → 0` induces, from `o` and the complex orientation of `ν_c`, the
complex orientation of `T_{f c} X` (`TauCeti.SmoothEmbedding.shortExact_orientationAt_normalSpace`,
which holds for an embedding of any dimension).
Its linear algebra is `TauCeti.AlmostComplexStructure.shortExact_orientation`. For the opposite
orientation of `M` the number is `-(M · M)`, since `M · M` itself does not depend on the
orientation of `M`.

## Main definitions

* `TauCeti.SmoothEmbedding.selfIntersectionNumber`: the Euler number of the normal bundle with its
  complex orientation, on the fundamental class of `(M, o)`.

## Main results

* `TauCeti.SmoothEmbedding.selfIntersectionNumber_eq_chernNumber`: it is the first Chern number of
  the complex line bundle `ν_J`.
* `TauCeti.SmoothEmbedding.selfIntersectionNumber_neg_orientation`: reversing the orientation of
  `M` negates the number.
* `TauCeti.SmoothEmbedding.selfIntersectionNumber_eq_of_comp`: the number depends only on the
  first-order behaviour of the ambient data along the surface. A map `φ` with `φ ∘ f = f'` that
  is `C¹` and `(J, J')`-holomorphic, with invertible derivative, at the points of `f(M)` gives
  equal numbers for `f` and `f'`: its derivative identifies the two complex normal bundles
  (`TauCeti.SmoothEmbedding.normalSpaceEquivOfComp`), and Tau Ceti's
  `TauCeti.complexEulerClass_eq_of_fiberwise` gives equal Euler classes.
* `TauCeti.SmoothEmbedding.selfIntersectionNumber_compDiffeomorphOfBoundaryless_symm`: for a
  surface `C` charted on another two-dimensional space and a diffeomorphism `e` from `C` to a
  surface `M` charted on `𝓡 2`, the number of the embedding of `M` with the same image is the
  Euler class of the complex normal bundle of the original embedding, evaluated on the
  fundamental class of `C`. It combines Tau Ceti's naturality of the Euler class, through
  `TauCeti.SmoothEmbedding.complexEulerClass_normalComplexStructure_compDiffeomorphOfBoundaryless`,
  with the invariance of fundamental classes under diffeomorphisms
  (`TauCeti.Manifold.Orientation.evalFundamentalClass_toHomologicalOrientation_map`).
* `TauCeti.SmoothEmbedding.selfIntersectionNumber_remodel`: its case `e = remodelDiffeomorph Φ C`,
  for `C` re-modelled on `𝓡 2` along a diffeomorphism `Φ` of models
  (`SymplecticGeometry.Remodel`).
* `TauCeti.SmoothEmbedding.selfIntersectionNumber_remodel_complexCurveOrientation`: for a complex
  curve with its complex orientation, this is
  `SymplecticGeometry.complexManifoldEvalFundamentalClass` of that Euler class.
* `TauCeti.SmoothEmbedding.shortExact_orientationAt_normalSpace`: for an embedding of any
  dimension whose tangent spaces `J` preserves, oriented by the structure that `J` induces on it,
  the orientations of the source and of the normal spaces induce that of `J`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Example 4.4.5 and §7.1.
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §9 (naturality of the Euler class) and §14.
-/

public section

noncomputable section

open _root_.Bundle Module
open scoped Manifold ContDiff

/-- The real dimension of the normal spaces of a surface charted on a two-dimensional space `F`
in a manifold of real dimension four is that of `ℂ`. -/
theorem SymplecticGeometry.finrank_real_complex_eq_sub_of_finrank_eq_four_of_finrank_eq_two
    {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (hE : finrank ℝ E = 4) (hF : finrank ℝ F = 2) :
    finrank ℝ ℂ = finrank ℝ E - finrank ℝ F := by
  rw [Complex.finrank_real_complex, hE, hF]

/-- The real dimension of the normal spaces of a surface in a manifold of real dimension four is
that of `ℂ`: this is the dimension hypothesis of Tau Ceti's normal bundle with model fibre `ℂ`. -/
theorem SymplecticGeometry.finrank_real_complex_eq_sub_of_finrank_eq_four {E : Type*}
    [AddCommGroup E] [Module ℝ E] (hE : finrank ℝ E = 4) :
    finrank ℝ ℂ = finrank ℝ E - finrank ℝ (EuclideanSpace ℝ (Fin 2)) :=
  finrank_real_complex_eq_sub_of_finrank_eq_four_of_finrank_eq_two hE finrank_euclideanSpace_fin

/-- The real dimension of `ℂ` is twice its complex dimension: the dimension convention of
complex structures on vector bundles with model fibre `ℂ`, as a `Fact` to enable locally as an
instance. -/
theorem Complex.finrank_real_complex_eq_two_mul_finrank_fact :
    Fact (finrank ℝ ℂ = 2 * finrank ℂ ℂ) :=
  ⟨by simp⟩

namespace TauCeti.SmoothEmbedding

open SymplecticGeometry SymplecticGeometry.Bundle

variable {E : Type} {H X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace X] [ChartedSpace H X]
  [IsManifold I ∞ X]
  {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
  [IsManifold (𝓡 2) ∞ M] {hn : (∞ : ℕ∞ω) ≠ 0}

section Number

attribute [local instance] Complex.finrank_real_complex_eq_two_mul_finrank_fact

variable [T2Space M] [CompactSpace M]

/-- The **self-intersection number** of a compact surface `M` embedded by `f` in a four-dimensional
manifold `X` with an almost complex structure `J` that preserves its tangent planes. It is the
evaluation `⟨e(ν_J), [M, o]⟩` of the Euler class of the complex line bundle
`ν_J = (f.normalComplexStructure hn J _ hJ).Fiber`, the normal bundle with the complex structure
induced by `J` and oriented by it, on the fundamental class of `M` for the
orientation `o`.

This is the self-intersection number `M · M` when `o` is the orientation of `M` given by `J`,
for which the frames `(u, J u)` are positive. For the opposite orientation it is `-(M · M)`
(`selfIntersectionNumber_neg_orientation`), whereas `M · M` does not depend on how `M` is
oriented. -/
def selfIntersectionNumber (f : SmoothEmbedding (𝓡 2) I ∞ M X) (hE : finrank ℝ E = 4)
    (J : SmoothAlmostComplexStructure I X)
    (hJ : ∀ x, Set.MapsTo (J (f x)) (f.isImmersion.tangentRange x hn)
        (f.isImmersion.tangentRange x hn))
    (o : Manifold.Orientation (𝓡 2) M (Fin 2)) : ℤ :=
  letI := f.normalSpaceFiberBundle hn (finrank_real_complex_eq_sub_of_finrank_eq_four hE)
  letI := f.normalSpaceVectorBundle hn (finrank_real_complex_eq_sub_of_finrank_eq_four hE)
  ((o.toHomologicalOrientation (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 2)) :
      HomologicalOrientation M (EuclideanSpace ℝ (Fin 2)) 2).evalFundamentalClass
    finrank_euclideanSpace_fin (ModuleCat.of ℤ (ULift ℤ)) (ContinuousMap.id M)
    (complexEulerClass (r := 0) ℂ (f.normalComplexStructure hn J
      (finrank_real_complex_eq_sub_of_finrank_eq_four hE) hJ).Fiber
      (finrank_self ℂ))).down

theorem selfIntersectionNumber_def (f : SmoothEmbedding (𝓡 2) I ∞ M X) (hE : finrank ℝ E = 4)
    (J : SmoothAlmostComplexStructure I X)
    (hJ : ∀ x, Set.MapsTo (J (f x)) (f.isImmersion.tangentRange x hn)
        (f.isImmersion.tangentRange x hn))
    (o : Manifold.Orientation (𝓡 2) M (Fin 2)) :
    letI := f.normalSpaceFiberBundle hn (finrank_real_complex_eq_sub_of_finrank_eq_four hE)
    letI := f.normalSpaceVectorBundle hn (finrank_real_complex_eq_sub_of_finrank_eq_four hE)
    f.selfIntersectionNumber hE J hJ o =
      ((o.toHomologicalOrientation (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 2)) :
          HomologicalOrientation M (EuclideanSpace ℝ (Fin 2)) 2).evalFundamentalClass
        finrank_euclideanSpace_fin (ModuleCat.of ℤ (ULift ℤ)) (ContinuousMap.id M)
        (complexEulerClass (r := 0) ℂ (f.normalComplexStructure hn J
          (finrank_real_complex_eq_sub_of_finrank_eq_four hE) hJ).Fiber
          (finrank_self ℂ))).down :=
  (rfl)

/-- The self-intersection number is the first Chern number of the complex line bundle of the
complex structure that `J` induces on the normal bundle. -/
theorem selfIntersectionNumber_eq_chernNumber (f : SmoothEmbedding (𝓡 2) I ∞ M X)
    (hE : finrank ℝ E = 4) (J : SmoothAlmostComplexStructure I X)
    (hJ : ∀ x, Set.MapsTo (J (f x)) (f.isImmersion.tangentRange x hn)
        (f.isImmersion.tangentRange x hn))
    (o : Manifold.Orientation (𝓡 2) M (Fin 2)) :
    letI := f.normalSpaceFiberBundle hn (finrank_real_complex_eq_sub_of_finrank_eq_four hE)
    letI := f.normalSpaceVectorBundle hn (finrank_real_complex_eq_sub_of_finrank_eq_four hE)
    f.selfIntersectionNumber hE J hJ o =
      chernNumber (o.toHomologicalOrientation finrank_euclideanSpace_fin)
        finrank_euclideanSpace_fin ℂ
        (f.normalComplexStructure hn J (finrank_real_complex_eq_sub_of_finrank_eq_four hE)
          hJ).Fiber := by
  rw [selfIntersectionNumber_def, chernNumber_def, firstChernClass_eq_complexEulerClass]

/-- Reversing the orientation `o` of the surface negates the number. -/
@[simp]
theorem selfIntersectionNumber_neg_orientation (f : SmoothEmbedding (𝓡 2) I ∞ M X)
    (hE : finrank ℝ E = 4) (J : SmoothAlmostComplexStructure I X)
    (hJ : ∀ x, Set.MapsTo (J (f x)) (f.isImmersion.tangentRange x hn)
        (f.isImmersion.tangentRange x hn))
    (o : Manifold.Orientation (𝓡 2) M (Fin 2)) :
    f.selfIntersectionNumber hE J hJ (-o) = -f.selfIntersectionNumber hE J hJ o := by
  rw [selfIntersectionNumber_eq_chernNumber, selfIntersectionNumber_eq_chernNumber,
    Manifold.Orientation.toHomologicalOrientation_neg, chernNumber_neg_orientation]

variable {E' : Type} {H' X' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [FiniteDimensional ℝ E'] [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  [TopologicalSpace X'] [ChartedSpace H' X'] [IsManifold I' ∞ X']

/-- **Locality of the self-intersection number.** Let
`f : M → X` and `f' : M → X'` embed the same compact surface in two four-manifolds with almost
complex structures `J` and `J'` that preserve its tangent planes, and let `φ : X → X'` be a map
with `φ ∘ f = f'` that, at each point `f x`, is `C¹` and `(J, J')`-holomorphic with invertible
derivative. Then the two self-intersection numbers agree, for every orientation `o` of `M`.

Only the first-order behaviour of `φ` along the surface enters: for instance `φ` may be a
biholomorphism from a neighbourhood of `f(M)` onto an open set of `X'`, extended arbitrarily.
The derivative of `φ` induces an isomorphism of the normal bundles that carries the complex
structure induced by `J` to that induced by `J'`, and isomorphic complex line bundles have the same
Euler class. -/
theorem selfIntersectionNumber_eq_of_comp (f : SmoothEmbedding (𝓡 2) I ∞ M X)
    (f' : SmoothEmbedding (𝓡 2) I' ∞ M X') (hE : finrank ℝ E = 4) (hE' : finrank ℝ E' = 4)
    (J : SmoothAlmostComplexStructure I X) (J' : SmoothAlmostComplexStructure I' X')
    (hJ : ∀ x, Set.MapsTo (J (f x)) (f.isImmersion.tangentRange x hn)
        (f.isImmersion.tangentRange x hn))
    (hJ' : ∀ x, Set.MapsTo (J' (f' x)) (f'.isImmersion.tangentRange x hn)
        (f'.isImmersion.tangentRange x hn))
    {φ : X → X'} (hφ : φ ∘ f = f') (hφ₁ : ∀ x, ContMDiffAt I I' 1 φ (f x))
    (hφJ : ∀ x, IsPseudoholomorphicAt J J' φ (f x))
    (hφd : ∀ x, (mfderiv I I' φ (f x)).IsInvertible)
    (o : Manifold.Orientation (𝓡 2) M (Fin 2)) :
    f.selfIntersectionNumber hE J hJ o = f'.selfIntersectionNumber hE' J' hJ' o := by
  have hdim := finrank_real_complex_eq_sub_of_finrank_eq_four hE
  have hdim' := finrank_real_complex_eq_sub_of_finrank_eq_four hE'
  let := f.normalSpaceFiberBundle hn hdim
  let := f.normalSpaceVectorBundle hn hdim
  let := f'.normalSpaceFiberBundle hn hdim'
  let := f'.normalSpaceVectorBundle hn hdim'
  -- The derivative of `φ` on normal spaces.
  let Φ := f.normalSpaceEquivOfComp f' hn hn hφd hφ
  have hc : ∀ x v, Φ x (f.normalComplexStructure hn J hdim hJ x v) =
      f'.normalComplexStructure hn J' hdim' hJ' x (Φ x v) := fun x v ↦ by
    rw [normalComplexStructure_apply, normalComplexStructure_apply]
    exact normalSpaceEquivOfComp_normalComplexStructureAt f f' hn hn hφd hφ x (hJ x) (hJ' x)
      (hφJ x) v
  rw [selfIntersectionNumber_def, selfIntersectionNumber_def,
    complexEulerClass_eq_of_fiberwise (finrank_self ℂ) (finrank_self ℂ)
      ((f.normalComplexStructure hn J hdim hJ).continuous_fiberEquivOfCommute
        (G₁ := ℂ) (G₂ := ℂ) (f'.normalComplexStructure hn J' hdim' hJ') Φ hc
        (f.continuous_normalSpaceEquivOfComp_of_contMDiffAt f' hn hn hφ₁ hφd hφ))]

end Number

section Remodel

open CategoryTheory

attribute [local instance] Complex.finrank_real_complex_eq_two_mul_finrank_fact

variable [I.Boundaryless]

section Real

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {C : Type} [TopologicalSpace C] [T2Space C] [CompactSpace C]
  [ChartedSpace F C] [IsManifold 𝓘(ℝ, F) ∞ C]

/-- **The self-intersection number after a change of parametrisation.** Let `C` be a compact
surface charted on a real space `F` of dimension two, `f` an embedding of `C` in a four-manifold
`X` whose tangent planes the almost complex structure `J` preserves, and `e` a diffeomorphism from
`C` to a surface `M` charted on `𝓡 2`. For an orientation `o` of `C`, carried to `M` by `e`, the
self-intersection number of the embedding `f ∘ e⁻¹` of `M` is the evaluation of the Euler class
of the normal bundle of `f`, with the complex structure induced by `J`, on the fundamental class
of `(C, o)`. -/
theorem selfIntersectionNumber_compDiffeomorphOfBoundaryless_symm [T2Space M] [CompactSpace M]
    (e : C ≃ₘ^∞⟮𝓘(ℝ, F), 𝓡 2⟯ M) (f : SmoothEmbedding 𝓘(ℝ, F) I ∞ C X)
    (hE : finrank ℝ E = 4) (hF : finrank ℝ F = 2) (J : SmoothAlmostComplexStructure I X)
    (hJ : ∀ x, Set.MapsTo (J (f x)) (f.isImmersion.tangentRange x hn)
        (f.isImmersion.tangentRange x hn))
    (o : Manifold.Orientation 𝓘(ℝ, F) C (Fin 2)) :
    letI := f.normalSpaceFiberBundle hn
      (finrank_real_complex_eq_sub_of_finrank_eq_four_of_finrank_eq_two hE hF)
    letI := f.normalSpaceVectorBundle hn
      (finrank_real_complex_eq_sub_of_finrank_eq_four_of_finrank_eq_two hE hF)
    (f.compDiffeomorphOfBoundaryless e.symm (by simp)).selfIntersectionNumber
        hE J (f.mapsTo_tangentRange_compDiffeomorphOfBoundaryless _ (by simp) hn (A := (J ·)) hJ)
        (o.map e hn (by rw [Fintype.card_fin, finrank_euclideanSpace_fin])) =
      ((o.toHomologicalOrientation hF).evalFundamentalClass hF (ModuleCat.of ℤ (ULift ℤ))
        (ContinuousMap.id C)
        (complexEulerClass (r := 0) ℂ (f.normalComplexStructure hn J
          (finrank_real_complex_eq_sub_of_finrank_eq_four_of_finrank_eq_two hE hF) hJ).Fiber
          (finrank_self ℂ))).down := by
  have hν := finrank_real_complex_eq_sub_of_finrank_eq_four_of_finrank_eq_two hE hF
  let := f.normalSpaceFiberBundle hn hν
  let := f.normalSpaceVectorBundle hn hν
  rw [selfIntersectionNumber_def,
    complexEulerClass_normalComplexStructure_compDiffeomorphOfBoundaryless f _ (by simp) J hJ hν
      (finrank_real_complex_eq_sub_of_finrank_eq_four hE) (finrank_self ℂ),
    Manifold.Orientation.evalFundamentalClass_toHomologicalOrientation_map hF
      finrank_euclideanSpace_fin o e hn,
    ← ModuleCat.comp_apply, ← TopCat.singularCohomologyMap_comp]
  -- The pull-back along `e` and then along its inverse is the identity.
  have hid : TopCat.ofHom (e.toHomeomorph : C(C, M)) ≫
      TopCat.ofHom (e.symm.toHomeomorph : C(M, C)) = 𝟙 (TopCat.of C) := by
    ext x
    simp
  rw [hid, TopCat.singularCohomologyMap_id, ModuleCat.id_apply]

/-- **The self-intersection number of a re-modelled surface.** Let `C` be a compact surface
charted on a real space `F` of dimension two, `Φ` a diffeomorphism from the model `𝓘(ℝ, F)` to
`𝓡 2`, and `f` an embedding of `C` in a four-manifold `X` whose tangent planes the almost
complex structure `J` preserves. Re-model `C` on `𝓡 2` along `Φ` (`Remodel Φ C`), and let
`g = f ∘ (remodelDiffeomorph Φ C)⁻¹` be the embedding of `Remodel Φ C` with the image of `f`.
For an orientation `o` of `C`, carried to `Remodel Φ C` by `remodelDiffeomorph Φ C`, the
self-intersection number of `g` is the evaluation of the Euler class of the normal bundle of `f`,
with the complex structure induced by `J`, on the fundamental class of `(C, o)`. -/
theorem selfIntersectionNumber_remodel
    (Φ : F ≃ₘ^∞⟮𝓘(ℝ, F), 𝓡 2⟯ EuclideanSpace ℝ (Fin 2)) (f : SmoothEmbedding 𝓘(ℝ, F) I ∞ C X)
    (hE : finrank ℝ E = 4) (hF : finrank ℝ F = 2) (J : SmoothAlmostComplexStructure I X)
    (hJ : ∀ x, Set.MapsTo (J (f x)) (f.isImmersion.tangentRange x hn)
        (f.isImmersion.tangentRange x hn))
    (o : Manifold.Orientation 𝓘(ℝ, F) C (Fin 2)) :
    letI := f.normalSpaceFiberBundle hn
      (finrank_real_complex_eq_sub_of_finrank_eq_four_of_finrank_eq_two hE hF)
    letI := f.normalSpaceVectorBundle hn
      (finrank_real_complex_eq_sub_of_finrank_eq_four_of_finrank_eq_two hE hF)
    (f.compDiffeomorphOfBoundaryless (remodelDiffeomorph Φ C).symm (by simp)).selfIntersectionNumber
        hE J (f.mapsTo_tangentRange_compDiffeomorphOfBoundaryless _ (by simp) hn (A := (J ·)) hJ)
        (o.map (remodelDiffeomorph Φ C) hn (by rw [Fintype.card_fin, finrank_euclideanSpace_fin])) =
      ((o.toHomologicalOrientation hF).evalFundamentalClass hF (ModuleCat.of ℤ (ULift ℤ))
        (ContinuousMap.id C)
        (complexEulerClass (r := 0) ℂ (f.normalComplexStructure hn J
          (finrank_real_complex_eq_sub_of_finrank_eq_four_of_finrank_eq_two hE hF) hJ).Fiber
          (finrank_self ℂ))).down :=
  selfIntersectionNumber_compDiffeomorphOfBoundaryless_symm _ f hE hF J hJ o

end Real

section Complex

open scoped TauCeti.ComplexManifold

variable {G : Type} [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G]
  {C : Type} [TopologicalSpace C] [T2Space C] [CompactSpace C] [ChartedSpace G C]
  [IsManifold 𝓘(ℂ, G) ∞ C]

/-- **The self-intersection number of a complex curve.** Let `C` be a compact complex curve,
modelled on `𝓘(ℂ, G)` with `finrank ℂ G = 1` and seen as a real surface over `𝓘(ℝ, G)`, `Φ` a
diffeomorphism from `𝓘(ℝ, G)` to `𝓡 2`, and `f` an embedding of `C` in a four-manifold `X`
whose tangent planes the almost complex structure `J` preserves. For the complex orientation of
`C` (`complexCurveOrientation`), carried to `Remodel Φ C`, the self-intersection number of
`f ∘ (remodelDiffeomorph Φ C)⁻¹` is the Euler class of the normal bundle of `f`, with the complex
structure induced by `J` and read in integral cohomology, paired with the fundamental class of `C`
for its complex orientation (`complexManifoldEvalFundamentalClass`). -/
theorem selfIntersectionNumber_remodel_complexCurveOrientation
    (hG : finrank ℂ G = 1) (Φ : G ≃ₘ^∞⟮𝓘(ℝ, G), 𝓡 2⟯ EuclideanSpace ℝ (Fin 2))
    (f : SmoothEmbedding 𝓘(ℝ, G) I ∞ C X) (hE : finrank ℝ E = 4)
    (J : SmoothAlmostComplexStructure I X)
    (hJ : ∀ x, Set.MapsTo (J (f x)) (f.isImmersion.tangentRange x hn)
        (f.isImmersion.tangentRange x hn)) :
    letI := f.normalSpaceFiberBundle hn
      (finrank_real_complex_eq_sub_of_finrank_eq_four_of_finrank_eq_two hE
        (finrank_real_of_finrank_complex_eq_add_one hG))
    letI := f.normalSpaceVectorBundle hn
      (finrank_real_complex_eq_sub_of_finrank_eq_four_of_finrank_eq_two hE
        (finrank_real_of_finrank_complex_eq_add_one hG))
    (f.compDiffeomorphOfBoundaryless (remodelDiffeomorph Φ C).symm (by simp)).selfIntersectionNumber
        hE J (f.mapsTo_tangentRange_compDiffeomorphOfBoundaryless _ (by simp) hn (A := (J ·)) hJ)
        ((complexCurveOrientation G C hG).map (remodelDiffeomorph Φ C) hn
          (by rw [Fintype.card_fin, finrank_euclideanSpace_fin])) =
      complexManifoldEvalFundamentalClass G C (r := 0) hG
        (((TopCat.of C).uliftIntegralCohomologyIso _).hom
          (complexEulerClass (r := 0) ℂ (f.normalComplexStructure hn J
            (finrank_real_complex_eq_sub_of_finrank_eq_four_of_finrank_eq_two hE
              (finrank_real_of_finrank_complex_eq_add_one hG)) hJ).Fiber (finrank_self ℂ))) := by
  rw [selfIntersectionNumber_compDiffeomorphOfBoundaryless_symm _ f hE
      (finrank_real_of_finrank_complex_eq_add_one hG) J hJ,
    complexManifoldEvalFundamentalClass_def,
    HomologicalOrientation.evalFundamentalClass_uliftIntegralCohomologyIso_hom,
    complexManifoldHomologicalOrientation_def,
    complexCurveOrientation_eq_complexManifoldOrientationOfFinrank]

end Complex

end Remodel

section Orientation

variable {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold I' ∞ N]

/-- **The orientations of `N` and of the normal spaces induce that of `J`.**
Let `f` embed a manifold `N` of real dimension `k` so that `J` preserves its tangent spaces, and
let `o` orient `N` at `c` by the almost complex structure `J.restrict f hJ` that `J` induces on
`N`. Then the orientation that the short exact sequence `0 → T_c N → T_{f c} X → ν_c → 0`, of the
differential and the normal class map, induces from `o` at `c` and the orientation of the structure
that `J` induces on `ν_c`, with `T_c N` first, is the orientation of `J` at `f c`.

For a surface, `k = 2`, a hypothesis that the frames `(u, J' u)` of `T_c N` are positive for `o`,
where `J' = J.restrict f hJ`, gives `ho` through
`TauCeti.AlmostComplexStructure.orientation_eq_of_apply_one_eq`. -/
theorem shortExact_orientationAt_normalSpace {k : ℕ} (hk : finrank ℝ E' = k)
    (f : SmoothEmbedding I' I ∞ N X) (J : SmoothAlmostComplexStructure I X)
    (hJ : ∀ x, Set.MapsTo (J (f x)) (f.isImmersion.tangentRange x hn)
        (f.isImmersion.tangentRange x hn))
    {o : Manifold.Orientation I' N (Fin k)} {c : N}
    (ho : o.orientationAt c = Orientation.reindex ℝ _
      (finCongr (n := finrank ℝ (TangentSpace I' c)) hk)
      (((J.restrict f hJ).almostComplexStructureAt c).orientation rfl)) :
    Orientation.shortExact (f.isSmoothEmbedding_toFun.isImmersion.mfderiv_injective hn c)
        (f.exact_mfderiv_normalClass c hn) (f.isImmersion.normalClass_surjective c hn)
            (o.orientationAt c)
        ((f.normalAlmostComplexStructureAt J hJ c).orientation rfl) hk rfl =
      Orientation.reindex ℝ _ (finCongr (by
        have h : finrank ℝ (TangentSpace I' c) = k := hk
        have := f.isImmersion.finrank_normalSpace_add_finrank c hn
        omega))
        ((J.almostComplexStructureAt (f c)).orientation rfl) := by
  rw [ho]
  refine (Orientation.shortExact_reindex_finCongr_left _ _ _ _ _ _ _ _).trans ?_
  rw [AlmostComplexStructure.shortExact_orientation _ _ _
      (SmoothAlmostComplexStructure.isComplexLinearMap_mfderiv hJ c)
      (f.isComplexLinearMap_normalClass J hJ c)]
  -- Both sides reindex the orientation of `J` at `f c` along casts between the same index types.
  exact (Orientation.reindex_trans _ _ _).symm.trans
    (congrArg (Orientation.reindex ℝ _ · _) (Equiv.ext fun _ ↦ rfl))

end Orientation

end TauCeti.SmoothEmbedding

end
