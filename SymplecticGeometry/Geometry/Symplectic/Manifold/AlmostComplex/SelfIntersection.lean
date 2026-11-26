/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Real
public import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.NormalSpace.ComplexStructure
public import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.NormalSpace.Exact
public import SymplecticGeometry.Geometry.Symplectic.Manifold.AlmostComplex.Submanifold
public import SymplecticGeometry.LinearAlgebra.ComplexStructure.Orientation
public import SymplecticGeometry.Topology.VectorBundle.Complex.FirstChernClass
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Smooth

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
* `TauCeti.SmoothEmbedding.shortExact_orientationAt_normalSpace`: for an embedding of any
  dimension whose tangent spaces `J` preserves, oriented by the structure that `J` induces on it,
  the orientations of the source and of the normal spaces induce that of `J`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Example 4.4.5.
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §14.
-/

public section

noncomputable section

open _root_.Bundle Module
open scoped Manifold ContDiff

/-- The real dimension of the normal spaces of a surface in a manifold of real dimension four is
that of `ℂ`: this is the dimension hypothesis of Tau Ceti's normal bundle with model fibre `ℂ`. -/
theorem SymplecticGeometry.finrank_real_complex_eq_sub_of_finrank_eq_four {E : Type*}
    [AddCommGroup E] [Module ℝ E] (hE : finrank ℝ E = 4) :
    finrank ℝ ℂ = finrank ℝ E - finrank ℝ (EuclideanSpace ℝ (Fin 2)) := by
  rw [Complex.finrank_real_complex, hE, finrank_euclideanSpace_fin]

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
    (hJ : ∀ x, Set.MapsTo (J (f x)) (f.tangentRange x hn) (f.tangentRange x hn))
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
    (hJ : ∀ x, Set.MapsTo (J (f x)) (f.tangentRange x hn) (f.tangentRange x hn))
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
    (hJ : ∀ x, Set.MapsTo (J (f x)) (f.tangentRange x hn) (f.tangentRange x hn))
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
    (hJ : ∀ x, Set.MapsTo (J (f x)) (f.tangentRange x hn) (f.tangentRange x hn))
    (o : Manifold.Orientation (𝓡 2) M (Fin 2)) :
    f.selfIntersectionNumber hE J hJ (-o) = -f.selfIntersectionNumber hE J hJ o := by
  rw [selfIntersectionNumber_eq_chernNumber, selfIntersectionNumber_eq_chernNumber,
    Manifold.Orientation.toHomologicalOrientation_neg, chernNumber_neg_orientation]

end Number

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
    (hJ : ∀ x, Set.MapsTo (J (f x)) (f.tangentRange x hn) (f.tangentRange x hn))
    {o : Manifold.Orientation I' N (Fin k)} {c : N}
    (ho : o.orientationAt c = Orientation.reindex ℝ _
      (finCongr (n := finrank ℝ (TangentSpace I' c)) hk)
      (((J.restrict f hJ).almostComplexStructureAt c).orientation rfl)) :
    Orientation.shortExact (f.isSmoothEmbedding_toFun.isImmersion.mfderiv_injective hn c)
        (f.exact_mfderiv_normalClass c hn) (f.normalClass_surjective c hn) (o.orientationAt c)
        ((f.normalAlmostComplexStructureAt J hJ c).orientation rfl) hk rfl =
      Orientation.reindex ℝ _ (finCongr (by
        have h : finrank ℝ (TangentSpace I' c) = k := hk
        have := f.finrank_normalSpace_add_finrank c hn
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
