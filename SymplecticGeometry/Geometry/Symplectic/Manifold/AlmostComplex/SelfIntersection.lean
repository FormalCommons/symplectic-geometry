/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Real
public import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.NormalSpace.ComplexStructure
public import SymplecticGeometry.LinearAlgebra.ComplexStructure.Orientation
public import SymplecticGeometry.Topology.VectorBundle.Complex.FirstChernClass
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Smooth
public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.Representative

/-!
# The self-intersection number of a `J`-invariant surface

Let `X` be a manifold of real dimension four with an almost complex structure `J`, and let
`f : M → X` embed a compact oriented surface `M` so that its tangent planes are `J`-invariant.
Then `J` descends to a complex structure on the normal bundle `ν` of `f`
(`TauCeti.SmoothEmbedding.normalComplexStructure`), which makes `ν` a complex line bundle `ν_J`
with model fibre `ℂ`. Its **self-intersection number** `M · M` is the Euler number of `ν`, oriented
by its complex structure: the evaluation on the fundamental class of `M` of Tau Ceti's Euler class
`TauCeti.complexEulerClass ℂ ν_J`.

The orientation of `ν` is the one the splitting `T_{f c} X = df (T_c M) ⊕ W` along a `J`-invariant
complement `W` asks for: the isomorphism `T_c M × ν_c ≃ T_{f c} X`, `(u, a) ↦ df u + r a` with
`r a` the representative of `a` in `W`, carries the product of the orientation of `M` and the
complex orientation of `ν_c` to the complex orientation of `T_{f c} X`, when `M` is oriented by `J`
(`TauCeti.SmoothEmbedding.orientation_prod_normalSpace`). Its linear algebra is
`TauCeti.AlmostComplexStructure.map_prodEquivOfIsCompl_orientation`.

## Main definitions

* `TauCeti.SmoothEmbedding.selfIntersectionNumber`: the Euler number of the normal bundle with its
  complex orientation.

## Main results

* `TauCeti.SmoothEmbedding.selfIntersectionNumber_eq_chernNumber`: it is the first Chern number of
  the complex line bundle `ν_J`.
* `TauCeti.SmoothEmbedding.selfIntersectionNumber_neg_orientation`: reversing the orientation of
  `M` negates it.
* `TauCeti.SmoothEmbedding.orientation_prod_normalSpace`: the complex orientation of the normal
  spaces is the one induced by the orientations of `X` and `M`.

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
    [NormedAddCommGroup E] [NormedSpace ℝ E] (hE : finrank ℝ E = 4) :
    finrank ℝ ℂ = finrank ℝ E - finrank ℝ (EuclideanSpace ℝ (Fin 2)) := by
  rw [Complex.finrank_real_complex, hE, finrank_euclideanSpace_fin]

namespace TauCeti.SmoothEmbedding

open SymplecticGeometry SymplecticGeometry.Bundle

variable {E : Type} {H X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace X] [ChartedSpace H X]
  [IsManifold I ∞ X]
  {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
  [IsManifold (𝓡 2) ∞ M] {hn : (∞ : ℕ∞ω) ≠ 0}

section Number

-- The complex line bundle of the normal complex structure has model fibre `ℂ`.
local instance : Fact (finrank ℝ ℂ = 2 * finrank ℂ ℂ) := ⟨by simp⟩

variable [T2Space M] [CompactSpace M]

/-- The **self-intersection number** of a compact surface `M`, oriented by `o`, embedded by `f` in
a four-dimensional manifold `X` with an almost complex structure `J` that preserves its tangent
planes: the Euler number of the normal bundle oriented by its complex structure, that is, the
evaluation on the fundamental class of `M` of the Euler class of the complex line bundle
`(f.normalComplexStructure _ J hJ).toContinuousComplexStructure.Fiber`. -/
def selfIntersectionNumber (f : SmoothEmbedding (𝓡 2) I ∞ M X) (hE : finrank ℝ E = 4)
    (J : SmoothAlmostComplexStructure I X)
    (hJ : ∀ x, ∀ v ∈ f.tangentRange x hn, J (f x) v ∈ f.tangentRange x hn)
    (o : Manifold.Orientation (𝓡 2) M (Fin 2)) : ℤ :=
  letI := f.normalSpaceFiberBundle hn (finrank_real_complex_eq_sub_of_finrank_eq_four hE)
  letI := f.normalSpaceVectorBundle hn (finrank_real_complex_eq_sub_of_finrank_eq_four hE)
  ((o.toHomologicalOrientation (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 2)) :
      HomologicalOrientation M (EuclideanSpace ℝ (Fin 2)) 2).evalFundamentalClass
    finrank_euclideanSpace_fin (ModuleCat.of ℤ (ULift ℤ)) (ContinuousMap.id M)
    (complexEulerClass (r := 0) ℂ (f.normalComplexStructure
      (finrank_real_complex_eq_sub_of_finrank_eq_four hE) J hJ).toContinuousComplexStructure.Fiber
      (finrank_self ℂ))).down

theorem selfIntersectionNumber_def (f : SmoothEmbedding (𝓡 2) I ∞ M X) (hE : finrank ℝ E = 4)
    (J : SmoothAlmostComplexStructure I X)
    (hJ : ∀ x, ∀ v ∈ f.tangentRange x hn, J (f x) v ∈ f.tangentRange x hn)
    (o : Manifold.Orientation (𝓡 2) M (Fin 2)) :
    letI := f.normalSpaceFiberBundle hn (finrank_real_complex_eq_sub_of_finrank_eq_four hE)
    letI := f.normalSpaceVectorBundle hn (finrank_real_complex_eq_sub_of_finrank_eq_four hE)
    f.selfIntersectionNumber hE J hJ o =
      ((o.toHomologicalOrientation (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 2)) :
          HomologicalOrientation M (EuclideanSpace ℝ (Fin 2)) 2).evalFundamentalClass
        finrank_euclideanSpace_fin (ModuleCat.of ℤ (ULift ℤ)) (ContinuousMap.id M)
        (complexEulerClass (r := 0) ℂ (f.normalComplexStructure
          (finrank_real_complex_eq_sub_of_finrank_eq_four hE) J
            hJ).toContinuousComplexStructure.Fiber (finrank_self ℂ))).down :=
  (rfl)

/-- The self-intersection number is the first Chern number of the complex line bundle of the
complex structure that `J` induces on the normal bundle. -/
theorem selfIntersectionNumber_eq_chernNumber (f : SmoothEmbedding (𝓡 2) I ∞ M X)
    (hE : finrank ℝ E = 4) (J : SmoothAlmostComplexStructure I X)
    (hJ : ∀ x, ∀ v ∈ f.tangentRange x hn, J (f x) v ∈ f.tangentRange x hn)
    (o : Manifold.Orientation (𝓡 2) M (Fin 2)) :
    letI := f.normalSpaceFiberBundle hn (finrank_real_complex_eq_sub_of_finrank_eq_four hE)
    letI := f.normalSpaceVectorBundle hn (finrank_real_complex_eq_sub_of_finrank_eq_four hE)
    f.selfIntersectionNumber hE J hJ o =
      chernNumber (o.toHomologicalOrientation finrank_euclideanSpace_fin)
        finrank_euclideanSpace_fin ℂ
        (f.normalComplexStructure (finrank_real_complex_eq_sub_of_finrank_eq_four hE)
          J hJ).toContinuousComplexStructure.Fiber := by
  rw [selfIntersectionNumber_def, chernNumber_def, firstChernClass_eq_complexEulerClass]

/-- Reversing the orientation of the surface negates its self-intersection number. -/
@[simp]
theorem selfIntersectionNumber_neg_orientation (f : SmoothEmbedding (𝓡 2) I ∞ M X)
    (hE : finrank ℝ E = 4) (J : SmoothAlmostComplexStructure I X)
    (hJ : ∀ x, ∀ v ∈ f.tangentRange x hn, J (f x) v ∈ f.tangentRange x hn)
    (o : Manifold.Orientation (𝓡 2) M (Fin 2)) :
    f.selfIntersectionNumber hE J hJ (-o) = -f.selfIntersectionNumber hE J hJ o := by
  rw [selfIntersectionNumber_eq_chernNumber, selfIntersectionNumber_eq_chernNumber,
    Manifold.Orientation.toHomologicalOrientation_neg, chernNumber_neg_orientation]

end Number

/-- **The complex orientation of the normal spaces is induced by the orientations of `X` and `M`.**
Let `M` be oriented by `o` so that the frames `(u, j u)` of `T_c M`, with `j` the restriction of `J`
read through `df`, are positive. For a `J`-invariant complement `W` of the tangent image at `c`, the
isomorphism `e : T_c M × ν_c ≃ T_{f c} X`, `(u, a) ↦ df u + r a` with `r a` the representative of
`a` in `W`, carries the ordered product of `o` at `c` and the orientation of the structure that `J`
induces on `ν_c` to the orientation of `J` at `f c`. -/
theorem orientation_prod_normalSpace (f : SmoothEmbedding (𝓡 2) I ∞ M X)
    (J : SmoothAlmostComplexStructure I X)
    (hJ : ∀ x, ∀ v ∈ f.tangentRange x hn, J (f x) v ∈ f.tangentRange x hn)
    {o : Manifold.Orientation (𝓡 2) M (Fin 2)} {c : M}
    (ho : ∀ b : Basis (Fin 2) ℝ (TangentSpace (𝓡 2) c),
      mfderiv (𝓡 2) I f c (b 1) = J (f c) (mfderiv (𝓡 2) I f c (b 0)) →
        b.orientation = o.orientationAt c)
    {W : Submodule ℝ (TangentSpace I (f c))} (hW : ∀ v ∈ W, J (f c) v ∈ W)
    (hc : (f.tangentRange c hn).IsTopCompl W)
    (e : (TangentSpace (𝓡 2) c × f.NormalSpace c hn) ≃ₗ[ℝ] TangentSpace I (f c))
    (he : ∀ u a, e (u, a) = mfderiv (𝓡 2) I f c u + f.complementRepresentative c hn hc a) :
    Orientation.map _ e ((o.orientationAt c).prod
        (f.normalAlmostComplexStructureAt J hJ c).orientation finrank_euclideanSpace_fin rfl) =
      Orientation.reindex ℝ _ (finCongr (by
        rw [← e.finrank_eq, finrank_prod]; exact congrArg (· + _) finrank_euclideanSpace_fin))
        (J.almostComplexStructureAt (f c)).orientation := by
  set K := J.almostComplexStructureAt (f c)
  set T := f.tangentRange c hn
  have hT : ∀ v ∈ T, K v ∈ T := fun v hv ↦ by
    rw [SmoothAlmostComplexStructure.almostComplexStructureAt_apply]
    exact hJ c v hv
  have hW' : ∀ v ∈ W, K v ∈ W := fun v hv ↦ by
    rw [SmoothAlmostComplexStructure.almostComplexStructureAt_apply]
    exact hW v hv
  have h := hc.isCompl
  -- The differential, as an isomorphism onto the tangent image.
  let d : TangentSpace (𝓡 2) c ≃ₗ[ℝ] T := LinearEquiv.ofInjective
    (mfderiv (𝓡 2) I f c).toLinearMap (f.isSmoothEmbedding_toFun.isImmersion.mfderiv_injective hn c)
  have hd (u : TangentSpace (𝓡 2) c) : (d u : TangentSpace I (f c)) = mfderiv (𝓡 2) I f c u :=
    LinearEquiv.ofInjective_apply _ _
  have he' : e = (d.prodCongr (LinearEquiv.refl ℝ (f.NormalSpace c hn))).trans
      (((LinearEquiv.refl ℝ T).prodCongr (T.quotientEquivOfIsCompl W h)).trans
        (T.prodEquivOfIsCompl W h)) := by
    refine LinearEquiv.ext fun ⟨u, a⟩ ↦ ?_
    rw [he, (f.complementRepresentative_eq_iff c hn hc a _).2
      ⟨(T.quotientEquivOfIsCompl W h a).property, ?_⟩]
    · -- `f.NormalSpace c hn` is by definition the quotient by the tangent image, and both sides
      -- are `df u` plus the representative of `a` in `W`.
      rfl
    · rw [normalClass_def]
      exact T.mk_quotientEquivOfIsCompl_apply h a
  have hT2 : finrank ℝ T = 2 := d.finrank_eq.symm.trans finrank_euclideanSpace_fin
  -- The differential carries `o` to the orientation of the restriction of `J`, by `ho` applied to
  -- the pull-back of a frame `(w, J w)` of the tangent image.
  have hdo : Orientation.map _ d (o.orientationAt c) =
      Orientation.reindex ℝ T (finCongr hT2) (K.restrict T hT).orientation := by
    have : Nontrivial T := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
    obtain ⟨w, hw⟩ := exists_ne (0 : T)
    let b : Basis (Fin 2) ℝ T := basisOfLinearIndependentOfCardEqFinrank
      ((K.restrict T hT).linearIndependent_pair hw) (by simp [hT2])
    have hb : ⇑b = ![w, K.restrict T hT w] := coe_basisOfLinearIndependentOfCardEqFinrank _ _
    have hbo := ho (b.map d.symm) (by
      simp only [Basis.map_apply, ← hd, LinearEquiv.apply_symm_apply, hb]
      simp [K])
    rw [← hbo, ← Basis.orientation_map,
      show (b.map d.symm).map d = b from Basis.eq_of_apply_eq fun i ↦ by simp]
    exact (K.restrict T hT).orientation_eq_of_apply_one_eq hT2 b (by simp [hb])
  rw [he']
  refine (Orientation.map_trans _ _ _).trans ?_
  refine (congrArg _ (Orientation.map_prod _ _ _ _ _ _)).trans ?_
  rw [Orientation.map_refl, Equiv.refl_apply, hdo,
    Orientation.prod_reindex_finCongr_left]
  refine (Orientation.map_reindex _ _ _).trans ?_
  rw [normalAlmostComplexStructureAt_def]
  refine (congrArg _ (K.map_prodEquivOfIsCompl_orientation hT hW' h)).trans ?_
  exact (Orientation.reindex_trans _ _ _).symm

end TauCeti.SmoothEmbedding

end
