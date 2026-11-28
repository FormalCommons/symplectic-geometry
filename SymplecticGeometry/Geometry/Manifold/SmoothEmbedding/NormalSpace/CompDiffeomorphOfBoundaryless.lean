/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.Diffeomorph
public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.Map
public import TauCeti.Geometry.Symplectic.Lagrangian.Embedding.Symplectic.Normal
public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.VectorBundle.Basic
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.NormalBundle
public import TauCeti.Topology.VectorBundle.Orientation.Complex.FiberwiseEquiv
import SymplecticGeometry.Topology.VectorBundle.Complex.Structure
import TauCeti.Geometry.Manifold.IsManifold.Basic
import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.Topology
import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.VectorBundle.Map
import TauCeti.Geometry.Symplectic.Lagrangian.Embedding.Symplectic.Normal.Bundle

/-!
# The normal bundle of an embedding reparametrised by a diffeomorphism

Let `f : M → X` be a smooth embedding and `e : M' ≃ M` a diffeomorphism from a manifold `M'` that
may be modelled on another space, and let `g = f ∘ e` be the reparametrised embedding
`TauCeti.SmoothEmbedding.compDiffeomorphOfBoundaryless`. Then `g` and `f` have the same tangent
planes: the tangent range of `g` at `x` is that of `f` at `e x`. Their normal spaces at `x` and at
`e x` are therefore the quotients of the same tangent space of `X` by the same subspace, and these
identifications form a continuous isomorphism of normal bundles over `e`. When an almost complex
structure `J` on `X` preserves the tangent planes of `f`, it preserves those of `g`, the
identifications are complex linear for the complex structures that `J` induces on the normal
bundles, and naturality of the Euler class gives that the Euler class of the complex normal bundle
of `g` is the pull-back along `e` of that of `f`. For a nondegenerate two-form on `X` for which
`f` and `g` have symplectic tangent images, the identifications carry the normal symplectic form
of `g` to that of `f`.

The fibrewise identification is Tau Ceti's `TauCeti.SmoothEmbedding.normalSpaceEquiv` for the
square `id ∘ g = f ∘ e`; its continuity and smoothness on total spaces are Tau Ceti's
`TauCeti.SmoothEmbedding.continuous_normalBundleMap` and
`TauCeti.SmoothEmbedding.contMDiff_normalBundleMap`, and its inverse is smooth since it is the
normal map of the square `id ∘ f = g ∘ e⁻¹`. The comparison of normal symplectic forms is Tau
Ceti's naturality `TauCeti.SmoothEmbedding.symplecticNormalForm_normalMap`, and the comparison of
Euler classes is Tau Ceti's `TauCeti.complexEulerClass_eq_singularCohomologyMap_of_fiberwise`.

## Main definitions

* `TauCeti.SmoothEmbedding.normalSpaceEquivCompDiffeomorphOfBoundaryless`: the identification of
  the normal space of `g` at `x` with that of `f` at `e x`.

## Main results

* `TauCeti.SmoothEmbedding.tangentRange_compDiffeomorphOfBoundaryless`: `g` and `f` have the same
  tangent planes.
* `TauCeti.SmoothEmbedding.mapsTo_tangentRange_compDiffeomorphOfBoundaryless`: an endomorphism
  field that preserves the tangent planes of `f` preserves those of `g`.
* `TauCeti.SmoothEmbedding.continuous_normalSpaceEquivCompDiffeomorphOfBoundaryless`: the
  identifications are continuous on total spaces.
* `TauCeti.SmoothEmbedding.contMDiff_normalSpaceEquivCompDiffeomorphOfBoundaryless` and
  `TauCeti.SmoothEmbedding.contMDiff_normalSpaceEquivCompDiffeomorphOfBoundaryless_symm_iff`: the
  identifications and their inverses are `C^r` on total spaces, when `f` and `e` are `C^n` with
  `r + 1 ≤ n`.
* `TauCeti.SmoothEmbedding.hasSymplecticTangentImages_compDiffeomorphOfBoundaryless_iff`: `g` has
  symplectic tangent images for a nondegenerate two-form exactly when `f` has.
* `TauCeti.SmoothEmbedding.symplecticNormalForm_normalSpaceEquivCompDiffeomorphOfBoundaryless`:
  the identifications preserve the normal symplectic forms.
* `TauCeti.SmoothEmbedding.complexEulerClass_normalComplexStructure_compDiffeomorphOfBoundaryless`:
  the Euler class of the complex normal bundle of `g` is the pull-back along `e` of that of `f`.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §§3, 9 and 14 (bundle maps, naturality of the Euler class).
* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §7.1.
-/

public section

noncomputable section

open _root_.Bundle Module Set Filter
open scoped Manifold ContDiff

universe u

namespace TauCeti.SmoothEmbedding

variable {E H X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace X] [ChartedSpace H X]
  {E' H' M : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace M] [ChartedSpace H' M]
  {E'' H'' M' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E'']
  [TopologicalSpace H''] {I'' : ModelWithCorners ℝ E'' H''} [I''.Boundaryless]
  [TopologicalSpace M'] [ChartedSpace H'' M']

section Pointwise

variable {n : ℕ∞ω} [IsManifold I n X] [IsManifold I'' n M']

/-- Reparametrising an embedding by a diffeomorphism does not move its tangent planes: the
tangent range of `f.compDiffeomorphOfBoundaryless e h1` at `x` is that of `f` at `e x`. -/
theorem tangentRange_compDiffeomorphOfBoundaryless (f : SmoothEmbedding I' I n M X)
    (e : M' ≃ₘ^n⟮I'', I'⟯ M) (h1 : 1 ≤ n) (x : M') :
    (f.compDiffeomorphOfBoundaryless e h1).isImmersion.tangentRange x
        (ENat.one_le_iff_ne_zero_withTop.1 h1) =
      f.isImmersion.tangentRange (e x) (ENat.one_le_iff_ne_zero_withTop.1 h1) := by
  rw [Manifold.IsImmersion.tangentRange_def, Manifold.IsImmersion.tangentRange_def]
  exact range_mfderiv_compDiffeomorphOfBoundaryless f e h1 x

/-- A field of endomorphisms `A y` of the tangent spaces of `X`, for instance an almost complex
structure, that maps the tangent planes of `f` into themselves does the same for those of the
reparametrised embedding `f.compDiffeomorphOfBoundaryless e h1`. -/
theorem mapsTo_tangentRange_compDiffeomorphOfBoundaryless (f : SmoothEmbedding I' I n M X)
    (e : M' ≃ₘ^n⟮I'', I'⟯ M) (h1 : 1 ≤ n)
    {A : ∀ y : X, TangentSpace I y → TangentSpace I y}
    (hA : ∀ y, MapsTo (A (f y))
      (f.isImmersion.tangentRange y (ENat.one_le_iff_ne_zero_withTop.1 h1))
      (f.isImmersion.tangentRange y (ENat.one_le_iff_ne_zero_withTop.1 h1))) (x : M') :
    MapsTo (A (f.compDiffeomorphOfBoundaryless e h1 x))
      ((f.compDiffeomorphOfBoundaryless e h1).isImmersion.tangentRange x
        (ENat.one_le_iff_ne_zero_withTop.1 h1))
      ((f.compDiffeomorphOfBoundaryless e h1).isImmersion.tangentRange x
        (ENat.one_le_iff_ne_zero_withTop.1 h1)) := by
  rw [tangentRange_compDiffeomorphOfBoundaryless, compDiffeomorphOfBoundaryless_apply]
  exact hA (e x)

/-- The reparametrised embedding `f.compDiffeomorphOfBoundaryless e h1` is `f ∘ e`, as a commuting
square with the identity of `X`. -/
theorem id_comp_compDiffeomorphOfBoundaryless (f : SmoothEmbedding I' I n M X)
    (e : M' ≃ₘ^n⟮I'', I'⟯ M) (h1 : 1 ≤ n) :
    _root_.id ∘ (f.compDiffeomorphOfBoundaryless e h1) = f ∘ e := by
  rw [coe_compDiffeomorphOfBoundaryless, Function.id_comp]

/-- The identification of the normal space at `x` of the reparametrised embedding
`f.compDiffeomorphOfBoundaryless e h1` with the normal space of `f` at `e x`: both are quotients of
the tangent space of `X` at `f (e x)` by the same subspace, and a class is sent to the class of
the same tangent vector. -/
def normalSpaceEquivCompDiffeomorphOfBoundaryless (f : SmoothEmbedding I' I n M X)
    (e : M' ≃ₘ^n⟮I'', I'⟯ M) (h1 : 1 ≤ n) (x : M') :
    (f.compDiffeomorphOfBoundaryless e h1).isImmersion.NormalSpace x
        (ENat.one_le_iff_ne_zero_withTop.1 h1) ≃L[ℝ]
      f.isImmersion.NormalSpace (e x) (ENat.one_le_iff_ne_zero_withTop.1 h1) :=
  (f.compDiffeomorphOfBoundaryless e h1).normalSpaceEquiv f (ENat.one_le_iff_ne_zero_withTop.1 h1)
    (ENat.one_le_iff_ne_zero_withTop.1 h1) (u := e) (v := _root_.id)
    (by rw [mfderiv_id]; exact ContinuousLinearMap.isInvertible_equiv (f := .refl ℝ _))
    (e.isInvertible_mfderiv (ENat.one_le_iff_ne_zero_withTop.1 h1)).surjective
    (EventuallyEq.of_eq (id_comp_compDiffeomorphOfBoundaryless f e h1))

/-- The identification of normal spaces sends the class of a tangent vector `w` of `X` at the
point `f.compDiffeomorphOfBoundaryless e h1 x = f (e x)` to the class of `w`. -/
@[simp]
theorem normalSpaceEquivCompDiffeomorphOfBoundaryless_normalClass (f : SmoothEmbedding I' I n M X)
    (e : M' ≃ₘ^n⟮I'', I'⟯ M) (h1 : 1 ≤ n) (x : M')
    (w : TangentSpace I (f.compDiffeomorphOfBoundaryless e h1 x)) :
    f.normalSpaceEquivCompDiffeomorphOfBoundaryless e h1 x
        ((f.compDiffeomorphOfBoundaryless e h1).isImmersion.normalClass x
          (ENat.one_le_iff_ne_zero_withTop.1 h1) w) =
      f.isImmersion.normalClass (e x) (ENat.one_le_iff_ne_zero_withTop.1 h1)
        (tangentSpaceCast I (f.compDiffeomorphOfBoundaryless e h1 x) (f (e x)) w) := by
  rw [normalSpaceEquivCompDiffeomorphOfBoundaryless, normalSpaceEquiv_normalClass, mfderiv_id,
    ContinuousLinearMap.id_apply]
  -- The base point `id (f.compDiffeomorphOfBoundaryless e h1 x)` reduces to
  -- `f.compDiffeomorphOfBoundaryless e h1 x`.
  rfl

/-- The inverse identification of normal spaces sends the class of a tangent vector `w` of `X` at
`f (e x)` to the class of `w` at the point `f.compDiffeomorphOfBoundaryless e h1 x`. -/
@[simp]
theorem normalSpaceEquivCompDiffeomorphOfBoundaryless_symm_normalClass
    (f : SmoothEmbedding I' I n M X) (e : M' ≃ₘ^n⟮I'', I'⟯ M) (h1 : 1 ≤ n) (x : M')
    (w : TangentSpace I (f (e x))) :
    (f.normalSpaceEquivCompDiffeomorphOfBoundaryless e h1 x).symm
        (f.isImmersion.normalClass (e x) (ENat.one_le_iff_ne_zero_withTop.1 h1) w) =
      (f.compDiffeomorphOfBoundaryless e h1).isImmersion.normalClass x
        (ENat.one_le_iff_ne_zero_withTop.1 h1)
        (tangentSpaceCast I (f (e x)) (f.compDiffeomorphOfBoundaryless e h1 x) w) := by
  rw [ContinuousLinearEquiv.symm_apply_eq,
    normalSpaceEquivCompDiffeomorphOfBoundaryless_normalClass,
    tangentSpaceCast_trans (compDiffeomorphOfBoundaryless_apply f e h1 x).symm
      (compDiffeomorphOfBoundaryless_apply f e h1 x), tangentSpaceCast_self]

/-- The identification of normal spaces is the normal map of the square
`id ∘ (f.compDiffeomorphOfBoundaryless e h1) = f ∘ e`. -/
theorem normalSpaceEquivCompDiffeomorphOfBoundaryless_toContinuousLinearMap
    (f : SmoothEmbedding I' I n M X)
    (e : M' ≃ₘ^n⟮I'', I'⟯ M) (h1 : 1 ≤ n) (x : M') :
    (f.normalSpaceEquivCompDiffeomorphOfBoundaryless e h1 x).toContinuousLinearMap =
      (f.compDiffeomorphOfBoundaryless e h1).normalMap f (ENat.one_le_iff_ne_zero_withTop.1 h1)
        (ENat.one_le_iff_ne_zero_withTop.1 h1)
        (EventuallyEq.of_eq (id_comp_compDiffeomorphOfBoundaryless f e h1)) := by
  rw [normalSpaceEquivCompDiffeomorphOfBoundaryless, normalSpaceEquiv_toContinuousLinearMap]

/-- The identification of normal spaces is complex linear for the complex structures that an
almost complex structure `J` preserving the tangent planes of `f` induces on the normal spaces of
`f` and of the reparametrised embedding. -/
theorem normalSpaceEquivCompDiffeomorphOfBoundaryless_normalComplexStructureAt [IsManifold I ∞ X]
    (f : SmoothEmbedding I' I n M X)
    (e : M' ≃ₘ^n⟮I'', I'⟯ M) (h1 : 1 ≤ n) (J : SmoothAlmostComplexStructure I X)
    (hJ : ∀ y, MapsTo (J (f y))
      (f.isImmersion.tangentRange y (ENat.one_le_iff_ne_zero_withTop.1 h1))
      (f.isImmersion.tangentRange y (ENat.one_le_iff_ne_zero_withTop.1 h1))) (x : M')
    (ν : (f.compDiffeomorphOfBoundaryless e h1).isImmersion.NormalSpace x
      (ENat.one_le_iff_ne_zero_withTop.1 h1)) :
    f.normalSpaceEquivCompDiffeomorphOfBoundaryless e h1 x
        ((f.compDiffeomorphOfBoundaryless e h1).normalComplexStructureAt
          (ENat.one_le_iff_ne_zero_withTop.1 h1) J x
          (f.mapsTo_tangentRange_compDiffeomorphOfBoundaryless e h1 (A := (J ·)) hJ x) ν) =
      f.normalComplexStructureAt (ENat.one_le_iff_ne_zero_withTop.1 h1) J (e x) (hJ (e x))
        (f.normalSpaceEquivCompDiffeomorphOfBoundaryless e h1 x ν) := by
  have hn : n ≠ 0 := ENat.one_le_iff_ne_zero_withTop.1 h1
  obtain ⟨w, rfl⟩ := (f.compDiffeomorphOfBoundaryless e h1).isImmersion.normalClass_surjective
    x hn ν
  rw [normalComplexStructureAt_normalClass,
    normalSpaceEquivCompDiffeomorphOfBoundaryless_normalClass,
    normalSpaceEquivCompDiffeomorphOfBoundaryless_normalClass, normalComplexStructureAt_normalClass]
  exact apply_eq_of_tangentSpaceCast
    (fun y v ↦ f.isImmersion.normalClass (e x) hn (tangentSpaceCast I y (f (e x)) (J y v)))
    (compDiffeomorphOfBoundaryless_apply f e h1 x) rfl

end Pointwise

section Bundle

variable {n : ℕ∞ω} [IsManifold I 1 X] [IsManifold I n X] [IsManifold I'' n M']

/-- The identifications of the normal spaces of `f.compDiffeomorphOfBoundaryless e h1` with those
of `f`, over `e`, are continuous on the total spaces of the normal bundles, for any model
fibres. -/
theorem continuous_normalSpaceEquivCompDiffeomorphOfBoundaryless {K K' : Type*}
    (f : SmoothEmbedding I' I n M X)
    (e : M' ≃ₘ^n⟮I'', I'⟯ M) (h1 : 1 ≤ n) :
    Continuous fun p : TotalSpace K
        (fun x ↦ (f.compDiffeomorphOfBoundaryless e h1).isImmersion.NormalSpace x
          (ENat.one_le_iff_ne_zero_withTop.1 h1)) ↦
      TotalSpace.mk' K'
        (E := fun y ↦ f.isImmersion.NormalSpace y (ENat.one_le_iff_ne_zero_withTop.1 h1))
        (e p.proj)
        (f.normalSpaceEquivCompDiffeomorphOfBoundaryless e h1 p.proj p.snd) := by
  have hn : n ≠ 0 := ENat.one_le_iff_ne_zero_withTop.1 h1
  refine ((f.compDiffeomorphOfBoundaryless e h1).continuous_normalBundleMap (K := K) (K' := K')
    f hn hn contMDiff_id (id_comp_compDiffeomorphOfBoundaryless f e h1)).congr fun p ↦ ?_
  rw [normalBundleMap_apply, ← normalSpaceEquivCompDiffeomorphOfBoundaryless_toContinuousLinearMap,
    ContinuousLinearEquiv.coe_coe]

end Bundle

section Smooth

variable {n r : ℕ∞ω} [IsManifold I n X] [IsManifold I'' n M'] [FiniteDimensional ℝ E']
  [FiniteDimensional ℝ E''] [IsManifold I (r + 1) X] [IsManifold I' (r + 1) M]
  [IsManifold I'' (r + 1) M']
  {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

/-- The identifications of the normal spaces of `f.compDiffeomorphOfBoundaryless e h1` with those
of `f`, over `e`, are `C^r` on the total spaces of the normal bundles with model fibre `P`, when
`f` and `e` are `C^n` with `r + 1 ≤ n`. -/
theorem contMDiff_normalSpaceEquivCompDiffeomorphOfBoundaryless (f : SmoothEmbedding I' I n M X)
    (e : M' ≃ₘ^n⟮I'', I'⟯ M) (h1 : 1 ≤ n) (hr : r + 1 ≤ n)
    (hP : finrank ℝ P = finrank ℝ E - finrank ℝ E')
    (hP' : finrank ℝ P = finrank ℝ E - finrank ℝ E'') :
    haveI : IsManifold I 1 X := .of_le (n := r + 1) le_add_self
    haveI : IsManifold I' 1 M := .of_le (n := r + 1) le_add_self
    haveI : IsManifold I'' 1 M' := .of_le (n := r + 1) le_add_self
    letI := f.normalSpaceFiberBundle (ENat.one_le_iff_ne_zero_withTop.1 h1) hP
    letI := (f.compDiffeomorphOfBoundaryless e h1).normalSpaceFiberBundle
      (ENat.one_le_iff_ne_zero_withTop.1 h1) hP'
    ContMDiff (I''.prod 𝓘(ℝ, P)) (I'.prod 𝓘(ℝ, P)) r
      fun p : TotalSpace P
          (fun x ↦ (f.compDiffeomorphOfBoundaryless e h1).isImmersion.NormalSpace x
            (ENat.one_le_iff_ne_zero_withTop.1 h1)) ↦
        TotalSpace.mk' P
          (E := fun y ↦ f.isImmersion.NormalSpace y (ENat.one_le_iff_ne_zero_withTop.1 h1))
          (e p.proj)
          (f.normalSpaceEquivCompDiffeomorphOfBoundaryless e h1 p.proj p.snd) := by
  have hn : n ≠ 0 := ENat.one_le_iff_ne_zero_withTop.1 h1
  have : IsManifold I 1 X := .of_le (n := r + 1) le_add_self
  have : IsManifold I' 1 M := .of_le (n := r + 1) le_add_self
  have : IsManifold I'' 1 M' := .of_le (n := r + 1) le_add_self
  let := f.normalSpaceFiberBundle hn hP
  let := (f.compDiffeomorphOfBoundaryless e h1).normalSpaceFiberBundle hn hP'
  refine ((f.compDiffeomorphOfBoundaryless e h1).contMDiff_normalBundleMap (r := r) f hn hn
    hr hr hP' hP contMDiff_id
    (id_comp_compDiffeomorphOfBoundaryless f e h1)).congr fun p ↦ ?_
  rw [normalBundleMap_apply, ← normalSpaceEquivCompDiffeomorphOfBoundaryless_toContinuousLinearMap,
    ContinuousLinearEquiv.coe_coe]

/-- A map into the normal bundle of `f.compDiffeomorphOfBoundaryless e h1` that is given over
`u y` by the inverse identification of normal spaces applied to `w y`, a normal vector of `f` at
`e (u y)`, is `C^k` for `k ≤ r` exactly when `y ↦ w y` is `C^k` as a map into the normal bundle
of `f`. -/
theorem contMDiff_normalSpaceEquivCompDiffeomorphOfBoundaryless_symm_iff
    {EY HY Y : Type*} [NormedAddCommGroup EY] [NormedSpace ℝ EY] [TopologicalSpace HY]
    {L : ModelWithCorners ℝ EY HY} [TopologicalSpace Y] [ChartedSpace HY Y]
    (f : SmoothEmbedding I' I n M X) (e : M' ≃ₘ^n⟮I'', I'⟯ M) (h1 : 1 ≤ n)
    (hr : r + 1 ≤ n) (hP : finrank ℝ P = finrank ℝ E - finrank ℝ E')
    (hP' : finrank ℝ P = finrank ℝ E - finrank ℝ E'') {k : ℕ∞ω} (hk : k ≤ r) {u : Y → M'}
    {w : ∀ y, f.isImmersion.NormalSpace (e (u y)) (ENat.one_le_iff_ne_zero_withTop.1 h1)} :
    haveI : IsManifold I 1 X := .of_le (n := r + 1) le_add_self
    haveI : IsManifold I' 1 M := .of_le (n := r + 1) le_add_self
    haveI : IsManifold I'' 1 M' := .of_le (n := r + 1) le_add_self
    letI := f.normalSpaceFiberBundle (ENat.one_le_iff_ne_zero_withTop.1 h1) hP
    letI := (f.compDiffeomorphOfBoundaryless e h1).normalSpaceFiberBundle
      (ENat.one_le_iff_ne_zero_withTop.1 h1) hP'
    ContMDiff L (I''.prod 𝓘(ℝ, P)) k (fun y ↦ TotalSpace.mk' P
        (E := fun x ↦ (f.compDiffeomorphOfBoundaryless e h1).isImmersion.NormalSpace x
          (ENat.one_le_iff_ne_zero_withTop.1 h1)) (u y)
        ((f.normalSpaceEquivCompDiffeomorphOfBoundaryless e h1 (u y)).symm (w y))) ↔
      ContMDiff L (I'.prod 𝓘(ℝ, P)) k (fun y ↦ TotalSpace.mk' P
        (E := fun x ↦ f.isImmersion.NormalSpace x (ENat.one_le_iff_ne_zero_withTop.1 h1)) (e (u y))
        (w y)) := by
  have hn : n ≠ 0 := ENat.one_le_iff_ne_zero_withTop.1 h1
  have : IsManifold I 1 X := .of_le (n := r + 1) le_add_self
  have : IsManifold I' 1 M := .of_le (n := r + 1) le_add_self
  have : IsManifold I'' 1 M' := .of_le (n := r + 1) le_add_self
  let := f.normalSpaceFiberBundle hn hP
  let := (f.compDiffeomorphOfBoundaryless e h1).normalSpaceFiberBundle hn hP'
  refine ⟨fun h ↦ (((f.contMDiff_normalSpaceEquivCompDiffeomorphOfBoundaryless e h1 hr
    hP hP').of_le hk).comp h).congr fun y ↦ ?_, fun h ↦ ?_⟩
  · simp only [Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply]
  -- The normal map of the square `id ∘ f = (f ∘ e) ∘ e⁻¹` inverts the identifications.
  have hsq : _root_.id ∘ f = (f.compDiffeomorphOfBoundaryless e h1) ∘ e.symm := by
    funext y
    simp
  refine (((f.contMDiff_normalBundleMap (r := r) (f.compDiffeomorphOfBoundaryless e h1) hn hn
    hr hr hP hP' contMDiff_id hsq).of_le hk).comp h).congr fun y ↦ ?_
  obtain ⟨v, hv⟩ := f.isImmersion.normalClass_surjective (e (u y)) hn (w y)
  rw [Function.comp_apply, normalBundleMap_apply, ← hv, normalMap_normalClass, mfderiv_id,
    ContinuousLinearMap.id_apply,
    normalSpaceEquivCompDiffeomorphOfBoundaryless_symm_normalClass]
  -- The base points `e⁻¹ (e (u y))` and `u y` are equal.
  generalize hb : e.symm (e (u y)) = b
  rw [e.symm_apply_apply] at hb
  subst hb
  rfl

end Smooth

section Symplectic

variable {n : ℕ∞ω} [IsManifold I ∞ X] [IsManifold I n X] [IsManifold I'' n M']
  {σ : SmoothTwoForm I X} {hσ : σ.IsNondegenerate}

/-- The reparametrised embedding `f.compDiffeomorphOfBoundaryless e h1` has symplectic tangent
images for a nondegenerate two-form `σ` on `X` exactly when `f` has. -/
theorem hasSymplecticTangentImages_compDiffeomorphOfBoundaryless_iff
    (f : SmoothEmbedding I' I n M X) (e : M' ≃ₘ^n⟮I'', I'⟯ M) (h1 : 1 ≤ n) :
    hσ.HasSymplecticTangentImages I'' (f.compDiffeomorphOfBoundaryless e h1) ↔
      hσ.HasSymplecticTangentImages I' f := by
  have hn : n ≠ 0 := ENat.one_le_iff_ne_zero_withTop.1 h1
  rw [coe_compDiffeomorphOfBoundaryless]
  exact hσ.hasSymplecticTangentImages_comp_diffeomorph_iff e hn

/-- The identification of the normal spaces of `f.compDiffeomorphOfBoundaryless e h1` with those
of `f` carries the normal symplectic form of the first, for a nondegenerate two-form `σ` on `X`,
to that of the second. -/
theorem symplecticNormalForm_normalSpaceEquivCompDiffeomorphOfBoundaryless
    (f : SmoothEmbedding I' I n M X) (e : M' ≃ₘ^n⟮I'', I'⟯ M) (h1 : 1 ≤ n)
    (hf : hσ.HasSymplecticTangentImages I' f)
    (hg : hσ.HasSymplecticTangentImages I'' (f.compDiffeomorphOfBoundaryless e h1)) (x : M')
    (ν μ : (f.compDiffeomorphOfBoundaryless e h1).isImmersion.NormalSpace x
      (ENat.one_le_iff_ne_zero_withTop.1 h1)) :
    f.symplecticNormalForm hf (e x) (ENat.one_le_iff_ne_zero_withTop.1 h1)
        (f.normalSpaceEquivCompDiffeomorphOfBoundaryless e h1 x ν)
        (f.normalSpaceEquivCompDiffeomorphOfBoundaryless e h1 x μ) =
      (f.compDiffeomorphOfBoundaryless e h1).symplecticNormalForm hg x
        (ENat.one_le_iff_ne_zero_withTop.1 h1) ν μ := by
  have hn : n ≠ 0 := ENat.one_le_iff_ne_zero_withTop.1 h1
  rw [← ContinuousLinearEquiv.coe_coe,
    normalSpaceEquivCompDiffeomorphOfBoundaryless_toContinuousLinearMap]
  refine (f.compDiffeomorphOfBoundaryless e h1).symplecticNormalForm_normalMap f hg hf hn hn _
    mdifferentiableAt_id (fun a b ↦ ?_) (e.isInvertible_mfderiv hn).surjective ν μ
  rw [mfderiv_id, ContinuousLinearMap.id_apply, ContinuousLinearMap.id_apply]
  -- The base point `id (g x)` is `g x`.
  rfl

end Symplectic

section EulerClass

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless] [IsManifold I ∞ X]
  [FiniteDimensional ℝ E'] {M : Type u} [TopologicalSpace M] [ChartedSpace H' M]
  [IsManifold I' ∞ M] [FiniteDimensional ℝ E''] {M' : Type u} [TopologicalSpace M']
  [ChartedSpace H'' M'] [IsManifold I'' ∞ M']
  {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  {G : Type u} [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G]
  [Fact (finrank ℝ P = 2 * finrank ℂ G)] {r : ℕ} {hn : (∞ : ℕ∞ω) ≠ 0}

/-- **The Euler class of the complex normal bundle of a reparametrised embedding.** Let `J` be a
smooth almost complex structure on `X` that preserves the tangent planes of a smooth embedding
`f : M → X`, and `e : M' ≃ M` a diffeomorphism. Then the Euler class of the normal bundle of
`f.compDiffeomorphOfBoundaryless e h1`, with the complex structure that `J` induces on it, is the
pull-back along `e` of the Euler class of the normal bundle of `f` with its induced complex
structure. The normal bundles have the model fibre `P` and the complex model `G`, of complex
dimension `r + 1`; `hν` and `hν'` are the dimension hypotheses of the two normal bundles, of
which the second follows from the first when `M'` is nonempty. -/
theorem complexEulerClass_normalComplexStructure_compDiffeomorphOfBoundaryless
    (f : SmoothEmbedding I' I ∞ M X) (e : M' ≃ₘ^∞⟮I'', I'⟯ M) (h1 : 1 ≤ (∞ : ℕ∞ω))
    (J : SmoothAlmostComplexStructure I X)
    (hJ : ∀ y, MapsTo (J (f y)) (f.isImmersion.tangentRange y hn)
      (f.isImmersion.tangentRange y hn))
    (hν : finrank ℝ P = finrank ℝ E - finrank ℝ E')
    (hν' : finrank ℝ P = finrank ℝ E - finrank ℝ E'') (hG : finrank ℂ G = r + 1) :
    letI := f.normalSpaceFiberBundle hn hν
    letI := f.normalSpaceVectorBundle hn hν
    letI := (f.compDiffeomorphOfBoundaryless e h1).normalSpaceFiberBundle hn hν'
    letI := (f.compDiffeomorphOfBoundaryless e h1).normalSpaceVectorBundle hn hν'
    complexEulerClass G ((f.compDiffeomorphOfBoundaryless e h1).normalComplexStructure hn J hν'
        (f.mapsTo_tangentRange_compDiffeomorphOfBoundaryless e h1 (A := (J ·)) hJ)).Fiber hG =
      TopCat.singularCohomologyMap (TopCat.ofHom (e.toHomeomorph : C(M', M))) (2 * r + 2)
        (complexEulerClass G (f.normalComplexStructure hn J hν hJ).Fiber hG) := by
  let := f.normalSpaceFiberBundle hn hν
  let := f.normalSpaceVectorBundle hn hν
  let := (f.compDiffeomorphOfBoundaryless e h1).normalSpaceFiberBundle hn hν'
  let := (f.compDiffeomorphOfBoundaryless e h1).normalSpaceVectorBundle hn hν'
  let Kg := (f.compDiffeomorphOfBoundaryless e h1).normalComplexStructure hn J hν'
    (f.mapsTo_tangentRange_compDiffeomorphOfBoundaryless e h1 (A := (J ·)) hJ)
  let Kf := f.normalComplexStructure hn J hν hJ
  have hΦ : ∀ x ν, f.normalSpaceEquivCompDiffeomorphOfBoundaryless e h1 x (Kg x ν) =
      Kf (e.toHomeomorph x) (f.normalSpaceEquivCompDiffeomorphOfBoundaryless e h1 x ν) :=
    fun x ν ↦ (congrArg _ (normalComplexStructure_apply _ hn J hν' _ x ν)).trans
      ((f.normalSpaceEquivCompDiffeomorphOfBoundaryless_normalComplexStructureAt e h1 J hJ x
        ν).trans (normalComplexStructure_apply f hn J hν hJ (e x) _).symm)
  exact complexEulerClass_eq_singularCohomologyMap_of_fiberwise hG hG
    (g := (e.toHomeomorph : C(M', M)))
    (Bundle.ContinuousComplexStructure.continuous_fiberEquivOfCommuteAlong Kg Kf _ _ hΦ
      (f.continuous_normalSpaceEquivCompDiffeomorphOfBoundaryless e h1))

end EulerClass

end TauCeti.SmoothEmbedding

end
