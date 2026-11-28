/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Basic
public import SymplecticGeometry.Topology.VectorBundle.DetBundle.CongrModel
public import TauCeti.Topology.VectorBundle.Determinant
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.ComplexStructure
public import SymplecticGeometry.Topology.VectorBundle.Complex.RestrictScalars
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Complex.Structure
import Mathlib.Analysis.Normed.Operator.Mul
import SymplecticGeometry.Geometry.Manifold.VectorBundle.Hom
import SymplecticGeometry.Geometry.Manifold.VectorBundle.RestrictScalars
import SymplecticGeometry.Topology.VectorBundle.DetBundle.Trivialization
import SymplecticGeometry.Topology.VectorBundle.ModelEquiv
import TauCeti.Analysis.Calculus.FDeriv.Det.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Hom.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Hermitian

/-!
# The determinant line of a smooth vector bundle is smooth

Let `𝕜'` be a complete normed field that is a normed algebra over the complete field `𝕜`, and let
`E` be a vector bundle over `𝕜'` with finite-dimensional model `G`, over a manifold `B` with a
model `I` over `𝕜`. Suppose that `E` is also a vector bundle over `𝕜`, with the same
trivializations, and that it is `C^n` over `𝕜`. The main case is a complex vector bundle over a
real manifold, with its real structure from `open scoped VectorBundle.ComplexToReal` (and the
finite dimension of `G` over `ℝ` from `FiniteDimensional.complexToReal`); the case `𝕜 = 𝕜'` is
that of a `C^n` vector bundle over `𝕜`.

This file shows that Tau Ceti's determinant line `TauCeti.DetBundle 𝕜' G E` is then a `C^n` line
bundle over `𝕜`. Its trivializations are induced by those of `E`
(`TauCeti.DetBundle.exists_eq_trivialization`), and its coordinate changes are multiplication by
the determinants over `𝕜'` of the coordinate changes of `E`
(`TauCeti.DetBundle.coordChangeL_trivialization`). The coordinate changes of `E` over `𝕜'` are
`C^n` over `𝕜` (`contMDiffOn_coordChangeL_of_restrictScalars`), and the determinant is a
polynomial, so it is `C^n` over `𝕜'` (`ContinuousLinearMap.contDiff_det`), hence over `𝕜`.

A fibrewise isomorphism `e x : E x ≃ E' x` of vector bundles over `𝕜'`, whose models `G` and `G'`
may differ, induces the map `TauCeti.DetBundle.congrModelHomeomorph` of the total spaces of the
determinant lines. In the charts at a point it multiplies the coordinate by the determinant of
the coordinate expression of `e`, composed with a fixed identification of the models
(`TauCeti.DetBundle.chartCoord_congrModelEquiv`). If `e` is `C^n` over `𝕜` on total spaces, that
expression is `C^n` over `𝕜` (`contMDiffAt_continuousLinearMapAt_comp_symmL_of_restrictScalars`),
so the factor is `C^n` and vanishes nowhere, and its inverse is `C^n` too. A fibrewise map that
is a `C^n` family of linear maps in the trivializations at each point is `C^n`
(`Bundle.contMDiff_bundleMap_of_coordinates`, which generalizes Tau Ceti's
`TauCeti.contMDiff_bundleMap_of_constant_coordinates`), so the transport and its inverse are `C^n`.
Neither bundle needs a `C^n` structure for this.

For a line bundle, Tau Ceti identifies the determinant line with the bundle itself
(`TauCeti.DetBundle.lineHomeomorph`). Read in the trivializations at a point, this identification
multiplies the coordinate by the vector of the basis `Module.finBasis 𝕜' G` of the model line
(`TauCeti.DetBundle.snd_apply_lineEquiv`), and its inverse takes the coordinate along that
vector. A fibrewise map that is a fixed continuous linear map in these trivializations is `C^n`
(`TauCeti.contMDiff_bundleMap_of_constant_coordinates`), so both are `C^n`. This needs no
smoothness of `E`.

For a continuous map `f : B' → B` of manifolds, Tau Ceti identifies the pull-back of the
determinant line with the determinant line of the pull-back
(`TauCeti.DetBundle.pullbackHomeomorph`). The preferred trivializations of both are those induced
by the trivialization of `E` at the image point, and in them the identification keeps the
coordinate (`TauCeti.DetBundle.snd_trivializationAt_pullbackEquiv`), so it is `C^n` in both
directions by the same lemma. Neither `f` nor `E` needs to be smooth.

For a `Cⁿ` complex structure `J` on a `Cⁿ` real vector bundle over a σ-compact Hausdorff
manifold, the determinant line of the complex bundle `J.toContinuousComplexStructure.Fiber` is a
`Cⁿ` complex line bundle (`TauCeti.DetBundle.contMDiffVectorBundle`), and Tau Ceti's
`TauCeti.exists_contMDiffRiemannianMetric_inner_smul_I` gives it a `Cⁿ` real metric that
multiplication by `Complex.I` preserves. The real scalar multiplication on its fibres is
continuous by the scoped instance `VectorBundle.ComplexToReal.continuousSMul`.

## Main results

* `TauCeti.DetBundle.contMDiffVectorBundle`: the determinant line of a `C^n` vector bundle is a
  `C^n` vector bundle.
* `TauCeti.DetBundle.contMDiff_congrModelHomeomorph`,
  `TauCeti.DetBundle.contMDiff_congrModelHomeomorph_symm`: a `C^n` fibrewise isomorphism of
  vector bundles, with possibly different models, induces a `C^n` map of their determinant lines,
  with `C^n` inverse.
* `TauCeti.DetBundle.contMDiff_lineHomeomorph`, `TauCeti.DetBundle.contMDiff_lineHomeomorph_symm`:
  for a line bundle, the identification of its determinant line with itself is `C^n` in both
  directions.
* `TauCeti.DetBundle.contMDiff_pullbackHomeomorph`,
  `TauCeti.DetBundle.contMDiff_pullbackHomeomorph_symm`: the identification of the pull-back of
  the determinant line with the determinant line of the pull-back is `C^n` in both directions.
* `SymplecticGeometry.Bundle.ContMDiffComplexStructure.exists_hermitianMetric_detBundle`: the
  determinant line of a smooth complex structure has a smooth Hermitian metric.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton University Press, 1974, §3.
* D. Huybrechts, *Complex Geometry: An Introduction*, §2.2.
-/

public section

open Bundle Module
open scoped Manifold

namespace TauCeti.DetBundle

variable {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜]
  [NontriviallyNormedField 𝕜'] [CompleteSpace 𝕜'] [NormedAlgebra 𝕜 𝕜']
  {EB HB B : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] [TopologicalSpace HB]
  {I : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B] {n : WithTop ℕ∞}
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜' G] [NormedSpace 𝕜 G] [IsScalarTower 𝕜 𝕜' G]
  [FiniteDimensional 𝕜' G]
  {E : B → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module 𝕜' (E x)]
  [∀ x, TopologicalSpace (E x)] [TopologicalSpace (TotalSpace G E)]
  [FiberBundle G E] [VectorBundle 𝕜' G E]

section Smooth

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 G] [∀ x, Module 𝕜 (E x)] [VectorBundle 𝕜 G E]
  [ContMDiffVectorBundle n G E I]
  [∀ x, Module 𝕜 (DetBundle 𝕜' G E x)] [VectorBundle 𝕜 𝕜' (DetBundle 𝕜' G E)]

/-- **The determinant line of a `C^n` vector bundle is a `C^n` line bundle.** For a vector bundle
`E` over `𝕜'` with finite-dimensional model, which is also a `C^n` vector bundle over `𝕜` with
the same trivializations, the coordinate changes of its determinant line, multiplication by the
determinants over `𝕜'` of those of `E`, are `C^n` over `𝕜`. For instance, the determinant line of
a smooth complex vector bundle over a real manifold is a smooth complex line bundle. -/
instance contMDiffVectorBundle : ContMDiffVectorBundle n 𝕜' (DetBundle 𝕜' G E) I where
  contMDiffOn_coordChangeL e e' _ _ := by
    obtain ⟨e₀, _, rfl⟩ := exists_eq_trivialization e
    obtain ⟨e₀', _, rfl⟩ := exists_eq_trivialization e'
    rw [trivialization_baseSet, trivialization_baseSet]
    have hdet : ContMDiffOn I 𝓘(𝕜, 𝕜') n
        (fun b ↦ (e₀.coordChangeL 𝕜' e₀' b : G →L[𝕜'] G).det)
        (e₀.baseSet ∩ e₀'.baseSet) :=
      (ContDiff.restrict_scalars 𝕜 ContinuousLinearMap.contDiff_det).contMDiff.comp_contMDiffOn
        (contMDiffOn_coordChangeL_of_restrictScalars e₀ e₀')
    refine ((ContinuousLinearMap.mul 𝕜 𝕜').contMDiff.comp_contMDiffOn hdet).congr fun b hb ↦ ?_
    ext c
    rw [Function.comp_apply, ContinuousLinearMap.mul_apply',
      ← coordChangeL_trivialization e₀ e₀' hb c,
      ← Trivialization.restrictScalars_coordChangeL 𝕜 𝕜', ContinuousLinearMap.coe_restrictScalars',
      ContinuousLinearEquiv.coe_coe]

end Smooth

section CongrModel

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 G]
  {G' : Type*} [NormedAddCommGroup G'] [NormedSpace 𝕜' G'] [NormedSpace 𝕜 G']
  [IsScalarTower 𝕜 𝕜' G'] [FiniteDimensional 𝕜' G'] [FiniteDimensional 𝕜 G']
  {E' : B → Type*} [∀ x, AddCommGroup (E' x)] [∀ x, Module 𝕜' (E' x)]
  [∀ x, TopologicalSpace (E' x)] [TopologicalSpace (TotalSpace G' E')]
  [FiberBundle G' E'] [VectorBundle 𝕜' G' E']

/-- Read in the charts at `a` of the determinant lines, the transport `congrModelEquiv e` is
multiplication by a function of the base point that is `C^n` at `a` and vanishes nowhere on the
two base sets. -/
private theorem exists_contMDiffAt_chartCoord_congrModelEquiv (e : ∀ x, E x ≃L[𝕜'] E' x)
    (he : ContMDiff (I.prod 𝓘(𝕜, G)) (I.prod 𝓘(𝕜, G')) n
      (fun p : TotalSpace G E ↦ TotalSpace.mk' G' p.proj (e p.proj p.snd))) (a : B) :
    ∃ s : B → 𝕜', ContMDiffAt I 𝓘(𝕜, 𝕜') n s a ∧
      ∀ x (hx : x ∈ (trivializationAt G E a).baseSet)
        (hx' : x ∈ (trivializationAt G' E' a).baseSet), s x ≠ 0 ∧ ∀ v : DetBundle 𝕜' G E x,
        chartCoord (trivializationAt G' E' a) hx' (congrModelEquiv (F₁ := G) (F' := G') e x v) =
          s x * chartCoord (trivializationAt G E a) hx v := by
  set t := trivializationAt G E a
  set t' := trivializationAt G' E' a
  have h : finrank 𝕜' G' = finrank 𝕜' G :=
    (VectorBundle.modelEquiv G G' a (e a)).toLinearEquiv.finrank_eq.symm
  set L : G' →L[𝕜'] G :=
    ((finBasis 𝕜' G').equiv (finBasis 𝕜' G) (finCongr h) : G' ≃ₗ[𝕜'] G).toContinuousLinearMap
  -- The coordinate expression of `e` is `C^n` over `𝕜`, and so is its determinant after `L`.
  have hT := contMDiffAt_continuousLinearMapAt_comp_symmL_of_restrictScalars
    (fun x ↦ (e x : E x →L[𝕜'] E' x)) a fun _ ↦ he _
  have hdet : ContDiff 𝕜 n fun T : G →L[𝕜'] G' ↦ LinearMap.det ((T.comp L : G' →L[𝕜'] G') :
      G' →ₗ[𝕜'] G') :=
    (ContinuousLinearMap.contDiff_det.comp
      ((ContinuousLinearMap.compL 𝕜' G' G G').flip L).contDiff).restrict_scalars 𝕜
  refine ⟨_, hdet.contMDiff.contMDiffAt.comp a hT, fun x hx hx' ↦
    ⟨fun h0 ↦ ?_, fun v ↦ chartCoord_congrModelEquiv e h t t' hx hx' v⟩⟩
  -- A zero factor would send the nonzero vector of chart coordinate `1` to zero.
  have h1 := chartCoord_congrModelEquiv e h t t' hx hx' ((chartCoord t hx).symm 1)
  rw [LinearEquiv.apply_symm_apply, mul_one] at h1
  have h2 := h1.trans h0
  rw [LinearEquiv.map_eq_zero_iff, ContinuousLinearEquiv.map_eq_zero_iff,
    LinearEquiv.map_eq_zero_iff] at h2
  exact one_ne_zero h2

/-- **The determinant transport between different models is `C^n`.** Let `e x : E x ≃ E' x` be
continuous `𝕜'`-linear isomorphisms of the fibres of vector bundles over `𝕜'` whose models `G`
and `G'` are finite-dimensional over `𝕜'` and over `𝕜`. If the map of total spaces induced by `e`
is `C^n` over `𝕜`, then so is the map `TauCeti.DetBundle.congrModelHomeomorph` that it induces
on the total spaces of the determinant lines. For instance, a smooth fibrewise complex-linear
isomorphism of complex vector bundles over a real manifold induces a smooth map of their
determinant lines. -/
theorem contMDiff_congrModelHomeomorph (e : ∀ x, E x ≃L[𝕜'] E' x)
    (he : ContMDiff (I.prod 𝓘(𝕜, G)) (I.prod 𝓘(𝕜, G')) n
      (fun p : TotalSpace G E ↦ TotalSpace.mk' G' p.proj (e p.proj p.snd))) :
    ContMDiff (I.prod 𝓘(𝕜, 𝕜')) (I.prod 𝓘(𝕜, 𝕜')) n (congrModelHomeomorph e he.continuous) := by
  refine (Bundle.contMDiff_bundleMap_of_coordinates (IB := I) (n := n)
    (fun x ↦ congrModelEquiv (F₁ := G) (F' := G') e x) fun a ↦ ?_).congr
      (congrModelHomeomorph_apply e he.continuous)
  obtain ⟨s, hs, hs'⟩ := exists_contMDiffAt_chartCoord_congrModelEquiv e he a
  refine ⟨fun x ↦ ContinuousLinearMap.mul 𝕜 𝕜' (s x),
    (ContinuousLinearMap.mul 𝕜 𝕜').contMDiff.contMDiffAt.comp a hs, ?_⟩
  rintro x ⟨hx, hx'⟩ v
  simp only [trivializationAt_eq, trivialization_baseSet] at hx hx' ⊢
  rw [trivialization_apply_mk _ hx', trivialization_apply_mk _ hx, (hs' x hx hx').2 v,
    ContinuousLinearMap.mul_apply']

/-- **The inverse of the determinant transport between different models is `C^n`.** Under the
hypotheses of `TauCeti.DetBundle.contMDiff_congrModelHomeomorph`, the inverse of the map
`TauCeti.DetBundle.congrModelHomeomorph` of the total spaces of the determinant lines is `C^n`
over `𝕜`. No smoothness of the inverses of `e` is assumed. -/
theorem contMDiff_congrModelHomeomorph_symm (e : ∀ x, E x ≃L[𝕜'] E' x)
    (he : ContMDiff (I.prod 𝓘(𝕜, G)) (I.prod 𝓘(𝕜, G')) n
      (fun p : TotalSpace G E ↦ TotalSpace.mk' G' p.proj (e p.proj p.snd))) :
    ContMDiff (I.prod 𝓘(𝕜, 𝕜')) (I.prod 𝓘(𝕜, 𝕜')) n
      (congrModelHomeomorph e he.continuous).symm := by
  refine (Bundle.contMDiff_bundleMap_of_coordinates (IB := I) (n := n)
    (fun x ↦ (congrModelEquiv (F₁ := G) (F' := G') e x).symm) fun a ↦ ?_).congr
      (congrModelHomeomorph_symm_apply e he.continuous)
  obtain ⟨s, hs, hs'⟩ := exists_contMDiffAt_chartCoord_congrModelEquiv e he a
  have hsa : s a ≠ 0 :=
    (hs' a (mem_baseSet_trivializationAt G E a) (mem_baseSet_trivializationAt G' E' a)).1
  -- In the charts at `a`, the inverse is multiplication by the inverse factor.
  refine ⟨fun x ↦ ContinuousLinearMap.mul 𝕜 𝕜' (s x)⁻¹,
    (ContinuousLinearMap.mul 𝕜 𝕜').contMDiff.contMDiffAt.comp a
      ((contDiffAt_inv 𝕜 hsa).contMDiffAt.comp a hs), ?_⟩
  rintro x ⟨hx', hx⟩ w
  simp only [trivializationAt_eq, trivialization_baseSet] at hx hx' ⊢
  obtain ⟨h0, hmul⟩ := hs' x hx hx'
  have h := hmul ((congrModelEquiv (F₁ := G) (F' := G') e x).symm w)
  rw [ContinuousLinearEquiv.apply_symm_apply] at h
  rw [trivialization_apply_mk _ hx', trivialization_apply_mk _ hx, h,
    ContinuousLinearMap.mul_apply', inv_mul_cancel_left₀ h0]

end CongrModel

section Line

/-- **The identification of a line bundle with its determinant line is `C^n`.** For a vector
bundle `L` whose model fibre is a line, the map `det L → L` of total spaces,
`TauCeti.DetBundle.lineHomeomorph`, is `C^n`. -/
theorem contMDiff_lineHomeomorph (hF : finrank 𝕜' G = 1) :
    ContMDiff (I.prod 𝓘(𝕜, 𝕜')) (I.prod 𝓘(𝕜, G)) n (lineHomeomorph (E := E) hF) := by
  have : Unique (Fin (finrank 𝕜' G)) := (finCongr hF).unique
  -- In trivializations, the map multiplies the coordinate by the basis vector of the model.
  let L : 𝕜' →L[𝕜] G :=
    ((ContinuousLinearMap.id 𝕜' 𝕜').smulRight (Module.finBasis 𝕜' G default)).restrictScalars 𝕜
  refine (TauCeti.contMDiff_bundleMap_of_constant_coordinates (IB := I) (n := n)
    (fun x ↦ lineEquiv (E := E) hF x) L fun a x hx v ↦ ?_).congr
      fun p ↦ by simp [lineHomeomorph_apply]
  rw [trivializationAt_eq, trivialization_baseSet, Set.inter_self] at hx
  rw [snd_apply_lineEquiv hF _ hx v default, trivializationAt_eq, trivialization_apply_mk _ hx]
  simp [L]

/-- **The identification of a line bundle with its determinant line is `C^n`.** For a vector
bundle `L` whose model fibre is a line, the inverse `L → det L` of
`TauCeti.DetBundle.lineHomeomorph` is `C^n`. -/
theorem contMDiff_lineHomeomorph_symm (hF : finrank 𝕜' G = 1) :
    ContMDiff (I.prod 𝓘(𝕜, G)) (I.prod 𝓘(𝕜, 𝕜')) n (lineHomeomorph (E := E) hF).symm := by
  have : Unique (Fin (finrank 𝕜' G)) := (finCongr hF).unique
  -- In trivializations, the map reads the coordinate of a vector along the basis of the model.
  let L : G →L[𝕜] 𝕜' :=
    (LinearMap.toContinuousLinearMap ((Module.finBasis 𝕜' G).coord default)).restrictScalars 𝕜
  refine (TauCeti.contMDiff_bundleMap_of_constant_coordinates (IB := I) (n := n)
    (fun x ↦ (lineEquiv (E := E) hF x).symm) L fun a x hx u ↦ ?_).congr
      fun p ↦ by simp [lineHomeomorph_symm_apply]
  rw [trivializationAt_eq, trivialization_baseSet, Set.inter_self] at hx
  have h := snd_apply_lineEquiv hF _ hx ((lineEquiv hF x).symm u) default
  rw [ContinuousLinearEquiv.apply_symm_apply] at h
  rw [h, trivializationAt_eq, trivialization_apply_mk _ hx]
  simp [L]

end Line

section Pullback

variable {EB' HB' B' : Type*} [NormedAddCommGroup EB'] [NormedSpace 𝕜 EB']
  [TopologicalSpace HB'] {I' : ModelWithCorners 𝕜 EB' HB'} [TopologicalSpace B']
  [ChartedSpace HB' B'] {K : Type*} [FunLike K B' B] [ContinuousMapClass K B' B] (f : K)

omit [NormedSpace 𝕜 G] [IsScalarTower 𝕜 𝕜' G] in
/-- **The pull-back of the determinant line is smoothly the determinant line of the pull-back.**
For a continuous map `f : B' → B` of manifolds, the map `TauCeti.DetBundle.pullbackHomeomorph f`
from the pull-back of `det E` to `det (f *ᵖ E)` is `C^n`. -/
theorem contMDiff_pullbackHomeomorph :
    ContMDiff (I'.prod 𝓘(𝕜, 𝕜')) (I'.prod 𝓘(𝕜, 𝕜')) n
      (pullbackHomeomorph (𝕜 := 𝕜') (F := G) (E := E) f) :=
  (TauCeti.contMDiff_bundleMap_of_constant_coordinates (IB := I') (n := n)
    (E₁ := (f : B' → B) *ᵖ (DetBundle 𝕜' G E)) (E₂ := DetBundle 𝕜' G ((f : B' → B) *ᵖ E))
    (fun y ↦ pullbackEquiv (f : B' → B) y) (ContinuousLinearMap.id 𝕜 𝕜') fun a y hy v ↦ by
      rw [ContinuousLinearMap.id_apply]
      exact snd_trivializationAt_pullbackEquiv f hy.1 v).congr
    fun p ↦ by simp

omit [NormedSpace 𝕜 G] [IsScalarTower 𝕜 𝕜' G] in
/-- **The pull-back of the determinant line is smoothly the determinant line of the pull-back.**
For a continuous map `f : B' → B` of manifolds, the inverse `det (f *ᵖ E) → f *ᵖ det E` of
`TauCeti.DetBundle.pullbackHomeomorph f` is `C^n`. -/
theorem contMDiff_pullbackHomeomorph_symm :
    ContMDiff (I'.prod 𝓘(𝕜, 𝕜')) (I'.prod 𝓘(𝕜, 𝕜')) n
      (pullbackHomeomorph (𝕜 := 𝕜') (F := G) (E := E) f).symm :=
  (TauCeti.contMDiff_bundleMap_of_constant_coordinates (IB := I') (n := n)
    (E₁ := DetBundle 𝕜' G ((f : B' → B) *ᵖ E)) (E₂ := (f : B' → B) *ᵖ (DetBundle 𝕜' G E))
    (fun y ↦ (pullbackEquiv (f : B' → B) y).symm) (ContinuousLinearMap.id 𝕜 𝕜')
      fun a y hy u ↦ by
        rw [ContinuousLinearMap.id_apply, ← snd_trivializationAt_pullbackEquiv f hy.2,
          ContinuousLinearEquiv.apply_symm_apply]).congr
    fun p ↦ by simp

end Pullback

end TauCeti.DetBundle

namespace SymplecticGeometry.Bundle.ContMDiffComplexStructure

open scoped ContDiff VectorBundle.ComplexToReal

variable {EB HB M : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [FiniteDimensional ℝ EB]
  [TopologicalSpace HB] {I : ModelWithCorners ℝ EB HB} [TopologicalSpace M] [ChartedSpace HB M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V] {n : ℕ∞} [ContMDiffVectorBundle n F V I]
  (G : Type*) [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G]
  [Fact (finrank ℝ F = 2 * finrank ℂ G)]

/-- **The determinant line of a smooth complex structure has a smooth Hermitian metric.** Let `J`
be a `Cⁿ` complex structure on a `Cⁿ` real vector bundle `V` with finite-dimensional model `F`,
over a σ-compact Hausdorff smooth manifold with finite-dimensional model, and let `G` be a complex
model with `dim_ℝ F = 2 dim_ℂ G`. The determinant line of the complex bundle
`J.toContinuousComplexStructure.Fiber`, as a real line bundle, carries a `Cⁿ` real metric `g`
that multiplication by `Complex.I` preserves: a Hermitian metric, in the form that
`SymplecticGeometry.Bundle.contMDiffFiberBundle_circleFiber` takes. -/
theorem exists_hermitianMetric_detBundle (J : ContMDiffComplexStructure I n F V) :
    ∃ g : ContMDiffRiemannianMetric I n ℂ
        (TauCeti.DetBundle ℂ G J.toContinuousComplexStructure.Fiber),
      ∀ x v w, g.inner x (Complex.I • v) (Complex.I • w) = g.inner x v w :=
  TauCeti.exists_contMDiffRiemannianMetric_inner_smul_I

end SymplecticGeometry.Bundle.ContMDiffComplexStructure

end
