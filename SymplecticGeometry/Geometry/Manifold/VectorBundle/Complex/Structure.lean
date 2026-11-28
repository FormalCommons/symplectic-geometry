/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.VectorBundle.ComplexStructure
public import SymplecticGeometry.Topology.VectorBundle.Complex.RestrictScalars
public import SymplecticGeometry.Topology.VectorBundle.Complex.Structure
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import all TauCeti.Topology.VectorBundle.Complex.Structure
import TauCeti.Geometry.Manifold.ContMDiff.ContinuousLinearEquiv
import TauCeti.Geometry.Manifold.VectorBundle.Hom.Basic
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-!
# The complex bundle of a smooth complex structure is smooth

Let `V` be a `Cⁿ` real vector bundle with finite-dimensional model fibre `F` over a manifold `M`,
and `J` a `Cⁿ` complex structure on `V`
(`SymplecticGeometry.Bundle.ContMDiffComplexStructure I n F V`). For a complex model `G` of half
the real dimension of `F`, Tau Ceti makes `J.toContinuousComplexStructure.Fiber`, which is `V`
with `J` as multiplication by `i`, a complex vector bundle with model fibre `G`
(`TauCeti.Bundle.ContinuousComplexStructure.vectorPrebundle`). This file shows that its
underlying real vector bundle (the scoped instance `VectorBundle.ComplexToReal.vectorBundle`) is
a `Cⁿ` vector bundle, and that the identification
`TauCeti.Bundle.ContinuousComplexStructure.totalSpaceHomeomorph` of its total space with that of
`V` is `Cⁿ` in both directions.

Write `K` for `J.toContinuousComplexStructure`. Over the base set of the trivialization of `V` at
`b₀`, the operators `K.coord b₀ b` that read `J b` in that trivialization depend `Cⁿ` on `b`,
since `J` is a `Cⁿ` section of the endomorphism bundle; hence so do the complex-linear parts
`K.complexLinearPart b₀ b` and, where these are invertible, their inverses. The coordinate
changes of the complex trivializations of `K.Fiber` are built from these and from the coordinate
changes of `V`, which gives the smoothness of the bundle. These proofs are the `Cⁿ` versions of
Tau Ceti's proofs of `TauCeti.Bundle.ContinuousComplexStructure.continuousOn_coord`,
`continuousOn_complexLinearPart`, `continuousOn_inverse_complexLinearPart` and
`continuousOn_realCoordChange` in `TauCeti/Topology/VectorBundle/Complex/Structure.lean`; the
smoothness of the inverses comes from Tau Ceti's `ContMDiffOn.clm_inverse`. The
smoothness of the identification of total spaces then follows from Tau Ceti's
`TauCeti.contMDiff_hom_bundle_iff` and `TauCeti.contMDiff_bundle_symm`, and that of the
identification along a pull-back from Tau Ceti's `Bundle.Pullback.contMDiff_iff`, as in the proof
of `SymplecticGeometry.Bundle.ContMDiffComplexStructure.continuous_pullbackFiberEquiv`.

The file imports all of Tau Ceti's `TauCeti.Topology.VectorBundle.Complex.Structure`: the atlas of
the complex trivializations, in the body of `vectorPrebundle`, is not exposed, and the coordinate
changes are Tau Ceti's private `realCoordChange`, which is used here rather than restated.

## Main results

* `SymplecticGeometry.Bundle.ContMDiffComplexStructure.contMDiffOn_coord`,
  `contMDiffOn_complexLinearPart`, `contMDiffOn_inverse_complexLinearPart`: smoothness of `J`
  read in a trivialization of `V`, of its complex-linear parts, and of their inverses.
* `SymplecticGeometry.Bundle.ContMDiffComplexStructure.contMDiffVectorBundle`: the complex bundle
  of `J` is a `Cⁿ` real vector bundle.
* `SymplecticGeometry.Bundle.ContMDiffComplexStructure.contMDiff_fiberEquiv`: the identity of the
  fibres, from the complex bundle to `V`, is a `Cⁿ` section of the bundle of real linear maps.
* `SymplecticGeometry.Bundle.ContMDiffComplexStructure.contMDiff_totalSpaceHomeomorph`,
  `contMDiff_totalSpaceHomeomorph_symm`: the identification of its total space with that of `V`
  is `Cⁿ` in both directions.
* `SymplecticGeometry.Bundle.ContMDiffComplexStructure.contMDiff_pullbackFiberEquiv`: along a
  `Cⁿ` map, the identification of the complex bundle of the pull-back of `J` with the pull-back
  of the complex bundle of `J` is `Cⁿ` on total spaces.
* `SymplecticGeometry.Bundle.ContMDiffComplexStructure.contMDiff_fiberEquivOfCommute`: a `Cⁿ`
  isomorphism of real bundles that carries `J` to a second `Cⁿ` complex structure is `Cⁿ` as an
  isomorphism of their complex bundles.

## References

* J. W. Milnor and J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §§3 and 14
-/

public section

noncomputable section

open _root_.Bundle Set Module Topology
open scoped ContDiff Manifold VectorBundle.ComplexToReal

namespace SymplecticGeometry.Bundle.ContMDiffComplexStructure

variable {EB HB M : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [TopologicalSpace HB] {I : ModelWithCorners ℝ EB HB}
  [TopologicalSpace M] [ChartedSpace HB M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V] {n : ℕ∞} [ContMDiffVectorBundle n F V I]
  (J : ContMDiffComplexStructure I n F V)

/-! ### `J` in the trivializations of `V` -/

/-- Read in the trivialization of `V` at `b₀`, the complex structure `J` is `Cⁿ` on the base set
of that trivialization. -/
theorem contMDiffOn_coord (b₀ : M) :
    ContMDiffOn I 𝓘(ℝ, F →L[ℝ] F) n (J.toContinuousComplexStructure.coord b₀)
      (trivializationAt F V b₀).baseSet := by
  have h := (Trivialization.contMDiffOn_section_iff
    (trivializationAt (F →L[ℝ] F) (fun x ↦ V x →L[ℝ] V x) b₀)
    (trivializationAt (F →L[ℝ] F) (fun x ↦ V x →L[ℝ] V x) b₀).open_baseSet subset_rfl).1
    J.toEndomorphism.contMDiff.contMDiffOn
  rw [hom_trivializationAt_baseSet, inter_self] at h
  refine h.congr fun b hb ↦ ContinuousLinearMap.ext fun w ↦ ?_
  -- Both sides are `J b` transported by the trivialization of `V` at `b₀`.
  rw [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates,
    ← (trivializationAt F V b₀).continuousLinearMapAt_symmL (R := ℝ) hb w,
    J.toContinuousComplexStructure.coord_apply hb]
  simp [Trivialization.continuousLinearMapAt_symmL _ hb]

/-- The complex-linear parts `J.toContinuousComplexStructure.complexLinearPart b₀ b` depend `Cⁿ`
on `b` over the base set of the trivialization of `V` at `b₀`. -/
theorem contMDiffOn_complexLinearPart (b₀ : M) :
    ContMDiffOn I 𝓘(ℝ, F →L[ℝ] F) n (J.toContinuousComplexStructure.complexLinearPart b₀)
      (trivializationAt F V b₀).baseSet := by
  have h := ((2⁻¹ : ℝ) • ContinuousLinearMap.id ℝ (F →L[ℝ] F)).contMDiff.comp_contMDiffOn
    ((contMDiffOn_const (c := ContinuousLinearMap.id ℝ F)).sub
      ((J.contMDiffOn_coord b₀).clm_comp
        (contMDiffOn_const (c := J.toContinuousComplexStructure.coord b₀ b₀))))
  exact h.congr fun b _ ↦ ContinuousLinearMap.ext fun w ↦ by
    simp [TauCeti.Bundle.ContinuousComplexStructure.complexLinearPart_apply]

/-- Where the complex-linear parts `J.toContinuousComplexStructure.complexLinearPart b₀ b` are
invertible, their inverses depend `Cⁿ` on `b`. -/
theorem contMDiffOn_inverse_complexLinearPart [CompleteSpace F] (b₀ : M) :
    ContMDiffOn I 𝓘(ℝ, F →L[ℝ] F) n
      (fun b ↦ Ring.inverse (J.toContinuousComplexStructure.complexLinearPart b₀ b))
      (J.toContinuousComplexStructure.unitSet b₀) := by
  simp_rw [ContinuousLinearMap.ringInverse_eq_inverse]
  exact ((J.contMDiffOn_complexLinearPart b₀).mono
    (J.toContinuousComplexStructure.unitSet_subset b₀)).clm_inverse
      fun b hb ↦ ContinuousLinearMap.isInvertible_iff_isUnit.2 hb.2

/-! ### The complex bundle -/

variable [FiniteDimensional ℝ F]

variable (G : Type*) [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G]
  [Fact (finrank ℝ F = 2 * finrank ℂ G)]

/-- The coordinate changes of the complex trivializations of
`J.toContinuousComplexStructure.Fiber`, as real linear maps, are `Cⁿ` on the overlaps of their
base sets. -/
private theorem contMDiffOn_realCoordChange (b₀ b₁ : M) :
    ContMDiffOn I 𝓘(ℝ, G →L[ℝ] G) n
      (J.toContinuousComplexStructure.realCoordChange G b₀ b₁)
      (J.toContinuousComplexStructure.unitSet b₀ ∩
        J.toContinuousComplexStructure.unitSet b₁) := by
  have := FiniteDimensional.completeSpace ℝ F
  set K := J.toContinuousComplexStructure
  have hsub : K.unitSet b₀ ∩ K.unitSet b₁ ⊆
      (trivializationAt F V b₀).baseSet ∩ (trivializationAt F V b₁).baseSet :=
    inter_subset_inter (K.unitSet_subset b₀) (K.unitSet_subset b₁)
  exact contMDiffOn_const.clm_comp
    (((J.contMDiffOn_inverse_complexLinearPart b₁).mono inter_subset_right).clm_comp
      (((contMDiffOn_coordChangeL (IB := I) (n := n) (trivializationAt F V b₀)
        (trivializationAt F V b₁)).mono hsub).clm_comp
        ((((J.contMDiffOn_complexLinearPart b₀).mono (K.unitSet_subset b₀)).mono
          inter_subset_left).clm_comp contMDiffOn_const)))

/-- The complex bundle `J.toContinuousComplexStructure.Fiber` of a `Cⁿ` complex structure, as a
real vector bundle, is a `Cⁿ` vector bundle. -/
instance contMDiffVectorBundle :
    ContMDiffVectorBundle n G J.toContinuousComplexStructure.Fiber I where
  contMDiffOn_coordChangeL := by
    rintro _ _ ⟨_, ⟨b₀, rfl⟩, rfl⟩ ⟨_, ⟨b₁, rfl⟩, rfl⟩
    -- Stated with `trivializationOfMemPretrivializationAtlas`, the goal does not find the
    -- `Trivialization.IsLinear ℝ` instance. Those trivializations are by definition
    -- `trivializationAt` at `b₀` and `b₁`, with base sets `unitSet b₀` and `unitSet b₁`.
    change ContMDiffOn I 𝓘(ℝ, G →L[ℝ] G) n
      (fun b ↦ ((trivializationAt G J.toContinuousComplexStructure.Fiber b₀).coordChangeL ℝ
        (trivializationAt G J.toContinuousComplexStructure.Fiber b₁) b : G →L[ℝ] G))
      (J.toContinuousComplexStructure.unitSet b₀ ∩ J.toContinuousComplexStructure.unitSet b₁)
    refine (J.contMDiffOn_realCoordChange G b₀ b₁).congr fun b hb ↦ ?_
    ext z
    rw [ContinuousLinearEquiv.coe_coe, Trivialization.coordChangeL_apply _ _ hb]
    exact (J.toContinuousComplexStructure.realCoordChange_apply G hb z).symm

/-- The identity of the fibres, from `J.toContinuousComplexStructure.Fiber` to `V`, is a `Cⁿ`
section of the bundle of real linear maps between them. -/
theorem contMDiff_fiberEquiv :
    ContMDiff I (I.prod 𝓘(ℝ, G →L[ℝ] F)) n fun x ↦ TotalSpace.mk' (G →L[ℝ] F)
      (E := fun x ↦ J.toContinuousComplexStructure.Fiber x →L[ℝ] V x)
        x (J.toContinuousComplexStructure.fiberEquiv x : _ →L[ℝ] V x) := by
  set K := J.toContinuousComplexStructure
  have := FiniteDimensional.completeSpace ℝ F
  intro x₀
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  -- Near `x₀`, the section read in the trivializations at `x₀` is
  -- `K.complexLinearPart x₀ x ∘ K.modelEquiv G x₀`.
  have hU : K.unitSet x₀ ∈ 𝓝 x₀ := (K.isOpen_unitSet x₀).mem_nhds (K.mem_unitSet_self x₀)
  have h := ((J.contMDiffOn_complexLinearPart x₀).contMDiffAt
    ((trivializationAt F V x₀).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt F V x₀))).clm_comp
      (contMDiffAt_const (c := (K.modelEquiv G x₀ : G →L[ℝ] F)))
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [hU] with x hx
  ext z
  have hx' : x ∈ (trivializationAt G K.Fiber x₀).baseSet := by
    rwa [K.baseSet_trivializationAt G]
  simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, Trivialization.symmL_apply _ hx',
    K.trivializationAt_symm_apply G hx]
  rw [← Trivialization.symmL_apply (R := ℝ) _ (K.unitSet_subset x₀ hx),
    Trivialization.continuousLinearMapAt_symmL _ (K.unitSet_subset x₀ hx)]

/-- The identification `TauCeti.Bundle.ContinuousComplexStructure.totalSpaceHomeomorph` of the
total space of the complex bundle of a `Cⁿ` complex structure with that of `V` is `Cⁿ`. -/
theorem contMDiff_totalSpaceHomeomorph :
    ContMDiff (I.prod 𝓘(ℝ, G)) (I.prod 𝓘(ℝ, F)) n
      (J.toContinuousComplexStructure.totalSpaceHomeomorph G) := by
  have := (TauCeti.contMDiff_hom_bundle_iff _).1 (J.contMDiff_fiberEquiv G)
  exact this.congr fun p ↦ by simp

/-- The inverse of the identification
`TauCeti.Bundle.ContinuousComplexStructure.totalSpaceHomeomorph` of the total space of the complex
bundle of a `Cⁿ` complex structure with that of `V` is `Cⁿ`. -/
theorem contMDiff_totalSpaceHomeomorph_symm :
    ContMDiff (I.prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, G)) n
      (J.toContinuousComplexStructure.totalSpaceHomeomorph G).symm := by
  have := TauCeti.contMDiff_bundle_symm J.toContinuousComplexStructure.fiberEquiv
    (((TauCeti.contMDiff_hom_bundle_iff _).1 (J.contMDiff_fiberEquiv G)).congr fun _ ↦ by
      simp only [ContinuousLinearEquiv.coe_coe])
  exact this.congr fun p ↦ by simp

omit J in
/-- Along a `Cⁿ` map `f : N → M`, the identification
`SymplecticGeometry.Bundle.ContMDiffComplexStructure.pullbackFiberEquiv` of the complex bundle of
`J.pullback f hf` with the pull-back of the complex bundle of `J` is `Cⁿ` on total spaces. -/
theorem contMDiff_pullbackFiberEquiv {EN HN N : Type*} [NormedAddCommGroup EN]
    [NormedSpace ℝ EN] [TopologicalSpace HN] {I' : ModelWithCorners ℝ EN HN} [TopologicalSpace N]
    [ChartedSpace HN N] {K : Type*} [FunLike K N M] [ContinuousMapClass K N M]
    (J : ContMDiffComplexStructure I n F V) (f : K) (hf : ContMDiff I' I n f) :
    ContMDiff (I'.prod 𝓘(ℝ, G)) (I'.prod 𝓘(ℝ, G)) n
      fun p : TotalSpace G (J.pullback f hf).toContinuousComplexStructure.Fiber ↦
        TotalSpace.mk' G (E := (f : N → M) *ᵖ J.toContinuousComplexStructure.Fiber) p.proj
          (J.pullbackFiberEquiv f hf p.proj p.snd) := by
  have := Pullback.contMDiffVectorBundle (F := F) (E := V) hf
  refine (Pullback.contMDiff_iff f hf).2 ⟨contMDiff_proj _,
    ((J.contMDiff_totalSpaceHomeomorph_symm G).comp ((Pullback.contMDiff_lift f hf).comp
      ((J.pullback f hf).contMDiff_totalSpaceHomeomorph G))).congr fun p ↦ ?_⟩
  simp [pullbackFiberEquiv_apply]
  -- `rfl` identifies the base point `(Pullback.lift f ⟨p.proj, _⟩).proj` with `f p.proj`.
  rfl

/-- **A smooth isomorphism that carries `J` to `J'` is a smooth isomorphism of complex bundles.**
Let `J` and `J'` be `Cⁿ` complex structures on `V` and on a second `Cⁿ` real vector bundle `V'`,
with complex models `G` and `G'`. If real-linear isomorphisms `Φ x : V x ≃ V' x` that carry `J`
to `J'` are `Cⁿ` on total spaces, then so are the complex-linear isomorphisms
`TauCeti.Bundle.ContinuousComplexStructure.fiberEquivOfCommute` that they give from the complex
bundle of `J` to that of `J'`. -/
theorem contMDiff_fiberEquivOfCommute {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
    [FiniteDimensional ℝ F'] {V' : M → Type*} [∀ x, AddCommGroup (V' x)] [∀ x, Module ℝ (V' x)]
    [∀ x, TopologicalSpace (V' x)] [∀ x, IsTopologicalAddGroup (V' x)]
    [∀ x, ContinuousSMul ℝ (V' x)] [TopologicalSpace (TotalSpace F' V')]
    [FiberBundle F' V'] [VectorBundle ℝ F' V'] [ContMDiffVectorBundle n F' V' I]
    (J' : ContMDiffComplexStructure I n F' V')
    (G' : Type*) [NormedAddCommGroup G'] [NormedSpace ℂ G'] [FiniteDimensional ℂ G']
    [Fact (finrank ℝ F' = 2 * finrank ℂ G')] (Φ : ∀ x, V x ≃L[ℝ] V' x)
    (hΦ : ContMDiff (I.prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, F')) n
      (fun p : TotalSpace F V ↦ TotalSpace.mk' F' p.proj (Φ p.proj p.snd)))
    (hJ : ∀ x v, Φ x (J.toContinuousComplexStructure x v) =
      J'.toContinuousComplexStructure x (Φ x v)) :
    ContMDiff (I.prod 𝓘(ℝ, G)) (I.prod 𝓘(ℝ, G')) n
      fun p : TotalSpace G J.toContinuousComplexStructure.Fiber ↦
        TotalSpace.mk' G' p.proj (J.toContinuousComplexStructure.fiberEquivOfCommute
          J'.toContinuousComplexStructure Φ hJ p.proj p.snd) :=
  ((J'.contMDiff_totalSpaceHomeomorph_symm G').comp
    (hΦ.comp (J.contMDiff_totalSpaceHomeomorph G))).congr fun p ↦ by
      rw [Function.comp_apply, Function.comp_apply,
        TauCeti.Bundle.ContinuousComplexStructure.totalSpaceHomeomorph_apply,
        TauCeti.Bundle.ContinuousComplexStructure.totalSpaceHomeomorph_symm_apply,
        TauCeti.Bundle.ContinuousComplexStructure.fiberEquivOfCommute_apply]

end SymplecticGeometry.Bundle.ContMDiffComplexStructure

end
