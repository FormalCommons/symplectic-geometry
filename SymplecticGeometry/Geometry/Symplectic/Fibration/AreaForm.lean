/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.FiberBundle.StructureGroup
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.TopForm
public import TauCeti.Geometry.Manifold.Orientation.Preserving
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import TauCeti.Geometry.Manifold.TwoForm.Basic
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Integration.Positivity
import SymplecticGeometry.Geometry.Manifold.FiberBundle.MapFiber
import SymplecticGeometry.Geometry.Manifold.FiberBundle.RestrictsTo
import SymplecticGeometry.Geometry.Manifold.Orientation.PositiveForm
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.ChangeOfVariables
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Regularity

/-!
# Area forms on the fibres of an oriented surface fibration

Let `A` be a smooth atlas of a map `proj : M → B` whose model fibre is a closed surface `F` with
an orientation `o`, and whose coordinate changes preserve `o`. This file builds a two-form `τ` on
`M` whose pull-back along every fibre inclusion of `A` is an area form positive for `o` with
integral one (`TauCeti.MapFiber.Atlas.exists_restricts_isPositive_area`).

The construction: a top form on `F` inducing `o`, divided by its integral, is a form `σ₀`
positive for `o` of integral one (`TauCeti.exists_smoothForm_pos_integralTopForm_eq_one`). Glue
the pull-backs of `σ₀` along the fibre coordinates of the charts with a partition of unity of the
base (`TauCeti.MapFiber.Atlas.glueForm`). On the fibre over `b'`, the glued form is the
combination, with the weights at `b'`, of the pull-backs of `σ₀` along coordinate changes
(`TauCeti.MapFiber.Atlas.mpullback_fiberInclusionMap_glueForm`). These preserve `o`, so each
pull-back is positive for `o`
(`TauCeti.Manifold.Orientation.IsOrientationPreservingAt.mpullback_apply_pos`) and has integral
one (change of variables,
`Topology.IsOpenEmbedding.integralTopForm_mpullback_of_isOrientationPreservingAt`); and the
weights are nonnegative with sum one.

## Main results

* `TauCeti.MapFiber.Atlas.exists_restricts_isPositive_area`: some two-form on `M` pulls back
  along every fibre inclusion of the atlas to a form positive for `o` with integral one.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §6.2
  (the proof of Theorem 6.2.2).
-/

public section

noncomputable section

open Bundle Set
open scoped Manifold ContDiff

namespace TauCeti.MapFiber.Atlas

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] {HB : Type*}
  [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {B : Type*} [TopologicalSpace B]
  [ChartedSpace HB B]
  {EF : Type*} [NormedAddCommGroup EF] [NormedSpace ℝ EF] [FiniteDimensional ℝ EF] {HF : Type*}
  [TopologicalSpace HF] {IF : ModelWithCorners ℝ EF HF} {F : Type*} [TopologicalSpace F]
  [ChartedSpace HF F] [IsManifold IF ∞ F]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners ℝ EM HM} {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  [IsManifold IM ∞ M]
  {proj : M → B} {A : Atlas F proj} {o : Manifold.Orientation IF F (Fin 2)}

variable [FiniteDimensional ℝ EB] [IsManifold IB ∞ B]

/-- **Area forms on the fibres.** Let `A` be a smooth atlas of `proj : M → B`, over a Hausdorff
σ-compact base modelled on a finite-dimensional space, whose model fibre is a nonempty compact
Hausdorff surface `F` with an orientation `o`, and whose coordinate changes preserve `o`. Then
some two-form `τ` on `M` pulls back along each fibre inclusion `v ↦ (A.trivAt b)⁻¹ (b', v)`, for
`b'` in the base set of `A.trivAt b`, to a form that takes a positive value on every basis with
the orientation of `o` and has integral one. -/
theorem exists_restricts_isPositive_area [T2Space B] [SigmaCompactSpace B] [T2Space F]
    [CompactSpace F] [Nonempty F] (hA : A.IsContMDiff ∞ IB IF IM)
    (hH : A.HasStructureGroup (Diffeomorph.orientationPreservingSubgroup (n := ∞) (by simp) o)) :
    ∃ τ : SmoothTwoForm IM M, ∀ b b' (hb' : b' ∈ (A.trivAt b).baseSet),
      (∀ x (c : Module.Basis (Fin 2) ℝ (TangentSpace IF x)), c.orientation = o.orientationAt x →
        0 < (SmoothForm.mpullback _ ((A.trivAt b).contMDiff_fiberInclusionMap
          (hA.contMDiffOn_trivAt_symm b) hb') τ).val x c) ∧
      integralTopForm o (SmoothForm.mpullback _ ((A.trivAt b).contMDiff_fiberInclusionMap
          (hA.contMDiffOn_trivAt_symm b) hb') τ).val = 1 := by
  obtain ⟨σ₀, hσ₀, hint⟩ := exists_smoothForm_pos_integralTopForm_eq_one o
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate IB isClosed_univ
    (fun i ↦ (A.trivAt i).baseSet) (fun i ↦ (A.trivAt i).open_baseSet)
    A.iUnion_baseSet_trivAt.ge
  refine ⟨⟨_, (isSmoothForm_glueForm hA hρ σ₀).mem_smoothBundleForms⟩, fun b b' hb' ↦ ?_⟩
  -- On the fibre over `b'`, the glued form combines the pull-backs of `σ₀` along the coordinate
  -- changes over `b'`, which are orientation-preserving diffeomorphisms `φ i`.
  have hφ : ∀ i, ∃ φ : F ≃ₘ⟮IF, IF⟯ F, i ∈ ρ.finsupport b' →
      φ ∈ Diffeomorph.orientationPreservingSubgroup (n := ∞) (by simp) o ∧
        ⇑φ = (A.trivAt b).coordChange (A.trivAt i) b' := fun i ↦ by
    by_cases hi : i ∈ ρ.finsupport b'
    · obtain ⟨φ, hφ, hφe⟩ := hasStructureGroup_iff.1 hH b i b' hb'
        (hρ i (subset_tsupport _ ((ρ.mem_finsupport b').1 hi)))
      exact ⟨φ, fun _ ↦ ⟨hφ, hφe⟩⟩
    · exact ⟨Diffeomorph.refl IF F ∞, fun h ↦ absurd h hi⟩
  choose φ hφ using hφ
  rw [SmoothForm.coe_mpullback, mpullback_fiberInclusionMap_glueForm hA hρ,
    Finset.sum_congr rfl fun i hi ↦ by rw [← (hφ i hi).2]]
  have hsum : ∑ i ∈ ρ.finsupport b', ρ i b' = 1 := ρ.sum_finsupport (x₀ := b') (mem_univ _)
  have hpos : ∀ i ∈ ρ.finsupport b', 0 < ρ i b' := fun i hi ↦
    lt_of_le_of_ne (ρ.nonneg i b') (Ne.symm ((ρ.mem_finsupport b').1 hi))
  have hop : ∀ i ∈ ρ.finsupport b', ∀ x,
      Manifold.Orientation.IsOrientationPreservingAt o o (φ i) x := fun i hi ↦
    Diffeomorph.mem_orientationPreservingSubgroup_iff.1 (hφ i hi).1
  refine ⟨fun x c hc ↦ ?_, ?_⟩
  · rw [Finset.sum_apply, ContinuousAlternatingMap.sum_apply]
    refine Finset.sum_pos (fun i hi ↦ ?_)
      (Finset.nonempty_of_sum_ne_zero (hsum.trans_ne one_ne_zero))
    rw [Pi.smul_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
    exact mul_pos (hpos i hi) ((hop i hi x).mpullback_apply_pos (fun c hc ↦ hσ₀ _ c hc) c hc)
  · have hE : Module.finrank ℝ EF = 2 := by simpa using o.card_eq.symm
    have hone : ∀ i ∈ ρ.finsupport b',
        integralTopForm o (TauCeti.mpullback IF IF (φ i) σ₀.val) = 1 := fun i hi ↦
      (Topology.IsOpenEmbedding.integralTopForm_mpullback_of_isOrientationPreservingAt
        (f := φ i) (φ i).toHomeomorph.isOpenEmbedding (hop i hi) (by simp)).trans hint
    rw [integralTopForm_sum o _ _ fun i _ ↦ ?_]
    · simp_rw [integralTopForm_smul]
      rw [Finset.sum_congr rfl fun i hi ↦ by rw [hone i hi, mul_one], hsum]
    · simpa using ((SmoothForm.mpullback (φ i) (φ i).contMDiff σ₀).isSmoothForm.smul
        (ρ i b')).integrableTopForm (isClosed_tsupport _).isCompact
        (Module.finBasisOfFinrankEq ℝ EF hE)

end TauCeti.MapFiber.Atlas

end

end
