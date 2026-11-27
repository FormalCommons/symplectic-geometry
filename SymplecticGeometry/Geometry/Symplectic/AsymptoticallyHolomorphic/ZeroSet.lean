/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.VectorBundle.ZeroSet.Embedding
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.ZeroSet.NormalSpace
public import SymplecticGeometry.Geometry.Manifold.Orientation.NormalOrientation
public import TauCeti.Geometry.Symplectic.Manifold.Volume
public import TauCeti.Topology.VectorBundle.Orientation.Complex.Basic
public import TauCeti.Geometry.Symplectic.Lagrangian.Embedding.Symplectic.Basic
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.CompatibleMetric
import SymplecticGeometry.Geometry.Manifold.VectorBundle.CovariantDerivative.Linearization
import SymplecticGeometry.Geometry.Symplectic.Manifold.TwoForm
import SymplecticGeometry.LinearAlgebra.Complex.DominantLinearPart

/-!
# Transverse symplectic zero sets

Let `σ` be a smooth two-form on `M` compatible with a smooth almost complex structure `J`, with
metric `g_J(u, v) = σ(u, J v)` (Tau Ceti's `TauCeti.SmoothTwoForm.Compatible.metric`), and let
`L → M` be a smooth real vector bundle whose fibres are complex lines with a norm. For a smooth
section `s` of `L` and a covariant derivative `D` on `L`, split `D s(x) : T_x M → L_x` into its
complex-linear part `∂s(x)` and its complex-antilinear part `∂̄s(x)`, for `J_x` and
multiplication by `i` on `L_x` (Tau Ceti's `TauCeti.complexLinearPart` and
`TauCeti.complexAntilinearPart`). If `‖∂̄s(x)‖ < ‖∂s(x)‖` at every zero `x` of `s`, operator norms
taken for `g_J` and the norm of `L_x`, then

* `s` is transverse to the zero section: its intrinsic linearization
  `TauCeti.sectionLinearization` is onto at every zero (`isTransverse_of_norm_dbar_lt`);
* its zero set, with the atlas of `SymplecticGeometry.transverseZeroSetChartedSpace`, is a
  symplectic submanifold: the inclusion `TauCeti.SmoothEmbedding.ofTransverseSection` is a
  symplectic submanifold embedding for `σ`
  (`isSymplecticSubmanifoldEmbedding_zeroSet_of_norm_dbar_lt`);
* if `L` is moreover a complex line bundle, the normal orientation of the zero set `Z` induced
  by the symplectic orientations of `M` and of `Z` (`TauCeti.SmoothEmbedding.normalOrientation`)
  is the one carried from the canonical orientation of `L` by the linearization of `s`
  (`SymplecticGeometry.normalOrientationOfSection`)
  (`normalOrientation_zeroSet_eq_normalOrientationOfSection_of_norm_dbar_lt`).

At a zero, `D s(x)` is the intrinsic linearization of `s` for every covariant derivative `D`
(`CovariantDerivative.apply_eq_sectionLinearization`), so no result asks `D` to be complex
linear or metric, and the norm of `L_x` need not come from a Hermitian metric. The pointwise
statements are `TauCeti.SymplecticForm.surjective_of_norm_complexAntilinearPart_lt`,
`TauCeti.SymplecticForm.isSymplectic_ker_of_norm_complexAntilinearPart_lt` and
`TauCeti.SymplecticForm.orientation_ker_eq_of_norm_complexAntilinearPart_lt`, applied on
`(T_x M, σ_x, J_x, g_J)`; the tangent space of the zero set at `x` is the kernel of the
linearization (`SymplecticGeometry.range_mfderiv_coe_transverseZeroSet`). The results are local:
`M` need not be compact, and `σ` need not be closed.

The orientations are compared fibre by fibre, by
`SymplecticGeometry.normalOrientation_ofTransverseSection_eq_normalOrientationOfSection_iff`: it
reduces the claim to the sequence `0 → ker → T_z M → L_z → 0` at each `z ∈ Z`, with `T_z Z`
carried onto the kernel by the differential of the inclusion
(`SymplecticGeometry.tangentSpaceEquivKerOfTransverseSection`). That map is a symplectomorphism
for the pulled-back form, so it carries the symplectic orientation of `Z` to that of the kernel,
and `TauCeti.SymplecticForm.ofExact_orientation_ker_of_norm_complexAntilinearPart_lt` concludes.
Both normal orientations put the tangent directions of `Z` first, so no sign appears, and `Z` may
have dimension zero.

## Main results

* `SymplecticGeometry.isTransverse_of_norm_dbar_lt`: the linearization of `s` is onto at its
  zeros.
* `SymplecticGeometry.isSymplecticSubmanifoldEmbedding_zeroSet_of_norm_dbar_lt`: the zero set is a
  symplectic submanifold.
* `SymplecticGeometry.normalOrientation_zeroSet_eq_normalOrientationOfSection_of_norm_dbar_lt`:
  for a complex line bundle, the normal orientation of the zero set induced by the symplectic
  orientations is the one carried from the complex orientation of `L`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §7.4.
* [S. K. Donaldson, *Symplectic submanifolds and almost-complex geometry*][Donaldson1996].
-/

public section

noncomputable section

open Bundle Function Module
open scoped Manifold ContDiff

namespace SymplecticGeometry

open TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {L : M → Type*} [TopologicalSpace (TotalSpace F L)] [∀ x, NormedAddCommGroup (L x)]
  [∀ x, NormedSpace ℝ (L x)] [∀ x, NormedSpace ℂ (L x)] [∀ x, IsScalarTower ℝ ℂ (L x)]
  [FiberBundle F L] [VectorBundle ℝ F L] [ContMDiffVectorBundle ∞ F L I]
  {σ : SmoothTwoForm I M} {J : SmoothAlmostComplexStructure I M} {s : Π x, L x}

/-- **Sections with dominant holomorphic derivative are transverse.** Let `σ` be compatible with
`J`, let the fibres of `L` be complex lines, and let `D` be a covariant derivative on `L`. If a
section `s`, differentiable at each of its zeros `x`, has there a complex-antilinear part of
`D s(x)` of smaller operator norm than its complex-linear part, for the metric `σ(·, J ·)` on
`T_x M`, then the intrinsic linearization of `s` is onto at each zero. -/
theorem isTransverse_of_norm_dbar_lt (hc : σ.Compatible J) (hL : ∀ x, finrank ℂ (L x) = 1)
    (D : CovariantDerivative I F L)
    (hs : ∀ x, s x = 0 →
      MDifferentiableAt I (I.prod 𝓘(ℝ, F)) (fun x ↦ TotalSpace.mk' F x (s x)) x)
    (hdom : ∀ x, s x = 0 →
      letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨hc.metric.toRiemannianMetric⟩
      ‖LinearMap.toContinuousLinearMap (complexAntilinearPart
          (J.almostComplexStructureAt x).toLinearMap
          (AlmostComplexStructure.ofComplexModule (L x)).toLinearMap
          (D s x : TangentSpace I x →ₗ[ℝ] L x))‖ <
        ‖LinearMap.toContinuousLinearMap (complexLinearPart
          (J.almostComplexStructureAt x).toLinearMap
          (AlmostComplexStructure.ofComplexModule (L x)).toLinearMap
          (D s x : TangentSpace I x →ₗ[ℝ] L x))‖) :
    ∀ x, s x = 0 → Surjective (sectionLinearization (F := F) I _root_.id s x) := by
  intro x hx
  let : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨hc.metric.toRiemannianMetric⟩
  rw [← D.apply_eq_sectionLinearization (hs x hx) hx]
  exact SymplecticForm.surjective_of_norm_complexAntilinearPart_lt
    («ω» := hc.tames.isNondegenerate.symplecticFormAt x) (J := J.almostComplexStructureAt x)
    (fun v w ↦ by simp [hc.inner_eq_eval₂ x v w]) (hL x) (hdom x hx)

/-- **Zero sets of sections with dominant holomorphic derivative are symplectic.** Let `σ` be
compatible with `J`, let the fibres of `L` be complex lines, and let `D` be a covariant derivative
on `L`. If a smooth section `s` has, at each of its zeros `x`, a complex-antilinear part of
`D s(x)` of smaller operator norm than its complex-linear part, for the metric `σ(·, J ·)` on
`T_x M`, then `s` is transverse (`isTransverse_of_norm_dbar_lt`), and the inclusion of its zero
set, modelled on a space `E'` of dimension `dim E - dim F`, is a symplectic submanifold embedding
for `σ`. -/
theorem isSymplecticSubmanifoldEmbedding_zeroSet_of_norm_dbar_lt [I.Boundaryless]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    (hc : σ.Compatible J) (hL : ∀ x, finrank ℂ (L x) = 1) (D : CovariantDerivative I F L)
    (hs : ContMDiff I (I.prod 𝓘(ℝ, F)) ∞ fun x ↦ TotalSpace.mk' F x (s x))
    (hdom : ∀ x, s x = 0 →
      letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨hc.metric.toRiemannianMetric⟩
      ‖LinearMap.toContinuousLinearMap (complexAntilinearPart
          (J.almostComplexStructureAt x).toLinearMap
          (AlmostComplexStructure.ofComplexModule (L x)).toLinearMap
          (D s x : TangentSpace I x →ₗ[ℝ] L x))‖ <
        ‖LinearMap.toContinuousLinearMap (complexLinearPart
          (J.almostComplexStructureAt x).toLinearMap
          (AlmostComplexStructure.ofComplexModule (L x)).toLinearMap
          (D s x : TangentSpace I x →ₗ[ℝ] L x))‖)
    (hE : finrank ℝ E' + finrank ℝ F = finrank ℝ E) :
    letI := transverseZeroSetChartedSpace (by simp) hs
      (isTransverse_of_norm_dbar_lt hc hL D
        (fun x _ ↦ (hs x).mdifferentiableAt (by simp)) hdom) hE
    hc.tames.isNondegenerate.IsSymplecticSubmanifoldEmbedding 𝓘(ℝ, E')
      (SmoothEmbedding.ofTransverseSection (by simp) hs
        (isTransverse_of_norm_dbar_lt hc hL D
          (fun x _ ↦ (hs x).mdifferentiableAt (by simp)) hdom) hE) := by
  let := transverseZeroSetChartedSpace (by simp) hs
    (isTransverse_of_norm_dbar_lt hc hL D
      (fun x _ ↦ (hs x).mdifferentiableAt (by simp)) hdom) hE
  refine (SmoothTwoForm.IsNondegenerate.isSymplecticSubmanifoldEmbedding_iff_of_isSmoothEmbedding
    (SmoothEmbedding.isSmoothEmbedding _)).2
    (SmoothTwoForm.IsNondegenerate.hasSymplecticTangentImages_iff_forall.2 fun z ↦ ?_)
  let : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨hc.metric.toRiemannianMetric⟩
  have hrange := range_mfderiv_coe_transverseZeroSet (by simp) hs
    (isTransverse_of_norm_dbar_lt hc hL D
      (fun x _ ↦ (hs x).mdifferentiableAt (by simp)) hdom) hE z
  rw [← D.apply_eq_sectionLinearization ((hs z).mdifferentiableAt (by simp)) z.property] at hrange
  have hk := SymplecticForm.isSymplectic_ker_of_norm_complexAntilinearPart_lt
    («ω» := hc.tames.isNondegenerate.symplecticFormAt z) (J := J.almostComplexStructureAt z)
    (fun v w ↦ by simp [hc.inner_eq_eval₂ z v w]) (hL z) (hdom z z.property)
  rw [SmoothEmbedding.coe_ofTransverseSection]
  exact hrange ▸ hk

section Orientation

/-! ### The normal orientation of the zero set -/

open scoped InnerProductSpace

variable [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F] [FiniteDimensional ℂ F] [VectorBundle ℂ F L]

/-- **The normal orientation of a symplectic zero set.** In the setting of
`isSymplecticSubmanifoldEmbedding_zeroSet_of_norm_dbar_lt`, let `L` moreover be a complex line
bundle. Orient `M` by the symplectic orientation of `σ` and the zero set `Z` of `s`, of dimension
`2 k`, by the symplectic orientation of the pull-back of `σ`. The normal orientation of `Z` that
these induce (`TauCeti.SmoothEmbedding.normalOrientation`, the tangent directions first) is the
orientation `SymplecticGeometry.normalOrientationOfSection` carried from the canonical
orientation `TauCeti.VectorBundleOrientation.complex` of `L` by the linearization of `s`. -/
theorem normalOrientation_zeroSet_eq_normalOrientationOfSection_of_norm_dbar_lt [I.Boundaryless]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    (hc : σ.Compatible J) (hF : finrank ℂ F = 1) (D : CovariantDerivative I F L)
    (hs : ContMDiff I (I.prod 𝓘(ℝ, F)) ∞ fun x ↦ TotalSpace.mk' F x (s x))
    (hdom : ∀ x, s x = 0 →
      letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨hc.metric.toRiemannianMetric⟩
      ‖LinearMap.toContinuousLinearMap (complexAntilinearPart
          (J.almostComplexStructureAt x).toLinearMap
          (AlmostComplexStructure.ofComplexModule (L x)).toLinearMap
          (D s x : TangentSpace I x →ₗ[ℝ] L x))‖ <
        ‖LinearMap.toContinuousLinearMap (complexLinearPart
          (J.almostComplexStructureAt x).toLinearMap
          (AlmostComplexStructure.ofComplexModule (L x)).toLinearMap
          (D s x : TangentSpace I x →ₗ[ℝ] L x))‖)
    (hE : finrank ℝ E' + finrank ℝ F = finrank ℝ E) {k : ℕ} (hk : finrank ℝ E' = 2 * k) :
    letI := transverseZeroSetChartedSpace (by simp) hs
      (isTransverse_of_norm_dbar_lt hc (fun x ↦ (VectorBundle.finrank_eq ℂ F L x).trans hF) D
        (fun x _ ↦ (hs x).mdifferentiableAt (by simp)) hdom) hE
    haveI := isManifold_transverseZeroSet (by simp) hs
      (isTransverse_of_norm_dbar_lt hc (fun x ↦ (VectorBundle.finrank_eq ℂ F L x).trans hF) D
        (fun x _ ↦ (hs x).mdifferentiableAt (by simp)) hdom) hE
    letI := (SmoothEmbedding.ofTransverseSection (by simp) hs
      (isTransverse_of_norm_dbar_lt hc (fun x ↦ (VectorBundle.finrank_eq ℂ F L x).trans hF) D
        (fun x _ ↦ (hs x).mdifferentiableAt (by simp)) hdom) hE).normalSpaceFiberBundle (P := F)
      (by simp) (Nat.eq_sub_of_add_eq' hE)
    letI := (SmoothEmbedding.ofTransverseSection (by simp) hs
      (isTransverse_of_norm_dbar_lt hc (fun x ↦ (VectorBundle.finrank_eq ℂ F L x).trans hF) D
        (fun x _ ↦ (hs x).mdifferentiableAt (by simp)) hdom) hE).normalSpaceVectorBundle (P := F)
      (by simp) (Nat.eq_sub_of_add_eq' hE)
    (SmoothEmbedding.ofTransverseSection (by simp) hs
      (isTransverse_of_norm_dbar_lt hc (fun x ↦ (VectorBundle.finrank_eq ℂ F L x).trans hF) D
        (fun x _ ↦ (hs x).mdifferentiableAt (by simp)) hdom) hE).normalOrientation (by simp)
        (Nat.eq_sub_of_add_eq' hE)
        ((hc.tames.isNondegenerate.volumeOrientation (n := k + 1)
          (by rw [← hE, hk, finrank_real_eq_two_mul_finrank_complex, hF]; ring)).reindex
            (finCongr (by rw [finrank_real_eq_two_mul_finrank_complex, hF]; ring)))
        ((isSymplecticSubmanifoldEmbedding_zeroSet_of_norm_dbar_lt hc
          (fun x ↦ (VectorBundle.finrank_eq ℂ F L x).trans hF) D hs hdom
            hE).isNondegenerate_mpullback.volumeOrientation hk) =
      normalOrientationOfSection (by simp) hs
        (isTransverse_of_norm_dbar_lt hc (fun x ↦ (VectorBundle.finrank_eq ℂ F L x).trans hF) D
          (fun x _ ↦ (hs x).mdifferentiableAt (by simp)) hdom) hE (Fintype.card_fin _)
        (VectorBundleOrientation.reindex
          (finCongr (finrank_real_eq_two_mul_finrank_complex (V := F)).symm)
          (VectorBundleOrientation.complex F L)) := by
  have hL : ∀ x, finrank ℂ (L x) = 1 := fun x ↦ (VectorBundle.finrank_eq ℂ F L x).trans hF
  have hT := isTransverse_of_norm_dbar_lt hc hL D (fun x _ ↦ (hs x).mdifferentiableAt (by simp))
    hdom
  have hm : (∞ : ℕ∞ω) ≠ 0 := by simp
  let := transverseZeroSetChartedSpace hm hs hT hE
  have := isManifold_transverseZeroSet hm hs hT hE
  rw [normalOrientation_ofTransverseSection_eq_normalOrientationOfSection_iff hm hs hT hE hk]
  intro z
  have hv := coe_tangentSpaceEquivKerOfTransverseSection hm hs hT hE z
  set f := SmoothEmbedding.ofTransverseSection hm hs hT hE
  have hz0 : s (f z) = 0 := SmoothEmbedding.ofTransverseSection_apply_eq_zero hm hs hT hE z
  let : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨hc.metric.toRiemannianMetric⟩
  have hd := hdom (f z) hz0
  rw [D.apply_eq_sectionLinearization ((hs (f z)).mdifferentiableAt (by simp)) hz0] at hd
  have hg : ∀ v w, hc.tames.isNondegenerate.symplecticFormAt (f z) v
      (J.almostComplexStructureAt (f z) w) = ⟪v, w⟫_ℝ := fun v w ↦ by
    simp [hc.inner_eq_eval₂ (f z) v w]
  rw [VectorBundleOrientation.reindex_apply, VectorBundleOrientation.complex_apply,
    Manifold.Orientation.orientationAt_reindex,
    SmoothTwoForm.IsNondegenerate.orientationAt_volumeOrientation,
    SmoothTwoForm.IsNondegenerate.orientationAt_volumeOrientation]
  refine Eq.trans ?_ ((SymplecticForm.ofExact_orientation_ker_of_norm_complexAntilinearPart_lt hg
    (hL (f z)) hd (by rw [← hk]; exact hE.symm)
    ((tangentSpaceEquivKerOfTransverseSection hm hs hT hE z).finrank_eq.symm.trans hk)
    (VectorBundle.finrank_eq ℝ F L _)).trans (SymplecticForm.reindex_orientation _ _ _).symm)
  congr 1
  · -- The differential of the inclusion is a symplectomorphism onto the kernel.
    refine SymplecticForm.IsSymplectomorphism.map_orientation
      (SymplecticForm.isSymplectomorphism_iff.2 fun v w ↦ ?_) hk
    exact (SymplecticForm.restrict_apply _ _ _ _ _).trans
      ((congrArg₂ (fun a b ↦ hc.tames.isNondegenerate.symplecticFormAt (f z) a b) (hv v)
        (hv w)).trans
      ((hc.tames.isNondegenerate.symplecticFormAt_mfderiv_mfderiv _ z v w).trans
        ((SmoothForm.bilinFormAt_apply _ z v w).trans
          (SmoothTwoForm.IsNondegenerate.symplecticFormAt_apply _ z v w).symm)))
  · -- The two `finCongr` reindexings compose to the one on the right, by definition.
    exact (Orientation.reindex_trans _ _ _).symm

end Orientation

end SymplecticGeometry
