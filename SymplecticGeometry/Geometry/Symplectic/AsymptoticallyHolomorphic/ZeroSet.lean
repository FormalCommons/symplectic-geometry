/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.VectorBundle.CovariantDerivative.Linearization
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.ZeroSet.Embedding
public import SymplecticGeometry.LinearAlgebra.Complex.DominantLinearPart
public import TauCeti.Geometry.Symplectic.Lagrangian.Embedding.Symplectic.Basic
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.CompatibleMetric

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
  (`isSymplecticSubmanifoldEmbedding_zeroSet_of_norm_dbar_lt`).

At a zero, `D s(x)` is the intrinsic linearization of `s` for every covariant derivative `D`
(`CovariantDerivative.apply_eq_sectionLinearization`), so neither result asks `D` to be complex
linear or metric, and the norm of `L_x` need not come from a Hermitian metric. The pointwise
statements are `TauCeti.SymplecticForm.surjective_of_norm_complexAntilinearPart_lt` and
`TauCeti.SymplecticForm.isSymplectic_ker_of_norm_complexAntilinearPart_lt`, applied on
`(T_x M, σ_x, J_x, g_J)`; the tangent space of the zero set at `x` is the kernel of the
linearization (`SymplecticGeometry.range_mfderiv_coe_transverseZeroSet`). Both results are local:
`M` need not be compact, and `σ` need not be closed.

## Main results

* `SymplecticGeometry.isTransverse_of_norm_dbar_lt`: the linearization of `s` is onto at its
  zeros.
* `SymplecticGeometry.isSymplecticSubmanifoldEmbedding_zeroSet_of_norm_dbar_lt`: the zero set is a
  symplectic submanifold.

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
smooth section `s` has, at each of its zeros `x`, a complex-antilinear part of `D s(x)` of smaller
operator norm than its complex-linear part, for the metric `σ(·, J ·)` on `T_x M`, then the
intrinsic linearization of `s` is onto at each zero. -/
theorem isTransverse_of_norm_dbar_lt (hc : σ.Compatible J) (hL : ∀ x, finrank ℂ (L x) = 1)
    (D : CovariantDerivative I F L)
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
          (D s x : TangentSpace I x →ₗ[ℝ] L x))‖) :
    ∀ x, s x = 0 → Surjective (sectionLinearization (F := F) I _root_.id s x) := by
  intro x hx
  let : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨hc.metric.toRiemannianMetric⟩
  rw [← D.apply_eq_sectionLinearization ((hs x).mdifferentiableAt (by simp)) hx]
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
      (isTransverse_of_norm_dbar_lt hc hL D hs hdom) hE
    hc.tames.isNondegenerate.IsSymplecticSubmanifoldEmbedding 𝓘(ℝ, E')
      (SmoothEmbedding.ofTransverseSection (by simp) hs
        (isTransverse_of_norm_dbar_lt hc hL D hs hdom) hE) := by
  let := transverseZeroSetChartedSpace (by simp) hs
    (isTransverse_of_norm_dbar_lt hc hL D hs hdom) hE
  refine (SmoothTwoForm.IsNondegenerate.isSymplecticSubmanifoldEmbedding_iff_of_isSmoothEmbedding
    (SmoothEmbedding.isSmoothEmbedding _)).2
    (SmoothTwoForm.IsNondegenerate.hasSymplecticTangentImages_iff_forall.2 fun z ↦ ?_)
  let : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨hc.metric.toRiemannianMetric⟩
  have hrange := range_mfderiv_coe_transverseZeroSet (by simp) hs
    (isTransverse_of_norm_dbar_lt hc hL D hs hdom) hE z
  rw [← D.apply_eq_sectionLinearization ((hs z).mdifferentiableAt (by simp)) z.property] at hrange
  have hk := SymplecticForm.isSymplectic_ker_of_norm_complexAntilinearPart_lt
    («ω» := hc.tames.isNondegenerate.symplecticFormAt z) (J := J.almostComplexStructureAt z)
    (fun v w ↦ by simp [hc.inner_eq_eval₂ z v w]) (hL z) (hdom z z.property)
  rw [SmoothEmbedding.coe_ofTransverseSection]
  exact hrange ▸ hk

end SymplecticGeometry
