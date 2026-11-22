/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Calculus.FDeriv.Det.Basic
public import TauCeti.Analysis.InnerProductSpace.AlternatingForm
public import TauCeti.Analysis.Matrix.Normed
public import TauCeti.Geometry.Manifold.ContMDiff.ContinuousAlternatingMap
public import TauCeti.Geometry.Manifold.ContMDiff.MFDeriv
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.ModelSpace
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
public import TauCeti.Geometry.Manifold.Riemannian.Codifferential
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.ChangeOfVariables
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.ChartGram
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.PartialDiffeomorph
import SymplecticGeometry.Analysis.Calculus.ContDiff.Matrix
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import TauCeti.Geometry.Manifold.Riemannian.FormMetric

/-!
# The metric, the Hodge star and the codifferential in a chart

Let `M` be an oriented Riemannian manifold of dimension `m` modelled on `E`, and let
`ψ : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞` be a chart with values in `E`. A form `φ` on `M` is read
in `ψ` as the flat form `mpullback 𝓘(ℝ, E) I ψ.symm φ` on `E`. This file gives the coordinate
expressions, on `ψ.target`, of the metric, of the inner product of forms, of the Hodge star and of
the codifferential.

## Main definitions

* `SymplecticGeometry.gramInChart ψ y`: the bilinear form on `E` that is the metric at `ψ.symm y`
  read through the differential of `ψ.symm`.
* `SymplecticGeometry.hodgeStarInChart o ψ hkl y`: the Hodge star of the tangent space at
  `ψ.symm y`, transported to forms on `E` through the differential of `ψ.symm`.
* `SymplecticGeometry.formInnerInChart ψ y`: the inner product of `k`-forms of the tangent space
  at `ψ.symm y`, read on the forms on `E` through the differential of `ψ`.

## Main results

* `SymplecticGeometry.contDiffOn_gramInChart`: the metric in the chart is smooth on `ψ.target`,
  and so are the entries of the inverse of its Gram matrix in a basis
  (`SymplecticGeometry.contDiffOn_inv_gramInChart_apply`), and so is the Riemannian Jacobian of
  `ψ.symm` (`PartialDiffeomorph.contDiffOn_riemannianJacobian_symm`).
* `SymplecticGeometry.gramInChart_apply_self_pos`: on `ψ.target`, the metric in the chart is
  positive on nonzero vectors.
* `SymplecticGeometry.gramInChart_trans_apply`: how the metric in the chart changes when the chart
  is followed by a partial diffeomorphism of `E`.
* `SymplecticGeometry.gramInChart_extChartPartialDiffeomorph`: for the atlas chart at `x`, its
  matrix in the basis `finBasis ℝ E` is Tau Ceti's chart Gram matrix
  `Riemannian.Tensor.chartGramMatrix`.
* `SymplecticGeometry.mpullback_symm_hodgeStar`: the Hodge star of a form, read in the chart, is
  `hodgeStarInChart` applied to the form read in the chart.
* `SymplecticGeometry.hodgeStarInChart_apply_eq_sum`: in a basis `b` of `E`, the star in the chart
  is the star of `E` for the inner product `gramInChart ψ y`: it is given by the volume of `b` and
  the inverse of the Gram matrix of `b`, as in
  `Orientation.formHodgeStar_apply_eq_volumeForm_mul_sum`.
* `SymplecticGeometry.contDiffOn_mpullback_riemannianVolumeForm`: the volume form read in the
  chart, evaluated on fixed vectors, is smooth on `ψ.target`.
* `SymplecticGeometry.contDiffOn_hodgeStarInChart`: the star in the chart is smooth on `ψ.target`.
* `SymplecticGeometry.fderiv_hodgeStarInChart_eq_zero`: at a point of `ψ.target` where the
  derivative of `gramInChart ψ` vanishes, so does the derivative of `hodgeStarInChart o ψ hkl`.
* `SymplecticGeometry.mpullback_symm_codifferential`: the codifferential `d^* β` read in the chart
  is `± S (d (S b))`, with `S` the star in the chart, `b` the form `β` read in the chart, `d` the
  flat exterior derivative, and the sign of Tau Ceti's `TauCeti.SmoothForm.codifferential`.
* `SymplecticGeometry.compContinuousLinearMap_hodgeStarInChart`: pulled back to the tangent
  space, the star in the chart is the Hodge star of the tangent space.
* `SymplecticGeometry.mpullback_symm_codifferential_of_fderiv_gramInChart_eq_zero`: where the
  metric in the chart has derivative zero, the codifferential read in the chart is
  `± S (Alt (S ∘ Db))`, with `Db` the derivative of the form read in the chart.
* `SymplecticGeometry.val_codifferential_symm_of_fderiv_gramInChart_eq_zero`: the same at the
  point `ψ.symm y` of `M`, as `± ⋆ Alt (⋆ ∘ B)` with `⋆` the Hodge star of the tangent space and
  `B` the derivative of the form read in the chart, carried there by `TauCeti.symbolInChart`.
* `SymplecticGeometry.alternatingFormInner_eq_formInnerInChart`: the pointwise inner product of
  two forms, read in the chart, is `formInnerInChart`; it is positive definite on `ψ.target`
  (`formInnerInChart_self_pos`) and smooth there (`contDiffOn_formInnerInChart`), and the Gram
  matrix of a basis is positive definite (`posDef_formInnerInChart`), so that a form is recovered
  from its inner products with the basis (`eq_sum_inv_mulVec_formInnerInChart`).

The proof of `hodgeStarInChart_apply_eq_sum` follows that of Tau Ceti's private lemma
`TauCeti.hodgeStar_symmL_apply` (`Geometry/Manifold/Riemannian/HodgeStar.lean`), with the
differential of `ψ.symm` in place of the inverse of a tangent trivialization. The proofs of
`exists_hodgeStarInChart_apply_eq` and `contDiffOn_hodgeStarInChart` adapt that of Tau Ceti's
`TauCeti.RoughForm.contMDiffAt_hodgeStar`, with the chart in place of the trivialization: the star
is evaluated on a fixed tuple, and its value is a smooth function of the volume and the Gram matrix
of a fixed basis.

## References

* [P. Griffiths, J. Harris, *Principles of Algebraic Geometry*][GriffithsHarris1978],
  Chapter 0, §6.
* F. W. Warner, *Foundations of Differentiable Manifolds and Lie Groups*, Graduate Texts in
  Mathematics 94, Springer, 1983, §6.1.
-/

public section

noncomputable section

open Set Module TauCeti
open Bundle (TotalSpace RiemannianBundle)
open scoped Manifold Topology ContDiff RealInnerProductSpace

namespace SymplecticGeometry

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] {m k l : ℕ}

/-! ### The metric in a chart -/

section Metric

open Bundle

variable (ψ : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞)

/-- The metric in the chart `ψ`: at `y`, the inner product of the tangent space at `ψ.symm y`,
read on `E` through the differential of `ψ.symm`. -/
def gramInChart (y : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  (ContinuousLinearMap.precomp ℝ (mfderiv 𝓘(ℝ, E) I ψ.symm y)).comp
    ((innerSL ℝ (E := TangentSpace I (ψ.symm y))).comp (mfderiv 𝓘(ℝ, E) I ψ.symm y))

theorem gramInChart_apply (y v w : E) :
    gramInChart ψ y v w = ⟪mfderiv 𝓘(ℝ, E) I ψ.symm y v, mfderiv 𝓘(ℝ, E) I ψ.symm y w⟫ :=
  (rfl)

/-- The metric in a chart is symmetric. -/
theorem gramInChart_comm (y v w : E) : gramInChart ψ y v w = gramInChart ψ y w v := by
  rw [gramInChart_apply, gramInChart_apply, real_inner_comm]

/-- On the target of the chart, the Gram matrix of the metric in a basis of `E` is positive
definite. -/
theorem posDef_gramInChart {ι : Type*} [Finite ι] (b : Basis ι ℝ E) {y : E}
    (hy : y ∈ ψ.target) : (Matrix.of fun i j ↦ gramInChart ψ y (b i) (b j)).PosDef := by
  have := Fintype.ofFinite ι
  set x := ψ.symm y
  have hcomp : (ContinuousLinearMap.toLinearMap (mfderiv I 𝓘(ℝ, E) ψ x) :
      TangentSpace I x →ₗ[ℝ] E) ∘ (fun i ↦ mfderiv 𝓘(ℝ, E) I ψ.symm y (b i)) = b :=
    funext fun i ↦ ψ.mfderiv_apply_mfderiv_symm_apply (by simp) hy (b i)
  have hli : LinearIndependent ℝ (fun i ↦ mfderiv 𝓘(ℝ, E) I ψ.symm y (b i)) :=
    LinearIndependent.of_comp _ (by rw [hcomp]; exact b.linearIndependent)
  convert Matrix.posDef_gram_of_linearIndependent hli using 1
  ext i j
  rw [Matrix.gram_apply, Matrix.of_apply, gramInChart_apply]

/-- On the target of the chart, the metric in the chart is positive on nonzero vectors. -/
theorem gramInChart_apply_self_pos {y : E} (hy : y ∈ ψ.target) {v : E} (hv : v ≠ 0) :
    0 < gramInChart ψ y v v := by
  rw [gramInChart_apply]
  refine real_inner_self_pos.2 fun h0 ↦ hv ?_
  have h := ψ.mfderiv_apply_mfderiv_symm_apply (by simp) hy v
  rw [h0, map_zero] at h
  exact h.symm

/-- **The metric under a change of coordinates.** If `Θ` is a partial diffeomorphism of `E`, the
metric in the chart `ψ.trans Θ` at `w`, evaluated on the images under the derivative of `Θ` of
two vectors, is the metric in the chart `ψ` at `Θ.symm w` evaluated on those vectors. -/
theorem gramInChart_trans_apply (Θ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞) {w : E}
    (hw : w ∈ Θ.target) (hψ : Θ.symm w ∈ ψ.target) (u v : E) :
    gramInChart (ψ.trans Θ) w (fderiv ℝ Θ (Θ.symm w) u) (fderiv ℝ Θ (Θ.symm w) v) =
      gramInChart ψ (Θ.symm w) u v := by
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have key (a : E) : mfderiv 𝓘(ℝ, E) I (ψ.trans Θ).symm w (fderiv ℝ Θ (Θ.symm w) a) =
      mfderiv 𝓘(ℝ, E) I ψ.symm (Θ.symm w) a := by
    have ha : fderiv ℝ Θ (Θ.symm w) a = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) Θ (Θ.symm w) a := by
      -- `NormedSpace.fromTangentSpace` is the identity of `E`, which Mathlib states by no lemma.
      rw [mfderiv_eq_fderiv]; rfl
    rw [ha, PartialDiffeomorph.coe_trans_symm, mfderiv_comp w
      (ψ.symm.mdifferentiableAt hn hψ) (Θ.symm.mdifferentiableAt hn hw)]
    exact congrArg (mfderiv 𝓘(ℝ, E) I ψ.symm (Θ.symm w))
      (Θ.mfderiv_symm_apply_mfderiv_apply_of_mem_target hn hw a)
  rw [gramInChart_apply, gramInChart_apply, key, key]
  -- The two inner products are taken in the tangent spaces at `(ψ.trans Θ).symm w` and at
  -- `ψ.symm (Θ.symm w)`, which are the same point by definition.
  rfl

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M]

/-- The metric in a chart is smooth on the target of the chart. -/
theorem contDiffOn_gramInChart
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] :
    ContDiffOn ℝ ∞ (gramInChart ψ) ψ.target := by
  refine contDiffOn_clm_apply.2 fun v ↦ contDiffOn_clm_apply.2 fun w y hy ↦ ?_
  have hψ : ContMDiffAt 𝓘(ℝ, E) I ∞ ψ.symm y :=
    ψ.symm.contMDiffOn.contMDiffAt (ψ.open_target.mem_nhds hy)
  have hs (v : E) := hψ.mfderiv_apply_sectionAlong (b := id) (s := fun _ ↦ v)
    (contMDiff_tangentBundleModelSpaceHomeomorph_symm_prodMk_const 𝓘(ℝ, E) v ∞).contMDiffAt
    (by simp)
  exact (contMDiffAt_iff_contDiffAt.1 (ContMDiffAt.inner_bundle (F := E)
    (E := fun x : M ↦ TangentSpace I x) (b := ψ.symm) (hs v) (hs w))).contDiffWithinAt

/-- The entries of the inverse of the Gram matrix of a basis `b` of `E` for the metric in a chart
are smooth on the target of the chart. -/
theorem contDiffOn_inv_gramInChart_apply
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (b : Basis ι ℝ E) (i j : ι) :
    ContDiffOn ℝ ∞ (fun y ↦ (Matrix.of fun i j ↦ gramInChart ψ y (b i) (b j))⁻¹ i j)
      ψ.target :=
  ContDiffOn.matrix_inv_apply (fun i j ↦
      contDiffOn_clm_apply.1 (contDiffOn_clm_apply.1 (contDiffOn_gramInChart ψ) (b i)) (b j))
    (fun _ hy ↦ (posDef_gramInChart ψ b hy).det_pos.ne') i j

/-- The Riemannian Jacobian of `ψ.symm` for a basis `b` of `E`, the square root of the determinant
of the Gram matrix of `b` for the metric in the chart, is smooth on the target of the chart. -/
theorem _root_.PartialDiffeomorph.contDiffOn_riemannianJacobian_symm
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (b : Basis ι ℝ E) :
    ContDiffOn ℝ ∞ (riemannianJacobian (I := I) b ψ.symm) ψ.target := by
  have h (y : E) : Matrix.gram ℝ (fun i ↦ mfderiv 𝓘(ℝ, E) I ψ.symm y (b i)) =
      Matrix.of fun i j ↦ gramInChart ψ y (b i) (b j) := by
    ext i j
    rw [Matrix.gram_apply, Matrix.of_apply, gramInChart_apply]
  have hJ : riemannianJacobian (I := I) b ψ.symm =
      fun y ↦ √(Matrix.of fun i j ↦ gramInChart ψ y (b i) (b j)).det := by
    ext y
    rw [riemannianJacobian_eq_sqrt_det_gram, h]
  rw [hJ]
  exact (ContDiffOn.matrix_det fun i j ↦ contDiffOn_clm_apply.1
    (contDiffOn_clm_apply.1 (contDiffOn_gramInChart ψ) (b i)) (b j)).sqrt
    fun y hy ↦ (posDef_gramInChart ψ b hy).det_pos.ne'

end Metric

/-- For the atlas chart at `x`, the matrix of the metric in the chart in the basis `finBasis ℝ E`
of `E` is Tau Ceti's chart Gram matrix at `x`. -/
theorem gramInChart_extChartPartialDiffeomorph [FiniteDimensional ℝ E] [IsManifold I ∞ M] (x : M)
    {y : E} (hy : y ∈ (extChartPartialDiffeomorph I ∞ x).target) (i j : Fin (finrank ℝ E)) :
    gramInChart (extChartPartialDiffeomorph I ∞ x) y (finBasis ℝ E i) (finBasis ℝ E j) =
      Riemannian.Tensor.chartGramMatrix (I := I) x ((extChartAt I x).symm y) i j := by
  have hsymm : ⇑(extChartPartialDiffeomorph I ∞ x).symm = (extChartAt I x).symm :=
    funext (extChartPartialDiffeomorph_symm_apply I ∞ x)
  rw [extChartPartialDiffeomorph_target] at hy
  have hyt : y ∈ (extChartAt I x).target := interior_subset hy
  have hI : range I ∈ 𝓝 y := mem_interior_iff_mem_nhds.mp
    (interior_mono (extChartAt_target_subset_range x) hy)
  have hsrc : (extChartAt I x).symm y ∈ (chartAt H x).source := by
    rw [← extChartAt_source I]
    exact (extChartAt I x).map_target hyt
  have hframe (c : Fin (finrank ℝ E)) : Riemannian.Tensor.chartLocalFrame (I := I) x c
      ((extChartAt I x).symm y) = mfderiv 𝓘(ℝ, E) I (extChartAt I x).symm y (finBasis ℝ E c) := by
    rw [Riemannian.Tensor.chartLocalFrame_eq_symmL, TangentBundle.symmL_trivializationAt hsrc,
      (extChartAt I x).right_inv hyt, mfderivWithin_of_mem_nhds hI]
    -- The two sides differ only in the types `E` and `TangentSpace 𝓘(ℝ, E) y` of the vector.
    rfl
  rw [gramInChart_apply, Riemannian.Tensor.chartGramMatrix_apply, hframe, hframe, hsymm]

/-! ### The Hodge star in a chart -/

section HodgeStar

open Bundle

/-- The fibrewise Hodge star `formHodgeStarCLM` at `x` is the Hodge star
`Orientation.formHodgeStar` of the tangent space at `x`, for the orientation that `o` gives it,
as a continuous linear map. -/
theorem _root_.TauCeti.formHodgeStarCLM_def [IsManifold I 1 M] [FiniteDimensional ℝ E]
    (o : Manifold.Orientation I M (Fin m)) (hkl : k + l = m) (x : M) :
    formHodgeStarCLM o hkl x =
      (letI := o.fact_finrank_tangentSpace x
       ((o.orientationAt x).formHodgeStar (hkl.trans (o.fact_finrank_tangentSpace x).out.symm)
         ).toContinuousLinearEquiv.toContinuousLinearMap) :=
  -- Tau Ceti does not expose the body of `formHodgeStarCLM`, so this is not `rfl` here.
  ContinuousLinearMap.ext fun a ↦ formHodgeStarCLM_apply o hkl x a

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M] (o : Manifold.Orientation I M (Fin m))
  (ψ : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞)

/-- The Hodge star in the chart `ψ`: at `y`, the Hodge star of the tangent space at `ψ.symm y`
for the orientation `o`, transported to forms on `E` through the differential of `ψ.symm`. On
`ψ.target` it is the Hodge star of `E` for the inner product `gramInChart ψ y`
(`hodgeStarInChart_apply_eq_sum`). -/
def hodgeStarInChart (hkl : k + l = m) (y : E) :
    (E [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] E [⋀^Fin l]→L[ℝ] ℝ :=
  ContinuousAlternatingMap.compContinuousLinearMapCLM (mfderiv 𝓘(ℝ, E) I ψ.symm y) ∘L
    formHodgeStarCLM o hkl (ψ.symm y) ∘L
      ContinuousAlternatingMap.compContinuousLinearMapCLM
        (mfderiv I 𝓘(ℝ, E) ψ (ψ.symm y) : TangentSpace I (ψ.symm y) →L[ℝ] E)

theorem hodgeStarInChart_def (hkl : k + l = m) (y : E) :
    hodgeStarInChart o ψ hkl y =
      ContinuousAlternatingMap.compContinuousLinearMapCLM (mfderiv 𝓘(ℝ, E) I ψ.symm y) ∘L
        formHodgeStarCLM o hkl (ψ.symm y) ∘L
          ContinuousAlternatingMap.compContinuousLinearMapCLM
            (mfderiv I 𝓘(ℝ, E) ψ (ψ.symm y) : TangentSpace I (ψ.symm y) →L[ℝ] E) :=
  (rfl)

theorem hodgeStarInChart_apply (hkl : k + l = m) (y : E)
    (a : E [⋀^Fin k]→L[ℝ] ℝ) (w : Fin l → E) :
    hodgeStarInChart o ψ hkl y a w = formHodgeStarCLM o hkl (ψ.symm y)
      (a.compContinuousLinearMap
        (mfderiv I 𝓘(ℝ, E) ψ (ψ.symm y) : TangentSpace I (ψ.symm y) →L[ℝ] E))
        (fun i ↦ mfderiv 𝓘(ℝ, E) I ψ.symm y (w i)) :=
  (rfl)

/-- On the target of the chart, the Hodge star of a form, read in the chart, is the star in the
chart applied to the form read in the chart. -/
theorem mpullback_symm_hodgeStar (hkl : k + l = m)
    (φ : RoughForm I M ℝ k) {y : E} (hy : y ∈ ψ.target) :
    (mpullback 𝓘(ℝ, E) I ψ.symm (RoughForm.hodgeStar o hkl φ) y : E [⋀^Fin l]→L[ℝ] ℝ) =
      hodgeStarInChart o ψ hkl y (mpullback 𝓘(ℝ, E) I ψ.symm φ y) := by
  ext w
  refine ((mpullback_apply _ _ y w).trans ?_).trans (hodgeStarInChart_apply o ψ hkl y _ w).symm
  rw [RoughForm.hodgeStar_eq_formHodgeStarCLM]
  exact (congrArg (fun a ↦ formHodgeStarCLM o hkl (ψ.symm y) a
    fun i ↦ mfderiv 𝓘(ℝ, E) I ψ.symm y (w i))
    (mpullback_symm_compContinuousLinearMap_mfderiv ψ (by simp) φ hy)).symm

/-- **The Hodge star in a chart, in a basis.** On the target of the chart, for a basis `b` of `E`
with Gram matrix `G` for `gramInChart ψ y`, `(S a)(w)` is the volume of `b` (read in the chart)
times the sum over the increasing `k`-tuples `i₁ < ⋯ < iₖ` of `a(b_{i₁}, …, b_{iₖ})` times the
`b`-determinant of `(∑ⱼ (G⁻¹)_{i₁ j} bⱼ, …, ∑ⱼ (G⁻¹)_{iₖ j} bⱼ, w₁, …, wₗ)`. This is
`Orientation.formHodgeStar_apply_eq_volumeForm_mul_sum` for the inner product `gramInChart ψ y`. -/
theorem hodgeStarInChart_apply_eq_sum (hkl : k + l = m)
    (b : Basis (Fin m) ℝ E) {y : E} (hy : y ∈ ψ.target) (a : E [⋀^Fin k]→L[ℝ] ℝ)
    (w : Fin l → E) :
    hodgeStarInChart o ψ hkl y a w =
      mpullback 𝓘(ℝ, E) I ψ.symm (riemannianVolumeForm o) y b *
        ∑ s : powersetCard (Fin m) k, a (b ∘ powersetCard.ofFinEmbEquiv.symm s) *
          b.det (Fin.append (fun i ↦ ∑ j,
            (Matrix.of fun i j ↦ gramInChart ψ y (b i) (b j))⁻¹
              (powersetCard.ofFinEmbEquiv.symm s i) j • b j) w ∘ Fin.cast hkl.symm) := by
  set x := ψ.symm y
  let := o.fact_finrank_tangentSpace x
  -- The differential of `ψ.symm` at `y` is a linear equivalence `A`, with inverse the differential
  -- of `ψ` at `x`; the frame `B = A ∘ b` is a basis of the tangent space at `x`.
  let A : E ≃L[ℝ] TangentSpace I x := ψ.mfderivSymmEquiv (by simp) hy
  let B : Basis (Fin m) ℝ (TangentSpace I x) := b.map A.toLinearEquiv
  have hA (v : E) : A v = mfderiv 𝓘(ℝ, E) I ψ.symm y v :=
    congrFun (ψ.coe_mfderivSymmEquiv _ hy) v
  have hAs (v : TangentSpace I x) : A.symm v = mfderiv I 𝓘(ℝ, E) ψ x v :=
    congrFun (ψ.coe_mfderivSymmEquiv_symm _ hy) v
  have hB (i : Fin m) : B i = A (b i) := Basis.map_apply _ _ _
  have hgram : Matrix.gram ℝ B = Matrix.of fun i j ↦ gramInChart ψ y (b i) (b j) := by
    ext i j
    rw [Matrix.gram_apply, hB, hB, hA, hA, Matrix.of_apply, gramInChart_apply]
  rw [hodgeStarInChart_apply, formHodgeStarCLM_apply,
    Orientation.formHodgeStar_apply_eq_volumeForm_mul_sum _ _ B, hgram]
  congr 1
  · refine Eq.trans ?_ (mpullback_apply _ _ y _).symm
    rw [riemannianVolumeForm_apply]
    exact congrArg _ (funext fun i ↦ (hB i).trans (hA _))
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  congr 1
  · refine (ContinuousAlternatingMap.compContinuousLinearMap_apply _ _ _).trans ?_
    exact congrArg a (funext fun i ↦
      (hAs _).symm.trans ((congrArg A.symm (hB _)).trans (A.symm_apply_apply _)))
  -- Read the determinant in the frame `B` back in `E` through `A`.
  rw [Basis.det_map]
  congr 1
  funext i
  simp only [Function.comp_apply]
  generalize Fin.cast _ i = j
  induction j using Fin.addCases with
  | left c => simp [map_sum, map_smul, hB]
  | right c =>
    simp only [Fin.append_right]
    exact (congrArg _ (hA _).symm).trans (A.toLinearEquiv.symm_apply_apply _)

/-- The Riemannian volume form read in the chart, evaluated on a fixed family `v` of vectors of
`E`, is smooth on the target of the chart. -/
theorem contDiffOn_mpullback_riemannianVolumeForm
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] (v : Fin m → E) :
    ContDiffOn ℝ ∞ (fun y ↦ mpullback 𝓘(ℝ, E) I ψ.symm (riemannianVolumeForm o) y v)
      ψ.target := by
  have : IsManifold I (∞ + 1) M := by simpa using ‹IsManifold I ∞ M›
  exact (ContinuousAlternatingMap.apply ℝ E ℝ v).contDiff.comp_contDiffOn
    (SmoothForm.contDiffOn_mpullback (⟨riemannianVolumeForm o,
      (isSmoothForm_riemannianVolumeForm o).mem_smoothBundleForms⟩ : SmoothForm I M ℝ m)
      ψ.open_target ψ.symm.contMDiffOn)

/-- On the target of the chart, the square of the volume of a basis `b` of `E`, read in the
chart, is the determinant of the Gram matrix of `b` for the metric in the chart. -/
theorem mpullback_riemannianVolumeForm_mul_self (b : Basis (Fin m) ℝ E) {y : E}
    (hy : y ∈ ψ.target) :
    mpullback 𝓘(ℝ, E) I ψ.symm (riemannianVolumeForm o) y b *
        mpullback 𝓘(ℝ, E) I ψ.symm (riemannianVolumeForm o) y b =
      (Matrix.of fun i j ↦ gramInChart ψ y (b i) (b j)).det := by
  set x := ψ.symm y
  let := o.fact_finrank_tangentSpace x
  have hgram : Matrix.gram ℝ (fun i ↦ mfderiv 𝓘(ℝ, E) I ψ.symm y (b i)) =
      Matrix.of fun i j ↦ gramInChart ψ y (b i) (b j) := by
    ext i j
    rw [Matrix.gram_apply, Matrix.of_apply, gramInChart_apply]
  have hv : mpullback 𝓘(ℝ, E) I ψ.symm (riemannianVolumeForm o) y b =
      (o.orientationAt x).volumeForm (fun i ↦ mfderiv 𝓘(ℝ, E) I ψ.symm y (b i)) :=
    (mpullback_apply _ _ y _).trans (riemannianVolumeForm_apply _ _ _)
  rw [hv, ← abs_mul_abs_self, (o.orientationAt x).abs_volumeForm_apply_eq_sqrt_det_gram, hgram,
    Real.mul_self_sqrt (posDef_gramInChart ψ b hy).det_pos.le]

open scoped Matrix.Norms.Operator in
/-- On the target of the chart, the value of the star in the chart on `a` and `w` is a function
of the volume of a basis `b` of `E` read in the chart and of the Gram matrix of `b` for the metric
in the chart, smooth wherever the determinant of the Gram matrix does not vanish. -/
theorem exists_hodgeStarInChart_apply_eq (hkl : k + l = m) (b : Basis (Fin m) ℝ E)
    (a : E [⋀^Fin k]→L[ℝ] ℝ) (w : Fin l → E) :
    ∃ F : ℝ × (Fin m → Fin m → ℝ) → ℝ,
      (∀ (c : ℝ) (g : Fin m → Fin m → ℝ), (Matrix.of g).det ≠ 0 → ContDiffAt ℝ ∞ F (c, g)) ∧
      ∀ y ∈ ψ.target, hodgeStarInChart o ψ hkl y a w =
        F (mpullback 𝓘(ℝ, E) I ψ.symm (riemannianVolumeForm o) y b,
          fun i j ↦ gramInChart ψ y (b i) (b j)) := by
  -- `F₀` is the expression of `hodgeStarInChart_apply_eq_sum` in the volume and in the entries of
  -- the inverse Gram matrix.
  let F₀ : ℝ × (Fin m → Fin m → ℝ) → ℝ := fun p ↦
    p.1 * ∑ s : powersetCard (Fin m) k, a (b ∘ powersetCard.ofFinEmbEquiv.symm s) *
      b.det (Fin.append (fun i ↦ ∑ j, p.2 (powersetCard.ofFinEmbEquiv.symm s i) j • b j) w ∘
        Fin.cast hkl.symm)
  refine ⟨fun p ↦ F₀ (p.1, Matrix.of.symm (Matrix.of p.2)⁻¹), fun c g hg ↦ ?_, fun y hy ↦ ?_⟩
  · have hF₀ : ContDiff ℝ ∞ F₀ := by
      refine contDiff_fst.mul (ContDiff.sum fun s _ ↦ contDiff_const.mul ?_)
      have hW : ContDiff ℝ ∞ fun p : ℝ × (Fin m → Fin m → ℝ) ↦
          Fin.append (fun i ↦ ∑ j, p.2 (powersetCard.ofFinEmbEquiv.symm s i) j • b j) w ∘
            Fin.cast hkl.symm := by
        refine contDiff_pi.2 fun i ↦ ?_
        simp only [Function.comp_apply]
        generalize Fin.cast hkl.symm i = j
        induction j using Fin.addCases with
        | left c =>
          simp only [Fin.append_left]
          exact ContDiff.sum fun j _ ↦ (by fun_prop : ContDiff ℝ ∞
            fun p : ℝ × (Fin m → Fin m → ℝ) ↦ p.2 (powersetCard.ofFinEmbEquiv.symm s c) j).smul
              contDiff_const
        | right c =>
          simp only [Fin.append_right]
          exact contDiff_const
      simpa [Function.comp_def] using
        (AlternatingMap.toContinuousAlternatingMap b.det).toContinuousMultilinearMap.contDiff.comp
          hW
    -- The inverse matrix is smooth where the determinant does not vanish: for the operator norm
    -- on matrices it is `Ring.inverse`, read through `Matrix.of`.
    have hinv : ContDiffAt ℝ ∞ (fun g : Fin m → Fin m → ℝ ↦ Matrix.of.symm (Matrix.of g)⁻¹) g := by
      have hu : IsUnit (Matrix.of g) := (Matrix.isUnit_iff_isUnit_det _).2 hg.isUnit
      have hof : ContDiff ℝ ∞ (Matrix.of : (Fin m → Fin m → ℝ) → Matrix (Fin m) (Fin m) ℝ) := by
        simpa using (Matrix.ofContinuousLinearEquiv ℝ :
          (Fin m → Fin m → ℝ) ≃L[ℝ] Matrix (Fin m) (Fin m) ℝ).contDiff
      have hof_symm : ContDiff ℝ ∞
          (Matrix.of.symm : Matrix (Fin m) (Fin m) ℝ → Fin m → Fin m → ℝ) := by
        simpa using (Matrix.ofContinuousLinearEquiv ℝ :
          (Fin m → Fin m → ℝ) ≃L[ℝ] Matrix (Fin m) (Fin m) ℝ).symm.contDiff
      simpa [Function.comp_def, Matrix.nonsing_inv_eq_ringInverse] using
        hof_symm.contDiffAt.comp g ((contDiffAt_ringInverse ℝ hu.unit).comp g hof.contDiffAt)
    exact hF₀.contDiffAt.comp (c, g) (contDiffAt_fst.prodMk
      (ContDiffAt.comp (g := fun g : Fin m → Fin m → ℝ ↦ Matrix.of.symm (Matrix.of g)⁻¹)
        (f := Prod.snd) (c, g) hinv contDiffAt_snd))
  · rw [hodgeStarInChart_apply_eq_sum o ψ hkl b hy a w]
    simp only [F₀, Matrix.of_symm_apply]

/-- The star in a chart is smooth on the target of the chart. -/
theorem contDiffOn_hodgeStarInChart
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] (hkl : k + l = m) :
    ContDiffOn ℝ ∞ (hodgeStarInChart o ψ hkl) ψ.target := by
  have hm : finrank ℝ E = m := by simpa using o.card_eq.symm
  let b : Basis (Fin m) ℝ E := (finBasis ℝ E).reindex (finCongr hm)
  -- The volume of `b` and the Gram matrix of `b`, read in the chart, are smooth.
  have hP : ContDiffOn ℝ ∞ (fun y ↦ (mpullback 𝓘(ℝ, E) I ψ.symm (riemannianVolumeForm o) y b,
      fun i j ↦ gramInChart ψ y (b i) (b j))) ψ.target :=
    (contDiffOn_mpullback_riemannianVolumeForm o ψ b).prodMk (contDiffOn_pi.2 fun i ↦
      contDiffOn_pi.2 fun j ↦ contDiffOn_clm_apply.1 (contDiffOn_clm_apply.1
        (contDiffOn_gramInChart ψ) (b i)) (b j))
  refine contDiffOn_clm_apply.2 fun a y hy ↦ ?_
  rw [← contMDiffWithinAt_iff_contDiffWithinAt]
  refine contMDiffWithinAt_continuousAlternatingMap_apply.2 fun w ↦ ?_
  rw [contMDiffWithinAt_iff_contDiffWithinAt]
  obtain ⟨F, hF, hSF⟩ := exists_hodgeStarInChart_apply_eq o ψ hkl b a w
  refine ((hF _ _ ?_).comp_contDiffWithinAt y (hP y hy)).congr (fun z hz ↦ hSF z hz) (hSF y hy)
  exact (posDef_gramInChart ψ b hy).det_pos.ne'

open scoped Matrix.Norms.Operator in
/-- **The star in a chart where the metric is flat to first order.** At a point of the target of
the chart where the derivative of the metric in the chart vanishes, the derivative of the star in
the chart vanishes too. -/
theorem fderiv_hodgeStarInChart_eq_zero
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    (hkl : k + l = m) {y : E} (hy : y ∈ ψ.target)
    (h : fderiv ℝ (gramInChart ψ) y = 0) : fderiv ℝ (hodgeStarInChart o ψ hkl) y = 0 := by
  have hm : finrank ℝ E = m := by simpa using o.card_eq.symm
  let b : Basis (Fin m) ℝ E := (finBasis ℝ E).reindex (finCongr hm)
  have hT := ψ.open_target.mem_nhds hy
  have hpos := (posDef_gramInChart ψ b hy).det_pos
  -- The entries of the Gram matrix of `b` have derivative zero at `y`.
  have hG : HasFDerivAt (𝕜 := ℝ) (fun z i j ↦ gramInChart ψ z (b i) (b j)) 0 y := by
    have hg := (((contDiffOn_gramInChart ψ).contDiffAt hT).differentiableAt
      (by simp)).hasFDerivAt
    rw [h] at hg
    refine hasFDerivAt_pi'.2 fun i ↦ ?_
    rw [ContinuousLinearMap.comp_zero]
    refine hasFDerivAt_pi'.2 fun j ↦ ?_
    rw [ContinuousLinearMap.comp_zero]
    simpa using (hg.clm_apply (hasFDerivAt_const (b i) y)).clm_apply (hasFDerivAt_const (b j) y)
  -- So does their determinant, the square of the volume of `b`; since the volume of `b` is
  -- differentiable and does not vanish, its derivative vanishes too.
  have hdet : HasFDerivAt (𝕜 := ℝ)
      (fun z ↦ (Matrix.of fun i j ↦ gramInChart ψ z (b i) (b j)).det) 0 y := by
    have hd : ContDiff ℝ ∞ fun g : Fin m → Fin m → ℝ ↦ (Matrix.of g).det := by
      simpa [Function.comp_def] using
        Matrix.contDiff_det.comp (Matrix.ofContinuousLinearEquiv ℝ :
          (Fin m → Fin m → ℝ) ≃L[ℝ] Matrix (Fin m) (Fin m) ℝ).contDiff
    have h0 := ((hd.differentiable (by simp)) _).hasFDerivAt.comp y hG
    rw [ContinuousLinearMap.comp_zero] at h0
    exact h0
  set f := fun z ↦ mpullback 𝓘(ℝ, E) I ψ.symm (riemannianVolumeForm o) z b
  have hf : DifferentiableAt ℝ f y :=
    ((contDiffOn_mpullback_riemannianVolumeForm o ψ b).contDiffAt hT).differentiableAt (by simp)
  have hfy : f y ≠ 0 := fun h0 ↦ hpos.ne' (by
    rw [← mpullback_riemannianVolumeForm_mul_self o ψ b hy]
    exact mul_self_eq_zero.2 h0)
  have hf2 := (hf.hasFDerivAt.mul hf.hasFDerivAt).congr_of_eventuallyEq
    (Filter.eventually_of_mem hT fun z hz ↦ (mpullback_riemannianVolumeForm_mul_self o ψ b hz).symm)
  have hf0 : fderiv ℝ f y = 0 := by
    have h2 : (f y + f y) • fderiv ℝ f y = 0 := by
      rw [add_smul]
      exact hf2.unique hdet
    exact (smul_eq_zero.1 h2).resolve_left fun h0 ↦ hfy (by linarith)
  have hP : HasFDerivAt (𝕜 := ℝ) (fun z ↦ (f z, fun i j ↦ gramInChart ψ z (b i) (b j)))
      ((0 : E →L[ℝ] ℝ).prod 0) y := by
    refine HasFDerivAt.prodMk ?_ hG
    rw [← hf0]
    exact hf.hasFDerivAt
  -- Each value of the star on `a` and `w` is a smooth function of these, hence has derivative
  -- zero at `y`, and the star is differentiable at `y`.
  have hS : DifferentiableAt ℝ (hodgeStarInChart o ψ hkl) y :=
    ((contDiffOn_hodgeStarInChart o ψ hkl).contDiffAt hT).differentiableAt (by simp)
  ext v a w
  obtain ⟨F, hF, hSF⟩ := exists_hodgeStarInChart_apply_eq o ψ hkl b a w
  have hc := (((hF _ _ hpos.ne').differentiableAt (by simp)).hasFDerivAt.comp y
    hP).congr_of_eventuallyEq (Filter.eventually_of_mem hT fun z hz ↦ hSF z hz)
  have hd := (ContinuousAlternatingMap.apply ℝ E ℝ w).hasFDerivAt.comp y
    (hS.hasFDerivAt.clm_apply (hasFDerivAt_const a y))
  have h0 := congrArg (· v) (hd.unique hc)
  simpa [Prod.mk_zero_zero] using h0

/-- **The codifferential in a chart.** On the target of the chart, the codifferential `d^* β` of
a smooth `(k + 1)`-form, read in the chart, is `(-1) ^ (m (k + 2) + 1) S' (d (S b))`, where `b` is
`β` read in the chart, `S` and `S'` are the stars in the chart in degrees `k + 1` and `l + 1`, `d`
is the flat exterior derivative, and the sign is that of Tau Ceti's
`TauCeti.SmoothForm.codifferential`. -/
theorem mpullback_symm_codifferential
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    (hkl : k + 1 + l = m) (hlk : l + 1 + k = m)
    (β : SmoothForm I M ℝ (k + 1)) {y : E} (hy : y ∈ ψ.target) :
    (mpullback 𝓘(ℝ, E) I ψ.symm (SmoothForm.codifferential o hkl β).val y :
        E [⋀^Fin k]→L[ℝ] ℝ) =
      (-1 : ℝ) ^ (m * (k + 2) + 1) • hodgeStarInChart o ψ hlk y
        (extDeriv (fun z ↦ hodgeStarInChart o ψ hkl z (mpullback 𝓘(ℝ, E) I ψ.symm β.val z)) y) := by
  have hsymm (z : E) (hz : z ∈ ψ.target) : ContMDiffAt 𝓘(ℝ, E) I 2 ψ.symm z :=
    (ψ.symm.contMDiffOn.contMDiffAt (ψ.open_target.mem_nhds hz)).of_le (by simp)
  have hd := mpullback_mextDeriv_on (s := ψ.target) hsymm
    (φ := (SmoothForm.hodgeStar o hkl β).val)
    (fun z _ ↦ ((SmoothForm.hodgeStar o hkl β).contMDiff _).of_le (m := 1) (by simp)) y hy
  have hev : (mpullback 𝓘(ℝ, E) I ψ.symm (SmoothForm.hodgeStar o hkl β).val :
      E → E [⋀^Fin l]→L[ℝ] ℝ) =ᶠ[𝓝 y]
      fun z ↦ hodgeStarInChart o ψ hkl z (mpullback 𝓘(ℝ, E) I ψ.symm β.val z) :=
    Filter.eventually_of_mem (ψ.open_target.mem_nhds hy) fun z hz ↦
      (congrArg (mpullback 𝓘(ℝ, E) I ψ.symm · z) (SmoothForm.coe_hodgeStar o hkl β)).trans
        (mpullback_symm_hodgeStar o ψ hkl _ hz)
  rw [SmoothForm.codifferential_apply o hkl hlk, Submodule.coe_smul, mpullback_smul,
    Pi.smul_apply, SmoothForm.coe_hodgeStar, mpullback_symm_hodgeStar o ψ hlk _ hy,
    mextDerivₗ_apply, hd, mextDeriv_eq_extDeriv, hev.extDeriv_eq]
  -- The two sides differ only in the type in which the scalar multiplication is taken: the fibre
  -- `TangentSpace 𝓘(ℝ, E) y [⋀^Fin k]→L[ℝ] Trivial E ℝ y` of the pullback, or `E [⋀^Fin k]→L[ℝ] ℝ`.
  rfl

/-- Pulled back to the tangent space along the differential of `ψ`, the star in the chart is the
Hodge star of the tangent space, applied to the pulled-back form. -/
theorem compContinuousLinearMap_hodgeStarInChart (hkl : k + l = m) {y : E} (hy : y ∈ ψ.target)
    (a : E [⋀^Fin k]→L[ℝ] ℝ) :
    (hodgeStarInChart o ψ hkl y a).compContinuousLinearMap
        (mfderiv I 𝓘(ℝ, E) ψ (ψ.symm y) : TangentSpace I (ψ.symm y) →L[ℝ] E) =
      formHodgeStarCLM o hkl (ψ.symm y)
        (a.compContinuousLinearMap
          (mfderiv I 𝓘(ℝ, E) ψ (ψ.symm y) : TangentSpace I (ψ.symm y) →L[ℝ] E)) := by
  ext w
  exact (hodgeStarInChart_apply o ψ hkl y a _).trans (congrArg _ (funext fun i ↦
    ψ.mfderiv_symm_apply_mfderiv_apply_of_mem_target (by simp) hy (w i)))

/-- At a point of the target where the metric in the chart has derivative zero, the
codifferential read in the chart is `± S (Alt (S ∘ Db))`, with `S` the star in the chart at that
point, `Db` the derivative there of the form read in the chart and `Alt` the alternation
`alternatizeUncurryFin`: the derivative of the star drops out. -/
theorem mpullback_symm_codifferential_of_fderiv_gramInChart_eq_zero
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    (hkl : k + 1 + l = m) (hlk : l + 1 + k = m)
    (β : SmoothForm I M ℝ (k + 1)) {y : E} (hy : y ∈ ψ.target)
    (h : fderiv ℝ (gramInChart ψ) y = 0) :
    (mpullback 𝓘(ℝ, E) I ψ.symm (SmoothForm.codifferential o hkl β).val y :
        E [⋀^Fin k]→L[ℝ] ℝ) =
      (-1 : ℝ) ^ (m * (k + 2) + 1) • hodgeStarInChart o ψ hlk y
        (ContinuousAlternatingMap.alternatizeUncurryFin (hodgeStarInChart o ψ hkl y ∘L
          fderiv ℝ (F := E [⋀^Fin (k + 1)]→L[ℝ] ℝ) (mpullback 𝓘(ℝ, E) I ψ.symm β.val) y)) := by
  have hT := ψ.open_target.mem_nhds hy
  have hS : DifferentiableAt ℝ (hodgeStarInChart o ψ hkl) y :=
    ((contDiffOn_hodgeStarInChart o ψ hkl).contDiffAt hT).differentiableAt (by simp)
  have hb : DifferentiableAt ℝ (F := E [⋀^Fin (k + 1)]→L[ℝ] ℝ)
      (mpullback 𝓘(ℝ, E) I ψ.symm β.val) y :=
    ((β.contDiffOn_mpullback ψ.open_target ψ.symm.contMDiffOn).contDiffAt hT).differentiableAt
      (by simp)
  rw [mpullback_symm_codifferential o ψ hkl hlk β hy, extDeriv, fderiv_clm_apply hS hb,
    fderiv_hodgeStarInChart_eq_zero o ψ hkl hy h]
  simp only [ContinuousLinearMap.flip_zero]
  -- The form read in the chart has the fibres of the pullback as its type, so the vanishing term
  -- is cleared up to that identification of types.
  erw [zero_apply]
  rw [add_zero]

open ContinuousAlternatingMap in
/-- At `ψ.symm y`, where the metric in the chart has derivative zero, the codifferential of `β`
is `± ⋆ Alt (⋆ ∘ B)`, with `⋆` the Hodge star of the tangent space at `ψ.symm y`, `Alt` the
alternation `alternatizeUncurryFin` and `B = TauCeti.symbolInChart ψ β y` the derivative of the
reading of `β` carried to that tangent space. -/
theorem val_codifferential_symm_of_fderiv_gramInChart_eq_zero
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    (hkl : k + 1 + l = m) (hlk : l + 1 + k = m) (β : SmoothForm I M ℝ (k + 1)) {y : E}
    (hy : y ∈ ψ.target) (h : fderiv ℝ (gramInChart ψ) y = 0) :
    (SmoothForm.codifferential o hkl β).val (ψ.symm y) =
      (-1 : ℝ) ^ (m * (k + 2) + 1) • formHodgeStarCLM o hlk (ψ.symm y)
        (alternatizeUncurryFin
          (formHodgeStarCLM o hkl (ψ.symm y) ∘L symbolInChart ψ β.val y)) := by
  -- The step on `E`, for a map `T` that intertwines the two stars, and the derivative `C`.
  have key (T : TangentSpace I (ψ.symm y) →L[ℝ] E)
      (hT : ∀ {i i' : ℕ} (hii' : i + i' = m) (a : E [⋀^Fin i]→L[ℝ] ℝ),
        (hodgeStarInChart o ψ hii' y a).compContinuousLinearMap T =
          formHodgeStarCLM o hii' (ψ.symm y) (a.compContinuousLinearMap T))
      (C : E →L[ℝ] E [⋀^Fin (k + 1)]→L[ℝ] ℝ) :
      ((-1 : ℝ) ^ (m * (k + 2) + 1) • hodgeStarInChart o ψ hlk y
        (alternatizeUncurryFin (hodgeStarInChart o ψ hkl y ∘L C))).compContinuousLinearMap T =
      (-1 : ℝ) ^ (m * (k + 2) + 1) • formHodgeStarCLM o hlk (ψ.symm y)
        (alternatizeUncurryFin (formHodgeStarCLM o hkl (ψ.symm y) ∘L
          (compContinuousLinearMapCLM T ∘L C ∘L T))) := by
    rw [← compContinuousLinearMapCLM_apply, map_smul, compContinuousLinearMapCLM_apply, hT,
      alternatizeUncurryFin_compContinuousLinearMap]
    congr 3
    ext v w
    simp only [ContinuousLinearMap.comp_apply, compContinuousLinearMapCLM_apply, hT]
  rw [← mpullback_symm_compContinuousLinearMap_mfderiv ψ (by simp)
      (SmoothForm.codifferential o hkl β).val hy,
    mpullback_symm_codifferential_of_fderiv_gramInChart_eq_zero o ψ hkl hlk β hy h,
    symbolInChart_def]
  exact key _ (fun hii' a ↦ compContinuousLinearMap_hodgeStarInChart o ψ hii' hy a) _

end HodgeStar

/-! ### The inner product of forms in a chart -/

section FormInner

open Bundle
open scoped Matrix

variable [FiniteDimensional ℝ E] (ψ : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞)

/-- The inner product of `k`-forms in the chart `ψ`: at `y`, the inner product
`alternatingFormInner` of the tangent space at `ψ.symm y`, read on the forms on `E` through the
differential of `ψ`. -/
def formInnerInChart (y : E) :
    (E [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] (E [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    (LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ
      (alternatingFormInner (TangentSpace I (ψ.symm y)) k).compl₁₂
        (ContinuousAlternatingMap.compContinuousLinearMapCLM
          (mfderiv I 𝓘(ℝ, E) ψ (ψ.symm y))).toLinearMap
        (ContinuousAlternatingMap.compContinuousLinearMapCLM
          (mfderiv I 𝓘(ℝ, E) ψ (ψ.symm y))).toLinearMap)

theorem formInnerInChart_apply (y : E) (β γ : E [⋀^Fin k]→L[ℝ] ℝ) :
    formInnerInChart ψ y β γ = alternatingFormInner (TangentSpace I (ψ.symm y)) k
      (β.compContinuousLinearMap (mfderiv I 𝓘(ℝ, E) ψ (ψ.symm y)))
      (γ.compContinuousLinearMap (mfderiv I 𝓘(ℝ, E) ψ (ψ.symm y))) :=
  (rfl)

/-- On the target of the chart, the pointwise inner product of two forms at `ψ.symm y` is the
inner product in the chart of their readings at `y`. -/
theorem alternatingFormInner_eq_formInnerInChart (φ φ' : RoughForm I M ℝ k) {y : E}
    (hy : y ∈ ψ.target) :
    alternatingFormInner (TangentSpace I (ψ.symm y)) k (φ (ψ.symm y)) (φ' (ψ.symm y)) =
      formInnerInChart ψ y (mpullback 𝓘(ℝ, E) I ψ.symm φ y : E [⋀^Fin k]→L[ℝ] ℝ)
        (mpullback 𝓘(ℝ, E) I ψ.symm φ' y : E [⋀^Fin k]→L[ℝ] ℝ) := by
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  rw [← mpullback_symm_compContinuousLinearMap_mfderiv ψ hn φ hy,
    ← mpullback_symm_compContinuousLinearMap_mfderiv ψ hn φ' hy]
  exact (formInnerInChart_apply ψ y _ _).symm

/-- On the target of the chart, the inner product of forms in the chart is positive definite. -/
theorem formInnerInChart_self_pos {y : E} (hy : y ∈ ψ.target) {β : E [⋀^Fin k]→L[ℝ] ℝ}
    (hβ : β ≠ 0) : 0 < formInnerInChart ψ y β β := by
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  rw [formInnerInChart_apply]
  refine (alternatingFormInner_self_nonneg _).lt_of_ne' fun h ↦ hβ ?_
  have h0 := alternatingFormInner_self_eq_zero.1 h
  ext v
  have key (i : Fin k) : mfderiv I 𝓘(ℝ, E) ψ (ψ.symm y) (mfderiv 𝓘(ℝ, E) I ψ.symm y (v i)) =
      v i :=
    ψ.mfderiv_apply_mfderiv_symm_apply hn hy (v i)
  have := DFunLike.congr_fun h0 fun i ↦ mfderiv 𝓘(ℝ, E) I ψ.symm y (v i)
  -- The form `β.compContinuousLinearMap _` lives on the tangent space, a type synonym of `E`,
  -- so the evaluation lemma is applied up to that synonym.
  erw [ContinuousAlternatingMap.compContinuousLinearMap_apply, Function.comp_def] at this
  convert this using 2
  exact (funext key).symm

/-- The inner product of two fixed forms in a chart is smooth on the target of the chart. -/
theorem contDiffOn_formInnerInChart_apply [T2Space M] [IsManifold I ∞ M]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    (β γ : E [⋀^Fin k]→L[ℝ] ℝ) :
    ContDiffOn ℝ ∞ (fun y ↦ formInnerInChart ψ y β γ) ψ.target := by
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  intro y₀ hy₀
  -- A bump function equal to `1` near `y₀`, supported in `ψ.target`.
  obtain ⟨ε, hε, hεt⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (ψ.open_target.mem_nhds hy₀)
  let θ : ContDiffBump y₀ := ⟨ε / 2, ε, by positivity, by linarith⟩
  have hθt : tsupport θ ⊆ ψ.target := θ.tsupport_eq.trans_subset hεt
  -- The smooth forms equal near `ψ.symm y₀` to the pullbacks of the constant forms `β`, `γ`.
  have hsm (δ : E [⋀^Fin k]→L[ℝ] ℝ) : ContDiff ℝ ∞ fun y ↦ θ y • δ :=
    θ.contDiff.smul contDiff_const
  have hc (δ : E [⋀^Fin k]→L[ℝ] ℝ) : HasCompactSupport fun y ↦ θ y • δ :=
    θ.hasCompactSupport.smul_right
  have hs (δ : E [⋀^Fin k]→L[ℝ] ℝ) : tsupport (fun y ↦ θ y • δ) ⊆ ψ.target :=
    (tsupport_smul_subset_left _ _).trans hθt
  let ext (δ : E [⋀^Fin k]→L[ℝ] ℝ) : SmoothForm I M ℝ k :=
    SmoothForm.extendByZeroAlong ψ (fun y ↦ θ y • δ) (hsm δ) (hc δ) (hs δ)
  have heq : (fun y ↦ alternatingFormInner (TangentSpace I (ψ.symm y)) k
      ((ext β).val (ψ.symm y)) ((ext γ).val (ψ.symm y))) =ᶠ[𝓝 y₀]
        fun y ↦ formInnerInChart ψ y β γ := by
    filter_upwards [Metric.closedBall_mem_nhds y₀ (by positivity : 0 < ε / 2)] with y hy
    have hyt : y ∈ ψ.target := hεt (Metric.closedBall_subset_closedBall (by linarith) hy)
    have h1 (δ : E [⋀^Fin k]→L[ℝ] ℝ) :
        (mpullback 𝓘(ℝ, E) I ψ.symm (ext δ).val y : E [⋀^Fin k]→L[ℝ] ℝ) = δ := by
      rw [SmoothForm.coe_extendByZeroAlong, mpullback_symm_extendByZeroAlong ψ _ hn hyt,
        θ.one_of_mem_closedBall hy, one_smul]
    rw [alternatingFormInner_eq_formInnerInChart ψ _ _ hyt, h1, h1]
  have hψ : ContMDiffAt 𝓘(ℝ, E) I ∞ ψ.symm y₀ :=
    ψ.symm.contMDiffOn.contMDiffAt (ψ.open_target.mem_nhds hy₀)
  have hinner := (((ext β).isSmoothForm.contMDiff_alternatingFormInner
    (ext γ).isSmoothForm).contMDiffAt (x := ψ.symm y₀)).comp y₀ hψ
  exact (contMDiffAt_iff_contDiffAt.1 hinner).congr_of_eventuallyEq heq.symm |>.contDiffWithinAt

/-- The inner product of forms in a chart is symmetric. -/
theorem formInnerInChart_comm (y : E) (β γ : E [⋀^Fin k]→L[ℝ] ℝ) :
    formInnerInChart ψ y β γ = formInnerInChart ψ y γ β := by
  rw [formInnerInChart_apply, formInnerInChart_apply, alternatingFormInner_comm]

/-- The inner product in a chart, expanded in a basis `e` of the forms on `E`. -/
theorem formInnerInChart_eq_sum_repr {κ : Type*} [Fintype κ]
    (e : Module.Basis κ ℝ (E [⋀^Fin k]→L[ℝ] ℝ)) (y : E) (β γ : E [⋀^Fin k]→L[ℝ] ℝ) :
    formInnerInChart ψ y β γ =
      ∑ p, ∑ q, e.repr β p * e.repr γ q * formInnerInChart ψ y (e p) (e q) := by
  conv_lhs => rw [← e.sum_repr β, ← e.sum_repr γ]
  simp only [map_sum, map_smul, _root_.sum_apply, _root_.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦ by ring

/-- The inner product in a chart of two forms that depend smoothly on the point is smooth on the
target of the chart. -/
theorem contDiffOn_formInnerInChart [T2Space M] [IsManifold I ∞ M]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    {f g : E → E [⋀^Fin k]→L[ℝ] ℝ} {s : Set E} (hs : s ⊆ ψ.target) (hf : ContDiffOn ℝ ∞ f s)
    (hg : ContDiffOn ℝ ∞ g s) :
    ContDiffOn ℝ ∞ (fun y ↦ formInnerInChart ψ y (f y) (g y)) s := by
  let e := Module.finBasis ℝ (E [⋀^Fin k]→L[ℝ] ℝ)
  refine ContDiffOn.congr ?_ fun y _ ↦ formInnerInChart_eq_sum_repr ψ e y (f y) (g y)
  have hc (p) {F : E → E [⋀^Fin k]→L[ℝ] ℝ} (hF : ContDiffOn ℝ ∞ F s) :
      ContDiffOn ℝ ∞ (fun y ↦ e.repr (F y) p) s :=
    (LinearMap.toContinuousLinearMap (e.coord p)).contDiff.comp_contDiffOn hF
  exact ContDiffOn.sum fun p _ ↦ ContDiffOn.sum fun q _ ↦ ((hc p hf).mul (hc q hg)).mul
    ((contDiffOn_formInnerInChart_apply ψ (e p) (e q)).mono hs)

/-- On the target of the chart, the Gram matrix of a basis of the forms on `E` for the inner
product in the chart is positive definite. -/
theorem posDef_formInnerInChart {κ : Type*} [Finite κ]
    (e : Module.Basis κ ℝ (E [⋀^Fin k]→L[ℝ] ℝ)) {y : E} (hy : y ∈ ψ.target) :
    (Matrix.of fun p q ↦ formInnerInChart ψ y (e p) (e q)).PosDef := by
  classical
  have := Fintype.ofFinite κ
  have h := (LinearMap.BilinForm.posDef_toQuadraticMap_iff_matrix e
    (formInnerInChart ψ y).toLinearMap₁₂
    (LinearMap.BilinForm.isSymm_def.2 fun β γ ↦ formInnerInChart_comm ψ y β γ)).1
    fun β hβ ↦ formInnerInChart_self_pos ψ hy hβ
  convert h using 1
  ext p q
  rw [LinearMap.BilinForm.toMatrix_apply, Matrix.of_apply,
    ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply]

/-- On the target of the chart, a form `β` is recovered from its inner products in the chart with
the vectors of a basis `e` of the forms on `E`, through the inverse of the Gram matrix of `e`. -/
theorem eq_sum_inv_mulVec_formInnerInChart {κ : Type*} [Fintype κ] [DecidableEq κ]
    (e : Module.Basis κ ℝ (E [⋀^Fin k]→L[ℝ] ℝ)) {y : E} (hy : y ∈ ψ.target)
    (β : E [⋀^Fin k]→L[ℝ] ℝ) :
    β = ∑ p, ((Matrix.of fun p q ↦ formInnerInChart ψ y (e p) (e q))⁻¹ *ᵥ
      fun q ↦ formInnerInChart ψ y β (e q)) p • e p := by
  set G := Matrix.of fun p q ↦ formInnerInChart ψ y (e p) (e q)
  have hGz : (fun q ↦ formInnerInChart ψ y β (e q)) = G *ᵥ e.repr β := by
    ext q
    rw [formInnerInChart_comm, formInnerInChart_eq_sum_repr ψ e]
    simp [G, Matrix.mulVec, dotProduct, mul_comm, Finsupp.single_apply]
  have hG : IsUnit G.det := isUnit_iff_ne_zero.2 (posDef_formInnerInChart ψ e hy).det_pos.ne'
  rw [hGz, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul G hG, Matrix.one_mulVec, e.sum_repr]

end FormInner

end SymplecticGeometry
