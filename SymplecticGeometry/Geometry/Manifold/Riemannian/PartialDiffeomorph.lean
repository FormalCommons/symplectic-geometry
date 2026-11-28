/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.ChartGram
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.ChangeOfVariables
import SymplecticGeometry.Geometry.Manifold.Riemannian.Basic
import SymplecticGeometry.Geometry.Manifold.Riemannian.VolumeDensity.ChangeOfVariables
import SymplecticGeometry.Analysis.Calculus.ContDiff.Matrix
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.Basic
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Order.Compact
import TauCeti.Geometry.Manifold.ContMDiff.MFDeriv
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# The metric in a chart, and bounds for a partial diffeomorphism on a compact set

Let `M` be a manifold whose tangent spaces carry a Riemannian metric, and let
`ψ : PartialDiffeomorph I 𝓘(ℝ, E) M E n`, `n ≠ 0`, be a chart onto an open subset of a real
normed space `E`. Reading the inner product of the tangent space at `ψ.symm y` through the
differential of `ψ.symm` gives a bilinear form `PartialDiffeomorph.gramInChart ψ y` on `E`, the
metric in the chart. Its Gram matrix in a basis is positive definite on `ψ.target`, and for
`n = ∞`, a finite-dimensional `E` and a smooth metric it is smooth there.

When `E` is finite-dimensional and the metric is continuous, on a compact set `K ⊆ ψ.target` the
differential of `ψ.symm` is bounded above and below for the Riemannian norm on the tangent spaces
of `M`, and the Riemannian Jacobian of `ψ.symm` is bounded above and away from zero. These are
the estimates that compare integrals over `M` with integrals in a chart. On a compact subset of
`ψ.source`, the differential of `ψ` is bounded above and below too: both bounds follow from those
for `ψ.symm` on the image of the set, since the two differentials are mutually inverse.

The norm bounds specialize those for any `C¹` map with injective differentials
(`ContMDiffOn.exists_norm_mfderiv_le_mul_norm`, `ContMDiffOn.exists_pos_mul_norm_le_norm_mfderiv`)
to `ψ.symm`, whose differentials are invertible (Tau Ceti's
`PartialDiffeomorph.isInvertible_mfderiv`). The Jacobian is positive where the differential is
injective (`TauCeti.riemannianJacobian_pos`), and continuous
(`TauCeti.continuousOn_riemannianJacobian`).

## Main definitions

* `PartialDiffeomorph.gramInChart ψ y`: the bilinear form on `E` that is the metric at `ψ.symm y`
  read through the differential of `ψ.symm`.

## Main results

* `PartialDiffeomorph.posDef_gramInChart` and `PartialDiffeomorph.gramInChart_apply_self_pos`: on
  `ψ.target`, the Gram matrix of the metric in the chart in a basis is positive definite, and the
  metric in the chart is positive on nonzero vectors.
* `PartialDiffeomorph.contDiffOn_gramInChart`: the metric in the chart is smooth on `ψ.target`,
  and so are the entries of the inverse of its Gram matrix in a basis
  (`PartialDiffeomorph.contDiffOn_inv_gramInChart_apply`), and so is the Riemannian Jacobian of
  `ψ.symm` (`PartialDiffeomorph.contDiffOn_riemannianJacobian_symm`).
* `PartialDiffeomorph.gramInChart_trans_apply`: how the metric in the chart changes when the chart
  is followed by a partial diffeomorphism of `E`.
* `PartialDiffeomorph.gramInChart_extChartPartialDiffeomorph`: for the atlas chart at `x`, its
  matrix in the basis `finBasis ℝ E` is Tau Ceti's chart Gram matrix
  `Riemannian.Tensor.chartGramMatrix`.
* `PartialDiffeomorph.exists_mul_norm_le_norm_mfderiv_symm_le`: two-sided bounds for the
  differential of `ψ.symm` on a compact subset of `ψ.target`.
* `PartialDiffeomorph.exists_norm_mvfderiv_le_mul_norm`: the differential of `ψ` is bounded on
  the image of such a set under `ψ.symm`.
* `PartialDiffeomorph.exists_mul_norm_le_norm_mvfderiv_le`: two-sided bounds for the differential
  of `ψ` on a compact subset of `ψ.source`.
* `PartialDiffeomorph.riemannianJacobian_symm_pos` and
  `PartialDiffeomorph.exists_le_riemannianJacobian_symm_le`: the Riemannian Jacobian of `ψ.symm`
  is positive on `ψ.target`, and bounded above and away from zero on a compact subset of it.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 2.
-/

public section

noncomputable section

open Bundle Set
open scoped ContDiff Manifold Topology RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

namespace PartialDiffeomorph

open Module TauCeti

variable {n : ℕ∞ω}

/-! ### The metric in a chart -/

section Metric

open Bundle

variable (ψ : PartialDiffeomorph I 𝓘(ℝ, E) M E n)

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
theorem posDef_gramInChart (hn : n ≠ 0) {ι : Type*} [Finite ι] (b : Basis ι ℝ E) {y : E}
    (hy : y ∈ ψ.target) : (Matrix.of fun i j ↦ gramInChart ψ y (b i) (b j)).PosDef := by
  have := Fintype.ofFinite ι
  set x := ψ.symm y
  have hcomp : (ContinuousLinearMap.toLinearMap (mfderiv I 𝓘(ℝ, E) ψ x) :
      TangentSpace I x →ₗ[ℝ] E) ∘ (fun i ↦ mfderiv 𝓘(ℝ, E) I ψ.symm y (b i)) = b :=
    funext fun i ↦ ψ.mfderiv_apply_mfderiv_symm_apply hn hy (b i)
  have hli : LinearIndependent ℝ (fun i ↦ mfderiv 𝓘(ℝ, E) I ψ.symm y (b i)) :=
    LinearIndependent.of_comp _ (by rw [hcomp]; exact b.linearIndependent)
  convert Matrix.posDef_gram_of_linearIndependent hli using 1
  ext i j
  rw [Matrix.gram_apply, Matrix.of_apply, gramInChart_apply]

/-- On the target of the chart, the metric in the chart is positive on nonzero vectors. -/
theorem gramInChart_apply_self_pos (hn : n ≠ 0) {y : E} (hy : y ∈ ψ.target) {v : E} (hv : v ≠ 0) :
    0 < gramInChart ψ y v v := by
  rw [gramInChart_apply]
  refine real_inner_self_pos.2 fun h0 ↦ hv ?_
  have h := ψ.mfderiv_apply_mfderiv_symm_apply hn hy v
  rw [h0, map_zero] at h
  exact h.symm

/-- **The metric under a change of coordinates.** If `Θ` is a partial diffeomorphism of `E`, the
metric in the chart `ψ.trans Θ` at `w`, evaluated on the images under the derivative of `Θ` of
two vectors, is the metric in the chart `ψ` at `Θ.symm w` evaluated on those vectors. -/
theorem gramInChart_trans_apply (hn : n ≠ 0) (Θ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E n)
    {w : E} (hw : w ∈ Θ.target) (hψ : Θ.symm w ∈ ψ.target) (u v : E) :
    gramInChart (ψ.trans Θ) w (fderiv ℝ Θ (Θ.symm w) u) (fderiv ℝ Θ (Θ.symm w) v) =
      gramInChart ψ (Θ.symm w) u v := by
  have key (a : E) : mfderiv 𝓘(ℝ, E) I (ψ.trans Θ).symm w (fderiv ℝ Θ (Θ.symm w) a) =
      mfderiv 𝓘(ℝ, E) I ψ.symm (Θ.symm w) a := by
    have h := Θ.mfderiv_symm_trans_apply_mfderiv_apply ψ.symm hn (Θ.map_target hw) hψ a
    rw [Θ.right_inv hw, mfderiv_eq_fderiv] at h
    rw [coe_trans_symm, ← coe_trans]
    exact h
  rw [gramInChart_apply, gramInChart_apply, key, key]
  -- The two inner products are taken in the tangent spaces at `(ψ.trans Θ).symm w` and at
  -- `ψ.symm (Θ.symm w)`, which are the same point by definition.
  rfl

end Metric

section Smooth

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M] (ψ : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞)

/-- The metric in a chart is smooth on the target of the chart. -/
theorem contDiffOn_gramInChart
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] :
    ContDiffOn ℝ ∞ (gramInChart ψ) ψ.target := by
  refine contDiffOn_clm_apply.2 fun v ↦ contDiffOn_clm_apply.2 fun w y hy ↦ ?_
  have hψ : ContMDiffAt 𝓘(ℝ, E) I ∞ ψ.symm y :=
    ψ.symm.contMDiffAt hy
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
    (fun _ hy ↦ (ψ.posDef_gramInChart (by simp) b hy).det_pos.ne') i j

end Smooth

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

/-- The Riemannian Jacobian of `ψ.symm`, for a partial diffeomorphism `ψ` from `M` onto an open
subset of `E` and any basis of `E`, is positive on `ψ.target`. -/
theorem riemannianJacobian_symm_pos {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : PartialDiffeomorph I 𝓘(ℝ, E) M E n) (hn : n ≠ 0) (b : Module.Basis ι ℝ E) {y : E}
    (hy : y ∈ ψ.target) : 0 < TauCeti.riemannianJacobian (I := I) b ψ.symm y :=
  TauCeti.riemannianJacobian_pos b (ψ.symm.isInvertible_mfderiv hn hy).injective

/-- The Riemannian Jacobian of `ψ.symm` for a basis `b` of `E`, the square root of the determinant
of the Gram matrix of `b` for the metric in the chart, is smooth on the target of the chart. -/
theorem contDiffOn_riemannianJacobian_symm [FiniteDimensional ℝ E] [IsManifold I ∞ M]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    (ψ : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ E) :
    ContDiffOn ℝ ∞ (TauCeti.riemannianJacobian (I := I) b ψ.symm) ψ.target := by
  have h (y : E) : Matrix.gram ℝ (fun i ↦ mfderiv 𝓘(ℝ, E) I ψ.symm y (b i)) =
      Matrix.of fun i j ↦ gramInChart ψ y (b i) (b j) := by
    ext i j
    rw [Matrix.gram_apply, Matrix.of_apply, gramInChart_apply]
  have hJ : TauCeti.riemannianJacobian (I := I) b ψ.symm =
      fun y ↦ √(Matrix.of fun i j ↦ gramInChart ψ y (b i) (b j)).det := by
    ext y
    rw [TauCeti.riemannianJacobian_eq_sqrt_det_gram, h]
  rw [hJ]
  exact (ContDiffOn.matrix_det fun i j ↦ contDiffOn_clm_apply.1
    (contDiffOn_clm_apply.1 (contDiffOn_gramInChart ψ) (b i)) (b j)).sqrt
    fun y hy ↦ (ψ.posDef_gramInChart (by simp) b hy).det_pos.ne'

variable [IsManifold I 1 M] [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

/-- On a compact subset `K` of the target of a partial diffeomorphism `ψ` from `M` onto an open
subset of a finite-dimensional real normed space, the differential of `ψ.symm` is bounded above
and below: `c * ‖v‖ ≤ ‖dψ⁻¹_y v‖ ≤ C * ‖v‖` for some `0 < c`, every `y ∈ K` and every `v`, the
middle norm being the Riemannian one. -/
theorem exists_mul_norm_le_norm_mfderiv_symm_le [FiniteDimensional ℝ E]
    (ψ : PartialDiffeomorph I 𝓘(ℝ, E) M E n) (hn : n ≠ 0) {K : Set E} (hK : IsCompact K)
    (hKψ : K ⊆ ψ.target) :
    ∃ c C, 0 < c ∧ ∀ y ∈ K, ∀ v : E,
      c * ‖v‖ ≤ ‖mfderiv 𝓘(ℝ, E) I ψ.symm y v‖ ∧ ‖mfderiv 𝓘(ℝ, E) I ψ.symm y v‖ ≤ C * ‖v‖ := by
  have hn' : 1 ≤ n := ENat.one_le_iff_ne_zero_withTop.2 hn
  obtain ⟨c, hc, hcK⟩ := ψ.symm.contMDiffOn.exists_pos_mul_norm_le_norm_mfderiv hn'
    ψ.open_target hK hKψ fun y hy ↦ (ψ.symm.isInvertible_mfderiv hn (hKψ hy)).injective
  obtain ⟨C, hCK⟩ := ψ.symm.contMDiffOn.exists_norm_mfderiv_le_mul_norm hn' ψ.open_target hK hKψ
  exact ⟨c, C, hc, fun y hy v ↦ ⟨hcK y hy v, hCK y hy v⟩⟩

/-- The differential of a partial diffeomorphism `ψ` from `M` onto an open subset of a
finite-dimensional real normed space is bounded, for the Riemannian norm on the tangent spaces
of `M`, on the image under `ψ.symm` of a compact subset of `ψ.target`. -/
theorem exists_norm_mvfderiv_le_mul_norm [FiniteDimensional ℝ E]
    (ψ : PartialDiffeomorph I 𝓘(ℝ, E) M E n) (hn : n ≠ 0) {K : Set E} (hK : IsCompact K)
    (hKψ : K ⊆ ψ.target) :
    ∃ C, ∀ x ∈ ψ.symm '' K, ∀ w : TangentSpace I x, ‖mvfderiv I ψ x w‖ ≤ C * ‖w‖ := by
  obtain ⟨c, _, hc, hcK⟩ := ψ.exists_mul_norm_le_norm_mfderiv_symm_le hn hK hKψ
  refine ⟨c⁻¹, ?_⟩
  rintro _ ⟨y, hy, rfl⟩ w
  have hx : ψ.symm y ∈ ψ.source := ψ.map_target (hKψ hy)
  -- Apply the lower bound at `ψ (ψ.symm y)` rather than at `y`, so that the differential of
  -- `ψ.symm` there undoes that of `ψ` at `ψ.symm y` without moving between tangent spaces.
  have hy' : ψ (ψ.symm y) ∈ K := by simpa [ψ.toPartialEquiv.right_inv (hKψ hy)] using hy
  have key : mfderiv 𝓘(ℝ, E) I ψ.symm (ψ (ψ.symm y)) (mvfderiv I ψ (ψ.symm y) w) = w := by
    rw [mvfderiv_apply_eq_mfderiv_apply]
    exact ψ.mfderiv_symm_apply_mfderiv_apply hn hx w
  have h := (hcK _ hy' (mvfderiv I ψ (ψ.symm y) w)).1
  rw [key] at h
  calc ‖mvfderiv I ψ (ψ.symm y) w‖ = c⁻¹ * (c * ‖mvfderiv I ψ (ψ.symm y) w‖) := by field_simp
    _ ≤ c⁻¹ * ‖w‖ := mul_le_mul_of_nonneg_left
        (h.trans_eq (TauCeti.norm_tangentSpace_congr (ψ.left_inv hx) rfl)) (inv_nonneg.2 hc.le)

/-- On a compact subset `K` of the source of a partial diffeomorphism `ψ` from `M` onto an open
subset of a finite-dimensional real normed space, the differential of `ψ` is bounded above and
below: `c * ‖w‖ ≤ ‖dψ_x w‖ ≤ C * ‖w‖` for some `0 < c`, every `x ∈ K` and every tangent vector
`w` at `x`, the norm of `w` being the Riemannian one. -/
theorem exists_mul_norm_le_norm_mvfderiv_le [FiniteDimensional ℝ E]
    (ψ : PartialDiffeomorph I 𝓘(ℝ, E) M E n) (hn : n ≠ 0) {K : Set M} (hK : IsCompact K)
    (hKψ : K ⊆ ψ.source) :
    ∃ c C, 0 < c ∧ ∀ x ∈ K, ∀ w : TangentSpace I x,
      c * ‖w‖ ≤ ‖mvfderiv I ψ x w‖ ∧ ‖mvfderiv I ψ x w‖ ≤ C * ‖w‖ := by
  have hK' : IsCompact (ψ '' K) := hK.image_of_continuousOn (ψ.contMDiffOn.continuousOn.mono hKψ)
  have hKψ' : ψ '' K ⊆ ψ.target := by
    rintro _ ⟨x, hx, rfl⟩
    exact ψ.map_source (hKψ hx)
  obtain ⟨_, C', -, hC'⟩ := ψ.exists_mul_norm_le_norm_mfderiv_symm_le hn hK' hKψ'
  obtain ⟨C, hC⟩ := ψ.exists_norm_mvfderiv_le_mul_norm hn hK' hKψ'
  refine ⟨(max C' 1)⁻¹, C, by positivity, fun x hx w ↦ ⟨?_, hC x ?_ w⟩⟩
  · -- The differential of `ψ.symm` at `ψ x` undoes that of `ψ` at `x`, and is bounded by `C'`.
    have key : mfderiv 𝓘(ℝ, E) I ψ.symm (ψ x) (mvfderiv I ψ x w) = w := by
      rw [mvfderiv_apply_eq_mfderiv_apply]
      exact ψ.mfderiv_symm_apply_mfderiv_apply hn (hKψ hx) w
    have h := (hC' (ψ x) (mem_image_of_mem _ hx) (mvfderiv I ψ x w)).2
    rw [key] at h
    have h' : ‖w‖ ≤ C' * ‖mvfderiv I ψ x w‖ :=
      (TauCeti.norm_tangentSpace_congr (ψ.left_inv (hKψ hx)) rfl).symm.trans_le h
    rw [inv_mul_le_iff₀ (by positivity)]
    exact h'.trans (by gcongr; exact le_max_left _ _)
  · exact ⟨ψ x, mem_image_of_mem _ hx, ψ.left_inv (hKψ hx)⟩

/-- On a compact subset of the target of a partial diffeomorphism `ψ` from `M` onto an open
subset of `E`, the Riemannian Jacobian of `ψ.symm` in any basis of `E` is bounded above and away
from zero. -/
theorem exists_le_riemannianJacobian_symm_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : PartialDiffeomorph I 𝓘(ℝ, E) M E n) (hn : n ≠ 0) (b : Module.Basis ι ℝ E)
    {K : Set E} (hK : IsCompact K) (hKψ : K ⊆ ψ.target) :
    ∃ c C, 0 < c ∧ ∀ y ∈ K,
      c ≤ TauCeti.riemannianJacobian (I := I) b ψ.symm y ∧
        TauCeti.riemannianJacobian (I := I) b ψ.symm y ≤ C := by
  have hcont := (TauCeti.continuousOn_riemannianJacobian (I := I) b
    (ψ.symm.contMDiffOn.of_le (ENat.one_le_iff_ne_zero_withTop.2 hn)) ψ.open_target).mono hKψ
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont
  have hle (y) (hy : y ∈ K) : TauCeti.riemannianJacobian (I := I) b ψ.symm y ≤ C :=
    (le_abs_self _).trans (hC y hy)
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, C, one_pos, by simp⟩
  obtain ⟨y₀, hy₀, hmin⟩ := hK.exists_isMinOn hne hcont
  exact ⟨_, C, ψ.riemannianJacobian_symm_pos hn b (hKψ hy₀), fun y hy ↦ ⟨hmin hy, hle y hy⟩⟩

end PartialDiffeomorph

end

end
