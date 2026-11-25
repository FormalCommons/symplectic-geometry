/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import TauCeti.Analysis.Sobolev.Wkp.Classical
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Basic
public import TauCeti.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Chart components of Sobolev data with a smooth reading

Let `C : TauCeti.SectionChartData E F S` be chart data with finite-dimensional model fibre `F`,
and `w : C.SobolevData μ p k` a tuple of scalar Sobolev functions whose chart data in chart `i`
agree almost everywhere on `C.image i` with a function `f : E → F` that is `Cᵏ` on `C.image i`.
This file compares, at every order `k`, the norms of the chart-`i` components `w i j` with the
`Lᵖ` norms of the classical derivatives `iteratedFDeriv ℝ m f`, `m ≤ k`, of the vector-valued
reading `f`:

* `TauCeti.SectionChartData.norm_le_mul_sum_lpNorm_iteratedFDeriv`: `‖w i j‖` is at most the
  norm of the `j`-th coordinate functional of `Module.finBasis ℝ F` times
  `∑ m ∈ Finset.range (k + 1), lpNorm (iteratedFDeriv ℝ m f) p (μ.restrict (C.image i))`. This
  is the order-`k` form of Tau Ceti's
  `TauCeti.SectionChartData.norm_le_mul_norm_chartValueL_add_norm_chartDerivL`.
* `TauCeti.SectionChartData.memLp_iteratedFDeriv_of_chartValueL_ae_eq` and
  `TauCeti.SectionChartData.lpNorm_iteratedFDeriv_le_of_chartValueL_ae_eq`: conversely, each
  `iteratedFDeriv ℝ m f` with `m ≤ k` is in `Lᵖ` on `C.image i`, with `Lᵖ` norm at most
  `(∑ j, ‖finBasis ℝ F j‖) * ‖w i‖`.

The proofs apply Tau Ceti's scalar results
`TauCeti.Wkp.norm_le_sum_lpNorm_iteratedFDeriv_of_contDiffOn`,
`TauCeti.Wkp.lpNorm_iteratedFDeriv_le_of_contDiffOn` and
`TauCeti.Wkp.memLp_iteratedFDeriv_of_contDiffOn` to the components of `f` in the basis
`Module.finBasis ℝ F`, which are the values of the `w i j` almost everywhere
(`TauCeti.SectionChartData.value_ae_eq_repr_of_chartValueL_ae_eq`, the form for any function of
Tau Ceti's `TauCeti.SectionChartData.value_ae_eq_repr_coord`). The derivatives of `f` and of its
components are compared pointwise by `Module.Basis.norm_iteratedFDeriv_le_sum` and Mathlib's
`ContinuousLinearMap.norm_iteratedFDeriv_comp_left`.
-/

public section

noncomputable section

open MeasureTheory Module
open scoped ENNReal

universe u

namespace Module.Basis

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [FiniteDimensional 𝕜 F] {ι : Type*} [Fintype ι]

/-- The `n`-th derivative of a function `f` with values in a finite-dimensional space, at a point
where `f` is `Cⁿ`, has norm at most the sum over a basis `b` of `‖b j‖` times the norm of the
`n`-th derivative of the `j`-th coordinate `y ↦ b.repr (f y) j`. -/
theorem norm_iteratedFDeriv_le_sum (b : Basis ι 𝕜 F) {f : E → F} {x : E} {n : ℕ}
    (hf : ContDiffAt 𝕜 n f x) :
    ‖iteratedFDeriv 𝕜 n f x‖ ≤
      ∑ j, ‖b j‖ * ‖iteratedFDeriv 𝕜 n (fun y ↦ b.repr (f y) j) x‖ := by
  have hc (j : ι) : ContDiffAt 𝕜 n (fun y ↦ b.repr (f y) j) x :=
    (LinearMap.toContinuousLinearMap (b.coord j)).contDiff.contDiffAt.comp x hf
  have hf' : f = fun y ↦ ∑ j, b.repr (f y) j • b j := funext fun y ↦ (b.sum_repr (f y)).symm
  nth_rw 1 [hf']
  rw [iteratedFDeriv_fun_sum_apply (f := fun j y ↦ b.repr (f y) j • b j)
    fun j _ ↦ (hc j).smul contDiffAt_const]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ ↦ ?_)
  rw [iteratedFDeriv_smul_const_apply (hc j)]
  refine (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans ?_
  rw [ContinuousLinearMap.norm_smulRight_apply]
  gcongr
  exact mul_le_of_le_one_left (norm_nonneg _) ContinuousLinearMap.norm_id_le

end Module.Basis

namespace TauCeti

namespace SectionChartData

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {S : Type*} [AddCommGroup S] [Module ℝ S] {C : SectionChartData E F S}
  {μ : Measure E} [μ.IsAddHaarMeasure] {p : ℝ≥0∞} [Fact (1 ≤ p)] {k : ℕ}

/-- If the chart data in chart `i` of a tuple `w` agree almost everywhere with a function `f`, then
the `j`-th component of `f` in the basis `Module.finBasis ℝ F` is the value of the entry `w i j`,
almost everywhere on `C.image i`. -/
theorem value_ae_eq_repr_of_chartValueL_ae_eq {w : C.SobolevData μ p k} {i : Fin C.n}
    {f : E → F} (hw : C.chartValueL μ p k i w =ᵐ[μ.restrict (C.image i)] f)
    (j : Fin (finrank ℝ F)) :
    (Wkp.value k (w i j) : E → ℝ) =ᵐ[μ.restrict (C.image i)]
      fun y ↦ (finBasis ℝ F).repr (f y) j := by
  filter_upwards [C.chartValueL_apply_ae μ p k i w, hw] with y hy hy'
  rw [← hy', hy, (finBasis ℝ F).repr_sum_self]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The components in the basis `Module.finBasis ℝ F` of a function that is `Cᵏ` on the image of
chart `i` are `Cᵏ` there. -/
private theorem contDiffOn_repr {i : Fin C.n} {f : E → F}
    (hf : ContDiffOn ℝ k f (C.image i)) (j : Fin (finrank ℝ F)) :
    ContDiffOn ℝ k (fun y ↦ (finBasis ℝ F).repr (f y) j) (C.image i) :=
  (LinearMap.toContinuousLinearMap ((finBasis ℝ F).coord j)).contDiff.comp_contDiffOn hf

omit [FiniteDimensional ℝ E] [μ.IsAddHaarMeasure] in
/-- Almost everywhere on the image of chart `i`, the norm of the `m`-th derivative of a reading
`f` that is `Cᵏ` there, `m ≤ k`, is at most the sum over the basis `Module.finBasis ℝ F` of the
norms of the basis vectors times those of the `m`-th derivatives of the components of `f`. -/
private theorem ae_norm_iteratedFDeriv_le_sum {i : Fin C.n} {f : E → F}
    (hf : ContDiffOn ℝ k f (C.image i)) {m : ℕ} (hm : m ≤ k) :
    ∀ᵐ y ∂μ.restrict (C.image i), ‖iteratedFDeriv ℝ m f y‖ ≤
      ‖∑ j, ‖finBasis ℝ F j‖ *
        ‖iteratedFDeriv ℝ m (fun z ↦ (finBasis ℝ F).repr (f z) j) y‖‖ := by
  refine ae_restrict_of_forall_mem (C.image i).isOpen.measurableSet fun y hy ↦ ?_
  refine ((finBasis ℝ F).norm_iteratedFDeriv_le_sum
    ((hf.contDiffAt ((C.image i).isOpen.mem_nhds hy)).of_le (by exact_mod_cast hm))).trans ?_
  exact Real.le_norm_self _

/-- **The derivatives of a smooth reading are in `Lᵖ`.** If the chart data in chart `i` of
`w : C.SobolevData μ p k` agree almost everywhere on `C.image i` with a function `f` that is `Cᵏ`
there, then every derivative `iteratedFDeriv ℝ m f` with `m ≤ k` is in `Lᵖ` on `C.image i`. -/
theorem memLp_iteratedFDeriv_of_chartValueL_ae_eq {i : Fin C.n} (w : C.SobolevData μ p k)
    {f : E → F} (hf : ContDiffOn ℝ k f (C.image i))
    (hw : C.chartValueL μ p k i w =ᵐ[μ.restrict (C.image i)] f) :
    ∀ m ≤ k, MemLp (iteratedFDeriv ℝ m f) p (μ.restrict (C.image i)) := fun m hm ↦
  (memLp_finsetSum _ fun j _ ↦
    ((Wkp.memLp_iteratedFDeriv_of_contDiffOn k (w i j) (contDiffOn_repr hf j)
      (value_ae_eq_repr_of_chartValueL_ae_eq hw j) m hm).norm.const_mul _)).of_le
    ((ContinuousOn.continuousOn_iteratedFDeriv hf (C.image i).isOpen
      (by exact_mod_cast hm)).aestronglyMeasurable (C.image i).isOpen.measurableSet)
    (ae_norm_iteratedFDeriv_le_sum hf hm)

/-- **The derivatives of a smooth reading are bounded by the components.** If the chart data in
chart `i` of `w : C.SobolevData μ p k` agree almost everywhere on `C.image i` with a function `f`
that is `Cᵏ` there, then for every `m ≤ k` the `Lᵖ` norm of `iteratedFDeriv ℝ m f` on `C.image i`
is at most the sum of the norms of the vectors of `Module.finBasis ℝ F` times the norm of the
chart-`i` part `w i` of the tuple. -/
theorem lpNorm_iteratedFDeriv_le_of_chartValueL_ae_eq {i : Fin C.n} (w : C.SobolevData μ p k)
    {f : E → F} (hf : ContDiffOn ℝ k f (C.image i))
    (hw : C.chartValueL μ p k i w =ᵐ[μ.restrict (C.image i)] f) :
    ∀ m ≤ k, lpNorm (iteratedFDeriv ℝ m f) p (μ.restrict (C.image i)) ≤
      (∑ j, ‖finBasis ℝ F j‖) * ‖w i‖ := by
  intro m hm
  set ν := μ.restrict (C.image i)
  set g := fun j : Fin (finrank ℝ F) ↦ fun z ↦ (finBasis ℝ F).repr (f z) j
  have hmem (j : Fin (finrank ℝ F)) : MemLp (iteratedFDeriv ℝ m (g j)) p ν :=
    Wkp.memLp_iteratedFDeriv_of_contDiffOn k (w i j) (contDiffOn_repr hf j)
      (value_ae_eq_repr_of_chartValueL_ae_eq hw j) m hm
  set φ := fun j y ↦ ‖iteratedFDeriv ℝ m (g j) y‖
  have hmem' (j : Fin (finrank ℝ F)) : MemLp (‖finBasis ℝ F j‖ • φ j) p ν :=
    (hmem j).norm.const_smul _
  calc lpNorm (iteratedFDeriv ℝ m f) p ν
      ≤ 1 * lpNorm (∑ j, ‖finBasis ℝ F j‖ • φ j) p ν :=
        lpNorm_le_mul_lpNorm_of_ae_le_mul
          ((ContinuousOn.continuousOn_iteratedFDeriv hf (C.image i).isOpen
            (by exact_mod_cast hm)).aestronglyMeasurable (C.image i).isOpen.measurableSet)
          (memLp_finsetSum' _ fun j _ ↦ hmem' j)
          ((ae_norm_iteratedFDeriv_le_sum hf hm).mono fun y hy ↦ by
            simpa [φ, g, Finset.sum_apply] using hy)
    _ ≤ ∑ j, lpNorm (‖finBasis ℝ F j‖ • φ j) p ν := by
        rw [one_mul]
        exact lpNorm_sum_le (fun j _ ↦ hmem' j) Fact.out
    _ = ∑ j, ‖finBasis ℝ F j‖ * lpNorm (iteratedFDeriv ℝ m (g j)) p ν := by
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [lpNorm_const_smul, coe_nnNorm, norm_norm, lpNorm_norm (hmem j).aestronglyMeasurable]
    _ ≤ ∑ j, ‖finBasis ℝ F j‖ * ‖w i‖ := by
        gcongr with j
        exact (Wkp.lpNorm_iteratedFDeriv_le_of_contDiffOn k (w i j) (contDiffOn_repr hf j)
          (value_ae_eq_repr_of_chartValueL_ae_eq hw j) m hm).trans (norm_le_pi_norm (w i) j)
    _ = (∑ j, ‖finBasis ℝ F j‖) * ‖w i‖ := (Finset.sum_mul ..).symm

/-- **The components are controlled by the derivatives of a smooth reading.** If the chart data
in chart `i` of `w : C.SobolevData μ p k` agree almost everywhere on `C.image i` with a function
`f` that is `Cᵏ` there, then the norm of the `j`-th chart-`i` component `w i j` is at most the norm
of the `j`-th coordinate functional of `Module.finBasis ℝ F` times the sum of the `Lᵖ` norms on
`C.image i` of the derivatives of `f` of orders `0` through `k`. -/
theorem norm_le_mul_sum_lpNorm_iteratedFDeriv {i : Fin C.n} (w : C.SobolevData μ p k)
    (j : Fin (finrank ℝ F)) {f : E → F} (hf : ContDiffOn ℝ k f (C.image i))
    (hw : C.chartValueL μ p k i w =ᵐ[μ.restrict (C.image i)] f) :
    ‖w i j‖ ≤ ‖LinearMap.toContinuousLinearMap ((finBasis ℝ F).coord j)‖ *
      ∑ m ∈ Finset.range (k + 1), lpNorm (iteratedFDeriv ℝ m f) p (μ.restrict (C.image i)) := by
  set c := LinearMap.toContinuousLinearMap ((finBasis ℝ F).coord j)
  refine (Wkp.norm_le_sum_lpNorm_iteratedFDeriv_of_contDiffOn k (w i j) (contDiffOn_repr hf j)
    (value_ae_eq_repr_of_chartValueL_ae_eq hw j)).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun m hm ↦ ?_
  have hm : m ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
  refine lpNorm_le_mul_lpNorm_of_ae_le_mul
    ((ContinuousOn.continuousOn_iteratedFDeriv (contDiffOn_repr hf j) (C.image i).isOpen
      (by exact_mod_cast hm)).aestronglyMeasurable (C.image i).isOpen.measurableSet)
    (memLp_iteratedFDeriv_of_chartValueL_ae_eq w hf hw m hm)
    (ae_restrict_of_forall_mem (C.image i).isOpen.measurableSet fun y hy ↦ ?_)
  exact c.norm_iteratedFDeriv_comp_left
    ((hf.contDiffAt ((C.image i).isOpen.mem_nhds hy)).of_le (by exact_mod_cast hm)) le_rfl

end SectionChartData

end TauCeti

end
