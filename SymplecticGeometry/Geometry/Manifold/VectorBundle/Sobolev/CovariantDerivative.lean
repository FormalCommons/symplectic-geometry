/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.VectorBundle.FiniteBundleAtlas.CovariantDerivative.Chart
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Sobolev.LowerOrder
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Sobolev.TangentHom
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.ContMDiffSection
import TauCeti.Analysis.Calculus.FDeriv.ContinuousLinearMap
import TauCeti.Analysis.Sobolev.Wkp.SmoothCoefficients
import TauCeti.Geometry.Manifold.VectorBundle.FiniteBundleAtlas.Transfer
import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Transfer

/-!
# The Sobolev realization of a smooth covariant derivative

Let `M` be a smooth boundaryless manifold whose model `E` is a finite-dimensional real inner
product space, and let `V → M` be a smooth real vector bundle with finite-dimensional model fibre
`F` and a finite bundle atlas `A`. A smooth covariant derivative `cov` on `V` extends to a bounded
operator

`W^{k+1,p}(M, V) → W^{k,p}(M, T*M ⊗ V)`

from the Sobolev sections `TauCeti.SobolevSection A μ p (k + 1)` of `V` to the Sobolev sections
`TauCeti.SobolevSection A.tangentHom μ p k` of `V`-valued one-forms, for every order `k` and every
`1 ≤ p ≤ ∞` (`IsCovariantDerivativeOn.sobolevL`).

In chart `i` a smooth section with reading `sᵢ` is sent to `d sᵢ + Γᵢ sᵢ`, where `Γᵢ` is the
zeroth-order term `TauCeti.FiniteBundleAtlas.chartZeroOrder` of `cov` in chart `i`
(`IsCovariantDerivativeOn.coord_tangentHom_eq_fderiv_add_chartZeroOrder`). The realization applies
the same formula to the chart data `uᵢ` of a Sobolev section, with the weak derivative of `uᵢ`,
whose components are Sobolev functions of order `k`
(`TauCeti.SectionChartData.chartDerivDataL`), in place of the derivative
(`IsCovariantDerivativeOn.chartValueL_sobolevL_ae`). Since `Γᵢ` is smooth on a neighbourhood of
the compact closure of the chart image, multiplication by it is bounded on Sobolev functions of
order `k` (`TauCeti.Wkp.contDiffOnCLMApplyL`).

These chart data are the components of a one-form: on the overlap of two charts, the weak
derivative of `uᵢ'` is computed from that of `uᵢ` by the weak chain rule under the chart transition
and the weak Leibniz rule for the coordinate change `g` of `V`
(`TauCeti.FiniteBundleAtlas.chartDerivL_ae_overlap`), and the term `d g` this produces is the one
by which the zeroth-order terms of the two charts differ
(`IsCovariantDerivativeOn.fderiv_coordChangeL_add_chartZeroOrder`). On sections of class
`C^{k+1}` the realization is `cov`
(`IsCovariantDerivativeOn.chartValueL_sobolevL_ofContMDiffSection_ae`).

The construction adapts Tau Ceti's `TauCeti.IsRealCauchyRiemannOperator.sobolevL`,
`TauCeti.IsRealCauchyRiemannOperator.zeroOrderL`
(`Geometry/Manifold/VectorBundle/Sobolev/CauchyRiemann/Basic.lean`) and
`TauCeti.IsRealCauchyRiemannOperator.sobolevSuccL`
(`Geometry/Manifold/VectorBundle/Sobolev/CauchyRiemann/HigherOrder.lean`), the realization of a
real Cauchy–Riemann operator on a complex curve, from the complex antilinear part of the derivative
to the whole derivative, and from the model `ℂ` to any finite-dimensional inner product space.
Unlike `sobolevSuccL`, which reduces membership in the Sobolev sections to the order-one
realization, the cocycle relation is proved here directly at every order, from the order-one
relation of the section regarded as one of order one
(`TauCeti.SectionChartData.toOrderOne`). The proofs of
`IsCovariantDerivativeOn.chartValueL_sobolevL_ofContMDiffSection_ae` and
`IsCovariantDerivativeOn.lowerOrderL_sobolevL` follow those of
`TauCeti.IsRealCauchyRiemannOperator.chartValueL_sobolevSuccL_ofContMDiffSection_ae` and
`TauCeti.IsRealCauchyRiemannOperator.zeroOneLowerOrdersL_sobolevSuccL_add`.

## Main definitions

* `IsCovariantDerivativeOn.zeroOrderL`: the zeroth-order term of `cov` in a chart, as a bounded map
  from order-`k + 1` chart data to order-`k` components.
* `IsCovariantDerivativeOn.sobolevL`: the bounded realization of a smooth covariant derivative
  from `W^{k+1,p}` sections to `W^{k,p}` one-forms.

## Main results

* `IsCovariantDerivativeOn.chartValueL_sobolevL_ae`: in chart `i` the realization is
  `Duᵢ + Γᵢ uᵢ`, for any weak derivative `Duᵢ` of the chart data `uᵢ`.
* `IsCovariantDerivativeOn.chartValueL_sobolevL_ofContMDiffSection_ae`: on `C^{k+1}` sections the
  realization is `cov`.
* `IsCovariantDerivativeOn.lowerOrderL_sobolevL`: the realizations at orders `k + 1` and `k`
  commute with forgetting the highest weak derivative.

## References

* [D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*][McDuffSalamon2012],
  Appendix C.1 and C.2.
-/

public section

noncomputable section

open Bundle MeasureTheory Module Set TopologicalSpace TauCeti TauCeti.FiniteBundleAtlas
open scoped Manifold ENNReal ContDiff

universe u

namespace IsCovariantDerivativeOn

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, E)]
  (A : FiniteBundleAtlas E M F V)
  {cov : (Π x : M, V x) → Π x : M, TangentSpace 𝓘(ℝ, E) x →L[ℝ] V x}
  (hcov : IsCovariantDerivativeOn F cov univ)
  (hcovs : ContMDiffCovariantDerivativeOn F ∞ cov univ)
  (μ : Measure E) [μ.IsAddHaarMeasure] (p : ℝ≥0∞) [Fact (1 ≤ p)] (k : ℕ)

/-! ### The zeroth-order term -/

include hcov hcovs in
/-- The zeroth-order term `Γᵢ` of `cov` in chart `i`, applied at order `k` to the components of a
tuple of order `k + 1`: the multiplier `TauCeti.Wkp.contDiffOnCLMApplyL` by the smooth operator
coefficient `TauCeti.FiniteBundleAtlas.chartZeroOrder`, after forgetting the highest derivative of
each component. -/
def zeroOrderL (i : Fin A.n) :
    A.sectionChartData.SobolevData μ p (k + 1) →L[ℝ]
      (Fin (finrank ℝ (E →L[ℝ] F)) → Wkp μ (A.sectionChartData.image i) p k) :=
  (Wkp.contDiffOnCLMApplyL (Omega := A.sectionChartData.image i)
    ((A.chart i).isOpen_inter_preimage_symm (A.triv i).open_baseSet).uniqueDiffOn
    (A.isCompact_closure_image i)
    ((A.closure_image_subset_chart_image_closure_dom i).trans
      (A.chart_image_closure_dom_subset i)) k (finBasis ℝ F) (finBasis ℝ (E →L[ℝ] F))
    (by simpa only [inter_univ] using hcov.contDiffOn_chartZeroOrder A hcovs isOpen_univ i)).comp
    ((ContinuousLinearMap.piMap fun _ : Fin (finrank ℝ F) ↦ Wkp.lowerOrderL k).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun i : Fin A.sectionChartData.n ↦
        ∀ _ : Fin (finrank ℝ F), Wkp μ (A.sectionChartData.image i) p (k + 1)) i))

/-- The components of the zeroth-order term are, almost everywhere, those of the operator
coefficient `Γᵢ` applied to the chart data. -/
theorem zeroOrderL_apply_ae (i : Fin A.n) (w : A.sectionChartData.SobolevData μ p (k + 1)) :
    ∀ᵐ y ∂μ.restrict (A.sectionChartData.image i), ∀ c,
      Wkp.value k (hcov.zeroOrderL A hcovs μ p k i w c) y =
        (finBasis ℝ (E →L[ℝ] F)).repr (A.chartZeroOrder cov i y
          (A.sectionChartData.chartValueL μ p (k + 1) i w y)) c := by
  refine ae_all_iff.2 fun c ↦ ?_
  have hvalues :
      (ContinuousLinearMap.piMap fun _ : Fin (finrank ℝ F) ↦ Wkp.lowerOrderL
        (mu := μ) (Omega := A.sectionChartData.image i) (p := p) k)
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun i : Fin A.sectionChartData.n ↦
          ∀ _ : Fin (finrank ℝ F), Wkp μ (A.sectionChartData.image i) p (k + 1)) i) w) =
        fun j ↦ Wkp.lowerOrderL k (w i j) := by
    funext j
    simp only [ContinuousLinearMap.coe_piMap', Pi.map_apply]
    -- The explicit chart-data index keeps the product-space instances aligned.
    exact congrArg (fun u : Fin (finrank ℝ F) → Wkp μ (A.sectionChartData.image i) p (k + 1) ↦
      Wkp.lowerOrderL k (u j)) (ContinuousLinearMap.proj_apply (R := ℝ)
        (φ := fun i : Fin A.sectionChartData.n ↦
          ∀ _ : Fin (finrank ℝ F), Wkp μ (A.sectionChartData.image i) p (k + 1)) i w)
  have hz := Wkp.value_contDiffOnCLMApplyL_ae (mu := μ) (Omega := A.sectionChartData.image i)
    (p := p) (g := A.chartZeroOrder cov i)
    ((A.chart i).isOpen_inter_preimage_symm (A.triv i).open_baseSet).uniqueDiffOn
    (A.isCompact_closure_image i)
    ((A.closure_image_subset_chart_image_closure_dom i).trans
      (A.chart_image_closure_dom_subset i)) k (finBasis ℝ F) (finBasis ℝ (E →L[ℝ] F))
    (by simpa only [inter_univ] using hcov.contDiffOn_chartZeroOrder A hcovs isOpen_univ i)
    (fun j ↦ Wkp.lowerOrderL k (w i j)) c
  filter_upwards [hz, A.sectionChartData.chartValueL_apply_ae μ p k i
    (fun i j ↦ Wkp.lowerOrderL k (w i j))] with y hy hv
  simp only [zeroOrderL, ContinuousLinearMap.comp_apply, hvalues, hy,
    ← A.sectionChartData.chartValueL_lowerOrderL μ p k i w, hv]

/-! ### The realization -/

/-- The `c`th component in chart `i` of the realization: the `c`th component of the weak
derivative of `uᵢ` plus that of the zeroth-order term applied to `uᵢ`. -/
private def chartL (i : Fin A.n) (c : Fin (finrank ℝ (E →L[ℝ] F))) :
    A.sectionChartData.SobolevData μ p (k + 1) →L[ℝ] Wkp μ (A.sectionChartData.image i) p k :=
  (ContinuousLinearMap.proj c).comp (A.sectionChartData.chartDerivDataL μ p k i) +
    (ContinuousLinearMap.proj c).comp (hcov.zeroOrderL A hcovs μ p k i)

private theorem chartL_apply (i : Fin A.n) (c : Fin (finrank ℝ (E →L[ℝ] F)))
    (w : A.sectionChartData.SobolevData μ p (k + 1)) :
    chartL A hcov hcovs μ p k i c w =
      A.sectionChartData.chartDerivDataL μ p k i w c + hcov.zeroOrderL A hcovs μ p k i w c :=
  rfl

/-- The components of the realization, before restricting to Sobolev sections. -/
private def dataL :
    A.sectionChartData.SobolevData μ p (k + 1) →L[ℝ]
      A.tangentHom.sectionChartData.SobolevData μ p k :=
  ContinuousLinearMap.pi fun i ↦ ContinuousLinearMap.pi fun c ↦
    (Wkp.restrictL (sectionChartData_image_tangentHom A i).le k).comp
      (chartL A hcov hcovs μ p k i c)

private theorem dataL_apply (w : A.sectionChartData.SobolevData μ p (k + 1)) (i : Fin A.n)
    (c : Fin (finrank ℝ (E →L[ℝ] F))) :
    dataL A hcov hcovs μ p k w i c =
      Wkp.restrictL (sectionChartData_image_tangentHom A i).le k
        (chartL A hcov hcovs μ p k i c w) :=
  rfl

/-- In chart `i`, the chart data of the components of the realization of `w` are `Duᵢ + Γᵢ uᵢ`
almost everywhere, for the weak derivative `Duᵢ` of the chart data `uᵢ` of `w` assembled from its
components `chartDerivDataL`. -/
private theorem chartValueL_dataL_ae (w : A.sectionChartData.SobolevData μ p (k + 1))
    (i : Fin A.n) :
    A.tangentHom.sectionChartData.chartValueL μ p k i (dataL A hcov hcovs μ p k w)
      =ᵐ[μ.restrict (A.image i)] fun y ↦
        (∑ a, Wkp.value k (A.sectionChartData.chartDerivDataL μ p k i w a) y •
          finBasis ℝ (E →L[ℝ] F) a) +
        A.chartZeroOrder cov i y (A.sectionChartData.chartValueL μ p (k + 1) i w y) := by
  have h₀ := (ae_image_tangentHom_iff' A μ i).1
    (A.tangentHom.sectionChartData.chartValueL_apply_ae μ p k i (dataL A hcov hcovs μ p k w))
  have hres := (ae_image_tangentHom_iff' A μ i).1 <| ae_all_iff.2 fun c ↦
    Wkp.value_restrictL_ae (sectionChartData_image_tangentHom A i).le k
      (chartL A hcov hcovs μ p k i c w)
  have hadd (c : Fin (finrank ℝ (E →L[ℝ] F))) := Wkp.value_add_ae k
    (A.sectionChartData.chartDerivDataL μ p k i w c) (hcov.zeroOrderL A hcovs μ p k i w c)
  filter_upwards [h₀, hres, ae_all_iff.2 hadd, hcov.zeroOrderL_apply_ae A hcovs μ p k i w]
    with y h₁ h₂ h₃ h₄
  rw [h₁]
  have hc (c : Fin (finrank ℝ (E →L[ℝ] F))) :
      Wkp.value k ((dataL A hcov hcovs μ p k w) i c) y =
        Wkp.value k (A.sectionChartData.chartDerivDataL μ p k i w c) y +
          (finBasis ℝ (E →L[ℝ] F)).repr (A.chartZeroOrder cov i y
            (A.sectionChartData.chartValueL μ p (k + 1) i w y)) c := by
    rw [dataL_apply, h₂ c, chartL_apply]
    refine (h₃ c).trans ?_
    rw [Pi.add_apply, h₄ c]
  simp_rw [hc, add_smul, Finset.sum_add_distrib, Basis.sum_repr]

include hcov in
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [T2Space M] in
/-- The pointwise identity behind the cocycle relation of the realization: if
`X' = g ∘ X ∘ dτ + (d g) v` and `v' = g v`, then `X' + Γᵢ' v' = g ∘ (X + Γᵢ v) ∘ dτ`. -/
private theorem chartData_overlap_eq {i i' : Fin A.n} {y : E} (hy : y ∈ A.overlap i i')
    {X X' : E →L[ℝ] F} {v v' : F}
    (hX : X' = ((A.triv i).coordChangeL ℝ (A.triv i') ((A.chart i').symm y) : F →L[ℝ] F).comp
        (X.comp (fderiv ℝ (A.transition i i') y)) +
      (fderiv ℝ (fun z ↦ ((A.triv i).coordChangeL ℝ (A.triv i') ((A.chart i').symm z) :
        F →L[ℝ] F)) y).flip v)
    (hv : v' = ((A.triv i).coordChangeL ℝ (A.triv i') ((A.chart i').symm y) : F →L[ℝ] F) v) :
    X' + A.chartZeroOrder cov i' y v' =
      ((A.triv i).coordChangeL ℝ (A.triv i') ((A.chart i').symm y) : F →L[ℝ] F).comp
        ((X + A.chartZeroOrder cov i (A.transition i i' y) v).comp
          (fderiv ℝ (A.transition i i') y)) := by
  have hcoord := (A.contDiffOn_coordChangeL_transferDomain (n := 1) i i').mono
    (A.overlap_subset_transferDomain i i')
  have hd : DifferentiableAt ℝ (fun z ↦ ((A.triv i).coordChangeL ℝ (A.triv i')
      ((A.chart i').symm z) : F →L[ℝ] F)) y :=
    (hcoord.differentiableOn one_ne_zero y hy).differentiableAt
      ((A.isOpen_overlap i i').mem_nhds hy)
  have hfd : fderiv ℝ (fun z ↦ (A.triv i).coordChangeL ℝ (A.triv i') ((A.chart i').symm z) v) y =
      (fderiv ℝ (fun z ↦ ((A.triv i).coordChangeL ℝ (A.triv i') ((A.chart i').symm z) :
        F →L[ℝ] F)) y).flip v := by
    ext u
    exact fderiv_clm_apply_const_apply hd v u
  -- The change-of-chart identity, with the coordinate change applied as a linear map.
  have key : fderiv ℝ
        (fun z ↦ (A.triv i).coordChangeL ℝ (A.triv i') ((A.chart i').symm z) v) y +
      A.chartZeroOrder cov i' y (((A.triv i).coordChangeL ℝ (A.triv i') ((A.chart i').symm y) :
        F →L[ℝ] F) v) =
      ((A.triv i).coordChangeL ℝ (A.triv i') ((A.chart i').symm y) : F →L[ℝ] F).comp
        ((A.chartZeroOrder cov i (A.transition i i' y) v).comp (fderiv ℝ (A.transition i i') y)) :=
    (hcov.mono (subset_univ _)).fderiv_coordChangeL_add_chartZeroOrder A
      (hcov.mono (subset_univ _)) hy v
  rw [hX, hv, add_assoc, ← hfd, key, ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]

include hcov in
/-- **The cocycle relation.** The chart data of the realization of a Sobolev section of order
`k + 1` satisfy the cocycle relation of one-forms on the overlap of every two charts. -/
private theorem compatible_dataL (w : SobolevSection A μ p (k + 1)) (i i' : Fin A.n) :
    A.tangentHom.sectionChartData.Compatible μ p k (dataL A hcov hcovs μ p k w) i i' := by
  have hC := A.aeTransition_sectionChartData μ
  have h₁ := ae_restrict_of_ae_restrict_of_subset (A.overlap_subset_image i i')
    (chartValueL_dataL_ae A hcov hcovs μ p k w i')
  have h₂ := (A.sectionChartData.aeTransition_iff.1 hC) (i := i) (i' := i')
    (chartValueL_dataL_ae A hcov hcovs μ p k w i)
  have h₃ := (A.sectionChartData.compatible_iff μ p 1).1
    (SectionChartData.compatible_of_mem hC (A.sectionChartData.toOrderOne μ p k w).property i i')
  have h₅ := ae_restrict_of_ae_restrict_of_subset (A.overlap_subset_image i i')
    (A.sectionChartData.sum_value_chartDerivDataL_ae_eq_chartDerivL_toOrderOne μ p k i' w).symm
  have h₆ := (A.sectionChartData.aeTransition_iff.1 hC) (i := i) (i' := i')
    (A.sectionChartData.sum_value_chartDerivDataL_ae_eq_chartDerivL_toOrderOne μ p k i w).symm
  refine (A.tangentHom.sectionChartData.compatible_iff μ p k).2 ?_
  refine (ae_overlap_tangentHom_iff' A μ i i').2 ?_
  filter_upwards [h₁, h₂, h₃,
    chartDerivL_ae_overlap A μ p (A.sectionChartData.toOrderOne μ p k w) i i', h₅, h₆,
    ae_restrict_mem (A.isOpen_overlap i i').measurableSet] with y h₁ h₂ h₃ h₄ h₅ h₆ hy
  rw [A.sectionChartData_transition_of_mem hy] at h₂ h₆
  rw [A.sectionChartData_coordChange_of_mem hy, A.sectionChartData_transition_of_mem hy,
    A.sectionChartData.chartValueL_toOrderOne μ p k w i,
    A.sectionChartData.chartValueL_toOrderOne μ p k w i'] at h₃
  rw [h₅, h₆, A.sectionChartData.chartValueL_toOrderOne μ p k w i] at h₄
  rw [sectionChartData_transition_tangentHom' A hy,
    sectionChartData_coordChange_tangentHom_apply' A hy, h₁, h₂]
  exact chartData_overlap_eq A hcov hy h₄ h₃

include hcov in
/-- The components of the realization of a Sobolev section of order `k + 1` are those of a
`V`-valued one-form of order `k`. -/
private theorem dataL_mem (w : SobolevSection A μ p (k + 1)) :
    dataL A hcov hcovs μ p k w ∈ A.tangentHom.sectionChartData.sobolevSections μ p k :=
  (SectionChartData.mem_sobolevSections_iff_forall_compatible
    (A.tangentHom.aeTransition_sectionChartData μ)).2 fun i i' ↦
      compatible_dataL A hcov hcovs μ p k w i i'

include hcov in
/-- **The Sobolev realization of a smooth covariant derivative** `cov` on `V`, as a bounded
operator `W^{k+1,p}(M, V) → W^{k,p}(M, T*M ⊗ V)` from the Sobolev sections of `V` to those of
`V`-valued one-forms, for every order `k` and `1 ≤ p ≤ ∞`. In chart `i` it sends a Sobolev section
with chart data `uᵢ` to `Duᵢ + Γᵢ uᵢ`, for the weak derivative `Duᵢ` of `uᵢ` and the zeroth-order
term `Γᵢ` of `cov` in chart `i` (`IsCovariantDerivativeOn.chartValueL_sobolevL_ae`). -/
def sobolevL : SobolevSection A μ p (k + 1) →L[ℝ] SobolevSection A.tangentHom μ p k :=
  ((dataL A hcov hcovs μ p k).comp
    (A.sectionChartData.sobolevSections μ p (k + 1)).subtypeL).codRestrict
      (A.tangentHom.sectionChartData.sobolevSections μ p k) (dataL_mem A hcov hcovs μ p k)

/-- The underlying tuple of the realization of a Sobolev section is `dataL`. -/
private theorem coe_sobolevL (w : SobolevSection A μ p (k + 1)) :
    ((hcov.sobolevL A hcovs μ p k w : SobolevSection A.tangentHom μ p k) :
      A.tangentHom.sectionChartData.SobolevData μ p k) = dataL A hcov hcovs μ p k w :=
  rfl

/-- **The chart formula of the realization.** In chart `i`, the realization of a Sobolev section
of order `k + 1` with chart data `uᵢ` is `Duᵢ + Γᵢ uᵢ` almost everywhere on the image of the
chart, for any weak derivative `Duᵢ` of `uᵢ` and the zeroth-order term `Γᵢ` of `cov` in chart
`i`. -/
theorem chartValueL_sobolevL_ae (w : SobolevSection A μ p (k + 1)) {i : Fin A.n}
    {Du : E → E →L[ℝ] F}
    (hDu : HasWeakFDerivOn μ (A.image i) (A.sectionChartData.chartValueL μ p (k + 1) i w) Du) :
    A.tangentHom.sectionChartData.chartValueL μ p k i
        ((hcov.sobolevL A hcovs μ p k w : SobolevSection A.tangentHom μ p k) :
          A.tangentHom.sectionChartData.SobolevData μ p k)
      =ᵐ[μ.restrict (A.image i)] fun y ↦ Du y +
        A.chartZeroOrder cov i y (A.sectionChartData.chartValueL μ p (k + 1) i w y) := by
  rw [coe_sobolevL]
  filter_upwards [chartValueL_dataL_ae A hcov hcovs μ p k w i,
    (A.sectionChartData.hasWeakFDerivOn_chartValueL_chartDerivDataL μ p k i w).ae_eq hDu]
    with y h hy
  rw [← hy]
  exact h

/-- **Agreement on smooth sections.** The realization of `cov` sends the Sobolev section of a
`C^{k+1}` section `s` to the one-form whose chart data are the readings of `cov s`. -/
theorem chartValueL_sobolevL_ofContMDiffSection_ae
    (s : Cₛ^((k + 1 : ℕ) : WithTop ℕ∞)⟮𝓘(ℝ, E); F, V⟯) (i : Fin A.n) :
    A.tangentHom.sectionChartData.chartValueL μ p k i
        ((hcov.sobolevL A hcovs μ p k (SobolevSection.ofContMDiffSection A μ p (k + 1) s) :
          SobolevSection A.tangentHom μ p k) : A.tangentHom.sectionChartData.SobolevData μ p k)
      =ᵐ[μ.restrict (A.image i)] A.tangentHom.coord i (cov s) := by
  have hcoord := SobolevSection.chartValueL_ofContMDiffSection_ae A μ p (k + 1) s i
  have hc : ContDiffOn ℝ 1 (A.coord i s) (A.image i) :=
    ((A.contDiffOn_coord s.contMDiff i).of_le (by exact_mod_cast Nat.le_add_left 1 k)).mono
      ((A.image_subset_chart_image_closure_dom i).trans (A.chart_image_closure_dom_subset i))
  filter_upwards [hcov.chartValueL_sobolevL_ae A hcovs μ p k _
      ((hc.hasWeakFDerivOn_fderiv (μ := μ) (Ω := A.image i)).congr_ae hcoord.symm),
    hcoord, ae_restrict_mem (A.image i).isOpen.measurableSet] with y h hc' hy
  rw [h, hc']
  exact ((hcov.mono (subset_univ _)).coord_tangentHom_eq_fderiv_add_chartZeroOrder A hy
    ((s.contMDiff _).mdifferentiableAt (by simp))).symm

/-- **Compatibility with the order.** Forgetting the highest weak derivative of the realization of
a Sobolev section of order `k + 2` gives the realization of the section regarded as one of order
`k + 1`. -/
@[simp]
theorem lowerOrderL_sobolevL (w : SobolevSection A μ p (k + 1 + 1)) :
    A.tangentHom.sectionChartData.lowerOrderL μ p k (hcov.sobolevL A hcovs μ p (k + 1) w) =
      hcov.sobolevL A hcovs μ p k (A.sectionChartData.lowerOrderL μ p (k + 1) w) := by
  refine SectionChartData.eq_of_chartValueL_ae_eq fun (i : Fin A.n) ↦
    (ae_image_tangentHom_iff' A μ i).2 ?_
  have hDu := A.sectionChartData.hasWeakFDerivOn_chartValueL_chartDerivDataL μ p (k + 1) i w
  have hlow := A.sectionChartData.chartValueL_coe_lowerOrderL μ p (k + 1) w i
  have hDu' : HasWeakFDerivOn μ (A.image i) (A.sectionChartData.chartValueL μ p (k + 1) i
      (A.sectionChartData.lowerOrderL μ p (k + 1) w)) _ := hlow ▸ hDu
  have hcoe : A.tangentHom.sectionChartData.chartValueL μ p k i
      ((A.tangentHom.sectionChartData.lowerOrderL μ p k (hcov.sobolevL A hcovs μ p (k + 1) w) :
        SobolevSection A.tangentHom μ p k) : A.tangentHom.sectionChartData.SobolevData μ p k) =
      A.tangentHom.sectionChartData.chartValueL μ p (k + 1) i
        ((hcov.sobolevL A hcovs μ p (k + 1) w : SobolevSection A.tangentHom μ p (k + 1)) :
          A.tangentHom.sectionChartData.SobolevData μ p (k + 1)) :=
    A.tangentHom.sectionChartData.chartValueL_coe_lowerOrderL μ p k _ i
  rw [hcoe]
  filter_upwards [hcov.chartValueL_sobolevL_ae A hcovs μ p (k + 1) w hDu,
    hcov.chartValueL_sobolevL_ae A hcovs μ p k _ hDu'] with y h₁ h₂
  rw [h₁, h₂, hlow]

end IsCovariantDerivativeOn

end
