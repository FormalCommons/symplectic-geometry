/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Measure
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.TopForm
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Operations
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Regularity
import TauCeti.Geometry.Manifold.ExtChartAt

/-!
# Integrating a top form against its measure

A top form `φ` on a `k`-dimensional manifold `M` has a measure `|φ|`
(`TauCeti.RoughForm.measure`), which uses no orientation. On an oriented manifold, a continuous
top form `φ` that is nonnegative on the positively oriented bases of each tangent space and
nonpositive on the negatively oriented ones has the same chart coefficients, with the signs of
the orientation, as `|φ|` has densities. Hence integrating the top form `f • φ` against the
orientation is integrating `f` against `|φ|`:

`∫_M f φ = ∫ f d|φ|`

for every continuous compactly supported function `f`
(`TauCeti.integralTopForm_smul_eq_integral_measure`).

In positive dimension the sign condition on negatively oriented bases follows from the one on
positively oriented bases. In dimension `0` the tangent space has only one basis, and it may be
negatively oriented, so the condition is stated with the relative sign
`Orientation.signBasis (o.orientationAt x) c`, which makes the theorem hold in every dimension.

The proof is that of `TauCeti.integralTopForm_smul_riemannianVolumeForm`
(`TauCeti/Geometry/Manifold/Riemannian/VolumeForm/Measure.lean`), for an arbitrary top form in
place of the Riemannian volume form: both integrals are sums of chart integrals over the
disjointed pieces of a chart cover of the support of `f`. The integral against `|φ|` over a
piece is computed in coordinates by `TauCeti.RoughForm.setIntegral_measure_of_subset`, whose
proof is that of `TauCeti.setIntegral_chartRiemannianVolume`. The sign of a chart coefficient is
read off as in the proof of `TauCeti.integralTopForm_nonneg`, from the compatibility of the chart
signs of an orientation lift.

## Main results

* `TauCeti.RoughForm.setIntegral_measure_of_subset`: the integral against `|φ|` over a
  measurable subset of a chart source, in coordinates.
* `TauCeti.signBasis_mul_signedInChartAt_eq_abs`: for a form nonnegative for the orientation,
  the signed chart coefficient is the absolute value of the chart coefficient.
* `TauCeti.integralTopForm_smul_eq_integral_measure`: `∫_M f φ = ∫ f d|φ|`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Chapter 16
  (integration of top forms and of densities).
-/

public section

noncomputable section

open Module MeasureTheory Set
open scoped ENNReal Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] {k : ℕ}

/-- **The signed chart coefficient of a nonnegative top form.** Let `φ` be a top form which, at
every point, is nonnegative on the positively oriented bases of the orientation of the lift `l`
and nonpositive on the negatively oriented ones. In a chart, its coefficient on a model basis
`b`, with the chart sign of `l` and the sign of `b` against the model orientation, is the
absolute value of the coefficient. -/
theorem signBasis_mul_signedInChartAt_eq_abs (l : Manifold.OrientationLift I M (Fin k))
    {φ : RoughForm I M ℝ k}
    (hφ : ∀ x (c : Basis (Fin k) ℝ (TangentSpace I x)),
      0 ≤ (Orientation.signBasis (l.orientationAt x) c : ℝ) * φ x c)
    (b : Basis (Fin k) ℝ E) {α x : M} (hx : x ∈ (extChartAt I α).source) :
    (Orientation.signBasis l.modelOrientation b : ℝ) *
        φ.signedInChartAt b α (fun z ↦ l.signAt α z) (extChartAt I α x) =
      |φ.inChartAt α (extChartAt I α x) b| := by
  have hα : x ∈ (chartAt H α).source := by rwa [extChartAt_source] at hx
  have hxx : x ∈ (chartAt H x).source := mem_chart_source H x
  let D := fderivWithin ℝ (extChartAt I x ∘ (extChartAt I α).symm) (range I) (extChartAt I α x)
  -- The chart signs compensate the sign of the transition Jacobian to the chart at `x`.
  have hD : 0 < (l.signAt α x : ℝ) * (l.signAt x x : ℝ) * D.toLinearMap.det := by
    rw [l.signAt_of_mem hα, l.signAt_of_mem hxx]
    exact l.compatible α x x hα hxx
  have hcoef := φ.inChartAt_apply_basis_eq_det_mul b ((extChartAt I α).map_source hx)
    (x := x) (by rw [(extChartAt I α).left_inv hx]; exact mem_extChartAt_source x)
  rw [(extChartAt I α).left_inv hx,
    RoughForm.inChartAt_chart_apply φ x (mem_extChartAt_source x)] at hcoef
  simp only [tangentCoordChange_self (mem_extChartAt_source x)] at hcoef
  -- The tuple `fun i ↦ b i` is the coercion of `b`, up to eta.
  rw [show (fun i ↦ b i) = ⇑b from rfl] at hcoef
  have key : 0 ≤ (Orientation.signBasis l.modelOrientation b : ℝ) * (l.signAt x x : ℝ) *
      φ x b := by
    have h := hφ x b
    rw [l.signBasis_orientationAt b x, Units.val_mul, Int.cast_mul] at h
    -- `h` reads `b` as a basis of the tangent space `TangentSpace I x`, which is `E`.
    exact h
  have hsq : (l.signAt x x : ℝ) * l.signAt x x = 1 := by
    exact_mod_cast Int.isUnit_mul_self (l.signAt x x).isUnit
  have habs (u : ℤˣ) : |(u : ℝ)| = 1 := by
    rcases Int.units_eq_one_or u with rfl | rfl <;> simp
  rw [RoughForm.signedInChartAt_apply_of_mem_source _ _ _ _ hx]
  have hnonneg : 0 ≤ (Orientation.signBasis l.modelOrientation b : ℝ) *
      ((l.signAt α x : ℝ) * φ.inChartAt α (extChartAt I α x) b) := by
    have h := mul_nonneg hD.le key
    rw [hcoef]
    linear_combination h + ((Orientation.signBasis l.modelOrientation b : ℝ) *
      l.signAt α x * D.toLinearMap.det * φ x b) * hsq
  rw [← abs_of_nonneg hnonneg, abs_mul, abs_mul, habs, habs, one_mul, one_mul]

namespace RoughForm

variable [MeasurableSpace M] [BorelSpace M] [LindelofSpace M] [hk : Fact (finrank ℝ E = k)]

attribute [local instance] extChartAtMeasurableSpaceE extChartAtBorelSpaceE

/-- **Integration against the measure of a top form in coordinates.** For a continuous top form
`φ` and a measurable subset `s` of a chart source, the integral of `g` over `s` against `|φ|` is
the integral, over the coordinate image of `s`, of `g` read in the chart, weighted by the
absolute value of the coefficient of `φ` in the chart. No measurability or integrability of `g`
is needed. -/
theorem setIntegral_measure_of_subset {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {φ : RoughForm I M ℝ k} (hφ : IsSmoothForm I 0 φ) {α : M} {s : Set M}
    (hs : MeasurableSet s) (hsub : s ⊆ (extChartAt I α).source) (g : M → F) :
    ∫ x in s, g x ∂φ.measure =
      ∫ y in (extChartAt I α) '' s,
        |φ.inChartAt α y (finBasisOfFinrankEq ℝ E hk.out)| • g ((extChartAt I α).symm y)
          ∂(finBasisOfFinrankEq ℝ E hk.out).addHaar := by
  classical
  set e := extChartAt I α
  set b := finBasisOfFinrankEq ℝ E hk.out
  have hR : MeasurableEmbedding (e.source.domRestrict e) :=
    measurableEmbedding_extChartAt_restrict α
  have hval : MeasurableEmbedding (Subtype.val : e.source → M) :=
    MeasurableEmbedding.subtypeVal (isOpen_extChartAt_source α).measurableSet
  have htargetm : MeasurableSet e.target := by
    simpa only [Set.range_domRestrict, PartialEquiv.image_source_eq_target] using
      hR.measurableSet_range
  -- A measurable density on `E` that is `|φ(b)|` on the chart target.
  set ρ : E → ℝ≥0∞ := e.target.piecewise (fun y ↦ ENNReal.ofReal |φ.inChartAt α y b|) 0
    with hρ_def
  have hρ : Measurable ρ :=
    (ENNReal.continuous_ofReal.comp_continuousOn (continuous_abs.comp_continuousOn
      ((continuous_eval_const (b : Fin k → E)).comp_continuousOn
        (hφ.continuousOn_inChartAt α)))).measurable_piecewise continuousOn_const htargetm
  have himage : e.source.domRestrict e '' (Subtype.val ⁻¹' s) = e '' s := by
    rw [Set.image_domRestrict, inter_eq_left.2 hsub]
  have hA : MeasurableSet (e '' s) := hs.image_extChartAt α hsub
  have htarget : e '' s ⊆ e.target :=
    e.image_source_eq_target.subset.trans' (Set.image_mono hsub)
  -- On the chart source, `|φ|` is the coordinate measure with density `ρ`, carried to `M`.
  have hν : φ.measure.restrict e.source =
      ((b.addHaar.withDensity ρ).comap (e.source.domRestrict e)).map Subtype.val := by
    ext t ht
    have hts : MeasurableSet (t ∩ e.source) := ht.inter (isOpen_extChartAt_source α).measurableSet
    rw [Measure.restrict_apply ht, φ.measure_apply_of_subset hts inter_subset_right,
      Measure.map_apply measurable_subtypeVal ht, hR.comap_apply, Set.image_domRestrict,
      withDensity_apply _ (hts.image_extChartAt α inter_subset_right)]
    refine setLIntegral_congr_fun (hts.image_extChartAt α inter_subset_right) fun y hy ↦ ?_
    rw [hρ_def, Set.piecewise_eq_of_mem _ _ _
      (e.image_source_eq_target.subset (Set.image_mono inter_subset_right hy))]
  -- Read `g` on the chart source through the coordinate map `e`.
  have hg (μ : Measure e.source) : ∫ z, g z ∂μ =
      ∫ z, (fun y ↦ g (e.symm y)) (e.source.domRestrict e z) ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall fun z ↦ by
      simp only [Set.domRestrict_apply, e.left_inv z.property])
  rw [← Measure.restrict_restrict_of_subset hsub, hν, hval.restrict_map, hval.integral_map,
    hR.restrict_comap, himage, hg]
  refine (hR.integral_map (fun y ↦ g (e.symm y))).symm.trans ?_
  rw [hR.map_comap, Measure.restrict_restrict hR.measurableSet_range,
    Set.inter_eq_right.2 (himage ▸ Set.image_subset_range _ _),
    setIntegral_withDensity_eq_setIntegral_toReal_smul hρ
      ((ae_restrict_iff' hA).2 (Filter.Eventually.of_forall fun y hy ↦ ?_)) _ hA]
  · refine setIntegral_congr_fun hA fun y hy ↦ ?_
    rw [hρ_def, Set.piecewise_eq_of_mem _ _ _ (htarget hy), ENNReal.toReal_ofReal (abs_nonneg _)]
  · rw [hρ_def, Set.piecewise_eq_of_mem _ _ _ (htarget hy)]
    exact ENNReal.ofReal_lt_top

end RoughForm

section Integral

variable [MeasurableSpace M] [BorelSpace M] [LindelofSpace M] [hk : Fact (finrank ℝ E = k)]

attribute [local instance] extChartAtMeasurableSpaceE extChartAtBorelSpaceE

/-- **Integrating a top form is integrating against its measure.** On an oriented manifold, let
`φ` be a continuous top form which, at every point, is nonnegative on the positively oriented
bases of the tangent space and nonpositive on the negatively oriented ones. Then for every
continuous compactly supported function `f`, the integral of the top form `f φ` is the integral
of `f` against the measure `|φ|` of `φ`: `∫_M f φ = ∫ f d|φ|`. -/
theorem integralTopForm_smul_eq_integral_measure (o : Manifold.Orientation I M (Fin k))
    {φ : RoughForm I M ℝ k} (hφ : IsSmoothForm I 0 φ)
    (hφo : ∀ x (c : Basis (Fin k) ℝ (TangentSpace I x)),
      0 ≤ (Orientation.signBasis (o.orientationAt x) c : ℝ) * φ x c)
    {f : M → ℝ} (hf : Continuous f) (hc : HasCompactSupport f) :
    integralTopForm o (fun x ↦ f x • φ x) = ∫ x, f x ∂φ.measure := by
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have := RoughForm.isLocallyFiniteMeasure_measure hφ
  obtain ⟨l, rfl⟩ := o.exists_lift
  simp only [Manifold.Orientation.orientationAt_mk] at hφo
  set b := finBasisOfFinrankEq ℝ E hk.out
  set ψ : RoughForm I M ℝ k := fun x ↦ f x • φ x
  -- `f φ` is a continuous top form supported in the support of `f`.
  have hψ : IsSmoothForm I 0 ψ := hφ.fun_smul (contMDiff_zero_iff.2 hf)
  have hsupp : _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] ℝ) ψ ⊆ tsupport f :=
    -- `simp` leaves the zero of the fibre at `x` against the value at `x` of the zero form.
    closure_mono fun x hx ↦ Function.mem_support.2 fun h ↦ hx (by simp [ψ, h]; rfl)
  have hi : IntegrableTopForm ψ :=
    hψ.integrableTopForm (hc.of_isClosed_subset isClosed_closure hsupp) b
  -- Compute both integrals on the disjointed pieces of a chart cover of the support of `f`.
  obtain ⟨n, α, u, _, hu, hcover⟩ := exists_finite_precompact_chart_cover (I := I) hc
  have hpiece (i : Fin n) : disjointed u i ⊆ (extChartAt I (α i)).source :=
    (disjointed_subset u i).trans (hu i).2.1
  have hmeas (i : Fin n) : MeasurableSet (disjointed u i) := by
    rw [disjointed_apply, Finset.sup_set_eq_biUnion]
    exact (hu i).1.measurableSet.diff
      (Finset.measurableSet_biUnion _ fun j _ ↦ (hu j).1.measurableSet)
  rw [integralTopForm_eq_sum_disjointed_chart_integrals l ψ hi b α u (fun i ↦ (hu i).1)
    (fun i ↦ (hu i).2.1) (hsupp.trans hcover), Finset.mul_sum,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := ⋃ i, disjointed u i) fun x hx ↦
      image_eq_zero_of_notMem_tsupport fun h ↦ hx (by rw [iUnion_disjointed]; exact hcover h),
    integral_iUnion_fintype hmeas (disjoint_disjointed u)
      fun i ↦ (hf.integrable_of_hasCompactSupport hc).integrableOn]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [RoughForm.setIntegral_measure_of_subset hφ (hmeas i) (hpiece i), ← integral_const_mul]
  refine setIntegral_congr_fun ((hmeas i).image_extChartAt (α i) (hpiece i)) ?_
  rintro _ ⟨x, hx, rfl⟩
  dsimp only
  rw [RoughForm.signedInChartAt_fun_smul, (extChartAt I (α i)).left_inv (hpiece i hx),
    mul_left_comm, signBasis_mul_signedInChartAt_eq_abs l hφo b (hpiece i hx), smul_eq_mul,
    mul_comm]

end Integral

end TauCeti
