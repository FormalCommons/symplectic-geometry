/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.AsymptoticallyHolomorphic.FrameChange

/-!
# Sections extended by zero from a rescaled unitary chart

Let `D` be rescaled unitary charts, `k ≥ k₀` a power and `x` a point. A complex function `f` on
`StdSpace ι` defines a section of `PowerBundle P k`, `D.sectionOfReading k x f`: at a point of the
source of `D.chart k x` whose image `z` lies in the ball `B` of radius `ρ₀ * √k`, it is the class
of the frame `D.frame k x` and of `f z`, and it is zero elsewhere. Its reading in the chart at `x`
is `f` on `B`. The peak sections of Donaldson's construction are built this way from cut-off
Gaussians.

When `f` has compact support in `B`, the section vanishes outside the image `K` of that support
under the inverse of the chart, a compact and so, in a Hausdorff `M`, closed set. So at a point
`y ∉ K` its readings and `∂̄` readings in the chart at `y` vanish near `0`, and so do all its jet
norms at `y`. At a point `y ∈ K`, the transition from the chart at `y` to the chart at `x` is
defined near `0` with values in `B`, and there the reading at `y` is the change of frame times `f`
composed with the transition
(`SymplecticGeometry.RescaledUnitaryCharts.reading_eq_frameChange_mul`); the change of frame and
the transition are smooth. So, when
`f` is moreover smooth on `B`, the readings at every point are smooth at `0`, and so are, on a
boundaryless manifold, the `∂̄` readings
(`SymplecticGeometry.RescaledUnitaryCharts.contDiffAt_dbarReading`): this is the smoothness that
`SymplecticGeometry.RescaledUnitaryCharts.IsAsymptoticallyHolomorphic` asks for.

## Main definitions

* `SymplecticGeometry.RescaledUnitaryCharts.sectionOfReading`: the section extended by zero.

## Main results

* `SymplecticGeometry.RescaledUnitaryCharts.reading_sectionOfReading`: its reading in the chart
  at `x` is `f` on `B`.
* `SymplecticGeometry.RescaledUnitaryCharts.jetNorm_sectionOfReading_eq_zero` and
  `SymplecticGeometry.RescaledUnitaryCharts.dbarJetNorm_sectionOfReading_eq_zero`: its jet norms
  vanish away from the image of the support of `f`.
* `SymplecticGeometry.RescaledUnitaryCharts.contDiffAt_reading_sectionOfReading` and
  `SymplecticGeometry.RescaledUnitaryCharts.contDiffAt_dbarReading_sectionOfReading`: for `f`
  with compact support in `B` and `C^n` there (`C^(n + 1)` for `∂̄`), its readings (`∂̄`
  readings) at every point are `C^n` at the centre; for smooth `f`, both are smooth
  (`SymplecticGeometry.RescaledUnitaryCharts.contDiffAt_reading_and_dbarReading_sectionOfReading`).

## References

* [S. K. Donaldson, *Symplectic submanifolds and almost-complex geometry*][Donaldson1996].
* [D. Auroux, *A remark about Donaldson's construction of symplectic submanifolds*][Auroux2002].
-/

public section

open scoped Manifold ContDiff Topology
open TauCeti Metric Bundle

namespace SymplecticGeometry

namespace RescaledUnitaryCharts

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] {ι : Type*} [Fintype ι]
  {P : M → Type*} [TopologicalSpace (TotalSpace Circle P)] [∀ x, TopologicalSpace (P x)]
  [FiberBundle Circle P] [∀ x, MulAction Circleᵐᵒᵖ (P x)] [PrincipalBundle Circle P]
  [ContMDiffFiberBundle ∞ Circle P I (𝓡 1)]
  {σ : SmoothTwoForm I M} {J : SmoothAlmostComplexStructure I M}
  {α : SmoothForm (I.prod (𝓡 1)) (ManifoldTotalSpace Circle P) ℝ 1} {k₀ : ℕ} {ρ₀ : ℝ}
  (D : RescaledUnitaryCharts P σ J α ι k₀ ρ₀)

/-! ### The section extended by zero -/

open Classical in
/-- The **section extended by zero** from a function `f` on the chart centred at `x`: at a point
`y` of the source of `D.chart k x` whose image lies in the ball of radius `ρ₀ * √k`, the class of
the frame `D.frame k x y` and of `f (D.chart k x y)`; zero at every other point. For `k₀ ≤ k`, its
reading in the chart at `x` is `f` on that ball
(`SymplecticGeometry.RescaledUnitaryCharts.reading_sectionOfReading`). -/
noncomputable def sectionOfReading (k : ℕ) (x : M) (f : StdSpace ι → ℂ) :
    Π y, PowerBundle P k y := fun y ↦
  if y ∈ (D.chart k x).source ∧ D.chart k x y ∈ ball (0 : StdSpace ι) (ρ₀ * √k) then
    AssociatedBundle.mk Circle (D.frame k x y) (PowerModel.toComplex.symm (f (D.chart k x y)))
  else 0

open Classical in
theorem sectionOfReading_def (k : ℕ) (x : M) (f : StdSpace ι → ℂ) (y : M) :
    D.sectionOfReading k x f y =
      if y ∈ (D.chart k x).source ∧ D.chart k x y ∈ ball (0 : StdSpace ι) (ρ₀ * √k) then
        AssociatedBundle.mk Circle (D.frame k x y) (PowerModel.toComplex.symm (f (D.chart k x y)))
      else 0 :=
  (rfl)

theorem sectionOfReading_apply_of_mem {k : ℕ} {x : M} (f : StdSpace ι → ℂ) {y : M}
    (hy : y ∈ (D.chart k x).source) (hyb : D.chart k x y ∈ ball (0 : StdSpace ι) (ρ₀ * √k)) :
    D.sectionOfReading k x f y =
      AssociatedBundle.mk Circle (D.frame k x y) (PowerModel.toComplex.symm (f (D.chart k x y))) :=
  by rw [sectionOfReading_def, ite_eq_left ⟨hy, hyb⟩]

theorem sectionOfReading_apply_of_notMem {k : ℕ} {x : M} (f : StdSpace ι → ℂ) {y : M}
    (hy : ¬(y ∈ (D.chart k x).source ∧ D.chart k x y ∈ ball (0 : StdSpace ι) (ρ₀ * √k))) :
    D.sectionOfReading k x f y = 0 := by
  rw [sectionOfReading_def, ite_eq_right hy]

/-- For `k₀ ≤ k` and `z` in the ball of radius `ρ₀ * √k`, the section extended by zero from `f`
is, at `(D.chart k x).symm z`, the class of the frame and of `f z`. -/
theorem sectionOfReading_chart_symm {k : ℕ} (hk : k₀ ≤ k) (x : M) (f : StdSpace ι → ℂ)
    {z : StdSpace ι} (hz : z ∈ ball (0 : StdSpace ι) (ρ₀ * √k)) :
    D.sectionOfReading k x f ((D.chart k x).symm z) =
      AssociatedBundle.mk Circle (D.frame k x ((D.chart k x).symm z))
        (PowerModel.toComplex.symm (f z)) := by
  have hzt := D.ball_subset_target hk x hz
  have hz' : D.chart k x ((D.chart k x).symm z) = z := (D.chart k x).right_inv hzt
  rw [D.sectionOfReading_apply_of_mem (y := (D.chart k x).symm z) f ((D.chart k x).map_target hzt)
    (hz'.symm ▸ hz), hz']

/-- For `k₀ ≤ k`, the reading in the chart at `x` of the section extended by zero from `f` is
`f` on the ball of radius `ρ₀ * √k`. -/
theorem reading_sectionOfReading {k : ℕ} (hk : k₀ ≤ k) (x : M) (f : StdSpace ι → ℂ) :
    Set.EqOn (D.reading k x (D.sectionOfReading k x f)) f (ball 0 (ρ₀ * √k)) := fun z hz ↦ by
  rw [reading_def, D.sectionOfReading_chart_symm hk x f hz,
    AssociatedBundle.mkLinearIsometryEquiv_symm_apply_mk, PrincipalBundle.division_self, one_smul,
    LinearIsometryEquiv.apply_symm_apply]

@[simp]
theorem sectionOfReading_zero (k : ℕ) (x : M) :
    D.sectionOfReading k x (0 : StdSpace ι → ℂ) = 0 := by
  funext y
  rw [sectionOfReading_def]
  split_ifs <;> simp [AssociatedBundle.mk_zero]

@[simp]
theorem sectionOfReading_add (k : ℕ) (x : M) (f g : StdSpace ι → ℂ) :
    D.sectionOfReading k x (f + g) = D.sectionOfReading k x f + D.sectionOfReading k x g := by
  funext y
  simp only [sectionOfReading_def, Pi.add_apply]
  split_ifs <;> simp [AssociatedBundle.mk_add]

@[simp]
theorem sectionOfReading_smul (k : ℕ) (x : M) (c : ℂ) (f : StdSpace ι → ℂ) :
    D.sectionOfReading k x (c • f) = c • D.sectionOfReading k x f := by
  funext y
  simp only [sectionOfReading_def, Pi.smul_apply]
  split_ifs
  · rw [map_smul, AssociatedBundle.mk_smul_scalar]
  · simp

/-- The section extended by zero from `f` vanishes outside the image of the support of `f` under
the inverse of the chart. -/
theorem sectionOfReading_eq_zero {k : ℕ} {x : M} {f : StdSpace ι → ℂ} {y : M}
    (hy : y ∉ (D.chart k x).symm '' Function.support f) :
    D.sectionOfReading k x f y = 0 := by
  rw [sectionOfReading_def]
  split_ifs with h
  · have hf : f (D.chart k x y) = 0 := by
      by_contra hf
      exact hy ⟨_, hf, (D.chart k x).left_inv h.1⟩
    simp [hf, AssociatedBundle.mk_zero]
  · rfl

/-! ### Vanishing away from the support -/

/-- Let `k₀ ≤ k` and let `f` have compact support in the ball of radius `ρ₀ * √k`. At a point `y`
outside the image of that support under the inverse of the chart at `x`, the reading in the chart
at `y` of the section extended by zero from `f` vanishes near `0`. -/
theorem reading_sectionOfReading_eventuallyEq_zero [T2Space M] {k : ℕ} (hk : k₀ ≤ k) {x : M}
    {f : StdSpace ι → ℂ} (hf : HasCompactSupport f) (hfb : tsupport f ⊆ ball 0 (ρ₀ * √k))
    {y : M} (hy : y ∉ (D.chart k x).symm '' tsupport f) :
    D.reading k y (D.sectionOfReading k x f) =ᶠ[𝓝 0] 0 := by
  have hK := (D.isCompact_chart_symm_image hk x hf.isCompact hfb).isClosed
  have hc : ContinuousAt (D.chart k y).symm 0 :=
    (D.chart k y).toOpenPartialHomeomorph.continuousAt_symm (D.zero_mem_chart_target hk y)
  have hmem : (D.chart k y).symm ⁻¹' ((D.chart k x).symm '' tsupport f)ᶜ ∈ 𝓝 0 :=
    hc.preimage_mem_nhds (hK.isOpen_compl.mem_nhds (by rwa [D.chart_symm_zero hk y]))
  filter_upwards [hmem] with w hw
  rw [reading_def, D.sectionOfReading_eq_zero fun h ↦ hw (Set.image_mono (subset_tsupport f) h),
    map_zero, map_zero, Pi.zero_apply]

/-- Under the hypotheses of
`SymplecticGeometry.RescaledUnitaryCharts.reading_sectionOfReading_eventuallyEq_zero`, the `∂̄`
reading in the chart at `y` vanishes near `0`. -/
theorem dbarReading_sectionOfReading_eventuallyEq_zero [T2Space M] {k : ℕ} (hk : k₀ ≤ k) {x : M}
    {f : StdSpace ι → ℂ} (hf : HasCompactSupport f) (hfb : tsupport f ⊆ ball 0 (ρ₀ * √k))
    {y : M} (hy : y ∉ (D.chart k x).symm '' tsupport f) :
    D.dbarReading k y (D.sectionOfReading k x f) =ᶠ[𝓝 0] 0 :=
  (D.dbarReading_eventuallyEq ((D.reading_sectionOfReading_eventuallyEq_zero hk hf hfb hy).trans
    (Filter.EventuallyEq.of_eq (D.reading_zero k y).symm))).trans
    (Filter.Eventually.of_forall (D.dbarReading_zero k y))

/-- Under the hypotheses of
`SymplecticGeometry.RescaledUnitaryCharts.reading_sectionOfReading_eventuallyEq_zero`, the jet
norms at `y` of the section extended by zero vanish. -/
theorem jetNorm_sectionOfReading_eq_zero [T2Space M] {k : ℕ} (hk : k₀ ≤ k) (r : ℕ) {x : M}
    {f : StdSpace ι → ℂ} (hf : HasCompactSupport f) (hfb : tsupport f ⊆ ball 0 (ρ₀ * √k))
    {y : M} (hy : y ∉ (D.chart k x).symm '' tsupport f) :
    D.jetNorm k r (D.sectionOfReading k x f) y = 0 := by
  rw [jetNorm_def, jetNormAt_congr_of_eventuallyEq r
    (D.reading_sectionOfReading_eventuallyEq_zero hk hf hfb hy), jetNormAt_zero_fun]

/-- Under the hypotheses of
`SymplecticGeometry.RescaledUnitaryCharts.reading_sectionOfReading_eventuallyEq_zero`, the jet
norms at `y` of `∂̄` of the section extended by zero vanish. -/
theorem dbarJetNorm_sectionOfReading_eq_zero [T2Space M] {k : ℕ} (hk : k₀ ≤ k) (r : ℕ) {x : M}
    {f : StdSpace ι → ℂ} (hf : HasCompactSupport f) (hfb : tsupport f ⊆ ball 0 (ρ₀ * √k))
    {y : M} (hy : y ∉ (D.chart k x).symm '' tsupport f) :
    D.dbarJetNorm k r (D.sectionOfReading k x f) y = 0 := by
  rw [dbarJetNorm_def, jetNormAt_congr_of_eventuallyEq r
    (D.dbarReading_sectionOfReading_eventuallyEq_zero hk hf hfb hy), jetNormAt_zero_fun]

/-! ### Smoothness -/

/-- Let `k₀ ≤ k` and let `f` be `C^n` on the ball of radius `ρ₀ * √k`, with compact support in it.
Then at every point `y`, the reading in the chart at `y` of the section extended by zero from `f`
is `C^n` at `0`. -/
theorem contDiffAt_reading_sectionOfReading [T2Space M] {n : ℕ∞} {k : ℕ} (hk : k₀ ≤ k) (x : M)
    {f : StdSpace ι → ℂ} (hf : HasCompactSupport f) (hfb : tsupport f ⊆ ball 0 (ρ₀ * √k))
    (hfs : ContDiffOn ℝ n f (ball 0 (ρ₀ * √k))) (y : M) :
    ContDiffAt ℝ n (D.reading k y (D.sectionOfReading k x f)) 0 := by
  by_cases hy : y ∈ (D.chart k x).symm '' tsupport f
  · obtain ⟨z, hz, rfl⟩ := hy
    have h0W := D.zero_mem_chartTransitionDomain hk x (hfb hz)
    -- In the chart at `y`, the section is the change of frame times `f` composed with the
    -- transition `τ` to the chart at `x`.
    have hτ := D.contDiffAt_chartTransition (n := n)
      (D.chartTransitionDomain_subset_source k x _ h0W)
    have hfτ : ContDiffAt ℝ n f (D.chartTransition k x ((D.chart k x).symm z) 0) :=
      hfs.contDiffAt (isOpen_ball.mem_nhds (D.mem_chartTransitionDomain_iff.1 h0W).2.2)
    refine ((D.contDiffAt_frameChange hk h0W).mul (hfτ.comp 0 hτ)).congr_of_eventuallyEq ?_
    filter_upwards [(D.isOpen_chartTransitionDomain k x _).mem_nhds h0W] with w hw
    rw [D.reading_eq_frameChange_mul (D.chartTransitionDomain_subset_source k x _ hw),
      D.reading_sectionOfReading hk x f (D.mem_chartTransitionDomain_iff.1 hw).2.2,
      Function.comp_apply]
  · exact contDiffAt_const.congr_of_eventuallyEq
      (D.reading_sectionOfReading_eventuallyEq_zero hk hf hfb hy)

/-- On a boundaryless manifold, let `k₀ ≤ k` and let `f` be `C^(n + 1)` on the ball of radius
`ρ₀ * √k`, with compact support in it. Then at every point `y`, the `∂̄` reading in the chart at
`y` of the section extended by zero from `f` is `C^n` at `0`. -/
theorem contDiffAt_dbarReading_sectionOfReading [T2Space M] [I.Boundaryless] {n : ℕ∞} {k : ℕ}
    (hk : k₀ ≤ k) (x : M) {f : StdSpace ι → ℂ} (hf : HasCompactSupport f)
    (hfb : tsupport f ⊆ ball 0 (ρ₀ * √k)) (hfs : ContDiffOn ℝ (n + 1) f (ball 0 (ρ₀ * √k)))
    (y : M) :
    ContDiffAt ℝ n (D.dbarReading k y (D.sectionOfReading k x f)) 0 := by
  have h := D.contDiffAt_reading_sectionOfReading (n := n + 1) hk x hf hfb (by exact_mod_cast hfs) y
  exact D.contDiffAt_dbarReading (D.zero_mem_chart_target hk y) (by exact_mod_cast h)

/-- On a boundaryless manifold, let `k₀ ≤ k` and let `f` be smooth on the ball of radius
`ρ₀ * √k`, with compact support in it. Then at every point `y`, the reading and the `∂̄` reading
in the chart at `y` of the section extended by zero from `f` are smooth at `0`, as
`SymplecticGeometry.RescaledUnitaryCharts.IsAsymptoticallyHolomorphic` asks. -/
theorem contDiffAt_reading_and_dbarReading_sectionOfReading [T2Space M] [I.Boundaryless]
    {k : ℕ} (hk : k₀ ≤ k) (x : M) {f : StdSpace ι → ℂ} (hf : HasCompactSupport f)
    (hfb : tsupport f ⊆ ball 0 (ρ₀ * √k)) (hfs : ContDiffOn ℝ ∞ f (ball 0 (ρ₀ * √k))) (y : M) :
    ContDiffAt ℝ ∞ (D.reading k y (D.sectionOfReading k x f)) 0 ∧
      ContDiffAt ℝ ∞ (D.dbarReading k y (D.sectionOfReading k x f)) 0 :=
  ⟨D.contDiffAt_reading_sectionOfReading hk x hf hfb hfs y,
    D.contDiffAt_dbarReading_sectionOfReading (n := ⊤) hk x hf hfb (hfs.of_le (by simp)) y⟩

end RescaledUnitaryCharts

end SymplecticGeometry

end
