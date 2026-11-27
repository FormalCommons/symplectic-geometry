/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.AsymptoticallyHolomorphic.FrameChange
public import SymplecticGeometry.Geometry.Symplectic.AsymptoticallyHolomorphic.PeakFunction
import SymplecticGeometry.Analysis.SpecialFunctions.Gaussian.Basic
import SymplecticGeometry.Geometry.Symplectic.AsymptoticallyHolomorphic.ChartChange

/-!
# Sections extended by zero from a rescaled unitary chart

Let `D` be rescaled unitary charts, `k ≥ k₀` a power and `x` a point. A complex function `f` on
`StdSpace ι` defines a section of `PowerBundle P k`, `D.sectionOfReading k x f`: at a point of the
source of `D.chart k x` whose image `z` lies in the ball `B` of radius `ρ₀ * √k`, it is the class
of the frame `D.frame k x` and of `f z`, and it is zero elsewhere. Its reading in the chart at `x`
is `f` on `B`. The peak sections of Donaldson's construction are built this way from cut-off
Gaussians.

When the closed support of `f` lies in `B`, it is compact, and the section vanishes outside its
image `K` under the inverse of the chart, a compact and so, in a Hausdorff `M`, closed set. So at a
point `y ∉ K` its readings and `∂̄` readings in the chart at `y` vanish near `0`, and so do all its
jet norms at `y`. At a point `y ∈ K`, the transition from the chart at `y` to the chart at `x` is
defined near `0` with values in `B`, and there the reading at `y` is the change of frame times `f`
composed with the transition
(`SymplecticGeometry.RescaledUnitaryCharts.reading_eq_frameChange_mul`); the change of frame and the
transition are smooth. So, when `f` is moreover smooth on `B`, the readings at every point are
smooth at `0`, and so are, on a boundaryless manifold, the `∂̄` readings
(`SymplecticGeometry.RescaledUnitaryCharts.contDiffAt_dbarReading`): this is the smoothness that
`SymplecticGeometry.RescaledUnitaryCharts.IsAsymptoticallyHolomorphic` asks for.

For a family `f k` of `C^r` functions supported, for every `ε > 0` and large `k`, in balls of
radius `ε * √k` (as balls of radius `2 * k ^ (1 / 6)` are,
`Real.eventually_mul_rpow_one_sixth_lt_mul_sqrt`), with `r`-jet norms bounded by a polynomial in
`‖z‖` times `exp (-c * ‖z‖ ^ 2)` uniformly in `k`, the `r`-jet norms of the sections extended by
zero decay like Gaussians in the rescaled distance
`d_k(x, y) = √(2π k) · d_g(x, y)` for the metric `g_J`. At a point `y = (D.chart k x)⁻¹ z` of
the image of the support, the change of chart
(`SymplecticGeometry.RescaledUnitaryCharts.jetNorm_le_of_chart_change`) bounds the jet norm at
`y` by a polynomial in `d_k(x, y)` times the jet norm of `f k` at `z`, and `d_k(x, y)` and
`‖z‖` are comparable
(`SymplecticGeometry.RescaledUnitaryCharts.ofReal_mul_riemannianEDist_symm_mem_Icc`), which turns
the Gaussian bound in `‖z‖` into one in `d_k(x, y)`
(`Real.one_add_pow_mul_exp_neg_mul_sq_le_of_le_mul`); elsewhere
the jet norm vanishes. Conversely, a point at rescaled distance less than `1 / √2` from `x` has a
coordinate of norm less than `1` in the chart at `x`
(`SymplecticGeometry.RescaledUnitaryCharts.exists_norm_lt_symm_eq_of_riemannianEDist_lt`), so a
lower bound on `f k` on the unit ball bounds the section from below near `x`.

The `∂̄` reading of a section in the chart at `x` is the antilinear part of its connection reading
`L` for `J_{k,x}`, the structure `J` read in the chart, while the model `∂̄`
(`SymplecticGeometry.modelDbar`) of its reading is the antilinear part of the same `L` for
`J₀ = stdComplexStructure ι`; the two differ by `(i / 2) L ∘ (J_{k,x} - J₀)`
(`SymplecticGeometry.RescaledUnitaryCharts.dbarReading_eq_modelDbar_add`). On the ball of radius
`ρ₀ * √k`, the jets of `J_{k,x} - J₀` are of size `(1 + ‖z‖) / √k`
(`SymplecticGeometry.RescaledUnitaryCharts.exists_jetNormAt_chartPushforward_sub_le`), and those
of `L` of size `1 + ‖z‖` times the jets of the reading
(`SymplecticGeometry.RescaledUnitaryCharts.exists_jetNormAt_connectionReading_le`), so the Leibniz
bound `SymplecticGeometry.jetNormAt_bilinear_le` bounds the `r`-jet norm of the `∂̄` reading by that of
the model `∂̄` plus `C * (1 + ‖z‖) ^ 2 / √k` times the `(r + 1)`-jet norm of the reading, with `C`
independent of `k`, `x` and the section.

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
  with closed support in `B` and `C^n` there (`C^(n + 1)` for `∂̄`), its readings (`∂̄`
  readings) at every point are `C^n` at the centre; for smooth `f`, both are smooth
  (`SymplecticGeometry.RescaledUnitaryCharts.contDiffAt_reading_and_dbarReading_sectionOfReading`).
* `SymplecticGeometry.RescaledUnitaryCharts.exists_jetNorm_sectionOfReading_le`: Gaussian decay
  of the jet norms in the rescaled distance from the centre.
* `SymplecticGeometry.RescaledUnitaryCharts.exists_le_norm_sectionOfReading`: the lower bound
  near the centre.
* `SymplecticGeometry.RescaledUnitaryCharts.exists_jetNormAt_dbarReading_le` and
  `SymplecticGeometry.RescaledUnitaryCharts.exists_jetNormAt_dbarReading_sectionOfReading_le`:
  the `∂̄` reading against the model `∂̄` in the chart at the centre.

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
theorem sectionOfReading_apply_eq_zero_of_notMem_image {k : ℕ} {x : M} {f : StdSpace ι → ℂ} {y : M}
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

/-- Let `k₀ ≤ k` and let the closed support of `f` lie in the ball of radius `ρ₀ * √k`. At a point
`y` outside the image of that support under the inverse of the chart at `x`, the reading in the
chart at `y` of the section extended by zero from `f` vanishes near `0`. -/
theorem reading_sectionOfReading_eventuallyEq_zero [T2Space M] {k : ℕ} (hk : k₀ ≤ k) {x : M}
    {f : StdSpace ι → ℂ} (hfb : tsupport f ⊆ ball 0 (ρ₀ * √k))
    {y : M} (hy : y ∉ (D.chart k x).symm '' tsupport f) :
    D.reading k y (D.sectionOfReading k x f) =ᶠ[𝓝 0] 0 := by
  -- The support of `f` is compact, as a closed subset of a closed ball.
  have hfc : IsCompact (tsupport f) := (isCompact_closedBall 0 _).of_isClosed_subset
    (isClosed_tsupport f) (hfb.trans ball_subset_closedBall)
  have hK := (D.isCompact_chart_symm_image hk x hfc hfb).isClosed
  have hc : ContinuousAt (D.chart k y).symm 0 :=
    (D.chart k y).toOpenPartialHomeomorph.continuousAt_symm (D.zero_mem_chart_target hk y)
  have hmem : (D.chart k y).symm ⁻¹' ((D.chart k x).symm '' tsupport f)ᶜ ∈ 𝓝 0 :=
    hc.preimage_mem_nhds (hK.isOpen_compl.mem_nhds (by rwa [D.chart_symm_zero hk y]))
  filter_upwards [hmem] with w hw
  rw [reading_def, D.sectionOfReading_apply_eq_zero_of_notMem_image
    fun h ↦ hw (Set.image_mono (subset_tsupport f) h), map_zero, map_zero, Pi.zero_apply]

/-- Under the hypotheses of
`SymplecticGeometry.RescaledUnitaryCharts.reading_sectionOfReading_eventuallyEq_zero`, the `∂̄`
reading in the chart at `y` vanishes near `0`. -/
theorem dbarReading_sectionOfReading_eventuallyEq_zero [T2Space M] {k : ℕ} (hk : k₀ ≤ k) {x : M}
    {f : StdSpace ι → ℂ} (hfb : tsupport f ⊆ ball 0 (ρ₀ * √k))
    {y : M} (hy : y ∉ (D.chart k x).symm '' tsupport f) :
    D.dbarReading k y (D.sectionOfReading k x f) =ᶠ[𝓝 0] 0 :=
  (D.dbarReading_eventuallyEq ((D.reading_sectionOfReading_eventuallyEq_zero hk hfb hy).trans
    (Filter.EventuallyEq.of_eq (D.reading_zero k y).symm))).trans
    (Filter.Eventually.of_forall (D.dbarReading_zero k y))

/-- Under the hypotheses of
`SymplecticGeometry.RescaledUnitaryCharts.reading_sectionOfReading_eventuallyEq_zero`, the jet
norms at `y` of the section extended by zero vanish. -/
theorem jetNorm_sectionOfReading_eq_zero [T2Space M] {k : ℕ} (hk : k₀ ≤ k) (r : ℕ) {x : M}
    {f : StdSpace ι → ℂ} (hfb : tsupport f ⊆ ball 0 (ρ₀ * √k))
    {y : M} (hy : y ∉ (D.chart k x).symm '' tsupport f) :
    D.jetNorm k r (D.sectionOfReading k x f) y = 0 := by
  rw [jetNorm_def, jetNormAt_congr_of_eventuallyEq r
    (D.reading_sectionOfReading_eventuallyEq_zero hk hfb hy), jetNormAt_zero_fun]

/-- Under the hypotheses of
`SymplecticGeometry.RescaledUnitaryCharts.reading_sectionOfReading_eventuallyEq_zero`, the jet
norms at `y` of `∂̄` of the section extended by zero vanish. -/
theorem dbarJetNorm_sectionOfReading_eq_zero [T2Space M] {k : ℕ} (hk : k₀ ≤ k) (r : ℕ) {x : M}
    {f : StdSpace ι → ℂ} (hfb : tsupport f ⊆ ball 0 (ρ₀ * √k))
    {y : M} (hy : y ∉ (D.chart k x).symm '' tsupport f) :
    D.dbarJetNorm k r (D.sectionOfReading k x f) y = 0 := by
  rw [dbarJetNorm_def, jetNormAt_congr_of_eventuallyEq r
    (D.dbarReading_sectionOfReading_eventuallyEq_zero hk hfb hy), jetNormAt_zero_fun]

/-! ### Smoothness -/

/-- Let `k₀ ≤ k` and let `f` be `C^n` on the ball of radius `ρ₀ * √k`, with its closed support in
it. Then at every point `y`, the reading in the chart at `y` of the section extended by zero from
`f` is `C^n` at `0`. -/
theorem contDiffAt_reading_sectionOfReading [T2Space M] {n : ℕ∞} {k : ℕ} (hk : k₀ ≤ k) (x : M)
    {f : StdSpace ι → ℂ} (hfb : tsupport f ⊆ ball 0 (ρ₀ * √k))
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
      (D.reading_sectionOfReading_eventuallyEq_zero hk hfb hy)

/-- On a boundaryless manifold, let `k₀ ≤ k` and let `f` be `C^(n + 1)` on the ball of radius
`ρ₀ * √k`, with its closed support in it. Then at every point `y`, the `∂̄` reading in the chart at
`y` of the section extended by zero from `f` is `C^n` at `0`. -/
theorem contDiffAt_dbarReading_sectionOfReading [T2Space M] [I.Boundaryless] {n : ℕ∞} {k : ℕ}
    (hk : k₀ ≤ k) (x : M) {f : StdSpace ι → ℂ}
    (hfb : tsupport f ⊆ ball 0 (ρ₀ * √k)) (hfs : ContDiffOn ℝ (n + 1) f (ball 0 (ρ₀ * √k)))
    (y : M) :
    ContDiffAt ℝ n (D.dbarReading k y (D.sectionOfReading k x f)) 0 := by
  have h := D.contDiffAt_reading_sectionOfReading (n := n + 1) hk x hfb (by exact_mod_cast hfs) y
  exact D.contDiffAt_dbarReading (D.zero_mem_chart_target hk y) (by exact_mod_cast h)

/-- On a boundaryless manifold, let `k₀ ≤ k` and let `f` be smooth on the ball of radius
`ρ₀ * √k`, with its closed support in it. Then at every point `y`, the reading and the `∂̄` reading
in the chart at `y` of the section extended by zero from `f` are smooth at `0`, as
`SymplecticGeometry.RescaledUnitaryCharts.IsAsymptoticallyHolomorphic` asks. -/
theorem contDiffAt_reading_and_dbarReading_sectionOfReading [T2Space M] [I.Boundaryless]
    {k : ℕ} (hk : k₀ ≤ k) (x : M) {f : StdSpace ι → ℂ}
    (hfb : tsupport f ⊆ ball 0 (ρ₀ * √k)) (hfs : ContDiffOn ℝ ∞ f (ball 0 (ρ₀ * √k))) (y : M) :
    ContDiffAt ℝ ∞ (D.reading k y (D.sectionOfReading k x f)) 0 ∧
      ContDiffAt ℝ ∞ (D.dbarReading k y (D.sectionOfReading k x f)) 0 :=
  ⟨D.contDiffAt_reading_sectionOfReading hk x hfb hfs y,
    D.contDiffAt_dbarReading_sectionOfReading (n := ⊤) hk x hfb (hfs.of_le (by simp)) y⟩

/-! ### `∂̄` against the model `∂̄` -/

/-- The `∂̄` reading of `s` in the chart at `x` is the model `∂̄` of its reading plus the
correction `(i / 2) L ∘ (J_{k,x}(z) - J₀)`, for `L` the connection read in the chart,
`J_{k,x}` the structure `J` read in the chart and `J₀ = stdComplexStructure ι`. -/
theorem dbarReading_eq_modelDbar_add (k : ℕ) (x : M) (s : Π y, PowerBundle P k y)
    (z : StdSpace ι) :
    D.dbarReading k x s z = modelDbar (D.reading k x s) z +
      (((2⁻¹ : ℂ) * Complex.I) • D.connectionReading k x s z).comp
        (J.chartPushforward (D.chart k x).toOpenPartialHomeomorph z -
          LinearMap.toContinuousLinearMap (stdComplexStructure ι).toLinearMap) := by
  ext v
  rw [modelDbar_def, ← connectionReading_def, dbarReading_def, add_apply,
    complexAntilinearPartContinuousLinearMap_apply_apply, LinearMap.coe_toContinuousLinearMap',
    complexAntilinearPart_apply, complexAntilinearPart_apply, ContinuousLinearMap.comp_apply,
    sub_apply, map_sub,
    smul_apply]
  simp only [ContinuousLinearMap.coe_coe, AlmostComplexStructure.ofComplexModule_apply,
    LinearMap.coe_toContinuousLinearMap', FunLike.coe_smul, Pi.smul_apply,
    smul_eq_mul, Complex.real_smul]
  push_cast
  ring

/-- **`∂̄` against the model `∂̄` in the chart at the centre.** On a boundaryless manifold, for
every order `r` there is a constant `C`, independent of `k ≥ k₀`, of the centre `x` and of the
section `s`, such that at every point `z` of the ball of radius `ρ₀ * √k` where the reading `f` of
`s` in the chart at `x` is `C^(r + 1)`, the `r`-jet norm at `z` of the `∂̄` reading of `s` is at
most that of the model `∂̄` of `f` plus `C * (√k)⁻¹ * (1 + ‖z‖) ^ 2` times the `(r + 1)`-jet norm
of `f` at `z`. -/
theorem exists_jetNormAt_dbarReading_le [I.Boundaryless] (r : ℕ) :
    ∃ C : ℝ, ∀ {k : ℕ}, k₀ ≤ k → ∀ (x : M) (s : Π y, PowerBundle P k y) {z : StdSpace ι},
      z ∈ ball 0 (ρ₀ * √k) → ContDiffAt ℝ (r + 1 : ℕ) (D.reading k x s) z →
        jetNormAt ℝ r (D.dbarReading k x s) z ≤
          jetNormAt ℝ r (modelDbar (D.reading k x s)) z +
            C * (√k)⁻¹ * (1 + ‖z‖) ^ 2 * jetNormAt ℝ (r + 1) (D.reading k x s) z := by
  set J₀ : StdSpace ι →L[ℝ] StdSpace ι :=
    LinearMap.toContinuousLinearMap (stdComplexStructure ι).toLinearMap
  set c : ℂ := (2⁻¹ : ℂ) * Complex.I
  -- Instance search does not find the operator norm on this space of bilinear maps unaided.
  let : NormedAddCommGroup ((StdSpace ι →L[ℝ] StdSpace ι) →L[ℝ] StdSpace ι →L[ℝ] ℂ) :=
    ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ ((StdSpace ι →L[ℝ] StdSpace ι) →L[ℝ] StdSpace ι →L[ℝ] ℂ) :=
    ContinuousLinearMap.toNormedSpace
  set B := ContinuousLinearMap.compL ℝ (StdSpace ι) (StdSpace ι) ℂ
  obtain ⟨A₁, hA₁⟩ := D.exists_jetNormAt_connectionReading_le r
  obtain ⟨A₂, hA₂⟩ := D.exists_jetNormAt_chartPushforward_sub_le r
  refine ⟨2 ^ r * ‖B‖ * ‖c‖ * A₁ * A₂, fun {k} hk x s z hz hs ↦ ?_⟩
  set g := D.reading k x s
  set JJ := J.chartPushforward (D.chart k x).toOpenPartialHomeomorph
  set L := D.connectionReading k x s
  have hs' : ContDiffAt ℝ (r + 1) g z := by exact_mod_cast hs
  have hJJ : ContDiffAt ℝ r JJ z :=
    ((J.contDiffOn_chartPushforward (D.chart k x).contMDiffOn
      (D.chart k x).symm.contMDiffOn).contDiffAt
      ((D.chart k x).open_target.mem_nhds (D.ball_subset_target hk x hz))).of_le
      (by exact_mod_cast le_top)
  -- The correction term is bilinear in `c • L` and `J_{k,x} - J₀`.
  have heq : D.dbarReading k x s = modelDbar g + fun w ↦ B ((c • L) w) (JJ w - J₀) := by
    funext w
    rw [D.dbarReading_eq_modelDbar_add, Pi.add_apply, ContinuousLinearMap.compL_apply,
      Pi.smul_apply]
  have hcL : ContDiffAt ℝ r (c • L) z := (D.contDiffAt_connectionReading hs').const_smul c
  have hJJ₀ : ContDiffAt ℝ r (fun w ↦ JJ w - J₀) z := hJJ.sub contDiffAt_const
  have hT := jetNormAt_bilinear_le B hcL hJJ₀
  rw [jetNormAt_smul] at hT
  have hM : ContDiffAt ℝ r (modelDbar g) z := by exact_mod_cast contDiffAt_modelDbar (n := r) hs'
  rw [heq]
  refine (jetNormAt_add_le hM
    ((B.contDiff.contDiffAt.comp z hcL).clm_apply hJJ₀)).trans (add_le_add le_rfl ?_)
  refine hT.trans ?_
  have : 0 ≤ ‖B‖ := ContinuousLinearMap.opNorm_nonneg B
  have hL0 : 0 ≤ jetNormAt ℝ r L z := jetNormAt_nonneg _ _ _
  have : 0 ≤ jetNormAt ℝ r (fun w ↦ JJ w - J₀) z := jetNormAt_nonneg _ _ _
  have : 0 ≤ A₁ * (1 + ‖z‖) * jetNormAt ℝ (r + 1) g z := hL0.trans (hA₁ k x s hs)
  calc 2 ^ r * ‖B‖ * (‖c‖ * jetNormAt ℝ r L z) * jetNormAt ℝ r (fun w ↦ JJ w - J₀) z
      ≤ 2 ^ r * ‖B‖ * (‖c‖ * (A₁ * (1 + ‖z‖) * jetNormAt ℝ (r + 1) g z)) *
          (A₂ * (√k)⁻¹ * (1 + ‖z‖)) := by
        gcongr
        exacts [hA₁ k x s hs, hA₂ hk x hz]
    _ = 2 ^ r * ‖B‖ * ‖c‖ * A₁ * A₂ * (√k)⁻¹ * (1 + ‖z‖) ^ 2 * jetNormAt ℝ (r + 1) g z := by
        ring

/-- **`∂̄` of sections extended by zero against the model `∂̄`.** On a boundaryless manifold, for
every order `r` there is a constant `C`, independent of `k ≥ k₀`, of the centre `x` and of `f`,
such that at every point `z` of the ball of radius `ρ₀ * √k` where `f` is `C^(r + 1)`, the
`r`-jet norm at `z` of the `∂̄` reading in the chart at `x` of the section extended by zero from
`f` is at most that of the model `∂̄` of `f` plus `C * (√k)⁻¹ * (1 + ‖z‖) ^ 2` times the
`(r + 1)`-jet norm of `f` at `z`. -/
theorem exists_jetNormAt_dbarReading_sectionOfReading_le [I.Boundaryless] (r : ℕ) :
    ∃ C : ℝ, ∀ {k : ℕ}, k₀ ≤ k → ∀ (x : M) (f : StdSpace ι → ℂ) {z : StdSpace ι},
      z ∈ ball 0 (ρ₀ * √k) → ContDiffAt ℝ (r + 1 : ℕ) f z →
        jetNormAt ℝ r (D.dbarReading k x (D.sectionOfReading k x f)) z ≤
          jetNormAt ℝ r (modelDbar f) z +
            C * (√k)⁻¹ * (1 + ‖z‖) ^ 2 * jetNormAt ℝ (r + 1) f z := by
  obtain ⟨C, hC⟩ := D.exists_jetNormAt_dbarReading_le r
  refine ⟨C, fun {k} hk x f z hz hf ↦ ?_⟩
  -- Near `z`, the reading of the section is `f`.
  have heq : D.reading k x (D.sectionOfReading k x f) =ᶠ[𝓝 z] f :=
    Filter.eventually_of_mem (isOpen_ball.mem_nhds hz) (D.reading_sectionOfReading hk x f)
  have h := hC hk x (D.sectionOfReading k x f) hz (hf.congr_of_eventuallyEq heq)
  rwa [jetNormAt_congr_of_eventuallyEq r (modelDbar_eventuallyEq heq),
    jetNormAt_congr_of_eventuallyEq (r + 1) heq] at h

/-! ### Gaussian decay and lower bound -/

section RiemannianEDist

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-- **Gaussian decay of sections extended by zero.** Let `M` be a Hausdorff boundaryless manifold,
let `σ` be compatible with `J`, let `M` carry a Riemannian metric whose inner product is
`⟪u, w⟫ = σ(u, J w)`, let `α` be a connection form, `ρ₀ > 0` and `r` an order. Let `f k` be, for
large `k`, `C^r` functions on `StdSpace ι` whose closed supports lie, for every `ε > 0`, in the
ball of radius `ε * √k` for large `k`, with Gaussian `r`-jet bounds uniform in `k`: there are
`A`, `N` and `c > 0` with `jetNormAt ℝ r (f k) z ≤ A * (1 + ‖z‖) ^ N * exp (-c * ‖z‖ ^ 2)` for
large `k` and all `z`. Then there are `C`, `N'` and `c' > 0` such that for large `k` and all points
`x` and `y`, the `r`-jet norm at `y` of the section extended by zero from `f k` in the chart at `x`
is at most `C * (1 + d) ^ N' * exp (-c' * d ^ 2)`, for `d` the real number `√(2π k) · d_g(x, y)`,
the rescaled Riemannian distance. -/
theorem exists_jetNorm_sectionOfReading_le [T2Space M] [I.Boundaryless]
    (hg : ∀ (x : M) (u w : TangentSpace I x), inner ℝ u w = σ.eval₂ x u (J x w))
    (hJ : σ.Compatible J) (hα : IsCircleConnectionForm α) (hρ₀ : 0 < ρ₀) (r : ℕ)
    {f : ℕ → StdSpace ι → ℂ} (hfs : ∀ᶠ k in Filter.atTop, ContDiff ℝ r (f k))
    (hfb : ∀ ε > 0, ∀ᶠ k : ℕ in Filter.atTop, tsupport (f k) ⊆ ball 0 (ε * √k))
    (hfg : ∃ A : ℝ, ∃ N : ℕ, ∃ c > 0, ∀ᶠ k in Filter.atTop, ∀ z,
      jetNormAt ℝ r (f k) z ≤ A * (1 + ‖z‖) ^ N * Real.exp (-c * ‖z‖ ^ 2)) :
    ∃ C : ℝ, ∃ N : ℕ, ∃ c > 0, ∀ᶠ k : ℕ in Filter.atTop, ∀ x y : M,
      D.jetNorm k r (D.sectionOfReading k x (f k)) y ≤
        C * (1 + (ENNReal.ofReal √(2 * Real.pi * k) *
          Manifold.riemannianEDist I x y).toReal) ^ N *
          Real.exp (-c * (ENNReal.ofReal √(2 * Real.pi * k) *
            Manifold.riemannianEDist I x y).toReal ^ 2) := by
  obtain ⟨ρ, hρ, hρρ₀, hchg⟩ := D.jetNorm_le_of_chart_change hg hJ hα hρ₀
  obtain ⟨C₁, hC₁⟩ := hchg r
  obtain ⟨ρ₁, hρ₁, hρ₁ρ₀, hcmp⟩ := D.exists_forall_isComparisonRadius hρ₀
  obtain ⟨A, N, c, hc, hA⟩ := hfg
  set ρ₂ := min ρ ρ₁
  refine ⟨max C₁ 0 * max A 0 * max √2 1 ^ N, 2 * r + N, c / √(3 / 2) ^ 2, by positivity, ?_⟩
  filter_upwards [hfs, hfb ρ₂ (lt_min hρ hρ₁), hA, Filter.eventually_ge_atTop k₀]
    with k hfs hball hA hk
  intro x y
  have hsub {ρ' : ℝ} (h : ρ₂ ≤ ρ') : ball (0 : StdSpace ι) (ρ₂ * √k) ⊆ ball 0 (ρ' * √k) :=
    ball_subset_ball (by gcongr)
  have hfb₀ : tsupport (f k) ⊆ ball 0 (ρ₀ * √k) :=
    hball.trans (hsub ((min_le_left _ _).trans hρρ₀))
  by_cases hy : y ∈ (D.chart k x).symm '' tsupport (f k)
  · obtain ⟨z, hz, rfl⟩ := hy
    have hz₂ := hball hz
    -- Near `z`, the reading in the chart at `x` is `f k`.
    have heq : D.reading k x (D.sectionOfReading k x (f k)) =ᶠ[𝓝 z] f k :=
      Filter.eventually_of_mem (isOpen_ball.mem_nhds (hfb₀ hz))
        (D.reading_sectionOfReading hk x (f k))
    have h1 := hC₁ hk x z (hsub (min_le_left _ _) hz₂) (hfs.contDiffAt.congr_of_eventuallyEq heq)
    rw [jetNormAt_congr_of_eventuallyEq r heq] at h1
    have hz₁ := hsub (min_le_right _ _) hz₂
    set d := (ENNReal.ofReal √(2 * Real.pi * k) *
      Manifold.riemannianEDist I x ((D.chart k x).symm z)).toReal
    -- The rescaled distance `d` and `‖z‖` are comparable.
    have hzd : ‖z‖ ≤ √2 * d :=
      D.norm_le_sqrt_two_mul_toReal_ofReal_mul_riemannianEDist_symm hg hρ₁ρ₀ hk x (hcmp hk x) hz₁
    have hdz : d ≤ √(3 / 2) * ‖z‖ := ENNReal.toReal_le_of_le_ofReal (by positivity)
      (D.ofReal_mul_riemannianEDist_symm_mem_Icc hg hρ₁ρ₀ hk x (hcmp hk x) hz₁).2
    have hgz := Real.one_add_pow_mul_exp_neg_mul_sq_le_of_le_mul N ENNReal.toReal_nonneg
      (by positivity : 0 < √(3 / 2)) hc.le hzd hdz
    calc D.jetNorm k r (D.sectionOfReading k x (f k)) ((D.chart k x).symm z)
        ≤ C₁ * (1 + d) ^ (2 * r) * jetNormAt ℝ r (f k) z := h1
      _ ≤ max C₁ 0 * (1 + d) ^ (2 * r) *
            (max A 0 * ((1 + ‖z‖) ^ N * Real.exp (-c * ‖z‖ ^ 2))) :=
          mul_le_mul (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
            ((hA z).trans (by
              rw [mul_assoc]
              exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)))
            (jetNormAt_nonneg _ _ _) (by positivity)
      _ ≤ max C₁ 0 * (1 + d) ^ (2 * r) * (max A 0 * (max √2 1 ^ N * (1 + d) ^ N *
            Real.exp (-(c / √(3 / 2) ^ 2) * d ^ 2))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hgz (le_max_right _ _))
            (by positivity)
      _ = max C₁ 0 * max A 0 * max √2 1 ^ N * (1 + d) ^ (2 * r + N) *
            Real.exp (-(c / √(3 / 2) ^ 2) * d ^ 2) := by
          ring
  · rw [D.jetNorm_sectionOfReading_eq_zero hk r hfb₀ hy]
    positivity

/-- **Lower bound of sections extended by zero near the centre.** Let `M` be Hausdorff, with a
Riemannian metric whose inner product is `⟪u, w⟫ = σ(u, J w)`, and let `ρ₀ > 0`. Let `f k` be
functions on `StdSpace ι` whose norms are at least `b` on the open unit ball, for large `k`. Then
there is `R > 0` such that for large `k`, all points `x`, and all `y` at rescaled distance
`√(2π k) · d_g(x, y)` less than `R` from `x`, the section extended by zero from `f k` in the chart
at `x` has norm at least `b` at `y`. -/
theorem exists_le_norm_sectionOfReading [T2Space M]
    (hg : ∀ (x : M) (u w : TangentSpace I x), inner ℝ u w = σ.eval₂ x u (J x w))
    (hρ₀ : 0 < ρ₀) {f : ℕ → StdSpace ι → ℂ} {b : ℝ}
    (hf : ∀ᶠ k in Filter.atTop, ∀ z : StdSpace ι, ‖z‖ < 1 → b ≤ ‖f k z‖) :
    ∃ R > 0, ∀ᶠ k : ℕ in Filter.atTop, ∀ x y : M,
      ENNReal.ofReal √(2 * Real.pi * k) * Manifold.riemannianEDist I x y < ENNReal.ofReal R →
        b ≤ ‖D.sectionOfReading k x (f k) y‖ := by
  obtain ⟨ρ₁, hρ₁, hρ₁ρ₀, hcmp⟩ := D.exists_forall_isComparisonRadius hρ₀
  refine ⟨(√2)⁻¹, by positivity, ?_⟩
  have hlarge : ∀ᶠ k : ℕ in Filter.atTop, 1 ≤ ρ₁ * √k :=
    ((Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop
      hρ₁).eventually_ge_atTop 1
  filter_upwards [hf, Filter.eventually_ge_atTop k₀, hlarge] with k hf hk hk1 x y hxy
  have h2 : (0 : ℝ) < √2 := by positivity
  obtain ⟨z, hz, rfl⟩ := D.exists_norm_lt_symm_eq_of_riemannianEDist_lt hg hρ₁ρ₀ hk x (hcmp hk x)
    (R := (√2)⁻¹) (le_mul_of_one_le_right (by positivity) hk1) hxy
  rw [mul_inv_cancel₀ h2.ne'] at hz
  have hz₀ : z ∈ ball (0 : StdSpace ι) (ρ₀ * √k) :=
    mem_ball_zero_iff.2 (hz.trans_le (hk1.trans (by gcongr)))
  rw [← D.norm_reading, D.reading_sectionOfReading hk x (f k) hz₀]
  exact hf z hz

end RiemannianEDist

end RescaledUnitaryCharts

end SymplecticGeometry

end
