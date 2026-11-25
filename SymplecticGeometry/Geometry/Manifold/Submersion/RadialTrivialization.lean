/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.Geometry.Manifold.Algebra.SMul
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.ContMDiff.Constructions
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import SymplecticGeometry.Analysis.SpecialFunctions.SmoothTransition
public import SymplecticGeometry.Geometry.Manifold.FiberBundle.ChangeModelFiber
public import SymplecticGeometry.Geometry.Manifold.RegularValue.Submersion
public import SymplecticGeometry.Geometry.Manifold.Submersion.ParallelTransport.Smooth
public import TauCeti.Geometry.Manifold.RegularValue.ManifoldLevel
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic
public import TauCeti.Geometry.Manifold.Submersion.Basic
public import TauCeti.Topology.FiberBundle.MapFiber

/-!
# Local trivializations by parallel transport

Let `D` be a `C^n` Ehresmann connection, `1 ≤ n`, on a proper `C^(n+1)` map `f : P → B` of
finite-dimensional boundaryless Hausdorff manifolds. This file builds trivializations of `f` by
parallel transport along a family of curves that join a fixed point `b₀` to the points of an
open set `U`.

For `Γ : B × ℝ → B` that is `C^(n+1)` on `U ×ˢ univ`, with `Γ (b, 0) = b₀` and
`Γ (b, 1) = b` for `b ∈ U`, transport along `u ↦ Γ (b, u)` from `0` to `1` carries the fibre over
`b₀` onto the fibre over `b`, with inverse the transport from `1` to `0`
(`TauCeti.IsEhresmannConnection.invOn_parallelTransport`). Together these maps form a
trivialization of `f` over `U` whose fibre is the fibre `TauCeti.MapFiber f b₀` of `f` over `b₀`,
with the subspace topology (`TauCeti.IsEhresmannConnection.parallelTransportTrivialization`).
Its continuity, and its smoothness below, come from the smoothness of transport in a family of
curves (`TauCeti.IsEhresmannConnection.contMDiffOn_parallelTransport_param`). The
fibre has no manifold structure in general, so the smoothness of the trivialization and of its
inverse is stated through the inclusion of the fibre into `P`: the trivialization, followed by
that inclusion, is `C^n` on its source
(`TauCeti.IsEhresmannConnection.contMDiffOn_parallelTransportTrivialization`), and its inverse is
the restriction of a map `B × P → P` that is `C^n` on `U ×ˢ (f ⁻¹' {b₀})`
(`TauCeti.IsEhresmannConnection.contMDiffOn_parallelTransportTrivialization_symm`). For a
manifold structure on the fibre that makes the inclusion a `C^n` embedding, such as the
regular-fibre atlas of a submersion, these two statements give the fields of Tau Ceti's
`TauCeti.MapFiber.Atlas.IsContMDiff` for the trivialization
(`TauCeti.IsEhresmannConnection.contMDiffOn_parallelTransportTrivialization_of_isSmoothEmbedding`,
`IsEhresmannConnection.contMDiffOn_parallelTransportTrivialization_symm_of_isSmoothEmbedding`).

A trivialization needs a value at every point of `P`, also over points outside `U`, so its fibre
is assumed nonempty. This is no loss: if the fibre over `b₀` is empty and `P` is not, `f` has no
trivialization with that fibre at all.

### The rays of a chart

The curves for the local triviality of a proper submersion are the rays of a chart of `B` from
the chart point of `b₀`, made smooth on all of `ℝ`.

A ray `t ↦ c + t • (y - c)` of a chart, for `t ∈ [0, 1]`, is not a smooth curve on all of `ℝ`
that stays in the chart, while parallel transport is set up for smooth curves `ℝ → B`. So the
rays are reparametrized by a fixed smooth bounded function `SymplecticGeometry.rayParam : ℝ → ℝ`,
equal to the identity on `Set.Icc 0 1` and with values in `(-1, 2)`, chosen with
`SymplecticGeometry.exists_contDiff_eqOn_id_Icc_mem_Ioo`.

For `b₀ : B` with chart point `c = extChartAt J b₀ b₀` and a radius `r` such that the ball of
radius `2 * r` around `c` lies in the chart target, `chartBall J b₀ r` is the open set of points
of the chart source whose chart point lies in the ball of radius `r` around `c`, and
`chartRay J b₀ (b, u)` is `(extChartAt J b₀).symm (c + rayParam u • (extChartAt J b₀ b - c))`.
On `chartBall J b₀ r × ℝ` this family is smooth (`contMDiff_chartRay_chartBall`), its curves
stay in the chart source (`chartRay_mem_source`), where they read as affine rays
(`extChartAt_chartRay`); they start at `b₀` (`chartRay_zero`), end at `b` (`chartRay_one`) and
follow the ray on `[0, 1]` (`chartRay_of_mem_Icc`).

`chartBall` and `chartRay` adapt Tau Ceti's `OpenPartialHomeomorph.chartBall` and the straight
lines of `OpenPartialHomeomorph.chartBallHomotopy`, from an open partial homeomorphism and
continuous maps to the extended chart `extChartAt J b₀` and smooth maps.

### Trivializations with a given fibre

Given a trivialization `e` of `f` with fibre `Z` over a neighbourhood of `b₀`, `C^n` with a `C^n`
inverse, the fibre over `b₀` is identified with `Z` by `e`
(`Bundle.Trivialization.mapFiberHomeomorph`). Changing the fibre of a trivialization by
transport through this identification (`Bundle.Trivialization.transFiberHomeomorph`) keeps it
`C^n` with a `C^n` inverse
(`Bundle.Trivialization.contMDiffOn_transFiberHomeomorph_mapFiberHomeomorph`,
`Bundle.Trivialization.contMDiffOn_transFiberHomeomorph_mapFiberHomeomorph_symm`).
For the rays `chartRay J b₀`, this gives a trivialization with fibre `Z` around `b₀` whose inverse
is transport along the rays of the chart at `b₀`
(`TauCeti.IsEhresmannConnection.exists_trivialization_parallelTransport`). Its smoothness
conditions are those of `TauCeti.MapFiber.Atlas.IsContMDiff`.

### Proper submersions are locally trivial

A smooth proper submersion `f` from a σ-compact manifold has an Ehresmann connection
(`Manifold.IsSubmersion.exists_isEhresmannConnection`), and every value of `f` is a regular value
(`Manifold.IsSubmersion.isRegularValue`).
Transport along the rays of the chart at a value `b₀` then trivializes `f` over `chartBall J b₀ r`,
with fibre `TauCeti.MapFiber f b₀`. With the regular-fibre atlas
`TauCeti.regularFiberChartedSpace` on that fibre, its inclusion into `P` is a smooth embedding
(`TauCeti.isSmoothEmbedding_coe_regularFiber`), so the trivialization is smooth with a smooth
inverse (`Manifold.IsSubmersion.exists_trivialization_of_isProperMap`). The value `b₀` must be
taken in the range of `f`: over a point outside it the fibre is empty, and no map from a nonempty
`P` to `B × ∅` exists.

The converse, that a smooth fibration with compact fibre is proper, is Tau Ceti's
`TauCeti.isProperMap_of_forall_exists_trivialization`. For compact `P`, every continuous map to
the Hausdorff `B` is proper (`Continuous.isProperMap`).

## Main definitions

* `SymplecticGeometry.rayParam`: a smooth bounded function `ℝ → ℝ` that is the identity on
  `[0, 1]`.
* `SymplecticGeometry.chartBall`: the preimage, in the chart source at `b₀`, of a ball around
  the chart point of `b₀`, as an open set of `B`.
* `SymplecticGeometry.chartRay`: the family of reparametrized rays of the chart at `b₀`.

## Main results

* `TauCeti.IsEhresmannConnection.parallelTransportTrivialization`: the trivialization of `f` over
  `U` by transport along a family of curves from `b₀`, with inverse
  `TauCeti.IsEhresmannConnection.parallelTransportTrivialization_symm_apply`.
* `TauCeti.IsEhresmannConnection.contMDiffOn_parallelTransportTrivialization`,
  `TauCeti.IsEhresmannConnection.contMDiffOn_parallelTransportTrivialization_symm`: it is `C^n`,
  with a `C^n` inverse.
* `TauCeti.IsEhresmannConnection.contMDiffOn_parallelTransportTrivialization_of_isSmoothEmbedding`,
  `IsEhresmannConnection.contMDiffOn_parallelTransportTrivialization_symm_of_isSmoothEmbedding`:
  the same for a manifold structure on the fibre whose inclusion into `P` is a `C^n` embedding.
* `TauCeti.IsEhresmannConnection.exists_trivialization_parallelTransport`: around each point of
  the base set of a `C^n` trivialization with fibre `Z`, a `C^n` trivialization with fibre `Z` by
  transport along the rays of a chart.
* `SymplecticGeometry.contMDiff_chartRay_chartBall`: the family of rays is smooth on
  `chartBall J b₀ r × ℝ`.
* `SymplecticGeometry.exists_pos_ball_two_mul_subset_extChartAt_target`: radii for which it is
  defined exist.
* `Manifold.IsSubmersion.exists_trivialization_of_isProperMap`: a smooth proper submersion from
  a σ-compact manifold is smoothly locally trivial, with the regular-fibre atlas on its fibres.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §6.1
  (Exercise 6.1.1).
* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer
  (1993), §9.
-/

public section

noncomputable section

open Function Bundle Set Filter
open scoped ContDiff Manifold Topology

namespace SymplecticGeometry

/-! ### The reparametrization of the rays -/

/-- A smooth function `ℝ → ℝ` that is the identity on `[0, 1]` and takes its values in
`(-1, 2)`, chosen by `SymplecticGeometry.exists_contDiff_eqOn_id_Icc_mem_Ioo`. -/
def rayParam : ℝ → ℝ :=
  (exists_contDiff_eqOn_id_Icc_mem_Ioo (zero_le_one' ℝ) one_pos).choose

private theorem rayParam_spec :
    ContDiff ℝ ∞ rayParam ∧ EqOn rayParam id (Icc 0 1) ∧
      (∀ t, rayParam t ∈ Ioo (0 - 1) (1 + 1)) ∧
      ∀ t ∉ Ioo (0 - 1 : ℝ) (1 + 1), rayParam t = (0 + 1) / 2 :=
  (exists_contDiff_eqOn_id_Icc_mem_Ioo (zero_le_one' ℝ) one_pos).choose_spec

theorem contDiff_rayParam {n : ℕ∞} : ContDiff ℝ n rayParam :=
  rayParam_spec.1.of_le (WithTop.coe_le_coe.2 le_top)

theorem rayParam_of_mem_Icc {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : rayParam t = t :=
  rayParam_spec.2.1 ht

@[simp]
theorem rayParam_zero : rayParam 0 = 0 := rayParam_of_mem_Icc (left_mem_Icc.2 zero_le_one)

@[simp]
theorem rayParam_one : rayParam 1 = 1 := rayParam_of_mem_Icc (right_mem_Icc.2 zero_le_one)

theorem abs_rayParam_le (t : ℝ) : |rayParam t| ≤ 2 := by
  obtain ⟨h₁, h₂⟩ := rayParam_spec.2.2.1 t
  exact abs_le.2 ⟨by linarith, by linarith⟩

/-! ### The rays of a chart -/

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [TopologicalSpace G] (J : ModelWithCorners ℝ F G)
  {B : Type*} [TopologicalSpace B] [ChartedSpace G B]

/-- The points of the chart source at `b₀` whose chart point lies in the ball of radius `r`
around the chart point of `b₀`, as an open set of `B`. -/
def chartBall (b₀ : B) (r : ℝ) : TopologicalSpace.Opens B :=
  ⟨(extChartAt J b₀).source ∩ extChartAt J b₀ ⁻¹' Metric.ball (extChartAt J b₀ b₀) r,
    isOpen_extChartAt_preimage' b₀ Metric.isOpen_ball⟩

theorem mem_chartBall_iff {b₀ b : B} {r : ℝ} :
    b ∈ chartBall J b₀ r ↔
      b ∈ (extChartAt J b₀).source ∧ extChartAt J b₀ b ∈ Metric.ball (extChartAt J b₀ b₀) r :=
  Iff.rfl

theorem mem_chartBall_self (b₀ : B) {r : ℝ} (hr : 0 < r) : b₀ ∈ chartBall J b₀ r :=
  (mem_chartBall_iff J).2 ⟨mem_extChartAt_source b₀, Metric.mem_ball_self hr⟩

theorem chartBall_mem_nhds (b₀ : B) {r : ℝ} (hr : 0 < r) : (chartBall J b₀ r : Set B) ∈ 𝓝 b₀ :=
  (chartBall J b₀ r).isOpen.mem_nhds (mem_chartBall_self J b₀ hr)

/-- The family of rays of the chart at `b₀`, reparametrized by `SymplecticGeometry.rayParam`:
the curve `u ↦ chartRay J b₀ (b, u)` is `(extChartAt J b₀).symm (c + rayParam u • (y - c))`,
where `c` and `y` are the chart points of `b₀` and `b`. -/
def chartRay (b₀ : B) (p : B × ℝ) : B :=
  (extChartAt J b₀).symm
    (extChartAt J b₀ b₀ + rayParam p.2 • (extChartAt J b₀ p.1 - extChartAt J b₀ b₀))

theorem chartRay_def (b₀ : B) (p : B × ℝ) :
    chartRay J b₀ p = (extChartAt J b₀).symm
      (extChartAt J b₀ b₀ + rayParam p.2 • (extChartAt J b₀ p.1 - extChartAt J b₀ b₀)) :=
  (rfl)

@[simp]
theorem chartRay_zero (b₀ b : B) : chartRay J b₀ (b, 0) = b₀ := by
  rw [chartRay_def, rayParam_zero, zero_smul, add_zero, extChartAt_to_inv]

theorem chartRay_one {b₀ b : B} (hb : b ∈ (extChartAt J b₀).source) :
    chartRay J b₀ (b, 1) = b := by
  rw [chartRay_def, rayParam_one, one_smul, add_sub_cancel, (extChartAt J b₀).left_inv hb]

/-- On `[0, 1]`, the curves of `chartRay J b₀` are the rays of the chart at `b₀`. -/
theorem chartRay_of_mem_Icc (b₀ b : B) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    chartRay J b₀ (b, t) = (extChartAt J b₀).symm
      (extChartAt J b₀ b₀ + t • (extChartAt J b₀ b - extChartAt J b₀ b₀)) := by
  rw [chartRay_def, rayParam_of_mem_Icc ht]

/-- If the ball of radius `2 * r` around the chart point `c` of `b₀` lies in the chart target,
then for `b ∈ chartBall J b₀ r` and every `u`, the point `c + rayParam u • (y - c)`, where `y` is
the chart point of `b`, lies in the chart target. -/
theorem add_rayParam_smul_sub_mem_extChartAt_target {b₀ b : B} {r : ℝ}
    (hr : Metric.ball (extChartAt J b₀ b₀) (2 * r) ⊆ (extChartAt J b₀).target)
    (hb : b ∈ chartBall J b₀ r) (u : ℝ) :
    extChartAt J b₀ b₀ + rayParam u • (extChartAt J b₀ b - extChartAt J b₀ b₀) ∈
      (extChartAt J b₀).target := by
  apply hr
  have hb' := ((mem_chartBall_iff J).1 hb).2
  rw [Metric.mem_ball, dist_eq_norm] at hb' ⊢
  rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
  calc |rayParam u| * ‖extChartAt J b₀ b - extChartAt J b₀ b₀‖
      ≤ 2 * ‖extChartAt J b₀ b - extChartAt J b₀ b₀‖ := by
        gcongr; exact abs_rayParam_le u
    _ < 2 * r := by linarith

/-- If the ball of radius `2 * r` around the chart point of `b₀` lies in the chart target, then
for `b ∈ chartBall J b₀ r` the curve `u ↦ chartRay J b₀ (b, u)` stays in the chart source. -/
theorem chartRay_mem_source {b₀ b : B} {r : ℝ}
    (hr : Metric.ball (extChartAt J b₀ b₀) (2 * r) ⊆ (extChartAt J b₀).target)
    (hb : b ∈ chartBall J b₀ r) (u : ℝ) :
    chartRay J b₀ (b, u) ∈ (extChartAt J b₀).source := by
  rw [chartRay_def]
  exact (extChartAt J b₀).map_target (add_rayParam_smul_sub_mem_extChartAt_target J hr hb u)

/-- If the ball of radius `2 * r` around the chart point `c` of `b₀` lies in the chart target,
then for `b ∈ chartBall J b₀ r`, with chart point `y`, the chart reading of the curve
`u ↦ chartRay J b₀ (b, u)` is `u ↦ c + rayParam u • (y - c)`. -/
theorem extChartAt_chartRay {b₀ b : B} {r : ℝ}
    (hr : Metric.ball (extChartAt J b₀ b₀) (2 * r) ⊆ (extChartAt J b₀).target)
    (hb : b ∈ chartBall J b₀ r) (u : ℝ) :
    extChartAt J b₀ (chartRay J b₀ (b, u)) =
      extChartAt J b₀ b₀ + rayParam u • (extChartAt J b₀ b - extChartAt J b₀ b₀) := by
  rw [chartRay_def]
  exact (extChartAt J b₀).right_inv (add_rayParam_smul_sub_mem_extChartAt_target J hr hb u)

/-- In a boundaryless manifold, there are radii `r > 0` for which the ball of radius `2 * r`
around the chart point of `b₀` lies in the chart target. -/
theorem exists_pos_ball_two_mul_subset_extChartAt_target [J.Boundaryless] (b₀ : B) :
    ∃ r > 0, Metric.ball (extChartAt J b₀ b₀) (2 * r) ⊆ (extChartAt J b₀).target := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (isOpen_extChartAt_target (I := J) b₀) _
    (mem_extChartAt_target b₀)
  exact ⟨ε / 2, half_pos hε, by rwa [mul_div_cancel₀ ε two_ne_zero]⟩

variable [IsManifold J ∞ B]

/-- The family of rays of the chart at `b₀` is smooth on `chartBall J b₀ r × ℝ`, if the ball of
radius `2 * r` around the chart point of `b₀` lies in the chart target. -/
theorem contMDiffOn_chartRay {b₀ : B} {r : ℝ}
    (hr : Metric.ball (extChartAt J b₀ b₀) (2 * r) ⊆ (extChartAt J b₀).target) :
    ContMDiffOn (J.prod 𝓘(ℝ, ℝ)) J ∞ (chartRay J b₀) ((chartBall J b₀ r : Set B) ×ˢ univ) := by
  have hφ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ rayParam := contDiff_rayParam.contMDiff
  have hsrc : MapsTo Prod.fst ((chartBall J b₀ r : Set B) ×ˢ (univ : Set ℝ))
      (chartAt G b₀).source := fun p hp ↦ by
    rw [← extChartAt_source J]; exact ((mem_chartBall_iff J).1 hp.1).1
  have hchart : ContMDiffOn (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, F) ∞ (fun p : B × ℝ ↦ extChartAt J b₀ p.1)
      ((chartBall J b₀ r : Set B) ×ˢ univ) :=
    (contMDiffOn_extChartAt (n := ∞)).comp contMDiff_fst.contMDiffOn hsrc
  have hin : ContMDiffOn (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, F) ∞ (fun p : B × ℝ ↦
      extChartAt J b₀ b₀ + rayParam p.2 • (extChartAt J b₀ p.1 - extChartAt J b₀ b₀))
      ((chartBall J b₀ r : Set B) ×ˢ univ) :=
    contMDiffOn_const.add ((hφ.comp contMDiff_snd).contMDiffOn.smul
      (hchart.sub contMDiffOn_const))
  exact (contMDiffOn_extChartAt_symm b₀).comp hin
    fun p hp ↦ add_rayParam_smul_sub_mem_extChartAt_target J hr hp.1 p.2

/-- **The family of rays of a chart is smooth.** If the ball of radius `2 * r` around the chart
point of `b₀` lies in the chart target, then `(b, u) ↦ chartRay J b₀ (b, u)` is smooth on
`chartBall J b₀ r × ℝ`, with `chartBall J b₀ r` an open submanifold of `B`. -/
theorem contMDiff_chartRay_chartBall {b₀ : B} {r : ℝ}
    (hr : Metric.ball (extChartAt J b₀ b₀) (2 * r) ⊆ (extChartAt J b₀).target) :
    ContMDiff (J.prod 𝓘(ℝ, ℝ)) J ∞ (fun p : chartBall J b₀ r × ℝ ↦ chartRay J b₀ (p.1, p.2)) :=
  (contMDiffOn_chartRay J hr).comp_contMDiff
    ((contMDiff_subtypeVal.comp contMDiff_fst).prodMk contMDiff_snd)
    fun p ↦ ⟨p.1.property, mem_univ _⟩

end SymplecticGeometry

namespace TauCeti

namespace IsEhresmannConnection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {P : Type*} [TopologicalSpace P] [ChartedSpace H P] [IsManifold I ∞ P] [I.Boundaryless]
  [T2Space P]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {B : Type*} [TopologicalSpace B] [ChartedSpace G B] [IsManifold J ∞ B] [J.Boundaryless]
  [T2Space B]
  {n : ℕ∞} {f : P → B} {D : Π x : P, Submodule ℝ (TangentSpace I x)}
  (hD : IsEhresmannConnection I J n f D)

section Trivialization

variable {b₀ : B} {U : Set B} {Γ : B × ℝ → B}

include hD in
/-- Transport along `u ↦ Γ (f x, u)` from `1` to `0` takes a point `x` over `U` into the fibre
over `b₀`. -/
private theorem apply_parallelTransport_one_zero (hn : 1 ≤ n) (hf : ContMDiff I J (n + 1) f)
    (hfp : IsProperMap f) (hΓ : ContMDiffOn (J.prod 𝓘(ℝ, ℝ)) J (n + 1) Γ (U ×ˢ univ))
    (hΓ₀ : ∀ b ∈ U, Γ (b, 0) = b₀) (hΓ₁ : ∀ b ∈ U, Γ (b, 1) = b) {x : P} (hx : f x ∈ U) :
    f (hD.parallelTransport (fun u ↦ Γ (f x, u)) 1 0 x) = b₀ := by
  have h := hD.parallelTransport_mem_preimage hn hf hfp
    (γ := fun u ↦ Γ (f x, u))
    (hΓ.comp_contMDiff (contMDiff_const.prodMk contMDiff_id) fun _ ↦ ⟨hx, mem_univ _⟩)
    (hΓ₁ _ hx).symm 0
  rwa [hΓ₀ _ hx] at h

include hD in
/-- Transport along `u ↦ Γ (b, u)` from `0` to `1` takes a point `v` of the fibre over `b₀` into
the fibre over `b ∈ U`. -/
private theorem apply_parallelTransport_zero_one (hn : 1 ≤ n) (hf : ContMDiff I J (n + 1) f)
    (hfp : IsProperMap f) (hΓ : ContMDiffOn (J.prod 𝓘(ℝ, ℝ)) J (n + 1) Γ (U ×ˢ univ))
    (hΓ₀ : ∀ b ∈ U, Γ (b, 0) = b₀) (hΓ₁ : ∀ b ∈ U, Γ (b, 1) = b) {b : B} (hb : b ∈ U) {v : P}
    (hv : f v = b₀) : f (hD.parallelTransport (fun u ↦ Γ (b, u)) 0 1 v) = b := by
  have h := hD.parallelTransport_mem_preimage hn hf hfp
    (γ := fun u ↦ Γ (b, u))
    (hΓ.comp_contMDiff (contMDiff_const.prodMk contMDiff_id) fun _ ↦ ⟨hb, mem_univ _⟩)
    (hv.trans (hΓ₀ _ hb).symm) 1
  rwa [hΓ₁ _ hb] at h

variable [Nonempty (MapFiber f b₀)]

open Classical in
/-- **The trivialization by parallel transport along a family of curves.** Let `D` be a `C^n`
Ehresmann connection, `1 ≤ n`, on a proper `C^(n+1)` map `f : P → B` of finite-dimensional
boundaryless Hausdorff manifolds, `U` an open set of `B`, and `Γ : B × ℝ → B` a family of curves,
`C^(n+1)` on `U ×ˢ univ`, from `Γ (b, 0) = b₀` to `Γ (b, 1) = b` for each `b ∈ U`. The
trivialization of `f` over `U` with fibre `TauCeti.MapFiber f b₀` sends a point `x` over `U` to
`f x` and the transport of `x` along `u ↦ Γ (f x, u)` from `1` to `0`; its inverse sends `(b, v)`
to the transport of `v` along `u ↦ Γ (b, u)` from `0` to `1`.

Points of `P` outside `f ⁻¹' U` are sent to an arbitrary point of the fibre, which is assumed
nonempty. -/
def parallelTransportTrivialization (hn : 1 ≤ n) (hf : ContMDiff I J (n + 1) f)
    (hfp : IsProperMap f) (hU : IsOpen U)
    (hΓ : ContMDiffOn (J.prod 𝓘(ℝ, ℝ)) J (n + 1) Γ (U ×ˢ univ))
    (hΓ₀ : ∀ b ∈ U, Γ (b, 0) = b₀) (hΓ₁ : ∀ b ∈ U, Γ (b, 1) = b) :
    Trivialization (MapFiber f b₀) f where
  toFun x := (f x, if hx : f x ∈ U then
    ⟨hD.parallelTransport (fun u ↦ Γ (f x, u)) 1 0 x,
      hD.apply_parallelTransport_one_zero hn hf hfp hΓ hΓ₀ hΓ₁ hx⟩
    else Classical.arbitrary _)
  invFun p := hD.parallelTransport (fun u ↦ Γ (p.1, u)) 0 1 p.2
  source := f ⁻¹' U
  target := U ×ˢ univ
  map_source' _ hx := ⟨hx, mem_univ _⟩
  map_target' p hp := by
    rw [mem_preimage, hD.apply_parallelTransport_zero_one hn hf hfp hΓ hΓ₀ hΓ₁ hp.1
      p.2.property]
    exact hp.1
  left_inv' x hx := by
    have hγ : ContMDiff 𝓘(ℝ, ℝ) J (n + 1) (fun u ↦ Γ (f x, u)) :=
      hΓ.comp_contMDiff (contMDiff_const.prodMk contMDiff_id) fun _ ↦ ⟨hx, mem_univ _⟩
    simp only [dite_eq_left (show f x ∈ U from hx)]
    exact (hD.invOn_parallelTransport hn hf hfp hγ 1 0).1 (hΓ₁ _ hx).symm
  right_inv' := by
    rintro ⟨b, v⟩ ⟨hb, -⟩
    have hγ : ContMDiff 𝓘(ℝ, ℝ) J (n + 1) (fun u ↦ Γ (b, u)) :=
      hΓ.comp_contMDiff (contMDiff_const.prodMk contMDiff_id) fun _ ↦ ⟨hb, mem_univ _⟩
    have hfy : f (hD.parallelTransport (fun u ↦ Γ (b, u)) 0 1 v) = b :=
      hD.apply_parallelTransport_zero_one hn hf hfp hΓ hΓ₀ hΓ₁ hb v.property
    refine Prod.ext hfy (Subtype.ext ?_)
    simp only [hfy, show b ∈ U from hb, ↓reduceDIte]
    exact (hD.invOn_parallelTransport hn hf hfp hγ 0 1).1 (v.property.trans (hΓ₀ _ hb).symm)
  open_source := hU.preimage hf.continuous
  open_target := hU.prod isOpen_univ
  continuousOn_toFun := by
    refine hf.continuous.continuousOn.prodMk ?_
    refine (Topology.IsInducing.continuousOn_iff (g := (Subtype.val : MapFiber f b₀ → P))
      Topology.IsEmbedding.subtypeVal.isInducing).2 ?_
    refine ((hD.contMDiffOn_parallelTransport_param hn hf hfp hU hΓ 1 0).continuousOn.comp
      (hf.continuous.prodMk continuous_id).continuousOn fun x hx ↦ ⟨hx, (hΓ₁ _ hx).symm⟩).congr
      fun x hx ↦ ?_
    simp only [comp_apply, id_eq, dite_eq_left (show f x ∈ U from hx)]
  continuousOn_invFun :=
    (hD.contMDiffOn_parallelTransport_param hn hf hfp hU hΓ 0 1).continuousOn.comp
      (continuous_fst.prodMk (continuous_subtypeVal.comp continuous_snd)).continuousOn
      fun p hp ↦ ⟨hp.1, p.2.property.trans (hΓ₀ _ hp.1).symm⟩
  baseSet := U
  open_baseSet := hU
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

variable (hn : 1 ≤ n) (hf : ContMDiff I J (n + 1) f) (hfp : IsProperMap f) (hU : IsOpen U)
  (hΓ : ContMDiffOn (J.prod 𝓘(ℝ, ℝ)) J (n + 1) Γ (U ×ˢ univ))
  (hΓ₀ : ∀ b ∈ U, Γ (b, 0) = b₀) (hΓ₁ : ∀ b ∈ U, Γ (b, 1) = b)

@[simp]
theorem parallelTransportTrivialization_baseSet :
    (hD.parallelTransportTrivialization hn hf hfp hU hΓ hΓ₀ hΓ₁).baseSet = U :=
  (rfl)

@[simp]
theorem parallelTransportTrivialization_apply_fst (x : P) :
    (hD.parallelTransportTrivialization hn hf hfp hU hΓ hΓ₀ hΓ₁ x).1 = f x :=
  (rfl)

/-- The trivialization by transport sends a point `x` over `U` to the transport of `x` along
`u ↦ Γ (f x, u)` from `1` to `0`, in the fibre over `b₀`. -/
@[simp]
theorem coe_parallelTransportTrivialization_apply_snd {x : P} (hx : f x ∈ U) :
    ((hD.parallelTransportTrivialization hn hf hfp hU hΓ hΓ₀ hΓ₁ x).2 : P) =
      hD.parallelTransport (fun u ↦ Γ (f x, u)) 1 0 x :=
  congrArg Subtype.val (dite_eq_left hx)

/-- The inverse of the trivialization by transport sends `(b, v)` to the transport of `v` along
`u ↦ Γ (b, u)` from `0` to `1`. -/
@[simp]
theorem parallelTransportTrivialization_symm_apply (p : B × MapFiber f b₀) :
    (hD.parallelTransportTrivialization hn hf hfp hU hΓ hΓ₀ hΓ₁).toOpenPartialHomeomorph.symm p =
      hD.parallelTransport (fun u ↦ Γ (p.1, u)) 0 1 p.2 :=
  (rfl)

/-- **The trivialization by transport is `C^n`.** Followed by the inclusion of the fibre
`TauCeti.MapFiber f b₀` into `P`, the trivialization by transport is `C^n` on its source. -/
theorem contMDiffOn_parallelTransportTrivialization :
    ContMDiffOn I (J.prod I) n
      (fun x ↦ ((hD.parallelTransportTrivialization hn hf hfp hU hΓ hΓ₀ hΓ₁ x).1,
        ((hD.parallelTransportTrivialization hn hf hfp hU hΓ hΓ₀ hΓ₁ x).2 : P)))
      (hD.parallelTransportTrivialization hn hf hfp hU hΓ hΓ₀ hΓ₁).source := by
  have hfn : ContMDiff I J n f := hf.of_le le_self_add
  have h := (hD.contMDiffOn_parallelTransport_param hn hf hfp hU hΓ 1 0).comp
    (hfn.prodMk contMDiff_id).contMDiffOn (s := f ⁻¹' U) fun x hx ↦ ⟨hx, (hΓ₁ _ hx).symm⟩
  refine (hfn.contMDiffOn.prodMk h).congr fun x hx ↦ Prod.ext rfl ?_
  exact hD.coe_parallelTransportTrivialization_apply_snd hn hf hfp hU hΓ hΓ₀ hΓ₁ hx

/-- **The inverse of the trivialization by transport is `C^n`.** The map
`(b, x) ↦` transport of `x` along `u ↦ Γ (b, u)` from `0` to `1` is `C^n` on
`U ×ˢ (f ⁻¹' {b₀})`; by `TauCeti.IsEhresmannConnection.parallelTransportTrivialization_symm_apply`,
the inverse of the trivialization by transport is its composition with the inclusion of the
fibre `TauCeti.MapFiber f b₀` into `P`. -/
theorem contMDiffOn_parallelTransportTrivialization_symm :
    ContMDiffOn (J.prod I) I n (fun p : B × P ↦ hD.parallelTransport (fun u ↦ Γ (p.1, u)) 0 1 p.2)
      ((hD.parallelTransportTrivialization hn hf hfp hU hΓ hΓ₀ hΓ₁).baseSet ×ˢ (f ⁻¹' {b₀})) :=
  (hD.contMDiffOn_parallelTransport_param hn hf hfp hU hΓ 0 1).mono fun p hp ↦
    ⟨hp.1, (hp.2 : f p.2 = b₀).trans (hΓ₀ _ hp.1).symm⟩

section Atlas

variable {EZ : Type*} [NormedAddCommGroup EZ] [NormedSpace ℝ EZ]
  {HZ : Type*} [TopologicalSpace HZ] {IZ : ModelWithCorners ℝ EZ HZ}
  [ChartedSpace HZ (MapFiber f b₀)]

/-- **The trivialization by transport is `C^n` for a manifold structure on the fibre.** For a
manifold structure on the fibre `TauCeti.MapFiber f b₀` whose inclusion into `P` is a `C^n`
embedding, the trivialization by transport is `C^n` on its source. -/
theorem contMDiffOn_parallelTransportTrivialization_of_isSmoothEmbedding
    (hι : Manifold.IsSmoothEmbedding IZ I n (Subtype.val : MapFiber f b₀ → P)) :
    ContMDiffOn I (J.prod IZ) n (hD.parallelTransportTrivialization hn hf hfp hU hΓ hΓ₀ hΓ₁)
      (hD.parallelTransportTrivialization hn hf hfp hU hΓ hΓ₀ hΓ₁).source := by
  have h := hD.contMDiffOn_parallelTransportTrivialization hn hf hfp hU hΓ hΓ₀ hΓ₁
  exact (contMDiff_fst.comp_contMDiffOn h).prodMk
    (hι.contMDiffOn_iff_comp.2 (contMDiff_snd.comp_contMDiffOn h))

/-- **The inverse of the trivialization by transport is `C^n` for a manifold structure on the
fibre.** For a manifold structure on the fibre `TauCeti.MapFiber f b₀` whose inclusion into `P`
is a `C^n` embedding, the inverse of the trivialization by transport is `C^n` on its target. -/
theorem contMDiffOn_parallelTransportTrivialization_symm_of_isSmoothEmbedding
    (hι : Manifold.IsSmoothEmbedding IZ I n (Subtype.val : MapFiber f b₀ → P)) :
    ContMDiffOn (J.prod IZ) I n
      (hD.parallelTransportTrivialization hn hf hfp hU hΓ hΓ₀ hΓ₁).toOpenPartialHomeomorph.symm
      (hD.parallelTransportTrivialization hn hf hfp hU hΓ hΓ₀ hΓ₁).target := by
  refine ((hD.contMDiffOn_parallelTransportTrivialization_symm hn hf hfp hU hΓ hΓ₀ hΓ₁).comp
    (contMDiff_fst.prodMk (hι.contMDiff.comp contMDiff_snd)).contMDiffOn
    fun p hp ↦ ⟨?_, p.2.property⟩).congr fun p _ ↦ ?_
  · rw [Trivialization.target_eq] at hp
    exact hp.1
  · exact hD.parallelTransportTrivialization_symm_apply hn hf hfp hU hΓ hΓ₀ hΓ₁ p

end Atlas

end Trivialization

section Radial

variable {EZ : Type*} [NormedAddCommGroup EZ] [NormedSpace ℝ EZ]
  {HZ : Type*} [TopologicalSpace HZ] {IZ : ModelWithCorners ℝ EZ HZ}
  {Z : Type*} [TopologicalSpace Z] [ChartedSpace HZ Z]

/-- **Local trivializations by parallel transport along the rays of a chart.** Let `D` be a `C^n`
Ehresmann connection, `1 ≤ n`, on a proper `C^(n+1)` map `f : P → B` of finite-dimensional
boundaryless Hausdorff manifolds, and `e` a trivialization of `f` with fibre `Z` that is `C^n`
on its source, with inverse `C^n` on its target, and `b₀ ∈ e.baseSet`. Then there is a
trivialization `e'` of `f` with fibre `Z`, `C^n` on its source with inverse `C^n` on its target,
with `b₀ ∈ e'.baseSet`, such that for each `b ∈ e'.baseSet` there is a smooth curve `γ`, equal on
`[0, 1]` to the ray `t ↦ (extChartAt J b₀).symm (c + t • (y - c))` of the chart at `b₀` from
`c = extChartAt J b₀ b₀` to `y = extChartAt J b₀ b`, with
`e'.symm (b, v) = hD.parallelTransport γ 0 1 (e.symm (b₀, v))` for every `v : Z`.

The smoothness conditions on `e` and on `e'` are the fields of `TauCeti.MapFiber.Atlas.IsContMDiff`
for a single trivialization. -/
theorem exists_trivialization_parallelTransport (hn : 1 ≤ n) (hf : ContMDiff I J (n + 1) f)
    (hfp : IsProperMap f) (e : Trivialization Z f)
    (he : ContMDiffOn I (J.prod IZ) n e e.source)
    (he' : ContMDiffOn (J.prod IZ) I n e.toOpenPartialHomeomorph.symm e.target)
    {b₀ : B} (hb₀ : b₀ ∈ e.baseSet) :
    ∃ e' : Trivialization Z f, ContMDiffOn I (J.prod IZ) n e' e'.source ∧
      ContMDiffOn (J.prod IZ) I n e'.toOpenPartialHomeomorph.symm e'.target ∧
      b₀ ∈ e'.baseSet ∧ ∀ b ∈ e'.baseSet, ∃ γ : ℝ → B, ContMDiff 𝓘(ℝ, ℝ) J ∞ γ ∧
        EqOn γ (fun t ↦ (extChartAt J b₀).symm
          (extChartAt J b₀ b₀ + t • (extChartAt J b₀ b - extChartAt J b₀ b₀))) (Icc 0 1) ∧
        ∀ v : Z, e'.toOpenPartialHomeomorph.symm (b, v) =
          hD.parallelTransport γ 0 1 (e.toOpenPartialHomeomorph.symm (b₀, v)) := by
  obtain ⟨r, hr, hball⟩ := SymplecticGeometry.exists_pos_ball_two_mul_subset_extChartAt_target J b₀
  set U : Set B := (SymplecticGeometry.chartBall J b₀ r : Set B)
  have hU : IsOpen U := (SymplecticGeometry.chartBall J b₀ r).isOpen
  have hb₀U : b₀ ∈ U := SymplecticGeometry.mem_chartBall_self J b₀ hr
  have hΓ : ContMDiffOn (J.prod 𝓘(ℝ, ℝ)) J ∞ (SymplecticGeometry.chartRay J b₀) (U ×ˢ univ) :=
    SymplecticGeometry.contMDiffOn_chartRay J hball
  -- The curve of the family through `b ∈ U`, smooth and equal to the ray on `[0, 1]`.
  have hγ : ∀ b ∈ U, ContMDiff 𝓘(ℝ, ℝ) J ∞ (fun u ↦ SymplecticGeometry.chartRay J b₀ (b, u)) ∧
      EqOn (fun u ↦ SymplecticGeometry.chartRay J b₀ (b, u)) (fun t ↦ (extChartAt J b₀).symm
        (extChartAt J b₀ b₀ + t • (extChartAt J b₀ b - extChartAt J b₀ b₀))) (Icc 0 1) :=
    fun b hb ↦ ⟨hΓ.comp_contMDiff (contMDiff_const.prodMk contMDiff_id) fun _ ↦ ⟨hb, mem_univ _⟩,
      fun _ ht ↦ SymplecticGeometry.chartRay_of_mem_Icc J b₀ b ht⟩
  rcases isEmpty_or_nonempty Z with hZ | hZ
  · -- If `Z` is empty, so is `P`, and the restriction of `e` to `U` will do.
    have : IsEmpty P := ⟨fun x ↦ hZ.false (e x).2⟩
    refine ⟨e.restrOpen U hU, fun x ↦ isEmptyElim x, fun p ↦ isEmptyElim p.2, ⟨hb₀, hb₀U⟩,
      fun b hb ↦ ⟨_, (hγ b hb.2).1, (hγ b hb.2).2, fun v ↦ isEmptyElim v⟩⟩
  have : Nonempty (MapFiber f b₀) :=
    ⟨⟨e.toOpenPartialHomeomorph.symm (b₀, Classical.arbitrary Z), e.proj_symm_apply' hb₀⟩⟩
  have hΓn : ContMDiffOn (J.prod 𝓘(ℝ, ℝ)) J (n + 1) (SymplecticGeometry.chartRay J b₀)
      (U ×ˢ univ) :=
    hΓ.of_le (WithTop.coe_le_coe.2 le_top)
  have hΓ₀ : ∀ b ∈ U, SymplecticGeometry.chartRay J b₀ (b, 0) = b₀ :=
    fun b _ ↦ SymplecticGeometry.chartRay_zero J b₀ b
  have hΓ₁ : ∀ b ∈ U, SymplecticGeometry.chartRay J b₀ (b, 1) = b :=
    fun b hb ↦ SymplecticGeometry.chartRay_one J ((SymplecticGeometry.mem_chartBall_iff J).1 hb).1
  set T := hD.parallelTransportTrivialization hn hf hfp hU hΓn hΓ₀ hΓ₁
  -- The fibre over `b₀` is read in `Z` through `e`.
  refine ⟨T.transFiberHomeomorph (e.mapFiberHomeomorph hb₀),
    T.contMDiffOn_transFiberHomeomorph_mapFiberHomeomorph hb₀
      (hD.contMDiffOn_parallelTransportTrivialization hn hf hfp hU hΓn hΓ₀ hΓ₁) he,
    T.contMDiffOn_transFiberHomeomorph_mapFiberHomeomorph_symm hb₀
      (hD.contMDiffOn_parallelTransportTrivialization_symm hn hf hfp hU hΓn hΓ₀ hΓ₁)
      (fun _ _ _ ↦ hD.parallelTransportTrivialization_symm_apply hn hf hfp hU hΓn hΓ₀ hΓ₁ _) he',
    hb₀U, fun b hb ↦ ⟨_, (hγ b hb).1, (hγ b hb).2, fun v ↦ by
      simp [T, parallelTransportTrivialization_symm_apply]⟩⟩

end Radial

end IsEhresmannConnection

end TauCeti
namespace Manifold.IsSubmersion

open TauCeti SymplecticGeometry Module

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {P : Type*} [TopologicalSpace P] [ChartedSpace H P] [IsManifold I ∞ P] [I.Boundaryless]
  [T2Space P] [SigmaCompactSpace P]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {B : Type*} [TopologicalSpace B] [ChartedSpace G B] [IsManifold J ∞ B] [J.Boundaryless]
  [T2Space B] {f : P → B}

/-- **Local triviality of proper submersions.** Let `f : P → B` be a smooth proper submersion
from a σ-compact Hausdorff manifold to a Hausdorff manifold, both finite-dimensional and
boundaryless, and let `b₀` be a value of `f`. Give the fibre `TauCeti.MapFiber f b₀` its
regular-fibre atlas `TauCeti.regularFiberChartedSpace`. Then `f` has a trivialization with
fibre `TauCeti.MapFiber f b₀` whose base set contains `b₀`, smooth on its source with a smooth
inverse on its target: these are the fields of `TauCeti.MapFiber.Atlas.IsContMDiff`.

The trivialization is by parallel transport, for an Ehresmann connection of `f`, along the rays
of the chart of `B` at `b₀`. -/
theorem exists_trivialization_of_isProperMap (hf : IsSubmersion I J ∞ f) (hfp : IsProperMap f)
    {b₀ : B} (hb₀ : b₀ ∈ range f) :
    let := regularFiberChartedSpace (m := ∞) (c := b₀) (by simp) hf.contMDiff
      BoundarylessManifold.isInteriorPoint (hf.isRegularValue (by simp) b₀)
    ∃ e : Trivialization (MapFiber f b₀) f, b₀ ∈ e.baseSet ∧
      ContMDiffOn I (J.prod 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ F) → ℝ)) ∞ e e.source ∧
      ContMDiffOn (J.prod 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ F) → ℝ)) I ∞
        e.toOpenPartialHomeomorph.symm e.target := by
  intro
  have hι := isSmoothEmbedding_coe_regularFiber (m := ∞) (c := b₀) (by simp) hf.contMDiff
    BoundarylessManifold.isInteriorPoint (hf.isRegularValue (by simp) b₀)
  obtain ⟨x₀, rfl⟩ := hb₀
  have : Nonempty (MapFiber f (f x₀)) := ⟨⟨x₀, rfl⟩⟩
  obtain ⟨D, hD⟩ := hf.exists_isEhresmannConnection (m := ⊤) (by simp)
  obtain ⟨r, hr, hball⟩ := exists_pos_ball_two_mul_subset_extChartAt_target J (f x₀)
  have hf' : ContMDiff I J ((⊤ : ℕ∞) + 1) f := hf.contMDiff.of_le (by simp)
  have hΓ : ContMDiffOn (J.prod 𝓘(ℝ, ℝ)) J ((⊤ : ℕ∞) + 1) (chartRay J (f x₀))
      ((chartBall J (f x₀) r : Set B) ×ˢ univ) :=
    (contMDiffOn_chartRay J hball).of_le (by simp)
  have hΓ₀ : ∀ b ∈ (chartBall J (f x₀) r : Set B), chartRay J (f x₀) (b, 0) = f x₀ :=
    fun b _ ↦ chartRay_zero J (f x₀) b
  have hΓ₁ : ∀ b ∈ (chartBall J (f x₀) r : Set B), chartRay J (f x₀) (b, 1) = b :=
    fun b hb ↦ chartRay_one J ((mem_chartBall_iff J).1 hb).1
  have hU := (chartBall J (f x₀) r).isOpen
  exact ⟨hD.parallelTransportTrivialization (by simp) hf' hfp hU hΓ hΓ₀ hΓ₁,
    mem_chartBall_self J _ hr,
    hD.contMDiffOn_parallelTransportTrivialization_of_isSmoothEmbedding (by simp) hf' hfp hU hΓ hΓ₀
      hΓ₁ hι,
    hD.contMDiffOn_parallelTransportTrivialization_symm_of_isSmoothEmbedding (by simp) hf' hfp hU
      hΓ hΓ₀ hΓ₁ hι⟩

end Manifold.IsSubmersion

end
