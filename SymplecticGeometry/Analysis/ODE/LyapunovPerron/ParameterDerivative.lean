/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

import TauCeti.Analysis.ODE.LyapunovPerron.VectorField
public import TauCeti.Analysis.ODE.LyapunovPerron.Smooth
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import SymplecticGeometry.Topology.ContinuousMap.Bounded.Normed

/-!
# A bounded parameter derivative for local stable solutions

Tau Ceti's `ContinuousLinearMap.exists_localStableGraph_of_contDiffAt` describes the confined
forward solutions of `y' = V (x + y)` near a hyperbolic zero `x` of a `C^n` vector field as a
`C^n` graph `z ↦ z + g z` over a ball in `range P`. It does not say how these solutions depend on
their starting point uniformly in time. This file adds that.

The solutions are built as Lyapunov–Perron fixed points `lyapunovPerronSolution ξ`, which are
bounded continuous curves on `[0, ∞)`. Their dependence on `ξ` is `C^n` as a map into bounded
curves with the sup norm
(`ContinuousLinearMap.contDiffAt_lyapunovPerronSolution_of_uniformContDiffOn`),
so evaluating at a time `t` gives a map whose derivative is bounded by the derivative into
bounded curves, for every `t` at once.

## Main results

* `ContinuousLinearMap.hasFDerivAt_lyapunovPerronSolution_apply`: the value at time `t` of a
  Lyapunov–Perron solution is differentiable in the parameter, with derivative the evaluation at
  `t` of the derivative into bounded curves.
* `ContinuousLinearMap.norm_fderiv_lyapunovPerronSolution_apply_le`: that derivative is bounded,
  uniformly in `t`, by the norm of the derivative into bounded curves.
* `ContinuousLinearMap.exists_localStableGraph_of_contDiffAt_fderiv`: the local stable graph of
  `exists_localStableGraph_of_contDiffAt`, with a confinement radius at most any given bound,
  together with a family of confined forward solutions starting on the graph whose derivatives
  in the starting point are bounded in time.
* `ContinuousLinearMap.localStableGraph_apply_eq_of_le`: two graph maps described by confined
  forward solutions, with nested confinement radii, agree where both are described.
* `ContinuousLinearMap.exists_localStableGraph_of_contDiffAt_infty`: for a field that is `C^∞`
  at the zero, one graph map is `C^n` near `0` for every `n`; it is the graph map of order one,
  which agrees near `0` with the graph map of each order `n` built inside its confinement ball.

The proof of `exists_localStableGraph_of_contDiffAt_fderiv` follows Tau Ceti's proof of
`ContinuousLinearMap.exists_localStableGraph_of_contDiffAt`; its choice of the radii follows the
private Tau Ceti step `TauCeti.exists_vectorField_remainder_data`, proved here again since it is
not public.

## References

* C. Chicone, *Ordinary Differential Equations with Applications*, second edition,
  Springer, 2006, §4.3.
* W. A. Coppel, *Dichotomies in Stability Theory*, Springer, 1978, Chapter 5.
-/

public section

open Filter Metric Set Topology
open scoped NNReal BoundedContinuousFunction

noncomputable section

namespace ContinuousLinearMap

section Solution

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  {K α ε : ℝ≥0} {A P : X →L[ℝ] X} {N : X → X}
  (hs : ∀ t : ℝ, 0 ≤ t → ∀ v : X,
    ‖NormedSpace.exp (t • A) (P v)‖ ≤ K * Real.exp (-α * t) * ‖v‖)
  (hu : ∀ t : ℝ, t ≤ 0 → ∀ v : X,
    ‖NormedSpace.exp (t • A) (v - P v)‖ ≤ K * Real.exp (α * t) * ‖v‖)
  (hα : 0 < α) (hN : LipschitzWith ε N) (hsmall : 2 * K * ε < α)
  {s : Set X} {δ : ℝ} {ξ₀ : X} {n : ℕ}

/-- If the nonlinearity is uniformly `C^n`, `n ≥ 1`, on a set that contains a uniform
neighbourhood of the Lyapunov–Perron solution with parameter `ξ₀`, then the value of the solution
at each time `t` is differentiable in the parameter at `ξ₀`, and its derivative is the evaluation
at `t` of the derivative of the solution as a bounded continuous curve. -/
theorem hasFDerivAt_lyapunovPerronSolution_apply (hn : 1 ≤ n)
    (hNn : TauCeti.UniformContDiffOn ℝ n N s) (hδ : 0 < δ)
    (hξ₀ : ∀ t, ball (lyapunovPerronSolution A P N hs hu hα hN hsmall ξ₀ t) δ ⊆ s)
    (t : ℝ≥0) :
    HasFDerivAt (fun ξ ↦ lyapunovPerronSolution A P N hs hu hα hN hsmall ξ t)
      ((BoundedContinuousFunction.evalCLM ℝ t).comp
        (fderiv ℝ (lyapunovPerronSolution A P N hs hu hα hN hsmall) ξ₀)) ξ₀ :=
  -- The composite `evalCLM ℝ t ∘ S` is `fun ξ ↦ S ξ t` by `evalCLM_apply`, not by unfolding.
  ((BoundedContinuousFunction.evalCLM ℝ t).hasFDerivAt.comp ξ₀
    ((contDiffAt_lyapunovPerronSolution_of_uniformContDiffOn hs hu hα hN hsmall hNn hδ hξ₀
      ).differentiableAt (by exact_mod_cast (Nat.one_le_iff_ne_zero.1 hn))).hasFDerivAt
    ).congr_of_eventuallyEq (Eventually.of_forall fun ξ ↦ by simp)

/-- Under the hypotheses of `ContinuousLinearMap.hasFDerivAt_lyapunovPerronSolution_apply`, the
derivative in the parameter of the value of the Lyapunov–Perron solution at time `t` is bounded,
independently of `t`, by the norm of the derivative of the solution as a bounded continuous
curve. -/
theorem norm_fderiv_lyapunovPerronSolution_apply_le (hn : 1 ≤ n)
    (hNn : TauCeti.UniformContDiffOn ℝ n N s) (hδ : 0 < δ)
    (hξ₀ : ∀ t, ball (lyapunovPerronSolution A P N hs hu hα hN hsmall ξ₀ t) δ ⊆ s)
    (t : ℝ≥0) :
    ‖fderiv ℝ (fun ξ ↦ lyapunovPerronSolution A P N hs hu hα hN hsmall ξ t) ξ₀‖ ≤
      ‖fderiv ℝ (lyapunovPerronSolution A P N hs hu hα hN hsmall) ξ₀‖ := by
  rw [(hasFDerivAt_lyapunovPerronSolution_apply hs hu hα hN hsmall hn hNn hδ hξ₀ t).fderiv]
  exact (opNorm_comp_le _ _).trans <|
    mul_le_of_le_one_left (norm_nonneg _) (BoundedContinuousFunction.norm_evalCLM_le_one t)

end Solution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {V : E → E} {x : E} {n : ℕ} {A P : E →L[ℝ] E} {K α : ℝ≥0}

/-- The radii of the local stable graph: at a point `x` where `V` has derivative `A`, the remainder
`z ↦ V (x + z) - A z` has derivative zero at `0`, is Lipschitz on a closed ball with a constant
small against the dichotomy constants, and is uniformly `C^n` on the open ball; a smaller
parameter radius `ρ` keeps the Lyapunov–Perron bound inside that ball. The radius `r` can be
taken at most any given `r₀ > 0`. -/
private theorem exists_remainder_radii (hn : 1 ≤ n) (hV : ContDiffAt ℝ n V x)
    (hA : HasFDerivAt V A x) (hα : 0 < α) {r₀ : ℝ} (hr₀ : 0 < r₀) :
    ∃ ε : ℝ≥0, ∃ r > 0, r ≤ r₀ ∧ ∃ ρ > 0,
      LipschitzOnWith ε (fun z ↦ V (x + z) - A z) (closedBall 0 r) ∧
      HasFDerivAt (fun z ↦ V (x + z) - A z) (0 : E →L[ℝ] E) 0 ∧
      2 * K * (ε * 2) < α ∧
      TauCeti.UniformContDiffOn ℝ n (fun z ↦ V (x + z) - A z) (ball 0 r) ∧
      (K : ℝ) / (1 - 2 * K * ((ε : ℝ) * 2) / α) * ρ < r := by
  set N : E → E := fun z ↦ V (x + z) - A z
  have hN : ContDiffAt ℝ n N 0 := by
    have hVx : ContDiffAt ℝ n V (x + 0) := by simpa using hV
    exact (hVx.comp 0 (contDiffAt_const.add contDiffAt_id)).sub A.contDiff.contDiffAt
  have hN' : HasFDerivAt N (0 : E →L[ℝ] E) 0 := by
    have hVx : HasFDerivAt (fun z ↦ V (x + z)) A 0 :=
      (hasFDerivAt_comp_add_left x).2 (by simpa using hA)
    simpa only [N, Pi.sub_def, sub_self] using hVx.sub A.hasFDerivAt
  set ε : ℝ≥0 := α / (8 * (K + 1))
  have hε : 0 < ε := by positivity
  have hsmall : 2 * K * (ε * 2) < α := by
    apply NNReal.coe_lt_coe.1
    have hαR : (0 : ℝ) < α := hα
    push_cast [ε]
    rw [div_mul_eq_mul_div, ← mul_div_assoc, div_lt_iff₀ (by positivity)]
    nlinarith [mul_nonneg α.coe_nonneg K.coe_nonneg]
  have hN1 : ContDiffAt ℝ 1 N 0 := hN.of_le (by exact_mod_cast hn)
  obtain ⟨u, hu, hNu⟩ := (hN1.hasStrictFDerivAt hN'
    one_ne_zero).exists_lipschitzOnWith_of_nnNorm_lt ε (by simpa using hε)
  obtain ⟨r₁, hr₁, hr₁u⟩ := Metric.mem_nhds_iff.1 hu
  obtain ⟨r₂, hr₂, hNn⟩ := hN.exists_uniformContDiffOn_closedBall
  set r := min (min (r₁ / 2) r₂) r₀
  have hr : 0 < r := lt_min (lt_min (by positivity) hr₂) hr₀
  obtain ⟨ρ, hρ, hρr⟩ := exists_pos_mul_lt hr ((K : ℝ) / (1 - 2 * K * ((ε : ℝ) * 2) / α))
  refine ⟨ε, r, hr, min_le_right _ _, ρ, hρ, hNu.mono ?_, hN', hsmall, hNn.mono ?_, hρr⟩
  · exact (closedBall_subset_ball (((min_le_left _ _).trans (min_le_left _ _)).trans_lt
      (by linarith))).trans hr₁u
  · exact ball_subset_closedBall.trans
      (closedBall_subset_closedBall ((min_le_left _ _).trans (min_le_right _ _)))

/-- **Local stable graph with a bounded parameter derivative.** Under the hypotheses of
`ContinuousLinearMap.exists_localStableGraph_of_contDiffAt`, and for any bound `r₀ > 0`, there
are a confinement radius `r ≤ r₀`, a parameter radius `ρ` and a graph map `g` with all of that
theorem's conclusions, and moreover a family `y` of curves such that, for each `z ∈ range P` with
`‖z‖ ≤ ρ`, the curve `y z` is a forward integral curve of `fun _ w ↦ V (x + w)` confined to the
closed ball of radius `r`, starting at `z + g z`; each `fun w ↦ y w t`, `t ≥ 0`, is
differentiable at `z`, and its derivative there is bounded independently of `t`. -/
theorem exists_localStableGraph_of_contDiffAt_fderiv
    (hs : ∀ t : ℝ, 0 ≤ t → ∀ z : E,
      ‖NormedSpace.exp (t • A) (P z)‖ ≤ K * Real.exp (-α * t) * ‖z‖)
    (hu : ∀ t : ℝ, t ≤ 0 → ∀ z : E,
      ‖NormedSpace.exp (t • A) (z - P z)‖ ≤ K * Real.exp (α * t) * ‖z‖)
    (hα : 0 < α) (hP : IsIdempotentElem P) (hAP : Commute A P)
    (hn : 1 ≤ n) (hV : ContDiffAt ℝ n V x) (hx : V x = 0) (hA : HasFDerivAt V A x)
    {r₀ : ℝ} (hr₀ : 0 < r₀) :
    ∃ r > 0, r ≤ r₀ ∧ ∃ ρ > 0, ∃ g : E → E, ∃ C : ℝ≥0,
      LipschitzWith C g ∧ g 0 = 0 ∧ HasFDerivAt g (0 : E →L[ℝ] E) 0 ∧
      (∀ z ∈ closedBall (0 : E) ρ, ContDiffAt ℝ n g z) ∧
      (∀ z, P (g z) = 0) ∧ (∀ z, g (P z) = g z) ∧
      {z : E | (∃ y : ℝ → E, IsIntegralCurveOn y (fun _ w ↦ V (x + w)) (Ici 0) ∧
        y 0 = z ∧ MapsTo y (Ici 0) (closedBall 0 r)) ∧ ‖P z‖ ≤ ρ} =
        (fun z ↦ z + g z) '' (Set.range P ∩ closedBall 0 ρ) ∧
      (∀ y : ℝ → E, IsIntegralCurveOn y (fun _ w ↦ V (x + w)) (Ici 0) →
        MapsTo y (Ici 0) (closedBall 0 r) → Tendsto y atTop (𝓝 0)) ∧
      ∃ y : E → ℝ → E, ∀ z ∈ Set.range P ∩ closedBall 0 ρ,
        IsIntegralCurveOn (y z) (fun _ w ↦ V (x + w)) (Ici 0) ∧
        MapsTo (y z) (Ici 0) (closedBall 0 r) ∧ y z 0 = z + g z ∧
        (∀ t, 0 ≤ t → DifferentiableAt ℝ (fun w ↦ y w t) z) ∧
        ∃ C : ℝ, ∀ t, 0 ≤ t → ‖fderiv ℝ (fun w ↦ y w t) z‖ ≤ C := by
  obtain ⟨ε, r, hr, hrr₀, ρ, hρ, hN, hN', hsmall, hNn, hρr⟩ :=
    exists_remainder_radii (K := K) hn hV hA hα hr₀
  set N : E → E := fun z ↦ V (x + z) - A z
  have hN0 : N 0 = 0 := by simp [N, hx]
  have hfield : (fun (_ : ℝ) z ↦ A z + N z) = fun (_ : ℝ) z ↦ V (x + z) := by
    funext _ z
    simp [N]
  have hB : 0 ≤ (K : ℝ) / (1 - 2 * K * ((ε : ℝ) * 2) / α) := by
    have hsmallR : 2 * (K : ℝ) * ((ε : ℝ) * 2) < α := by exact_mod_cast hsmall
    have := (div_lt_one (show (0 : ℝ) < α from hα)).2 hsmallR
    exact div_nonneg K.coe_nonneg (by linarith)
  have hball (z : E) (hz : z ∈ closedBall (0 : E) ρ) :
      (K : ℝ) / (1 - 2 * K * ((ε : ℝ) * 2) / α) * ‖z‖ < r :=
    (mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.1 hz) hB).trans_lt hρr
  -- The cut-off remainder and its Lyapunov–Perron solutions.
  set M : E → E := N ∘ TauCeti.radialRetraction r
  have hM : LipschitzWith (ε * 2) M := hN.comp_radialRetraction hr.le
  have hMn : TauCeti.UniformContDiffOn ℝ n M (ball (0 : E) r) :=
    hNn.congr isOpen_ball fun w hw ↦ by
      simp [M, TauCeti.radialRetraction_of_norm_le (mem_ball_zero_iff.1 hw).le]
  set S := lyapunovPerronSolution A P M hs hu hα hM hsmall
  have hSball (z : E) (hz : z ∈ closedBall (0 : E) ρ) (t : ℝ≥0) :
      ball (S z t) (r - (K : ℝ) / (1 - 2 * K * ((ε : ℝ) * 2) / α) * ρ) ⊆ ball 0 r :=
    ball_lyapunovPerronSolution_comp_radialRetraction_subset hs hu hr.le hN hsmall hα hN0
      (mem_closedBall_zero_iff.1 hz) t
  have hδ : 0 < r - (K : ℝ) / (1 - 2 * K * ((ε : ℝ) * 2) / α) * ρ := sub_pos.2 hρr
  set g := localStableGraphMap A P N r hs hu hr.le hN hsmall
  refine ⟨r, hr, hrr₀, ρ, hρ, g, _, lipschitzWith_localStableGraphMap hs hu hr.le hN hsmall,
    localStableGraphMap_zero hs hu hr.le hN hsmall hN0,
    hasFDerivAt_localStableGraphMap_zero hs hu hr.le hN hsmall hN0 hN',
    fun z hz ↦ contDiffAt_localStableGraphMap_of_uniformContDiffOn hs hu hr.le hN hsmall
      hN0 hNn (hball z hz),
    apply_localStableGraphMap hs hu hr.le hN hsmall hP hAP,
    localStableGraphMap_map hs hu hr.le hN hsmall hP, ?_, ?_,
    fun z t ↦ S z t.toNNReal, fun z hz ↦ ?_⟩
  · have hset := setOf_exists_isIntegralCurveOn_mapsTo_closedBall_eq_image hs hu hr.le hN
      hsmall hN0 hP hAP hρr.le
    rwa [hfield] at hset
  · intro y hy hmaps
    exact tendsto_of_isIntegralCurveOn_mapsTo_closedBall hs hu hN hsmall hN0 hP hAP
      (hfield ▸ hy) hmaps
  obtain ⟨⟨w, rfl⟩, hz⟩ := hz
  have hmaps : MapsTo (fun t : ℝ ↦ S (P w) t.toNNReal) (Ici 0) (closedBall 0 r) :=
    fun t _ ↦ ball_subset_closedBall (hSball _ hz _ (mem_ball_self hδ))
  refine ⟨?_, hmaps, ?_, fun t _ ↦ ?_, ‖fderiv ℝ S (P w)‖, fun t _ ↦ ?_⟩
  · rw [← hfield]
    exact (isIntegralCurveOn_comp_radialRetraction_iff hmaps).2
      (isIntegralCurveOn_lyapunovPerronSolution hs hu hα hM hsmall (P w))
  · have h0 := lyapunovPerronSolution_zero_eq_add_lyapunovPerronGraphMap hs hu hα hM hsmall (P w)
    rw [← localStableGraphMap_def A P N r hs hu hr.le hN hsmall hα, ← mul_apply_eq_comp,
      hP.eq] at h0
    simpa using h0
  · exact (hasFDerivAt_lyapunovPerronSolution_apply hs hu hα hM hsmall hn hMn hδ
      (hSball _ hz) t.toNNReal).differentiableAt
  · exact norm_fderiv_lyapunovPerronSolution_apply_le hs hu hα hM hsmall hn hMn hδ
      (hSball _ hz) t.toNNReal

/-- Two local stable graph maps agree where both are described. Let `g` and `g'` be graph
maps over `range P`, with values in `ker P` and constant along the fibres of `P`, such that the
starting points `z` of forward integral curves of `v` confined to `closedBall 0 r`
(respectively `closedBall 0 r'`) with `‖P z‖ ≤ ρ` (respectively `ρ'`) form the graph of `g`
(respectively `g'`) over `range P ∩ closedBall 0 ρ` (respectively `ρ'`). If `r' ≤ r`, then
`g z = g' z` whenever `‖P z‖ ≤ ρ` and `‖P z‖ ≤ ρ'`. -/
theorem localStableGraph_apply_eq_of_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {P : F →L[ℝ] F} (hP : IsIdempotentElem P) {v : ℝ → F → F} {g g' : F → F}
    {r r' ρ ρ' : ℝ} (hr : r' ≤ r)
    (hPg : ∀ z, P (g z) = 0) (hgP : ∀ z, g (P z) = g z)
    (hPg' : ∀ z, P (g' z) = 0) (hgP' : ∀ z, g' (P z) = g' z)
    (hset : {z : F | (∃ y : ℝ → F, IsIntegralCurveOn y v (Ici 0) ∧
        y 0 = z ∧ MapsTo y (Ici 0) (closedBall 0 r)) ∧ ‖P z‖ ≤ ρ} =
        (fun z ↦ z + g z) '' (Set.range P ∩ closedBall 0 ρ))
    (hset' : {z : F | (∃ y : ℝ → F, IsIntegralCurveOn y v (Ici 0) ∧
        y 0 = z ∧ MapsTo y (Ici 0) (closedBall 0 r')) ∧ ‖P z‖ ≤ ρ'} =
        (fun z ↦ z + g' z) '' (Set.range P ∩ closedBall 0 ρ'))
    {z : F} (hzρ : ‖P z‖ ≤ ρ) (hzρ' : ‖P z‖ ≤ ρ') :
    g z = g' z := by
  have hPP (w : F) : P (P w) = P w := by rw [← mul_apply_eq_comp, hP.eq]
  -- The point of the graph of `g'` over `P z` starts a curve confined to the larger ball, so it
  -- lies on the graph of `g`.
  have hmem : P z + g' (P z) ∈ (fun z ↦ z + g' z) '' (Set.range P ∩ closedBall 0 ρ') :=
    ⟨P z, ⟨⟨z, rfl⟩, mem_closedBall_zero_iff.2 hzρ'⟩, rfl⟩
  rw [← hset'] at hmem
  obtain ⟨⟨y, hy, hy0, hymaps⟩, -⟩ := hmem
  have hmem : P z + g' (P z) ∈ {z : F | (∃ y : ℝ → F, IsIntegralCurveOn y v (Ici 0) ∧
      y 0 = z ∧ MapsTo y (Ici 0) (closedBall 0 r)) ∧ ‖P z‖ ≤ ρ} :=
    ⟨⟨y, hy, hy0, hymaps.mono_right (closedBall_subset_closedBall hr)⟩,
      by rwa [map_add, hPP, hPg', add_zero]⟩
  rw [hset] at hmem
  obtain ⟨w, ⟨⟨u, rfl⟩, -⟩, hw⟩ := hmem
  have hwz : P u = P z := by
    have := congrArg P hw
    rwa [map_add, map_add, hPP, hPP, hPg, hPg', add_zero, add_zero] at this
  rw [hwz, add_right_inj] at hw
  rw [← hgP, hw, hgP']

/-- **Local stable graph of a smooth field.** Under the hypotheses of
`ContinuousLinearMap.exists_localStableGraph_of_contDiffAt_fderiv` for a field `V` that is `C^∞`
at `x`, one graph map `g` has all the conclusions of that theorem at order one, and moreover is
`C^n` on a closed ball around `0` for every `n`, the radius of the ball depending on `n`. -/
theorem exists_localStableGraph_of_contDiffAt_infty
    (hs : ∀ t : ℝ, 0 ≤ t → ∀ z : E,
      ‖NormedSpace.exp (t • A) (P z)‖ ≤ K * Real.exp (-α * t) * ‖z‖)
    (hu : ∀ t : ℝ, t ≤ 0 → ∀ z : E,
      ‖NormedSpace.exp (t • A) (z - P z)‖ ≤ K * Real.exp (α * t) * ‖z‖)
    (hα : 0 < α) (hP : IsIdempotentElem P) (hAP : Commute A P)
    (hV : ContDiffAt ℝ (⊤ : ℕ∞) V x) (hx : V x = 0) (hA : HasFDerivAt V A x)
    {r₀ : ℝ} (hr₀ : 0 < r₀) :
    ∃ r > 0, r ≤ r₀ ∧ ∃ ρ > 0, ∃ g : E → E, ∃ C : ℝ≥0,
      LipschitzWith C g ∧ g 0 = 0 ∧ HasFDerivAt g (0 : E →L[ℝ] E) 0 ∧
      (∀ z ∈ closedBall (0 : E) ρ, ContDiffAt ℝ 1 g z) ∧
      (∀ n : ℕ, ∃ ρₙ > 0, ∀ z ∈ closedBall (0 : E) ρₙ, ContDiffAt ℝ n g z) ∧
      (∀ z, P (g z) = 0) ∧ (∀ z, g (P z) = g z) ∧
      {z : E | (∃ y : ℝ → E, IsIntegralCurveOn y (fun _ w ↦ V (x + w)) (Ici 0) ∧
        y 0 = z ∧ MapsTo y (Ici 0) (closedBall 0 r)) ∧ ‖P z‖ ≤ ρ} =
        (fun z ↦ z + g z) '' (Set.range P ∩ closedBall 0 ρ) ∧
      (∀ y : ℝ → E, IsIntegralCurveOn y (fun _ w ↦ V (x + w)) (Ici 0) →
        MapsTo y (Ici 0) (closedBall 0 r) → Tendsto y atTop (𝓝 0)) ∧
      ∃ y : E → ℝ → E, ∀ z ∈ Set.range P ∩ closedBall 0 ρ,
        IsIntegralCurveOn (y z) (fun _ w ↦ V (x + w)) (Ici 0) ∧
        MapsTo (y z) (Ici 0) (closedBall 0 r) ∧ y z 0 = z + g z ∧
        (∀ t, 0 ≤ t → DifferentiableAt ℝ (fun w ↦ y w t) z) ∧
        ∃ C : ℝ, ∀ t, 0 ≤ t → ‖fderiv ℝ (fun w ↦ y w t) z‖ ≤ C := by
  obtain ⟨r, hr, hrr₀, ρ, hρ, g, C, hgL, hg0, hg', hg1, hPg, hgP, hset, htend, y, hy⟩ :=
    exists_localStableGraph_of_contDiffAt_fderiv (n := 1) hs hu hα hP hAP le_rfl
      (contDiffAt_infty.1 hV 1) hx hA hr₀
  refine ⟨r, hr, hrr₀, ρ, hρ, g, C, hgL, hg0, hg', fun z hz ↦ by simpa using hg1 z hz,
    fun n ↦ ?_, hPg, hgP, hset, htend, y, hy⟩
  -- A graph map of order `n + 1` with a smaller confinement radius agrees with `g` near `0`.
  obtain ⟨r', -, hr', ρ', hρ', g', -, -, -, -, hg'n, hPg', hgP', hset', -⟩ :=
    exists_localStableGraph_of_contDiffAt_fderiv (n := n + 1) hs hu hα hP hAP (by omega)
      (contDiffAt_infty.1 hV _) hx hA hr
  have hU : IsOpen {u : E | ‖P u‖ < min ρ ρ'} :=
    isOpen_lt (continuous_norm.comp P.continuous) continuous_const
  obtain ⟨δ, hδ, hδU⟩ := Metric.isOpen_iff.1 hU 0 (by simpa using lt_min hρ hρ')
  refine ⟨min ρ' (δ / 2), lt_min hρ' (by positivity), fun z hz ↦ ?_⟩
  have hzU : z ∈ {u : E | ‖P u‖ < min ρ ρ'} :=
    hδU (closedBall_subset_ball (half_lt_self hδ)
      (closedBall_subset_closedBall (min_le_right _ _) hz))
  have hgg : g =ᶠ[𝓝 z] g' := Filter.mem_of_superset (hU.mem_nhds hzU) fun u hu ↦
    localStableGraph_apply_eq_of_le hP hr' hPg hgP hPg' hgP' hset hset'
      (le_min_iff.1 (le_of_lt hu)).1 (le_min_iff.1 (le_of_lt hu)).2
  exact ((hg'n z (closedBall_subset_closedBall (min_le_left _ _) hz)).congr_of_eventuallyEq
    hgg).of_le (by exact_mod_cast n.le_succ)

end ContinuousLinearMap

end
