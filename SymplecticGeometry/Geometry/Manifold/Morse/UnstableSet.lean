/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Stable.Manifold
public import TauCeti.Geometry.Manifold.Morse.PseudoGradient.Existence
public import TauCeti.Geometry.Manifold.IntegralCurve.GlobalFlow
public import Mathlib.Analysis.InnerProductSpace.PiL2
import TauCeti.Analysis.ODE.ScalarLinear
import TauCeti.Geometry.Manifold.IntegralCurve.Interval
import TauCeti.Geometry.Manifold.MFDeriv.Curve
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import Mathlib.Analysis.Calculus.Deriv.Prod
import SymplecticGeometry.Analysis.SpecialFunctions.Log.Unbounded

/-!
# The unstable set near a critical point where the field is linear

Let `X` be a complete `C¹` vector field on a boundaryless manifold `M` modelled on `E`, with flow
`Φ = TauCeti.globalFlow X`, and let `φ` be a Morse chart at `p` on whose source `X` is the linear
field `TauCeti.MorseChart.field` of the chart, `z ↦ (-wᵢ zᵢ)ᵢ` in its coordinates. Nothing is
assumed of `X` away from the chart, and `M` need not be compact. To ask this only on an open
neighbourhood `V` of `p`, apply the results to the restricted chart `φ.restr`.

Let `B` be the image under the chart of a closed Euclidean ball of radius `ρ > 0` in the
coordinates of negative weight (the other coordinates being `0`), and assume that this ball lies in
the target of the chart. The continuous linear map `TauCeti.MorseChart.negativeExtendL` sends
coordinates `c` in this Euclidean space to the vector of the model space with coordinates `c` of
negative weight and `0` of positive weight. We show:

* `TauCeti.MorseChart.globalFlow_toChart_symm_negativeExtend_of_norm_le`: in backward time the
  flow moves the points of `B` radially: for `t ≤ 0`, `Φ t` sends the point with coordinates `c`
  to the point with coordinates `e^{t} c`;
* `TauCeti.MorseChart.mapsTo_closedBall_unstableSet`: `B` lies in the unstable set of `p`;
* `TauCeti.MorseChart.exists_globalFlow_eq_of_mem_unstableSet`: every point `x ≠ p` of the
  unstable set of `p` is `Φ s y` for a point `y` of the boundary sphere of `B`, with `s ≥ 0` unless
  `x ∈ B`, and `TauCeti.MorseChart.eq_of_globalFlow_eq_globalFlow`: the flow line of `x` meets that
  sphere only once.

Then, for a function `θ` on the coordinates of negative weight, we study the map
`F c = Φ (θ c) y_c`, where `y_c` is the point with coordinates `c` of negative weight and `0` of
positive weight: each point of the ball is moved along its flow line for the time `θ c`.

* `TauCeti.MorseChart.globalFlow_toChart_symm_negativeExtend_smul`: for `‖u‖ ≤ ρ` and
  `0 < r ≤ 1`, the flow for the time `s` from `y_{r u}` is the flow for the time `s + log r`
  from `y_u`;
* `TauCeti.MorseChart.injOn_globalFlow_toChart_symm_negativeExtend`: `F` is injective on the
  closed ball when `r ↦ θ (r • u) + log r` is strictly monotone on `(0, 1]` for each `u` of the
  sphere; the centre goes to `p`
  (`TauCeti.MorseChart.globalFlow_toChart_symm_negativeExtend_zero`), and on each ray the radius
  is recovered from this function;
* `TauCeti.MorseChart.mapsTo_globalFlow_closedBall_unstableSet`: `F` maps the ball into the
  unstable set of `p`;
* `TauCeti.MorseChart.globalFlow_mem_image_closedBall` and
  `TauCeti.MorseChart.globalFlow_mem_image_ball`: for `θ` continuous on the closed ball, `‖u‖ ≤ ρ`
  and `s ≤ θ u` (resp. `s < θ u`), the point `Φ s y_u` is the image under `F` of a point of
  the closed (resp. open) ball, found by the intermediate value theorem
  `Real.exists_mem_Ioc_add_log_eq`. With
  `TauCeti.MorseChart.exists_globalFlow_eq_of_mem_unstableSet`, this describes which points of
  the unstable set `F` reaches.

The last step of the first list rests on
`TauCeti.MorseBottChart.coord_toChart_of_isMIntegralCurve`: in any Morse–Bott chart in which
`X` reads `(-wᵢ zᵢ)ᵢ`, an integral curve of `X` is read in the
coordinates as the linear flow `TauCeti.MorseBottChart.linearFlow` while it stays in the source of
the chart; each coordinate solves a scalar linear equation, solved by
`TauCeti.eq_exp_smul_of_hasDerivAt_smul`. The backward orbit of a point of the unstable set
eventually stays in the chart, close to `p`; a coordinate of positive weight would grow like
`e^{-t}` along it, so all of them vanish and the orbit runs along the coordinates of negative
weight.

The radial flow comes from `TauCeti.MorseBottChart.globalFlow_toChart_symm_coord_symm`, stated for
the flow of any complete `C¹` field that reads `(-wᵢ zᵢ)ᵢ` in a Morse–Bott chart. It adapts
`TauCeti.IsBottAdaptedPseudoGradient.flow_toChart_symm_of_forall_mem_uIcc`
(`Morse/Bott/Flow.lean`), which is stated for the flow of an adapted pseudo-gradient, and has the
same two steps: the linear orbit is an integral curve, and two integral curves that agree at
time `0` agree on `uIcc 0 t` (`IsMIntegralCurveOn.eqOn_of_isPreconnected`). The use of the
coordinates of negative weight follows
`TauCeti.MorseChart.linearFlow_coord_negativeExtend` and
`TauCeti.IsAdaptedPseudoGradient.exists_isSliceChart_unstableSet` (`Morse/Stable/Manifold.lean`),
which treat adapted pseudo-gradients on compact manifolds.

In the chart, `TauCeti.MorseChart.field_toChart_symm` writes the field of the chart at the point
with coordinates `z` as the image of `(-wᵢ zᵢ)ᵢ` under the differential of the inverse chart;
`TauCeti.MorseChart.field_toChart_symm_negativeExtend` specializes it to the point with
coordinates `c` of negative weight, where that vector is `c`.

Some facts need only the chart, not the field.

* `TauCeti.MorseChart.exists_pos_forall_norm_le_negativeExtend_mem_target`: some `ρ > 0` makes
  the ball above lie in the target, by
  `TauCeti.MorseBottChart.exists_pos_forall_norm_lt_mem_target`;
* `TauCeti.MorseChart.apply_toChart_symm_negativeExtend`: `g = g p - ‖c‖² / 2` at the point with
  coordinates `c`, by the normal form `TauCeti.MorseBottChart.eq_quadratic`, the negative weights
  being `-1` (`TauCeti.MorseChart.weight_eq_neg_one_of_weight_neg`);
* `TauCeti.MorseChart.finrank_euclideanSpace_negativeWeight`: the Euclidean space of the
  coordinates of negative weight has the dimension of the Morse index.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Part I, §3.
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Section 2.1.
-/

public section

open Filter Function Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {g : M → ℝ} {p : M} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}

namespace MorseBottChart

variable (φ : MorseBottChart E g p)

/-- **An integral curve inside the chart is a linear orbit.** If `X` reads `(-wᵢ zᵢ)ᵢ` in the
coordinates of the Morse–Bott chart `φ` and the integral curve `γ` of `X` stays in the source for
the times in `[u, T]`, then the coordinates of `γ u` are those of `γ T` moved by the linear flow
for the time `u - T`. -/
theorem coord_toChart_of_isMIntegralCurve
    (hφ : ∀ y ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
      fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i))
    {γ : ℝ → M} (hγ : IsMIntegralCurve γ X) {u T : ℝ} (huT : u ≤ T)
    (hsrc : ∀ s ∈ Icc u T, γ s ∈ φ.toChart.source) :
    φ.coord (φ.toChart (γ u)) = φ.linearFlow (u - T) (φ.coord (φ.toChart (γ T))) := by
  set c : ℝ → Fin (Module.finrank ℝ E) → ℝ := fun s ↦ φ.coord (φ.toChart (γ s))
  have hc (s : ℝ) (hs : s ∈ Icc u T) : HasDerivAt c (fun i ↦ -(φ.weight i * c s i)) s := by
    have h := φ.coordL.hasFDerivAt.comp_hasDerivAt s <|
      Manifold.hasDerivAt_comp_curve (φ.mdifferentiableAt_toChart (hsrc s hs)) (hγ s)
    convert h using 1
    · funext t
      simp only [c, comp_apply, coordL_apply]
    · exact ((φ.coordL_apply _).trans (hφ _ (hsrc s hs))).symm
  funext i
  have h := eq_exp_smul_of_hasDerivAt_smul (v := fun s ↦ c s i) (c := -φ.weight i) (s := T)
    (t := u) fun τ hτ ↦ by
      rw [uIcc_of_ge huT] at hτ
      simpa [neg_mul] using hasDerivAt_pi.1 (hc τ hτ) i
  rw [linearFlow_apply, ← neg_mul]
  exact h

variable [CompleteSpace E] [T2Space M] [IsManifold 𝓘(ℝ, E) 1 M]
  (hX : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent 1 (fun y ↦ (⟨y, X y⟩ : TangentBundle 𝓘(ℝ, E) M)))
  (hXc : IsCompleteVectorField X)

/-- **The flow is linear in the chart along a linear orbit inside it.** If `X` reads `(-wᵢ zᵢ)ᵢ`
in the coordinates of the Morse–Bott chart `φ` and the linear orbit of the coordinates `z` stays in
the chart for all times between `0` and `t`, then the flow of `X` moves the point with coordinates
`z` at time `t` to the point with coordinates `(e^{-wᵢ t} zᵢ)ᵢ`. -/
theorem globalFlow_toChart_symm_coord_symm
    (hφ : ∀ y ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
      fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i))
    {z : Fin (Module.finrank ℝ E) → ℝ} {t : ℝ}
    (hz : ∀ s ∈ uIcc 0 t, φ.coord.symm (φ.linearFlow s z) ∈ φ.toChart.target) :
    globalFlow X hX hXc t (φ.toChart.symm (φ.coord.symm z)) =
      φ.toChart.symm (φ.coord.symm (φ.linearFlow t z)) :=
  ((φ.isMIntegralCurveOn_toChart_symm_linearFlow hφ hz).eqOn_of_isPreconnected
    ((isMIntegralCurve_globalFlow hX hXc _).isMIntegralCurveOn _) isPreconnected_uIcc
    left_mem_uIcc (fun _ _ ↦ hX _)
    (by rw [linearFlow_zero, Flow.map_zero_apply]) right_mem_uIcc).symm

end MorseBottChart

namespace MorseChart

variable (φ : MorseChart E g p)

/-- The continuous linear map `c ↦ φ.negativeExtend c.ofLp` from the Euclidean space of the
coordinates of negative weight of the Morse chart `φ` to the model space: it sends `c` to the
vector with coordinates `c` of negative weight and `0` of positive weight. -/
noncomputable def negativeExtendL : EuclideanSpace ℝ {i // φ.weight i < 0} →L[ℝ] E :=
  LinearMap.toContinuousLinearMap (φ.negativeExtend ∘ₗ (WithLp.linearEquiv 2 ℝ _).toLinearMap)

@[simp]
theorem negativeExtendL_apply (c : EuclideanSpace ℝ {i // φ.weight i < 0}) :
    φ.negativeExtendL c = φ.negativeExtend c.ofLp := (rfl)

/-- The Euclidean space of the coordinates of negative weight of a Morse chart has the dimension of
the Morse index. -/
theorem finrank_euclideanSpace_negativeWeight :
    Module.finrank ℝ (EuclideanSpace ℝ {i // φ.weight i < 0}) =
      manifoldMorseIndex 𝓘(ℝ, E) g p := by
  rw [finrank_euclideanSpace, ← Module.finrank_fintype_fun_eq_card (R := ℝ),
    φ.finrank_negativeWeight_fun]

/-- A field equal to the linear field of a Morse chart on its source reads `(-wᵢ zᵢ)ᵢ` in the
coordinates of the chart. -/
theorem coord_mfderiv_of_forall_eq_field (hXφ : ∀ y ∈ φ.toChart.source, X y = φ.field y)
    {y : M} (hy : y ∈ φ.toChart.source) :
    φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
      fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i) := by
  rw [hXφ y hy, φ.coord_mfderiv_field hy]

/-- **The field of a Morse chart through the inverse chart.** At the point of the chart with
coordinates `z`, the field of the Morse chart is the image of the vector `(-wᵢ zᵢ)ᵢ` under the
differential of the inverse chart. -/
theorem field_toChart_symm {z : E} (hz : z ∈ φ.toChart.target) :
    φ.field (φ.toChart.symm z) = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart.symm z
      (φ.coord.symm fun i ↦ -(φ.weight i * φ.coord z i)) := by
  refine (φ.eq_field_of_coord_mfderiv (φ.toChart.map_target hz) ?_).symm
  rw [φ.toChart.mfderiv_apply_mfderiv_symm_apply_of_mem_maximalAtlas φ.mem_maximalAtlas_one hz
    (φ.coord.symm fun i ↦ -(φ.weight i * φ.coord z i) : E),
    φ.toChart.right_inv hz, LinearEquiv.apply_symm_apply]

/-- A negative weight of a Morse chart is `-1`. -/
theorem weight_eq_neg_one_of_weight_neg {i : Fin (Module.finrank ℝ E)} (hi : φ.weight i < 0) :
    φ.weight i = -1 :=
  (φ.weight_eq_neg_one_or_eq_one i).resolve_right fun h ↦ by rw [h] at hi; norm_num at hi

/-- **The field of a Morse chart on the coordinates of negative weight.** At the point of the
chart with coordinates `c` of negative weight and `0` of positive weight, the field of the Morse
chart is the image of `c` under the differential of the inverse chart: the weights of these
coordinates are `-1`. -/
theorem field_toChart_symm_negativeExtend {c : {i // φ.weight i < 0} → ℝ}
    (hc : φ.negativeExtend c ∈ φ.toChart.target) :
    φ.field (φ.toChart.symm (φ.negativeExtend c)) =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart.symm (φ.negativeExtend c) (φ.negativeExtend c) := by
  rw [φ.field_toChart_symm hc]
  congr 1
  refine φ.coord.symm_apply_eq.2 (funext fun i ↦ ?_)
  by_cases hi : φ.weight i < 0
  · rw [φ.weight_eq_neg_one_of_weight_neg hi]; ring
  · rw [φ.coord_negativeExtend_of_not_weight_neg c hi]; ring

/-- **A radius for the coordinates of negative weight.** There is `ρ > 0` such that the chart's
target contains every vector whose coordinates are `c` of negative weight and `0` of positive
weight, for each `c` of Euclidean norm at most `ρ`. -/
theorem exists_pos_forall_norm_le_negativeExtend_mem_target :
    ∃ ρ > 0, ∀ c : EuclideanSpace ℝ {i // φ.weight i < 0}, ‖c‖ ≤ ρ →
      φ.negativeExtend c.ofLp ∈ φ.toChart.target := by
  obtain ⟨r, hr, hrT⟩ := φ.exists_pos_forall_norm_lt_mem_target
  refine ⟨r / 2, half_pos hr, fun c hc ↦ ?_⟩
  rw [← LinearEquiv.symm_apply_apply φ.coord (φ.negativeExtend c.ofLp)]
  refine hrT _ (lt_of_le_of_lt ?_ (half_lt_self hr))
  refine (pi_norm_le_iff_of_nonneg ((norm_nonneg c).trans hc)).2 fun i ↦ ?_
  by_cases hi : φ.weight i < 0
  · rw [φ.coord_negativeExtend_of_weight_neg _ ⟨i, hi⟩]
    exact (PiLp.norm_apply_le c ⟨i, hi⟩).trans hc
  · rw [φ.coord_negativeExtend_of_not_weight_neg _ hi, norm_zero]
    exact (norm_nonneg c).trans hc

/-- **The level on the coordinates of negative weight.** At the point of the Morse chart with
coordinates `c` of negative weight and `0` of positive weight, `g = g p - ‖c‖² / 2`, `‖c‖` being
the Euclidean norm of `c`. -/
theorem apply_toChart_symm_negativeExtend {c : EuclideanSpace ℝ {i // φ.weight i < 0}}
    (hc : φ.negativeExtend c.ofLp ∈ φ.toChart.target) :
    g (φ.toChart.symm (φ.negativeExtend c.ofLp)) = g p - ‖c‖ ^ 2 / 2 := by
  rw [φ.eq_quadratic _ (φ.toChart.map_target hc), φ.toChart.right_inv hc,
    ← Fintype.sum_subtype_add_sum_subtype (fun i ↦ φ.weight i < 0), EuclideanSpace.norm_sq_eq]
  have h0 : ∑ i : {i // ¬φ.weight i < 0},
      φ.weight i * φ.coord (φ.negativeExtend c.ofLp) i ^ 2 = 0 :=
    Finset.sum_eq_zero fun i _ ↦ by
      rw [φ.coord_negativeExtend_of_not_weight_neg _ i.property]; ring
  have h1 : ∑ i : {i // φ.weight i < 0},
      φ.weight i * φ.coord (φ.negativeExtend c.ofLp) i ^ 2 = -∑ i, ‖c i‖ ^ 2 := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [φ.coord_negativeExtend_of_weight_neg, φ.weight_eq_neg_one_of_weight_neg i.property,
      Real.norm_eq_abs, sq_abs]
    ring
  rw [h0, h1]
  ring

variable [CompleteSpace E] [T2Space M] [IsManifold 𝓘(ℝ, E) 1 M]
  (hX : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent 1 (fun y ↦ (⟨y, X y⟩ : TangentBundle 𝓘(ℝ, E) M)))
  (hXc : IsCompleteVectorField X)

/-- The centre of a Morse chart on whose source `X` is the linear field is a rest point of the
flow of `X`. -/
theorem globalFlow_self (hXφ : ∀ y ∈ φ.toChart.source, X y = φ.field y) (t : ℝ) :
    globalFlow X hX hXc t p = p := by
  have h := φ.globalFlow_toChart_symm_coord_symm hX hXc
    (fun _ hy ↦ φ.coord_mfderiv_of_forall_eq_field hXφ hy) (z := 0) (t := t) fun s _ ↦ by
    rw [MorseBottChart.linearFlow_zero_right, map_zero, ← φ.apply_self]
    exact φ.toChart.map_source φ.mem_source
  rwa [MorseBottChart.linearFlow_zero_right, φ.toChart_symm_coord_symm_zero] at h

/-- The flow of `X` fixes the point of the Morse chart with coordinates `0` of negative weight,
which is the centre `p`, when `X` is the linear field of the chart on its source. -/
theorem globalFlow_toChart_symm_negativeExtend_zero
    (hXφ : ∀ y ∈ φ.toChart.source, X y = φ.field y) (t : ℝ) :
    globalFlow X hX hXc t
      (φ.toChart.symm (φ.negativeExtend (0 : EuclideanSpace ℝ {i // φ.weight i < 0}).ofLp)) =
        p := by
  rw [WithLp.ofLp_zero, map_zero, φ.toChart_symm_zero, φ.globalFlow_self hX hXc hXφ]

/-- **Radial flow along the coordinates of negative weight.** If `X` is the linear field of the
Morse chart `φ` on its source, `t ≤ 0`, and the points with coordinates `e^{s} c` of negative
weight and `0` of positive weight lie in the chart for `t ≤ s ≤ 0`, then the flow of `X` at time
`t` moves the point with coordinates `c` to the point with coordinates `e^{t} c`. -/
theorem globalFlow_toChart_symm_negativeExtend (hXφ : ∀ y ∈ φ.toChart.source, X y = φ.field y)
    {c : {i // φ.weight i < 0} → ℝ} {t : ℝ} (ht : t ≤ 0)
    (hc : ∀ s ∈ Icc t 0, φ.negativeExtend (Real.exp s • c) ∈ φ.toChart.target) :
    globalFlow X hX hXc t (φ.toChart.symm (φ.negativeExtend c)) =
      φ.toChart.symm (φ.negativeExtend (Real.exp t • c)) := by
  have hlin (s : ℝ) : φ.coord.symm (φ.linearFlow s (φ.coord (φ.negativeExtend c))) =
      φ.negativeExtend (Real.exp s • c) := by
    rw [φ.linearFlow_coord_negativeExtend, ← map_smul, LinearEquiv.symm_apply_apply, map_smul]
  have h := φ.globalFlow_toChart_symm_coord_symm hX hXc
    (fun _ hy ↦ φ.coord_mfderiv_of_forall_eq_field hXφ hy)
    (z := φ.coord (φ.negativeExtend c)) (t := t) fun s hs ↦ by
      rw [hlin]
      exact hc s (by rwa [uIcc_of_ge ht] at hs)
  rwa [hlin, LinearEquiv.symm_apply_apply] at h

variable {ρ : ℝ}

/-- **Radial flow on a ball of negative coordinates.** Let `X` be the linear field of the Morse
chart `φ` on its source, and let the closed Euclidean ball of radius `ρ` in the coordinates of
negative weight lie in the chart. For `‖c‖ ≤ ρ` and `t ≤ 0`, the flow of `X` at time `t` moves the
point with coordinates `c` of negative weight (and `0` of positive weight) to the point with
coordinates `e^{t} c`. -/
theorem globalFlow_toChart_symm_negativeExtend_of_norm_le
    (hXφ : ∀ y ∈ φ.toChart.source, X y = φ.field y)
    (hρ : ∀ c : EuclideanSpace ℝ {i // φ.weight i < 0}, ‖c‖ ≤ ρ →
      φ.negativeExtend c.ofLp ∈ φ.toChart.target)
    {c : EuclideanSpace ℝ {i // φ.weight i < 0}} (hc : ‖c‖ ≤ ρ) {t : ℝ} (ht : t ≤ 0) :
    globalFlow X hX hXc t (φ.toChart.symm (φ.negativeExtend c.ofLp)) =
      φ.toChart.symm (φ.negativeExtend (Real.exp t • c).ofLp) := by
  rw [WithLp.ofLp_smul]
  refine φ.globalFlow_toChart_symm_negativeExtend hX hXc hXφ ht fun s hs ↦ ?_
  rw [← WithLp.ofLp_smul]
  refine hρ _ ((norm_smul_le _ _).trans ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos s)]
  exact (mul_le_of_le_one_left (norm_nonneg c) (Real.exp_le_one_iff.2 hs.2)).trans hc

/-- **A ball of negative coordinates lies in the unstable set.** Let `X` be the linear field of the
Morse chart `φ` at `p` on its source, and let the closed Euclidean ball of radius `ρ` in the
coordinates of negative weight lie in the chart. Then the chart sends this ball, with the
coordinates of positive weight set to `0`, into the unstable set of `p` for the flow of `X`. -/
theorem mapsTo_closedBall_unstableSet (hXφ : ∀ y ∈ φ.toChart.source, X y = φ.field y)
    (hρ : ∀ c : EuclideanSpace ℝ {i // φ.weight i < 0}, ‖c‖ ≤ ρ →
      φ.negativeExtend c.ofLp ∈ φ.toChart.target) :
    MapsTo (fun c : EuclideanSpace ℝ {i // φ.weight i < 0} ↦
        φ.toChart.symm (φ.negativeExtend c.ofLp))
      (Metric.closedBall 0 ρ) (Flow.unstableSet (globalFlow X hX hXc) p) := by
  intro c hc
  rw [mem_closedBall_zero_iff] at hc
  rw [Flow.mem_unstableSet]
  have hev : (fun t ↦ φ.toChart.symm (φ.negativeExtend (Real.exp t • c).ofLp)) =ᶠ[atBot]
      fun t ↦ globalFlow X hX hXc t (φ.toChart.symm (φ.negativeExtend c.ofLp)) :=
    (eventually_le_atBot 0).mono fun t ht ↦
      (φ.globalFlow_toChart_symm_negativeExtend_of_norm_le hX hXc hXφ hρ hc ht).symm
  refine Tendsto.congr' hev ?_
  have h := φ.tendsto_toChart_symm_coord_symm_nhds_zero.comp
    (by simpa using Real.tendsto_exp_atBot.smul_const (φ.coord (φ.negativeExtend c.ofLp)))
  simpa [comp_def, WithLp.ofLp_smul] using h

/-- **The backward orbit of a point of the unstable set runs along the coordinates of negative
weight.** If `X` is the linear field of the Morse chart `φ` at `p` on its source and `x` lies in
the unstable set of `p` for the flow `Φ` of `X`, there are a time `T ≤ 0` and coordinates `a` of
negative weight such that for every `u ≤ T` the point with coordinates `e^{u - T} a` of negative
weight and `0` of positive weight lies in the chart and is `Φ u x`. -/
theorem exists_globalFlow_eq_toChart_symm_negativeExtend_of_mem_unstableSet
    (hXφ : ∀ y ∈ φ.toChart.source, X y = φ.field y) {x : M}
    (hx : x ∈ Flow.unstableSet (globalFlow X hX hXc) p) :
    ∃ T ≤ 0, ∃ a : {i // φ.weight i < 0} → ℝ, ∀ u ≤ T,
      φ.negativeExtend (Real.exp (u - T) • a) ∈ φ.toChart.target ∧
        globalFlow X hX hXc u x = φ.toChart.symm (φ.negativeExtend (Real.exp (u - T) • a)) := by
  set Φ := globalFlow X hX hXc
  rw [Flow.mem_unstableSet] at hx
  have hcont : ContinuousAt (fun y ↦ φ.coord (φ.toChart y)) p :=
    by simpa only [comp_def, MorseBottChart.coordL_apply] using
      φ.coordL.continuous.continuousAt.comp (φ.toChart.continuousAt φ.mem_source)
  have h0 : φ.coord (φ.toChart p) = 0 := by rw [φ.apply_self, map_zero]
  have hev : ∀ᶠ t in atBot, Φ t x ∈ φ.toChart.source ∧ ‖φ.coord (φ.toChart (Φ t x))‖ < 1 := by
    refine (hx.eventually (φ.toChart.open_source.mem_nhds φ.mem_source)).and ?_
    have hball : (fun y ↦ φ.coord (φ.toChart y)) ⁻¹' Metric.ball 0 1 ∈ 𝓝 p :=
      hcont.preimage_mem_nhds (by rw [h0]; exact Metric.ball_mem_nhds 0 one_pos)
    exact (hx.eventually hball).mono fun t ht ↦ by simpa using ht
  obtain ⟨T₀, hT₀⟩ := eventually_atBot.1 hev
  set T := min T₀ 0
  have hT (u : ℝ) (hu : u ≤ T) :
      Φ u x ∈ φ.toChart.source ∧ ‖φ.coord (φ.toChart (Φ u x))‖ < 1 :=
    hT₀ u (hu.trans (min_le_left _ _))
  have hlin (u : ℝ) (hu : u ≤ T) : φ.coord (φ.toChart (Φ u x)) =
      φ.linearFlow (u - T) (φ.coord (φ.toChart (Φ T x))) :=
    φ.coord_toChart_of_isMIntegralCurve (fun _ hy ↦ φ.coord_mfderiv_of_forall_eq_field hXφ hy)
      (isMIntegralCurve_globalFlow hX hXc x) hu fun s hs ↦ (hT s hs.2).1
  set v := φ.toChart (Φ T x)
  -- The coordinates of positive weight of `v` vanish: along the backward orbit they grow like
  -- `e^{T - u}`, while the orbit stays in the unit ball of the coordinates.
  have hpos (i : Fin (Module.finrank ℝ E)) (hi : ¬φ.weight i < 0) : φ.coord v i = 0 := by
    have hw : φ.weight i = 1 := (φ.weight_eq_neg_one_or_eq_one i).resolve_left fun h ↦
      hi (by rw [h]; norm_num)
    have hle (u : ℝ) (hu : u ≤ T) : |φ.coord v i| ≤ Real.exp (u - T) := by
      have h1 := (norm_le_pi_norm (φ.coord (φ.toChart (Φ u x))) i).trans_lt (hT u hu).2
      rw [hlin u hu, MorseBottChart.linearFlow_apply, hw, one_mul, Real.norm_eq_abs, abs_mul,
        abs_of_pos (Real.exp_pos _), Real.exp_neg, inv_mul_lt_iff₀ (Real.exp_pos _),
        mul_one] at h1
      exact h1.le
    have htend : Tendsto (fun u ↦ Real.exp (u - T)) atBot (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_atBot_add_const_right _ _ tendsto_id)
    exact abs_nonpos_iff.1 (ge_of_tendsto htend ((eventually_le_atBot T).mono hle))
  have hv : φ.negativeExtend (φ.negativeCoord v) = v := φ.negativeExtend_negativeCoord hpos
  refine ⟨T, min_le_right _ _, φ.negativeCoord v, fun u hu ↦ ?_⟩
  have key : φ.toChart (Φ u x) = φ.negativeExtend (Real.exp (u - T) • φ.negativeCoord v) := by
    refine φ.coord.injective ?_
    rw [hlin u hu, map_smul, map_smul, ← φ.linearFlow_coord_negativeExtend, hv]
  exact ⟨key ▸ φ.toChart.map_source (hT u hu).1, by rw [← key, φ.toChart.left_inv (hT u hu).1]⟩

/-- **The flow along a ray of negative coordinates.** Let `X` be the linear field of the Morse
chart `φ` on its source, and let the closed Euclidean ball of radius `ρ` in the coordinates of
negative weight lie in the chart. For `‖u‖ ≤ ρ` and `0 < r ≤ 1`, running the flow of `X` for the
time `s` from the point with coordinates `r • u` is running it for the time `s + log r` from the
point with coordinates `u`. -/
theorem globalFlow_toChart_symm_negativeExtend_smul
    (hXφ : ∀ y ∈ φ.toChart.source, X y = φ.field y)
    (hρ : ∀ c : EuclideanSpace ℝ {i // φ.weight i < 0}, ‖c‖ ≤ ρ →
      φ.negativeExtend c.ofLp ∈ φ.toChart.target)
    {u : EuclideanSpace ℝ {i // φ.weight i < 0}} (hu : ‖u‖ ≤ ρ) {r : ℝ} (hr0 : 0 < r)
    (hr1 : r ≤ 1) (s : ℝ) :
    globalFlow X hX hXc s (φ.toChart.symm (φ.negativeExtend (r • u).ofLp)) =
      globalFlow X hX hXc (s + Real.log r) (φ.toChart.symm (φ.negativeExtend u.ofLp)) := by
  rw [Flow.map_add, φ.globalFlow_toChart_symm_negativeExtend_of_norm_le hX hXc hXφ hρ hu
    (Real.log_nonpos hr0.le hr1), Real.exp_log hr0]

/-- **The unstable set is swept out from a sphere of negative coordinates.** Let `X` be the linear
field of the Morse chart `φ` at `p` on its source, `Φ` its flow, and let the closed Euclidean ball
of radius `ρ > 0` in the coordinates of negative weight lie in the chart. Every point `x ≠ p` of
the unstable set of `p` is `Φ s y` for a point `y` of the chart with coordinates `c` of negative
weight, `‖c‖ = ρ`, and `0` of positive weight; and `s ≥ 0` unless `x` lies in the image of the
ball. -/
theorem exists_globalFlow_eq_of_mem_unstableSet (hXφ : ∀ y ∈ φ.toChart.source, X y = φ.field y)
    (hρ0 : 0 < ρ)
    (hρ : ∀ c : EuclideanSpace ℝ {i // φ.weight i < 0}, ‖c‖ ≤ ρ →
      φ.negativeExtend c.ofLp ∈ φ.toChart.target)
    {x : M} (hx : x ∈ Flow.unstableSet (globalFlow X hX hXc) p) (hxp : x ≠ p) :
    ∃ s : ℝ, ∃ c : EuclideanSpace ℝ {i // φ.weight i < 0}, ‖c‖ = ρ ∧
      globalFlow X hX hXc s (φ.toChart.symm (φ.negativeExtend c.ofLp)) = x ∧
      (0 ≤ s ∨ x ∈ (fun c : EuclideanSpace ℝ {i // φ.weight i < 0} ↦
        φ.toChart.symm (φ.negativeExtend c.ofLp)) '' Metric.closedBall 0 ρ) := by
  set Φ := globalFlow X hX hXc
  obtain ⟨T, -, a, ha⟩ :=
    φ.exists_globalFlow_eq_toChart_symm_negativeExtend_of_mem_unstableSet hX hXc hXφ hx
  have hx' : x = Φ (-T) (Φ T x) := (Φ.map_neg_apply_map T x).symm
  have haT : Φ T x = φ.toChart.symm (φ.negativeExtend a) := by
    have h := (ha T le_rfl).2
    rwa [sub_self, Real.exp_zero, one_smul] at h
  set A : EuclideanSpace ℝ {i // φ.weight i < 0} := WithLp.toLp 2 a
  have hA : A ≠ 0 := by
    rintro hA0
    have ha0 : a = 0 := by simpa [A] using hA0
    rw [haT, ha0, map_zero, φ.toChart_symm_zero, φ.globalFlow_self hX hXc hXφ] at hx'
    exact hxp hx'
  set n := ‖A‖
  have hn : 0 < n := norm_pos_iff.2 hA
  set c := (ρ / n) • A
  obtain ⟨hc, hcA⟩ : ‖c‖ = ρ ∧ (n / ρ) • c = A := by
    simp [c, n, norm_smul, abs_of_pos hρ0, hA, smul_smul, hρ0.ne']
  -- The orbit of `x` meets the sphere of radius `ρ`, at the time `T - log (n / ρ)`.
  have hmeet : Φ T x = Φ (Real.log (n / ρ)) (φ.toChart.symm (φ.negativeExtend c.ofLp)) := by
    rcases le_or_gt n ρ with hnρ | hnρ
    · rw [← zero_add (Real.log _), ← φ.globalFlow_toChart_symm_negativeExtend_smul hX hXc hXφ hρ
        hc.le (div_pos hn hρ0) ((div_le_one hρ0).2 hnρ), Flow.map_zero_apply, hcA, haT]
    · have hu : T + Real.log (ρ / n) ≤ T := by
        linarith [Real.log_nonpos (div_pos hρ0 hn).le ((div_le_one hn).2 hnρ.le)]
      have h := (ha _ hu).2
      rw [add_sub_cancel_left, Real.exp_log (div_pos hρ0 hn)] at h
      have hT : T = Real.log (n / ρ) + (T + Real.log (ρ / n)) := by
        rw [← inv_div, Real.log_inv]
        ring
      rw [hT, Flow.map_add, h]
      simp only [c, A, WithLp.ofLp_smul]
  refine ⟨-T + Real.log (n / ρ), c, hc, ?_, ?_⟩
  · rw [Flow.map_add, ← hmeet, ← hx']
  rcases le_or_gt 0 (-T + Real.log (n / ρ)) with hs | hs
  · exact .inl hs
  refine .inr ⟨Real.exp (-T + Real.log (n / ρ)) • c, ?_, ?_⟩
  · rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), hc]
    exact mul_le_of_le_one_left hρ0.le (Real.exp_le_one_iff.2 hs.le)
  · dsimp only
    rw [← φ.globalFlow_toChart_symm_negativeExtend_of_norm_le hX hXc hXφ hρ hc.le hs.le,
      Flow.map_add, ← hmeet, ← hx']

/-- One case of `TauCeti.MorseChart.eq_of_globalFlow_eq_globalFlow`, for `s' ≤ s`. -/
private theorem eq_of_globalFlow_eq_globalFlow_of_le
    (hXφ : ∀ y ∈ φ.toChart.source, X y = φ.field y) (hρ0 : 0 < ρ)
    (hρ : ∀ c : EuclideanSpace ℝ {i // φ.weight i < 0}, ‖c‖ ≤ ρ →
      φ.negativeExtend c.ofLp ∈ φ.toChart.target)
    {s s' : ℝ} {c c' : EuclideanSpace ℝ {i // φ.weight i < 0}} (hc : ‖c‖ = ρ) (hc' : ‖c'‖ = ρ)
    (hss' : s' ≤ s)
    (h : globalFlow X hX hXc s (φ.toChart.symm (φ.negativeExtend c.ofLp)) =
      globalFlow X hX hXc s' (φ.toChart.symm (φ.negativeExtend c'.ofLp))) :
    s = s' ∧ c = c' := by
  set Φ := globalFlow X hX hXc
  have hle : s' - s ≤ 0 := by linarith
  have h1 : φ.toChart.symm (φ.negativeExtend c.ofLp) =
      φ.toChart.symm (φ.negativeExtend (Real.exp (s' - s) • c').ofLp) := by
    rw [← φ.globalFlow_toChart_symm_negativeExtend_of_norm_le hX hXc hXφ hρ hc'.le hle,
      sub_eq_neg_add, Flow.map_add, ← h, Flow.map_neg_apply_map]
  have hn : ‖Real.exp (s' - s) • c'‖ ≤ ρ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), hc']
    exact mul_le_of_le_one_left hρ0.le (Real.exp_le_one_iff.2 hle)
  have h2 : c = Real.exp (s' - s) • c' :=
    WithLp.ofLp_injective 2 <| φ.injective_negativeExtend <| by
      have h1' := congrArg φ.toChart h1
      rwa [φ.toChart.right_inv (hρ _ hc.le), φ.toChart.right_inv (hρ _ hn)] at h1'
  have h3 : Real.exp (s' - s) = 1 := by
    have h4 := congrArg norm h2
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), hc, hc'] at h4
    nlinarith
  have h5 : s = s' := by
    have := Real.exp_eq_one_iff _ |>.1 h3
    linarith
  exact ⟨h5, by rw [h2, h3, one_smul]⟩

/-- **A flow line meets the sphere of negative coordinates at most once.** Let `X` be the linear
field of the Morse chart `φ` on its source, `Φ` its flow, and let the closed Euclidean ball of
radius `ρ > 0` in the coordinates of negative weight lie in the chart. If two points `y`, `y'` of
the chart with coordinates `c`, `c'` of negative weight, `‖c‖ = ‖c'‖ = ρ`, and `0` of positive
weight satisfy `Φ s y = Φ s' y'`, then `s = s'` and `c = c'`. -/
theorem eq_of_globalFlow_eq_globalFlow (hXφ : ∀ y ∈ φ.toChart.source, X y = φ.field y)
    (hρ0 : 0 < ρ)
    (hρ : ∀ c : EuclideanSpace ℝ {i // φ.weight i < 0}, ‖c‖ ≤ ρ →
      φ.negativeExtend c.ofLp ∈ φ.toChart.target)
    {s s' : ℝ} {c c' : EuclideanSpace ℝ {i // φ.weight i < 0}} (hc : ‖c‖ = ρ) (hc' : ‖c'‖ = ρ)
    (h : globalFlow X hX hXc s (φ.toChart.symm (φ.negativeExtend c.ofLp)) =
      globalFlow X hX hXc s' (φ.toChart.symm (φ.negativeExtend c'.ofLp))) :
    s = s' ∧ c = c' := by
  rcases le_total s' s with hss' | hss'
  · exact φ.eq_of_globalFlow_eq_globalFlow_of_le hX hXc hXφ hρ0 hρ hc hc' hss' h
  · obtain ⟨h1, h2⟩ := φ.eq_of_globalFlow_eq_globalFlow_of_le hX hXc hXφ hρ0 hρ hc' hc hss' h.symm
    exact ⟨h1.symm, h2.symm⟩

/-- **The time-`θ` flow-out of a ball of negative coordinates is injective.** Let `X` be the linear
field of the Morse chart `φ` at `p` on its source, `Φ` its flow, and let the closed Euclidean ball
of radius `ρ` in the coordinates of negative weight lie in the chart. Let `θ` be a function on
these coordinates such that `r ↦ θ (r • u) + log r` is strictly monotone on `(0, 1]` for each `u`
with `‖u‖ = ρ`. Then `c ↦ Φ (θ c) y_c`, where `y_c` is the point with coordinates `c` of negative
weight and `0` of positive weight, is injective on the closed ball of radius `ρ`. -/
theorem injOn_globalFlow_toChart_symm_negativeExtend
    (hXφ : ∀ y ∈ φ.toChart.source, X y = φ.field y)
    (hρ : ∀ c : EuclideanSpace ℝ {i // φ.weight i < 0}, ‖c‖ ≤ ρ →
      φ.negativeExtend c.ofLp ∈ φ.toChart.target)
    {θ : EuclideanSpace ℝ {i // φ.weight i < 0} → ℝ}
    (hθ : ∀ u : EuclideanSpace ℝ {i // φ.weight i < 0}, ‖u‖ = ρ →
      StrictMonoOn (fun r ↦ θ (r • u) + Real.log r) (Ioc 0 1)) :
    InjOn (fun c ↦ globalFlow X hX hXc (θ c) (φ.toChart.symm (φ.negativeExtend c.ofLp)))
      (Metric.closedBall 0 ρ) := by
  set Φ := globalFlow X hX hXc
  -- A nonzero point `c` of the ball is `(‖c‖ / ρ) • u` for the point `u = (ρ / ‖c‖) • c` of the
  -- sphere of radius `ρ`.
  have hsphere {c : EuclideanSpace ℝ {i // φ.weight i < 0}} (hc0 : c ≠ 0) (hc : ‖c‖ ≤ ρ) :
      ‖(ρ / ‖c‖) • c‖ = ρ ∧ (‖c‖ / ρ) • (ρ / ‖c‖) • c = c ∧ 0 < ‖c‖ / ρ ∧ ‖c‖ / ρ ≤ 1 := by
    have hn : 0 < ‖c‖ := norm_pos_iff.2 hc0
    have hρ0 : 0 < ρ := hn.trans_le hc
    refine ⟨?_, ?_, div_pos hn hρ0, (div_le_one hρ0).2 hc⟩ <;>
      simp [norm_smul, abs_of_pos hρ0, hc0, smul_smul, hρ0.ne']
  -- The image of a nonzero point `c` of the ball, through the point of the sphere on its ray.
  have hray {c : EuclideanSpace ℝ {i // φ.weight i < 0}} (hc0 : c ≠ 0) (hc : ‖c‖ ≤ ρ) :
      Φ (θ c) (φ.toChart.symm (φ.negativeExtend c.ofLp)) =
        Φ (θ c + Real.log (‖c‖ / ρ)) (φ.toChart.symm (φ.negativeExtend ((ρ / ‖c‖) • c).ofLp)) := by
    obtain ⟨hu, hcu, hr0, hr1⟩ := hsphere hc0 hc
    have h := φ.globalFlow_toChart_symm_negativeExtend_smul hX hXc hXφ hρ hu.le hr0 hr1 (θ c)
    rwa [hcu] at h
  -- No nonzero point of the ball goes to `p`.
  have hne {c : EuclideanSpace ℝ {i // φ.weight i < 0}} (hc0 : c ≠ 0) (hc : ‖c‖ ≤ ρ) :
      Φ (θ c) (φ.toChart.symm (φ.negativeExtend c.ofLp)) ≠ p := by
    intro h
    have h' := congrArg (Φ (-θ c)) h
    rw [Flow.map_neg_apply_map, φ.globalFlow_self hX hXc hXφ] at h'
    exact φ.toChart_symm_negativeExtend_ne (by simpa using hc0) (hρ c hc) h'
  have hzero := φ.globalFlow_toChart_symm_negativeExtend_zero hX hXc hXφ (θ 0)
  intro c hc c' hc' h
  rw [mem_closedBall_zero_iff] at hc hc'
  dsimp only at h
  rcases eq_or_ne c 0 with rfl | hc0
  · by_contra hc0'
    exact hne (Ne.symm hc0') hc' (h.symm.trans hzero)
  rcases eq_or_ne c' 0 with rfl | hc0'
  · exact absurd (h.trans hzero) (hne hc0 hc)
  obtain ⟨hu, hcu, hr0, hr1⟩ := hsphere hc0 hc
  obtain ⟨hu', hcu', hr0', hr1'⟩ := hsphere hc0' hc'
  rw [hray hc0 hc, hray hc0' hc'] at h
  have hρ0 : 0 < ρ := (norm_pos_iff.2 hc0).trans_le hc
  obtain ⟨hs, huu⟩ := φ.eq_of_globalFlow_eq_globalFlow hX hXc hXφ hρ0 hρ hu hu' h
  have hs' : θ ((‖c‖ / ρ) • (ρ / ‖c‖) • c) + Real.log (‖c‖ / ρ) =
      θ ((‖c'‖ / ρ) • (ρ / ‖c‖) • c) + Real.log (‖c'‖ / ρ) := by
    rw [hcu, huu, hcu']
    exact hs
  have hr := (hθ _ hu).injOn ⟨hr0, hr1⟩ ⟨hr0', hr1'⟩ hs'
  calc c = (‖c‖ / ρ) • (ρ / ‖c‖) • c := hcu.symm
    _ = (‖c'‖ / ρ) • (ρ / ‖c'‖) • c' := by rw [hr, huu]
    _ = c' := hcu'

/-- **The time-`θ` flow-out of a ball of negative coordinates lies in the unstable set.** Let `X`
be the linear field of the Morse chart `φ` at `p` on its source, `Φ` its flow, and let the closed
Euclidean ball of radius `ρ` in the coordinates of negative weight lie in the chart. For any
function `θ` on these coordinates, `c ↦ Φ (θ c) y_c`, where `y_c` is the point with coordinates `c`
of negative weight and `0` of positive weight, maps this ball into the unstable set of `p`. -/
theorem mapsTo_globalFlow_closedBall_unstableSet (hXφ : ∀ y ∈ φ.toChart.source, X y = φ.field y)
    (hρ : ∀ c : EuclideanSpace ℝ {i // φ.weight i < 0}, ‖c‖ ≤ ρ →
      φ.negativeExtend c.ofLp ∈ φ.toChart.target)
    (θ : EuclideanSpace ℝ {i // φ.weight i < 0} → ℝ) :
    MapsTo (fun c ↦ globalFlow X hX hXc (θ c) (φ.toChart.symm (φ.negativeExtend c.ofLp)))
      (Metric.closedBall 0 ρ) (Flow.unstableSet (globalFlow X hX hXc) p) := fun _ hc ↦
  (Flow.apply_mem_unstableSet_iff _ _).2 (φ.mapsTo_closedBall_unstableSet hX hXc hXφ hρ hc)

/-- **The time-`θ` flow-out of a ball of negative coordinates sweeps the unstable set.** Let `X` be
the linear field of the Morse chart `φ` at `p` on its source, `Φ` its flow, and let the closed
Euclidean ball of radius `ρ` in the coordinates of negative weight lie in the chart. Let `θ` be a
function on these coordinates, continuous on the closed ball of radius `ρ`, and write `y_c` for
the point with coordinates `c` of negative weight and `0` of positive weight. If `‖u‖ ≤ ρ` and
`s ≤ θ u`, then `Φ s y_u` is `Φ (θ c) y_c` for some `c` in the closed ball of radius `ρ`. -/
theorem globalFlow_mem_image_closedBall (hXφ : ∀ y ∈ φ.toChart.source, X y = φ.field y)
    (hρ : ∀ c : EuclideanSpace ℝ {i // φ.weight i < 0}, ‖c‖ ≤ ρ →
      φ.negativeExtend c.ofLp ∈ φ.toChart.target)
    {θ : EuclideanSpace ℝ {i // φ.weight i < 0} → ℝ}
    (hθ : ContinuousOn θ (Metric.closedBall 0 ρ))
    {u : EuclideanSpace ℝ {i // φ.weight i < 0}} (hu : ‖u‖ ≤ ρ) {s : ℝ} (hs : s ≤ θ u) :
    globalFlow X hX hXc s (φ.toChart.symm (φ.negativeExtend u.ofLp)) ∈
      (fun c ↦ globalFlow X hX hXc (θ c) (φ.toChart.symm (φ.negativeExtend c.ofLp))) ''
        Metric.closedBall 0 ρ := by
  -- For `r ∈ [0, 1]`, the point `r • u` stays in the closed ball.
  have hmem {r : ℝ} (hr : r ∈ Icc 0 1) : r • u ∈ Metric.closedBall 0 ρ :=
    (convex_closedBall 0 ρ).smul_mem_of_zero_mem
      (Metric.mem_closedBall_self ((norm_nonneg u).trans hu)) (mem_closedBall_zero_iff.2 hu) hr
  obtain ⟨r, hr, hrs⟩ := Real.exists_mem_Ioc_add_log_eq (f := fun r ↦ θ (r • u))
    (hθ.comp (continuous_id.smul continuous_const).continuousOn fun _ ↦ hmem) (by simpa using hs)
  refine ⟨r • u, ?_, ?_⟩
  · exact hmem (Ioc_subset_Icc_self hr)
  · dsimp only
    rw [φ.globalFlow_toChart_symm_negativeExtend_smul hX hXc hXφ hρ hu hr.1 hr.2, hrs]

/-- **The time-`θ` flow-out of an open ball of negative coordinates.** Let `X` be the linear field
of the Morse chart `φ` at `p` on its source, `Φ` its flow, and let the closed Euclidean ball of
radius `ρ` in the coordinates of negative weight lie in the chart. Let `θ` be a function on these
coordinates, continuous on the closed ball of radius `ρ`, and write `y_c` for the point with
coordinates `c` of negative weight and `0` of positive weight. If `‖u‖ ≤ ρ` and `s < θ u`, then
`Φ s y_u` is `Φ (θ c) y_c` for some `c` in the open ball of radius `ρ`. -/
theorem globalFlow_mem_image_ball (hXφ : ∀ y ∈ φ.toChart.source, X y = φ.field y) (hρ0 : 0 < ρ)
    (hρ : ∀ c : EuclideanSpace ℝ {i // φ.weight i < 0}, ‖c‖ ≤ ρ →
      φ.negativeExtend c.ofLp ∈ φ.toChart.target)
    {θ : EuclideanSpace ℝ {i // φ.weight i < 0} → ℝ}
    (hθ : ContinuousOn θ (Metric.closedBall 0 ρ))
    {u : EuclideanSpace ℝ {i // φ.weight i < 0}} (hu : ‖u‖ ≤ ρ) {s : ℝ} (hs : s < θ u) :
    globalFlow X hX hXc s (φ.toChart.symm (φ.negativeExtend u.ofLp)) ∈
      (fun c ↦ globalFlow X hX hXc (θ c) (φ.toChart.symm (φ.negativeExtend c.ofLp))) ''
        Metric.ball 0 ρ := by
  -- For `r ∈ [0, 1]`, the point `r • u` stays in the closed ball.
  have hmem {r : ℝ} (hr : r ∈ Icc 0 1) : r • u ∈ Metric.closedBall 0 ρ :=
    (convex_closedBall 0 ρ).smul_mem_of_zero_mem
      (Metric.mem_closedBall_self ((norm_nonneg u).trans hu)) (mem_closedBall_zero_iff.2 hu) hr
  obtain ⟨r, hr, hrs⟩ := Real.exists_mem_Ioc_add_log_eq (f := fun r ↦ θ (r • u))
    (hθ.comp (continuous_id.smul continuous_const).continuousOn fun _ ↦ hmem)
    (by simpa using hs.le)
  have hr1 : r < 1 := hr.2.lt_of_ne fun h ↦ hs.ne <| by simpa [h] using hrs.symm
  refine ⟨r • u, ?_, ?_⟩
  · rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg hr.1.le]
    exact (mul_le_mul_of_nonneg_left hu hr.1.le).trans_lt (mul_lt_of_lt_one_left hρ0 hr1)
  · dsimp only
    rw [φ.globalFlow_toChart_symm_negativeExtend_smul hX hXc hXφ hρ hu hr.1 hr.2, hrs]

end MorseChart

end TauCeti
