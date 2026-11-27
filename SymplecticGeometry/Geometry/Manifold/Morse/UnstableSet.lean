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
import TauCeti.Geometry.Manifold.IntegralCurve.Maximal
import TauCeti.Geometry.Manifold.MFDeriv.Curve
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# The unstable set near a critical point where the field is linear

Let `X` be a complete `C¹` vector field on a boundaryless manifold `M` modelled on `E`, with flow
`Φ = TauCeti.globalFlow X`, and let `φ` be a Morse chart at `p` on whose source `X` is the linear
field `TauCeti.MorseChart.field` of the chart, `z ↦ (-wᵢ zᵢ)ᵢ` in its coordinates. Nothing is
assumed of `X` away from the chart, and `M` need not be compact. To ask this only on an open
neighbourhood `V` of `p`, apply the results to the restricted chart `φ.restr`.

Let `B` be the image under the chart of a closed Euclidean ball of radius `ρ > 0` in the
coordinates of negative weight (the other coordinates being `0`), and assume that this ball lies in
the target of the chart. We show:

* `TauCeti.MorseChart.globalFlow_toChart_symm_negativeExtend_of_norm_le`: in backward time the
  flow moves the points of `B` radially: for `t ≤ 0`, `Φ t` sends the point with coordinates `c`
  to the point with coordinates `e^{t} c`;
* `TauCeti.MorseChart.mapsTo_closedBall_unstableSet`: `B` lies in the unstable set of `p`;
* `TauCeti.MorseChart.exists_globalFlow_eq_of_mem_unstableSet`: every point `x ≠ p` of the
  unstable set of `p` is `Φ s y` for a point `y` of the boundary sphere of `B`, with `s ≥ 0` unless
  `x ∈ B`, and `TauCeti.MorseChart.eq_of_globalFlow_eq_globalFlow`: the flow line of `x` meets that
  sphere only once.

The last step rests on `TauCeti.MorseChart.coord_toChart_globalFlow_of_forall_mem_source`: while an
orbit stays in the source of the chart, it is read in the coordinates as the linear flow
`TauCeti.MorseBottChart.linearFlow`. The backward orbit of a point of the unstable set eventually
stays in the chart, close to `p`; a coordinate of positive weight would grow like `e^{-t}` along it,
so all of them vanish and the orbit runs along the coordinates of negative weight.

The radial flow comes from `TauCeti.MorseChart.globalFlow_toChart_symm_coord_symm`, which adapts
`TauCeti.IsBottAdaptedPseudoGradient.flow_toChart_symm_of_forall_mem_uIcc`
(`Morse/Bott/Flow.lean`) from the flow of an adapted pseudo-gradient to the flow of any complete
field equal to the linear field on the chart. The use of the coordinates of negative weight follows
`TauCeti.MorseChart.linearFlow_coord_negativeExtend` and
`TauCeti.IsAdaptedPseudoGradient.exists_isSliceChart_unstableSet` (`Morse/Stable/Manifold.lean`),
which treat adapted pseudo-gradients on compact manifolds.

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

namespace MorseChart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {g : M → ℝ} {p : M} (φ : MorseChart E g p)
  {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}

/-- A field equal to the linear field of a Morse chart on its source reads `(-wᵢ zᵢ)ᵢ` in the
coordinates of the chart. -/
theorem coord_mfderiv_of_forall_eq_field (hXφ : ∀ y ∈ φ.toChart.source, X y = φ.field y)
    {y : M} (hy : y ∈ φ.toChart.source) :
    φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
      fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i) := by
  rw [hXφ y hy, φ.coord_mfderiv_field hy]

variable [CompleteSpace E] [T2Space M] [IsManifold 𝓘(ℝ, E) 1 M]
  (hX : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent 1 (fun y ↦ (⟨y, X y⟩ : TangentBundle 𝓘(ℝ, E) M)))
  (hXc : IsCompleteVectorField X)

/-- **The flow is linear in the chart along a linear orbit inside it.** If `X` is the linear field
of the Morse chart `φ` on its source and the linear orbit of the coordinates `z` stays in the
chart for all times between `0` and `t`, then the flow of `X` moves the point with coordinates `z`
at time `t` to the point with coordinates `(e^{-wᵢ t} zᵢ)ᵢ`. -/
theorem globalFlow_toChart_symm_coord_symm (hXφ : ∀ y ∈ φ.toChart.source, X y = φ.field y)
    {z : Fin (Module.finrank ℝ E) → ℝ} {t : ℝ}
    (hz : ∀ s ∈ uIcc 0 t, φ.coord.symm (φ.linearFlow s z) ∈ φ.toChart.target) :
    globalFlow X hX hXc t (φ.toChart.symm (φ.coord.symm z)) =
      φ.toChart.symm (φ.coord.symm (φ.linearFlow t z)) := by
  have := φ.finiteDimensional
  -- The times at which the linear orbit lies in the chart form an open set containing the
  -- closed interval between `0` and `t`, hence an open interval around it.
  set U := {s : ℝ | φ.coord.symm (φ.linearFlow s z) ∈ φ.toChart.target}
  have hU : IsOpen U :=
    φ.toChart.open_target.preimage <|
      φ.coord.symm.toLinearMap.continuous_of_finiteDimensional.comp <|
        continuous_iff_continuousAt.2 fun s ↦ (φ.hasDerivAt_linearFlow z s).continuousAt
  have hIcc : Icc (min 0 t) (max 0 t) ⊆ U := fun s hs ↦ hz s (by rwa [← Icc_min_max])
  obtain ⟨a, b₁, ⟨ha, hb₁⟩, hab₁⟩ := mem_nhds_iff_exists_Ioo_subset.1 <|
    hU.mem_nhds (hIcc ⟨le_rfl, min_le_max⟩)
  obtain ⟨a₂, b, ⟨ha₂, hb⟩, hab₂⟩ := mem_nhds_iff_exists_Ioo_subset.1 <|
    hU.mem_nhds (hIcc ⟨min_le_max, le_rfl⟩)
  have hab : ∀ s ∈ Ioo a b, φ.coord.symm (φ.linearFlow s z) ∈ φ.toChart.target := fun s hs ↦ by
    rcases lt_or_ge s (min 0 t) with hsm | hsm
    · exact hab₁ ⟨hs.1, hsm.trans hb₁⟩
    rcases le_or_gt s (max 0 t) with hsM | hsM
    · exact hIcc ⟨hsm, hsM⟩
    · exact hab₂ ⟨ha₂.trans hsM, hs.2⟩
  have hmem {s : ℝ} (hs : s ∈ uIcc 0 t) : s ∈ Ioo a b := by
    rw [← Icc_min_max] at hs
    exact ⟨ha.trans_le hs.1, hs.2.trans_lt hb⟩
  have heq := (φ.isMIntegralCurveOn_toChart_symm_linearFlow
    (fun y hy ↦ φ.coord_mfderiv_of_forall_eq_field hXφ hy) hab).eqOn_maximalIntegralCurve hX
    (hmem left_mem_uIcc) (by rw [MorseBottChart.linearFlow_zero])
  rw [globalFlow_apply]
  exact heq (hmem right_mem_uIcc)

/-- The centre of a Morse chart on whose source `X` is the linear field is a rest point of the
flow of `X`. -/
theorem globalFlow_self (hXφ : ∀ y ∈ φ.toChart.source, X y = φ.field y) (t : ℝ) :
    globalFlow X hX hXc t p = p := by
  have h := φ.globalFlow_toChart_symm_coord_symm hX hXc hXφ (z := 0) (t := t) fun s _ ↦ by
    rw [MorseBottChart.linearFlow_zero_right, map_zero, ← φ.apply_self]
    exact φ.toChart.map_source φ.mem_source
  rwa [MorseBottChart.linearFlow_zero_right, φ.toChart_symm_coord_symm_zero] at h

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
  have h := φ.globalFlow_toChart_symm_coord_symm hX hXc hXφ
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
  have h0 : φ.negativeExtend (0 : EuclideanSpace ℝ {i // φ.weight i < 0}).ofLp = 0 := by
    rw [WithLp.ofLp_zero, map_zero]
  have hsymm : φ.toChart.symm 0 = p := by
    rw [← φ.apply_self, φ.toChart.left_inv φ.mem_source]
  have hcont : Continuous fun c : EuclideanSpace ℝ {i // φ.weight i < 0} ↦
      φ.negativeExtend c.ofLp :=
    φ.negativeExtend.continuous_of_finiteDimensional.comp (PiLp.continuous_ofLp 2 _)
  have hlim : Tendsto (fun t : ℝ ↦ Real.exp t • c) atBot (𝓝 0) := by
    simpa using Real.tendsto_exp_atBot.smul_const c
  have h := (φ.toChart.continuousAt_symm (h0 ▸ hρ 0 (by simpa using hc.trans' (norm_nonneg c))
    )).tendsto.comp ((hcont.tendsto 0).comp hlim)
  rwa [h0, hsymm] at h
/-- **An orbit inside the chart is a linear orbit.** If `X` is the linear field of the Morse chart
`φ` on its source and the orbit of `x` stays in the source for the times in `[u, T]`, then the
coordinates of `Φ u x` are those of `Φ T x` moved by the linear flow for the time `u - T`. -/
theorem coord_toChart_globalFlow_of_forall_mem_source
    (hXφ : ∀ y ∈ φ.toChart.source, X y = φ.field y) {x : M} {u T : ℝ} (huT : u ≤ T)
    (hsrc : ∀ s ∈ Icc u T, globalFlow X hX hXc s x ∈ φ.toChart.source) :
    φ.coord (φ.toChart (globalFlow X hX hXc u x)) =
      φ.linearFlow (u - T) (φ.coord (φ.toChart (globalFlow X hX hXc T x))) := by
  set c : ℝ → Fin (Module.finrank ℝ E) → ℝ := fun s ↦ φ.coord (φ.toChart (globalFlow X hX hXc s x))
  have hc (s : ℝ) (hs : s ∈ Icc u T) : HasDerivAt c (fun i ↦ -(φ.weight i * c s i)) s := by
    have h := φ.coordL.hasFDerivAt.comp_hasDerivAt s <|
      Manifold.hasDerivAt_comp_curve (φ.mdifferentiableAt_toChart (hsrc s hs))
        (isMIntegralCurve_globalFlow hX hXc x s)
    convert h using 1
    · funext t
      simp only [c, comp_apply, MorseBottChart.coordL_apply]
    · exact ((φ.coordL_apply _).trans
        (φ.coord_mfderiv_of_forall_eq_field hXφ (hsrc s hs))).symm
  funext i
  -- `s ↦ e^{wᵢ s} cᵢ(s)` has derivative `0` on `[u, T]`, so it takes the same value at `u` and `T`.
  have hf (s : ℝ) (hs : s ∈ Icc u T) :
      HasDerivAt (fun s ↦ Real.exp (φ.weight i * s) * c s i) 0 s := by
    have h := (((hasDerivAt_id s).const_mul (φ.weight i)).exp).mul
      (hasDerivAt_pi.1 (hc s hs) i)
    convert h using 1
    · funext t
      simp only [Pi.mul_apply, id]
    · simp only [id]
      ring
  have hconst := constant_of_has_deriv_right_zero
    (fun s hs ↦ (hf s hs).continuousAt.continuousWithinAt)
    (fun s hs ↦ (hf s (Ico_subset_Icc_self hs)).hasDerivWithinAt) T ⟨huT, le_rfl⟩
  rw [MorseBottChart.linearFlow_apply]
  have hpos := Real.exp_pos (φ.weight i * u)
  have hexp : Real.exp (-(φ.weight i * (u - T))) =
      Real.exp (φ.weight i * T) / Real.exp (φ.weight i * u) := by
    rw [← Real.exp_sub]
    ring_nf
  rw [hexp, div_mul_eq_mul_div, hconst, mul_div_cancel_left₀ _ hpos.ne']

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
    φ.coord_toChart_globalFlow_of_forall_mem_source hX hXc hXφ hu fun s hs ↦ (hT s hs.2).1
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
  have hx' : x = Φ (-T) (Φ T x) := by rw [← Flow.map_add, neg_add_cancel, Flow.map_zero_apply]
  have haT : Φ T x = φ.toChart.symm (φ.negativeExtend a) := by
    have h := (ha T le_rfl).2
    rwa [sub_self, Real.exp_zero, one_smul] at h
  set A : EuclideanSpace ℝ {i // φ.weight i < 0} := WithLp.toLp 2 a
  have hA : A ≠ 0 := by
    rintro hA0
    have ha0 : a = 0 := by simpa [A] using hA0
    rw [haT, ha0, map_zero, ← φ.apply_self, φ.toChart.left_inv φ.mem_source,
      φ.globalFlow_self hX hXc hXφ] at hx'
    exact hxp hx'
  set n := ‖A‖
  have hn : 0 < n := norm_pos_iff.2 hA
  set c := (ρ / n) • A
  have hc : ‖c‖ = ρ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hρ0 hn), div_mul_cancel₀ _ hn.ne']
  have hcA : (n / ρ) • c = A := by
    rw [smul_smul, div_mul_div_comm, mul_comm n ρ, div_self (mul_pos hρ0 hn).ne', one_smul]
  -- The orbit of `x` meets the sphere of radius `ρ`, at the time `T - log (n / ρ)`.
  have hmeet : Φ T x = Φ (Real.log (n / ρ)) (φ.toChart.symm (φ.negativeExtend c.ofLp)) := by
    rcases le_or_gt n ρ with hnρ | hnρ
    · rw [φ.globalFlow_toChart_symm_negativeExtend_of_norm_le hX hXc hXφ hρ hc.le
        (Real.log_nonpos (div_pos hn hρ0).le ((div_le_one hρ0).2 hnρ)),
        Real.exp_log (div_pos hn hρ0), hcA, haT]
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
      sub_eq_neg_add, Flow.map_add, ← h, ← Flow.map_add, neg_add_cancel, Flow.map_zero_apply]
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

end MorseChart

end TauCeti
