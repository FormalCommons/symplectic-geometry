/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Dynamics.Flow.LevelCrossing
public import TauCeti.Geometry.Manifold.IntegralCurve.GlobalFlow
public import TauCeti.Geometry.Manifold.Morse.Stable.Manifold
import SymplecticGeometry.Analysis.InnerProductSpace.RadialExtension
import SymplecticGeometry.Geometry.Manifold.Flow.BandCrossing
import SymplecticGeometry.Geometry.Manifold.Flow.Basic
import SymplecticGeometry.Geometry.Manifold.Flow.LevelCrossing
import SymplecticGeometry.Geometry.Manifold.IntegralCurve.Monotone
import SymplecticGeometry.Geometry.Manifold.Morse.UnstableSet

/-!
# A time function on a ball of negative coordinates from the crossing time of a level

Let `X` be a complete smooth vector field on a boundaryless manifold `M` modelled on `E`, with
flow `Φ = TauCeti.globalFlow X`, let `g` be a smooth function with `dg(X) ≤ 0`, and let `φ` be a
Morse chart of `g` at `p` on whose source `X` is the linear field `TauCeti.MorseChart.field`.
Write `N` for the Euclidean space of the coordinates of negative weight, and `y_c` for the point
of the chart with coordinates `c ∈ N` of negative weight and `0` of positive weight. Let the closed
ball of radius `ρ > 0` of `N` lie in the chart, let `a < g p`, and let `b ≥ a` bound `g` on the
points `y_c` with `‖c‖ = ρ`. Assume that the band `g⁻¹[a, b]` is compact and that `dg(X) < 0` on
it.

`TauCeti.MorseChart.exists_radial_extension_levelCrossingTime` gives a smooth `θ : N → ℝ`, equal
on the sphere of radius `ρ` to the time `Flow.levelCrossingTime Φ g a` at which the flow line of
`y_c` crosses the level `{g = a}`, such that `r ↦ θ (r • u) + log r` has a positive derivative for
every `u`. It states this in the two forms that the next steps use: that function is strictly
monotone on `(0, ∞)`, which gives the hypothesis of
`TauCeti.MorseChart.injOn_globalFlow_toChart_symm_negativeExtend`, and `1 + dθ_c(c) > 0` (its
derivative at `r = 1` for `u = c`), the hypothesis of
`TauCeti.MorseChart.exists_isSmoothEmbedding_globalFlow_toChart_symm`. The map
`F c = Φ (θ c) y_c` then sends the sphere of radius `ρ` into the level
`{g = a}` and the closed ball into `{a ≤ g}`, and its image of the open ball contains every point
of the unstable set of `p` above the level `a`.

The construction:

* Each flow line from the sphere reaches the level `a`: forwards it goes below `a` by the descent
  lemma `TauCeti.exists_forall_globalFlow_lt`, and backwards it tends to `p`, where `g p > a`.
* It crosses the level only once (`IsMIntegralCurve.subsingleton_setOfPred_apply_eq`), since `g` is
  antitone along it and `dg(X) < 0` on the level. So the crossing time is smooth near the sphere
  (`TauCeti.contMDiffAt_levelCrossingTime`).
* Composed with `u ↦ ρ • u` on the unit sphere, it extends radially from the radius `ρ` by
  `SymplecticGeometry.exists_contDiff_radial_extension_hasDerivAt_add_log_pos`.
* For `‖u‖ = ρ` and `0 < r ≤ 1`, `F (r • u) = Φ (θ (r • u) + log r) y_u`
  (`TauCeti.MorseChart.globalFlow_toChart_symm_negativeExtend_smul`), with a time at most `θ u`
  since that time increases with `r` (`SymplecticGeometry.strictMonoOn_smul_add_log`),
  so `g ≥ a` there; and the description of the unstable set from the sphere
  (`TauCeti.MorseChart.exists_globalFlow_eq_of_mem_unstableSet`) with
  `TauCeti.MorseChart.globalFlow_mem_image_ball` gives the last property.

The flow lines through a sphere of negative coordinates, followed up to a level, are also how
Tau Ceti's `TauCeti.IsAdaptedPseudoGradient.exists_isSliceChart_unstableSet`
(`Morse/Stable/Manifold.lean`) describes the unstable set of an adapted pseudo-gradient.

## Main results

* `TauCeti.MorseChart.exists_radial_extension_levelCrossingTime`: the time function `θ` and the
  properties of `F` above.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Part I, §3.
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Section 2.1.
-/

public section

open Filter Function Metric Set Topology
open scoped ContDiff Manifold

namespace TauCeti

namespace MorseChart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [T2Space M] [IsManifold 𝓘(ℝ, E) 1 M]
  {g : M → ℝ} {p : M} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x} (φ : MorseChart E g p)
  (hX : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent 1 (fun y ↦ (⟨y, X y⟩ : TangentBundle 𝓘(ℝ, E) M)))
  (hXc : IsCompleteVectorField X)

/-- **A time function from the crossing time of a level.** Let `X` be a complete smooth field
with flow `Φ`, `g` a smooth function with `dg(X) ≤ 0`, and `φ` a Morse chart of `g` at `p` on
whose source `X` is the linear field of the chart. Write `y_c` for the point of the chart with
coordinates `c` of negative weight and `0` of positive weight, and let the closed ball of radius
`ρ > 0` of these coordinates lie in the chart. Let `a < g p`, `a ≤ b`, `g (y_c) ≤ b` for
`‖c‖ = ρ`, and let the band `g⁻¹[a, b]` be compact with `dg(X) < 0` on it.

Then there is a smooth `θ`, equal for `‖c‖ = ρ` to the time at which the flow line of `y_c`
crosses the level `{g = a}`, such that `r ↦ θ (r • u) + log r` is strictly monotone on `(0, ∞)`
for every `u`, such that `1 + dθ_c(c) > 0` for every `c`, and such that `F c = Φ (θ c) y_c`
maps the sphere of radius `ρ` into
`{g = a}` and the closed ball into `{a ≤ g}`, and reaches, from the open ball, every point `x` of
the unstable set of `p` with `a < g x`. -/
theorem exists_radial_extension_levelCrossingTime [IsManifold 𝓘(ℝ, E) ∞ M]
    (hXs : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent ∞ (fun y ↦ (⟨y, X y⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hXφ : ∀ y ∈ φ.toChart.source, X y = φ.field y) (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ g)
    (hgX : ∀ y, mvfderiv 𝓘(ℝ, E) g y (X y) ≤ 0) {ρ : ℝ} (hρ0 : 0 < ρ)
    (hρ : ∀ c : EuclideanSpace ℝ {i // φ.weight i < 0}, ‖c‖ ≤ ρ →
      φ.negativeExtend c.ofLp ∈ φ.toChart.target)
    {a b : ℝ} (ha : a < g p) (hab : a ≤ b)
    (hb : ∀ c : EuclideanSpace ℝ {i // φ.weight i < 0}, ‖c‖ = ρ →
      g (φ.toChart.symm (φ.negativeExtend c.ofLp)) ≤ b)
    (hcompact : IsCompact (g ⁻¹' Icc a b))
    (hneg : ∀ y, a ≤ g y → g y ≤ b → mvfderiv 𝓘(ℝ, E) g y (X y) < 0) :
    ∃ θ : EuclideanSpace ℝ {i // φ.weight i < 0} → ℝ, ContDiff ℝ ∞ θ ∧
      (∀ c : EuclideanSpace ℝ {i // φ.weight i < 0}, ‖c‖ = ρ →
        θ c = Flow.levelCrossingTime (globalFlow X hX hXc) g a
          (φ.toChart.symm (φ.negativeExtend c.ofLp))) ∧
      (∀ u : EuclideanSpace ℝ {i // φ.weight i < 0},
        StrictMonoOn (fun r ↦ θ (r • u) + Real.log r) (Ioi 0)) ∧
      (∀ c : EuclideanSpace ℝ {i // φ.weight i < 0}, 0 < 1 + fderiv ℝ θ c c) ∧
      MapsTo (fun c ↦ globalFlow X hX hXc (θ c) (φ.toChart.symm (φ.negativeExtend c.ofLp)))
        (sphere 0 ρ) {x | g x = a} ∧
      MapsTo (fun c ↦ globalFlow X hX hXc (θ c) (φ.toChart.symm (φ.negativeExtend c.ofLp)))
        (closedBall 0 ρ) {x | a ≤ g x} ∧
      ∀ x ∈ Flow.unstableSet (globalFlow X hX hXc) p, a < g x →
        x ∈ (fun c ↦ globalFlow X hX hXc (θ c) (φ.toChart.symm (φ.negativeExtend c.ofLp))) ''
          ball 0 ρ := by
  set Φ := globalFlow X hX hXc
  set ι : EuclideanSpace ℝ {i // φ.weight i < 0} → M :=
    fun c ↦ φ.toChart.symm (φ.negativeExtend c.ofLp)
  have hgd (y : M) : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ) g y := (hg y).mdifferentiableAt (by simp)
  -- Along each flow line `g` is antitone, and it meets the level `a` at most once.
  have hanti (y : M) : Antitone fun t ↦ g (Φ t y) :=
    antitone_comp_globalFlow hX hXc (hg.mdifferentiable (by simp)) hgX y
  have huniq (y : M) : {t | g (Φ t y) = a}.Subsingleton :=
    (isMIntegralCurve_globalFlow hX hXc y).subsingleton_setOfPred_apply_eq (fun _ ↦ hgd _) (hanti y)
      fun _ ht ↦ (hneg _ ht.ge (ht.le.trans hab)).ne
  -- Each flow line from the sphere reaches the level `a`.
  obtain ⟨T, hT0, hT⟩ :=
    exists_forall_globalFlow_lt hX hXc (hg.of_le (by simp)) hab hcompact hneg
  have hreach (c : EuclideanSpace ℝ {i // φ.weight i < 0}) (hc : ‖c‖ = ρ) :
      ∃ t, g (Φ t (ι c)) = a := by
    have hlow : g (Φ T (ι c)) < a := hT _ (hb c hc) T le_rfl
    have hu : Tendsto (fun t ↦ g (Φ t (ι c))) atBot (𝓝 (g p)) :=
      (hg.continuous.tendsto p).comp (Flow.mem_unstableSet.1
        (φ.mapsTo_closedBall_unstableSet hX hXc hXφ hρ (mem_closedBall_zero_iff.2 hc.le)))
    obtain ⟨t₀, ht₀, ht₀0⟩ :=
      ((hu.eventually (lt_mem_nhds ha)).and (eventually_le_atBot 0)).exists
    have hcont : Continuous fun t ↦ g (Φ t (ι c)) :=
      hg.continuous.comp (Φ.continuous_eval_const _)
    obtain ⟨t, -, ht⟩ := intermediate_value_Icc' (ht₀0.trans hT0) hcont.continuousOn
      ⟨hlow.le, ht₀.le⟩
    exact ⟨t, ht⟩
  -- The crossing time, as a function of the coordinates, is smooth near the sphere.
  set τ : EuclideanSpace ℝ {i // φ.weight i < 0} → ℝ :=
    fun c ↦ Flow.levelCrossingTime Φ g a (ι c)
  have hιs : ContDiff ℝ ∞ fun c : EuclideanSpace ℝ {i // φ.weight i < 0} ↦
      φ.negativeExtend c.ofLp := by
    simp_rw [← negativeExtendL_apply]
    exact φ.negativeExtendL.contDiff
  have hτs (c : EuclideanSpace ℝ {i // φ.weight i < 0}) (hc : ‖c‖ = ρ) :
      ContDiffAt ℝ ∞ τ c := by
    have hlev : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) ∞ (Flow.levelCrossingTime Φ g a) (ι c) :=
      contMDiffAt_levelCrossingTime (n := ⊤) le_top hXs hXc (flowOf_eq_globalFlow hX hXc)
        (Eventually.of_forall huniq) (hreach c hc) (hg _)
        (hneg _ (Flow.apply_flow_levelCrossingTime (hreach c hc)).ge
          ((Flow.apply_flow_levelCrossingTime (hreach c hc)).le.trans hab)).ne
    have hsymm : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ φ.toChart.symm (φ.negativeExtend c.ofLp) :=
      (contMDiffOn_symm_of_mem_maximalAtlas φ.mem_maximalAtlas).contMDiffAt
        (φ.toChart.open_target.mem_nhds (hρ c hc.le))
    exact contMDiffAt_iff_contDiffAt.1
      (hlev.comp c (hsymm.comp c hιs.contMDiff.contMDiffAt))
  -- Extend radially the crossing time from the sphere of radius `ρ`.
  obtain ⟨θ, hθs, -, hθτ₁, hθ₁d⟩ :=
    SymplecticGeometry.exists_contDiff_radial_extension_hasDerivAt_add_log_pos (n := ⊤)
      (τ := fun u ↦ τ (ρ • u)) (ρ := ρ)
      (fun u hu ↦ (hτs (ρ • u) (by rw [norm_smul, hu, mul_one, Real.norm_of_nonneg hρ0.le])).comp
        u (contDiffAt_id.const_smul ρ)) hρ0
  have hθτ (c : EuclideanSpace ℝ {i // φ.weight i < 0}) (hc : ‖c‖ = ρ) : θ c = τ c := by
    have h1 : ‖ρ⁻¹ • c‖ = 1 := by
      rw [norm_smul, hc, Real.norm_of_nonneg (inv_nonneg.2 hρ0.le), inv_mul_cancel₀ hρ0.ne']
    have h := hθτ₁ _ h1 ρ le_rfl
    rwa [smul_inv_smul₀ hρ0.ne'] at h
  -- Along each ray `r ↦ θ (r • u) + log r` is strictly monotone, and `0 < 1 + dθ_c(c)`.
  have hmono (u : EuclideanSpace ℝ {i // φ.weight i < 0}) :
      StrictMonoOn (fun r ↦ θ (r • u) + Real.log r) (Ioi 0) :=
    SymplecticGeometry.strictMonoOn_smul_add_log hθ₁d u
  have hθc (c : EuclideanSpace ℝ {i // φ.weight i < 0}) : 0 < 1 + fderiv ℝ θ c c :=
    SymplecticGeometry.one_add_fderiv_apply_self_pos hθ₁d c
  -- The centre of the ball goes to `p`.
  have hF0 : Φ (θ 0) (ι 0) = p := φ.globalFlow_toChart_symm_negativeExtend_zero hX hXc hXφ (θ 0)
  -- On the sphere, `F` lands on the level `a`.
  have hsph (c : EuclideanSpace ℝ {i // φ.weight i < 0}) (hc : ‖c‖ = ρ) :
      g (Φ (θ c) (ι c)) = a := by
    rw [hθτ c hc]
    exact Flow.apply_flow_levelCrossingTime (hreach c hc)
  refine ⟨θ, hθs, hθτ, hmono, hθc,
    fun c hc ↦ hsph c (mem_sphere_zero_iff_norm.1 hc), ?_, ?_⟩
  · intro c hc
    rw [mem_closedBall_zero_iff] at hc
    rcases eq_or_ne c 0 with rfl | hc0
    · simp only [mem_ofPred_eq]
      rw [hF0]
      exact ha.le
    have hn : 0 < ‖c‖ := norm_pos_iff.2 hc0
    set u := (ρ / ‖c‖) • c
    set r := ‖c‖ / ρ
    have hr0 : 0 < r := div_pos hn hρ0
    have hr1 : r ≤ 1 := (div_le_one hρ0).2 hc
    have hu : ‖u‖ = ρ := by
      rw [norm_smul, Real.norm_of_nonneg (div_pos hρ0 hn).le, div_mul_cancel₀ _ hn.ne']
    have hru : r • u = c := by
      simp only [u, r, smul_smul]
      rw [div_mul_div_comm, mul_comm, div_self (mul_pos hρ0 hn).ne', one_smul]
    -- The time `θ (r • u) + log r` is at most `θ u`, by monotonicity along the ray.
    have hle : θ (r • u) + Real.log r ≤ θ u := by
      simpa using (hmono u).monotoneOn hr0 (show (0 : ℝ) < 1 from one_pos) hr1
    simp only [mem_ofPred_eq]
    rw [← hru, φ.globalFlow_toChart_symm_negativeExtend_smul hX hXc hXφ hρ hu.le hr0 hr1]
    calc a = g (Φ (θ u) (ι u)) := (hsph u hu).symm
      _ ≤ g (Φ (θ (r • u) + Real.log r) (ι u)) := hanti _ hle
  · intro x hx hax
    rcases eq_or_ne x p with rfl | hxp
    · exact ⟨0, mem_ball_self hρ0, hF0⟩
    obtain ⟨s, c, hc, hsx, -⟩ :=
      φ.exists_globalFlow_eq_of_mem_unstableSet hX hXc hXφ hρ0 hρ hx hxp
    have hs : s < θ c := by
      by_contra! h
      have := hanti (ι c) h
      simp only at this
      rw [hsx, hsph c hc] at this
      linarith
    rw [← hsx]
    exact φ.globalFlow_mem_image_ball hX hXc hXφ hρ0 hρ hθs.continuous.continuousOn hc.le hs

end MorseChart

end TauCeti

end
