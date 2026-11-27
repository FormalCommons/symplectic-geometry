/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.CenteredExtChartAt
public import SymplecticGeometry.Geometry.Manifold.Morse.GradientLike
import SymplecticGeometry.Geometry.Manifold.Flow.BandCrossing
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# An energy barrier for gradient-like fields, read in a chart

Let `X` be gradient-like for `f` on a Hausdorff manifold `M` modelled on a finite-dimensional
real space `E`, and let `γ` be an integral curve of `X` that tends to a point `p`. Along `γ` the
function `f` increases, and it stays below its limit `f p`. Read `γ` in the centred chart
`κ = SymplecticGeometry.centeredExtChartAt 𝓘(ℝ, E) p`, which sends `p` to `0`. If
`c ‖dκ(X)‖ ≤ df(X)` on the closed annulus `s ≤ ‖κ y‖ ≤ r` of the chart, then crossing that
annulus raises `f` by at least `c (r - s)`. So a curve that starts in the ball of radius `s` at a
value above `f p - c (r - s)` never leaves the chart, and stays in its closed ball of radius `r`.

Suppose moreover that `f` is `C¹`, that `X` is continuous, and that near `p` the function `f` has
no critical point other than `p`. Then for every small enough `r > 0`, such a `c > 0` exists on
the annulus `r / 2 ≤ ‖κ y‖ ≤ r`, by compactness: there `df(X)` is positive and `dκ(X)` is
bounded.

## Main declarations

* `TauCeti.IsGradientLike.mem_source_and_norm_centeredExtChartAt_le_of_tendsto`: the energy
  barrier, for given `s`, `r` and `c`.
* `TauCeti.IsGradientLike.exists_forall_mem_source_and_norm_centeredExtChartAt_le`: at an isolated
  critical point, the radius `r₀` of a closed ball in the chart and, for each `r ≤ r₀`, the
  room `ε` in the values of `f` that confine to the ball of radius `r` the curves tending to `p`
  that start in the ball of radius `r / 2`.

## Implementation notes

The argument follows Tau Ceti's `Flow.IsNegativeGradient.dist_le_of_mem_stableSet`, with the
time reversed (here `f` increases towards its limit) and on a manifold, in a chart. Since the norm
of `E` need not be differentiable, the curve's displacement across the annulus is bounded by the
crossing estimate `IsMIntegralCurveOn.mul_norm_sub_le_sub`, applied to the chart, rather than by
differentiating the distance.

## References

* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  Chapter 11
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 2.
-/

public section

open Filter Metric Set
open scoped ContDiff Manifold Topology
open SymplecticGeometry

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}

namespace IsGradientLike

/-- **An energy barrier for gradient-like fields.** Let `γ` be an integral curve of a field `X`
gradient-like for a differentiable function `f`, tending to `p`, and `κ` the centred chart at
`p`, whose target contains the closed ball of radius `r` about `0`. Suppose `c ≥ 0` and
`c ‖dκ(X)‖ ≤ df(X)` on the closed annulus `s ≤ ‖κ y‖ ≤ r`. If `γ 0` lies in the source of `κ`
with `‖κ (γ 0)‖ ≤ s` and `f p - c (r - s) < f (γ 0)`, then at every time `t ≥ 0` the curve lies
in the source of `κ`, with `‖κ (γ t)‖ ≤ r`. -/
theorem mem_source_and_norm_centeredExtChartAt_le_of_tendsto (hX : IsGradientLike f X)
    (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f) {γ : ℝ → M} (hγ : IsMIntegralCurve γ X) {p : M}
    (hlim : Tendsto γ atTop (𝓝 p)) {s r c : ℝ} (hc : 0 ≤ c)
    (hr : closedBall (0 : E) r ⊆ (centeredExtChartAt 𝓘(ℝ, E) p).target)
    (hann : ∀ y ∈ (centeredExtChartAt 𝓘(ℝ, E) p).source,
      s ≤ ‖centeredExtChartAt 𝓘(ℝ, E) p y‖ → ‖centeredExtChartAt 𝓘(ℝ, E) p y‖ ≤ r →
      c * ‖mvfderiv 𝓘(ℝ, E) (centeredExtChartAt 𝓘(ℝ, E) p) y (X y)‖ ≤
        mvfderiv 𝓘(ℝ, E) f y (X y))
    (h₀ : γ 0 ∈ (centeredExtChartAt 𝓘(ℝ, E) p).source)
    (hs : ‖centeredExtChartAt 𝓘(ℝ, E) p (γ 0)‖ ≤ s)
    (hfγ : f p - c * (r - s) < f (γ 0)) {t : ℝ} (ht : 0 ≤ t) :
    γ t ∈ (centeredExtChartAt 𝓘(ℝ, E) p).source ∧ ‖centeredExtChartAt 𝓘(ℝ, E) p (γ t)‖ ≤ r := by
  set κ := centeredExtChartAt 𝓘(ℝ, E) p
  have hγc := hγ.continuous
  -- Along `γ`, `f` increases towards its limit `f p`.
  have hmono : Monotone (f ∘ γ) := hX.monotone_comp hγ fun τ ↦ hf (γ τ)
  have hle (τ : ℝ) : f (γ τ) ≤ f p :=
    hmono.ge_of_tendsto ((hf p).continuousAt.tendsto.comp hlim) τ
  have hsr : s < r := by
    by_contra! h
    nlinarith [hle 0]
  -- `b` is the first time at which `γ` leaves the open ball of radius `r` in the chart.
  set O : Set M := (chartBall 𝓘(ℝ, E) p r : Set M)
  have hO : IsOpen O := (chartBall 𝓘(ℝ, E) p r).isOpen
  have hmemO {y : M} : y ∈ O ↔ y ∈ κ.source ∧ ‖κ y‖ < r :=
    mem_chartBall_iff_norm_centeredExtChartAt_lt _ _
  have h0O : γ 0 ∈ O := hmemO.2 ⟨h₀, hs.trans_lt hsr⟩
  by_contra! hcon
  have htO : γ t ∉ O := fun h ↦ (hmemO.1 h).2.not_ge (hcon (hmemO.1 h).1).le
  set A := {τ ∈ Icc 0 t | γ τ ∉ O}
  have hAbdd : BddBelow A := ⟨0, fun τ h ↦ h.1.1⟩
  have hbA : sInf A ∈ A :=
    (isClosed_Icc.inter (hO.isClosed_compl.preimage hγc)).csInf_mem ⟨t, ⟨ht, le_rfl⟩, htO⟩ hAbdd
  set b := sInf A
  have hbefore : ∀ τ ∈ Ico 0 b, γ τ ∈ O := fun τ hτ ↦ by
    by_contra hh
    exact hτ.2.not_ge (csInf_le hAbdd ⟨⟨hτ.1, hτ.2.le.trans hbA.1.2⟩, hh⟩)
  have hb0 : 0 < b := lt_of_le_of_ne hbA.1.1 fun h ↦ hbA.2 (h ▸ h0O)
  -- Up to time `b`, `γ` stays in the compact image of the closed ball of radius `r`.
  set C := κ.symm '' closedBall 0 r
  have hC : IsClosed C :=
    ((isCompact_closedBall _ _).image_of_continuousOn (κ.continuousOn_symm.mono hr)).isClosed
  have hOC : O ⊆ C := fun y hy ↦
    ⟨κ y, ball_subset_closedBall (mem_ball_zero_iff.2 (hmemO.1 hy).2), κ.left_inv (hmemO.1 hy).1⟩
  have hIcc : Icc 0 b ⊆ γ ⁻¹' C := by
    rw [← closure_Ico hb0.ne]
    exact closure_minimal (fun τ hτ ↦ hOC (hbefore τ hτ)) (hC.preimage hγc)
  have hsrc (τ : ℝ) (hτ : τ ∈ Icc 0 b) : γ τ ∈ κ.source ∧ ‖κ (γ τ)‖ ≤ r := by
    obtain ⟨w, hw, hwγ⟩ := hIcc hτ
    rw [← hwγ, κ.right_inv (hr hw)]
    exact ⟨κ.map_target (hr hw), mem_closedBall_zero_iff.1 hw⟩
  have hbr : r ≤ ‖κ (γ b)‖ := by
    by_contra! h
    exact hbA.2 (hmemO.2 ⟨(hsrc b ⟨hb0.le, le_rfl⟩).1, h⟩)
  -- `a` is the last time before `b` at which `γ` is within `s` of `p` in the chart.
  have hcont : ContinuousOn (fun τ ↦ κ (γ τ)) (Icc 0 b) :=
    κ.continuousOn.comp hγc.continuousOn fun τ h ↦ (hsrc τ h).1
  set B := Icc 0 b ∩ (fun τ ↦ κ (γ τ)) ⁻¹' closedBall 0 s
  have hBbdd : BddAbove B := ⟨b, fun τ h ↦ h.1.2⟩
  have haB : sSup B ∈ B :=
    (hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_closedBall).csSup_mem
      ⟨0, ⟨le_rfl, hb0.le⟩, mem_closedBall_zero_iff.2 hs⟩ hBbdd
  set a := sSup B
  have haB' : ‖κ (γ a)‖ ≤ s := mem_closedBall_zero_iff.1 haB.2
  have hab : a < b := lt_of_le_of_ne haB.1.2 fun h ↦ by rw [h] at haB'; linarith
  have hafter : Icc a b ⊆ Icc 0 b ∩ (fun τ ↦ κ (γ τ)) ⁻¹' {w | s ≤ ‖w‖} := by
    rw [← closure_Ioc hab.ne]
    refine closure_minimal (fun τ hτ ↦ ⟨⟨haB.1.1.trans hτ.1.le, hτ.2⟩, ?_⟩)
      (hcont.preimage_isClosed_of_isClosed isClosed_Icc
        (isClosed_le continuous_const continuous_norm))
    by_contra hh
    exact hτ.1.not_ge (le_csSup hBbdd ⟨⟨haB.1.1.trans hτ.1.le, hτ.2⟩,
      mem_closedBall_zero_iff.2 (not_le.1 hh).le⟩)
  -- Between `a` and `b`, `γ` crosses the annulus, and `f` rises by `c` times the displacement.
  have hmv := (hγ.isMIntegralCurveOn _).mul_norm_sub_le_sub (fun τ _ ↦ hf (γ τ)) hc hab.le
    (fun τ hτ ↦ mdifferentiableAt_centeredExtChartAt (hsrc τ (hafter hτ).1).1)
    fun τ hτ ↦
      have hτ' := hafter (Ico_subset_Icc_self hτ)
      hann _ (hsrc τ hτ'.1).1 hτ'.2 (hsrc τ hτ'.1).2
  have hdisp : r - s ≤ ‖κ (γ b) - κ (γ a)‖ := by
    have := norm_sub_norm_le (κ (γ b)) (κ (γ a))
    linarith
  have hfa : f (γ 0) ≤ f (γ a) := hmono haB.1.1
  nlinarith [hle b, mul_le_mul_of_nonneg_left hdisp hc]

/-- **Confinement near an isolated critical point.** Let `X` be continuous and gradient-like for a
`C¹` function `f`, and let `p` be a point near which `f` has no critical point other than `p`.
Let `κ` be the centred chart at `p`. There is `r₀ > 0` with the closed ball of radius `r₀` about
`0` in the target of `κ`, such that for every `r ∈ (0, r₀]` there is `ε > 0` with the following
property: an integral curve `γ` of `X` tending to `p`, with `γ 0` in the source of `κ`,
`‖κ (γ 0)‖ ≤ r / 2` and `f p - ε < f (γ 0)`, lies in the source of `κ` with `‖κ (γ t)‖ ≤ r` at
every time `t ≥ 0`. -/
theorem exists_forall_mem_source_and_norm_centeredExtChartAt_le (hX : IsGradientLike f X)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) 1 f)
    (hXc : Continuous fun y ↦ (⟨y, X y⟩ : TangentBundle 𝓘(ℝ, E) M)) {p : M}
    (hp : ∀ᶠ y in 𝓝[≠] p, mvfderiv 𝓘(ℝ, E) f y ≠ 0) :
    ∃ r₀ > 0, closedBall (0 : E) r₀ ⊆ (centeredExtChartAt 𝓘(ℝ, E) p).target ∧
      ∀ r ∈ Ioc 0 r₀, ∃ ε > 0, ∀ γ : ℝ → M, IsMIntegralCurve γ X → Tendsto γ atTop (𝓝 p) →
        γ 0 ∈ (centeredExtChartAt 𝓘(ℝ, E) p).source →
        ‖centeredExtChartAt 𝓘(ℝ, E) p (γ 0)‖ ≤ r / 2 →
        f p - ε < f (γ 0) → ∀ t, 0 ≤ t →
          γ t ∈ (centeredExtChartAt 𝓘(ℝ, E) p).source ∧
            ‖centeredExtChartAt 𝓘(ℝ, E) p (γ t)‖ ≤ r := by
  set e := extChartAt 𝓘(ℝ, E) p
  -- The estimates are proved in the extended chart `e`, and read in the centred one.
  have htarget {ρ : ℝ} (h : closedBall (e p) ρ ⊆ e.target) :
      closedBall (0 : E) ρ ⊆ (centeredExtChartAt 𝓘(ℝ, E) p).target := fun w hw ↦ by
    rw [mem_centeredExtChartAt_target_iff]
    exact h (by simpa [e, dist_eq_norm] using hw)
  -- A ball about `e p` in the chart target whose points other than `e p` are not critical.
  have hev : ∀ᶠ w in 𝓝 (e p),
      w ∈ e.target ∧ (e.symm w ≠ p → mvfderiv 𝓘(ℝ, E) f (e.symm w) ≠ 0) := by
    have h₁ : ∀ᶠ y in 𝓝 p, y ≠ p → mvfderiv 𝓘(ℝ, E) f y ≠ 0 := eventually_nhdsWithin_iff.1 hp
    have h₂ : Tendsto e.symm (𝓝 (e p)) (𝓝 p) := by
      simpa only [e, extChartAt_to_inv] using (continuousAt_extChartAt_symm p).tendsto
    exact Filter.Eventually.and (extChartAt_target_mem_nhds (I := 𝓘(ℝ, E)) p) (h₂.eventually h₁)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  refine ⟨δ / 2, half_pos hδ,
    htarget fun w hw ↦ (hball w (closedBall_subset_ball (half_lt_self hδ) hw)).1, fun r hr ↦ ?_⟩
  have hrδ : closedBall (e p) r ⊆ ball (e p) δ :=
    closedBall_subset_ball (hr.2.trans_lt (half_lt_self hδ))
  have hrt : closedBall (e p) r ⊆ e.target := fun w hw ↦ (hball w (hrδ hw)).1
  -- On the compact annulus `r / 2 ≤ ‖w - e p‖ ≤ r`, `df(X)` is positive and `de(X)` bounded.
  set K := {w | r / 2 ≤ ‖w - e p‖} ∩ closedBall (e p) r
  have hK : IsCompact K := (isCompact_closedBall _ _).inter_left
    (isClosed_le continuous_const (continuous_norm.comp (continuous_sub_right _)))
  have hKt : K ⊆ e.target := fun w hw ↦ hrt hw.2
  have hdf : Continuous fun y ↦ mvfderiv 𝓘(ℝ, E) f y (X y) :=
    (hf.contMDiff_mvfderiv_apply (m := 0) (by simp)).continuous.comp hXc
  have hpos (w : E) (hw : w ∈ K) : 0 < mvfderiv 𝓘(ℝ, E) f (e.symm w) (X (e.symm w)) := by
    refine hX.mvfderiv_apply_pos ((hball w (hrδ hw.2)).2 fun h ↦ ?_)
    have hwp : w = e p := by rw [← e.right_inv (hKt hw), h]
    have := hw.1
    rw [mem_ofPred_eq, hwp, sub_self, norm_zero] at this
    linarith [hr.1]
  obtain ⟨m, hm, hmK⟩ :=
    hK.exists_forall_le' (hdf.comp_continuousOn ((continuousOn_extChartAt_symm p).mono hKt)) hpos
  set V := VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm X with hVdef
  have hV : ContinuousOn V K := by
    have h := ContMDiffOn.contDiffOn_mpullback_extChartAt_symm (x := p) (m := 0) (n := ∞)
      (U := univ) (contMDiff_zero_iff.2 hXc).contMDiffOn (by simp)
    rw [(isOpen_extChartAt_target p).interior_eq, preimage_univ, inter_univ] at h
    exact h.continuousOn.mono hKt
  obtain ⟨L, hL⟩ := hK.exists_bound_of_continuousOn hV
  set c := m / max L 1
  have hc : 0 < c := div_pos hm (lt_max_of_lt_right one_pos)
  refine ⟨c * (r - r / 2), mul_pos hc (by linarith [hr.1]),
    fun γ hγ hlim h₀ hs hfγ t ht ↦ ?_⟩
  refine hX.mem_source_and_norm_centeredExtChartAt_le_of_tendsto (hf.mdifferentiable one_ne_zero)
    hγ hlim hc.le (htarget hrt) (fun y hy h₁ h₂ ↦ ?_) h₀ hs hfγ ht
  rw [centeredExtChartAt_source_eq_extChartAt_source] at hy
  rw [centeredExtChartAt_apply] at h₁ h₂
  rw [mvfderiv_centeredExtChartAt]
  have hyK : e y ∈ K := ⟨h₁, mem_closedBall_iff_norm.2 h₂⟩
  have hVy : mvfderiv 𝓘(ℝ, E) e y (X y) = V (e y) := by
    rw [mvfderiv_apply_eq_mfderiv_apply, hVdef,
      VectorField.mpullback_extChartAt_symm_apply_eq_mfderiv X hy (by simp)]
  calc c * ‖mvfderiv 𝓘(ℝ, E) e y (X y)‖ ≤ c * max L 1 := by
        rw [hVy]
        exact mul_le_mul_of_nonneg_left ((hL _ hyK).trans (le_max_left _ _)) hc.le
    _ = m := div_mul_cancel₀ _ (lt_max_of_lt_right one_pos).ne'
    _ ≤ mvfderiv 𝓘(ℝ, E) f y (X y) := by
      have h := hmK _ hyK
      rwa [Function.comp_apply, e.left_inv hy] at h

end IsGradientLike

end TauCeti

end
