/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.IntegralCurve.GlobalFlow
public import TauCeti.Geometry.Manifold.Morse.Stable.Manifold
public import Mathlib.Geometry.Manifold.SmoothEmbedding
import SymplecticGeometry.Analysis.Calculus.Deriv.MeanValue
import SymplecticGeometry.Geometry.Manifold.Morse.Core.Coordinates
import SymplecticGeometry.Geometry.Manifold.Morse.Core.CrossingTime
import SymplecticGeometry.Geometry.Manifold.Morse.Core.FlowOut
import SymplecticGeometry.Geometry.Manifold.Morse.UnstableSet

/-!
# The cube chart of the unstable set at a critical point

Let `X` be a complete smooth vector field on a boundaryless finite-dimensional manifold `M`
modelled on `E`, with flow `Φ = TauCeti.globalFlow X`, and let `g` be a smooth function with
`dg(X) ≤ 0`. Let `φ` be a Morse chart of `g` at `p`, of index `m`, on whose source `X` is the linear
field `TauCeti.MorseChart.field`. Write `D m = (Fin m → ℝ) × (Fin (dim E - m) → ℝ)` with sup norms,
with cube `closedBall 0 1 ×ˢ {0}` and boundary sphere `sphere 0 1 ×ˢ {0}`.

## Main results

* `TauCeti.MorseChart.exists_cubeChart_unstableSet`: given levels `a₀ < a < g p` such that
  `dg(X) < 0` at every point `y` with `a₀ ≤ g y < g p`, and such that the bands `g⁻¹[a₀, b]`
  with `b < g p` are compact, there is a smooth embedding `χ : D m → M` with open range and
  `χ 0 = p` which sends the cube into the unstable set of `p` above the level `a₀`, and its
  boundary sphere below the level `a`, and whose image of the cube contains every point of the
  unstable set of `p` at level at least `a`.

## Construction

Pick a level `a'` strictly between `a₀` and `a`, and a radius `ρ > 0` such that the closed
Euclidean ball of radius `ρ` of the coordinates of negative weight lies in the chart, with
`ρ² / 2 < g p - a`; on its sphere `g = g p - ρ² / 2`, which lies above `a`
(`TauCeti.MorseChart.apply_toChart_symm_negativeExtend`). Then:

* `TauCeti.MorseChart.exists_radial_extension_levelCrossingTime` (`Morse/Core/CrossingTime.lean`)
  gives the time function `θ`, equal on the sphere to the crossing time of the level `a'`, for
  which `r ↦ θ (r • u) + log r` has a positive derivative. So `F c = Φ (θ c) y_c` sends the sphere
  to the level `a'`, the closed ball above it, and its open ball reaches the part of the unstable
  set of `p` above `a'`.
* `F` is injective on the closed ball
  (`TauCeti.MorseChart.injOn_globalFlow_toChart_symm_negativeExtend`), and its thickening
  in the coordinates of positive weight is a smooth embedding with open image near the ball
  (`TauCeti.MorseChart.exists_isSmoothEmbedding_globalFlow_toChart_symm`,
  `Morse/Core/FlowOut.lean`).
* The points `c` of the closed ball with `g (F c) ≥ a` form a compact subset `K` of the open ball,
  and `SymplecticGeometry.exists_cubeChart_of_isSmoothEmbedding` (`Morse/Core/Coordinates.lean`)
  turns the thickened map into the chart on all of `D m`.

The chart composes a Morse chart with the flow as Tau Ceti's
`TauCeti.IsAdaptedPseudoGradient.exists_isSliceChart_unstableSet` (`Morse/Stable/Manifold.lean`)
does on compact manifolds, here with a time that depends on the point.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Part I, §3.
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Section 2.1.
-/

public section

open Function Manifold Metric Set
open scoped ContDiff

namespace TauCeti

namespace MorseChart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [T2Space M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {g : M → ℝ} {p : M} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}
  (hX : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent 1 (fun y ↦ (⟨y, X y⟩ : TangentBundle 𝓘(ℝ, E) M)))
  (hXc : IsCompleteVectorField X)

/-- **The cube chart of the unstable set at a critical point.** Let `X` be a complete smooth
field with flow `Φ`, `g` a smooth function with `dg(X) ≤ 0`, and `φ` a Morse chart of `g` at `p`
on whose source `X` is the linear field of the chart. Let `a₀ < a < g p`, let
`dg(X) < 0` at every point `y` with `a₀ ≤ g y < g p`, and let `g⁻¹[a₀, b]` be compact for every
`b < g p`. Write `m` for the Morse index of `g` at `p`.

Then there is a smooth embedding `χ : (Fin m → ℝ) × (Fin (dim E - m) → ℝ) → M` (sup norms) with
open range and `χ 0 = p` that maps `closedBall 0 1 ×ˢ {0}` into the unstable set of `p` for `Φ`
and above the level `a₀`, and `sphere 0 1 ×ˢ {0}` below the level `a`, and whose image of
`closedBall 0 1 ×ˢ {0}` contains every point of the unstable set of `p` at level at least `a`. -/
theorem exists_cubeChart_unstableSet
    (hXs : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent ∞ (fun y ↦ (⟨y, X y⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (φ : MorseChart E g p) (hXφ : ∀ y ∈ φ.toChart.source, X y = φ.field y)
    (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ g) (hgX : ∀ y, mvfderiv 𝓘(ℝ, E) g y (X y) ≤ 0)
    {a₀ a : ℝ} (ha₀ : a₀ < a) (ha : a < g p)
    (hcompact : ∀ b < g p, IsCompact (g ⁻¹' Icc a₀ b))
    (hneg : ∀ y, a₀ ≤ g y → g y < g p → mvfderiv 𝓘(ℝ, E) g y (X y) < 0) :
    ∃ χ : (Fin (manifoldMorseIndex 𝓘(ℝ, E) g p) → ℝ) ×
        (Fin (Module.finrank ℝ E - manifoldMorseIndex 𝓘(ℝ, E) g p) → ℝ) → M,
      IsSmoothEmbedding 𝓘(ℝ, (Fin (manifoldMorseIndex 𝓘(ℝ, E) g p) → ℝ) ×
        (Fin (Module.finrank ℝ E - manifoldMorseIndex 𝓘(ℝ, E) g p) → ℝ)) 𝓘(ℝ, E) ∞ χ ∧
      IsOpen (range χ) ∧ χ 0 = p ∧
      MapsTo χ (closedBall 0 1 ×ˢ {0})
        (Flow.unstableSet (globalFlow X hX hXc) p ∩ {x | a₀ < g x}) ∧
      MapsTo χ (sphere 0 1 ×ˢ {0}) {x | g x < a} ∧
      Flow.unstableSet (globalFlow X hX hXc) p ∩ {x | a ≤ g x} ⊆
        χ '' (closedBall 0 1 ×ˢ {0}) := by
  set Φ := globalFlow X hX hXc
  -- The radius `ρ`, with the sphere of radius `ρ` at the level `b = g p - ρ² / 2 > a`.
  obtain ⟨ρ₀, hρ₀, hρ₀T⟩ := φ.exists_pos_forall_norm_le_negativeExtend_mem_target
  set ρ := min ρ₀ (Real.sqrt (g p - a))
  have hρ0 : 0 < ρ := lt_min hρ₀ (Real.sqrt_pos.2 (sub_pos.2 ha))
  have hρ (c : EuclideanSpace ℝ {i // φ.weight i < 0}) (hc : ‖c‖ ≤ ρ) :
      φ.negativeExtend c.ofLp ∈ φ.toChart.target :=
    hρ₀T c (hc.trans (min_le_left _ _))
  have hρsq : ρ ^ 2 ≤ g p - a := by
    calc ρ ^ 2 ≤ Real.sqrt (g p - a) ^ 2 := pow_le_pow_left₀ hρ0.le (min_le_right _ _) 2
      _ = g p - a := Real.sq_sqrt (sub_pos.2 ha).le
  set b := g p - ρ ^ 2 / 2
  have hab : a < b := by
    have : 0 < ρ ^ 2 := by positivity
    simp only [b]; linarith
  have hbp : b < g p := by
    have : 0 < ρ ^ 2 := by positivity
    simp only [b]; linarith
  have hb (c : EuclideanSpace ℝ {i // φ.weight i < 0}) (hc : ‖c‖ = ρ) :
      g (φ.toChart.symm (φ.negativeExtend c.ofLp)) ≤ b := by
    rw [φ.apply_toChart_symm_negativeExtend (hρ c hc.le), hc]
  -- The level `a'` between `a₀` and `a`, and the time function `θ`.
  set a' := (a₀ + a) / 2
  have ha₀' : a₀ < a' := by simp only [a']; linarith
  have ha' : a' < a := by simp only [a']; linarith
  obtain ⟨θ, hθs, -, hθd, hsph, hball, hreach⟩ :=
    φ.exists_radial_extension_levelCrossingTime hX hXc hXs hXφ hg hgX hρ0 hρ
      (ha'.trans ha) (ha'.trans hab).le hb
      ((hcompact b hbp).of_isClosed_subset
        (isClosed_Icc.preimage hg.continuous) fun y hy ↦ ⟨ha₀'.le.trans hy.1, hy.2⟩)
      fun y hy hy' ↦ hneg y (ha₀'.le.trans hy) (hy'.trans_lt hbp)
  set F := fun c : EuclideanSpace ℝ {i // φ.weight i < 0} ↦
    Φ (θ c) (φ.toChart.symm (φ.negativeExtend c.ofLp)) with hF
  -- `F` is injective on the closed ball, and its thickening is an open embedding near it.
  have hmono (u : EuclideanSpace ℝ {i // φ.weight i < 0}) (hu : ‖u‖ = ρ) :
      StrictMonoOn (fun r ↦ θ (r • u) + Real.log r) (Ioc 0 1) :=
    (StrictMonoOn.of_forall_hasDerivAt_pos (convex_Ioi 0)
      (hθd u (norm_pos_iff.1 (hu ▸ hρ0)))).mono Ioc_subset_Ioi_self
  have hinj : InjOn F (closedBall 0 ρ) :=
    φ.injOn_globalFlow_toChart_symm_negativeExtend hX hXc hXφ hρ hmono
  have hθρ (c : EuclideanSpace ℝ {i // φ.weight i < 0}) (_ : ‖c‖ ≤ ρ) :
      0 < 1 + fderiv ℝ θ c c := by
    rcases eq_or_ne c 0 with rfl | hc0
    · simp
    obtain ⟨d, hd, hdd⟩ := hθd c hc0 1 one_pos
    have h : HasDerivAt (fun r : ℝ ↦ θ (r • c) + Real.log r) (fderiv ℝ θ c c + 1) 1 := by
      have hθc : HasFDerivAt θ (fderiv ℝ θ c) ((1 : ℝ) • c) := by
        rw [one_smul]; exact ((hθs.differentiable (by simp)) c).hasFDerivAt
      have h1 := hθc.comp_hasDerivAt (1 : ℝ) ((hasDerivAt_id (1 : ℝ)).smul_const c)
      simp only [one_smul] at h1
      exact h1.add (by simpa using Real.hasDerivAt_log one_ne_zero)
    rw [add_comm, h.unique hdd]
    exact hd
  obtain ⟨V, hBV, -, hΨ, hΨo⟩ :=
    φ.exists_isSmoothEmbedding_globalFlow_toChart_symm hX hXc hXs hXφ hρ hθs hθρ hinj
  -- The compact set `K` of points of the closed ball sent at level at least `a`.
  have hFc : ContinuousOn F (closedBall 0 ρ) := by
    have h1 : ContinuousOn (fun c : EuclideanSpace ℝ {i // φ.weight i < 0} ↦
        φ.toChart.symm (φ.negativeExtend c.ofLp)) (closedBall 0 ρ) := by
      simp_rw [← negativeExtendL_apply]
      exact φ.toChart.continuousOn_symm.comp φ.negativeExtendL.continuous.continuousOn
        fun c hc ↦ by simpa using hρ c (mem_closedBall_zero_iff.1 hc)
    exact Φ.cont'.comp_continuousOn (hθs.continuous.continuousOn.prodMk h1)
  set K := closedBall (0 : EuclideanSpace ℝ {i // φ.weight i < 0}) ρ ∩ {c | a ≤ g (F c)}
  have hK : IsCompact K :=
    (isCompact_closedBall _ _).of_isClosed_subset
      (hFc.preimage_isClosed_of_isClosed isClosed_closedBall
        (isClosed_le continuous_const hg.continuous)) inter_subset_left
  have hKρ : K ⊆ ball 0 ρ := fun c hc ↦ by
    refine mem_ball_zero_iff.2 ((mem_closedBall_zero_iff.1 hc.1).lt_of_ne fun h ↦ ?_)
    have h1 : g (F c) = a' := hsph (mem_sphere_zero_iff_norm.2 h)
    have h2 : a ≤ g (F c) := hc.2
    rw [h1] at h2
    exact absurd h2 (not_le.2 ha')
  -- The cube coordinates.
  have hm : Module.finrank ℝ (EuclideanSpace ℝ {i // φ.weight i < 0}) =
      manifoldMorseIndex 𝓘(ℝ, E) g p := by
    rw [finrank_euclideanSpace, ← Module.finrank_fintype_fun_eq_card (R := ℝ),
      φ.finrank_negativeWeight_fun]
  have hk : Module.finrank ℝ φ.stableSubspace =
      Module.finrank ℝ E - manifoldMorseIndex 𝓘(ℝ, E) g p := by
    have := φ.finrank_stableSubspace_add_manifoldMorseIndex
    omega
  obtain ⟨χ, hχ, hχo, hχ0, hχc, hχs, hχK⟩ :=
    SymplecticGeometry.exists_cubeChart_of_isSmoothEmbedding hm hk hΨ hΨo hρ0 hBV hK hKρ
  -- The thickened map at `(c, 0)` is `F c`.
  have hΨF {S : Set (EuclideanSpace ℝ {i // φ.weight i < 0})} :
      (fun q : V ↦ Φ (θ q.val.1) (φ.toChart.symm (φ.negativeExtend q.val.1.ofLp + q.val.2))) ''
        (Subtype.val ⁻¹' (S ×ˢ {0})) ⊆ F '' S := by
    rintro _ ⟨⟨⟨c, y⟩, _⟩, ⟨hc, hy⟩, rfl⟩
    obtain rfl : y = 0 := hy
    exact ⟨c, hc, by simp [hF]⟩
  refine ⟨χ, hχ, hχo, ?_, fun x hx ↦ ?_, fun x hx ↦ ?_, fun x hx ↦ ?_⟩
  · rw [hχ0]
    dsimp only
    rw [Prod.fst_zero, Prod.snd_zero, ZeroMemClass.coe_zero, add_zero, WithLp.ofLp_zero, map_zero,
      φ.toChart_symm_zero]
    exact φ.globalFlow_self hX hXc hXφ _
  · obtain ⟨c, hc, hcx⟩ := hΨF (hχc hx)
    rw [← hcx]
    exact ⟨φ.mapsTo_globalFlow_closedBall_unstableSet hX hXc hXφ hρ θ (ball_subset_closedBall hc),
      ha₀'.trans_le (hball (ball_subset_closedBall hc))⟩
  · obtain ⟨c, hc, hcx⟩ := hΨF (hχs hx)
    rw [← hcx]
    simp only [mem_ofPred_eq]
    by_contra! h
    exact hc.2 ⟨ball_subset_closedBall hc.1, h⟩
  · obtain ⟨c, hc, hcx⟩ := hreach x hx.1 (ha'.trans_le hx.2)
    refine hχK ⟨⟨(c, 0), hBV ⟨ball_subset_closedBall hc, rfl⟩⟩,
      ⟨⟨ball_subset_closedBall hc, ?_⟩, rfl⟩, ?_⟩
    · rw [mem_ofPred_eq, hcx]
      exact hx.2
    · dsimp only
      rw [ZeroMemClass.coe_zero, add_zero]
      exact hcx

end MorseChart

end TauCeti

end
