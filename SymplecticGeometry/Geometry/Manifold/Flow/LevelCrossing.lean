/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Dynamics.Flow.LevelCrossing
public import TauCeti.Geometry.Manifold.Flow.HittingTime
public import TauCeti.Geometry.Manifold.Flow.Complete
import TauCeti.Geometry.Manifold.Flow.ReturnDerivative
import TauCeti.Geometry.Manifold.IntegralCurve.GlobalFlow
import SymplecticGeometry.Geometry.Manifold.IntegralCurve.Monotone

/-!
# Smoothness of the level-crossing time of a complete flow

Let `v` be a complete `C^n` vector field (`1 ≤ n`) on a boundaryless manifold modelled on a
Banach space, and `Φ` its flow as a Mathlib `Flow` (such as `TauCeti.globalFlow v`; the results
take `flowOf v = ⇑Φ`, which `TauCeti.flowOf_eq_globalFlow` provides). Let `g : M → ℝ`, and let
the orbits through a neighbourhood of `x` meet the level `{g = c}` at most once; suppose that the
orbit of `x` reaches the level at the time `T = Flow.levelCrossingTime Φ g c x`, at a point `Φ T x`
where `g` is `C^n` with `dg (v) ≠ 0`. Then near `x` the crossing time agrees with the hitting time
`TauCeti.flowHittingTime v g T x` of that level, which is `C^n` by the implicit function theorem.
Hence the crossing time, and the map `y ↦ Φ (Flow.levelCrossingTime Φ g c y) y` into the level,
are `C^n` near `x`.

No new implicit function argument is needed. The hitting time carries the points near `x` into the
level (`TauCeti.eventually_flowHittingTime`), and on an orbit that meets the level at most once the
crossing time is the only time spent on the level (`Flow.apply_flow_levelCrossingTime`). Tau
Ceti's `TauCeti.contMDiffAt_flowHittingTime` and `TauCeti.contMDiffAt_flowOf_comp` then give the
smoothness. In finite dimension, the same eventual equality identifies the map to the level near `x`
with Tau Ceti's transition `TauCeti.flowTransition v g T x`, so the kernel of its derivative at `x`
is the line through `v x`: it contains `v x` by `TauCeti.mfderiv_flowTransition_apply_eq_zero`,
and nothing else, by `TauCeti.mfderiv_flowTransition_apply` and the injectivity of the derivative
of the time-`T` map (`TauCeti.injective_mfderiv_flowOf`).

When the field crosses the level upwards (`0 < dg (v)` on it), each orbit meets the level at most
once (`IsMIntegralCurve.subsingleton_setOfPred_apply_eq_of_mvfderiv_pos`), and the points whose
orbits meet it form an open set: just before and just after its crossing an orbit lies on either
side of the level, so the nearby orbits do too, and they cross it in between by the intermediate
value theorem. For a `C^n` function `g`, the crossing time and the crossing point of such a level
are then `C^n` on that open set.

## Main results

* `TauCeti.levelCrossingTime_eventuallyEq_flowHittingTime`: near a point whose orbit crosses the
  level transversally, the crossing time is the hitting time of the level.
* `TauCeti.ker_mfderiv_flow_levelCrossingTime`: in finite dimension, the derivative of the map to
  the level has kernel the line through the field.
* `TauCeti.contMDiffAt_levelCrossingTime`, `TauCeti.contMDiffOn_levelCrossingTime`: the crossing
  time is `C^n` where the crossing is transverse.
* `TauCeti.contMDiffAt_flow_levelCrossingTime`, `TauCeti.contMDiffOn_flow_levelCrossingTime`: so
  is the map that flows each point to the point where its orbit crosses the level.
* `TauCeti.isOpen_setOf_exists_flow_apply_eq`: the points whose orbits meet a level crossed
  upwards form an open set.
* `TauCeti.contMDiffAt_levelCrossingTime_of_mvfderiv_pos`,
  `TauCeti.contMDiffOn_levelCrossingTime_of_mvfderiv_pos`,
  `TauCeti.contMDiffAt_flow_levelCrossingTime_of_mvfderiv_pos` and
  `TauCeti.contMDiffOn_flow_levelCrossingTime_of_mvfderiv_pos`: for a `C^n` function, the crossing
  time and the crossing point of a level crossed upwards are `C^n` at each point of that open
  set, and on it.

## References

* J. Palis, W. de Melo, *Geometric Theory of Dynamical Systems*, Springer 1982, Chapter 3, §1
  (transversal sections and the Poincaré map).
-/

public section

open Filter
open scoped ContDiff Manifold Topology

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [IsManifold I 1 M] [BoundarylessManifold I M]
  {v : (x : M) → TangentSpace I x} {Φ : Flow ℝ M} {g : M → ℝ} {c : ℝ} {x : M}

omit [CompleteSpace E] [T2Space M] [IsManifold I 1 M] [BoundarylessManifold I M] in
/-- **Orbits that cross an upward level form an open set.** Let the orbits of the flow `Φ` be
integral curves of `v`, and let `g` be continuous, and differentiable with `dg (v) > 0` at each
point of the level `{g = c}`. Then the set of points whose orbits meet that level is open. -/
theorem isOpen_setOf_exists_flow_apply_eq (hΦ : ∀ x, IsMIntegralCurve (fun t ↦ Φ t x) v)
    (hg : Continuous g)
    (hgv : ∀ x, g x = c → MDifferentiableAt I 𝓘(ℝ) g x ∧ 0 < mvfderiv I g x (v x)) :
    IsOpen {x | ∃ t, g (Φ t x) = c} := by
  refine isOpen_iff_mem_nhds.2 fun x ⟨t, ht⟩ ↦ ?_
  have hcont (s : ℝ) : Continuous fun y ↦ g (Φ s y) :=
    hg.comp (Φ.continuous continuous_const continuous_id)
  have horb (y : M) : Continuous fun s ↦ g (Φ s y) :=
    hg.comp (Φ.continuous continuous_id continuous_const)
  -- The orbit of `x` is below the level just before `t` and above it just after, and so are the
  -- orbits of the nearby points, which then cross the level in between.
  have hlo := (hΦ x).apply_lt_of_apply_le (f := g) (horb x) (fun _ ↦ hgv _) ht.le (sub_one_lt t)
  have hhi := (hΦ x).lt_apply_of_le_apply (f := g) (horb x) (fun _ ↦ hgv _) ht.ge (lt_add_one t)
  filter_upwards [(hcont (t - 1)).continuousAt.eventually (gt_mem_nhds hlo),
    (hcont (t + 1)).continuousAt.eventually (lt_mem_nhds hhi)] with y hy₁ hy₂
  obtain ⟨s, -, hs⟩ := intermediate_value_Icc (by linarith : t - 1 ≤ t + 1)
    (horb y).continuousOn ⟨hy₁.le, hy₂.le⟩
  exact ⟨s, hs⟩

/-- **The crossing time is a hitting time.** Let `v` be a complete `C¹` field with flow `Φ`, and
let the orbits through a neighbourhood of `x` meet the level `{g = c}` at most once. If the orbit
of `x` meets the level `{g = c}`, at the time `T`, at a point where `g` is `C¹` and `dg (v) ≠ 0`,
then near `x` the time at which orbits cross the level is the hitting time
`flowHittingTime v g T x`. -/
theorem levelCrossingTime_eventuallyEq_flowHittingTime
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) (hcomplete : IsCompleteVectorField v)
    (hΦ : flowOf v = ⇑Φ) (huniq : ∀ᶠ y in 𝓝 x, {t | g (Φ t y) = c}.Subsingleton)
    (hx : ∃ t, g (Φ t x) = c)
    (hg : ContMDiffAt I 𝓘(ℝ) 1 g (Φ (Flow.levelCrossingTime Φ g c x) x))
    (hgv : mvfderiv I g (Φ (Flow.levelCrossingTime Φ g c x) x)
      (v (Φ (Flow.levelCrossingTime Φ g c x) x)) ≠ 0) :
    Flow.levelCrossingTime Φ g c =ᶠ[𝓝 x]
      flowHittingTime v g (Flow.levelCrossingTime Φ g c x) x := by
  set T := Flow.levelCrossingTime Φ g c x
  have hc : g (Φ T x) = c := Flow.apply_flow_levelCrossingTime hx
  rw [← hΦ] at hg hgv
  filter_upwards [eventually_flowHittingTime hv (hcomplete.mem_flowDomain T x) hg hgv, huniq]
    with y hy huniq_y
  have hyc : g (Φ (flowHittingTime v g T x y) y) = c := by rw [← hc, ← hΦ, hy.2]
  exact huniq_y (Flow.apply_flow_levelCrossingTime ⟨_, hyc⟩) hyc

/-- **The kernel of the derivative of the map to the level.** Let `v` be a complete `C¹` field on a
finite-dimensional manifold, with flow `Φ`, and let the orbits through a neighbourhood of `x` meet
the level `{g = c}` at most once. If the orbit of `x` meets the level at a point where `g` is `C¹`
and `dg (v) ≠ 0`, then the derivative at `x` of `y ↦ Φ (Flow.levelCrossingTime Φ g c y) y` has
kernel the line spanned by `v x`. -/
theorem ker_mfderiv_flow_levelCrossingTime [FiniteDimensional ℝ E]
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) (hcomplete : IsCompleteVectorField v)
    (hΦ : flowOf v = ⇑Φ) (huniq : ∀ᶠ y in 𝓝 x, {t | g (Φ t y) = c}.Subsingleton)
    (hx : ∃ t, g (Φ t x) = c)
    (hg : ContMDiffAt I 𝓘(ℝ) 1 g (Φ (Flow.levelCrossingTime Φ g c x) x))
    (hgv : mvfderiv I g (Φ (Flow.levelCrossingTime Φ g c x) x)
      (v (Φ (Flow.levelCrossingTime Φ g c x) x)) ≠ 0) :
    (mfderiv I I (fun y ↦ Φ (Flow.levelCrossingTime Φ g c y) y) x).ker = ℝ ∙ v x := by
  set T := Flow.levelCrossingTime Φ g c x
  -- Near `x`, the map to the level is the transition to the section through `Φ T x`.
  have hF : (fun y ↦ Φ (Flow.levelCrossingTime Φ g c y) y) =ᶠ[𝓝 x] flowTransition v g T x := by
    filter_upwards [levelCrossingTime_eventuallyEq_flowHittingTime hv hcomplete hΦ huniq hx hg
      hgv] with y hy
    rw [flowTransition_apply, hy, hΦ]
  have hT := hcomplete.mem_flowDomain T x
  rw [← hΦ] at hg hgv
  -- `flowTransition v g T x x` and `Φ T x` are equal but not by definition, so the tangent spaces
  -- at them are identified by `rfl` below, as in `HasMFDerivAt.congr_of_eventuallyEq_abuse`.
  have hD (w : TangentSpace I x) :
      mfderiv I I (fun y ↦ Φ (Flow.levelCrossingTime Φ g c y) y) x w =
        mfderiv I I (flowTransition v g T x) x w := by
    rw [(HasMFDerivAt.congr_of_eventuallyEq_abuse
      (mdifferentiableAt_flowTransition hv hT hg hgv).hasMFDerivAt hF).mfderiv]
    rfl
  ext w
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, Submodule.mem_span_singleton, hD]
  constructor
  · -- The time-`T` map sends `w` and `-dτ(w) • v x` to the same vector, and is injective.
    intro h
    rw [mfderiv_flowTransition_apply hv hT hg hgv] at h
    refine ⟨-mvfderiv I (flowHittingTime v g T x) x w,
      injective_mfderiv_flowOf hv hcomplete T x ?_⟩
    rw [map_smul, mfderiv_flowOf_apply_self hv hT]
    exact (neg_smul _ _).trans (eq_neg_of_add_eq_zero_right h).symm
  · rintro ⟨r, rfl⟩
    rw [map_smul, mfderiv_flowTransition_apply_eq_zero hv hT hg hgv, smul_zero]
    rfl

variable {n : ℕ∞} (hn : 1 ≤ n) [IsManifold I n M]
  (hv : CMDiff n (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) (hcomplete : IsCompleteVectorField v)
  (hΦ : flowOf v = ⇑Φ)
include hn hv hcomplete hΦ

/-- **The crossing time is `C^n` where the crossing is transverse.** Let `v` be a complete `C^n`
field (`1 ≤ n`) with flow `Φ`, and let the orbits through a neighbourhood of `x` meet the
level `{g = c}` at most once. If the orbit of `x` meets the level at a point where `g` is `C^n`
and `dg (v) ≠ 0`, then the time `Flow.levelCrossingTime Φ g c` at which orbits cross the level
is `C^n` at `x`. -/
theorem contMDiffAt_levelCrossingTime
    (huniq : ∀ᶠ y in 𝓝 x, {t | g (Φ t y) = c}.Subsingleton)
    (hx : ∃ t, g (Φ t x) = c)
    (hg : ContMDiffAt I 𝓘(ℝ) n g (Φ (Flow.levelCrossingTime Φ g c x) x))
    (hgv : mvfderiv I g (Φ (Flow.levelCrossingTime Φ g c x) x)
      (v (Φ (Flow.levelCrossingTime Φ g c x) x)) ≠ 0) :
    ContMDiffAt I 𝓘(ℝ) n (Flow.levelCrossingTime Φ g c) x := by
  have hn' : ((1 : ℕ∞) : WithTop ℕ∞) ≤ n := by exact_mod_cast hn
  have heq := levelCrossingTime_eventuallyEq_flowHittingTime (hv.of_le hn') hcomplete hΦ huniq hx
    (hg.of_le hn') hgv
  rw [← hΦ] at hg hgv
  exact (contMDiffAt_flowHittingTime hn hv (hcomplete.mem_flowDomain _ x) hg
    hgv).congr_of_eventuallyEq heq

/-- **The crossing point is `C^n` where the crossing is transverse.** Under the hypotheses of
`TauCeti.contMDiffAt_levelCrossingTime`, the map `y ↦ Φ (Flow.levelCrossingTime Φ g c y) y`, which
flows each point to the point where its orbit crosses the level `{g = c}`, is `C^n` at `x`. -/
theorem contMDiffAt_flow_levelCrossingTime
    (huniq : ∀ᶠ y in 𝓝 x, {t | g (Φ t y) = c}.Subsingleton)
    (hx : ∃ t, g (Φ t x) = c)
    (hg : ContMDiffAt I 𝓘(ℝ) n g (Φ (Flow.levelCrossingTime Φ g c x) x))
    (hgv : mvfderiv I g (Φ (Flow.levelCrossingTime Φ g c x) x)
      (v (Φ (Flow.levelCrossingTime Φ g c x) x)) ≠ 0) :
    ContMDiffAt I I n (fun y ↦ Φ (Flow.levelCrossingTime Φ g c y) y) x := by
  have h := contMDiffAt_flowOf_comp hn hv
    (contMDiffAt_levelCrossingTime hn hv hcomplete hΦ huniq hx hg hgv) contMDiffAt_id
    (hcomplete.mem_flowDomain _ x)
  rwa [hΦ] at h

/-- **The crossing time is `C^n` on an open set of transverse crossings.** Let `v` be a complete
`C^n` field (`1 ≤ n`) with flow `Φ`, `g : M → ℝ` and `U` an open set. If the orbit of every point of
`U` meets the level `{g = c}` exactly once, at a point where `g` is `C^n` and `dg (v) ≠ 0`, then
the crossing time `Flow.levelCrossingTime Φ g c` is `C^n` on `U`. -/
theorem contMDiffOn_levelCrossingTime {U : Set M} (hU : IsOpen U)
    (huniq : ∀ x ∈ U, {t | g (Φ t x) = c}.Subsingleton) (hx : ∀ x ∈ U, ∃ t, g (Φ t x) = c)
    (hg : ∀ x ∈ U, ContMDiffAt I 𝓘(ℝ) n g (Φ (Flow.levelCrossingTime Φ g c x) x))
    (hgv : ∀ x ∈ U, mvfderiv I g (Φ (Flow.levelCrossingTime Φ g c x) x)
      (v (Φ (Flow.levelCrossingTime Φ g c x) x)) ≠ 0) :
    ContMDiffOn I 𝓘(ℝ) n (Flow.levelCrossingTime Φ g c) U := fun x hxU ↦
  (contMDiffAt_levelCrossingTime hn hv hcomplete hΦ (eventually_of_mem (hU.mem_nhds hxU) huniq)
    (hx x hxU) (hg x hxU) (hgv x hxU)).contMDiffWithinAt

/-- **The crossing point is `C^n` on an open set of transverse crossings.** Under the hypotheses
of `TauCeti.contMDiffOn_levelCrossingTime`, the map `y ↦ Φ (Flow.levelCrossingTime Φ g c y) y`
onto the level `{g = c}` is `C^n` on `U`. -/
theorem contMDiffOn_flow_levelCrossingTime {U : Set M} (hU : IsOpen U)
    (huniq : ∀ x ∈ U, {t | g (Φ t x) = c}.Subsingleton) (hx : ∀ x ∈ U, ∃ t, g (Φ t x) = c)
    (hg : ∀ x ∈ U, ContMDiffAt I 𝓘(ℝ) n g (Φ (Flow.levelCrossingTime Φ g c x) x))
    (hgv : ∀ x ∈ U, mvfderiv I g (Φ (Flow.levelCrossingTime Φ g c x) x)
      (v (Φ (Flow.levelCrossingTime Φ g c x) x)) ≠ 0) :
    ContMDiffOn I I n (fun y ↦ Φ (Flow.levelCrossingTime Φ g c y) y) U := fun x hxU ↦
  (contMDiffAt_flow_levelCrossingTime hn hv hcomplete hΦ
    (eventually_of_mem (hU.mem_nhds hxU) huniq) (hx x hxU) (hg x hxU)
    (hgv x hxU)).contMDiffWithinAt

/-- **The crossing time of an upward level is `C^n`.** Let `v` be a complete `C^n` field
(`1 ≤ n`) with flow `Φ`, and let `g` be `C^n` with `dg (v) > 0` at each point of the level
`{g = c}`. If the orbit of `x` meets the level, then the crossing time
`Flow.levelCrossingTime Φ g c` is `C^n` at `x`. -/
theorem contMDiffAt_levelCrossingTime_of_mvfderiv_pos (hg : ContMDiff I 𝓘(ℝ) n g)
    (hgv : ∀ y, g y = c → 0 < mvfderiv I g y (v y)) (hx : ∃ t, g (Φ t x) = c) :
    ContMDiffAt I 𝓘(ℝ) n (Flow.levelCrossingTime Φ g c) x := by
  have hn' : ((1 : ℕ∞) : WithTop ℕ∞) ≤ n := by exact_mod_cast hn
  have hcurve (y : M) : IsMIntegralCurve (fun t ↦ Φ t y) v := by
    have h := isMIntegralCurve_globalFlow (hv.of_le hn') hcomplete y
    rwa [← flowOf_eq_globalFlow (hv.of_le hn') hcomplete, hΦ] at h
  have hgv' (y : M) (hy : g y = c) : MDifferentiableAt I 𝓘(ℝ) g y ∧ 0 < mvfderiv I g y (v y) :=
    ⟨(hg y).mdifferentiableAt (zero_lt_one.trans_le hn').ne', hgv y hy⟩
  exact contMDiffAt_levelCrossingTime hn hv hcomplete hΦ
    (eventually_of_mem ((isOpen_setOf_exists_flow_apply_eq hcurve hg.continuous hgv').mem_nhds hx)
      fun y _ ↦ (hcurve y).subsingleton_setOfPred_apply_eq_of_mvfderiv_pos (f := g)
        (hg.continuous.comp (hcurve y).continuous) fun _ ↦ hgv' _)
    hx (hg _) (hgv _ (Flow.apply_flow_levelCrossingTime hx)).ne'

/-- **The crossing time of an upward level is `C^n` where the level is met.** Under the
hypotheses of `TauCeti.contMDiffAt_levelCrossingTime_of_mvfderiv_pos`, the crossing time
`Flow.levelCrossingTime Φ g c` is `C^n` on the set of points whose orbits meet the level
`{g = c}`, which is open by `TauCeti.isOpen_setOf_exists_flow_apply_eq`. -/
theorem contMDiffOn_levelCrossingTime_of_mvfderiv_pos (hg : ContMDiff I 𝓘(ℝ) n g)
    (hgv : ∀ y, g y = c → 0 < mvfderiv I g y (v y)) :
    ContMDiffOn I 𝓘(ℝ) n (Flow.levelCrossingTime Φ g c) {x | ∃ t, g (Φ t x) = c} := fun _ hx ↦
  (contMDiffAt_levelCrossingTime_of_mvfderiv_pos hn hv hcomplete hΦ hg hgv hx).contMDiffWithinAt

/-- **The crossing point of an upward level is `C^n`.** Under the hypotheses of
`TauCeti.contMDiffAt_levelCrossingTime_of_mvfderiv_pos`, the map
`y ↦ Φ (Flow.levelCrossingTime Φ g c y) y`, which follows each orbit to the level `{g = c}`, is
`C^n` at `x`. -/
theorem contMDiffAt_flow_levelCrossingTime_of_mvfderiv_pos (hg : ContMDiff I 𝓘(ℝ) n g)
    (hgv : ∀ y, g y = c → 0 < mvfderiv I g y (v y)) (hx : ∃ t, g (Φ t x) = c) :
    ContMDiffAt I I n (fun y ↦ Φ (Flow.levelCrossingTime Φ g c y) y) x := by
  have h := contMDiffAt_flowOf_comp hn hv
    (contMDiffAt_levelCrossingTime_of_mvfderiv_pos hn hv hcomplete hΦ hg hgv hx) contMDiffAt_id
    (hcomplete.mem_flowDomain _ x)
  rwa [hΦ] at h

/-- **The crossing point of an upward level is `C^n` where the level is met.** Under the
hypotheses of `TauCeti.contMDiffAt_levelCrossingTime_of_mvfderiv_pos`, the map
`y ↦ Φ (Flow.levelCrossingTime Φ g c y) y`, which follows each orbit to the level `{g = c}`, is
`C^n` on the set of points whose orbits meet the level. -/
theorem contMDiffOn_flow_levelCrossingTime_of_mvfderiv_pos (hg : ContMDiff I 𝓘(ℝ) n g)
    (hgv : ∀ y, g y = c → 0 < mvfderiv I g y (v y)) :
    ContMDiffOn I I n (fun y ↦ Φ (Flow.levelCrossingTime Φ g c y) y)
      {x | ∃ t, g (Φ t x) = c} := fun _ hx ↦
  (contMDiffAt_flow_levelCrossingTime_of_mvfderiv_pos hn hv hcomplete hΦ hg hgv
    hx).contMDiffWithinAt

end TauCeti
