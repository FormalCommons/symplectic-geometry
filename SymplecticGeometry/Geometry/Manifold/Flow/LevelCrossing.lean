/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Dynamics.Flow.LevelCrossing
public import TauCeti.Geometry.Manifold.Flow.HittingTime
public import TauCeti.Geometry.Manifold.Flow.Complete

/-!
# Smoothness of the level-crossing time of a complete flow

Let `v` be a complete `C^n` vector field (`1 ≤ n`) on a boundaryless manifold modelled on a
Banach space, and `Φ` its flow as a Mathlib `Flow` (such as `TauCeti.globalFlow v`; the results
take `flowOf v = ⇑Φ`, which `TauCeti.flowOf_eq_globalFlow` provides). Let `g : M → ℝ` decrease
strictly along the orbits through a neighbourhood of `x`, and suppose the orbit of `x` reaches the
level `{g = c}` at the time `T = Flow.levelCrossingTime Φ g c x`, at a point `Φ T x` where `g` is
`C^n` with `dg (v) ≠ 0`. Then near `x` the crossing time agrees with the hitting time
`TauCeti.flowHittingTime v g T x` of that level, which is `C^n` by the implicit function theorem.
Hence the crossing time, and the map `y ↦ Φ (Flow.levelCrossingTime Φ g c y) y` into the level,
are `C^n` near `x`.

No new implicit function argument is needed. The hitting time carries the points near `x` into the
level (`TauCeti.eventually_flowHittingTime`), and on an orbit along which `g` decreases strictly
the crossing time is the only time spent on the level (`Flow.eq_levelCrossingTime_iff`). Tau
Ceti's `TauCeti.contMDiffAt_flowHittingTime` and `TauCeti.contMDiffAt_flowOf_comp` then give the
smoothness.

## Main results

* `TauCeti.levelCrossingTime_eventuallyEq_flowHittingTime`: near a point whose orbit crosses the
  level transversally, the crossing time is the hitting time of the level.
* `TauCeti.contMDiffAt_levelCrossingTime`, `TauCeti.contMDiffOn_levelCrossingTime`: the crossing
  time is `C^n` where the crossing is transverse.
* `TauCeti.contMDiffAt_flow_levelCrossingTime`, `TauCeti.contMDiffOn_flow_levelCrossingTime`: so
  is the map that flows each point to the point where its orbit crosses the level.

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

/-- **The crossing time is a hitting time.** Let `v` be a complete `C¹` field with flow `Φ`, and
let `g` be strictly decreasing along the orbits through a neighbourhood of `x`. If the orbit of `x`
meets the level `{g = c}`, at the time `T`, at a point where `g` is `C¹` and `dg (v) ≠ 0`, then
near `x` the time at which orbits cross the level is the hitting time `flowHittingTime v g T x`. -/
theorem levelCrossingTime_eventuallyEq_flowHittingTime
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) (hcomplete : IsCompleteVectorField v)
    (hΦ : flowOf v = ⇑Φ) (hanti : ∀ᶠ y in 𝓝 x, StrictAnti fun t ↦ g (Φ t y))
    (hx : ∃ t, g (Φ t x) = c)
    (hg : ContMDiffAt I 𝓘(ℝ) 1 g (Φ (Flow.levelCrossingTime Φ g c x) x))
    (hgv : mvfderiv I g (Φ (Flow.levelCrossingTime Φ g c x) x)
      (v (Φ (Flow.levelCrossingTime Φ g c x) x)) ≠ 0) :
    Flow.levelCrossingTime Φ g c =ᶠ[𝓝 x]
      flowHittingTime v g (Flow.levelCrossingTime Φ g c x) x := by
  set T := Flow.levelCrossingTime Φ g c x
  have hc : g (Φ T x) = c := Flow.apply_flow_levelCrossingTime hx
  rw [← hΦ] at hg hgv
  filter_upwards [eventually_flowHittingTime hv (hcomplete.mem_flowDomain T x) hg hgv, hanti]
    with y hy hanti_y
  have hyc : g (Φ (flowHittingTime v g T x y) y) = c := by rw [← hc, ← hΦ, hy.2]
  exact ((Flow.eq_levelCrossingTime_iff hanti_y ⟨_, hyc⟩).2 hyc).symm

variable {n : ℕ∞} (hn : 1 ≤ n) [IsManifold I n M]
  (hv : CMDiff n (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) (hcomplete : IsCompleteVectorField v)
  (hΦ : flowOf v = ⇑Φ)
include hn hv hcomplete hΦ

/-- **The crossing time is `C^n` where the crossing is transverse.** Let `v` be a complete `C^n`
field (`1 ≤ n`) with flow `Φ`, and let `g` be strictly decreasing along the orbits through a
neighbourhood of `x`. If the orbit of `x` meets the level `{g = c}` at a point where `g` is `C^n`
and `dg (v) ≠ 0`, then the time `Flow.levelCrossingTime Φ g c` at which orbits cross the level
is `C^n` at `x`. -/
theorem contMDiffAt_levelCrossingTime (hanti : ∀ᶠ y in 𝓝 x, StrictAnti fun t ↦ g (Φ t y))
    (hx : ∃ t, g (Φ t x) = c)
    (hg : ContMDiffAt I 𝓘(ℝ) n g (Φ (Flow.levelCrossingTime Φ g c x) x))
    (hgv : mvfderiv I g (Φ (Flow.levelCrossingTime Φ g c x) x)
      (v (Φ (Flow.levelCrossingTime Φ g c x) x)) ≠ 0) :
    ContMDiffAt I 𝓘(ℝ) n (Flow.levelCrossingTime Φ g c) x := by
  have hn' : ((1 : ℕ∞) : WithTop ℕ∞) ≤ n := by exact_mod_cast hn
  have heq := levelCrossingTime_eventuallyEq_flowHittingTime (hv.of_le hn') hcomplete hΦ hanti hx
    (hg.of_le hn') hgv
  rw [← hΦ] at hg hgv
  exact (contMDiffAt_flowHittingTime hn hv (hcomplete.mem_flowDomain _ x) hg
    hgv).congr_of_eventuallyEq heq

/-- **The crossing point is `C^n` where the crossing is transverse.** Under the hypotheses of
`TauCeti.contMDiffAt_levelCrossingTime`, the map `y ↦ Φ (Flow.levelCrossingTime Φ g c y) y`, which
flows each point to the point where its orbit crosses the level `{g = c}`, is `C^n` at `x`. -/
theorem contMDiffAt_flow_levelCrossingTime (hanti : ∀ᶠ y in 𝓝 x, StrictAnti fun t ↦ g (Φ t y))
    (hx : ∃ t, g (Φ t x) = c)
    (hg : ContMDiffAt I 𝓘(ℝ) n g (Φ (Flow.levelCrossingTime Φ g c x) x))
    (hgv : mvfderiv I g (Φ (Flow.levelCrossingTime Φ g c x) x)
      (v (Φ (Flow.levelCrossingTime Φ g c x) x)) ≠ 0) :
    ContMDiffAt I I n (fun y ↦ Φ (Flow.levelCrossingTime Φ g c y) y) x := by
  have h := contMDiffAt_flowOf_comp hn hv
    (contMDiffAt_levelCrossingTime hn hv hcomplete hΦ hanti hx hg hgv) contMDiffAt_id
    (hcomplete.mem_flowDomain _ x)
  rwa [hΦ] at h

/-- **The crossing time is `C^n` on an open set of transverse crossings.** Let `v` be a complete
`C^n` field (`1 ≤ n`) with flow `Φ`, `g` a `C^n` function and `U` an open set. If `g` is strictly
decreasing along the orbit of every point of `U`, and that orbit meets the level `{g = c}` at a
point where `dg (v) ≠ 0`, then the crossing time `Flow.levelCrossingTime Φ g c` is `C^n` on `U`. -/
theorem contMDiffOn_levelCrossingTime (hg : ContMDiff I 𝓘(ℝ) n g) {U : Set M} (hU : IsOpen U)
    (hanti : ∀ x ∈ U, StrictAnti fun t ↦ g (Φ t x)) (hx : ∀ x ∈ U, ∃ t, g (Φ t x) = c)
    (hgv : ∀ x ∈ U, mvfderiv I g (Φ (Flow.levelCrossingTime Φ g c x) x)
      (v (Φ (Flow.levelCrossingTime Φ g c x) x)) ≠ 0) :
    ContMDiffOn I 𝓘(ℝ) n (Flow.levelCrossingTime Φ g c) U := fun x hxU ↦
  (contMDiffAt_levelCrossingTime hn hv hcomplete hΦ (eventually_of_mem (hU.mem_nhds hxU) hanti)
    (hx x hxU) hg.contMDiffAt (hgv x hxU)).contMDiffWithinAt

/-- **The crossing point is `C^n` on an open set of transverse crossings.** Under the hypotheses
of `TauCeti.contMDiffOn_levelCrossingTime`, the map `y ↦ Φ (Flow.levelCrossingTime Φ g c y) y`
onto the level `{g = c}` is `C^n` on `U`. -/
theorem contMDiffOn_flow_levelCrossingTime (hg : ContMDiff I 𝓘(ℝ) n g) {U : Set M}
    (hU : IsOpen U) (hanti : ∀ x ∈ U, StrictAnti fun t ↦ g (Φ t x))
    (hx : ∀ x ∈ U, ∃ t, g (Φ t x) = c)
    (hgv : ∀ x ∈ U, mvfderiv I g (Φ (Flow.levelCrossingTime Φ g c x) x)
      (v (Φ (Flow.levelCrossingTime Φ g c x) x)) ≠ 0) :
    ContMDiffOn I I n (fun y ↦ Φ (Flow.levelCrossingTime Φ g c y) y) U := fun x hxU ↦
  (contMDiffAt_flow_levelCrossingTime hn hv hcomplete hΦ
    (eventually_of_mem (hU.mem_nhds hxU) hanti) (hx x hxU) hg.contMDiffAt
    (hgv x hxU)).contMDiffWithinAt

end TauCeti
