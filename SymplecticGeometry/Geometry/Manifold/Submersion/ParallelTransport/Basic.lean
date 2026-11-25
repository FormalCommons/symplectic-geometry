/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Submersion.HorizontalLiftField
public import TauCeti.Geometry.Manifold.Distribution.Horizontal
public import TauCeti.Geometry.Manifold.MFDeriv.Curve
import Mathlib.Geometry.Manifold.Instances.Icc
import SymplecticGeometry.Geometry.Manifold.Distribution.Horizontal
import SymplecticGeometry.Geometry.Manifold.Flow.TimeDependent
import TauCeti.Geometry.Manifold.IntegralCurve.Interval
import TauCeti.Geometry.Manifold.IsManifold.Basic

/-!
# Horizontal lifts of curves

Let `D` be an Ehresmann connection on a map `f : P → B` (Tau Ceti's
`TauCeti.IsEhresmannConnection`). A curve `c : ℝ → P` is horizontal when its velocities lie in
`D` (`TauCeti.IsHorizontalMap`). The velocity of a differentiable horizontal curve is then the
horizontal lift of the velocity of its projection `f ∘ c`
(`TauCeti.IsEhresmannConnection.curveVelocity_eq_horizontalLift_iff`), so a horizontal curve
over a given curve `γ` of `B` is determined by a first-order equation, and its value at one time
determines it.

This file proves that uniqueness for a `C¹` connection on a `C²` map `f`, and curves over a `C²`
curve `γ` of the base, on a closed interval of times and on all of `ℝ`. Near a time `t`, read the
velocity of `γ` in the trivialization of the tangent bundle of `B` at `γ t`, and spread it to the
field on `B` that has that reading at every point of the trivialization's base set. Its
horizontal lift is a time-dependent field on `P`, jointly `C¹` in time and point
(`TauCeti.IsEhresmannConnection.contMDiffAt_horizontalLift`), and both curves solve it near `t`.
Lifted through their clocks
(`TauCeti.hasMFDerivWithinAt_prodMk_timeDependentSuspensionField`), they are integral curves of
its suspension on `ℝ × P`, which is `C¹` at that point
(`TauCeti.contMDiffAt_timeDependentSuspensionField`). Tau Ceti's local uniqueness of integral
curves on a preconnected set of times,
`IsMIntegralCurveOn.eventuallyEq_of_isPreconnected`, which allows `t` to be an end of the
interval, makes them agree near `t`. The set of times where the curves agree is then open and
closed in the interval, which is connected. The last step follows the proof of Tau Ceti's
`IsMIntegralCurveOn.eqOn_of_isPreconnected`, with a field that changes from time to time. The
description of the velocity of a horizontal curve is the analogue for Ehresmann connections of
Tau Ceti's `TauCeti.IsRiemannianSubmersion.curveVelocity_eq_horizontalLift_iff`.

The smoothness asked of `γ` is what makes the field `C¹` in time: the velocity of the projection
of a merely differentiable curve need not even be continuous.

It then proves that lifts exist over a closed interval of times that `γ` maps into the base set
of one trivialization `e` of the tangent bundle of `B`, for a proper map `f`. A time-dependent
field `V` on `B`, jointly `C^n` and zero outside a compact set `K`, has the velocity of `γ` as its
value along `γ` on the interval
(`Bundle.Trivialization.exists_timeDependentField_eq_curveVelocity`). Its horizontal lift vanishes
outside the compact set `f ⁻¹' K`, so its suspension is complete
(`TauCeti.isCompleteVectorField_timeDependentSuspensionField`), and the lift through `x` is the
trajectory of the time-dependent flow through `x`. The projection of that trajectory and `γ` solve
the same equation on `B` on the interval, so they agree there
(`TauCeti.timeDependentFlowOf_eq_of_hasMFDerivWithinAt`).

Finally it glues these local lifts into a lift over all of `ℝ`
(`TauCeti.IsEhresmannConnection.exists_isHorizontalMap_lift`). The times `t` for which some lift
through `x` at `s` lies over `γ` on `Set.uIcc s t` form a set that is open and closed in `ℝ`:
near any time, a lift over one trivialization, started at a nearby time of a lift already found,
agrees with it on their common interval by uniqueness, and following the old lift up to a time
inside that interval and the new one after it gives a longer lift. Lifts over the intervals
`Set.Icc (s - k) (s + k)` then agree where both are defined, and near each time the global lift
is one of them, so it is as smooth as they are and horizontal (horizontality is local:
`TauCeti.IsHorizontalMap.of_forall_eventuallyEq`).

## Main results

* `TauCeti.IsEhresmannConnection.curveVelocity_eq_horizontalLift_iff`: a differentiable curve has
  as velocity the horizontal lift of the velocity of its projection exactly where its velocity is
  horizontal.
* `TauCeti.IsEhresmannConnection.eqOn_of_isHorizontalMap`: two differentiable horizontal curves
  over the same `C²` curve of `B` on `Set.Icc a b` that agree at one time of it agree on it.
* `TauCeti.IsEhresmannConnection.eq_of_isHorizontalMap`: the same on all of `ℝ`.
* `TauCeti.IsEhresmannConnection.exists_isHorizontalMap_lift_of_mapsTo_baseSet`: for a proper map,
  a curve `γ` of `B` has a horizontal lift through any point over `γ s`, on a closed interval
  containing `s` that `γ` maps into the base set of one trivialization of the tangent bundle.
* `TauCeti.IsEhresmannConnection.exists_isHorizontalMap_lift`: for a proper map, every `C^(n+1)`
  curve of `B` has a `C^n` horizontal lift over all of `ℝ` through any point over one of its
  values.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §6.3.
* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer
  (1993), §9.
-/

public section

noncomputable section

open Function Bundle Set Filter TauCeti.Manifold
open scoped ContDiff Manifold Topology

namespace TauCeti

namespace IsEhresmannConnection

section Velocity

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {P : Type*} [TopologicalSpace P] [ChartedSpace H P] [IsManifold I 1 P]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners 𝕜 F G}
  {B : Type*} [TopologicalSpace B] [ChartedSpace G B]
  {n : ℕ∞ω} {f : P → B} {D : Π x : P, Submodule 𝕜 (TangentSpace I x)}
  (hD : IsEhresmannConnection I J n f D)

/-- A curve `c`, differentiable at `u`, has at `u` the horizontal lift at `c u` of the velocity of
its projection `f ∘ c` as its velocity if and only if its velocity at `u` is horizontal. -/
theorem curveVelocity_eq_horizontalLift_iff {c : 𝕜 → P} {u : 𝕜}
    (hc : MDifferentiableAt 𝓘(𝕜, 𝕜) I c u) :
    curveVelocity I c u = hD.horizontalLift (c u) (curveVelocity J (f ∘ c) u) ↔
      curveVelocity I c u ∈ D (c u) := by
  refine ⟨fun h ↦ h ▸ (hD.horizontalLift _ _).property, fun hmem ↦ ?_⟩
  refine congrArg Subtype.val ((hD.eq_horizontalLift_iff (w := ⟨_, hmem⟩)).2 ?_)
  have hmap := curveVelocityWithin_map (f := f) (hD.mdifferentiable (c u))
    uniqueDiffWithinAt_univ hc.mdifferentiableWithinAt
  rw [curveVelocityWithin_univ, curveVelocityWithin_univ] at hmap
  exact hmap.symm

end Velocity

section Uniqueness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {P : Type*} [TopologicalSpace P] [ChartedSpace H P] [IsManifold I 1 P]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {B : Type*} [TopologicalSpace B] [ChartedSpace G B] [IsManifold J 1 B]
  {n : ℕ∞ω} {f : P → B} {D : Π x : P, Submodule ℝ (TangentSpace I x)}
  (hD : IsEhresmannConnection I J n f D)

/-- The local step of `TauCeti.IsEhresmannConnection.eqOn_of_isHorizontalMap`: the two curves
agree near a time of `Set.Icc a b` at which they agree. -/
private theorem eventuallyEq_of_isHorizontalMap
    (hD : IsEhresmannConnection I J 1 f D) (hf : ContMDiff I J 2 f) {γ : ℝ → B}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) J 2 γ) {c₁ c₂ : ℝ → P}
    (hc₁ : MDifferentiable 𝓘(ℝ, ℝ) I c₁) (hc₂ : MDifferentiable 𝓘(ℝ, ℝ) I c₂)
    (hh₁ : IsHorizontalMap 𝓘(ℝ, ℝ) D c₁) (hh₂ : IsHorizontalMap 𝓘(ℝ, ℝ) D c₂) {a b : ℝ}
    (hab : a < b) (hγ₁ : EqOn (f ∘ c₁) γ (Icc a b)) (hγ₂ : EqOn (f ∘ c₂) γ (Icc a b))
    {t : ℝ} (ht : t ∈ Icc a b) (h : c₁ t = c₂ t) : c₁ =ᶠ[𝓝[Icc a b] t] c₂ := by
  let eB := trivializationAt F (TangentSpace J) (γ t)
  have hbt : γ t ∈ eB.baseSet := FiberBundle.mem_baseSet_trivializationAt' _
  -- The velocity of `γ` read in `eB`, and the lift of the field with that reading.
  let v : ℝ → F := fun u ↦ (eB ⟨γ u, curveVelocity J γ u⟩).2
  let X : ℝ → Π y : P, TangentSpace I y := fun u y ↦ hD.horizontalLift y (eB.symm (f y) (v u))
  have hv : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, F) 1 v t := by
    have hlift := hγ.contMDiffAt.contMDiffAt_curveVelocityLift (m := 1) (t := t) (by norm_num)
    rw [show curveVelocityLift J γ = fun u ↦ ⟨γ u, curveVelocity J γ u⟩ from
      funext (curveVelocityLift_apply γ)] at hlift
    exact (contMDiffAt_totalSpace_iff.1 hlift).2
  have hft : f (c₁ t) = γ t := hγ₁ ht
  have hbx : f (c₁ t) ∈ eB.baseSet := hft ▸ hbt
  have hw : ContMDiffAt (𝓘(ℝ, ℝ).prod I) J.tangent 1
      (fun p : ℝ × P ↦ (⟨f p.2, eB.symm (f p.2) (v p.1)⟩ : TangentBundle J B)) (t, c₁ t) := by
    have hfs : ContMDiffAt (𝓘(ℝ, ℝ).prod I) J 1 (fun p : ℝ × P ↦ f p.2) (t, c₁ t) :=
      ((hf (c₁ t)).of_le one_le_two).comp (t, c₁ t) contMDiffAt_snd
    refine contMDiffAt_totalSpace_iff.2 ⟨hfs, ?_⟩
    dsimp only
    rw [hft]
    refine (hv.comp _ contMDiffAt_fst).congr_of_eventuallyEq ?_
    filter_upwards [(hf.continuous.continuousAt.comp continuousAt_snd).preimage_mem_nhds
      (eB.open_baseSet.mem_nhds hbx)] with p hp
    rw [Function.comp_apply]
    rw [eB.apply_mk_symm (b := f p.2) hp]
  have hX : ContMDiffAt (𝓘(ℝ, ℝ).prod I) I.tangent 1
      (fun p : ℝ × P ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I P)) (t, c₁ t) :=
    hD.contMDiffAt_horizontalLift (g := Prod.snd) (fun _ ↦ rfl) ((hf (c₁ t)).of_le (by norm_num))
      contMDiffAt_snd hw
  -- The suspension of `X` is `C¹` at `(t, c₁ t)`.
  have hW := contMDiffAt_timeDependentSuspensionField hX
  -- Near `t`, `γ` stays in the base set of `eB`.
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1
    (hγ.continuous.continuousAt.preimage_mem_nhds (eB.open_baseSet.mem_nhds hbt))
  have hS : IsPreconnected (Icc a b ∩ Metric.ball t ε) :=
    ((convex_Icc a b).inter (convex_ball t ε)).isPreconnected
  have htS : t ∈ Icc a b ∩ Metric.ball t ε := ⟨ht, Metric.mem_ball_self hε⟩
  -- Both curves, lifted through their clocks, are integral curves of the suspension there.
  have hcurve {c : ℝ → P} (hc : MDifferentiable 𝓘(ℝ, ℝ) I c)
      (hh : IsHorizontalMap 𝓘(ℝ, ℝ) D c) (hγc : EqOn (f ∘ c) γ (Icc a b)) :
      IsMIntegralCurveOn (fun r ↦ (r, c r)) (timeDependentSuspensionField X)
        (Icc a b ∩ Metric.ball t ε) := by
    intro u hu
    have hfc : f (c u) = γ u := hγc hu.1
    -- The projection `f ∘ c` has the velocity of `γ`, since they agree on `Set.Icc a b`.
    have hcv : curveVelocity J (f ∘ c) u = curveVelocity J γ u := by
      have hu' := (uniqueDiffOn_Icc hab) u hu.1
      have h₁ := (hasMFDerivAt_curveVelocity
        ((hD.mdifferentiable (c u)).comp u (hc u))).hasMFDerivWithinAt (s := Icc a b)
      have h₂ := (hasMFDerivAt_curveVelocity ((hγ.mdifferentiable (by norm_num)) u)
        ).hasMFDerivWithinAt (s := Icc a b) |>.congr_of_eventuallyEq
          (eventuallyEq_nhdsWithin_of_eqOn hγc) hfc
      rw [← curveVelocityWithin_eq_of_hasMFDerivWithinAt h₁ hu']
      exact curveVelocityWithin_eq_of_hasMFDerivWithinAt h₂ hu'
    have hvel : curveVelocity I c u = X u (c u) := by
      rw [(hD.curveVelocity_eq_horizontalLift_iff (hc u)).2
        (curveVelocity_apply (I := I) (γ := c) (t := u) ▸ hh.mfderiv_mem u 1)]
      refine congrArg (fun w ↦ (hD.horizontalLift (c u) w : TangentSpace I (c u))) ?_
      have hsymm : eB.symm (γ u) (v u) = curveVelocity J γ u :=
        eB.symm_apply_apply_mk (hball hu.2) _
      rw [hcv, ← hsymm, hfc]
    have hcu : HasMFDerivWithinAt 𝓘(ℝ, ℝ) I c (Icc a b ∩ Metric.ball t ε) u
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X u (c u))) := by
      rw [← hvel]
      exact (hasMFDerivAt_curveVelocity (hc u)).hasMFDerivWithinAt
    exact hasMFDerivWithinAt_prodMk_timeDependentSuspensionField hcu
  have heq := (hcurve hc₁ hh₁ hγ₁).eventuallyEq_of_isPreconnected (hcurve hc₂ hh₂ hγ₂) hS htS
    hW (by rw [h])
  rw [← nhdsWithin_inter_of_mem'
    (mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds t hε))]
  exact heq.mono fun r hr ↦ congrArg Prod.snd hr

include hD in
/-- **Uniqueness of horizontal lifts on an interval.** Let `D` be a `C^n` Ehresmann connection,
`1 ≤ n`, on a `C²` map `f : P → B` from a Hausdorff manifold, and `γ` a `C²` curve
in `B`. Two differentiable horizontal curves `c₁ c₂ : ℝ → P` that lie over `γ` on `Set.Icc a b`
and agree at one time of `Set.Icc a b` agree on all of it. -/
theorem eqOn_of_isHorizontalMap [T2Space P] (hn : 1 ≤ n)
    (hf : ContMDiff I J 2 f) {γ : ℝ → B} (hγ : ContMDiff 𝓘(ℝ, ℝ) J 2 γ) {c₁ c₂ : ℝ → P}
    (hc₁ : MDifferentiable 𝓘(ℝ, ℝ) I c₁) (hc₂ : MDifferentiable 𝓘(ℝ, ℝ) I c₂)
    (hh₁ : IsHorizontalMap 𝓘(ℝ, ℝ) D c₁) (hh₂ : IsHorizontalMap 𝓘(ℝ, ℝ) D c₂) {a b t₀ : ℝ}
    (hγ₁ : EqOn (f ∘ c₁) γ (Icc a b)) (hγ₂ : EqOn (f ∘ c₂) γ (Icc a b)) (ht₀ : t₀ ∈ Icc a b)
    (h : c₁ t₀ = c₂ t₀) : EqOn c₁ c₂ (Icc a b) := by
  have hD₁ : IsEhresmannConnection I J 1 f D := hD.of_le hn
  rcases lt_or_ge a b with hab | hba
  · let : PreconnectedSpace (Icc a b) :=
      isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
    have hcont {c : ℝ → P} (hc : MDifferentiable 𝓘(ℝ, ℝ) I c) :
        Continuous fun u : Icc a b ↦ c u :=
      hc.continuous.comp continuous_subtypeVal
    have hopen : IsOpen {u : Icc a b | c₁ u = c₂ u} := by
      rw [isOpen_iff_mem_nhds]
      intro u hu
      rw [nhds_subtype_eq_comap_nhdsWithin]
      exact Filter.preimage_mem_comap (eventuallyEq_of_isHorizontalMap hD₁ hf hγ hc₁ hc₂ hh₁
        hh₂ hab hγ₁ hγ₂ u.property hu)
    have hall := IsClopen.eq_univ (s := {u : Icc a b | c₁ u = c₂ u})
      ⟨isClosed_eq (hcont hc₁) (hcont hc₂), hopen⟩ ⟨⟨t₀, ht₀⟩, h⟩
    exact fun u hu ↦ Set.eq_univ_iff_forall.mp hall ⟨u, hu⟩
  · -- If `b ≤ a`, then `Set.Icc a b` has at most the point `t₀`.
    intro u hu
    obtain rfl : u = t₀ :=
      le_antisymm (hu.2.trans (hba.trans ht₀.1)) (ht₀.2.trans (hba.trans hu.1))
    exact h

include hD in
/-- **Uniqueness of horizontal lifts.** Let `D` be a `C^n` Ehresmann connection, `1 ≤ n`, on a
`C²` map `f : P → B` from a Hausdorff manifold, and `γ` a `C²` curve in `B`. Two
differentiable horizontal curves `c₁ c₂ : ℝ → P` over `γ` that agree at one time are equal. -/
theorem eq_of_isHorizontalMap [T2Space P] (hn : 1 ≤ n)
    (hf : ContMDiff I J 2 f) {γ : ℝ → B} (hγ : ContMDiff 𝓘(ℝ, ℝ) J 2 γ) {c₁ c₂ : ℝ → P}
    (hc₁ : MDifferentiable 𝓘(ℝ, ℝ) I c₁) (hc₂ : MDifferentiable 𝓘(ℝ, ℝ) I c₂)
    (hh₁ : IsHorizontalMap 𝓘(ℝ, ℝ) D c₁) (hh₂ : IsHorizontalMap 𝓘(ℝ, ℝ) D c₂)
    (hγ₁ : f ∘ c₁ = γ) (hγ₂ : f ∘ c₂ = γ) {t₀ : ℝ} (h : c₁ t₀ = c₂ t₀) : c₁ = c₂ :=
  funext fun u ↦ hD.eqOn_of_isHorizontalMap hn hf hγ hc₁ hc₂ hh₁ hh₂
    (a := min t₀ u) (b := max t₀ u) (fun r _ ↦ congrFun hγ₁ r) (fun r _ ↦ congrFun hγ₂ r)
    ⟨min_le_left _ _, le_max_left _ _⟩ h ⟨min_le_right _ _, le_max_right _ _⟩

end Uniqueness

section Existence

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

include hD in
/-- **Horizontal lifts of a curve over an interval in one trivialization.** Let `D` be a `C^n`
Ehresmann connection, `1 ≤ n`, on a proper `C^(n+1)` map `f : P → B` of finite-dimensional
boundaryless Hausdorff manifolds, and `γ` a `C^(n+1)` curve in `B` that maps `Set.Icc a b` into
the base set of a trivialization `e` of the tangent bundle of `B`. For every `s ∈ Set.Icc a b` and
every `x` with `f x = γ s`, there is a `C^n` horizontal curve `c` with `c s = x` that lies over `γ`
on `Set.Icc a b`. -/
theorem exists_isHorizontalMap_lift_of_mapsTo_baseSet (hn : 1 ≤ n)
    (hf : ContMDiff I J (n + 1) f) (hfp : IsProperMap f) {γ : ℝ → B}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) J (n + 1) γ) {a b s : ℝ} (hs : s ∈ Icc a b)
    (e : Trivialization F (π F (TangentSpace J))) [MemTrivializationAtlas e]
    (hγe : MapsTo γ (Icc a b) e.baseSet) {x : P} (hx : f x = γ s) :
    ∃ c : ℝ → P, ContMDiff 𝓘(ℝ, ℝ) I n c ∧ IsHorizontalMap 𝓘(ℝ, ℝ) D c ∧
      EqOn (f ∘ c) γ (Icc a b) ∧ c s = x := by
  have hn' : (1 : ℕ∞ω) ≤ n := by exact_mod_cast hn
  have : IsManifold I n P := .of_le (n := ∞) (by exact_mod_cast le_top)
  -- A compactly supported field `V` on `B` through the velocities of `γ`, and its lift `X`.
  obtain ⟨V, K, hK, hV, hV0, hVγ⟩ := e.exists_timeDependentField_eq_curveVelocity hγ hγe
  let X : ℝ → Π y : P, TangentSpace I y := fun u ↦ hD.horizontalLiftField (V u)
  have hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent n
      (fun p : ℝ × P ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I P)) :=
    hD.contMDiff_horizontalLiftField_timeDependent hf hV
  have hX1 := hX.of_le hn'
  -- Both suspensions are complete: `X` vanishes outside `f ⁻¹' K`, compact since `f` is proper.
  have hXc : IsCompleteVectorField (timeDependentSuspensionField X) :=
    isCompleteVectorField_timeDependentSuspensionField hX1 (hfp.isCompact_preimage hK)
      fun u y hy ↦ hD.horizontalLiftField_eq_zero _ (hV0 u (f y) hy)
  have hVc : IsCompleteVectorField (timeDependentSuspensionField V) :=
    isCompleteVectorField_timeDependentSuspensionField (hV.of_le hn') hK hV0
  -- The lift is the trajectory of `X` through `x` at time `s`.
  let c : ℝ → P := fun u ↦ timeDependentFlowOf X s u x
  have hcd (u : ℝ) : HasMFDerivAt 𝓘(ℝ, ℝ) I c u ((1 : ℝ →L[ℝ] ℝ).smulRight (X u (c u))) :=
    hasMFDerivAt_timeDependentFlowOf hX1 ((timeDependentFlowDomain_eq_univ hXc).symm ▸ mem_univ _)
  -- Its projection is a trajectory of `V`.
  have hfc (u : ℝ) : HasMFDerivAt 𝓘(ℝ, ℝ) J (f ∘ c) u
      ((1 : ℝ →L[ℝ] ℝ).smulRight (V u ((f ∘ c) u))) := by
    refine ((hD.mdifferentiable (c u)).hasMFDerivAt.comp u (hcd u)).congr_mfderiv ?_
    refine ContinuousLinearMap.ext fun (r : ℝ) ↦ ?_
    exact ((mfderiv I J f (c u)).map_smul r (X u (c u))).trans
      (congrArg (r • ·) (hD.mfderiv_horizontalLiftField (V u) (c u)))
  refine ⟨c, ?_, ?_, fun u hu ↦ ?_, timeDependentFlowOf_self X s x⟩
  · exact (contMDiff_timeDependentFlowOf hXc hn hX).comp
      ((contMDiff_const.prodMk contMDiff_id).prodMk contMDiff_const)
  · refine isHorizontalMap_iff.2 fun u r ↦ ?_
    rw [(hcd u).mfderiv]
    exact (D (c u)).smul_mem r (hD.horizontalLiftField_mem (V u) (c u))
  · -- On `Set.Icc a b`, `γ` is a trajectory of `V` too, through `f x` at time `s`.
    have hγS (t : ℝ) (ht : t ∈ Icc a b) : HasMFDerivWithinAt 𝓘(ℝ, ℝ) J γ (Icc a b) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (V t (γ t))) := by
      rw [hVγ t ht]
      exact (hasMFDerivAt_curveVelocity ((hγ.mdifferentiable (by simp)) t)).hasMFDerivWithinAt
    have h₁ := timeDependentFlowOf_eq_of_hasMFDerivWithinAt (hV.of_le hn') hVc
      isPreconnected_Icc hγS hs hu
    have h₂ := timeDependentFlowOf_eq_of_hasMFDerivWithinAt (hV.of_le hn') hVc
      isPreconnected_Icc (fun t _ ↦ (hfc t).hasMFDerivWithinAt) hs hu
    rw [← h₁, ← h₂]
    simp [c, timeDependentFlowOf_self, hx]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ P] [I.Boundaryless] [T2Space P] in
/-- The step of `TauCeti.IsEhresmannConnection.exists_isHorizontalMap_lift` that glues two curves:
the curve that follows `c₁` up to the time `m` and `c₂` after it is `C^k` and horizontal, if `c₁`
and `c₂` are and agree near `m`. -/
private theorem contMDiff_isHorizontalMap_piecewise {k : ℕ∞ω} {c₁ c₂ : ℝ → P}
    (hc₁ : ContMDiff 𝓘(ℝ, ℝ) I k c₁) (hc₂ : ContMDiff 𝓘(ℝ, ℝ) I k c₂)
    (hh₁ : IsHorizontalMap 𝓘(ℝ, ℝ) D c₁) (hh₂ : IsHorizontalMap 𝓘(ℝ, ℝ) D c₂) {m : ℝ}
    (hm : c₁ =ᶠ[𝓝 m] c₂) :
    ContMDiff 𝓘(ℝ, ℝ) I k (fun u ↦ if u ≤ m then c₁ u else c₂ u) ∧
      IsHorizontalMap 𝓘(ℝ, ℝ) D (fun u ↦ if u ≤ m then c₁ u else c₂ u) := by
  have hloc (u : ℝ) : (fun u ↦ if u ≤ m then c₁ u else c₂ u) =ᶠ[𝓝 u] c₁ ∨
      (fun u ↦ if u ≤ m then c₁ u else c₂ u) =ᶠ[𝓝 u] c₂ := by
    rcases lt_trichotomy u m with hu | rfl | hu
    · refine .inl ?_
      filter_upwards [Iio_mem_nhds hu] with v hv
      simp [le_of_lt hv]
    · refine .inr ?_
      filter_upwards [hm] with v hv
      split_ifs
      exacts [hv, rfl]
    · refine .inr ?_
      filter_upwards [Ioi_mem_nhds hu] with v hv
      simp [not_le.2 (mem_Ioi.1 hv)]
  refine ⟨fun u ↦ ?_, IsHorizontalMap.of_forall_eventuallyEq fun u ↦ ?_⟩
  · rcases hloc u with h | h
    · exact (hc₁ u).congr_of_eventuallyEq h
    · exact (hc₂ u).congr_of_eventuallyEq h
  · rcases hloc u with h | h
    · exact ⟨c₁, hh₁, h⟩
    · exact ⟨c₂, hh₂, h⟩

include hD in
/-- The first step of `TauCeti.IsEhresmannConnection.exists_isHorizontalMap_lift`: for every time
`t`, a lift through `x` at time `s` over `Set.uIcc s t`. The times `t` with such a lift form an
open and closed set: near each time, a lift over one trivialization continues any lift that
reaches that neighbourhood. -/
private theorem exists_isHorizontalMap_lift_uIcc (hn : 1 ≤ n)
    (hf : ContMDiff I J (n + 1) f) (hfp : IsProperMap f) {γ : ℝ → B}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) J (n + 1) γ) {s : ℝ} {x : P} (hx : f x = γ s) (t : ℝ) :
    ∃ c : ℝ → P, ContMDiff 𝓘(ℝ, ℝ) I n c ∧ IsHorizontalMap 𝓘(ℝ, ℝ) D c ∧
      EqOn (f ∘ c) γ (uIcc s t) ∧ c s = x := by
  have hn' : (1 : ℕ∞ω) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℕ∞ω) ≠ 0 := (zero_lt_one.trans_le hn').ne'
  have h2 : (2 : ℕ∞ω) ≤ n + 1 := by
    have := add_le_add hn' (le_refl (1 : ℕ∞ω))
    rwa [one_add_one_eq_two] at this
  let S : Set ℝ := {t | ∃ c : ℝ → P, ContMDiff 𝓘(ℝ, ℝ) I n c ∧ IsHorizontalMap 𝓘(ℝ, ℝ) D c ∧
      EqOn (f ∘ c) γ (uIcc s t) ∧ c s = x}
  -- Near each time `t`, a lift over one trivialization continues any lift that reaches near `t`.
  have hstep (t : ℝ) : ∃ ε > 0, ∀ t' ∈ S, dist t' t < ε → Metric.ball t ε ⊆ S := by
    let e := trivializationAt F (TangentSpace J) (γ t)
    obtain ⟨ε₀, hε₀, hball⟩ := Metric.mem_nhds_iff.1
      (hγ.continuous.continuousAt.preimage_mem_nhds
        (e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' (γ t))))
    obtain ⟨ε, hε, hεε⟩ : ∃ ε, 0 < ε ∧ ε < ε₀ := ⟨ε₀ / 2, by positivity, by linarith⟩
    refine ⟨ε, hε, fun t' ⟨c₁, hc₁, hh₁, hγ₁, hs₁⟩ ht' t'' ht'' ↦ ?_⟩
    have hmaps : MapsTo γ (Icc (t - ε) (t + ε)) e.baseSet := fun u hu ↦ hball (by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [hu.1, hu.2])
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at ht''
    rw [Real.dist_eq, abs_lt] at ht'
    have ht'J : t' ∈ Icc (t - ε) (t + ε) := ⟨by linarith, by linarith⟩
    obtain ⟨c₂, hc₂, hh₂, hγ₂, hs₂⟩ := hD.exists_isHorizontalMap_lift_of_mapsTo_baseSet hn hf
      hfp hγ ht'J e hmaps (x := c₁ t') (hγ₁ right_mem_uIcc)
    -- The two lifts agree where both lie over `γ`.
    have hagree : EqOn c₁ c₂ (uIcc s t' ∩ Icc (t - ε) (t + ε)) := by
      rw [uIcc, Icc_inter_Icc]
      exact hD.eqOn_of_isHorizontalMap hn' (hf.of_le h2) (hγ.of_le h2) (hc₁.mdifferentiable hn0)
        (hc₂.mdifferentiable hn0) hh₁ hh₂
        (fun u hu ↦ hγ₁ (Icc_subset_Icc le_sup_left inf_le_left hu))
        (fun u hu ↦ hγ₂ (Icc_subset_Icc le_sup_right inf_le_right hu))
        ⟨sup_le inf_le_right ht'J.1, le_inf le_sup_right ht'J.2⟩ hs₂.symm
    rcases lt_or_ge s (t - ε) with hs | hs
    · -- `s` lies before the interval: follow `c₁`, then `c₂`.
      have hm : c₁ =ᶠ[𝓝 ((t - ε + t') / 2)] c₂ := by
        filter_upwards [Ioo_mem_nhds (show t - ε < (t - ε + t') / 2 by linarith)
          (show (t - ε + t') / 2 < t' by linarith)] with v hv
        exact hagree ⟨mem_uIcc.2 (.inl ⟨by linarith [hv.1], hv.2.le⟩),
          ⟨hv.1.le, by linarith [hv.2]⟩⟩
      obtain ⟨hcs, hhs⟩ := contMDiff_isHorizontalMap_piecewise hc₁ hc₂ hh₁ hh₂ hm
      refine ⟨_, hcs, hhs, fun u hu ↦ ?_, by simp [show s ≤ (t - ε + t') / 2 by linarith, hs₁]⟩
      rw [mem_uIcc] at hu
      simp only [comp_apply]
      split_ifs with hum
      · exact hγ₁ (mem_uIcc.2 (.inl ⟨by rcases hu with h | h <;> linarith, by linarith⟩))
      · exact hγ₂ ⟨by linarith, by rcases hu with h | h <;> linarith⟩
    rcases lt_or_ge (t + ε) s with hs' | hs'
    · -- `s` lies after the interval: follow `c₂`, then `c₁`.
      have hm : c₂ =ᶠ[𝓝 ((t' + (t + ε)) / 2)] c₁ := by
        filter_upwards [Ioo_mem_nhds (show t' < (t' + (t + ε)) / 2 by linarith)
          (show (t' + (t + ε)) / 2 < t + ε by linarith)] with v hv
        exact (hagree ⟨mem_uIcc.2 (.inr ⟨hv.1.le, by linarith [hv.2]⟩),
          ⟨by linarith [hv.1], hv.2.le⟩⟩).symm
      obtain ⟨hcs, hhs⟩ := contMDiff_isHorizontalMap_piecewise hc₂ hc₁ hh₂ hh₁ hm
      refine ⟨_, hcs, hhs, fun u hu ↦ ?_,
        by simp [show ¬ s ≤ (t' + (t + ε)) / 2 by linarith, hs₁]⟩
      rw [mem_uIcc] at hu
      simp only [comp_apply]
      split_ifs with hum
      · exact hγ₂ ⟨by rcases hu with h | h <;> linarith, by linarith⟩
      · exact hγ₁ (mem_uIcc.2 (.inr ⟨by linarith, by rcases hu with h | h <;> linarith⟩))
    · -- `s` lies in the interval: `c₂` is a lift through `x`.
      refine ⟨c₂, hc₂, hh₂, fun u hu ↦ hγ₂ ?_, ?_⟩
      · rcases mem_uIcc.1 hu with h | h <;> constructor <;> linarith
      · rw [← hs₁]
        exact (hagree ⟨left_mem_uIcc, hs, hs'⟩).symm
  have hsS : s ∈ S := by
    obtain ⟨c, hc, hh, hγc, hcs⟩ := hD.exists_isHorizontalMap_lift_of_mapsTo_baseSet hn hf hfp hγ
      (left_mem_Icc.2 le_rfl) (trivializationAt F (TangentSpace J) (γ s))
      (fun u hu ↦ by
        rw [Icc_self, mem_singleton_iff] at hu
        exact hu ▸ FiberBundle.mem_baseSet_trivializationAt' _) hx
    exact ⟨c, hc, hh, by rwa [uIcc_self, ← Icc_self], hcs⟩
  have hopen : IsOpen S := Metric.isOpen_iff.2 fun t ht ↦ by
    obtain ⟨ε, hε, h⟩ := hstep t
    exact ⟨ε, hε, h t ht (by simpa using hε)⟩
  have hclosed : IsClosed S := closure_subset_iff_isClosed.1 fun t ht ↦ by
    obtain ⟨ε, hε, h⟩ := hstep t
    obtain ⟨t', ht', hd⟩ := Metric.mem_closure_iff.1 ht ε hε
    exact h t' ht' (by rwa [dist_comm]) (Metric.mem_ball_self hε)
  have hS : S = univ := IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨s, hsS⟩
  exact (show t ∈ S from hS ▸ mem_univ t)

include hD in
/-- **Horizontal lifts of curves.** Let `D` be a `C^n` Ehresmann connection, `1 ≤ n`, on a proper
`C^(n+1)` map `f : P → B` of finite-dimensional boundaryless Hausdorff manifolds, and `γ` a
`C^(n+1)` curve in `B`. For every time `s` and every `x` with `f x = γ s`, there is a `C^n`
horizontal curve `c` over `γ` with `c s = x`. For `n = ∞`, `f`, `γ` and `c` are all smooth. -/
theorem exists_isHorizontalMap_lift (hn : 1 ≤ n)
    (hf : ContMDiff I J (n + 1) f) (hfp : IsProperMap f) {γ : ℝ → B}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) J (n + 1) γ) {s : ℝ} {x : P} (hx : f x = γ s) :
    ∃ c : ℝ → P, ContMDiff 𝓘(ℝ, ℝ) I n c ∧ IsHorizontalMap 𝓘(ℝ, ℝ) D c ∧ f ∘ c = γ ∧
      c s = x := by
  have hn' : (1 : ℕ∞ω) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℕ∞ω) ≠ 0 := (zero_lt_one.trans_le hn').ne'
  have h2 : (2 : ℕ∞ω) ≤ n + 1 := by
    have := add_le_add hn' (le_refl (1 : ℕ∞ω))
    rwa [one_add_one_eq_two] at this
  -- A lift over `Set.Icc (s - k) (s + k)` for each `k`: lift from `s` back to `s - k`, then
  -- from `s - k` on to `s + k`; by uniqueness the second lift passes through `x` at `s`.
  have hlift (k : ℕ) : ∃ c : ℝ → P, ContMDiff 𝓘(ℝ, ℝ) I n c ∧ IsHorizontalMap 𝓘(ℝ, ℝ) D c ∧
      EqOn (f ∘ c) γ (Icc (s - k) (s + k)) ∧ c s = x := by
    obtain ⟨c₁, hc₁, hh₁, hγ₁, hs₁⟩ := hD.exists_isHorizontalMap_lift_uIcc hn hf hfp hγ hx (s - k)
    obtain ⟨c₂, hc₂, hh₂, hγ₂, hs₂⟩ := hD.exists_isHorizontalMap_lift_uIcc hn hf hfp hγ
      (hγ₁ right_mem_uIcc) (s + k)
    rw [uIcc_of_ge (by linarith)] at hγ₁
    rw [uIcc_of_le (by linarith)] at hγ₂
    refine ⟨c₂, hc₂, hh₂, hγ₂, ?_⟩
    rw [← hs₁]
    exact hD.eqOn_of_isHorizontalMap hn' (hf.of_le h2) (hγ.of_le h2) (hc₂.mdifferentiable hn0)
      (hc₁.mdifferentiable hn0) hh₂ hh₁ (hγ₂.mono (Icc_subset_Icc_right (by linarith))) hγ₁
      (left_mem_Icc.2 (by linarith)) hs₂ (right_mem_Icc.2 (by linarith))
  choose c hc hh hγc hcs using hlift
  -- The lifts agree where both lie over `γ`.
  have hagree (k l : ℕ) : EqOn (c k) (c l) (Icc (s - k) (s + k) ∩ Icc (s - l) (s + l)) := by
    rw [Icc_inter_Icc]
    exact hD.eqOn_of_isHorizontalMap hn' (hf.of_le h2) (hγ.of_le h2) ((hc k).mdifferentiable hn0)
      ((hc l).mdifferentiable hn0) (hh k) (hh l)
      (fun u hu ↦ hγc k (Icc_subset_Icc le_sup_left inf_le_left hu))
      (fun u hu ↦ hγc l (Icc_subset_Icc le_sup_right inf_le_right hu))
      ⟨sup_le (sub_le_self _ k.cast_nonneg) (sub_le_self _ l.cast_nonneg),
        le_inf (le_add_of_nonneg_right k.cast_nonneg) (le_add_of_nonneg_right l.cast_nonneg)⟩
      ((hcs k).trans (hcs l).symm)
  -- At `u`, follow the lift over an interval that contains `u` in its interior.
  let N : ℝ → ℕ := fun u ↦ ⌈|u - s|⌉₊ + 1
  have hN (u : ℝ) : u ∈ Ioo (s - N u) (s + N u) := by
    have := Nat.le_ceil |u - s|
    simp only [N, Nat.cast_add, Nat.cast_one]
    constructor <;> linarith [le_abs_self (u - s), neg_abs_le (u - s)]
  have hloc (u : ℝ) : (fun v ↦ c (N v) v) =ᶠ[𝓝 u] c (N u) := by
    filter_upwards [Ioo_mem_nhds (hN u).1 (hN u).2] with v hv
    exact hagree (N v) (N u) ⟨Ioo_subset_Icc_self (hN v), Ioo_subset_Icc_self hv⟩
  exact ⟨fun v ↦ c (N v) v, fun u ↦ (hc (N u) u).congr_of_eventuallyEq (hloc u),
    IsHorizontalMap.of_forall_eventuallyEq fun u ↦ ⟨_, hh (N u), hloc u⟩,
    funext fun u ↦ hγc (N u) (Ioo_subset_Icc_self (hN u)), hcs (N s)⟩

end Existence

end IsEhresmannConnection

end TauCeti

end
