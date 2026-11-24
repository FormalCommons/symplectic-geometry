/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Submersion.HorizontalLiftField
public import TauCeti.Geometry.Manifold.Distribution.Horizontal
public import TauCeti.Geometry.Manifold.MFDeriv.Curve
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

## Main results

* `TauCeti.IsEhresmannConnection.curveVelocity_eq_horizontalLift_iff`: a differentiable curve has
  as velocity the horizontal lift of the velocity of its projection exactly where its velocity is
  horizontal.
* `TauCeti.IsEhresmannConnection.eqOn_of_isHorizontalMap`: two differentiable horizontal curves
  over the same `C²` curve of `B` on `Set.Icc a b` that agree at one time of it agree on it.
* `TauCeti.IsEhresmannConnection.eq_of_isHorizontalMap`: the same on all of `ℝ`.

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

end IsEhresmannConnection

end TauCeti

end
