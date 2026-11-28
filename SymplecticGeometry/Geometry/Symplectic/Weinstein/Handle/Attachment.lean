/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Weinstein.Handle.StableDisc
public import TauCeti.Dynamics.Flow.LevelCrossing
import SymplecticGeometry.Geometry.Manifold.Flow.LevelCrossing
import SymplecticGeometry.Geometry.Manifold.IntegralCurve.Monotone
import SymplecticGeometry.Geometry.Manifold.Morse.GradientLike

/-!
# Attaching handles: orbits across a sublevel transverse to the Liouville field

Let `(ω, X, f)` be a Weinstein structure on a boundaryless Hausdorff manifold `M`, with flow
`Φ = hW.flow`, and let `a, b` be reals. Put
`K = {f ≤ a} ∪ ⋃ p ∈ criticalPoints f ∩ f ⁻¹' Icc a b, Φ.stableSet p`: the lower sublevel
together with the stable sets of the critical points in the region `f ⁻¹' Icc a b`. Let `g : M → ℝ`
be a function whose sublevel `{g ≤ 0}` is to be moved onto `{f ≤ b}` along the orbits of `X`:
`X` points out of it along `g ⁻¹' {0}` (`0 < dg(X)` there), it contains `K` in `{g < 0}`, and it
lies in `{f < b}`. This file proves the facts about the orbits of `Φ` that such a move uses:

1. an orbit meets `g ⁻¹' {0}` at most once, going from `{g < 0}` to `{g > 0}`;
2. the backward orbit of every point of `{f ≤ b}` enters `{g < 0}`;
3. the forward orbit of every point of `g ⁻¹' {0}` reaches the level `f ⁻¹' {b}`, after a
   positive time;
4. the times at which orbits cross `g ⁻¹' {0}` and a regular level `f ⁻¹' {b}`
   (`Flow.levelCrossingTime`) are smooth where the orbits meet these levels, and the time from
   `g ⁻¹' {0}` to `f ⁻¹' {b}` is positive and bounded.

Fact (1) is the library's `IsMIntegralCurve.lt_apply_of_le_apply`,
`IsMIntegralCurve.apply_lt_of_apply_le` and
`IsMIntegralCurve.subsingleton_setOfPred_apply_eq_of_mvfderiv_pos`, applied to the orbits of `Φ`.
Facts (2) and (3) follow from the statements about gradient-like flows in a compact region of
`Morse/GradientLike.lean`. A backward orbit that never enters `{f ≤ a}` clusters at `-∞` at a
critical point in the region (`TauCeti.IsGradientLike.exists_flow_apply_le_or_mapClusterPt_atBot`),
which is a rest point and so lies in `K`
(`SymplecticGeometry.IsWeinsteinStructure.mem_stableSet_self`), inside the open set `{g < 0}`.
A forward orbit from `g ⁻¹' {0}` that stays below `b` tends to a critical point in the region
(`TauCeti.IsGradientLike.exists_mem_stableSet_of_isCompact`), which would put its starting point
in `K`, where `g < 0`.

For fact (4), the library's `TauCeti.contMDiffOn_levelCrossingTime_of_mvfderiv_pos` and
`TauCeti.contMDiffOn_flow_levelCrossingTime_of_mvfderiv_pos`
(`Geometry/Manifold/Flow/LevelCrossing.lean`) give the smoothness of the crossing time and the
crossing point of a level crossed upwards, on the open set of points whose orbits meet it. The
level `g ⁻¹' {0}` is a closed subset of the compact region `f ⁻¹' Icc a b`, on which the continuous
crossing time of `f ⁻¹' {b}` is bounded.

The statements are made for a Weinstein structure and any reals `a, b`; for a Weinstein cobordism
`hW : IsWeinsteinCobordism ω X f a b` they apply to `hW.isWeinsteinStructure`, with `K` written
out as above.

## Main results

* `SymplecticGeometry.IsWeinsteinStructure.lt_flow_apply_of_le_flow_apply`,
  `SymplecticGeometry.IsWeinsteinStructure.flow_apply_lt_of_flow_apply_le` and
  `SymplecticGeometry.IsWeinsteinStructure.subsingleton_setOfPred_flow_apply_eq_of_mvfderiv_pos`:
  an orbit crosses a level of `g` on which `dg(X) > 0` at most once, and only upwards.
* `SymplecticGeometry.IsWeinsteinStructure.exists_flow_apply_neg`: the backward orbit of a point
  of `{f ≤ b}` enters `{g < 0}`.
* `SymplecticGeometry.IsWeinsteinStructure.exists_flow_apply_eq_upper`: the forward orbit of a
  point of `g ⁻¹' {0}` reaches `f ⁻¹' {b}`.
* `SymplecticGeometry.IsWeinsteinStructure.contMDiffOn_levelCrossingTime_of_mvfderiv_pos` and
  `SymplecticGeometry.IsWeinsteinStructure.contMDiffOn_flow_levelCrossingTime_of_mvfderiv_pos`:
  the crossing time of such a level, and the crossing point, are smooth on the open set of points
  whose orbits meet it;
  `SymplecticGeometry.IsWeinsteinStructure.contMDiffOn_levelCrossingTime_of_isRegularValue`: so is
  the crossing time of a regular level of `f`.
* `SymplecticGeometry.IsWeinsteinStructure.exists_forall_levelCrossingTime_mem_Ioc`: the time from
  `g ⁻¹' {0}` to `f ⁻¹' {b}` lies in `Ioc 0 T` for a common `T`.

## References

* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  Section 11.1
-/

public section

open Filter Set TauCeti
open scoped Manifold Topology

namespace SymplecticGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) (⊤ : ℕ∞) M]
  [T2Space M]
  {ω : SmoothTwoForm 𝓘(ℝ, E) M} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x} {f : M → ℝ}

namespace IsWeinsteinStructure

variable (hW : IsWeinsteinStructure ω X f) {g : M → ℝ} {c : ℝ}
include hW

/-- **An orbit crosses an upward level of `g` only upwards.** Let `g` be continuous, and
differentiable with `dg(X) > 0` at each point of the level `g ⁻¹' {c}`. If
`c ≤ g (Φ s x)` for the flow `Φ` of a Weinstein structure, then `c < g (Φ t x)` for every
`t > s`. -/
theorem lt_flow_apply_of_le_flow_apply (hg : Continuous g)
    (hgX : ∀ x, g x = c → MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ) g x ∧ 0 < mvfderiv 𝓘(ℝ, E) g x (X x))
    (x : M) {s t : ℝ} (hs : c ≤ g (hW.flow s x)) (hst : s < t) : c < g (hW.flow t x) :=
  (hW.isMIntegralCurve_flow x).lt_apply_of_le_apply (f := g)
    (hg.comp (hW.isMIntegralCurve_flow x).continuous) (fun _ ↦ hgX _) hs hst

/-- **An orbit crosses an upward level of `g` only upwards, looking backwards.** Let `g` be
continuous, and differentiable with `dg(X) > 0` at each point of the level `g ⁻¹' {c}`. If
`g (Φ t x) ≤ c` for the flow `Φ` of a Weinstein structure, then `g (Φ s x) < c` for every
`s < t`. -/
theorem flow_apply_lt_of_flow_apply_le (hg : Continuous g)
    (hgX : ∀ x, g x = c → MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ) g x ∧ 0 < mvfderiv 𝓘(ℝ, E) g x (X x))
    (x : M) {s t : ℝ} (ht : g (hW.flow t x) ≤ c) (hst : s < t) : g (hW.flow s x) < c :=
  (hW.isMIntegralCurve_flow x).apply_lt_of_apply_le (f := g)
    (hg.comp (hW.isMIntegralCurve_flow x).continuous) (fun _ ↦ hgX _) ht hst

/-- **An orbit meets an upward level of `g` at most once.** Let `g` be continuous, and
differentiable with `dg(X) > 0` at each point of the level `g ⁻¹' {c}`. Then every orbit of the
flow of a Weinstein structure meets that level at most once. -/
theorem subsingleton_setOfPred_flow_apply_eq_of_mvfderiv_pos (hg : Continuous g)
    (hgX : ∀ x, g x = c → MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ) g x ∧ 0 < mvfderiv 𝓘(ℝ, E) g x (X x))
    (x : M) :
    {t | g (hW.flow t x) = c}.Subsingleton :=
  (hW.isMIntegralCurve_flow x).subsingleton_setOfPred_apply_eq_of_mvfderiv_pos (f := g)
    (hg.comp (hW.isMIntegralCurve_flow x).continuous) fun _ ↦ hgX _

/-- **Backward orbits enter `{g < 0}`.** Let `g` be continuous, and let `{g < 0}` contain the
sublevel `{f ≤ a}` and the stable sets of the critical points of `f` in `f ⁻¹' Icc a b` under the
flow `Φ` of a Weinstein structure. Then for every `x` with `f x ≤ b` there is a time `t ≤ 0` with
`g (Φ t x) < 0`. -/
theorem exists_flow_apply_neg {a b : ℝ} (hg : Continuous g)
    (hK : {x | f x ≤ a} ∪ ⋃ p ∈ criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Icc a b, hW.flow.stableSet p ⊆
      {x | g x < 0}) {x : M} (hx : f x ≤ b) :
    ∃ t ≤ 0, g (hW.flow t x) < 0 := by
  have hf := hW.isGeneralizedMorse.contMDiff.mdifferentiable (by simp)
  rcases hW.isGradientLike.exists_flow_apply_le_or_mapClusterPt_atBot hW.isMIntegralCurve_flow hf
    (hW.isProperMap.isCompact_preimage isCompact_Icc) hx with ⟨t, ht, hft⟩ | ⟨⟨z, hz⟩, hcrit⟩
  · exact ⟨t, ht, hK (Or.inl hft)⟩
  · -- The cluster point `z` is a rest point in the region, so `g z < 0`, and the backward orbit
    -- comes back near `z` at arbitrarily negative times.
    have hzK : g z < 0 := hK <| Or.inr <| mem_biUnion (hcrit z hz)
      (hW.mem_stableSet_self (hcrit z hz).1)
    obtain ⟨t, ht, hneg⟩ := ((mapClusterPt_iff_frequently.1 hz _
      ((isOpen_lt hg continuous_const).mem_nhds hzK)).and_eventually
      (eventually_le_atBot 0)).exists
    exact ⟨t, hneg, ht⟩

/-- **Forward orbits from `g ⁻¹' {0}` reach the upper level.** Let `{g < 0}` contain the sublevel
`{f ≤ a}` and the stable sets of the critical points of `f` in `f ⁻¹' Icc a b` under the flow `Φ`
of a Weinstein structure. Then for every `x` with `g x = 0` and `f x < b` there is a time `t > 0`
with `f (Φ t x) = b`. -/
theorem exists_flow_apply_eq_upper {a b : ℝ}
    (hK : {x | f x ≤ a} ∪ ⋃ p ∈ criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Icc a b, hW.flow.stableSet p ⊆
      {x | g x < 0})
    {x : M} (hx : g x = 0) (hxb : f x < b) :
    ∃ t, 0 < t ∧ f (hW.flow t x) = b := by
  have hf := hW.isGeneralizedMorse.contMDiff.mdifferentiable (by simp)
  by_contra hne
  push Not at hne
  -- The forward orbit stays below `b`: otherwise it would cross `f ⁻¹' {b}` after time `0`.
  have hb : ∀ t, 0 ≤ t → f (hW.flow t x) ≤ b := by
    intro t ht
    by_contra hlt
    push Not at hlt
    have hcont : ContinuousOn (fun s ↦ f (hW.flow s x)) (Icc 0 t) :=
      (hf.continuous.comp (hW.isMIntegralCurve_flow x).continuous).continuousOn
    obtain ⟨s, hs, hfs⟩ := intermediate_value_Icc ht hcont
      ⟨by simpa only [Flow.map_zero_apply] using hxb.le, hlt.le⟩
    rcases hs.1.eq_or_lt with rfl | hs₀
    · simp only [Flow.map_zero_apply] at hfs
      exact hxb.ne hfs
    · exact hne s hs₀ hfs
  -- So `x` lies in `K`, where `g < 0`.
  refine ((hK ?_ : g x < 0).ne hx).elim
  rcases lt_or_ge (f x) a with hxa | hxa
  · exact Or.inl hxa.le
  · obtain ⟨p, hp, hxp⟩ := hW.isGradientLike.exists_mem_stableSet_of_isCompact
      hW.isMIntegralCurve_flow hf (hW.isProperMap.isCompact_preimage isCompact_Icc)
      (hW.isGeneralizedMorse.finite_criticalPoints_inter
        (hW.isProperMap.isCompact_preimage isCompact_Icc)) hxa hb
    exact Or.inr (mem_biUnion hp hxp)

/-! ### Crossing times -/

/-- **The crossing time of an upward level is smooth.** Let `g` be smooth with `dg(X) > 0` at
each point of the level `g ⁻¹' {c}`. Then the time `Flow.levelCrossingTime φ g c` at which orbits
of the flow `φ` of a Weinstein structure cross that level is smooth on the set of points whose
orbits meet it, which is open by `TauCeti.isOpen_setOf_exists_flow_apply_eq`. -/
theorem contMDiffOn_levelCrossingTime_of_mvfderiv_pos
    (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) (⊤ : ℕ∞) g)
    (hgX : ∀ x, g x = c → 0 < mvfderiv 𝓘(ℝ, E) g x (X x)) :
    ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) (⊤ : ℕ∞) (Flow.levelCrossingTime hW.flow g c)
      {x | ∃ t, g (hW.flow t x) = c} :=
  _root_.TauCeti.contMDiffOn_levelCrossingTime_of_mvfderiv_pos le_top hW.contMDiff_field
    hW.isCompleteVectorField hW.flowOf_eq_flow hg hgX

/-- **The crossing point of an upward level is smooth.** Let `g` be smooth with `dg(X) > 0` at
each point of the level `g ⁻¹' {c}`. Then the map `y ↦ φ (Flow.levelCrossingTime φ g c y) y`, for
`φ` the flow of a Weinstein structure, which follows each orbit to the level, is smooth on the
set of points whose orbits meet it. -/
theorem contMDiffOn_flow_levelCrossingTime_of_mvfderiv_pos
    (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) (⊤ : ℕ∞) g)
    (hgX : ∀ x, g x = c → 0 < mvfderiv 𝓘(ℝ, E) g x (X x)) :
    ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) (⊤ : ℕ∞)
      (fun y ↦ hW.flow (Flow.levelCrossingTime hW.flow g c y) y)
      {x | ∃ t, g (hW.flow t x) = c} :=
  _root_.TauCeti.contMDiffOn_flow_levelCrossingTime_of_mvfderiv_pos le_top hW.contMDiff_field
    hW.isCompleteVectorField hW.flowOf_eq_flow hg hgX

/-- **The crossing time of a regular level is smooth.** For a regular value `b` of the function of
a Weinstein structure with flow `φ`, the time `Flow.levelCrossingTime φ f b` at which orbits cross
the level `f ⁻¹' {b}` is smooth on the open set of points whose orbits meet that level. -/
theorem contMDiffOn_levelCrossingTime_of_isRegularValue {b : ℝ}
    (hb : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) f b) :
    ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) (⊤ : ℕ∞) (Flow.levelCrossingTime hW.flow f b)
      {x | ∃ t, f (hW.flow t x) = b} :=
  hW.contMDiffOn_levelCrossingTime_of_mvfderiv_pos hW.isGeneralizedMorse.contMDiff
    fun _ hx ↦ hW.isGradientLike.mvfderiv_apply_pos_of_isRegularValue hb hx

/-- **The time from `g ⁻¹' {0}` to the upper level is bounded.** Let `b` be a regular value of the
function of a Weinstein structure with flow `φ`, let `g` be continuous with `f < b` on
`g ⁻¹' {0}`, and let `{g < 0}` contain the sublevel `{f ≤ a}` and the stable sets of the critical
points of `f` in `f ⁻¹' Icc a b`. Then there is a `T` such that the orbit of every point `x` of
`g ⁻¹' {0}` crosses the level `f ⁻¹' {b}` at a time `Flow.levelCrossingTime φ f b x` in
`Ioc 0 T`. -/
theorem exists_forall_levelCrossingTime_mem_Ioc {a b : ℝ}
    (hb : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) f b) (hg : Continuous g)
    (hK : {x | f x ≤ a} ∪ ⋃ p ∈ criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Icc a b, hW.flow.stableSet p ⊆
      {x | g x < 0})
    (hgb : ∀ x, g x = 0 → f x < b) :
    ∃ T, ∀ x, g x = 0 → Flow.levelCrossingTime hW.flow f b x ∈ Ioc 0 T := by
  have hfX (x : M) (hx : f x = b) :
      MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ) f x ∧ 0 < mvfderiv 𝓘(ℝ, E) f x (X x) :=
    ⟨hW.isGeneralizedMorse.contMDiff.mdifferentiableAt (by simp),
      hW.isGradientLike.mvfderiv_apply_pos_of_isRegularValue hb hx⟩
  -- The orbit of a point of `g ⁻¹' {0}` meets `f ⁻¹' {b}` exactly once, at a positive time.
  have hcross (x : M) (hx : g x = 0) :
      ∃ t, 0 < t ∧ f (hW.flow t x) = b ∧ Flow.levelCrossingTime hW.flow f b x = t := by
    obtain ⟨t, ht, hft⟩ := hW.exists_flow_apply_eq_upper hK hx (hgb x hx)
    exact ⟨t, ht, hft, hW.subsingleton_setOfPred_flow_apply_eq_of_mvfderiv_pos
      hW.isGeneralizedMorse.contMDiff.continuous hfX x
      (Flow.apply_flow_levelCrossingTime ⟨t, hft⟩) hft⟩
  -- `g ⁻¹' {0}` is a closed subset of the compact region `f ⁻¹' Icc a b`.
  have hcompact : IsCompact (g ⁻¹' {0}) :=
    (hW.isProperMap.isCompact_preimage isCompact_Icc).of_isClosed_subset
      (isClosed_singleton.preimage hg) fun x hx ↦
        ⟨(not_le.1 fun hxa ↦ (hK (Or.inl hxa) : g x < 0).ne hx).le, (hgb x hx).le⟩
  obtain ⟨T, hT⟩ := hcompact.bddAbove_image
    ((hW.contMDiffOn_levelCrossingTime_of_isRegularValue hb).continuousOn.mono fun x hx ↦
      (hcross x hx).elim fun t ht ↦ ⟨t, ht.2.1⟩)
  refine ⟨T, fun x hx ↦ ⟨?_, hT (mem_image_of_mem _ hx)⟩⟩
  obtain ⟨t, ht, -, hτ⟩ := hcross x hx
  exact hτ ▸ ht

end IsWeinsteinStructure

end SymplecticGeometry

end
