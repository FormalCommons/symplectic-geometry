/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Weinstein.Handle.StableDisc
import SymplecticGeometry.Geometry.Manifold.Flow.LevelCrossing
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
   positive time.

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

end IsWeinsteinStructure

end SymplecticGeometry

end
