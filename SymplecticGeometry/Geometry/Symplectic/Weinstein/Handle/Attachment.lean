/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Weinstein.Handle.StableDisc
public import SymplecticGeometry.Geometry.Symplectic.Weinstein.Handle.Cobordism
public import TauCeti.Dynamics.Flow.LevelCrossing
import SymplecticGeometry.Analysis.Calculus.BumpFunction.SlowDescent
import SymplecticGeometry.Dynamics.Flow.LevelCrossing
import SymplecticGeometry.Geometry.Manifold.Flow.TimeChange
import SymplecticGeometry.Geometry.Manifold.IntegralCurve.Monotone
import SymplecticGeometry.Geometry.Manifold.Flow.LevelCrossing
import SymplecticGeometry.Geometry.Manifold.Morse.GradientLike
import TauCeti.Topology.Compactness.Normed

/-!
# Attaching handles: moving a sublevel onto `{f ≤ b}` along the Liouville flow

Let `(ω, X, f)` be a Weinstein structure on a boundaryless Hausdorff manifold `M`, with flow
`Φ = hW.flow`, and let `a, b` be reals. Put
`K = {f ≤ a} ∪ ⋃ p ∈ criticalPoints f ∩ f ⁻¹' Icc a b, Φ.stableSet p`: the lower sublevel
together with the stable sets of the critical points in the region `f ⁻¹' Icc a b`. Let `g : M → ℝ`
be a function whose sublevel `{g ≤ 0}` is to be moved onto `{f ≤ b}` along the orbits of `X`:
`X` points out of it along `g ⁻¹' {0}` (`0 < dg(X)` there), it contains `K` in `{g < 0}`, and it
lies in `{f < b}`. This file proves the facts about the orbits of `Φ` that such a move uses,
and then makes the move.

1. an orbit meets `g ⁻¹' {0}` at most once, going from `{g < 0}` to `{g > 0}`;
2. the backward orbit of every point of `{f ≤ b}` enters `{g < 0}`;
3. the forward orbit of every point of `g ⁻¹' {0}` reaches the level `f ⁻¹' {b}`, after a
   positive time;
4. the times at which orbits cross `g ⁻¹' {0}` and a regular level `f ⁻¹' {b}`
   (`Flow.levelCrossingTime`) are smooth where the orbits meet these levels, and the time from
   `g ⁻¹' {0}` to `f ⁻¹' {b}` is positive and bounded.

Fact (1) needs no statement of its own: it is the library's
`IsMIntegralCurve.lt_apply_of_le_apply` and `IsMIntegralCurve.apply_lt_of_apply_le`, applied to
the orbit `hW.isMIntegralCurve_flow x` of `Φ`, and
`TauCeti.subsingleton_setOf_flow_apply_eq_of_mvfderiv_pos`.
Facts (2) and (3) follow from the statements about gradient-like flows in a compact region of
`Morse/GradientLike.lean`. A backward orbit that never enters `{f ≤ a}` clusters at `-∞` at a
critical point in the region (`TauCeti.IsGradientLike.exists_flow_apply_le_or_mapClusterPt_atBot`),
which is a rest point and so lies in `K`
(`SymplecticGeometry.IsWeinsteinStructure.mem_stableSet_self`), inside the open set `{g < 0}`.
A forward orbit from `g ⁻¹' {0}` that stays below `b` tends to a critical point in the region
(`TauCeti.IsGradientLike.exists_mem_stableSet_of_isCompact`), which would put its starting point
in `K`, where `g < 0`.

For fact (4), `IsWeinsteinStructure.contMDiffOn_levelCrossingTime_of_mvfderiv_pos` and
`IsWeinsteinStructure.contMDiffOn_flow_levelCrossingTime_of_mvfderiv_pos`
(`Weinstein/Handle/StableDisc.lean`) give the smoothness of the crossing time and the crossing
point of a level crossed upwards, on the open set of points whose orbits meet it, and
`IsWeinsteinStructure.contMDiffOn_levelCrossingTime_of_isRegularValue`, in the same file, is the
case of a regular level of `f`. The
level `g ⁻¹' {0}` is a closed subset of the compact region `f ⁻¹' Icc a b`, on which the continuous
crossing time of `f ⁻¹' {b}` is bounded.

The statements are made for a Weinstein structure and any reals `a, b`; for a Weinstein cobordism
`hW : IsWeinsteinCobordism ω X f a b` they apply to `hW.isWeinsteinStructure`, with `K` written
out as above.

The move itself changes time along each orbit through `g ⁻¹' {0}` by a function `τ`,
`IsWeinsteinStructure.attachmentTime`. A point of such an orbit is `x = Φ s y` for one `y` on
`g ⁻¹' {0}`, by fact (1), and `τ x = T y * μ s`, where `T y` is the time from `y` to
`f ⁻¹' {b}` and `μ` is a bump that vanishes before a time `-δ` and equals `1` at time `0`
(`exists_contDiff_bump_neg_one_lt_mul_deriv`); `τ` is `0` off these orbits. It is nonnegative,
and it vanishes on `{f ≤ a}` when `δ` is the margin of `exists_pos_forall_lt_flow_apply`.
When `μ` has compact support, so does `τ`: its support lies in the compact set of points `Φ s y`
with `s` in `tsupport μ` and `y` on `g ⁻¹' {0}`, which is inside the open set of orbits crossing
`g ⁻¹' {0}`. There `τ` is built from the smooth crossing times and crossing point of fact (4), so
`τ` is smooth everywhere.

Along the orbit of a point `y` of `g ⁻¹' {0}`, `τ` is `t ↦ T y * μ t`, so its derivative along
`X` there is `T y * μ'`; with `T` bounded by `T₀` and `-1 < T₀ * μ'`, this gives `0 < 1 + dτ(X)`,
the condition under which the time change by `τ` is a diffeomorphism
(`TauCeti.globalFlowTimeChangeDiffeomorph`). Where `τ` is not differentiable, `dτ` is `0`, so the
inequality needs no smoothness of `τ`.

Let `Ψ x = Φ (τ x) x` be that time change. Off the orbits through `g ⁻¹' {0}` it is the identity,
and there `g` has one sign along each whole orbit, so `{g ≤ 0}` and `{f ≤ b}` agree on such an
orbit by fact (2) and the hypothesis `f < b` on `{g ≤ 0}`. On the orbit of a point `y` of
`g ⁻¹' {0}`, `Ψ (Φ s y) = Φ (s + T y * μ s) y`, and `s ↦ s + T y * μ s` is strictly increasing
and equals `T y` at `s = 0`. So `Ψ` carries the part `s ≤ 0` of the orbit, which is its part in
`{g ≤ 0}` by fact (1), into `{f ≤ b}`, and the part `s > 0` into `{b < f}`, as `b` is crossed only
once. Since `Ψ` is a bijection, it carries `{g ≤ 0}` onto `{f ≤ b}`
(`IsWeinsteinCobordism.exists_diffeomorph_image_sublevel_eq`). This is the step of Milnor's proof
of Theorem 3.1 in which a sublevel is pushed along the flow of a gradient-like field, here with a
time that varies from orbit to orbit and with critical points inside `{g < 0}`.

## Main definitions

* `SymplecticGeometry.IsWeinsteinStructure.attachmentTime`: the time function `τ`.

## Main results

* `SymplecticGeometry.IsWeinsteinStructure.exists_flow_apply_neg`: the backward orbit of a point
  of `{f ≤ b}` enters `{g < 0}`.
* `SymplecticGeometry.IsWeinsteinStructure.exists_flow_apply_eq_upper`: the forward orbit of a
  point of `g ⁻¹' {0}` reaches `f ⁻¹' {b}`.
* `SymplecticGeometry.IsWeinsteinStructure.exists_pos_forall_lt_flow_apply`: for some `δ > 0`,
  the orbits of the points of `g ⁻¹' {0}` stay out of `{f ≤ a}` from time `-δ` on.
* `SymplecticGeometry.IsWeinsteinStructure.exists_forall_levelCrossingTime_mem_Ioc`: the time from
  `g ⁻¹' {0}` to `f ⁻¹' {b}` lies in `Ioc 0 T` for a common `T`.
* `SymplecticGeometry.IsWeinsteinStructure.attachmentTime_flow_apply`: `τ (Φ s y) = T y * μ s`
  for `y` on `g ⁻¹' {0}`.
* `SymplecticGeometry.IsWeinsteinStructure.attachmentTime_nonneg`,
  `SymplecticGeometry.IsWeinsteinStructure.attachmentTime_eq_zero_of_le`: `0 ≤ τ`, and `τ = 0` on
  `{f ≤ a}`.
* `SymplecticGeometry.IsWeinsteinStructure.hasCompactSupport_attachmentTime`,
  `SymplecticGeometry.IsWeinsteinStructure.contMDiff_attachmentTime`: `τ` has compact support and
  is smooth, for a compact level `g ⁻¹' {0}` and a smooth bump `μ` with compact support.
* `SymplecticGeometry.IsWeinsteinStructure.one_add_mvfderiv_attachmentTime_pos`:
  `0 < 1 + dτ(X)` everywhere, for a bump `μ` with `-1 < T₀ * μ'`, `T₀` bounding the time from
  `g ⁻¹' {0}` to `f ⁻¹' {b}`.
* `SymplecticGeometry.IsWeinsteinStructure.apply_flow_attachmentTime_le`,
  `SymplecticGeometry.IsWeinsteinStructure.lt_apply_flow_attachmentTime`: the time change
  `x ↦ Φ (τ x) x` maps `{g ≤ 0}` into `{f ≤ b}` and `{0 < g}` into `{b < f}`.
* `SymplecticGeometry.IsWeinsteinCobordism.exists_diffeomorph_image_sublevel_eq`: for a Weinstein
  cobordism, a diffeomorphism `x ↦ Φ (τ x) x`, fixing `{f ≤ a}`, carries `{g ≤ 0}` onto
  `{f ≤ b}`.

## References

* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  Section 11.1
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  §3, Theorem 3.1 (moving sublevels along the flow of a rescaled gradient field).
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

variable (hW : IsWeinsteinStructure ω X f) {g : M → ℝ}
include hW

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

omit [T2Space M] in
/-- **The level `g ⁻¹' {0}` is compact.** Let `g` be continuous, let `{g < 0}` contain the
sublevel `{f ≤ a}` of the function of a Weinstein structure, and let `f ≤ b` on `g ⁻¹' {0}`. Then
`g ⁻¹' {0}` is compact, as a closed subset of the compact region `f ⁻¹' Icc a b`. -/
theorem isCompact_preimage_zero {a b : ℝ} (hg : Continuous g)
    (ha : {x | f x ≤ a} ⊆ {x | g x < 0}) (hgb : ∀ x, g x = 0 → f x ≤ b) :
    IsCompact (g ⁻¹' {0}) :=
  (hW.isProperMap.isCompact_preimage isCompact_Icc).of_isClosed_subset
    (isClosed_singleton.preimage hg) fun x hx ↦
      ⟨(not_le.1 fun hxa ↦ (ha hxa : g x < 0).ne hx).le, hgb x hx⟩

/-- **A margin between the lower sublevel and the backward orbits of `g ⁻¹' {0}`.** Let `g` be
continuous, let `{g < 0}` contain the sublevel `{f ≤ a}` of the function of a Weinstein structure
with flow `Φ`, and let `f ≤ b` on `g ⁻¹' {0}`. Then there is `δ > 0` such that `a < f (Φ s y)` for
every `y` with `g y = 0` and every time `s ≥ -δ`. -/
theorem exists_pos_forall_lt_flow_apply {a b : ℝ} (hg : Continuous g)
    (ha : {x | f x ≤ a} ⊆ {x | g x < 0}) (hgb : ∀ x, g x = 0 → f x ≤ b) :
    ∃ δ > 0, ∀ y, g y = 0 → ∀ s, -δ ≤ s → a < f (hW.flow s y) := by
  -- `a < f` on `g ⁻¹' {0}` and `f ∘ Φ` is continuous, so the bound holds for all small times,
  -- uniformly on the compact level.
  obtain ⟨ε, hε, h⟩ := (hW.isCompact_preimage_zero hg ha hgb).exists_pos_forall_norm_lt
    (Q := fun s y ↦ a < f (hW.flow s y)) fun y hy ↦
      (hW.isGeneralizedMorse.contMDiff.continuous.comp
        (hW.flow.continuous continuous_fst continuous_snd)).continuousAt.eventually
        (lt_mem_nhds (by
          simpa only [Function.comp_apply, Flow.map_zero_apply] using
            not_le.1 fun h ↦ (ha h : g y < 0).ne hy))
  -- For later times, `f` increases along the orbit.
  refine ⟨ε / 2, half_pos hε, fun y hy s hs ↦ (h ?_ y hy).trans_le (hW.monotone_comp_flow y hs)⟩
  rw [norm_neg, Real.norm_of_nonneg (half_pos hε).le]
  exact half_lt_self hε

/-! ### Crossing times -/

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
  -- The orbit of a point of `g ⁻¹' {0}` meets `f ⁻¹' {b}` exactly once, at a positive time.
  have hcross (x : M) (hx : g x = 0) :
      ∃ t, 0 < t ∧ f (hW.flow t x) = b ∧ Flow.levelCrossingTime hW.flow f b x = t := by
    obtain ⟨t, ht, hft⟩ := hW.exists_flow_apply_eq_upper hK hx (hgb x hx)
    exact ⟨t, ht, hft, Flow.levelCrossingTime_eq_of_subsingleton
      (_root_.TauCeti.subsingleton_setOf_flow_apply_eq_of_mvfderiv_pos
        (hW.contMDiff_field.of_le (by simp)) hW.isCompleteVectorField hW.flowOf_eq_flow
        (hW.isGeneralizedMorse.contMDiff.mdifferentiable (by simp))
        (fun _ ↦ hW.isGradientLike.mvfderiv_apply_pos_of_isRegularValue hb) x) hft⟩
  obtain ⟨T, hT⟩ :=
    (hW.isCompact_preimage_zero hg (subset_union_left.trans hK)
      fun x hx ↦ (hgb x hx).le).bddAbove_image
    ((hW.contMDiffOn_levelCrossingTime_of_isRegularValue hb).continuousOn.mono fun x hx ↦
      (hcross x hx).elim fun t ht ↦ ⟨t, ht.2.1⟩)
  refine ⟨T, fun x hx ↦ ⟨?_, hT (mem_image_of_mem _ hx)⟩⟩
  obtain ⟨t, ht, -, hτ⟩ := hcross x hx
  exact hτ ▸ ht

/-! ### The time function of the attachment -/

/-- **The time function of the attachment.** For `g : M → ℝ`, a level `b` and a bump `μ : ℝ → ℝ`,
the function `τ : M → ℝ` defined as follows on a point `x` whose orbit under the flow `Φ` meets
`g ⁻¹' {0}`: with `c = Flow.levelCrossingTime Φ g 0 x`, so that `y = Φ c x` lies on
`g ⁻¹' {0}` and `x = Φ (-c) y`, it is `τ x = Flow.levelCrossingTime Φ f b y * μ (-c)`, the time
from `y` to the level `f ⁻¹' {b}` scaled by `μ` at the time of `x` along the orbit of `y`.
It is `0` on the points whose orbits do not meet `g ⁻¹' {0}`. -/
noncomputable def attachmentTime (g : M → ℝ) (b : ℝ) (μ : ℝ → ℝ) : M → ℝ :=
  {x | ∃ t, g (hW.flow t x) = 0}.indicator fun x ↦
    Flow.levelCrossingTime hW.flow f b (hW.flow (Flow.levelCrossingTime hW.flow g 0 x) x) *
      μ (-Flow.levelCrossingTime hW.flow g 0 x)

/-- The definition of `IsWeinsteinStructure.attachmentTime`. -/
theorem attachmentTime_def (g : M → ℝ) (b : ℝ) (μ : ℝ → ℝ) :
    hW.attachmentTime g b μ = {x | ∃ t, g (hW.flow t x) = 0}.indicator fun x ↦
      Flow.levelCrossingTime hW.flow f b (hW.flow (Flow.levelCrossingTime hW.flow g 0 x) x) *
        μ (-Flow.levelCrossingTime hW.flow g 0 x) :=
  (rfl)

variable {b : ℝ} {μ : ℝ → ℝ}

/-- **The time function vanishes off the orbits of `g ⁻¹' {0}`.** If the orbit of `x` under the
flow does not meet `g ⁻¹' {0}`, then `hW.attachmentTime g b μ x = 0`. -/
theorem attachmentTime_of_forall_ne {x : M} (hx : ∀ t, g (hW.flow t x) ≠ 0) :
    hW.attachmentTime g b μ x = 0 := by
  rw [attachmentTime_def]
  refine indicator_of_notMem ?_ _
  rintro ⟨t, ht⟩
  exact hx t ht

/-- **The time function on the orbits of `g ⁻¹' {0}`.** If the orbit of `x` under the flow `Φ`
meets `g ⁻¹' {0}`, then, with `c = Flow.levelCrossingTime Φ g 0 x`, the time function at `x` is
`Flow.levelCrossingTime Φ f b (Φ c x) * μ (-c)`. -/
theorem attachmentTime_of_exists {x : M} (hx : ∃ t, g (hW.flow t x) = 0) :
    hW.attachmentTime g b μ x =
      Flow.levelCrossingTime hW.flow f b (hW.flow (Flow.levelCrossingTime hW.flow g 0 x) x) *
        μ (-Flow.levelCrossingTime hW.flow g 0 x) := by
  rw [attachmentTime_def, indicator_of_mem hx]

/-- **The time function along an orbit crossing `g ⁻¹' {0}`.** Let `g` be differentiable with
`dg(X) > 0` on `g ⁻¹' {0}`, and let `y` lie on `g ⁻¹' {0}`. Then the time function at the point
`Φ s y` of the orbit of `y` is `T y * μ s`, where `T y = Flow.levelCrossingTime Φ f b y` is the
time from `y` to the level `f ⁻¹' {b}`. -/
theorem attachmentTime_flow_apply (hg : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) g)
    (hgX : ∀ y, g y = 0 → 0 < mvfderiv 𝓘(ℝ, E) g y (X y)) {y : M} (hy : g y = 0) (s : ℝ) :
    hW.attachmentTime g b μ (hW.flow s y) = Flow.levelCrossingTime hW.flow f b y * μ s := by
  have hback : hW.flow (-s) (hW.flow s y) = y := hW.flow.map_neg_apply_map s y
  -- The orbit meets `g ⁻¹' {0}` only once, at `y`, so its crossing time from `Φ s y` is `-s`.
  have hc : Flow.levelCrossingTime hW.flow g 0 (hW.flow s y) = -s :=
    Flow.levelCrossingTime_eq_of_subsingleton
      (_root_.TauCeti.subsingleton_setOf_flow_apply_eq_of_mvfderiv_pos
        (hW.contMDiff_field.of_le (by simp)) hW.isCompleteVectorField hW.flowOf_eq_flow hg hgX _)
      (by rwa [hback])
  rw [hW.attachmentTime_of_exists ⟨-s, by rwa [hback]⟩, hc, hback, neg_neg]

/-- **The time function is nonnegative.** If `f < b` on `g ⁻¹' {0}` and `μ ≥ 0`, then
`0 ≤ hW.attachmentTime g b μ x` for every `x`: the level `f ⁻¹' {b}` is crossed in the future of
each point of `g ⁻¹' {0}`, since `f` increases along the orbits. -/
theorem attachmentTime_nonneg (hgb : ∀ y, g y = 0 → f y < b) (hμ : ∀ s, 0 ≤ μ s) (x : M) :
    0 ≤ hW.attachmentTime g b μ x := by
  rw [attachmentTime_def]
  exact indicator_nonneg (fun x hx ↦ mul_nonneg (Flow.levelCrossingTime_nonneg_of_monotone
    (hW.monotone_comp_flow _) (hgb _ (Flow.apply_flow_levelCrossingTime hx))) (hμ _)) x

/-- **The time function vanishes on the lower sublevel.** Let `δ` be such that the orbit of each
point `y` of `g ⁻¹' {0}` stays in `{a < f}` from time `-δ` on (as given by
`IsWeinsteinStructure.exists_pos_forall_lt_flow_apply`), and let `μ` vanish on `Iic (-δ)`.
Then `hW.attachmentTime g b μ x = 0` whenever `f x ≤ a`. -/
theorem attachmentTime_eq_zero_of_le {a δ : ℝ}
    (hδ : ∀ y, g y = 0 → ∀ s, -δ ≤ s → a < f (hW.flow s y)) (hμ : ∀ s ≤ -δ, μ s = 0) {x : M}
    (hx : f x ≤ a) : hW.attachmentTime g b μ x = 0 := by
  by_cases h : ∃ t, g (hW.flow t x) = 0
  swap
  · exact hW.attachmentTime_of_forall_ne fun t ht ↦ h ⟨t, ht⟩
  rw [hW.attachmentTime_of_exists h]
  -- `x = Φ (-c) y` with `y` on `g ⁻¹' {0}` and `f x ≤ a`, so the time `-c` is before `-δ`.
  have hle : -Flow.levelCrossingTime hW.flow g 0 x ≤ -δ := by
    refine le_of_not_gt fun hlt ↦ (hx.trans_lt ?_).false
    simpa only [Flow.map_neg_apply_map] using
      hδ _ (Flow.apply_flow_levelCrossingTime h) _ hlt.le
  rw [hμ _ hle, mul_zero]

/-- **The support of the time function.** The support of `τ = hW.attachmentTime g b μ` lies in
the image of `Function.support μ ×ˢ g ⁻¹' {0}` under `(s, y) ↦ Φ s y`: a point where `τ` does
not vanish is `Φ s y` for a point `y` of `g ⁻¹' {0}` and a time `s` with `μ s ≠ 0`. -/
theorem support_attachmentTime_subset :
    Function.support (hW.attachmentTime g b μ) ⊆
      (fun p : ℝ × M ↦ hW.flow p.1 p.2) '' (Function.support μ ×ˢ (g ⁻¹' {0})) := by
  intro x hx
  by_cases h : ∃ t, g (hW.flow t x) = 0
  swap
  · exact (hx (hW.attachmentTime_of_forall_ne fun t ht ↦ h ⟨t, ht⟩)).elim
  rw [Function.mem_support, hW.attachmentTime_of_exists h] at hx
  exact ⟨(-Flow.levelCrossingTime hW.flow g 0 x, hW.flow (Flow.levelCrossingTime hW.flow g 0 x) x),
    ⟨right_ne_zero_of_mul hx, Flow.apply_flow_levelCrossingTime h⟩,
    Flow.map_neg_apply_map _ _ _⟩

/-- **The closed support of the time function.** If `g ⁻¹' {0}` is compact and `μ` has compact
support, then the closed support of `τ = hW.attachmentTime g b μ` lies in the image of
`tsupport μ ×ˢ g ⁻¹' {0}` under `(s, y) ↦ Φ s y`, which is compact. -/
theorem tsupport_attachmentTime_subset (hg : IsCompact (g ⁻¹' {0})) (hμ : HasCompactSupport μ) :
    tsupport (hW.attachmentTime g b μ) ⊆
      (fun p : ℝ × M ↦ hW.flow p.1 p.2) '' (tsupport μ ×ˢ (g ⁻¹' {0})) :=
  closure_minimal (hW.support_attachmentTime_subset.trans
      (image_mono (prod_mono (subset_tsupport μ) subset_rfl)))
    ((hμ.isCompact.prod hg).image (hW.flow.continuous continuous_fst continuous_snd)).isClosed

/-- **The time function has compact support**, if `g ⁻¹' {0}` is compact and the bump `μ` has
compact support. -/
theorem hasCompactSupport_attachmentTime (hg : IsCompact (g ⁻¹' {0}))
    (hμ : HasCompactSupport μ) : HasCompactSupport (hW.attachmentTime g b μ) :=
  ((hμ.isCompact.prod hg).image
    (hW.flow.continuous continuous_fst continuous_snd)).of_isClosed_subset
      (isClosed_tsupport _) (hW.tsupport_attachmentTime_subset hg hμ)

/-- **The time function is smooth.** Let `b` be a regular value of `f`, let `g` be smooth with
`dg(X) > 0` along a compact level `g ⁻¹' {0}` whose points have orbits that meet `f ⁻¹' {b}`, and
let the bump `μ` be smooth with compact support. Then `τ = hW.attachmentTime g b μ` is smooth. -/
theorem contMDiff_attachmentTime (hb : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) f b)
    (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) (⊤ : ℕ∞) g)
    (hgX : ∀ y, g y = 0 → 0 < mvfderiv 𝓘(ℝ, E) g y (X y)) (hgc : IsCompact (g ⁻¹' {0}))
    (hgb : ∀ y, g y = 0 → ∃ t, f (hW.flow t y) = b)
    (hμ : ContDiff ℝ (⊤ : ℕ∞) μ) (hμc : HasCompactSupport μ) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) (⊤ : ℕ∞) (hW.attachmentTime g b μ) := by
  have hU : IsOpen {x | ∃ t, g (hW.flow t x) = 0} :=
    isOpen_setOf_exists_flow_apply_eq hW.isMIntegralCurve_flow hg.continuous
      fun x hx ↦ ⟨hg.mdifferentiableAt (by simp), hgX x hx⟩
  -- On the open set of orbits crossing `g ⁻¹' {0}`, `τ` is a product of smooth composites.
  have hT := (hW.contMDiffOn_levelCrossingTime_of_isRegularValue hb).comp
    (hW.contMDiffOn_flow_levelCrossingTime_of_mvfderiv_pos hg hgX) fun x hx ↦
      hgb _ (Flow.apply_flow_levelCrossingTime hx)
  have hc := hμ.contMDiff.comp_contMDiffOn
    (hW.contMDiffOn_levelCrossingTime_of_mvfderiv_pos hg hgX).neg
  have hon := (hT.mul hc).congr fun x hx ↦ hW.attachmentTime_of_exists (b := b) (μ := μ) hx
  -- The closed support of `τ` lies in that set, since `g (Φ (-s) (Φ s y)) = g y = 0`.
  refine contMDiff_of_tsupport fun x hx ↦ hon.contMDiffAt (hU.mem_nhds ?_)
  obtain ⟨⟨s, y⟩, ⟨-, hy⟩, rfl⟩ := hW.tsupport_attachmentTime_subset hgc hμc hx
  exact ⟨-s, by simpa only [Flow.map_neg_apply_map, mem_preimage, mem_singleton_iff] using hy⟩

/-- **The time change of the attachment moves forward along each orbit.** Let `g` be
differentiable with `dg(X) > 0` on `g ⁻¹' {0}`, let the time `T y` from each point `y` of
`g ⁻¹' {0}` to the level `f ⁻¹' {b}` lie in `[0, T₀]`, and let the bump `μ` be differentiable with
`-1 < T₀ * μ' s` for every `s`. Then `τ = hW.attachmentTime g b μ` satisfies `0 < 1 + dτ(X)` at
every point. -/
theorem one_add_mvfderiv_attachmentTime_pos (hg : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) g)
    (hgX : ∀ y, g y = 0 → 0 < mvfderiv 𝓘(ℝ, E) g y (X y)) {T₀ : ℝ}
    (hT : ∀ y, g y = 0 → Flow.levelCrossingTime hW.flow f b y ∈ Icc 0 T₀)
    (hμ : Differentiable ℝ μ) (hμT : ∀ s, -1 < T₀ * deriv μ s) (x : M) :
    0 < 1 + mvfderiv 𝓘(ℝ, E) (hW.attachmentTime g b μ) x (X x) := by
  by_cases hd : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ) (hW.attachmentTime g b μ) x
  swap
  · simp [mvfderiv_eq_zero_iff.2 (mfderiv_zero_of_not_mdifferentiableAt hd)]
  -- `dτ(X)` at `x` is the derivative of `τ` along the orbit of `x` at time `0`.
  have hτ : HasDerivAt (hW.attachmentTime g b μ ∘ fun t ↦ hW.flow t x)
      (mvfderiv 𝓘(ℝ, E) (hW.attachmentTime g b μ) x (X x)) 0 := by
    have hc := Manifold.hasDerivAt_comp_curve
      (γ := fun t ↦ hW.flow t x) (by rwa [Flow.map_zero_apply]) (hW.isMIntegralCurve_flow x 0)
    beta_reduce at hc
    rwa [Flow.map_zero_apply] at hc
  by_cases h : ∃ t, g (hW.flow t x) = 0
  swap
  · -- Off the orbits of `g ⁻¹' {0}`, `τ` vanishes along the whole orbit of `x`.
    have h0 : (hW.attachmentTime g b μ ∘ fun t ↦ hW.flow t x) = fun _ ↦ 0 := by
      ext t
      refine hW.attachmentTime_of_forall_ne fun s hs ↦ h ⟨s + t, ?_⟩
      rwa [Flow.map_add]
    rw [h0] at hτ
    rw [hτ.unique (hasDerivAt_const 0 0)]
    simp
  -- Otherwise `y = Φ c x` lies on `g ⁻¹' {0}`, and `τ (Φ t x) = T y * μ (t - c)`.
  set c := Flow.levelCrossingTime hW.flow g 0 x
  have hy := Flow.apply_flow_levelCrossingTime h
  have heq : (hW.attachmentTime g b μ ∘ fun t ↦ hW.flow t x) =
      fun t ↦ Flow.levelCrossingTime hW.flow f b (hW.flow c x) * μ (t + -c) := by
    ext t
    rw [Function.comp_apply, ← hW.attachmentTime_flow_apply hg hgX hy, ← Flow.map_add,
      neg_add_cancel_right]
  rw [heq] at hτ
  rw [hτ.unique ((((hμ _).hasDerivAt).comp_add_const 0 (-c)).const_mul _), zero_add]
  obtain ⟨h0, hT₀⟩ := hT _ hy
  rcases le_total 0 (deriv μ (-c)) with hμc | hμc
  · nlinarith [hμT (-c)]
  · nlinarith [hμT (-c)]

/-- **The time change of the attachment keeps `{g ≤ 0}` below `b`.** Let `g` be differentiable
with `dg(X) > 0` on `g ⁻¹' {0}` and `f < b` on `{g ≤ 0}`, let the orbit of each point of
`g ⁻¹' {0}` meet `f ⁻¹' {b}`, and let `μ ≤ 1`. Then, with `τ = hW.attachmentTime g b μ`, the
point `Φ (τ x) x` lies in `{f ≤ b}` for every `x` with `g x ≤ 0`. -/
theorem apply_flow_attachmentTime_le (hg : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) g)
    (hgX : ∀ y, g y = 0 → 0 < mvfderiv 𝓘(ℝ, E) g y (X y)) (hgb : ∀ x, g x ≤ 0 → f x < b)
    (hgf : ∀ y, g y = 0 → ∃ t, f (hW.flow t y) = b) (hμ : ∀ s, μ s ≤ 1) {x : M}
    (hx : g x ≤ 0) : f (hW.flow (hW.attachmentTime g b μ x) x) ≤ b := by
  by_cases h : ∃ t, g (hW.flow t x) = 0
  swap
  · rw [hW.attachmentTime_of_forall_ne fun t ht ↦ h ⟨t, ht⟩, Flow.map_zero_apply]
    exact (hgb x hx).le
  obtain ⟨t, ht⟩ := h
  obtain ⟨y, hy, s, rfl⟩ : ∃ y, g y = 0 ∧ ∃ s, x = hW.flow s y :=
    ⟨_, ht, _, (Flow.map_neg_apply_map _ _ _).symm⟩
  -- `x = Φ s y` with `s ≤ 0`, since `g > 0` after the crossing at `y`.
  have hs : s ≤ 0 := by
    refine le_of_not_gt fun hs ↦ hx.not_gt ?_
    refine IsMIntegralCurve.lt_apply_of_le_apply (hW.isMIntegralCurve_flow y)
      (hg.continuous.comp (hW.isMIntegralCurve_flow y).continuous)
      (fun t ht ↦ ⟨hg _, hgX _ ht⟩) (s := 0) ?_ hs
    rw [Flow.map_zero_apply, hy]
  have hT : 0 ≤ Flow.levelCrossingTime hW.flow f b y :=
    Flow.levelCrossingTime_nonneg_of_monotone (hW.monotone_comp_flow y) (hgb y hy.le)
  -- So `Φ (τ x) x = Φ (T y * μ s + s) y` with `T y * μ s + s ≤ T y`.
  rw [hW.attachmentTime_flow_apply hg hgX hy, ← Flow.map_add]
  refine (hW.monotone_comp_flow y (?_ : _ ≤ Flow.levelCrossingTime hW.flow f b y)).trans_eq
    (Flow.apply_flow_levelCrossingTime (hgf y hy))
  nlinarith [mul_le_mul_of_nonneg_left (hμ s) hT]

/-- **The time change of the attachment moves `{g > 0}` above `b`.** Let `b` be a regular value
of `f`, let `g` be differentiable with `dg(X) > 0` on `g ⁻¹' {0}` and `f < b` on `g ⁻¹' {0}`,
and let `{g < 0}` contain `{f ≤ a}` and the stable sets of the critical points of `f` in
`f ⁻¹' Icc a b`. Let `μ 0 = 1`, and let `τ = hW.attachmentTime g b μ` be differentiable with
`0 < 1 + dτ(X)` everywhere. Then the point `Φ (τ x) x` lies in `{b < f}` for every `x` with
`0 < g x`. -/
theorem lt_apply_flow_attachmentTime {a : ℝ} (hb : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) f b)
    (hg : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) g)
    (hgX : ∀ y, g y = 0 → 0 < mvfderiv 𝓘(ℝ, E) g y (X y))
    (hK : {x | f x ≤ a} ∪ ⋃ p ∈ criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Icc a b, hW.flow.stableSet p ⊆
      {x | g x < 0})
    (hgb : ∀ y, g y = 0 → f y < b) (hτ : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) (hW.attachmentTime g b μ))
    (hpos : ∀ y, 0 < 1 + mvfderiv 𝓘(ℝ, E) (hW.attachmentTime g b μ) y (X y)) (hμ0 : μ 0 = 1)
    {x : M} (hx : 0 < g x) : b < f (hW.flow (hW.attachmentTime g b μ x) x) := by
  have hf := hW.isGeneralizedMorse.contMDiff.mdifferentiable (by simp)
  by_cases h : ∃ t, g (hW.flow t x) = 0
  swap
  · -- Off the orbits of `g ⁻¹' {0}`, `Φ (τ x) x = x`, and `g > 0` along the whole orbit of `x`,
    -- whereas the backward orbit of a point of `{f ≤ b}` enters `{g < 0}`.
    rw [hW.attachmentTime_of_forall_ne fun t ht ↦ h ⟨t, ht⟩, Flow.map_zero_apply]
    refine lt_of_not_ge fun hxb ↦ ?_
    obtain ⟨t, -, ht⟩ := hW.exists_flow_apply_neg hg.continuous hK hxb
    obtain ⟨u, -, hu⟩ := intermediate_value_uIcc (a := t) (b := 0)
      ((hg.continuous.comp (hW.isMIntegralCurve_flow x).continuous).continuousOn)
      (mem_uIcc.2 (Or.inl ⟨ht.le, by simpa only [Function.comp_apply, Flow.map_zero_apply]
        using hx.le⟩))
    exact h ⟨u, hu⟩
  obtain ⟨t, ht⟩ := h
  obtain ⟨y, hy, s, rfl⟩ : ∃ y, g y = 0 ∧ ∃ s, x = hW.flow s y :=
    ⟨_, ht, _, (Flow.map_neg_apply_map _ _ _).symm⟩
  -- `x = Φ s y` with `0 < s`, since `g < 0` before the crossing at `y`.
  have hs : 0 < s := by
    refine lt_of_not_ge fun hs ↦ ?_
    rcases hs.lt_or_eq with hs | rfl
    · refine hx.not_gt (IsMIntegralCurve.apply_lt_of_apply_le (hW.isMIntegralCurve_flow y)
        (hg.continuous.comp (hW.isMIntegralCurve_flow y).continuous)
        (fun t ht ↦ ⟨hg _, hgX _ ht⟩) (t := 0) ?_ hs)
      rw [Flow.map_zero_apply, hy]
    · rw [Flow.map_zero_apply, hy] at hx
      exact hx.false
  set T := Flow.levelCrossingTime hW.flow f b y
  -- The reparametrization `r ↦ r + τ (Φ r y) = r + T * μ r` of the orbit of `y` is strictly
  -- increasing and takes the value `T` at `0`, so it is above `T` at `s`.
  have hmono : StrictMono fun r ↦ r + T * μ r := by
    have := strictMono_add_apply_globalFlow (hW.contMDiff_field.of_le (by simp))
      hW.isCompleteVectorField hτ hpos y
    simpa only [← hW.flow_def, hW.attachmentTime_flow_apply hg hgX hy] using this
  have hlt : T < s + T * μ s := by simpa [hμ0] using hmono hs
  obtain ⟨t, -, hft⟩ := hW.exists_flow_apply_eq_upper hK hy (hgb y hy)
  rw [hW.attachmentTime_flow_apply hg hgX hy, ← Flow.map_add, add_comm]
  refine IsMIntegralCurve.lt_apply_of_le_apply (hW.isMIntegralCurve_flow y)
    (hf.continuous.comp (hW.isMIntegralCurve_flow y).continuous)
    (fun t ht ↦ ⟨hf _, hW.isGradientLike.mvfderiv_apply_pos_of_isRegularValue hb ht⟩) ?_ hlt
  rw [Flow.apply_flow_levelCrossingTime ⟨t, hft⟩]

end IsWeinsteinStructure

namespace IsWeinsteinCobordism

variable {a b : ℝ}

/-- **The upper sublevel is the lower domain with handles attached.** Let `(ω, X, f)` be a
Weinstein cobordism between the regular levels `a < b`, with flow `Φ`, and let `g` be a smooth
function such that `X` points out of `{g ≤ 0}` along `g ⁻¹' {0}` (`0 < dg(X)` there),
`{g ≤ 0}` lies in `{f < b}`, and `{g < 0}` contains `{f ≤ a}` and the stable sets of the critical
points of `f` in `f ⁻¹' Icc a b`. Then there are a smooth compactly supported function `τ ≥ 0`,
vanishing on `{f ≤ a}`, and a diffeomorphism `Ψ` of `M` with `Ψ x = Φ (τ x) x`, that carries
`{g ≤ 0}` onto `{f ≤ b}`. -/
theorem exists_diffeomorph_image_sublevel_eq (hW : IsWeinsteinCobordism ω X f a b) {g : M → ℝ}
    (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) (⊤ : ℕ∞) g)
    (hgX : ∀ x, g x = 0 → 0 < mvfderiv 𝓘(ℝ, E) g x (X x))
    (hK : {x | f x ≤ a} ∪ ⋃ p ∈ criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Icc a b,
      hW.isWeinsteinStructure.flow.stableSet p ⊆ {x | g x < 0})
    (hgb : ∀ x, g x ≤ 0 → f x < b) :
    ∃ τ : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) (⊤ : ℕ∞) τ ∧ (∀ x, 0 ≤ τ x) ∧
      (∀ x, f x ≤ a → τ x = 0) ∧ HasCompactSupport τ ∧
      ∃ Ψ : M ≃ₘ^(⊤ : ℕ∞)⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ M,
        (∀ x, Ψ x = hW.isWeinsteinStructure.flow (τ x) x) ∧
        Ψ '' {x | g x ≤ 0} = {x | f x ≤ b} := by
  set hS := hW.isWeinsteinStructure
  have hgd : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) g := hg.mdifferentiable (by simp)
  have ha : {x | f x ≤ a} ⊆ {x | g x < 0} := subset_union_left.trans hK
  have hgc := hS.isCompact_preimage_zero hg.continuous ha fun x hx ↦ (hgb x hx.le).le
  have hgf (y : M) (hy : g y = 0) : ∃ t, f (hS.flow t y) = b :=
    (hS.exists_flow_apply_eq_upper hK hy (hgb y hy.le)).imp fun _ ht ↦ ht.2
  -- The margin `δ`, the bound `T₀` on the time from `g ⁻¹' {0}` to `f ⁻¹' {b}`, and the bump.
  obtain ⟨δ, hδ, hδa⟩ := hS.exists_pos_forall_lt_flow_apply hg.continuous ha
    fun x hx ↦ (hgb x hx.le).le
  obtain ⟨T, hT⟩ := hS.exists_forall_levelCrossingTime_mem_Ioc hW.isRegularValue_upper
    hg.continuous hK fun x hx ↦ hgb x hx.le
  have hTI (y : M) (hy : g y = 0) : Flow.levelCrossingTime hS.flow f b y ∈ Icc 0 (max T 0) :=
    ⟨(hT y hy).1.le, (hT y hy).2.trans (le_max_left _ _)⟩
  obtain ⟨μ, hμ, hμc, hμI, hμδ, -, hμ0, hμT⟩ :=
    exists_contDiff_bump_neg_one_lt_mul_deriv hδ (le_max_right T 0)
  have hτ := hS.contMDiff_attachmentTime hW.isRegularValue_upper hg hgX hgc hgf hμ hμc
  have hτc := hS.hasCompactSupport_attachmentTime (b := b) hgc hμc
  have hpos := hS.one_add_mvfderiv_attachmentTime_pos hgd hgX hTI
    (hμ.differentiable (by simp)) hμT
  let Ψ := globalFlowTimeChangeDiffeomorph hS.isCompleteVectorField le_top hS.contMDiff_field hτ
    (hτc.isCompact_range hτ.continuous).isBounded hpos
  have hΨ (x : M) : Ψ x = hS.flow (hS.attachmentTime g b μ x) x := by
    rw [globalFlowTimeChangeDiffeomorph_apply, hS.flow_def]
  refine ⟨hS.attachmentTime g b μ, hτ,
    hS.attachmentTime_nonneg (fun y hy ↦ hgb y hy.le) fun s ↦ (hμI s).1,
    fun x hx ↦ hS.attachmentTime_eq_zero_of_le hδa hμδ hx, hτc, Ψ, hΨ, ?_⟩
  -- `Ψ` maps `{g ≤ 0}` into `{f ≤ b}` and `{0 < g}` into `{b < f}`, and it is a bijection.
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_ofPred_eq, hΨ]
    exact hS.apply_flow_attachmentTime_le hgd hgX hgb hgf (fun s ↦ (hμI s).2) hx
  · intro hz
    obtain ⟨x, rfl⟩ : ∃ x, Ψ x = z := Ψ.surjective z
    rw [mem_ofPred_eq, hΨ] at hz
    refine ⟨x, mem_ofPred.2 (le_of_not_gt fun hx ↦ hz.not_gt ?_), rfl⟩
    exact hS.lt_apply_flow_attachmentTime hW.isRegularValue_upper hgd hgX hK
      (fun y hy ↦ hgb y hy.le) (hτ.mdifferentiable (by simp)) hpos hμ0 hx

end IsWeinsteinCobordism

end SymplecticGeometry

end
