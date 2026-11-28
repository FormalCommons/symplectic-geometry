/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Weinstein.Handle.StableDisc
public import TauCeti.Dynamics.Flow.LevelCrossing
import SymplecticGeometry.Dynamics.Flow.LevelCrossing
import SymplecticGeometry.Geometry.Manifold.IntegralCurve.Monotone
import SymplecticGeometry.Geometry.Manifold.Morse.GradientLike
import TauCeti.Topology.Compactness.Normed

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

Fact (1) needs no statement of its own: it is the library's
`IsMIntegralCurve.lt_apply_of_le_apply`, `IsMIntegralCurve.apply_lt_of_apply_le` and
`IsMIntegralCurve.subsingleton_setOfPred_apply_eq_of_mvfderiv_pos`, applied to the orbit
`hW.isMIntegralCurve_flow x` of `Φ`.
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
  have hfX (x : M) (hx : f x = b) :
      MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ) f x ∧ 0 < mvfderiv 𝓘(ℝ, E) f x (X x) :=
    ⟨hW.isGeneralizedMorse.contMDiff.mdifferentiableAt (by simp),
      hW.isGradientLike.mvfderiv_apply_pos_of_isRegularValue hb hx⟩
  -- The orbit of a point of `g ⁻¹' {0}` meets `f ⁻¹' {b}` exactly once, at a positive time.
  have hcross (x : M) (hx : g x = 0) :
      ∃ t, 0 < t ∧ f (hW.flow t x) = b ∧ Flow.levelCrossingTime hW.flow f b x = t := by
    obtain ⟨t, ht, hft⟩ := hW.exists_flow_apply_eq_upper hK hx (hgb x hx)
    exact ⟨t, ht, hft, Flow.levelCrossingTime_eq_of_subsingleton
      ((hW.isMIntegralCurve_flow x).subsingleton_setOfPred_apply_eq_of_mvfderiv_pos
        (hW.isGeneralizedMorse.contMDiff.continuous.comp (hW.isMIntegralCurve_flow x).continuous)
        (fun _ ↦ hfX _)) hft⟩
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

/-- **The time function along an orbit crossing `g ⁻¹' {0}`.** Let `g` be differentiable with
`dg(X) > 0` on `g ⁻¹' {0}`, and let `y` lie on `g ⁻¹' {0}`. Then the time function at the point
`Φ s y` of the orbit of `y` is `T y * μ s`, where `T y = Flow.levelCrossingTime Φ f b y` is the
time from `y` to the level `f ⁻¹' {b}`. -/
theorem attachmentTime_flow_apply (hg : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) g)
    (hgX : ∀ y, g y = 0 → 0 < mvfderiv 𝓘(ℝ, E) g y (X y)) {y : M} (hy : g y = 0) (s : ℝ) :
    hW.attachmentTime g b μ (hW.flow s y) = Flow.levelCrossingTime hW.flow f b y * μ s := by
  have hback : hW.flow (-s) (hW.flow s y) = y := by
    rw [← Flow.map_add, neg_add_cancel, Flow.map_zero_apply]
  -- The orbit meets `g ⁻¹' {0}` only once, at `y`, so its crossing time from `Φ s y` is `-s`.
  have hc : Flow.levelCrossingTime hW.flow g 0 (hW.flow s y) = -s :=
    Flow.levelCrossingTime_eq_of_subsingleton
      ((hW.isMIntegralCurve_flow _).subsingleton_setOfPred_apply_eq_of_mvfderiv_pos
        (hg.continuous.comp (hW.isMIntegralCurve_flow _).continuous) fun _ h ↦ ⟨hg _, hgX _ h⟩)
      (by rwa [hback])
  rw [attachmentTime_def, indicator_of_mem, hc, hback, neg_neg]
  exact ⟨-s, by rwa [hback]⟩

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
  rw [attachmentTime_def]
  refine indicator_apply_eq_zero.2 fun h ↦ ?_
  -- `x = Φ (-c) y` with `y` on `g ⁻¹' {0}` and `f x ≤ a`, so the time `-c` is before `-δ`.
  have hle : -Flow.levelCrossingTime hW.flow g 0 x ≤ -δ := by
    refine le_of_not_gt fun hlt ↦ (hx.trans_lt ?_).false
    simpa only [← Flow.map_add, neg_add_cancel, Flow.map_zero_apply] using
      hδ _ (Flow.apply_flow_levelCrossingTime h) _ hlt.le
  rw [hμ _ hle, mul_zero]

end IsWeinsteinStructure

end SymplecticGeometry

end
