/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Weinstein.Handle.Cobordism
public import SymplecticGeometry.Geometry.Symplectic.Weinstein.Handle.StableDisc
public import TauCeti.Dynamics.Flow.LevelCrossing
import SymplecticGeometry.Dynamics.Flow.Stable
import SymplecticGeometry.Geometry.Manifold.Flow.BandCrossing
import SymplecticGeometry.Geometry.Manifold.Flow.LevelCrossing
import SymplecticGeometry.Geometry.Symplectic.Weinstein.Handle.Linearization

/-!
# The stable set of a critical point in the lower level of a cobordism

Let `(ω, X, f)` be a Weinstein structure with flow `φ`, and `p` a nondegenerate critical point of
`f`. This file studies where the stable set of `p`, the set of points whose orbits tend to `p`,
meets a lower regular level `f ⁻¹' {a}`. It treats the critical points of Morse index zero,
the local minima of `f`: their stable set is the point itself, so it does not meet any level
other than `f ⁻¹' {f p}`.

It also builds the map that carries a point back along its orbit to the lower level. When `f` has
no critical point in `f ⁻¹' Ico a c`, as below the critical level `c` of an elementary cobordism,
the orbit of each point `x` with `a ≤ f x < c` meets `f ⁻¹' {a}` exactly once, at a time
`Flow.levelCrossingTime φ f a x ≤ 0`, and transversally. The map
`x ↦ φ (Flow.levelCrossingTime φ f a x) x` is smooth on `f ⁻¹' Ioo a c`, takes values in
`f ⁻¹' {a}`, and preserves the stable set of every point. Its derivative at a point `x` of that band
kills exactly the line through `X x`.

## Main declarations

* `SymplecticGeometry.IsWeinsteinStructure.stableSet_eq_singleton_of_manifoldMorseIndex_eq_zero`:
  the stable set of a nondegenerate critical point of index zero is `{p}`.
* `SymplecticGeometry.IsWeinsteinCobordism.stableSet_inter_preimage_eq_empty`: in a Weinstein
  cobordism between the levels `a` and `b`, the stable set of a nondegenerate critical point of
  index zero does not meet the lower level `f ⁻¹' {a}`.
* `SymplecticGeometry.IsWeinsteinStructure.exists_nonpos_flow_apply_eq`,
  `.subsingleton_setOf_flow_apply_eq` and `.eq_levelCrossingTime_iff`: the orbit of a point of
  `f ⁻¹' Ico a c` meets the level `f ⁻¹' {a}` exactly at the time
  `Flow.levelCrossingTime φ f a x`; `.levelCrossingTime_nonpos`: that time is nonpositive;
  `.mvfderiv_apply_pos_flow_levelCrossingTime`: the crossing is transverse.
* `SymplecticGeometry.IsWeinsteinStructure.mapsTo_flow_levelCrossingTime`,
  `.contMDiffOn_flow_levelCrossingTime` and `.mapsTo_flow_levelCrossingTime_stableSet`: the
  backward map to the lower level takes values in `f ⁻¹' {a}`, is smooth on `f ⁻¹' Ioo a c`, and
  sends a stable set into its part on the lower level.
* `SymplecticGeometry.IsWeinsteinStructure.contMDiffOn_levelCrossingTime` and
  `.mvfderiv_levelCrossingTime_apply_field`: the crossing time is smooth on `f ⁻¹' Ioo a c`,
  and decreases at unit speed along the orbits.
* `SymplecticGeometry.IsWeinsteinStructure.ker_mfderiv_flow_levelCrossingTime`: the kernel of the
  derivative of the backward map at `x` is the span of `X x`.

## Implementation notes

The stable subspace of the linearization of `X` at `p` has dimension the Morse index of `f` at
`p` (`TauCeti.IsGradientLike.finrank_stableSubspace_eq_manifoldMorseIndex`), so at index zero it
is trivial, and the local stable disc of
`SymplecticGeometry.IsWeinsteinStructure.exists_localStableDisc` is the point `p`. That disc
contains every point of the stable set in a neighbourhood `U` of `p` at which `f` exceeds
`f p - ε`. So near `p` the only point of the stable set is `p`, and since `p` is a rest point of
the flow, `Flow.stableSet_eq_singleton_of_eventually` makes the whole stable set `{p}`.
Tau Ceti's `Flow.stableSet_eq_singleton_of_antitone` does not apply here: it needs `p` to
be a global extremum of the function. The argument follows Tau Ceti's
`TauCeti.IsAdaptedPseudoGradient.unstableSet_eq_singleton_of_manifoldMorseIndex_eq_zero`, the
same statement for the unstable sets of the flow of an adapted pseudo-gradient of a Morse
function, with the local stable disc in place of its slice charts.

The second statement holds for every Weinstein cobordism, elementary or not, so it is stated for
`SymplecticGeometry.IsWeinsteinCobordism`, and dot notation finds it on an elementary one. It
needs no assumption that `p` lies in the region: a critical point on the level `a` would make `a`
a critical value
(`SymplecticGeometry.IsWeinsteinCobordism.criticalPoints_inter_subset_preimage_Ioo`).

The backward map is stated for a Weinstein structure and a band `f ⁻¹' Ico a c` free of critical
points; for an elementary cobordism, `exists_criticalPoints_inter_preimage_Ico_eq_empty` in the
namespace `SymplecticGeometry.IsElementaryWeinsteinCobordism` gives such a `c`. Neither
nondegeneracy nor the cobordism is needed. The backward orbit reaches the level `a` because the
band `f ⁻¹' Icc a (f x)` is compact, since `f` is proper, and the reversed field `-X` decreases
`f` on it, so that `SymplecticGeometry.exists_forall_isMIntegralCurve_apply_lt` applies to the
reversed orbit. It meets the level at most once by
`IsMIntegralCurve.subsingleton_setOf_apply_eq`, again on the reversed orbit. The smoothness is
the implicit function theorem at the regular level `a`, in the form of
`TauCeti.contMDiffOn_levelCrossingTime` for the crossing time, and not the continuity of
`Flow.levelCrossingTime` on a connecting set.

For the kernel, Tau Ceti's `TauCeti.mfderiv_flowOf_comp_prodMk_apply` writes the derivative of
the backward map at `x` as `w ↦ dτ(w) X + dφ_T(w)`, with `τ` the crossing time and `T = τ x`.
Since `dφ_T (X x) = X (φ_T x)` (`TauCeti.mfderiv_flowOf_apply_self`) and `dτ (X x) = -1`, the
vector `X x` is in the kernel. Conversely, if `w` is in the kernel, then `dφ_T` sends `w` and
`-dτ(w) X x` to the same vector, so they are equal, as `dφ_T` is injective
(`TauCeti.injective_mfderiv_flowOf`).

## References

* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  Chapter 11, on the stable manifolds of the critical points of a Weinstein structure
-/

public section

open Filter Set TauCeti
open scoped Manifold Topology

namespace SymplecticGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) (⊤ : ℕ∞) M]
  [T2Space M]
  {ω : SmoothTwoForm 𝓘(ℝ, E) M} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x} {f : M → ℝ}

/-- **The stable set of a minimum is a point.** Let `p` be a nondegenerate critical point of
Morse index zero of the function of a Weinstein structure `(ω, X, f)`. Then the only point whose
orbit under the flow of `X` tends to `p` is `p` itself. -/
theorem IsWeinsteinStructure.stableSet_eq_singleton_of_manifoldMorseIndex_eq_zero
    (hW : IsWeinsteinStructure ω X f) {p : M}
    (hp : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f p)
    (h0 : manifoldMorseIndex 𝓘(ℝ, E) f p = 0) :
    hW.flow.stableSet p = {p} := by
  set A : E →L[ℝ] E := sectionLinearization (F := E) 𝓘(ℝ, E) id X p
  have hXp := hW.mdifferentiableAt_field p
  have hS : A.stableSubspace = ⊥ := Submodule.finrank_eq_zero.1 <|
    (hW.isGradientLike.finrank_stableSubspace_eq_manifoldMorseIndex hp hXp rfl).trans h0
  have hfix (t : ℝ) : hW.flow t p = p :=
    hW.flow_apply_of_mvfderiv_eq_zero (mem_criticalPoints.1 hp.mem_criticalPoints) t
  obtain ⟨ι, ρ, -, hι0, -, -, ⟨U, hU, ε, hε, hcov⟩, -⟩ := hW.exists_localStableDisc hp rfl
  have hV : U ∩ {y | f p - ε < f y} ∈ 𝓝 p := inter_mem hU <|
    hW.isGeneralizedMorse.contMDiff.continuous.continuousAt.preimage_mem_nhds
      (Ioi_mem_nhds (by linarith))
  refine Flow.stableSet_eq_singleton_of_eventually hfix ?_
  filter_upwards [hV] with y hy hys
  obtain ⟨z, -, hz⟩ := hcov ⟨⟨hys, hy.1⟩, hy.2⟩
  have hz0 : z = 0 := Subtype.ext ((Submodule.mem_bot ℝ).1 (hS ▸ z.property))
  rw [hz0, hι0] at hz
  exact hz.symm

/-- **The stable set of a minimum misses the lower level.** In a Weinstein cobordism between the
levels `a` and `b`, the stable set of a nondegenerate critical point `p` of Morse index zero does
not meet the lower level `f ⁻¹' {a}`. -/
theorem IsWeinsteinCobordism.stableSet_inter_preimage_eq_empty {a b : ℝ}
    (hW : IsWeinsteinCobordism ω X f a b) {p : M}
    (hp : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f p)
    (h0 : manifoldMorseIndex 𝓘(ℝ, E) f p = 0) :
    hW.isWeinsteinStructure.flow.stableSet p ∩ f ⁻¹' {a} = ∅ := by
  rw [hW.isWeinsteinStructure.stableSet_eq_singleton_of_manifoldMorseIndex_eq_zero hp h0,
    singleton_inter_eq_empty, mem_preimage, mem_singleton_iff]
  intro hpa
  have hmem : p ∈ criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Icc a b :=
    ⟨hp.mem_criticalPoints, hpa.ge, hpa.le.trans hW.lt.le⟩
  exact (hW.criticalPoints_inter_subset_preimage_Ioo hmem).1.ne' hpa

/-! ### The backward map to the lower level -/

namespace IsWeinsteinStructure

variable (hW : IsWeinsteinStructure ω X f) {a c : ℝ} {x : M}

/-- **Backward orbits reach the lower level.** Let `(ω, X, f)` be a Weinstein structure, and let
`f` have no critical point in `f ⁻¹' Ico a c`. Then the orbit of every point `x` with
`a ≤ f x < c` meets the level `f ⁻¹' {a}` at some time `t ≤ 0`. -/
theorem exists_nonpos_flow_apply_eq (hc : criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Ico a c = ∅)
    (hx : f x ∈ Ico a c) : ∃ t ≤ 0, f (hW.flow t x) = a := by
  have hf := hW.isGeneralizedMorse.contMDiff
  -- On the compact band `f ⁻¹' Icc a (f x)`, the reversed field `-X` decreases `f`.
  have hneg : ∀ y, a ≤ f y → f y ≤ f x → mvfderiv 𝓘(ℝ, E) f y ((-X) y) < 0 := by
    intro y hay hyx
    have hy : y ∉ criticalPoints 𝓘(ℝ, E) f := fun h ↦
      eq_empty_iff_forall_notMem.1 hc y ⟨h, hay, hyx.trans_lt hx.2⟩
    rw [Pi.neg_apply, map_neg, neg_lt_zero]
    exact hW.isGradientLike.mvfderiv_apply_pos (by rwa [mem_criticalPoints] at hy)
  obtain ⟨T, hT0, hT⟩ := exists_forall_isMIntegralCurve_apply_lt
    hW.contMDiff_field.neg_section.continuous (hf.of_le (by simp)) hx.1
    (hW.isProperMap.isCompact_preimage isCompact_Icc) hneg
  have hlt : f (hW.flow (-T) x) < a := by
    simpa using hT _ (hW.isMIntegralCurve_flow x).comp_neg 0 T (by simp) (by simp)
  have hcont : Continuous fun t ↦ f (hW.flow t x) :=
    hf.continuous.comp (hW.isMIntegralCurve_flow x).continuous
  obtain ⟨t, ht, hta⟩ := intermediate_value_Icc (neg_nonpos.2 hT0) hcont.continuousOn
    ⟨hlt.le, by simpa using hx.1⟩
  exact ⟨t, ht.2, hta⟩

/-- **An orbit meets a regular level at most once.** For a regular value `a` of the function of a
Weinstein structure, the orbit of every point meets the level `f ⁻¹' {a}` at most once. -/
theorem subsingleton_setOf_flow_apply_eq (ha : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) f a) (x : M) :
    {t | f (hW.flow t x) = a}.Subsingleton := by
  -- Run the orbit backwards, so that `f` decreases along it.
  have h := (hW.isMIntegralCurve_flow x).comp_neg.subsingleton_setOf_apply_eq (f := f) (c := a)
    (fun _ ↦ hW.isGeneralizedMorse.contMDiff.mdifferentiableAt (by simp))
    (fun s t hst ↦ hW.monotone_comp_flow x (neg_le_neg hst)) fun t ht ↦ by
      rw [Pi.neg_apply, map_neg, neg_ne_zero]
      exact (hW.isGradientLike.mvfderiv_apply_pos_of_isRegularValue ha ht).ne'
  intro s hs t ht
  exact neg_inj.1 (h (show -s ∈ _ by simpa using hs) (show -t ∈ _ by simpa using ht))

/-- **The time of the crossing of the lower level.** Let `f` have no critical point in
`f ⁻¹' Ico a c`, and `a ≤ f x < c`. The times at which the orbit of `x` lies on the level
`f ⁻¹' {a}` are exactly the crossing time `Flow.levelCrossingTime hW.flow f a x`. -/
theorem eq_levelCrossingTime_iff (hc : criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Ico a c = ∅)
    (hx : f x ∈ Ico a c) {t : ℝ} :
    t = Flow.levelCrossingTime hW.flow f a x ↔ f (hW.flow t x) = a := by
  have ha : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) f a :=
    isRegularValue_iff_notMem_image_criticalPoints.2 fun ⟨y, hy, hya⟩ ↦
      eq_empty_iff_forall_notMem.1 hc y ⟨hy, hya.ge, hya.trans_lt (hx.1.trans_lt hx.2)⟩
  obtain ⟨s, -, hs⟩ := hW.exists_nonpos_flow_apply_eq hc hx
  have hlct := Flow.apply_flow_levelCrossingTime ⟨s, hs⟩
  exact ⟨fun h ↦ h ▸ hlct, fun h ↦ hW.subsingleton_setOf_flow_apply_eq ha x h hlct⟩

/-- **The crossing of the lower level is in the past.** If `f` has no critical point in
`f ⁻¹' Ico a c` and `a ≤ f x < c`, the orbit of `x` crosses the level `f ⁻¹' {a}` at a time
`t ≤ 0`. -/
theorem levelCrossingTime_nonpos (hc : criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Ico a c = ∅)
    (hx : f x ∈ Ico a c) : Flow.levelCrossingTime hW.flow f a x ≤ 0 := by
  obtain ⟨s, hs0, hs⟩ := hW.exists_nonpos_flow_apply_eq hc hx
  exact (hW.eq_levelCrossingTime_iff hc hx).2 hs ▸ hs0

/-- **The backward map lands in the lower level.** If `f` has no critical point in
`f ⁻¹' Ico a c`, the map `y ↦ φ (Flow.levelCrossingTime φ f a y) y`, for `φ` the flow, sends
`f ⁻¹' Ico a c` into the level `f ⁻¹' {a}`. -/
theorem mapsTo_flow_levelCrossingTime (hc : criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Ico a c = ∅) :
    MapsTo (fun y ↦ hW.flow (Flow.levelCrossingTime hW.flow f a y) y) (f ⁻¹' Ico a c)
      (f ⁻¹' {a}) :=
  fun _ hx ↦ (hW.eq_levelCrossingTime_iff hc hx).1 rfl

/-- **The crossing of the lower level is transverse.** If `f` has no critical point in
`f ⁻¹' Ico a c` and `a ≤ f x < c`, the field `X` increases `f` strictly at the point where the
orbit of `x` crosses the level `f ⁻¹' {a}`. -/
theorem mvfderiv_apply_pos_flow_levelCrossingTime
    (hc : criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Ico a c = ∅) (hx : f x ∈ Ico a c) :
    0 < mvfderiv 𝓘(ℝ, E) f (hW.flow (Flow.levelCrossingTime hW.flow f a x) x)
      (X (hW.flow (Flow.levelCrossingTime hW.flow f a x) x)) := by
  have hy : f (hW.flow (Flow.levelCrossingTime hW.flow f a x) x) = a :=
    hW.mapsTo_flow_levelCrossingTime hc hx
  refine hW.isGradientLike.mvfderiv_apply_pos fun h ↦ eq_empty_iff_forall_notMem.1 hc _
    ⟨mem_criticalPoints.2 h, hy.ge, ?_⟩
  exact hy.trans_lt (hx.1.trans_lt hx.2)

/-- **The crossing time of the lower level is smooth.** If `f` has no critical point in
`f ⁻¹' Ico a c`, the time `Flow.levelCrossingTime φ f a` at which the orbit of a point crosses the
level `f ⁻¹' {a}`, for `φ` the flow, is smooth on `f ⁻¹' Ioo a c`.

The proof uses the implicit function theorem at the regular level `a`, through
`TauCeti.contMDiffOn_levelCrossingTime`. -/
theorem contMDiffOn_levelCrossingTime (hc : criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Ico a c = ∅) :
    ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) (⊤ : ℕ∞) (Flow.levelCrossingTime hW.flow f a)
      (f ⁻¹' Ioo a c) := by
  have hIco {y : M} (hy : y ∈ f ⁻¹' Ioo a c) : f y ∈ Ico a c := Ioo_subset_Ico_self hy
  exact _root_.TauCeti.contMDiffOn_levelCrossingTime (n := ⊤) le_top hW.contMDiff_field
    hW.isCompleteVectorField hW.flowOf_eq_flow
    (isOpen_Ioo.preimage hW.isGeneralizedMorse.contMDiff.continuous)
    (fun _ hy _ hs _ ht ↦ ((hW.eq_levelCrossingTime_iff hc (hIco hy)).2 hs).trans
      ((hW.eq_levelCrossingTime_iff hc (hIco hy)).2 ht).symm)
    (fun _ hy ↦ ⟨_, hW.mapsTo_flow_levelCrossingTime hc (hIco hy)⟩)
    (fun _ _ ↦ hW.isGeneralizedMorse.contMDiff _)
    fun _ hy ↦ (hW.mvfderiv_apply_pos_flow_levelCrossingTime hc (hIco hy)).ne'

/-- **The backward map to the lower level is smooth.** If `f` has no critical point in
`f ⁻¹' Ico a c`, the map `y ↦ φ (Flow.levelCrossingTime φ f a y) y`, for `φ` the flow, which
follows the orbit of each point back to the level `f ⁻¹' {a}`, is smooth on `f ⁻¹' Ioo a c`. -/
theorem contMDiffOn_flow_levelCrossingTime
    (hc : criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Ico a c = ∅) :
    ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) (⊤ : ℕ∞)
      (fun y ↦ hW.flow (Flow.levelCrossingTime hW.flow f a y) y) (f ⁻¹' Ioo a c) := by
  intro y hy
  have h := contMDiffAt_flowOf_comp le_top hW.contMDiff_field
    ((hW.contMDiffOn_levelCrossingTime hc).contMDiffAt ((isOpen_Ioo.preimage
      hW.isGeneralizedMorse.contMDiff.continuous).mem_nhds hy)) contMDiffAt_id
    (hW.isCompleteVectorField.mem_flowDomain _ y)
  rw [hW.flowOf_eq_flow] at h
  exact h.contMDiffWithinAt

/-- **The crossing time decreases at unit speed along orbits.** If `f` has no critical point in
`f ⁻¹' Ico a c` and `a < f x < c`, the derivative at `x` of the crossing time
`Flow.levelCrossingTime φ f a` of the level `f ⁻¹' {a}`, in the direction of `X x`, is `-1`. -/
theorem mvfderiv_levelCrossingTime_apply_field
    (hc : criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Ico a c = ∅) (hx : f x ∈ Ioo a c) :
    mvfderiv 𝓘(ℝ, E) (Flow.levelCrossingTime hW.flow f a) x (X x) = -1 := by
  have hv : CMDiff 1 (fun y ↦ (⟨y, X y⟩ : TangentBundle 𝓘(ℝ, E) M)) :=
    hW.contMDiff_field.of_le (by simp)
  have hU : f ⁻¹' Ioo a c ∈ 𝓝 x :=
    (isOpen_Ioo.preimage hW.isGeneralizedMorse.contMDiff.continuous).mem_nhds hx
  have hτ : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ) (Flow.levelCrossingTime hW.flow f a) x :=
    ((hW.contMDiffOn_levelCrossingTime hc).contMDiffAt hU).mdifferentiableAt (by simp)
  have hcurve := hasDerivAt_comp_flowOf hv (mem_flowDomain_zero hv x)
    (by rwa [flowOf_zero X])
  rw [flowOf_zero X] at hcurve
  -- Near `s = 0`, the point `φ s x` stays in the band, and its crossing time is `τ x - s`.
  have hev : ∀ᶠ s in 𝓝 (0 : ℝ), Flow.levelCrossingTime hW.flow f a (flowOf X s x) =
      Flow.levelCrossingTime hW.flow f a x - s := by
    have hcont : Continuous fun s ↦ hW.flow s x := (hW.isMIntegralCurve_flow x).continuous
    filter_upwards [hcont.continuousAt.preimage_mem_nhds (by simpa using hU)] with s hs
    rw [hW.flowOf_eq_flow]
    refine ((hW.eq_levelCrossingTime_iff hc (Ioo_subset_Ico_self hs)).2 ?_).symm
    rw [← Flow.map_add, sub_add_cancel]
    exact hW.mapsTo_flow_levelCrossingTime hc (Ioo_subset_Ico_self hx)
  refine hcurve.unique ?_
  simpa using ((hasDerivAt_id' (0 : ℝ)).const_sub
    (Flow.levelCrossingTime hW.flow f a x)).congr_of_eventuallyEq hev

/-- **The kernel of the derivative of the backward map.** If `f` has no critical point in
`f ⁻¹' Ico a c` and `a < f x < c`, the derivative at `x` of the map
`y ↦ φ (Flow.levelCrossingTime φ f a y) y` to the lower level, for `φ` the flow, has kernel the
line spanned by `X x`. -/
theorem ker_mfderiv_flow_levelCrossingTime
    (hc : criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Ico a c = ∅) (hx : f x ∈ Ioo a c) :
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E)
      (fun y ↦ hW.flow (Flow.levelCrossingTime hW.flow f a y) y) x).ker = ℝ ∙ X x := by
  have hv : CMDiff 1 (fun y ↦ (⟨y, X y⟩ : TangentBundle 𝓘(ℝ, E) M)) :=
    hW.contMDiff_field.of_le (by simp)
  have hU : f ⁻¹' Ioo a c ∈ 𝓝 x :=
    (isOpen_Ioo.preimage hW.isGeneralizedMorse.contMDiff.continuous).mem_nhds hx
  set τ := Flow.levelCrossingTime hW.flow f a
  have hτ : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ) τ x :=
    ((hW.contMDiffOn_levelCrossingTime hc).contMDiffAt hU).mdifferentiableAt (by simp)
  have hdom := hW.isCompleteVectorField.mem_flowDomain (τ x) x
  -- The derivative of the backward map is `w ↦ dτ(w) X + dφ_{τ x}(w)`.
  have hD (w : TangentSpace 𝓘(ℝ, E) x) :
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun y ↦ hW.flow (τ y) y) x w =
        mvfderiv 𝓘(ℝ, E) τ x w • X (hW.flow (τ x) x) +
          mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (hW.flow (τ x)) x w := by
    have h := mfderiv_flowOf_comp_prodMk_apply (f := id) hv hτ mdifferentiableAt_id hdom w
    rwa [mfderiv_id, ContinuousLinearMap.id_apply, hW.flowOf_eq_flow] at h
  have hinj := hW.flowOf_eq_flow ▸ injective_mfderiv_flowOf hv hW.isCompleteVectorField (τ x) x
  have hX := hW.flowOf_eq_flow ▸ mfderiv_flowOf_apply_self hv hdom
  ext w
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, Submodule.mem_span_singleton, hD]
  constructor
  · -- Then `dφ_{τ x}` sends `w` and `-dτ(w) X x` to the same vector, and it is injective.
    intro h
    refine ⟨-mvfderiv 𝓘(ℝ, E) τ x w, hinj ?_⟩
    rw [map_smul, hX]
    exact (neg_smul _ _).trans (eq_neg_of_add_eq_zero_right h).symm
  · rintro ⟨r, rfl⟩
    rw [map_smul, map_smul, hX, hW.mvfderiv_levelCrossingTime_apply_field hc hx]
    simp only [smul_eq_mul, mul_neg, mul_one, neg_smul, neg_add_cancel]

/-- **The backward map preserves stable sets.** If `f` has no critical point in `f ⁻¹' Ico a c`,
the map `y ↦ φ (Flow.levelCrossingTime φ f a y) y`, for `φ` the flow, sends the points of the
stable set of `p` in `f ⁻¹' Ico a c` to points of that stable set on the level `f ⁻¹' {a}`. -/
theorem mapsTo_flow_levelCrossingTime_stableSet
    (hc : criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Ico a c = ∅) (p : M) :
    MapsTo (fun y ↦ hW.flow (Flow.levelCrossingTime hW.flow f a y) y)
      (hW.flow.stableSet p ∩ f ⁻¹' Ico a c) (hW.flow.stableSet p ∩ f ⁻¹' {a}) :=
  fun _ hx ↦ ⟨Flow.isInvariant_stableSet _ _ _ hx.1, hW.mapsTo_flow_levelCrossingTime hc hx.2⟩

end IsWeinsteinStructure

end SymplecticGeometry

end
