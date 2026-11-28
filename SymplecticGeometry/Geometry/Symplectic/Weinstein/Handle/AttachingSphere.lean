/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Weinstein.Handle.Cobordism
public import SymplecticGeometry.Geometry.Symplectic.Weinstein.Handle.StableDisc
public import TauCeti.Dynamics.Flow.LevelCrossing
public import Mathlib.Geometry.Manifold.Instances.Sphere
public import Mathlib.Geometry.Manifold.SmoothEmbedding
public import TauCeti.Geometry.Manifold.Distribution.Horizontal
import SymplecticGeometry.Dynamics.Flow.LevelCrossing
import SymplecticGeometry.Dynamics.Flow.Stable
import SymplecticGeometry.Geometry.Manifold.Flow.BandCrossing
import SymplecticGeometry.Geometry.Manifold.Flow.LevelCrossing
import SymplecticGeometry.Geometry.Manifold.IntegralCurve.Monotone
import SymplecticGeometry.Geometry.Manifold.RegularValue.SublevelBoundary
import SymplecticGeometry.Geometry.Symplectic.Weinstein.Handle.Linearization
import SymplecticGeometry.Geometry.Manifold.VectorField.Pullback
import TauCeti.Geometry.Manifold.Immersion.Differential
import TauCeti.Geometry.Manifold.MFDeriv.Slice
import TauCeti.Geometry.Manifold.MFDeriv.Basic

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

Finally, it prepares the sphere that will be the attaching sphere of `p` inside the local stable
disc. For a disc `ι` with a left inverse on the ball of radius `ρ`, as given by
`exists_localStableDisc`, an injective continuous linear map `L` and `0 < s` with
`s * ‖L‖ < ρ`, the map `u ↦ ι (s • L u)` on the unit sphere is a smooth injective immersion
into the stable set of `p`, below the level `f p`, that meets no critical point. On the stable
subspace, `L` can be taken from
`TauCeti.IsGradientLike.exists_continuousLinearEquiv_stableSubspace`.

With that choice, at index `m + 1`, the sphere is the level `-H = s ^ 2` of the Hessian form `H`
of `f` at `p`, read on the disc; `X` is transverse to it, and the orbit of every point `x ≠ p` of
the stable set meets it exactly once. Taking `s` small enough puts the sphere above any given
level `a < f p`, so that the backward map to the level `a` is smooth near it.

When `f` has no critical point in `f ⁻¹' Ico a (f p)`, as in an elementary cobordism between the
levels `a` and `b`, the backward map carries that sphere to the level `f ⁻¹' {a}`. The result is
a smooth injective immersion of the sphere whose image is the part of the stable set of `p` on
that level.

Last, for a regular value `a`, the boundary of the Weinstein domain `{x | f x ≤ a}` carries the
contact form `fillingContactForm` of its filling. Any map into that boundary whose image in `M`
lies in the stable set of `p` is horizontal for the kernel of this contact form.

Together, these give the attaching sphere of `p` in an elementary cobordism: a smooth embedding
of the sphere into the boundary of `{x | f x ≤ a}`, onto the part of the stable set of `p` on
that level, and horizontal for its contact form.

## Main declarations

* `SymplecticGeometry.IsWeinsteinStructure.stableSet_eq_singleton_of_manifoldMorseIndex_eq_zero`:
  the stable set of a nondegenerate critical point of index zero is `{p}`.
* `SymplecticGeometry.IsWeinsteinCobordism.stableSet_inter_preimage_eq_empty`: in a Weinstein
  cobordism between the levels `a` and `b`, the stable set of a nondegenerate critical point of
  index zero does not meet the lower level `f ⁻¹' {a}`.
* `SymplecticGeometry.IsWeinsteinStructure.exists_nonpos_flow_apply_eq` and
  `.eq_levelCrossingTime_iff`: the orbit of a point of `f ⁻¹' Ico a c` meets the level
  `f ⁻¹' {a}` exactly at the time `Flow.levelCrossingTime φ f a x`; `.levelCrossingTime_nonpos`:
  that time is nonpositive; `.mvfderiv_apply_pos_flow_levelCrossingTime`: the crossing is
  transverse.
* `SymplecticGeometry.IsWeinsteinStructure.mapsTo_flow_levelCrossingTime`,
  `.contMDiffOn_flow_levelCrossingTime` and `.mapsTo_flow_levelCrossingTime_stableSet`: the
  backward map to the lower level takes values in `f ⁻¹' {a}`, is smooth on `f ⁻¹' Ioo a c`, and
  sends a stable set into its part on the lower level.
* `SymplecticGeometry.IsWeinsteinStructure.ker_mfderiv_flow_levelCrossingTime`: the kernel of the
  derivative of the backward map at `x` is the span of `X x`.
* `SymplecticGeometry.contMDiff_comp_smul_coe_sphere`, `.injective_comp_smul_coe_sphere` and
  `.injective_mfderiv_comp_smul_coe_sphere`: a sphere scaled into the ball on which a disc is an
  immersion with a left inverse is a smooth injective immersion;
  `SymplecticGeometry.IsWeinsteinStructure.range_comp_smul_coe_sphere_subset`: for the local
  stable disc, it lies in the stable set, below `f p`, off the critical points.
* `SymplecticGeometry.IsWeinsteinStructure.exists_sphere_existsUnique_flow_apply_mem_range`: at
  index `m + 1` and for each level `a < f p`, a smoothly immersed sphere in the stable set
  above `a`, transverse to `X`, that every orbit of the stable set other than `p` meets exactly
  once.
* `SymplecticGeometry.IsWeinsteinStructure.exists_le_flow_apply_notMem_of_isCompact` and
  `.exists_flow_apply_mem_diff_of_isCompact`: the backward orbit of a point `x ≠ p` of the stable
  set leaves each compact part `K` of it, so an orbit that reaches an open set `G` whose points
  of the stable set lie in `K` passes through `K \ G`.
* `SymplecticGeometry.IsWeinsteinStructure.exists_sphere_range_eq_stableSet_inter_preimage`: at
  index `m + 1`, for a level `a < f p` with no critical point in `f ⁻¹' Ico a (f p)`, a smooth
  injective immersion of the unit sphere onto the part of the stable set of `p` on the level `a`;
  the version in the namespace `SymplecticGeometry.IsElementaryWeinsteinCobordism` states it for
  the lower level of an elementary Weinstein cobordism between `a` and `b`.
* In the namespace `SymplecticGeometry.IsWeinsteinStructure`,
  `isHorizontalMap_kerDistribution_fillingContactForm_of_range_subset_stableSet`: a map into the
  boundary of a regular sublevel, with image in the stable set of a nondegenerate critical point,
  is horizontal for the contact form of that boundary.
* `SymplecticGeometry.IsElementaryWeinsteinCobordism.exists_attachingSphere`: in an elementary
  Weinstein cobordism between `a` and `b`, a nondegenerate critical point of index `m + 1` has an
  attaching sphere, a smooth embedding of the unit sphere into the boundary of `{x | f x ≤ a}`
  whose image in `M` is its stable set on the level `a`, horizontal for the contact form.

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
`IsMIntegralCurve.subsingleton_setOfPred_apply_eq_of_mvfderiv_pos` applied to the orbit, with
`g = f`, since `df(X) > 0` on a regular level. The smoothness is the implicit function theorem
at the regular level `a`, in the form of
`SymplecticGeometry.IsWeinsteinStructure.contMDiffOn_flow_levelCrossingTime_of_mvfderiv_pos`
with `g = f`, and not the continuity of `Flow.levelCrossingTime` on a connecting set.

The kernel is `TauCeti.ker_mfderiv_flow_levelCrossingTime`. Its hypotheses are checked one by
one: near `x` each orbit meets the level `a` at most once, by
`SymplecticGeometry.IsWeinsteinStructure.eq_levelCrossingTime_iff`; the orbit of `x` reaches the
level, by `SymplecticGeometry.IsWeinsteinStructure.mapsTo_flow_levelCrossingTime`; and
`df(X) ≠ 0` at the point where it does, by
`SymplecticGeometry.IsWeinsteinStructure.mvfderiv_apply_pos_flow_levelCrossingTime`.

The immersion is the chain rule with Mathlib's `injective_mvfderiv_subtypeVal_sphere` for the
inclusion of the sphere, and injectivity comes from the left inverse of the disc. That the
sphere lies below `f p` and off the critical points is
`SymplecticGeometry.IsWeinsteinStructure.apply_lt_of_mem_stableSet` and
`SymplecticGeometry.IsWeinsteinStructure.notMem_criticalPoints_of_mem_stableSet`.

For the crossing, take the left inverse `π` of the disc and `L` the isometry
from `EuclideanSpace ℝ (Fin (m + 1))` with the inner product `-H` on the stable subspace, so that
`-H (π y) (π y) = ‖L⁻¹ (π y)‖ ^ 2`. Two crossings are impossible because `-H ∘ π` decreases
strictly along the orbits of the disc near `p`
(`SymplecticGeometry.IsWeinsteinStructure.LocalStableDisc.exists_forall_flow_strictAntiOn`).
Transversality holds for the same reason: `-H ∘ π` is constant on the sphere, so its
differential vanishes on the tangent vectors of the sphere
(`TauCeti.mfderiv_mfderiv_apply_eq_zero_of_comp_eventuallyEq_const`), while it is negative on
`X`. For the existence of a crossing, the orbit of `x` ends in the part of the disc strictly
inside the sphere, and its backward orbit leaves the compact cap bounded by the sphere: `f`
increases at a rate bounded below along it on that cap, which has no critical point below `f p`,
while `f` is bounded below there.
Since an interval is connected, the orbit meets the sphere between a time at which it is outside
the cap and a later time at which it is strictly inside the sphere. The sphere lies above the
level `a` because `ι` is continuous at `0`, with `ι 0 = p` and `a < f p`, so that a small
enough scale keeps it in the open set `f ⁻¹' Ioi a`.

When the band `f ⁻¹' Ico a (f p)` is free of critical points, the backward map `B` to the level
`a` is smooth near the sphere `σ` chosen above `a`, and `B ∘ σ` is the sphere in the level `a`.
It is immersed because the kernel of the differential of `B` is the line of `X`, which is
transverse to `σ`. It is injective because two points of `σ` with the same image under `B` lie
on one orbit, which crosses `σ` only once. It is onto the part of the stable set on the level
`a`: the orbit of such a point `y` crosses `σ` at some `σ u`, and `B` carries `σ u` back to
`y` since the orbit meets the level `a` only once. In an elementary cobordism, the critical level
`c = f p` bounds such a band, so the elementary version is a corollary.

For horizontality, the contact form at a boundary point `w` of the sublevel is `-ι_Y σ`, with
`σ` and `Y` the pullbacks of `ω` and `X` along the inclusion `ι` of the sublevel into `M`. Since
the differential of `ι` is invertible, it sends `Y w` to `X (ι w)`, so `ι_Y σ` is the pullback of
`ι_X ω` along `ι` (`TauCeti.mpullback_interior_at`). With the chain rule, the contact form on a
tangent vector of the map is `ι_X ω` on its image in `M`, which vanishes by
`SymplecticGeometry.IsWeinsteinStructure.interior_apply_mfderiv_eq_zero_of_range_subset_stableSet`.
No smoothness of the map is needed: where it is not differentiable, its differential is zero.

The attaching sphere lifts the injective immersion `τ` into the level `a` to the boundary of the
sublevel, which is that level (`TauCeti.boundary_scalarRegularSublevel`). Tau Ceti's
`ContMDiff.isImmersion_of_injective_mfderiv` makes `τ` an immersion, and since the sphere is
compact, the lift is a smooth embedding by
`TauCeti.isSmoothEmbedding_of_isImmersion_comp_coe_boundary_scalarRegularSublevel`.

## References

* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  Lemma 11.13 (a): the one-form `ι_X ω` vanishes on the stable manifold of a critical point of a
  Weinstein structure, so that its intersection with a regular level is isotropic for the contact
  structure there
-/

public section

open Filter Function Metric Module Set TauCeti
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
  obtain ⟨D⟩ := hW.exists_localStableDisc hp rfl
  obtain ⟨U, hU, ε, hε, hcov⟩ := D.exists_stableSet_inter_subset_image_ball
  have hV : U ∩ {y | f p - ε < f y} ∈ 𝓝 p := inter_mem hU <|
    hW.isGeneralizedMorse.contMDiff.continuous.continuousAt.preimage_mem_nhds
      (Ioi_mem_nhds (by linarith))
  refine Flow.stableSet_eq_singleton_of_eventually hfix ?_
  filter_upwards [hV] with y hy hys
  obtain ⟨z, -, hz⟩ := hcov ⟨⟨hys, hy.1⟩, hy.2⟩
  have hz0 : z = 0 := Subtype.ext ((Submodule.mem_bot ℝ).1 (hS ▸ z.property))
  rw [hz0, D.ι_zero] at hz
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
    hf.continuous.comp (hW.flow.continuous_eval_const x)
  obtain ⟨t, ht, hta⟩ := intermediate_value_Icc (neg_nonpos.2 hT0) hcont.continuousOn
    ⟨hlt.le, by simpa using hx.1⟩
  exact ⟨t, ht.2, hta⟩

/-- **The time of the crossing of the lower level.** Let `f` have no critical point in
`f ⁻¹' Ico a c`, and `a ≤ f x < c`. The times at which the orbit of `x` lies on the level
`f ⁻¹' {a}` are exactly the crossing time `Flow.levelCrossingTime hW.flow f a x`. -/
theorem eq_levelCrossingTime_iff (hc : criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Ico a c = ∅)
    (hx : f x ∈ Ico a c) {t : ℝ} :
    t = Flow.levelCrossingTime hW.flow f a x ↔ f (hW.flow t x) = a := by
  obtain ⟨s, -, hs⟩ := hW.exists_nonpos_flow_apply_eq hc hx
  have hf := hW.isGeneralizedMorse.contMDiff
  exact ⟨fun h ↦ h ▸ Flow.apply_flow_levelCrossingTime ⟨s, hs⟩, fun h ↦
    (Flow.levelCrossingTime_eq_of_subsingleton
      ((hW.isMIntegralCurve_flow x).subsingleton_setOfPred_apply_eq_of_mvfderiv_pos
        (hf.continuous.comp (hW.isMIntegralCurve_flow x).continuous)
        (fun _ hy ↦ ⟨hf.mdifferentiableAt (by simp),
          hW.isGradientLike.mvfderiv_apply_pos_of_criticalPoints_inter_preimage_Ico_eq_empty
            (hx.1.trans_lt hx.2) hc hy⟩)) h).symm⟩

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
      (X (hW.flow (Flow.levelCrossingTime hW.flow f a x) x)) :=
  hW.isGradientLike.mvfderiv_apply_pos_of_criticalPoints_inter_preimage_Ico_eq_empty
    (hx.1.trans_lt hx.2) hc (hW.mapsTo_flow_levelCrossingTime hc hx)

/-- **The backward map to the lower level is smooth.** If `f` has no critical point in
`f ⁻¹' Ico a c`, the map `y ↦ φ (Flow.levelCrossingTime φ f a y) y`, for `φ` the flow, which
follows the orbit of each point back to the level `f ⁻¹' {a}`, is smooth on `f ⁻¹' Ioo a c`.

The proof uses the implicit function theorem at the regular level `a`, through the library's
`SymplecticGeometry.IsWeinsteinStructure.contMDiffOn_flow_levelCrossingTime_of_mvfderiv_pos`. -/
theorem contMDiffOn_flow_levelCrossingTime
    (hc : criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Ico a c = ∅) :
    ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) (⊤ : ℕ∞)
      (fun y ↦ hW.flow (Flow.levelCrossingTime hW.flow f a y) y) (f ⁻¹' Ioo a c) := fun x hx ↦
  (hW.contMDiffOn_flow_levelCrossingTime_of_mvfderiv_pos hW.isGeneralizedMorse.contMDiff
    (fun _ ↦ hW.isGradientLike.mvfderiv_apply_pos_of_criticalPoints_inter_preimage_Ico_eq_empty
      (hx.1.trans hx.2) hc) x
    ⟨_, hW.mapsTo_flow_levelCrossingTime hc (Ioo_subset_Ico_self hx)⟩).mono
      fun _ hy ↦ ⟨_, hW.mapsTo_flow_levelCrossingTime hc (Ioo_subset_Ico_self hy)⟩

/-- **The kernel of the derivative of the backward map.** If `f` has no critical point in
`f ⁻¹' Ico a c` and `a < f x < c`, the derivative at `x` of the map
`y ↦ φ (Flow.levelCrossingTime φ f a y) y` to the lower level, for `φ` the flow, has kernel the
line spanned by `X x`. -/
theorem ker_mfderiv_flow_levelCrossingTime
    (hc : criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Ico a c = ∅) (hx : f x ∈ Ioo a c) :
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E)
      (fun y ↦ hW.flow (Flow.levelCrossingTime hW.flow f a y) y) x).ker = ℝ ∙ X x := by
  have hIco {y : M} (hy : y ∈ f ⁻¹' Ioo a c) : f y ∈ Ico a c := Ioo_subset_Ico_self hy
  exact _root_.TauCeti.ker_mfderiv_flow_levelCrossingTime (hW.contMDiff_field.of_le (by simp))
    hW.isCompleteVectorField hW.flowOf_eq_flow
    (eventually_of_mem ((isOpen_Ioo.preimage hW.isGeneralizedMorse.contMDiff.continuous).mem_nhds
      hx) fun _ hy _ hs _ ht ↦ ((hW.eq_levelCrossingTime_iff hc (hIco hy)).2 hs).trans
        ((hW.eq_levelCrossingTime_iff hc (hIco hy)).2 ht).symm)
    ⟨_, hW.mapsTo_flow_levelCrossingTime hc (hIco hx)⟩
    ((hW.isGeneralizedMorse.contMDiff _).of_le (by simp))
    (hW.mvfderiv_apply_pos_flow_levelCrossingTime hc (hIco hx)).ne'

/-- **The backward map preserves stable sets.** If `f` has no critical point in `f ⁻¹' Ico a c`,
the map `y ↦ φ (Flow.levelCrossingTime φ f a y) y`, for `φ` the flow, sends the points of the
stable set of `p` in `f ⁻¹' Ico a c` to points of that stable set on the level `f ⁻¹' {a}`. -/
theorem mapsTo_flow_levelCrossingTime_stableSet
    (hc : criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Ico a c = ∅) (p : M) :
    MapsTo (fun y ↦ hW.flow (Flow.levelCrossingTime hW.flow f a y) y)
      (hW.flow.stableSet p ∩ f ⁻¹' Ico a c) (hW.flow.stableSet p ∩ f ⁻¹' {a}) :=
  fun _ hx ↦ ⟨Flow.isInvariant_stableSet _ _ _ hx.1, hW.mapsTo_flow_levelCrossingTime hc hx.2⟩

end IsWeinsteinStructure

/-! ### A sphere in the local stable disc -/

section Sphere

variable {EN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN] {HN : Type*} [TopologicalSpace HN]
  {I : ModelWithCorners ℝ EN HN} {N : Type*}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {n : ℕ}
  {ι : F → N} {ρ s : ℝ} {L : V →L[ℝ] F}

/-- A point `u` of the unit sphere of `V` is sent by `s • L` into the ball of radius `ρ`, if
`0 ≤ s` and `s * ‖L‖ < ρ`. -/
theorem norm_smul_apply_coe_sphere_lt (hs : 0 ≤ s) (hsL : s * ‖L‖ < ρ) (u : sphere (0 : V) 1) :
    ‖s • L u‖ < ρ :=
  calc ‖s • L u‖ = s * ‖L u‖ := by rw [norm_smul, Real.norm_of_nonneg hs]
    _ ≤ s * (‖L‖ * ‖(u : V)‖) := by gcongr; exact L.le_opNorm _
    _ = s * ‖L‖ := by rw [norm_eq_of_mem_sphere u, mul_one]
    _ < ρ := hsL

/-- **A scaled sphere in a disc is smooth.** If `ι` is smooth at every point of the ball of
radius `ρ`, and `0 ≤ s` with `s * ‖L‖ < ρ`, then `u ↦ ι (s • L u)` is smooth on the unit sphere
of `V`. -/
theorem contMDiff_comp_smul_coe_sphere [TopologicalSpace N] [ChartedSpace HN N]
    [Fact (finrank ℝ V = n + 1)]
    (hι : ∀ z ∈ ball (0 : F) ρ, ContMDiffAt 𝓘(ℝ, F) I (⊤ : ℕ∞) ι z)
    (hs : 0 ≤ s) (hsL : s * ‖L‖ < ρ) :
    ContMDiff (𝓡 n) I (⊤ : ℕ∞) fun u : sphere (0 : V) 1 ↦ ι (s • L u) := fun u ↦
  (hι _ (mem_ball_zero_iff.2 (norm_smul_apply_coe_sphere_lt hs hsL u))).comp u
    ((s • L).contDiff.contMDiff.comp contMDiff_coe_sphere u)

/-- **A scaled sphere in a disc is injective.** If `ι` has a left inverse `π` on the ball of
radius `ρ`, `L` is injective, and `0 < s` with `s * ‖L‖ < ρ`, then `u ↦ ι (s • L u)` is
injective on the unit sphere of `V`. -/
theorem injective_comp_smul_coe_sphere {π : N → F} (hπ : ∀ z ∈ ball (0 : F) ρ, π (ι z) = z)
    (hs : 0 < s) (hsL : s * ‖L‖ < ρ) (hL : Injective L) :
    Injective fun u : sphere (0 : V) 1 ↦ ι (s • L u) := by
  intro u v h
  have h' := congrArg π h
  simp only at h'
  rw [hπ _ (mem_ball_zero_iff.2 (norm_smul_apply_coe_sphere_lt hs.le hsL u)),
    hπ _ (mem_ball_zero_iff.2 (norm_smul_apply_coe_sphere_lt hs.le hsL v))] at h'
  exact Subtype.ext (hL (smul_right_injective F hs.ne' h'))

/-- **A scaled sphere in a disc is immersed.** If `ι` has injective differential at every point
of the ball of radius `ρ`, `L` is injective, and `0 < s` with `s * ‖L‖ < ρ`, then
`u ↦ ι (s • L u)` has injective differential at every point of the unit sphere of `V`. -/
theorem injective_mfderiv_comp_smul_coe_sphere [TopologicalSpace N] [ChartedSpace HN N]
    [Fact (finrank ℝ V = n + 1)]
    (hι : ∀ z ∈ ball (0 : F) ρ, Injective (mfderiv 𝓘(ℝ, F) I ι z))
    (hs : 0 < s) (hsL : s * ‖L‖ < ρ) (hL : Injective L) (u : sphere (0 : V) 1) :
    Injective (mfderiv (𝓡 n) I (fun u : sphere (0 : V) 1 ↦ ι (s • L u)) u) := by
  -- `mvfderiv` of the inclusion is its `mfderiv` followed by the identification of the tangent
  -- spaces of `V` with `V`.
  have h1 : Injective (mfderiv (𝓡 n) 𝓘(ℝ, V) ((↑) : sphere (0 : V) 1 → V) u) := by
    have h := injective_mvfderiv_subtypeVal_sphere (n := n) u
    rw [mvfderiv, ContinuousLinearMap.coe_comp] at h
    exact h.of_comp
  have h2 : Injective (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, F) (s • L) u) := by
    rw [ContinuousLinearMap.mfderiv_eq]
    exact fun a b h ↦ hL (smul_right_injective F hs.ne' h)
  -- The map is `ι ∘ (s • L) ∘ (↑)` by definition; `TauCeti.injective_mfderiv_comp` needs it
  -- written as that composite to match.
  rw [show (fun u : sphere (0 : V) 1 ↦ ι (s • L u)) = ι ∘ (s • L) ∘ (↑) from rfl]
  exact TauCeti.injective_mfderiv_comp
    (hι _ (mem_ball_zero_iff.2 (norm_smul_apply_coe_sphere_lt hs.le hsL u)))
    (TauCeti.injective_mfderiv_comp h2 h1)

/-- **A scaled sphere misses the centre of the disc.** If `ι 0 = p`, `ι` has a left inverse `π`
on the ball of radius `ρ`, `L` is injective, and `0 < s` with `s * ‖L‖ < ρ`, then
`ι (s • L u) ≠ p` for every point `u` of the unit sphere of `V`. -/
theorem comp_smul_coe_sphere_ne {p : N} (hι0 : ι 0 = p) {π : N → F}
    (hπ : ∀ z ∈ ball (0 : F) ρ, π (ι z) = z) (hs : 0 < s) (hsL : s * ‖L‖ < ρ)
    (hL : Injective L) (u : sphere (0 : V) 1) : ι (s • L u) ≠ p := by
  intro h
  have h' := congrArg π (h.trans hι0.symm)
  rw [hπ _ (mem_ball_zero_iff.2 (norm_smul_apply_coe_sphere_lt hs.le hsL u)),
    hπ _ (mem_ball_self (hsL.trans_le' (by positivity)))] at h'
  have hu : L u = 0 := (smul_eq_zero.1 h').resolve_left hs.ne'
  exact ne_zero_of_mem_unit_sphere u (hL (hu.trans L.map_zero.symm))

end Sphere

namespace IsWeinsteinStructure

variable (hW : IsWeinsteinStructure ω X f)
include hW

/-- **A scaled sphere in a local stable disc.** Let `(ω, X, f)` be a Weinstein structure, and
`ι : F → M` a map with `ι 0 = p` that sends the ball of radius `ρ` into the stable set of `p`
and has a left inverse `π` there, as the local stable disc of
`SymplecticGeometry.IsWeinsteinStructure.exists_localStableDisc` does. For `L` injective and
`0 < s` with `s * ‖L‖ < ρ`, the points `ι (s • L u)`, for `u` on the unit sphere of `V`, lie in
the stable set of `p`, strictly below the level `f p`, and are not critical points of `f`.

With `exists_localStableDisc`, `contMDiff_comp_smul_coe_sphere`,
`injective_comp_smul_coe_sphere` and `injective_mfderiv_comp_smul_coe_sphere`, this makes
`u ↦ ι (s • L u)` an injective immersion of the sphere into the stable set of `p`. -/
theorem range_comp_smul_coe_sphere_subset {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {p : M} {ι : F → M} {ρ s : ℝ}
    {L : V →L[ℝ] F} (hι0 : ι 0 = p) (hιs : ι '' ball 0 ρ ⊆ hW.flow.stableSet p)
    {π : M → F} (hπ : ∀ z ∈ ball (0 : F) ρ, π (ι z) = z) (hs : 0 < s) (hsL : s * ‖L‖ < ρ)
    (hL : Injective L) :
    range (fun u : sphere (0 : V) 1 ↦ ι (s • L u)) ⊆
      (hW.flow.stableSet p ∩ f ⁻¹' Iio (f p)) \ criticalPoints 𝓘(ℝ, E) f := by
  rintro _ ⟨u, rfl⟩
  have hu := mem_ball_zero_iff.2 (norm_smul_apply_coe_sphere_lt hs.le hsL u)
  have hmem := hιs (mem_image_of_mem ι hu)
  have hne := comp_smul_coe_sphere_ne hι0 hπ hs hsL hL u
  exact ⟨⟨hmem, hW.apply_lt_of_mem_stableSet hmem hne⟩,
    hW.notMem_criticalPoints_of_mem_stableSet hmem hne⟩

/-- **Backward orbits leave every compact part of a stable set.** Let `(ω, X, f)` be a Weinstein
structure with flow `φ`, `K` a compact subset of the stable set of `p`, and `x ≠ p` a point of
that stable set. Then before every time `T`, the orbit of `x` has a point outside `K`. -/
theorem exists_le_flow_apply_notMem_of_isCompact {p x : M} {K : Set M} (hK : IsCompact K)
    (hKs : K ⊆ hW.flow.stableSet p) (hx : x ∈ hW.flow.stableSet p) (hxp : x ≠ p) (T : ℝ) :
    ∃ t ≤ T, hW.flow t x ∉ K := by
  by_contra! h
  have hf := hW.isGeneralizedMorse.contMDiff
  have hmono := hW.strictMono_comp_flow_of_mem_stableSet hx hxp
  set b := f (hW.flow T x)
  have hbp : b < f p := hW.apply_lt_of_mem_stableSet ((Flow.apply_mem_stableSet_iff _ T).2 hx)
    (Flow.apply_ne_of_mem_stableSet hx hxp T)
  -- On the compact part `B` of `K` below `b`, there is no critical point, so `df(X) ≥ c > 0`.
  set B := K ∩ f ⁻¹' Iic b
  have hB : IsCompact B := hK.inter_right (isClosed_Iic.preimage hf.continuous)
  have hcont : Continuous fun y ↦ mvfderiv 𝓘(ℝ, E) f y (X y) :=
    (hf.contMDiff_mvfderiv_apply (m := 0) (by simp)).continuous.comp hW.contMDiff_field.continuous
  obtain ⟨y₀, hy₀, hmin⟩ := hB.exists_isMinOn ⟨_, h T le_rfl, le_rfl⟩ hcont.continuousOn
  have hpos (y : M) (hy : y ∈ B) : 0 < mvfderiv 𝓘(ℝ, E) f y (X y) := by
    refine hW.isGradientLike.mvfderiv_apply_pos fun h0 ↦
      hW.notMem_criticalPoints_of_mem_stableSet (hKs hy.1) ?_ (mem_criticalPoints.2 h0)
    rintro rfl
    exact (lt_irrefl _ (hbp.trans_le' hy.2))
  have hc := hpos y₀ hy₀
  -- `f` is bounded below on `K`, but decreases at rate `c` along the backward orbit.
  obtain ⟨y₁, -, hfmin⟩ := hK.exists_isMinOn ⟨_, h T le_rfl⟩ hf.continuous.continuousOn
  set a := f y₁ - 1
  have hab : a ≤ b := by linarith [isMinOn_iff.1 hfmin _ (h T le_rfl)]
  have hγ := (hW.isMIntegralCurve_flow (hW.flow T x)).comp_neg
  have hγt (u : ℝ) : hW.flow (-u) (hW.flow T x) = hW.flow (-u + T) x :=
    (Flow.map_add _ _ _ _).symm
  set t := (b - a) / mvfderiv 𝓘(ℝ, E) f y₀ (X y₀) + 1
  have ht : 0 ≤ t := by have := div_nonneg (by linarith : 0 ≤ b - a) hc.le; linarith
  have hlt := hγ.apply_lt_of_mvfderiv_apply_le_neg (fun _ ↦ hf.mdifferentiable (by simp) _) hab
    (ε := mvfderiv 𝓘(ℝ, E) f y₀ (X y₀)) (s := 0) (t := t) (fun u _ hub ↦ by
      simp only [hγt] at hub ⊢
      have hle : -u + T ≤ T := hmono.le_iff_le.1 hub
      rw [Pi.neg_apply, map_neg, neg_le_neg_iff]
      have hmem : hW.flow (-u) (hW.flow T x) ∈ B := by rw [hγt]; exact ⟨h _ hle, hub⟩
      exact isMinOn_iff.1 hmin _ hmem)
    (by simp [b]) ht (by
      rw [sub_zero, mul_add, mul_div_cancel₀ _ hc.ne', mul_one]
      linarith)
  simp only [hγt] at hlt
  linarith [isMinOn_iff.1 hfmin _ (h (-t + T) (by linarith))]

/-- **An orbit of a stable set enters a compact part of it through its edge.** Let `(ω, X, f)` be a
Weinstein structure with flow `φ`, `K` a compact subset of the stable set of `p`, and `G` an open
set whose points in the stable set lie in `K`. If the orbit of a point `x ≠ p` of the stable set
meets `G`, then it also meets `K \ G`. -/
theorem exists_flow_apply_mem_diff_of_isCompact {p x : M} {K G : Set M} (hK : IsCompact K)
    (hKs : K ⊆ hW.flow.stableSet p) (hG : IsOpen G) (hGK : hW.flow.stableSet p ∩ G ⊆ K)
    (hx : x ∈ hW.flow.stableSet p) (hxp : x ≠ p) {T : ℝ} (hT : hW.flow T x ∈ G) :
    ∃ t, hW.flow t x ∈ K \ G := by
  obtain ⟨t₀, ht₀T, ht₀⟩ := hW.exists_le_flow_apply_notMem_of_isCompact hK hKs hx hxp T
  by_contra! h
  have hφc : Continuous fun t ↦ hW.flow t x := hW.flow.continuous_eval_const x
  -- Otherwise the times outside `K` and those in `G` split `[t₀, T]` into two disjoint open sets.
  obtain ⟨t, -, h₁, h₂⟩ := isPreconnected_Icc (a := t₀) (b := T)
    ((fun t ↦ hW.flow t x) ⁻¹' Kᶜ) ((fun t ↦ hW.flow t x) ⁻¹' G)
    (hK.isClosed.isOpen_compl.preimage hφc) (hG.preimage hφc)
    (fun t _ ↦ (em (hW.flow t x ∈ K)).symm.imp id fun hK' ↦ not_not.1 fun hG' ↦ h t ⟨hK', hG'⟩)
    ⟨t₀, ⟨le_rfl, ht₀T⟩, ht₀⟩ ⟨T, ⟨ht₀T, le_rfl⟩, hT⟩
  exact h₁ (hGK ⟨(Flow.apply_mem_stableSet_iff _ t).2 hx, h₂⟩)

/-- **A sphere in the local stable disc crossed once by each orbit.** Let `(ω, X, f)` be a
Weinstein structure with flow `φ`, `p` a nondegenerate critical point of `f` of Morse index
`m + 1`, and `a < f p`. There is a smooth injective immersion `σ` of the unit sphere of
`EuclideanSpace ℝ (Fin (m + 1))` into `M` such that:
* its image lies in the stable set of `p`, strictly between the levels `a` and `f p`, and
  contains no critical point of `f`;
* `X` is transverse to it: at no point `u` is `X (σ u)` in the range of the differential of `σ`;
* the orbit of every point `x ≠ p` of the stable set of `p` meets the image of `σ` at exactly
  one time. -/
theorem exists_sphere_existsUnique_flow_apply_mem_range {p : M}
    (hp : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f p) {m : ℕ}
    (hm : manifoldMorseIndex 𝓘(ℝ, E) f p = m + 1) {a : ℝ} (ha : a < f p) :
    ∃ σ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 → M,
      ContMDiff (𝓡 m) 𝓘(ℝ, E) (⊤ : ℕ∞) σ ∧ Injective σ ∧
      (∀ u, Injective (mfderiv (𝓡 m) 𝓘(ℝ, E) σ u)) ∧
      range σ ⊆ (hW.flow.stableSet p ∩ f ⁻¹' Ioo a (f p)) \ criticalPoints 𝓘(ℝ, E) f ∧
      (∀ u, X (σ u) ∉ range (mfderiv (𝓡 m) 𝓘(ℝ, E) σ u)) ∧
      ∀ x ∈ hW.flow.stableSet p, x ≠ p → ∃! t, hW.flow t x ∈ range σ := by
  have : Fact (finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) = m + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  set V := EuclideanSpace ℝ (Fin (m + 1))
  set A : E →L[ℝ] E := sectionLinearization (F := E) 𝓘(ℝ, E) id X p with hA
  set S := A.stableSubspace
  obtain ⟨D⟩ := hW.exists_localStableDisc hp hA
  obtain ⟨ρ', ⟨hρ', hρ'ρ⟩, hdec⟩ := D.exists_forall_flow_strictAntiOn hp hA
  obtain ⟨U, hU, ε, hε, hcov⟩ := D.exists_stableSet_inter_subset_image_ball
  have hρ := D.ρ_pos
  have hι0 := D.ι_zero
  have hιs (z : S) (hz : z ∈ ball 0 D.ρ) := And.intro (D.contMDiffAt_ι z hz)
    (D.injective_mfderiv_ι z hz)
  have hst := D.image_ball_subset_stableSet
  have hπ : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, S) (⊤ : ℕ∞) D.π (extChartAt 𝓘(ℝ, E) p).source := by
    simpa only [← centeredExtChartAt_source_eq_extChartAt_source] using D.contMDiffOn_π
  have hπι (z : S) (hz : z ∈ ball 0 D.ρ) := D.π_ι hz
  have hπp := D.π_self
  -- Only these properties of the disc are used below, so its data become plain variables.
  set ι := D.ι
  set ρ := D.ρ
  set π := D.π
  clear_value ι ρ π
  obtain ⟨L, hL⟩ := hW.isGradientLike.exists_continuousLinearEquiv_stableSubspace hp
    (hW.mdifferentiableAt_field p) hA hm
  set e := extChartAt 𝓘(ℝ, E) p
  set H := fderiv ℝ (fderiv ℝ (f ∘ e.symm)) (e p)
  set L' : V →L[ℝ] S := L.toContinuousLinearMap
  have hHL (v : V) : -H (L' v) (L' v) = ‖v‖ ^ 2 := hL v
  -- An open neighbourhood `W` of `p` whose points in the stable set lie on the disc.
  set W : Set M := interior U ∩ e.source ∩ {y | f p - ε < f y}
  have hWo : IsOpen W := (isOpen_interior.inter (isOpen_extChartAt_source p)).inter
    (isOpen_lt continuous_const hW.isGeneralizedMorse.contMDiff.continuous)
  have hpW : p ∈ W := ⟨⟨mem_interior_iff_mem_nhds.2 hU, mem_extChartAt_source p⟩, by simp [hε]⟩
  have hWcov {y : M} (hy : y ∈ hW.flow.stableSet p) (hyW : y ∈ W) : ι (π y) = y := by
    obtain ⟨z, hz, rfl⟩ := hcov ⟨⟨hy, interior_subset hyW.1.1⟩, hyW.2⟩
    rw [hπι z hz]
  -- A radius `δ` such that `ι` maps the ball of radius `δ` into `W`, above the level `a`.
  have hWa : IsOpen (W ∩ {y | a < f y}) :=
    hWo.inter (isOpen_lt continuous_const hW.isGeneralizedMorse.contMDiff.continuous)
  obtain ⟨δ, hδ, hδW⟩ := Metric.mem_nhds_iff.1
    ((hιs 0 (mem_ball_self hρ)).1.continuousAt.preimage_mem_nhds
      (hWa.mem_nhds (hι0 ▸ ⟨hpW, ha⟩ : ι 0 ∈ W ∩ {y | a < f y})))
  -- The scale `s`, so small that `L'` maps the closed ball of radius `s` into the balls of radii
  -- `δ` and `ρ'`.
  set r := min δ ρ'
  have hr : 0 < r := lt_min hδ hρ'
  set s := r / (2 * (‖L'‖ + 1))
  have hs : 0 < s := by positivity
  have hsL : s * ‖L'‖ < r := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [norm_nonneg L']
  have hsLρ : s * ‖L'‖ < ρ := hsL.trans_le ((min_le_right _ _).trans hρ'ρ)
  have hLv {v : V} (hv : ‖v‖ ≤ s) : ‖L' v‖ < r :=
    (L'.le_opNorm v).trans_lt ((mul_le_mul_of_nonneg_left hv (norm_nonneg _)).trans_lt
      (by rw [mul_comm]; exact hsL))
  have hLρ' {v : V} (hv : ‖v‖ ≤ s) : L' v ∈ ball 0 ρ' :=
    mem_ball_zero_iff.2 ((hLv hv).trans_le (min_le_right _ _))
  have hLWa {v : V} (hv : ‖v‖ ≤ s) : ι (L' v) ∈ W ∩ {y | a < f y} :=
    hδW (mem_ball_zero_iff.2 ((hLv hv).trans_le (min_le_left _ _)))
  have hLW {v : V} (hv : ‖v‖ ≤ s) : ι (L' v) ∈ W := (hLWa hv).1
  have hπL {v : V} (hv : ‖v‖ ≤ s) : π (ι (L' v)) = L' v :=
    hπι _ (ball_subset_ball hρ'ρ (hLρ' hv))
  have hL0 {v : V} (hv : ‖v‖ = s) : L' v ≠ 0 := fun h ↦ by
    rw [L.map_eq_zero_iff.1 h, norm_zero] at hv
    exact hs.ne hv
  -- The sphere, and its image as the image of the sphere of radius `s` under `ι ∘ L'`.
  set σ : sphere (0 : V) 1 → M := fun u ↦ ι (s • L' u) with hσdef
  have hus (u : sphere (0 : V) 1) : ‖s • (u : V)‖ = s := by
    rw [norm_smul, norm_eq_of_mem_sphere u, Real.norm_of_nonneg hs.le, mul_one]
  have hrange (y : M) : y ∈ range σ ↔ ∃ v : V, ‖v‖ = s ∧ ι (L' v) = y := by
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨s • u, hus u, by rw [map_smul]⟩
    · rintro ⟨v, hv, rfl⟩
      refine ⟨⟨s⁻¹ • v, ?_⟩, ?_⟩
      · rw [mem_sphere_zero_iff_norm, norm_smul, hv, norm_inv, Real.norm_of_nonneg hs.le,
          inv_mul_cancel₀ hs.ne']
      · simp only [hσdef]
        rw [map_smul, smul_smul, mul_inv_cancel₀ hs.ne', one_smul]
  refine ⟨σ, contMDiff_comp_smul_coe_sphere (fun z hz ↦ (hιs z hz).1) hs.le hsLρ,
    injective_comp_smul_coe_sphere hπι hs hsLρ L.injective,
    injective_mfderiv_comp_smul_coe_sphere
      (fun z hz ↦ (hιs z hz).2) hs hsLρ L.injective,
    fun y hy ↦ ?_, ?_, ?_⟩
  · -- The sphere lies above the level `a` by the choice of `δ`.
    obtain ⟨⟨hys, hyp⟩, hyc⟩ := hW.range_comp_smul_coe_sphere_subset hι0 hst hπι hs hsLρ
      L.injective hy
    obtain ⟨v, hv, rfl⟩ := (hrange y).1 hy
    exact ⟨⟨hys, (hLWa hv.le).2, hyp⟩, hyc⟩
  · -- Transversality: `-H ∘ π` is constant on the sphere, but decreases strictly along `X`.
    intro u
    set z := s • L' (u : V)
    have hzeq : z = L' (s • (u : V)) := (map_smul L' s (u : V)).symm
    have hz : z ∈ ball 0 ρ' := hzeq ▸ hLρ' (hus u).le
    obtain ⟨d, hd0, hd⟩ := ((hdec z hz).2 (hzeq ▸ hL0 (hus u))).1 0 le_rfl
    set h : M → ℝ := fun y ↦ -H (π y) (π y)
    have hc (u' : sphere (0 : V) 1) : (h ∘ σ) u' = s ^ 2 := by
      simp only [Function.comp_apply, hσdef, h]
      rw [← map_smul, hπL (hus u').le, hHL, hus]
    -- The derivative of `h` along the orbit of `σ u` at time `0` is `d < 0`.
    have hg : ContDiff ℝ 1 fun ζ : S ↦ -H ζ ζ :=
      ((H.contDiff.comp S.subtypeL.contDiff).clm_apply S.subtypeL.contDiff).neg
    have hhd : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ) h (σ u) :=
      ((hg.contMDiff.comp_contMDiffOn (hπ.of_le (by simp))).contMDiffAt
        ((isOpen_extChartAt_source p).mem_nhds (hzeq ▸ hLW (hus u).le).1.2)).mdifferentiableAt
        one_ne_zero
    have hw : mvfderiv 𝓘(ℝ, E) h (σ u) (X (σ u)) ≠ 0 := by
      have h00 : hW.flow 0 (σ u) = σ u := Flow.map_zero_apply _ _
      have hcurve := Manifold.hasDerivAt_comp_curve (γ := fun t ↦ hW.flow t (σ u))
        (by rwa [h00]) (hW.isMIntegralCurve_flow (σ u) 0)
      have := hd.unique hcurve
      beta_reduce at this
      rw [h00] at this
      exact this ▸ hd0.ne
    rintro ⟨v, hv⟩
    exact hw (hv ▸ TauCeti.mfderiv_mfderiv_apply_eq_zero_of_comp_eventuallyEq_const (K := 𝓘(ℝ))
      (.of_forall hc) v)
  · intro x hx hxp
    -- Two crossings would give the same value `s ^ 2` of `-H` at two times along the disc.
    have hle (t₁ t₂ : ℝ) (h₁ : hW.flow t₁ x ∈ range σ) (h₂ : hW.flow t₂ x ∈ range σ) :
        t₂ ≤ t₁ := by
      by_contra! hlt
      obtain ⟨v₁, hv₁, he₁⟩ := (hrange _).1 h₁
      obtain ⟨v₂, hv₂, he₂⟩ := (hrange _).1 h₂
      have hanti := ((hdec (L' v₁) (hLρ' hv₁.le)).2 (hL0 hv₁)).2
      have h' : hW.flow (t₂ - t₁) (ι (L' v₁)) = ι (L' v₂) := by
        rw [he₁, ← Flow.map_add, sub_add_cancel, he₂]
      have := hanti (mem_Ici.2 le_rfl) (mem_Ici.2 (sub_nonneg.2 hlt.le)) (sub_pos.2 hlt)
      simp only [Flow.map_zero_apply, h'] at this
      rw [hπL hv₁.le, hπL hv₂.le, hHL, hHL, hv₁, hv₂] at this
      exact lt_irrefl _ this
    obtain ⟨t, ht⟩ : ∃ t, hW.flow t x ∈ range σ := by
      have hπc : ContinuousOn (fun y ↦ ‖L.symm (π y)‖) e.source :=
        L.symm.continuous.norm.comp_continuousOn hπ.continuousOn
      -- At a late time `T`, the orbit is in the part `G` of `W` strictly inside the sphere.
      have hκ : Tendsto (fun t ↦ ‖L.symm (π (hW.flow t x))‖) atTop (𝓝 0) := by
        have h := (hπc.continuousAt ((isOpen_extChartAt_source p).mem_nhds
          (mem_extChartAt_source p))).tendsto.comp (Flow.mem_stableSet.1 hx)
        simpa only [Function.comp_def, hπp, map_zero, norm_zero] using h
      obtain ⟨T, hTW, hTs⟩ := (((Flow.mem_stableSet.1 hx).eventually (hWo.mem_nhds hpW)).and
        (hκ.eventually (gt_mem_nhds hs))).exists
      set G := W ∩ (fun y ↦ ‖L.symm (π y)‖) ⁻¹' Iio s
      have hGo : IsOpen G :=
        (hπc.mono fun _ hy ↦ hy.1.2 : ContinuousOn _ W).isOpen_inter_preimage hWo isOpen_Iio
      -- The compact cap `K` bounded by the sphere contains the points of the stable set in `G`.
      set K := ι '' (L' '' closedBall 0 s)
      have hK : IsCompact K :=
        ((isCompact_closedBall (0 : V) s).image L'.continuous).image_of_continuousOn (by
          rintro _ ⟨v, hv, rfl⟩
          exact (hιs _ (ball_subset_ball hρ'ρ (hLρ' (mem_closedBall_zero_iff.1 hv)))).1
            |>.continuousAt.continuousWithinAt)
      have hKs : K ⊆ hW.flow.stableSet p := by
        rintro _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
        exact hst ⟨_, ball_subset_ball hρ'ρ (hLρ' (mem_closedBall_zero_iff.1 hv)), rfl⟩
      have hGK : hW.flow.stableSet p ∩ G ⊆ K := fun y hy ↦
        ⟨_, ⟨L.symm (π y), mem_closedBall_zero_iff.2 (le_of_lt hy.2.2),
          L.apply_symm_apply _⟩, hWcov hy.1 hy.2.1⟩
      -- The orbit meets `K` outside `G`, that is on the sphere.
      obtain ⟨t, ⟨_, ⟨v, hv, rfl⟩, he⟩, htG⟩ :=
        hW.exists_flow_apply_mem_diff_of_isCompact hK hKs hGo hGK hx hxp ⟨hTW, hTs⟩
      have hvle := mem_closedBall_zero_iff.1 hv
      refine ⟨t, (hrange _).2 ⟨v, hvle.antisymm (not_lt.1 fun hvs ↦ htG ?_), he⟩⟩
      refine ⟨he ▸ hLW hvle, ?_⟩
      simp only [mem_preimage, mem_Iio]
      rw [← he, hπL hvle, ContinuousLinearEquiv.coe_coe, L.symm_apply_apply]
      exact hvs
    exact ⟨t, ht, fun t' ht' ↦ le_antisymm (hle t t' ht ht') (hle t' t ht' ht)⟩

/-- **The stable sphere in a lower level.** Let `(ω, X, f)` be a Weinstein structure, `p` a
nondegenerate critical point of `f` of Morse index `m + 1`, and `a < f p` a level such that `f`
has no critical point in `f ⁻¹' Ico a (f p)`. There is a smooth injective immersion `τ` of the
unit sphere of `EuclideanSpace ℝ (Fin (m + 1))` into `M` whose image is the set of points of the
level `f ⁻¹' {a}` whose orbits tend to `p`. -/
theorem exists_sphere_range_eq_stableSet_inter_preimage {p : M}
    (hp : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f p) {m : ℕ}
    (hm : manifoldMorseIndex 𝓘(ℝ, E) f p = m + 1) {a : ℝ} (ha : a < f p)
    (hc : criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Ico a (f p) = ∅) :
    ∃ τ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 → M,
      ContMDiff (𝓡 m) 𝓘(ℝ, E) (⊤ : ℕ∞) τ ∧ Injective τ ∧
      (∀ u, Injective (mfderiv (𝓡 m) 𝓘(ℝ, E) τ u)) ∧
      range τ = hW.flow.stableSet p ∩ f ⁻¹' {a} := by
  set φ := hW.flow
  obtain ⟨σ, hσ, hσi, hσd, hσr, hσX, hσu⟩ :=
    hW.exists_sphere_existsUnique_flow_apply_mem_range hp hm ha
  -- The backward map `B` to the level `a`, and the points of the sphere in its domain.
  set B : M → M := fun y ↦ φ (Flow.levelCrossingTime φ f a y) y
  have hσs (u) : σ u ∈ φ.stableSet p := (hσr ⟨u, rfl⟩).1.1
  have hσI (u) : σ u ∈ f ⁻¹' Ioo a (f p) := (hσr ⟨u, rfl⟩).1.2
  have hσIco (u) : f (σ u) ∈ Ico a (f p) := Ioo_subset_Ico_self (hσI u)
  have hBa (u) : B (σ u) ∈ φ.stableSet p ∩ f ⁻¹' {a} :=
    hW.mapsTo_flow_levelCrossingTime_stableSet hc p ⟨hσs u, hσIco u⟩
  have hBne (u) : B (σ u) ≠ p := fun h ↦ ha.ne (h ▸ (hBa u).2).symm
  have hBσ (u) : φ (-Flow.levelCrossingTime φ f a (σ u)) (B (σ u)) = σ u :=
    φ.map_neg_apply_map _ _
  have hBd (u) : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) B (σ u) :=
    ((hW.contMDiffOn_flow_levelCrossingTime hc).contMDiffAt
      ((isOpen_Ioo.preimage hW.isGeneralizedMorse.contMDiff.continuous).mem_nhds
        (hσI u))).mdifferentiableAt (by simp)
  refine ⟨B ∘ σ, (hW.contMDiffOn_flow_levelCrossingTime hc).comp_contMDiff hσ hσI,
    fun u v huv ↦ ?_, fun u ↦ ?_, ?_⟩
  · -- Two points of the sphere with the same image lie on one orbit, which meets the sphere once.
    have huv' : B (σ u) = B (σ v) := huv
    obtain ⟨t, -, ht⟩ := hσu _ (hBa u).1 (hBne u)
    have hu := ht _ ⟨u, (hBσ u).symm⟩
    have hv := ht _ ⟨v, (hBσ v).symm.trans (by rw [huv'])⟩
    refine hσi ((hBσ u).symm.trans ?_)
    rw [hu, ← hv, huv', hBσ]
  · -- The kernel of the differential of `B` is the line of `X`, which is transverse to `σ`.
    rw [mfderiv_comp u (hBd u) ((hσ u).mdifferentiableAt (by simp)),
      injective_iff_map_eq_zero]
    intro v hv
    have hker : mfderiv (𝓡 m) 𝓘(ℝ, E) σ u v ∈ ℝ ∙ X (σ u) := by
      rw [← hW.ker_mfderiv_flow_levelCrossingTime hc (hσI u)]
      exact hv
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 hker
    rcases eq_or_ne r 0 with rfl | hr0
    · exact injective_iff_map_eq_zero _ |>.1 (hσd u) v (by rw [← hr, zero_smul])
    · refine absurd ⟨r⁻¹ • v, ?_⟩ (hσX u)
      rw [map_smul, ← hr, smul_smul, inv_mul_cancel₀ hr0, one_smul]
  · refine Subset.antisymm (range_subset_iff.2 hBa) fun y ⟨hys, hya⟩ ↦ ?_
    -- The orbit of `y` meets the sphere at some `σ u`, which `B` sends back to `y`.
    have hyp : y ≠ p := fun h ↦ ha.ne (h ▸ hya).symm
    obtain ⟨t, ⟨u, hu⟩, -⟩ := hσu y hys hyp
    refine ⟨u, ?_⟩
    have hlct : -t = Flow.levelCrossingTime φ f a (σ u) := by
      rw [hW.eq_levelCrossingTime_iff hc (hσIco u), hu, φ.map_neg_apply_map]
      exact hya
    calc (B ∘ σ) u = φ (-t) (σ u) := by simp only [Function.comp_apply, B, hlct]
      _ = y := by rw [hu, φ.map_neg_apply_map]

section Horizontal

variable {EN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN] {HN : Type*} [TopologicalSpace HN]
  {IN : ModelWithCorners ℝ EN HN} {N : Type*} [TopologicalSpace N] [ChartedSpace HN N]

/-- **Stable sets are horizontal in a lower regular level.** Let `(ω, X, f)` be a Weinstein
structure on a manifold `M` of dimension `n + 1`, `a` a regular value of `f`, and `p` a
nondegenerate critical point of `f`. Give the sublevel `W = {x | f x ≤ a}` the structure of a
Weinstein domain of `IsWeinsteinStructure.isWeinsteinDomain_scalarRegularSublevel`, and its
boundary the contact form `α = fillingContactForm σ Y` of that filling, where `σ` is the
pull-back of `ω` along the inclusion `ι : W → M` and `Y` the pull-back `x ↦ (dι_x)⁻¹ (X x)` of
`X`. Then every map `γ : N → ∂W` whose composite with the inclusion `∂W → M` takes values in the
stable set of `p` is horizontal for the kernel distribution of `α`: the image of each differential
of `γ` lies in `ker α`.

See [CieliebakEliashberg2012], Lemma 11.13 (a). -/
theorem isHorizontalMap_kerDistribution_fillingContactForm_of_range_subset_stableSet {n : ℕ}
    (hn : finrank ℝ E = n + 1) {a : ℝ} (ha : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) f a) {p : M}
    (hp : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f p) :
    letI := scalarRegularSublevelChartedSpace
      (hW.isGeneralizedMorse.contMDiff.of_le (by simp)) ha hn
    haveI := isManifold_scalarRegularSublevel ha hn (by simp) hW.isGeneralizedMorse.contMDiff
    ∀ {γ : N → (𝓡∂ (n + 1)).boundary {x | f x ≤ a}},
      range (fun y ↦ ((γ y : {x | f x ≤ a}) : M)) ⊆ hW.flow.stableSet p →
      IsHorizontalMap IN (fillingContactForm
        (SmoothForm.mpullback Subtype.val (contMDiff_subtypeVal_scalarRegularSublevel ha hn
          (by simp) hW.isGeneralizedMorse.contMDiff) ω)
        ⟨VectorField.mpullback (𝓡∂ (n + 1)) 𝓘(ℝ, E) Subtype.val X,
          (hW.isWeinsteinDomain_scalarRegularSublevel hn ha).isStrongFilling
            |>.isOutwardPointingField.contMDiff⟩).kerDistribution γ := by
  have hf := hW.isGeneralizedMorse.contMDiff
  let := scalarRegularSublevelChartedSpace (hf.of_le (by simp)) ha hn
  have := isManifold_scalarRegularSublevel ha hn (by simp) hf
  have hι := contMDiff_subtypeVal_scalarRegularSublevel ha hn (by simp) hf
  have hinv := isInvertible_mfderiv_subtypeVal_scalarRegularSublevel (hf.of_le (by simp)) ha hn
  have hb :=
    (isSmoothEmbedding_subtypeVal_boundary (n := n) (k := (⊤ : ℕ∞)) {x | f x ≤ a}).contMDiff
  intro γ hs
  rw [isHorizontalMap_iff_range_mfderiv_le]
  intro y
  by_cases hγ : MDifferentiableAt IN (𝓡 n) γ y
  swap
  · simp [mfderiv_zero_of_not_mdifferentiableAt hγ]
  rintro _ ⟨v, rfl⟩
  let w : {x | f x ≤ a} := (γ y).val
  have hιw : MDifferentiableAt (𝓡∂ (n + 1)) 𝓘(ℝ, E) Subtype.val w :=
    (hι w).mdifferentiableAt (by simp)
  have hbw := (hb (γ y)).mdifferentiableAt (by simp)
  have hbγ := hbw.comp y hγ
  have h0 := hW.interior_apply_mfderiv_eq_zero_of_range_subset_stableSet hp
    (hιw.comp y hbγ) hs v
  rw [mfderiv_comp_apply y hιw hbγ, mfderiv_comp_apply y hbw hγ, Function.comp_apply,
    Function.comp_apply, ← mpullback_apply_one, mpullback_interior_at _ _ _ _
    (VectorField.mfderiv_apply_mpullback (hinv w) X)] at h0
  rw [SmoothForm.mem_kerDistribution, coe_fillingContactForm, Pi.neg_apply,
    ContinuousAlternatingMap.neg_apply, mpullback_apply_one, ContMDiffSection.coeFn_mk,
    SmoothForm.coe_mpullback]
  exact neg_eq_zero.2 h0

end Horizontal

end IsWeinsteinStructure

namespace IsElementaryWeinsteinCobordism

/-- **The stable sphere in the lower level.** Let `(ω, X, f)` be an elementary Weinstein cobordism
between the levels `a` and `b`, and `p` a nondegenerate critical point of `f` in the region
`f ⁻¹' Icc a b`, of Morse index `m + 1`. There is a smooth injective immersion `τ` of
the unit sphere of `EuclideanSpace ℝ (Fin (m + 1))` into `M` whose image is the set of points of
the lower level `f ⁻¹' {a}` whose orbits tend to `p`. -/
theorem exists_sphere_range_eq_stableSet_inter_preimage {a b : ℝ}
    (hW : IsElementaryWeinsteinCobordism ω X f a b) {p : M}
    (hp : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f p) (hpab : f p ∈ Icc a b) {m : ℕ}
    (hm : manifoldMorseIndex 𝓘(ℝ, E) f p = m + 1) :
    ∃ τ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 → M,
      ContMDiff (𝓡 m) 𝓘(ℝ, E) (⊤ : ℕ∞) τ ∧ Injective τ ∧
      (∀ u, Injective (mfderiv (𝓡 m) 𝓘(ℝ, E) τ u)) ∧
      range τ = hW.isWeinsteinStructure.flow.stableSet p ∩ f ⁻¹' {a} := by
  obtain ⟨c, -, hsub, hc⟩ := hW.exists_criticalPoints_inter_preimage_Ico_eq_empty
  have hpc : f p = c := hsub ⟨hp.mem_criticalPoints, hpab⟩
  exact hW.isWeinsteinStructure.exists_sphere_range_eq_stableSet_inter_preimage hp hm
    (hW.criticalPoints_inter_subset_preimage_Ioo ⟨hp.mem_criticalPoints, hpab⟩).1 (hpc ▸ hc)

/-- **The attaching sphere.** Let `(ω, X, f)` be an elementary Weinstein cobordism between the
levels `a` and `b` on a manifold `M` of dimension `n + 1`, and `p` a nondegenerate critical point
of `f` in the region `f ⁻¹' Icc a b`, of Morse index `m + 1`. Give the sublevel
`W = {x | f x ≤ a}` the structure of a Weinstein domain of
`IsWeinsteinStructure.isWeinsteinDomain_scalarRegularSublevel`, and its boundary `∂W` the contact
form `α = fillingContactForm σ Y` of that filling. Then there is a smooth embedding `γ` of the
unit sphere of `EuclideanSpace ℝ (Fin (m + 1))` into `∂W` whose image in `M` is the set of points
of the lower level `f ⁻¹' {a}` whose orbits tend to `p`, and which is horizontal for the kernel
distribution of `α`.

See [CieliebakEliashberg2012], Lemma 11.13 (a). -/
theorem exists_attachingSphere {a b : ℝ} (hW : IsElementaryWeinsteinCobordism ω X f a b) {n : ℕ}
    (hn : finrank ℝ E = n + 1) {p : M} (hp : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f p)
    (hpab : f p ∈ Icc a b) {m : ℕ} (hm : manifoldMorseIndex 𝓘(ℝ, E) f p = m + 1) :
    letI := scalarRegularSublevelChartedSpace
      (hW.isWeinsteinStructure.isGeneralizedMorse.contMDiff.of_le (by simp))
      hW.isRegularValue_lower hn
    haveI := isManifold_scalarRegularSublevel hW.isRegularValue_lower hn (by simp)
      hW.isWeinsteinStructure.isGeneralizedMorse.contMDiff
    ∃ γ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 → (𝓡∂ (n + 1)).boundary {x | f x ≤ a},
      Manifold.IsSmoothEmbedding (𝓡 m) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (⊤ : ℕ∞) γ ∧
      range (fun u ↦ ((γ u : {x | f x ≤ a}) : M)) =
        hW.isWeinsteinStructure.flow.stableSet p ∩ f ⁻¹' {a} ∧
      IsHorizontalMap (𝓡 m) (SmoothForm.kerDistribution (fillingContactForm
        (SmoothForm.mpullback Subtype.val (contMDiff_subtypeVal_scalarRegularSublevel
          hW.isRegularValue_lower hn (by simp)
          hW.isWeinsteinStructure.isGeneralizedMorse.contMDiff) ω)
        ⟨VectorField.mpullback (𝓡∂ (n + 1)) 𝓘(ℝ, E) Subtype.val X,
          (hW.isWeinsteinStructure.isWeinsteinDomain_scalarRegularSublevel hn
            hW.isRegularValue_lower).isStrongFilling.isOutwardPointingField.contMDiff⟩)) γ := by
  have hf := hW.isWeinsteinStructure.isGeneralizedMorse.contMDiff
  have ha := hW.isRegularValue_lower
  let := scalarRegularSublevelChartedSpace (hf.of_le (by simp)) ha hn
  have := isManifold_scalarRegularSublevel ha hn (by simp) hf
  obtain ⟨τ, hτ, hτi, hτd, hτr⟩ := hW.exists_sphere_range_eq_stableSet_inter_preimage hp hpab hm
  have hτa (u) : f (τ u) = a := (hτr.le ⟨u, rfl⟩).2
  -- The lift of `τ` to the boundary of the sublevel, which is the level `f ⁻¹' {a}`.
  have hbd := boundary_scalarRegularSublevel ha hn (by simp) hf
  let γ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 → (𝓡∂ (n + 1)).boundary {x | f x ≤ a} :=
    fun u ↦ ⟨⟨τ u, (hτa u).le⟩, hbd ▸ hτa u⟩
  have hγ : (fun u ↦ ((γ u : {x | f x ≤ a}) : M)) = τ := rfl
  refine ⟨γ, ?_, hγ ▸ hτr, ?_⟩
  · refine isSmoothEmbedding_of_isImmersion_comp_coe_boundary_scalarRegularSublevel ha hn
      (by simp) hf (by simp) le_rfl ?_ (hγ ▸ hτi)
    exact hγ ▸ ContMDiff.isImmersion_of_injective_mfderiv hτ (by simp) hτd
  · exact hW.isWeinsteinStructure
      |>.isHorizontalMap_kerDistribution_fillingContactForm_of_range_subset_stableSet hn ha hp
        (hγ ▸ hτr.le.trans inter_subset_left)

end IsElementaryWeinsteinCobordism

end SymplecticGeometry

end
