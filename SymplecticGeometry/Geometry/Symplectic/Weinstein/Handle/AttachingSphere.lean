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
import SymplecticGeometry.Analysis.ODE.LyapunovBilinForm
import SymplecticGeometry.Dynamics.Flow.Stable
import SymplecticGeometry.Geometry.Manifold.Flow.BandCrossing
import SymplecticGeometry.Geometry.Manifold.Flow.LevelCrossing
import SymplecticGeometry.Geometry.Symplectic.Weinstein.Handle.Linearization
import TauCeti.LinearAlgebra.QuadraticForm.Real

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
disc. On a stable set, `f` lies strictly below its value at the limit `p` away from `p`, and `p`
is the only critical point. When `p` has Morse index `m`, the negative of the Hessian of `f` in
the chart at `p` is a Euclidean norm on the stable subspace of the linearization of `X`, through a
continuous linear equivalence `L` with `EuclideanSpace ℝ (Fin m)`. For a disc `ι` with a left
inverse on the ball of radius `ρ`, as given by `exists_localStableDisc`, and `0 < s` with
`s * ‖L‖ < ρ`, the map `u ↦ ι (s • L u)` on the unit sphere is a smooth injective immersion
into the stable set of `p`, below the level `f p`, that meets no critical point.

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
* `SymplecticGeometry.IsWeinsteinStructure.ker_mfderiv_flow_levelCrossingTime`: the kernel of the
  derivative of the backward map at `x` is the span of `X x`.
* `QuadraticMap.PosDef.exists_continuousLinearEquiv_euclideanSpace`: a positive definite form on
  a space of dimension `n` is `‖u‖ ^ 2` in a continuous linear coordinate `u` in
  `EuclideanSpace ℝ (Fin n)`; `TauCeti.IsGradientLike.exists_continuousLinearEquiv_stableSubspace`
  applies it to the negative of the Hessian on the stable subspace.
* `SymplecticGeometry.IsWeinsteinStructure.apply_lt_of_mem_stableSet` and
  `.notMem_criticalPoints_of_mem_stableSet`: a point `x ≠ p` of the stable set of `p` has
  `f x < f p` and is not a critical point.
* `SymplecticGeometry.contMDiff_comp_smul_coe_sphere`, `.injective_comp_smul_coe_sphere` and
  `.injective_mfderiv_comp_smul_coe_sphere`: a sphere scaled into the ball on which a disc is an
  immersion with a left inverse is a smooth injective immersion;
  `SymplecticGeometry.IsWeinsteinStructure.range_comp_smul_coe_sphere_subset`: for the local
  stable disc, it lies in the stable set, below `f p`, off the critical points.

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
the implicit function theorem at the regular level `a`, in the form of Tau Ceti's
`TauCeti.contMDiffOn_flow_levelCrossingTime`, and not the continuity of
`Flow.levelCrossingTime` on a connecting set.

The kernel is `TauCeti.ker_mfderiv_flow_levelCrossingTime`, whose hypotheses are checked as for
the smoothness.

The Euclidean coordinate is Tau Ceti's
`TauCeti.nonempty_isometryEquiv_toQuadraticForm'_one_of_posDef`, which makes a positive definite
form isometric to the sum of squares, read on `EuclideanSpace ℝ (Fin n)`, as in the proof of
`QuadraticMap.PosDef.exists_linearEquiv_image_closedBall_eq`
(`SymplecticGeometry.Analysis.InnerProductSpace.Ellipsoid`); the Hessian is negative definite on
the stable subspace by `ContinuousLinearMap.apply_self_neg_of_mem_stableSubspace`. The strict
bound on a stable set uses that `f` is monotone along orbits and at most `f p` on the stable set:
if `f x = f p`, then `f` is constant on the forward orbit of `x`, so `df(X)` vanishes at the time
`1` point, which is then a rest point in the stable set of `p`, hence `p`
(`Flow.eq_of_mem_stableSet`). The immersion is the chain rule with Mathlib's
`injective_mvfderiv_subtypeVal_sphere` for the inclusion of the sphere, and injectivity comes
from the left inverse of the disc.

## References

* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  Chapter 11, on the stable manifolds of the critical points of a Weinstein structure
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

/-- **The backward map to the lower level is smooth.** If `f` has no critical point in
`f ⁻¹' Ico a c`, the map `y ↦ φ (Flow.levelCrossingTime φ f a y) y`, for `φ` the flow, which
follows the orbit of each point back to the level `f ⁻¹' {a}`, is smooth on `f ⁻¹' Ioo a c`.

The proof uses the implicit function theorem at the regular level `a`, through Tau Ceti's
`TauCeti.contMDiffOn_flow_levelCrossingTime`. -/
theorem contMDiffOn_flow_levelCrossingTime
    (hc : criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Ico a c = ∅) :
    ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) (⊤ : ℕ∞)
      (fun y ↦ hW.flow (Flow.levelCrossingTime hW.flow f a y) y) (f ⁻¹' Ioo a c) := by
  have hIco {y : M} (hy : y ∈ f ⁻¹' Ioo a c) : f y ∈ Ico a c := Ioo_subset_Ico_self hy
  exact _root_.TauCeti.contMDiffOn_flow_levelCrossingTime (n := ⊤) le_top hW.contMDiff_field
    hW.isCompleteVectorField hW.flowOf_eq_flow
    (isOpen_Ioo.preimage hW.isGeneralizedMorse.contMDiff.continuous)
    (fun _ hy _ hs _ ht ↦ ((hW.eq_levelCrossingTime_iff hc (hIco hy)).2 hs).trans
      ((hW.eq_levelCrossingTime_iff hc (hIco hy)).2 ht).symm)
    (fun _ hy ↦ ⟨_, hW.mapsTo_flow_levelCrossingTime hc (hIco hy)⟩)
    (fun _ _ ↦ hW.isGeneralizedMorse.contMDiff _)
    fun _ hy ↦ (hW.mvfderiv_apply_pos_flow_levelCrossingTime hc (hIco hy)).ne'

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

/-- **A positive definite form is a Euclidean norm.** A positive definite quadratic form `Q` on
a real normed space `V` of dimension `n` is the squared norm of `EuclideanSpace ℝ (Fin n)`
carried over by a continuous linear equivalence: `Q (L u) = ‖u‖ ^ 2`. -/
theorem _root_.QuadraticMap.PosDef.exists_continuousLinearEquiv_euclideanSpace
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {Q : QuadraticForm ℝ V} (hQ : Q.PosDef) {n : ℕ} (hn : finrank ℝ V = n) :
    ∃ L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] V, ∀ u, Q (L u) = ‖u‖ ^ 2 := by
  subst hn
  obtain ⟨φ⟩ := TauCeti.nonempty_isometryEquiv_toQuadraticForm'_one_of_posDef hQ
  refine ⟨((WithLp.linearEquiv 2 ℝ _).trans φ.symm.toLinearEquiv).toContinuousLinearEquiv,
    fun u ↦ ?_⟩
  simp only [LinearEquiv.coe_toContinuousLinearEquiv', LinearEquiv.trans_apply,
    QuadraticMap.IsometryEquiv.coe_toLinearEquiv]
  rw [φ.symm.map_app, EuclideanSpace.real_norm_sq_eq]
  simp [Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
    Matrix.toLinearMap₂'_apply', dotProduct, pow_two]

omit [T2Space M] in
/-- **Euclidean coordinates on the stable subspace.** Let `X` be gradient-like for `f`, let `p`
be a nondegenerate critical point of `f` of Morse index `m`, let `X` be differentiable at `p`,
and let `A` be the linearization of `X` at `p`. Write `H` for the second derivative of `f` read
in the chart at `p`, which is negative definite on the stable subspace of `A`. Then some
continuous linear equivalence `L` from `EuclideanSpace ℝ (Fin m)` onto the stable subspace
satisfies `-H (L u) (L u) = ‖u‖ ^ 2` for every `u`. -/
theorem _root_.TauCeti.IsGradientLike.exists_continuousLinearEquiv_stableSubspace
    (hX : IsGradientLike f X) {p : M} (hp : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f p)
    (hXp : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E).tangent
      (fun x ↦ (X x : TangentBundle 𝓘(ℝ, E) M)) p)
    {A : E →L[ℝ] E} (hA : A = sectionLinearization (F := E) 𝓘(ℝ, E) id X p) {m : ℕ}
    (hm : manifoldMorseIndex 𝓘(ℝ, E) f p = m) :
    ∃ L : EuclideanSpace ℝ (Fin m) ≃L[ℝ] A.stableSubspace, ∀ u,
      -fderiv ℝ (fderiv ℝ (f ∘ (extChartAt 𝓘(ℝ, E) p).symm)) (extChartAt 𝓘(ℝ, E) p p)
        (L u) (L u) = ‖u‖ ^ 2 := by
  obtain ⟨c, hc, hcB⟩ := hX.exists_pos_mul_norm_sq_le_fderiv_fderiv hp hXp hA
  have hB := ((isManifoldNondegenerateCriticalPoint_iff _).1 hp).contDiffAt.isSymmSndFDerivAt
    (by simp)
  set H := fderiv ℝ (fderiv ℝ (f ∘ (extChartAt 𝓘(ℝ, E) p).symm)) (extChartAt 𝓘(ℝ, E) p p)
  set Q : QuadraticForm ℝ A.stableSubspace :=
    -(H.toBilinForm.toQuadraticMap.comp A.stableSubspace.subtype)
  have hQ (v : A.stableSubspace) : Q v = -H v v := by
    simp [Q, LinearMap.BilinMap.toQuadraticMap_apply]
  have hQpos : Q.PosDef := fun v hv ↦ by
    rw [hQ, neg_pos]
    exact ContinuousLinearMap.apply_self_neg_of_mem_stableSubspace hB hc hcB v.property
      (by simpa using hv)
  obtain ⟨L, hL⟩ := hQpos.exists_continuousLinearEquiv_euclideanSpace
    ((hX.finrank_stableSubspace_eq_manifoldMorseIndex hp hXp hA).trans hm)
  exact ⟨L, fun u ↦ (hQ _).symm.trans (hL u)⟩

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

/-- **A scaled sphere in a disc is immersed.** If `ι` is differentiable with injective
differential at every point of the ball of radius `ρ`, `L` is injective, and `0 < s` with
`s * ‖L‖ < ρ`, then `u ↦ ι (s • L u)` has injective differential at every point of the unit
sphere of `V`. -/
theorem injective_mfderiv_comp_smul_coe_sphere [TopologicalSpace N] [ChartedSpace HN N]
    [Fact (finrank ℝ V = n + 1)]
    (hι : ∀ z ∈ ball (0 : F) ρ, MDifferentiableAt 𝓘(ℝ, F) I ι z ∧
      Injective (mfderiv 𝓘(ℝ, F) I ι z))
    (hs : 0 < s) (hsL : s * ‖L‖ < ρ) (hL : Injective L) (u : sphere (0 : V) 1) :
    Injective (mfderiv (𝓡 n) I (fun u : sphere (0 : V) 1 ↦ ι (s • L u)) u) := by
  obtain ⟨hιd, hιi⟩ := hι _ (mem_ball_zero_iff.2 (norm_smul_apply_coe_sphere_lt hs.le hsL u))
  have hc : MDifferentiableAt (𝓡 n) 𝓘(ℝ, V) ((↑) : sphere (0 : V) 1 → V) u :=
    (contMDiff_coe_sphere u).mdifferentiableAt one_ne_zero
  have hg : MDifferentiableAt 𝓘(ℝ, V) 𝓘(ℝ, F) (s • L) (u : V) := (s • L).mdifferentiableAt
  rw [show (fun u : sphere (0 : V) 1 ↦ ι (s • L u)) = ι ∘ (s • L) ∘ (↑) from rfl,
    mfderiv_comp u hιd (hg.comp u hc), mfderiv_comp u hg hc, ContinuousLinearMap.mfderiv_eq]
  -- `mvfderiv` of the inclusion is its `mfderiv` followed by the identification of the tangent
  -- spaces of `V` with `V`.
  have h1 : Injective (mfderiv (𝓡 n) 𝓘(ℝ, V) ((↑) : sphere (0 : V) 1 → V) u) := by
    have h := injective_mvfderiv_subtypeVal_sphere (n := n) u
    rw [mvfderiv, ContinuousLinearMap.coe_comp] at h
    exact h.of_comp
  have h2 : Injective (s • L) := fun a b h ↦ hL (smul_right_injective F hs.ne' h)
  -- The tangent spaces of `V` and `F` are `V` and `F`, so the composition of the differentials is
  -- that of the underlying maps.
  exact hιi.comp (h2.comp h1)

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

/-- **The function is strictly below its limit on a stable set.** If the orbit of `x ≠ p` under
the flow of a Weinstein structure `(ω, X, f)` tends to `p`, then `f x < f p`. -/
theorem apply_lt_of_mem_stableSet {p x : M} (hx : x ∈ hW.flow.stableSet p) (hxp : x ≠ p) :
    f x < f p := by
  refine (hW.apply_le_of_mem_stableSet hx).lt_of_ne fun hfx ↦ hxp ?_
  -- `f` is constant on the forward orbit of `x`, so the point at time `1` is critical.
  have hconst : ∀ t, 0 ≤ t → f (hW.flow t x) = f p := fun t ht ↦
    le_antisymm (hW.apply_le_of_mem_stableSet ((Flow.apply_mem_stableSet_iff _ t).2 hx))
      (hfx ▸ by simpa using hW.monotone_comp_flow x ht)
  have h0 : HasDerivAt (fun t ↦ f (hW.flow t x)) 0 1 :=
    (hasDerivAt_const (1 : ℝ) (f p)).congr_of_eventuallyEq <|
      (eventually_gt_nhds one_pos).mono fun t ht ↦ hconst t ht.le
  have hcrit : mvfderiv 𝓘(ℝ, E) f (hW.flow 1 x) = 0 := by
    by_contra h
    exact (hW.isGradientLike.mvfderiv_apply_pos h).ne' ((hW.hasDerivAt_comp_flow x 1).unique h0)
  have h1 := Flow.eq_of_mem_stableSet (hW.flow_apply_of_mvfderiv_eq_zero hcrit)
    ((Flow.apply_mem_stableSet_iff _ 1).2 hx)
  have hfix := Flow.fixed_of_mem_stableSet hx (-1)
  rw [← h1, ← Flow.map_add] at hfix
  simp only [neg_add_cancel, Flow.map_zero_apply] at hfix
  exact hfix.trans h1

/-- **No other critical point on a stable set.** A point `x ≠ p` of the stable set
of `p` under the flow of a Weinstein structure `(ω, X, f)` is not a critical point of `f`. -/
theorem notMem_criticalPoints_of_mem_stableSet {p x : M} (hx : x ∈ hW.flow.stableSet p)
    (hxp : x ≠ p) : x ∉ criticalPoints 𝓘(ℝ, E) f := fun h ↦
  hxp (Flow.eq_of_mem_stableSet (hW.flow_apply_of_mvfderiv_eq_zero (mem_criticalPoints.1 h)) hx)

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

end IsWeinsteinStructure

end SymplecticGeometry

end
