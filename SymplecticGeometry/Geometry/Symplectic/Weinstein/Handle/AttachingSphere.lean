/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Weinstein.Handle.Cobordism
public import SymplecticGeometry.Geometry.Symplectic.Weinstein.Handle.StableDisc
import SymplecticGeometry.Dynamics.Flow.Stable
import SymplecticGeometry.Geometry.Symplectic.Weinstein.Handle.Linearization

/-!
# The stable set of a critical point in the lower level of a cobordism

Let `(ω, X, f)` be a Weinstein structure with flow `φ`, and `p` a nondegenerate critical point of
`f`. This file studies where the stable set of `p`, the set of points whose orbits tend to `p`,
meets a lower regular level `f ⁻¹' {a}`. Here it treats the critical points of Morse index zero,
the local minima of `f`: their stable set is the point itself, so it does not meet any level
other than `f ⁻¹' {f p}`.

## Main declarations

* `SymplecticGeometry.IsWeinsteinStructure.stableSet_eq_singleton_of_manifoldMorseIndex_eq_zero`:
  the stable set of a nondegenerate critical point of index zero is `{p}`.
* `SymplecticGeometry.IsWeinsteinCobordism.stableSet_inter_preimage_eq_empty`: in a Weinstein
  cobordism between the levels `a` and `b`, the stable set of a nondegenerate critical point of
  index zero does not meet the lower level `f ⁻¹' {a}`.

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

end SymplecticGeometry

end
