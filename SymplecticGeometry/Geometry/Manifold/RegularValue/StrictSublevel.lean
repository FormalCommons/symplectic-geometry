/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.RegularValue.Scalar.Sublevel.Basic

/-!
# Open subsets of the strict sublevel are smooth in the sublevel manifold

Let `f : M → ℝ` be a `C^m` function, `1 ≤ m`, on a boundaryless manifold modelled on a real space
of dimension `n + 1`, and let `a` be a regular value of `f`. Tau Ceti gives the sublevel
`{x | f x ≤ a}` the atlas `TauCeti.scalarRegularSublevelChartedSpace`, modelled on
`EuclideanHalfSpace (n + 1)`, and proves that the inclusion of the sublevel into `M` is `C^m`
(`TauCeti.contMDiff_subtypeVal_scalarRegularSublevel`).

This file goes the other way on the strict sublevel: for an open set `U` of `M` contained in
`{x | f x < a}`, with its open-subset manifold structure, the inclusion of `U` into the sublevel
manifold is `C^m` (`TauCeti.contMDiff_codRestrict_scalarRegularSublevel`). Taking
`U = {x | f x < a}` gives the smoothness of the inclusion of the strict sublevel.

The proof reads the inclusion in the preferred chart of the sublevel at a point `x` of `U`. By
`TauCeti.exists_scalarRegularSublevelChartAt_of_lt`, near `x` this chart is the extended chart
of `M` at `x`, followed by a fixed linear equivalence and a translation, so the inclusion is
`C^m` at `x`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Proposition 5.47.
-/

public section

open Module Set TopologicalSpace
open scoped ContDiff Manifold Topology

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] {f : M → ℝ} {a : ℝ}
  {n : ℕ} [I.Boundaryless] [FiniteDimensional ℝ E]

/-- Let `a` be a regular value of a `C^m` function `f : M → ℝ`, `1 ≤ m`. The inclusion of an open
set `U ⊆ {x | f x < a}` of `M`, with its open-subset manifold structure, into the sublevel
`{x | f x ≤ a}`, with its preferred atlas modelled on `EuclideanHalfSpace (n + 1)`, is `C^m`. -/
theorem contMDiff_codRestrict_scalarRegularSublevel {m : ℕ∞ω} [IsManifold I m M]
    (hreg : IsRegularValue I 𝓘(ℝ) f a) (hn : finrank ℝ E = n + 1) (hm : 1 ≤ m)
    (hfm : ContMDiff I 𝓘(ℝ) m f) {U : Opens M} (hU : (U : Set M) ⊆ f ⁻¹' Iio a) :
    letI := scalarRegularSublevelChartedSpace (hfm.of_le hm) hreg hn
    ContMDiff I (𝓡∂ (n + 1)) m
      (codRestrict (Subtype.val : U → M) {x | f x ≤ a} fun x ↦ (hU x.property).le) := by
  let := scalarRegularSublevelChartedSpace (hfm.of_le hm) hreg hn
  intro x
  have hcont : Continuous (codRestrict (Subtype.val : U → M) {x | f x ≤ a}
      fun x ↦ (hU x.property).le) := continuous_subtypeVal.codRestrict _
  rw [contMDiffAt_iff_target]
  refine ⟨hcont.continuousAt, ?_⟩
  obtain ⟨r, -, -, happly⟩ := exists_scalarRegularSublevelChartAt_of_lt (hfm.of_le hm) hreg hn
    (x := ⟨x, (hU x.property).le⟩) (hU x.property)
  set T := ContinuousLinearEquiv.ofFinrankEq (𝕜 := ℝ) (E := E)
    (F := EuclideanSpace ℝ (Fin (n + 1))) (by rw [hn, finrank_euclideanSpace_fin])
  have hsmooth : ContMDiffAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) m
      (fun w : U ↦ T (extChartAt I (x : M) w - extChartAt I (x : M) x) +
        EuclideanSpace.single 0 (2 * r)) x :=
    ((T : E →L[ℝ] EuclideanSpace ℝ (Fin (n + 1))).contMDiff.contMDiffAt.comp x
      ((contMDiffAt_extChartAt.comp x contMDiff_subtypeVal.contMDiffAt).sub
        contMDiffAt_const)).add contMDiffAt_const
  refine hsmooth.congr_of_eventuallyEq ?_
  filter_upwards [hcont.continuousAt.preimage_mem_nhds
    ((scalarRegularSublevelChartAt (hfm.of_le hm) hreg hn _).open_source.mem_nhds
      (mem_scalarRegularSublevelChartAt_source (hfm.of_le hm) hreg hn _))] with w hw
  rw [Function.comp_apply, extChartAt_coe, Function.comp_apply,
    scalarRegularSublevelChartedSpace_chartAt, modelWithCornersEuclideanHalfSpace_apply]
  exact (happly _ hw).2

end TauCeti

end
