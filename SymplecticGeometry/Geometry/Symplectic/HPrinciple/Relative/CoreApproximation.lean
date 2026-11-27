/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.MetricSpace.Thickening
public import SymplecticGeometry.Geometry.Manifold.Morse.Core.Basic

/-!
# Holonomic approximation over all cubes of a band core

This file is to carry out holonomic approximation over all the cubes of a band core `c`
(`Morse/Core/Basic.lean`) at once, relative to an open set containing the sublevel below the
band and to a closed set of parameters, by working in the chart of each cube and carrying the
results back to the manifold.

For now it contains the first step: the cubes are pairwise disjoint compact sets, so, in a
Hausdorff manifold, small closed thickenings of the unit cubes in the charts still have pairwise
disjoint images (`BandCore.exists_pairwise_disjoint_image_cthickening`). This margin lets the
corrections made in the chart of one cube be extended to the manifold without meeting the
other cubes.

## Main declarations

* `SymplecticGeometry.BandCore.exists_pairwise_disjoint_image_cthickening`: a margin `δ'` with
  `0 < δ' ≤ 1 / 2` such that the images under the charts of the closed `δ'`-thickenings of the
  unit cubes are pairwise disjoint.

## References

* [Y. Eliashberg and N. Mishachev, *Introduction to the h-Principle*][EliashbergMishachev2002]
-/

public section

open Set Metric Topology

namespace SymplecticGeometry

namespace BandCore

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {g : M → ℝ} {a₀ a b : ℝ}

/-- **Disjoint margins around the cubes of a band core.** In a Hausdorff manifold, there is
`δ'` with `0 < δ' ≤ 1 / 2` such that the images under the charts of a band core of the closed
`δ'`-thickenings of the unit cubes `closedBall 0 1 ×ˢ {0}` are pairwise disjoint. -/
theorem exists_pairwise_disjoint_image_cthickening [T2Space M] (c : BandCore I g a₀ a b) :
    ∃ δ' > 0, δ' ≤ 1 / 2 ∧ Pairwise fun i j ↦
      Disjoint (c.chart i '' cthickening δ' (closedBall 0 1 ×ˢ {0}))
        (c.chart j '' cthickening δ' (closedBall 0 1 ×ˢ {0})) := by
  have hQ (i : c.ι) : IsCompact (closedBall 0 1 ×ˢ {0} :
      Set ((Fin (c.dim i) → ℝ) × (Fin (Module.finrank ℝ E - c.dim i) → ℝ))) :=
    (isCompact_closedBall 0 1).prod isCompact_singleton
  have hcont (i : c.ι) : Continuous (c.chart i) :=
    (c.isSmoothEmbedding_chart i).contMDiff.continuous
  -- For small `δ`, the image of the `δ`-thickening of a cube lies in any open neighbourhood of
  -- the image of the cube.
  have hsmall (i : c.ι) {O : Set M} (hO : IsOpen O)
      (hQO : c.chart i '' closedBall 0 1 ×ˢ {0} ⊆ O) :
      ∀ᶠ δ in 𝓝 (0 : ℝ), c.chart i '' cthickening δ (closedBall 0 1 ×ˢ {0}) ⊆ O := by
    obtain ⟨ε, hε, hεO⟩ :=
      (hQ i).exists_cthickening_subset_open (hO.preimage (hcont i)) (image_subset_iff.1 hQO)
    filter_upwards [gt_mem_nhds hε] with δ hδ
    exact image_subset_iff.2 ((cthickening_mono hδ.le _).trans hεO)
  -- Each pair of distinct cubes has disjoint open neighbourhoods, which the images of small
  -- thickenings of the cubes stay in.
  have hpair (i j : c.ι) : ∀ᶠ δ in 𝓝 (0 : ℝ), i ≠ j →
      Disjoint (c.chart i '' cthickening δ (closedBall 0 1 ×ˢ {0}))
        (c.chart j '' cthickening δ (closedBall 0 1 ×ˢ {0})) := by
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall fun _ h ↦ (h hij).elim
    obtain ⟨U, V, hU, hV, hQU, hQV, hUV⟩ := SeparatedNhds.of_isCompact_isCompact
      ((hQ i).image (hcont i)) ((hQ j).image (hcont j)) (c.pairwise_disjoint hij)
    filter_upwards [hsmall i hU hQU, hsmall j hV hQV] with δ hδU hδV _
    exact hUV.mono hδU hδV
  obtain ⟨δ', ⟨hδ', hδ'1⟩, hδ'0⟩ :=
    (((Filter.eventually_all.2 fun i ↦ Filter.eventually_all.2 (hpair i)).and
      (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).filter_mono nhdsWithin_le_nhds).and
      self_mem_nhdsWithin |>.exists (f := 𝓝[>] (0 : ℝ))
  exact ⟨δ', hδ'0, hδ'1, fun i j hij ↦ hδ' i j hij⟩

end BandCore

end SymplecticGeometry

end
