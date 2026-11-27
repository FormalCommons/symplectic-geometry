/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Topology.Separation.Hausdorff

/-!
# Thickenings of products, and images of small closed thickenings

For the sup edistance on a product of two pseudo-emetric spaces, the open `r`-thickening of a
product set is the product of the open `r`-thickenings of its factors.

Under a continuous map `f`, the image of the closed `δ`-thickening of a compact set `K` lies,
for every small `δ`, in any given open neighbourhood of `f '' K`. Hence finitely many compact
sets whose images under continuous maps into a Hausdorff space are pairwise disjoint still have
pairwise disjoint images after a small closed thickening of each. With every map the identity,
this is a closed-thickening, eventual form of Tau Ceti's
`TauCeti.exists_thickenings_pairwiseDisjoint`, whose pair-by-pair proof the one here follows.

## Main results

* `Metric.thickening_prod`: `thickening r (s ×ˢ t) = thickening r s ×ˢ thickening r t`.
* `Metric.eventually_image_cthickening_subset`: for `δ` near `0`,
  `f '' cthickening δ K ⊆ O` when `f '' K ⊆ O`, with `K` compact and `O` open.
* `Metric.eventually_pairwise_disjoint_image_cthickening`: for `δ` near `0`, the sets
  `f i '' cthickening δ (K i)` are pairwise disjoint when the sets `f i '' K i` are.
-/

public section

open Set Topology

namespace Metric

variable {X Y : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y]

/-- The open `r`-thickening of a product set, for the sup edistance on a product of
pseudo-emetric spaces, is the product of the open `r`-thickenings of its factors. -/
theorem thickening_prod (r : ℝ) (s : Set X) (t : Set Y) :
    thickening r (s ×ˢ t) = thickening r s ×ˢ thickening r t := by
  ext x
  simp [mem_thickening_iff_infEDist_lt, Set.mem_prod, infEDist_prod]

/-- Under a continuous map `f`, the image of the closed `δ`-thickening of a compact set `K` lies,
for every `δ` close enough to `0`, in any open set `O` that contains `f '' K`. -/
theorem eventually_image_cthickening_subset {Z : Type*} [TopologicalSpace Z] {f : X → Z}
    (hf : Continuous f) {K : Set X} (hK : IsCompact K) {O : Set Z} (hO : IsOpen O)
    (hKO : f '' K ⊆ O) : ∀ᶠ δ in 𝓝 (0 : ℝ), f '' cthickening δ K ⊆ O := by
  obtain ⟨ε, hε, hεO⟩ :=
    hK.exists_cthickening_subset_open (hO.preimage hf) (image_subset_iff.1 hKO)
  filter_upwards [eventually_lt_nhds hε] with δ hδ
  exact image_subset_iff.2 ((cthickening_mono hδ.le _).trans hεO)

/-- Let `K i`, for `i` in a finite type, be compact sets in pseudo-emetric spaces `X i`, and
`f i : X i → Z` continuous maps into a Hausdorff space such that the images `f i '' K i` are
pairwise disjoint. Then, for every `δ` close enough to `0`, the images `f i '' cthickening δ (K i)`
of the closed `δ`-thickenings are still pairwise disjoint. -/
theorem eventually_pairwise_disjoint_image_cthickening {ι Z : Type*} {X : ι → Type*} [Finite ι]
    [∀ i, PseudoEMetricSpace (X i)] [TopologicalSpace Z] [T2Space Z] {f : ∀ i, X i → Z}
    (hf : ∀ i, Continuous (f i)) {K : ∀ i, Set (X i)} (hK : ∀ i, IsCompact (K i))
    (hdisj : Pairwise fun i j ↦ Disjoint (f i '' K i) (f j '' K j)) :
    ∀ᶠ δ in 𝓝 (0 : ℝ), Pairwise fun i j ↦
      Disjoint (f i '' cthickening δ (K i)) (f j '' cthickening δ (K j)) := by
  simp only [Pairwise, Filter.eventually_all]
  intro i j hij
  obtain ⟨U, V, hU, hV, hKU, hKV, hUV⟩ := SeparatedNhds.of_isCompact_isCompact
    ((hK i).image (hf i)) ((hK j).image (hf j)) (hdisj hij)
  filter_upwards [eventually_image_cthickening_subset (hf i) (hK i) hU hKU,
    eventually_image_cthickening_subset (hf j) (hK j) hV hKV] with δ hδU hδV
  exact hUV.mono hδU hδV

end Metric

end
