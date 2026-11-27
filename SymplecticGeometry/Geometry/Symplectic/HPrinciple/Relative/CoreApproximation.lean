/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.MetricSpace.Thickening
public import SymplecticGeometry.Geometry.Manifold.Morse.Core.Basic
public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Basic
import SymplecticGeometry.Geometry.Diffeomorphism.Diffeotopy.Extend
import SymplecticGeometry.Geometry.Diffeomorphism.Diffeotopy.Support
import SymplecticGeometry.Geometry.Manifold.Diffeomorph.Prod.Basic
import SymplecticGeometry.Geometry.Symplectic.HPrinciple.Relative.CubeCoordinates
import SymplecticGeometry.Topology.MetricSpace.Thickening

/-!
# Holonomic approximation over all cubes of a band core

This file is to carry out holonomic approximation over all the cubes of a band core `c`
(`Morse/Core/Basic.lean`) at once, relative to an open set containing the sublevel below the
band and to a closed set of parameters, by working in the chart of each cube and carrying the
results back to the manifold.

For now it contains three steps shared by the smooth and the continuous form.

* The cubes are pairwise disjoint compact sets, so, in a Hausdorff manifold, small closed
  thickenings of the unit cubes in the charts still have pairwise disjoint images
  (`BandCore.exists_pairwise_disjoint_image_cthickening`). This margin lets the corrections made
  in the chart of one cube be extended to the manifold without meeting the other cubes.
* A diffeotopy `h i` of `S × D i` for each cube `i`, keeping the parameter in `S` and moving only
  points over a compact `C i` of the chart's domain `D i`, gives one family of diffeotopies of
  `M` (`BandCore.exists_diffeotopy_of_cubes`). Each `h i` is extended along `id × c.chart i` by
  `TauCeti.extendDiffeotopyAlong`, and the extensions are composed. When the `C i` lie in sets
  `W i` with pairwise disjoint images, the composite acts on `c.chart i '' W i` as `h i` read
  through the chart (`TauCeti.Diffeotopy.list_prod_map_apply_of_mem`), and it fixes every point
  outside the images of the `C i`. Its slice at a parameter and a time is the diffeomorphism of
  `M` that the time slice of the composite, a diffeomorphism of `S × M` keeping the parameter
  (`TauCeti.Diffeotopy.list_prod_map_apply_fst`), induces (`Diffeomorph.slice`).
* The cube data that holonomic approximation returns change nothing over a neighbourhood of
  the relative set `B i` of each cube (`exists_relativeSet`) and outside compact sets `C i`.
  The points where they may change something thus lie over the compact sets
  `Z i := Prod.snd '' C i ∩ {z | z.1 ∉ interior (N' i)}`, which the chart sends above `a`.
  Removing their images from `N` leaves an open set `N₁` between `{g ≤ a}` and `N` over which
  the data are trivial (`BandCore.exists_isOpen_compl_image_chart_notMem_interior`).

## Main declarations

* `SymplecticGeometry.BandCore.exists_pairwise_disjoint_image_cthickening`: a margin `δ'` with
  `0 < δ' ≤ 1 / 2` such that the images under the charts of the closed `δ'`-thickenings of the
  unit cubes are pairwise disjoint.
* `SymplecticGeometry.BandCore.exists_isOpen_compl_image_chart_notMem_interior`: the open set
  `N₁`, with `{g ≤ a} ⊆ N₁ ⊆ N`, over which the cube data are trivial.
* `SymplecticGeometry.BandCore.exists_diffeotopy_of_cubes`: the smooth family of diffeotopies of
  `M`, over `S × [0, 1]`, obtained from one diffeotopy of `S × D i` per cube.

## References

* [Y. Eliashberg and N. Mishachev, *Introduction to the h-Principle*][EliashbergMishachev2002]
-/

public section

open Set Metric Topology
open scoped Manifold ContDiff

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
  have h := eventually_pairwise_disjoint_image_cthickening
    (fun i ↦ (c.isSmoothEmbedding_chart i).contMDiff.continuous)
    (fun _ ↦ (isCompact_closedBall 0 1).prod isCompact_singleton) c.pairwise_disjoint
  obtain ⟨δ', ⟨hδ', hδ'1⟩, hδ'0⟩ :=
    ((h.and (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).filter_mono
      nhdsWithin_le_nhds).and self_mem_nhdsWithin |>.exists (f := 𝓝[>] (0 : ℝ))
  exact ⟨δ', hδ'0, hδ'1, hδ'⟩

/-- **The open set where the cube data are trivial.** Let `N` be an open set containing
`{g ≤ a}` in a Hausdorff manifold, and let `δ : ℝ`. For each cube `i` of a band core `c`, let
`C i ⊆ S i × D i` be compact, where the parameter space `S i` may depend on the cube and `D i`
is the domain of `c.chart i`, with every point `(q, z)` having `z` in the open `δ`-thickening
of the unit cube; let `B i` be a set of core coordinates such that the chart sends every
point `z` of that thickening with `z.1 ∉ B i` above `a` (as item 3 of `exists_relativeSet`
gives); and let `N' i` be a neighbourhood of `B i`. Put
`Z i := Prod.snd '' C i ∩ {z | z.1 ∉ interior (N' i)}`. Then each `Z i` is compact and misses
the preimage of `{g ≤ a}` under the chart, and `N₁ := N ∩ ⋂ i, (c.chart i '' Z i)ᶜ` is open,
contains `{g ≤ a}` and is contained in `N`. Moreover, if `(q, z) ∈ C i` and `c.chart i z ∈ N₁`,
then `z.1 ∈ interior (N' i)`. -/
theorem exists_isOpen_compl_image_chart_notMem_interior [T2Space M] (c : BandCore I g a₀ a b)
    {N : Set M} (hN : IsOpen N) (haN : {x | g x ≤ a} ⊆ N) {S : c.ι → Type*}
    [∀ i, TopologicalSpace (S i)]
    {C : ∀ i, Set (S i × (Fin (c.dim i) → ℝ) × (Fin (Module.finrank ℝ E - c.dim i) → ℝ))}
    (hC : ∀ i, IsCompact (C i)) {δ : ℝ}
    (hCδ : ∀ i, ∀ p ∈ C i, p.2 ∈ thickening δ (closedBall 0 1 ×ˢ {0}))
    {B N' : ∀ i, Set (Fin (c.dim i) → ℝ)}
    (hB : ∀ i, ∀ z ∈ thickening δ (closedBall 0 1 ×ˢ {0}), z.1 ∉ B i → a < g (c.chart i z))
    (hBN' : ∀ i, N' i ∈ 𝓝ˢ (B i)) :
    ∃ N₁ : Set M,
      N₁ = N ∩ ⋂ i, (c.chart i '' (Prod.snd '' C i ∩ {z | z.1 ∉ interior (N' i)}))ᶜ ∧
      (∀ i, IsCompact (Prod.snd '' C i ∩ {z | z.1 ∉ interior (N' i)}) ∧
        Disjoint (Prod.snd '' C i ∩ {z | z.1 ∉ interior (N' i)})
          (c.chart i ⁻¹' {x | g x ≤ a})) ∧
      IsOpen N₁ ∧ {x | g x ≤ a} ⊆ N₁ ∧ N₁ ⊆ N ∧
      ∀ i, ∀ p ∈ C i, c.chart i p.2 ∈ N₁ → p.2.1 ∈ interior (N' i) := by
  have hZ (i : c.ι) : IsCompact (Prod.snd '' C i ∩ {z | z.1 ∉ interior (N' i)}) :=
    ((hC i).image continuous_snd).inter_right
      (isOpen_interior.isClosed_compl.preimage continuous_fst)
  have hZa (i : c.ι) : Disjoint (Prod.snd '' C i ∩ {z | z.1 ∉ interior (N' i)})
      (c.chart i ⁻¹' {x | g x ≤ a}) := by
    refine disjoint_left.2 ?_
    rintro z ⟨⟨p, hp, rfl⟩, hz⟩ hga
    exact (hga : g (c.chart i p.2) ≤ a).not_gt
      (hB i _ (hCδ i p hp) fun hzB ↦ hz (subset_interior_iff_mem_nhdsSet.2 (hBN' i) hzB))
  refine ⟨_, rfl, fun i ↦ ⟨hZ i, hZa i⟩, ?_, fun x hx ↦ ⟨haN hx, ?_⟩, inter_subset_left,
    fun i p hp hx ↦ ?_⟩
  · exact hN.inter (isOpen_iInter_of_finite fun i ↦
      ((hZ i).image (c.isSmoothEmbedding_chart i).contMDiff.continuous).isClosed.isOpen_compl)
  · refine mem_iInter.2 fun i ↦ ?_
    rintro ⟨z, hz, rfl⟩
    exact disjoint_left.1 (hZa i) hz hx
  · by_contra hz
    exact mem_iInter.1 hx.2 i ⟨p.2, ⟨mem_image_of_mem _ hp, hz⟩, rfl⟩

variable [T2Space M] [FiniteDimensional ℝ E] [IsManifold I ∞ M]

/-- **Extending cube diffeotopies to the manifold.** Let `c` be a band core in a Hausdorff
manifold `M`, `S` a normed space, and for each cube `i` let `h i` be a diffeotopy of `S × D i`,
`D i` the domain of `c.chart i`, that keeps the parameter in `S` and fixes every `(q, z)` with
`z` outside a compact set `C i`. Let `C i ⊆ W i`, with the images `c.chart i '' W i` pairwise
disjoint. Then there is a smooth `Φ : (S × [0, 1]) × M → M` such that

* each slice `x ↦ Φ (p, x)` is a diffeomorphism of `M`, so a local diffeomorphism;
* `Φ ((q, 0), x) = x`;
* `Φ ((q, t), c.chart i z) = c.chart i (h i (t, (q, z))).2` for `z ∈ W i`;
* `Φ (p, x) = x` for `x` outside the union of the `c.chart i '' C i`;
* if, for one `q`, every `h i` fixes every `(q, z)` at every time, then `Φ ((q, t), x) = x`
  for all `t` and `x`. -/
theorem exists_diffeotopy_of_cubes (c : BandCore I g a₀ a b) {S : Type*}
    [NormedAddCommGroup S] [NormedSpace ℝ S]
    (h : ∀ i, TauCeti.Diffeotopy
      (𝓘(ℝ, S).prod 𝓘(ℝ, (Fin (c.dim i) → ℝ) × (Fin (Module.finrank ℝ E - c.dim i) → ℝ))) ∞
      (S × ((Fin (c.dim i) → ℝ) × (Fin (Module.finrank ℝ E - c.dim i) → ℝ))))
    (hfst : ∀ i t p, (h i (t, p)).1 = p.1)
    {C W : ∀ i, Set ((Fin (c.dim i) → ℝ) × (Fin (Module.finrank ℝ E - c.dim i) → ℝ))}
    (hC : ∀ i, IsCompact (C i)) (hh : ∀ i t p, p.2 ∉ C i → h i (t, p) = p)
    (hCW : ∀ i, C i ⊆ W i)
    (hW : Pairwise fun i j ↦ Disjoint (c.chart i '' W i) (c.chart j '' W j)) :
    ∃ Φ : (S × unitInterval) × M → M,
      ContMDiff ((𝓘(ℝ, S).prod (𝓡∂ 1)).prod I) I ∞ Φ ∧
      (∀ p, ∃ f : M ≃ₘ⟮I, I⟯ M, ∀ x, f x = Φ (p, x)) ∧
      (∀ p, IsLocalDiffeomorph I I ∞ fun x ↦ Φ (p, x)) ∧
      (∀ q x, Φ ((q, 0), x) = x) ∧
      (∀ i q t, ∀ z ∈ W i, Φ ((q, t), c.chart i z) = c.chart i (h i (t, (q, z))).2) ∧
      (∀ p, ∀ x ∉ ⋃ i, c.chart i '' C i, Φ (p, x) = x) ∧
      ∀ q, (∀ i t z, h i (t, (q, z)) = (q, z)) → ∀ t x, Φ ((q, t), x) = x := by
  let Ψ (i : c.ι) := TauCeti.extendDiffeotopyAlong (c.isLocalDiffeomorph_chart i)
    (c.isOpenEmbedding_chart i) (h i) (hC i) (hh i)
  have hΨ (i : c.ι) (t : unitInterval) (q : S) (z) :
      Ψ i (t, (q, c.chart i z)) = (q, c.chart i (h i (t, (q, z))).2) := by
    rw [TauCeti.extendDiffeotopyAlong_apply_prodMk, hfst]
  have hΨC (i : c.ι) (t : unitInterval) (q : S) {y : M} (hy : y ∉ c.chart i '' C i) :
      Ψ i (t, (q, y)) = (q, y) :=
    TauCeti.extendDiffeotopyAlong_apply_of_notMem _ _ _ _ _ t q hy
  let l := (Finset.univ : Finset c.ι).toList
  have hl (i : c.ι) : i ∈ l := Finset.mem_toList.2 (Finset.mem_univ i)
  let P := (l.map Ψ).prod
  have hPfst (t : unitInterval) (p : S × M) : (P (t, p)).1 = p.1 :=
    TauCeti.Diffeotopy.list_prod_map_apply_fst
      (fun j _ ↦ TauCeti.fst_extendDiffeotopyAlong_apply _ _ _ _ _ (hfst j)) t p
  have hslice (t : unitInterval) (p : S × M) : (P.timeSlice t p).1 = p.1 := by
    rw [TauCeti.Diffeotopy.timeSlice_apply, hPfst]
  let f (p : S × unitInterval) : M ≃ₘ⟮I, I⟯ M := (P.timeSlice p.2).slice (hslice p.2) p.1
  have hf (p : S × unitInterval) (x : M) : f p x = (P (p.2, (p.1, x))).2 := by
    rw [Diffeomorph.slice_apply, TauCeti.Diffeotopy.timeSlice_apply]
  have hPW : l.Pairwise fun i j ↦
      Disjoint (univ ×ˢ (c.chart i '' W i) : Set (S × M)) (univ ×ˢ (c.chart j '' W j)) :=
    (Finset.nodup_toList _).pairwise_of_forall_ne fun i _ j _ hij ↦
      disjoint_prod.2 (.inr (hW hij))
  refine ⟨fun p ↦ (P (p.1.2, (p.1.1, p.2))).2, ?_, fun p ↦ ⟨f p, hf p⟩, fun p ↦ ?_,
    fun q x ↦ by simp only [TauCeti.Diffeotopy.apply_zero], fun i q t z hz ↦ ?_,
    fun p x hx ↦ ?_, fun q hq t x ↦ ?_⟩
  · exact contMDiff_snd.comp (P.contMDiff.comp (contMDiff_fst.snd.prodMk
      (contMDiff_fst.fst.prodMk contMDiff_snd)))
  · simpa only [← hf] using (f p).isLocalDiffeomorph
  · exact congrArg Prod.snd ((TauCeti.Diffeotopy.list_prod_map_apply_of_mem hPW t
      (fun j _ y hy ↦ hΨC j t y.1 fun hyC ↦ hy ⟨mem_univ _, image_mono (hCW j) hyC⟩) (hl i)
      (x := (q, c.chart i z)) ⟨mem_univ _, mem_image_of_mem _ hz⟩).trans (hΨ i t q z))
  · refine congrArg Prod.snd (TauCeti.Diffeotopy.list_prod_map_apply_eq_self_of_notMem_biUnion
      (W := fun i ↦ (univ ×ˢ (c.chart i '' C i) : Set (S × M))) (x := (p.1, x)) p.2
      (fun j _ y hy ↦ hΨC j p.2 y.1 fun hyC ↦ hy ⟨mem_univ _, hyC⟩) fun hmem ↦ ?_)
    obtain ⟨i, -, hi⟩ := mem_iUnion₂.1 hmem
    exact hx (mem_iUnion.2 ⟨i, hi.2⟩)
  · refine congrArg Prod.snd
      (TauCeti.Diffeotopy.list_prod_map_apply_eq_self (x := (q, x)) fun i _ ↦ ?_)
    by_cases hx : x ∈ c.chart i '' C i
    · obtain ⟨z, -, rfl⟩ := hx
      rw [hΨ, hq]
    · exact hΨC i t q hx

end BandCore

end SymplecticGeometry

end
