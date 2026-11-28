/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.MetricSpace.Thickening
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.SmoothFamily.Basic
public import SymplecticGeometry.Geometry.Manifold.Morse.Core.Basic
public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Basic
import SymplecticGeometry.Analysis.Calculus.HolonomicApproximation.Parametric
import SymplecticGeometry.Geometry.Diffeomorphism.Diffeotopy.Basic
import SymplecticGeometry.Geometry.Diffeomorphism.Diffeotopy.Extend
import SymplecticGeometry.Geometry.Diffeomorphism.Diffeotopy.Slice
import SymplecticGeometry.Geometry.Diffeomorphism.Diffeotopy.Support
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Pullback.LocalDiffeomorph
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Smooth
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.SmoothFamily.NormedSpace
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.SmoothFamily.PartialDiffeomorph
import SymplecticGeometry.Geometry.Symplectic.HPrinciple.FormalPrimitive
import SymplecticGeometry.Geometry.Symplectic.HPrinciple.Relative.CubeCoordinates
import SymplecticGeometry.Topology.MetricSpace.Thickening
import TauCeti.Geometry.Symplectic.Manifold.RelativeMoser
import TauCeti.Topology.Algebra.Support

/-!
# Holonomic approximation over all cubes of a band core

This file is to carry out holonomic approximation over all the cubes of a band core `c`
(`Morse/Core/Basic.lean`) at once, relative to an open set containing the sublevel below the
band and to a closed set of parameters, by working in the chart of each cube and carrying the
results back to the manifold.

It contains these steps, shared by the smooth and the continuous form.

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
  outside the images of the `C i`. Since the composite keeps the parameter
  (`TauCeti.Diffeotopy.list_prod_map_apply_fst`), its slices at a parameter and a time are
  diffeomorphisms of `M` (`TauCeti.Diffeotopy.slice`).
* The cube data that holonomic approximation returns change nothing over a neighbourhood of
  the relative set `B i` of each cube (`exists_relativeSet`) and outside compact sets `C i`.
  The points where they may change something thus lie over the compact sets
  `Z i := Prod.snd '' C i ∩ {z | z.1 ∉ interior (N' i)}`, which the chart sends above `a`.
  Removing their images from `N` leaves an open set `N₁` between `{g ≤ a}` and `N` over which
  the data are trivial (`BandCore.exists_isOpen_compl_image_chart_notMem_interior`).
* A correction `corr i` of one-forms on `D i`, depending smoothly on `q ∈ S`, for each cube,
  vanishing off a compact `C i`, gives one smooth family of one-forms on `M`
  (`BandCore.exists_oneForm_of_cubes`): to a smooth family `B` it adds, for each cube, the
  extension by zero of `corr i (q, ·)` along the inverse of
  the chart (`TauCeti.SmoothForm.extendByZeroAlong`, `BandCore.chartPartialDiffeomorph`). It is
  smooth by `SymplecticGeometry.IsSmoothFamily.extendByZeroAlong`. When the `C i` lie in sets
  `W i` with pairwise disjoint images, the other corrections vanish on `c.chart i '' W i`, so
  there the reading of the new family in the chart of cube `i` is that of `B` plus `corr i`
  (`TauCeti.mpullback_symm_extendByZeroAlong`).
* At the points of the open set `U ⊆ Λ × M` of `exists_stagePath`, the segments from `τ l` to
  `α l + d (B' (s l))` must stay nondegenerate (`BandCore.exists_isOpen_nondegenerate_of_cubes`).
  The set `U` is the union of `univ ×ˢ N₁`, where the segment is constantly `τ l`, and of the
  images under `id × c.chart i` of open sets on which the segment's reading in the chart is
  nondegenerate. That reading is computed from the reading of `B'` above, with
  `TauCeti.mpullback_symm_mextDerivₗ` for the exterior derivative, and nondegeneracy carries back
  to `M` by `TauCeti.SmoothTwoForm.nondegenerate_bilinFormAt_iff_of_isInvertible_mfderiv`, since
  the chart is a local diffeomorphism (`BandCore.isLocalDiffeomorph_chart`).
* `BandCore.exists_stageData_of_cubes` puts these steps together. From one diffeotopy, one
  correction and one open set of nondegenerate readings per cube, of the shape that holonomic
  approximation in each chart returns, it gives the diffeotopy `Φ`, the one-forms `B'` and the
  open sets `N₁` and `U` that `exists_stagePath` (`Relative/StagePath.lean`) asks for. On `N₁`
  the readings of `B'` and `B` agree, which gives `B' = B` there by
  `TauCeti.mpullback_apply_eq_mpullback_apply_iff`, since the chart is a local diffeomorphism.
* `BandCore.exists_approximation_family` is the smooth form. In the chart of each cube it reads
  the one-forms, with the formal primitive of the reading of `τ - α`
  (`SymplecticGeometry.formalPrimitive`) as first-order part, takes a margin of nondegeneracy
  for the reading of `τ`
  (`SymplecticGeometry.IsSmoothFamily.exists_pos_forall_nondegenerate_sub_smul`),
  makes the datum holonomic near `P₀` by a cutoff in the parameter
  (`SymplecticGeometry.exists_contDiff_fderiv_eq_of_fderiv_eq_on_param`), and applies
  `SymplecticGeometry.exists_holonomic_approximation_family` relative to the core points of
  `BandCore.exists_relativeSet`. Near the moved cube the exterior derivative of the
  approximation is close to the reading of `τ - α`
  (`SymplecticGeometry.norm_extDeriv_sub_le_of_norm_fderiv_sub_formalPrimitive_le`), so the
  segments stay nondegenerate, and `BandCore.exists_stageData_of_cubes` gives the data on `M`.

## Main declarations

* `SymplecticGeometry.BandCore.exists_pairwise_disjoint_image_cthickening`: a margin `δ'` with
  `0 < δ' ≤ 1 / 2` such that the images under the charts of the closed `δ'`-thickenings of the
  unit cubes are pairwise disjoint.
* `SymplecticGeometry.BandCore.exists_isOpen_compl_image_chart_notMem_interior`: the open set
  `N₁`, with `{g ≤ a} ⊆ N₁ ⊆ N`, over which the cube data are trivial.
* `SymplecticGeometry.BandCore.exists_diffeotopy_of_cubes`: the smooth family of diffeotopies of
  `M`, over `S × [0, 1]`, obtained from one diffeotopy of `S × D i` per cube.
* `SymplecticGeometry.BandCore.exists_oneForm_of_cubes`: the smooth family of one-forms on `M`
  obtained from a smooth family `B` and one correction on `S × D i` per cube.
* `SymplecticGeometry.BandCore.exists_isOpen_nondegenerate_of_cubes`: the open set `U` of
  parameters and points at which the segments of two-forms towards the corrected forms stay
  nondegenerate.
* `SymplecticGeometry.BandCore.exists_stageData_of_cubes`: from per-cube data of the shape that
  holonomic approximation returns, the diffeotopy, the corrected one-forms and the open sets
  `N₁` and `U` that `exists_stagePath` needs.
* `SymplecticGeometry.BandCore.exists_approximation_family`: holonomic approximation over all
  cubes of a band core for smooth families over a finite-dimensional normed space, in the form
  that `exists_stagePath` takes.

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
    ((h.and (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 2))).filter_mono
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
  have hPW : l.Pairwise fun i j ↦
      Disjoint (univ ×ˢ (c.chart i '' W i) : Set (S × M)) (univ ×ˢ (c.chart j '' W j)) :=
    (Finset.nodup_toList _).pairwise_of_forall_ne fun i _ j _ hij ↦
      disjoint_prod.2 (.inr (hW hij))
  refine ⟨fun p ↦ (P (p.1.2, (p.1.1, p.2))).2, ?_,
    fun p ↦ ⟨P.slice hPfst p.1 p.2, P.slice_apply hPfst p.1 p.2⟩, fun p ↦ ?_,
    fun q x ↦ by simp only [TauCeti.Diffeotopy.apply_zero], fun i q t z hz ↦ ?_,
    fun p x hx ↦ ?_, fun q hq t x ↦ ?_⟩
  · simpa only [TauCeti.Diffeotopy.slice_apply] using P.contMDiff_slice hPfst
  · simpa only [TauCeti.Diffeotopy.coe_slice] using (P.slice hPfst p.1 p.2).isLocalDiffeomorph
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

open TauCeti in
/-- **Carrying cube corrections of one-forms to the manifold.** Let `c` be a band core in a
Hausdorff manifold `M`, `S` a normed space, `B` a smooth family over `S` of one-forms on `M`, and
for each cube `i` let `corr i : S × D i → D i [⋀^Fin 1]→L[ℝ] ℝ`, `D i` the domain of `c.chart i`,
be smooth and vanish at every `(q, z)` with `z` outside a compact set `C i`. Let `C i ⊆ W i`, with
the images `c.chart i '' W i` pairwise disjoint. Then there is a smooth family `B'` over `S` of
one-forms on `M` such that

* `B' q` agrees with `B q` outside the union of the `c.chart i '' C i`;
* for `z ∈ W i`, the pullback of `B' q` along `c.chart i` at `z` minus that of `B q` is
  `corr i (q, z)`;
* if every `corr i (q, ·)` vanishes, then `B' q = B q`.

The family is `B q` plus the sum over the cubes of the extensions by zero of `corr i (q, ·)` along
the inverses of the charts. -/
theorem exists_oneForm_of_cubes (c : BandCore I g a₀ a b) {S : Type*}
    [NormedAddCommGroup S] [NormedSpace ℝ S] {B : S → SmoothForm I M ℝ 1}
    (hB : IsSmoothFamily 𝓘(ℝ, S) B)
    {corr : ∀ i, S × ((Fin (c.dim i) → ℝ) × (Fin (Module.finrank ℝ E - c.dim i) → ℝ)) →
      ((Fin (c.dim i) → ℝ) × (Fin (Module.finrank ℝ E - c.dim i) → ℝ)) [⋀^Fin 1]→L[ℝ] ℝ}
    (hcorr : ∀ i, ContDiff ℝ ∞ (corr i))
    {C W : ∀ i, Set ((Fin (c.dim i) → ℝ) × (Fin (Module.finrank ℝ E - c.dim i) → ℝ))}
    (hC : ∀ i, IsCompact (C i)) (hcorrC : ∀ i q, ∀ z ∉ C i, corr i (q, z) = 0)
    (hCW : ∀ i, C i ⊆ W i)
    (hW : Pairwise fun i j ↦ Disjoint (c.chart i '' W i) (c.chart j '' W j)) :
    ∃ B' : S → SmoothForm I M ℝ 1, IsSmoothFamily 𝓘(ℝ, S) B' ∧
      (∀ q, ∀ x ∉ ⋃ i, c.chart i '' C i, (B' q).val x = (B q).val x) ∧
      (∀ i q, ∀ z ∈ W i,
        (mpullback 𝓘(ℝ, (Fin (c.dim i) → ℝ) × (Fin (Module.finrank ℝ E - c.dim i) → ℝ)) I
            (c.chart i) (B' q).val z -
          mpullback 𝓘(ℝ, (Fin (c.dim i) → ℝ) × (Fin (Module.finrank ℝ E - c.dim i) → ℝ)) I
            (c.chart i) (B q).val z :
          ((Fin (c.dim i) → ℝ) × (Fin (Module.finrank ℝ E - c.dim i) → ℝ)) [⋀^Fin 1]→L[ℝ] ℝ) =
          corr i (q, z)) ∧
      ∀ q, (∀ i z, corr i (q, z) = 0) → B' q = B q := by
  have htgt (i : c.ι) {s} : s ⊆ (c.chartPartialDiffeomorph i).target := by
    rw [chartPartialDiffeomorph_target]
    exact subset_univ s
  have hsupp (i : c.ι) (q : S) : tsupport (fun z ↦ corr i (q, z)) ⊆ C i :=
    TauCeti.tsupport_subset_of_forall_notMem_eq_zero (hcorrC i q) (hC i).isClosed
  -- The extension by zero of the correction of cube `i`.
  let ext (i : c.ι) (q : S) : SmoothForm I M ℝ 1 :=
    TauCeti.SmoothForm.extendByZeroAlong (c.chartPartialDiffeomorph i) (fun z ↦ corr i (q, z))
      ((hcorr i).comp (contDiff_const.prodMk contDiff_id))
      ((hC i).of_isClosed_subset (isClosed_tsupport _) (hsupp i q)) (htgt i)
  have hext (i : c.ι) (q : S) : (ext i q).val =
      TauCeti.RoughForm.extendByZeroAlong (c.chartPartialDiffeomorph i) fun z ↦ corr i (q, z) :=
    TauCeti.SmoothForm.coe_extendByZeroAlong _ _ _ _ _
  -- Off `c.chart i '' C i`, the extension of the correction of cube `i` vanishes.
  have hext0 (i : c.ι) (q : S) {x : M} (hx : x ∉ c.chart i '' C i) : (ext i q).val x = 0 := by
    rw [hext]
    refine TauCeti.RoughForm.extendByZeroAlong_apply_of_notMem_image _ fun hx' ↦ hx ?_
    rw [chartPartialDiffeomorph_symm_apply] at hx'
    exact image_mono (hsupp i q) hx'
  have hval (q : S) (x : M) :
      (B q + ∑ i, ext i q).val x = (B q).val x + ∑ i, (ext i q).val x := by
    simp only [SmoothBundleForm.add_apply, SmoothBundleForm.sum_apply]
  refine ⟨fun q ↦ B q + ∑ i, ext i q, hB.add (IsSmoothFamily.sum fun i _ ↦ ?_),
    fun q x hx ↦ ?_, fun i q z hz ↦ ?_, fun q hq ↦ ?_⟩
  · have h := contMDiff_iff_contDiff.2 (hcorr i)
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod] at h
    exact IsSmoothFamily.extendByZeroAlong h (hC i) (htgt i) (hcorrC i) (hext i)
  · rw [hval, Finset.sum_eq_zero fun i _ ↦ hext0 i q fun hxi ↦ hx (mem_iUnion.2 ⟨i, hxi⟩),
      add_zero]
  · -- At `c.chart i z`, only the correction of cube `i` is left.
    have hx : (B q + ∑ j, ext j q).val (c.chart i z) =
        ((B q).val + (ext i q).val) (c.chart i z) := by
      rw [hval, Pi.add_apply, Finset.sum_eq_single i (fun j _ hji ↦ hext0 j q fun ⟨w, hw, hwz⟩ ↦
        (hW hji).ne_of_mem ⟨w, hCW j hw, rfl⟩ ⟨z, hz, rfl⟩ hwz)
        (fun h ↦ (h (Finset.mem_univ i)).elim)]
    rw [mpullback_apply_congr hx, mpullback_add, Pi.add_apply, add_sub_cancel_left, hext,
      ← chartPartialDiffeomorph_symm_apply,
      TauCeti.mpullback_symm_extendByZeroAlong _ _ (by simp) (htgt i (mem_univ z))]
  · have h0 (i : c.ι) : ext i q = 0 := by
      have hz : (fun z ↦ corr i (q, z)) = 0 := funext (hq i)
      simp only [ext, hz, TauCeti.SmoothForm.extendByZeroAlong_zero]
    simp only [h0, Finset.sum_const_zero, add_zero]

omit [T2Space M] in
open TauCeti in
/-- **The open set where the segments of two-forms stay nondegenerate.** Let `c` be a band core in
a manifold `M`, `s : Λ → S`, `τ α : Λ → SmoothTwoForm I M` with `τ l` nondegenerate for `l ∈ K`,
and `B B'` families over `S` of one-forms on `M`. Write `T` for the open `δ'`-thickening of the
unit cube in the domain `D i` of `c.chart i`. Suppose that

* on a set `N`, `τ l = α l + d (B (s l))` for every `l`;
* on an open `N₁ ⊆ N`, `B' q = B q` for every `q`;
* on `T`, the reading of `B' q` in the chart of cube `i` is the reading of `B q` plus
  `corr i (q, ·)`, a smooth correction (as `BandCore.exists_oneForm_of_cubes` gives);
* `V i ⊆ Λ × D i` is open, and at its points `(l, z)` with `l ∈ K` and `z ∈ T ∩ ball 0 2`, for
  every `r ∈ [0, 1]`, the reading at `z` of `τ l + r • (α l + d (B (s l)) - τ l)` plus
  `r • d (corr i (s l, ·)) z` is nondegenerate.

Let `U` be the union of `univ ×ˢ N₁` and of the images of `V i ∩ (univ ×ˢ (T ∩ ball 0 2))` under
`id × c.chart i`. Then `U` is open, contains `K ×ˢ N₁` and each `(l, c.chart i z)` with
`(l, z) ∈ V i` and `z ∈ T ∩ ball 0 2`, and at each of its points `(l, y)` with `l ∈ K` every
`τ l + r • (α l + d (B' (s l)) - τ l)`, `r ∈ [0, 1]`, is nondegenerate at `y`. On `univ ×ˢ N₁`
the segment is constantly `τ l`; on the image of `V i` its reading is the one of the hypothesis,
and nondegeneracy carries back along the chart, a local diffeomorphism. -/
theorem exists_isOpen_nondegenerate_of_cubes (c : BandCore I g a₀ a b) {Λ S : Type*}
    [TopologicalSpace Λ] [NormedAddCommGroup S] [NormedSpace ℝ S] {K : Set Λ} {s : Λ → S}
    {τ α : Λ → SmoothTwoForm I M} (hnd : ∀ l ∈ K, (τ l).IsNondegenerate)
    {B B' : S → SmoothForm I M ℝ 1} {N N₁ : Set M}
    (hτN : ∀ l, ∀ x ∈ N, (τ l).val x = (α l + mextDerivₗ I 1 (B (s l))).val x)
    (hN₁ : IsOpen N₁) (hN₁N : N₁ ⊆ N) (hB'N₁ : ∀ q, ∀ x ∈ N₁, (B' q).val x = (B q).val x)
    {δ' : ℝ}
    {corr : ∀ i, S × ((Fin (c.dim i) → ℝ) × (Fin (Module.finrank ℝ E - c.dim i) → ℝ)) →
      ((Fin (c.dim i) → ℝ) × (Fin (Module.finrank ℝ E - c.dim i) → ℝ)) [⋀^Fin 1]→L[ℝ] ℝ}
    (hcorr : ∀ i, ContDiff ℝ ∞ (corr i))
    (hB' : ∀ i q, ∀ z ∈ thickening δ' (closedBall 0 1 ×ˢ {0}),
      (mpullback 𝓘(ℝ, (Fin (c.dim i) → ℝ) × (Fin (Module.finrank ℝ E - c.dim i) → ℝ)) I
          (c.chart i) (B' q).val z -
        mpullback 𝓘(ℝ, (Fin (c.dim i) → ℝ) × (Fin (Module.finrank ℝ E - c.dim i) → ℝ)) I
          (c.chart i) (B q).val z :
        ((Fin (c.dim i) → ℝ) × (Fin (Module.finrank ℝ E - c.dim i) → ℝ)) [⋀^Fin 1]→L[ℝ] ℝ) =
        corr i (q, z))
    {V : ∀ i, Set (Λ × (Fin (c.dim i) → ℝ) × (Fin (Module.finrank ℝ E - c.dim i) → ℝ))}
    (hV : ∀ i, IsOpen (V i))
    (hVnd : ∀ i, ∀ p ∈ V i, p.1 ∈ K →
      p.2 ∈ thickening δ' (closedBall 0 1 ×ˢ {0}) ∩ ball 0 2 → ∀ r ∈ Icc (0 : ℝ) 1,
      (MultilinearMap.toBilinMap (@HAdd.hAdd
        (((Fin (c.dim i) → ℝ) × (Fin (Module.finrank ℝ E - c.dim i) → ℝ)) [⋀^Fin 2]→L[ℝ] ℝ)
        (((Fin (c.dim i) → ℝ) × (Fin (Module.finrank ℝ E - c.dim i) → ℝ)) [⋀^Fin 2]→L[ℝ] ℝ) _ _
        (mpullback 𝓘(ℝ, (Fin (c.dim i) → ℝ) × (Fin (Module.finrank ℝ E - c.dim i) → ℝ)) I
          (c.chart i) (τ p.1 + r • (α p.1 + mextDerivₗ I 1 (B (s p.1)) - τ p.1)).val p.2)
        (r • extDeriv (fun z ↦ corr i (s p.1, z)) p.2)).toMultilinearMap).Nondegenerate) :
    ∃ U : Set (Λ × M),
      U = univ ×ˢ N₁ ∪ ⋃ i, Prod.map id (c.chart i) ''
        (V i ∩ univ ×ˢ (thickening δ' (closedBall 0 1 ×ˢ {0}) ∩ ball 0 2)) ∧
      IsOpen U ∧ K ×ˢ N₁ ⊆ U ∧
      (∀ i, ∀ p ∈ V i, p.2 ∈ thickening δ' (closedBall 0 1 ×ˢ {0}) ∩ ball 0 2 →
        (p.1, c.chart i p.2) ∈ U) ∧
      ∀ p ∈ U, p.1 ∈ K → ∀ r ∈ Icc (0 : ℝ) 1,
        ((τ p.1 + r • (α p.1 + mextDerivₗ I 1 (B' (s p.1)) - τ p.1)).bilinFormAt
          p.2).Nondegenerate := by
  have hT (i : c.ι) : IsOpen (thickening δ' (closedBall 0 1 ×ˢ {0}) ∩ ball
      (0 : (Fin (c.dim i) → ℝ) × (Fin (Module.finrank ℝ E - c.dim i) → ℝ)) 2) :=
    isOpen_thickening.inter isOpen_ball
  refine ⟨_, rfl, (isOpen_univ.prod hN₁).union (isOpen_iUnion fun i ↦
      (IsOpenMap.id.prodMap (c.isOpenEmbedding_chart i).isOpenMap) _
        ((hV i).inter (isOpen_univ.prod (hT i)))),
    fun p hp ↦ .inl ⟨mem_univ _, hp.2⟩,
    fun i p hp hz ↦ .inr (mem_iUnion.2 ⟨i, p, ⟨hp, mem_univ _, hz⟩, rfl⟩), ?_⟩
  rintro ⟨l, y⟩ hp hl r hr
  rcases hp with ⟨-, hy⟩ | hp
  · -- On `N₁`, `d (B' (s l)) = d (B (s l))`, so the segment is constantly `τ l`.
    have hd : (mextDerivₗ I 1 (B' (s l))).val y = (mextDerivₗ I 1 (B (s l))).val y := by
      rw [mextDerivₗ_apply, mextDerivₗ_apply]
      exact mextDeriv_congr_of_eventuallyEq
        (Filter.eventually_of_mem (hN₁.mem_nhds hy) fun x hx ↦ hB'N₁ _ x hx)
    have heq : (α l + mextDerivₗ I 1 (B' (s l))).val y = (τ l).val y := by
      rw [hτN l y (hN₁N hy)]
      simp only [SmoothBundleForm.add_apply, hd]
    exact SmoothTwoForm.bilinFormAt_add_smul_sub_of_eq heq r ▸
      (hnd l hl).nondegenerate_bilinFormAt y
  · obtain ⟨i, ⟨l, z⟩, ⟨hV', -, hz⟩, he⟩ := mem_iUnion.1 hp
    simp only [Prod.map_apply, id_eq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    -- The readings of `B q` and `B' q` in the chart, as functions on its domain.
    let ρ (B₀ : S → SmoothForm I M ℝ 1) (q : S) :
        (Fin (c.dim i) → ℝ) × (Fin (Module.finrank ℝ E - c.dim i) → ℝ) →
          ((Fin (c.dim i) → ℝ) × (Fin (Module.finrank ℝ E - c.dim i) → ℝ)) [⋀^Fin 1]→L[ℝ] ℝ :=
      mpullback 𝓘(ℝ, (Fin (c.dim i) → ℝ) × (Fin (Module.finrank ℝ E - c.dim i) → ℝ)) I
        (c.chart i) (B₀ q).val
    -- The reading of `d (B₀ q)` in the chart is the exterior derivative of the reading of `B₀ q`.
    have hd (B₀ : S → SmoothForm I M ℝ 1) (q : S) :
        (mpullback 𝓘(ℝ, (Fin (c.dim i) → ℝ) × (Fin (Module.finrank ℝ E - c.dim i) → ℝ)) I
          (c.chart i) (mextDerivₗ I 1 (B₀ q)).val z :
          ((Fin (c.dim i) → ℝ) × (Fin (Module.finrank ℝ E - c.dim i) → ℝ)) [⋀^Fin 2]→L[ℝ] ℝ) =
        extDeriv (ρ B₀ q) z := by
      have h := mpullback_symm_mextDerivₗ (c.chartPartialDiffeomorph i) (B₀ q) (y := z) (by simp)
      rwa [chartPartialDiffeomorph_symm_apply] at h
    -- Near `z`, the reading of `B' (s l)` is that of `B (s l)` plus the correction.
    have hev : ρ B' (s l) =ᶠ[𝓝 z] ρ B (s l) + fun w ↦ corr i (s l, w) :=
      Filter.eventually_of_mem (isOpen_thickening.mem_nhds hz.1) fun w hw ↦ by
        rw [Pi.add_apply, ← hB' i (s l) w hw]
        exact (add_sub_cancel _ _).symm
    have hdiff : DifferentiableAt ℝ (ρ B (s l)) z := by
      have h := SmoothForm.differentiableAt_mpullback_symm (B (s l)) (c.chartPartialDiffeomorph i)
        (y := z) (by simp)
      rwa [chartPartialDiffeomorph_symm_apply] at h
    have hdiffc : DifferentiableAt ℝ (fun w ↦ corr i (s l, w)) z :=
      ((hcorr i).comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp) z
    have hform : τ l + r • (α l + mextDerivₗ I 1 (B' (s l)) - τ l) =
        τ l + r • (α l + mextDerivₗ I 1 (B (s l)) - τ l) +
          r • (mextDerivₗ I 1 (B' (s l)) - mextDerivₗ I 1 (B (s l))) := by
      module
    -- The readings at `z` of two-forms on `M`.
    let θ (φ : SmoothForm I M ℝ 2) :
        ((Fin (c.dim i) → ℝ) × (Fin (Module.finrank ℝ E - c.dim i) → ℝ)) [⋀^Fin 2]→L[ℝ] ℝ :=
      mpullback 𝓘(ℝ, (Fin (c.dim i) → ℝ) × (Fin (Module.finrank ℝ E - c.dim i) → ℝ)) I
        (c.chart i) φ.val z
    have hkey : θ (τ l + r • (α l + mextDerivₗ I 1 (B' (s l)) - τ l)) =
        θ (τ l + r • (α l + mextDerivₗ I 1 (B (s l)) - τ l)) +
          r • extDeriv (fun w ↦ corr i (s l, w)) z := by
      rw [hform]
      simp only [θ, Submodule.coe_add, Submodule.coe_smul, Submodule.coe_sub, mpullback_add,
        mpullback_smul, mpullback_sub, Pi.add_apply, Pi.smul_apply, Pi.sub_apply]
      rw [hd, hd, hev.extDeriv_eq, extDeriv_add hdiff hdiffc]
      exact congrArg (_ + r • ·) (add_sub_cancel_left _ _)
    -- Along the chart, nondegeneracy at `c.chart i z` is that of the reading at `z`.
    have hbil (φ : SmoothForm I M ℝ 2) :
        (SmoothForm.mpullback (c.chart i) (c.isSmoothEmbedding_chart i).contMDiff φ).bilinFormAt z =
          MultilinearMap.toBilinMap (θ φ).toMultilinearMap :=
      -- `rfl` unfolds the local abbreviation `θ`.
      by rw [SmoothForm.bilinFormAt_def, SmoothForm.coe_mpullback]; rfl
    refine (SmoothTwoForm.nondegenerate_bilinFormAt_iff_of_isInvertible_mfderiv
      ((c.isLocalDiffeomorph_chart i z).isInvertible_mfderiv (by simp))
      (η := SmoothForm.mpullback (c.chart i) (c.isSmoothEmbedding_chart i).contMDiff _)
      (by rw [SmoothForm.coe_mpullback])).2 ?_
    rw [hbil, hkey]
    exact hVnd i (l, z) hV' hl hz r hr

open TauCeti in
/-- **Carrying the cube data of a band core back to the manifold.** Let `c` be a band core in a
Hausdorff manifold `M`, `N` an open set containing `{g ≤ a}`, `S` a normed space, `s : Λ → S`,
`K P₀ ⊆ Λ`, `τ α : Λ → SmoothTwoForm I M` with `τ l` nondegenerate for `l ∈ K`, and `B` a smooth
family over `S` of one-forms on `M` with `τ l = α l + d (B (s l))` on `N`. Let `Q` be the unit
cube `closedBall 0 1 ×ˢ {0}` in the domain `D i` of `c.chart i`, and let `0 < δ ≤ δ' ≤ 1 / 2`
with the images under the charts of the closed `δ'`-thickenings of `Q` pairwise disjoint
(`BandCore.exists_pairwise_disjoint_image_cthickening`). For each cube `i` let

* `h i` be a diffeotopy of `S × D i` that keeps the parameter and moves points by less than `δ`,
  and `corr i : S × D i → D i [⋀^Fin 1]→L[ℝ] ℝ` be smooth;
* `C i ⊆ S × D i` be compact, with its points over the open `δ`-thickening of `Q`, such that off
  `C i` the diffeotopy `h i` is the identity and `corr i` vanishes;
* `R i` be a set of core coordinates such that the chart sends each point `z` of the open
  `δ`-thickening of `Q` with `z.1 ∉ R i` above `a` (item 3 of `exists_relativeSet`), and `N' i`
  a neighbourhood of `R i` over which `h i` is the identity and `corr i` vanishes;
* over `s l`, for `l ∈ P₀`, `h i` be the identity and `corr i` vanish;
* `V i ⊆ Λ × D i` be open, containing `(l, (h i (1, (s l, y))).2)` for `l ∈ K` and `y ∈ Q`, such
  that at its points `(l, z)` with `l ∈ K` and `z` in `ball 0 2` and in the open
  `δ'`-thickening of `Q`, for every `r ∈ [0, 1]`, the reading at `z` of
  `τ l + r • (α l + d (B (s l)) - τ l)` plus `r • d (corr i (s l, ·)) z` is nondegenerate.

Then there are a smooth `Φ : (S × [0, 1]) × M → M`, a smooth family `B'` over `S` of one-forms on
`M`, an open `N₁ ⊆ M` and an open `U ⊆ Λ × M` such that

* each slice `x ↦ Φ (p, x)` is a diffeomorphism of `M`, so a local diffeomorphism, and
  `Φ ((q, 0), x) = x`;
* `{g ≤ a} ⊆ N₁ ⊆ N`, and on `N₁` every slice of `Φ` is the identity and `B' q = B q`;
* for `l ∈ P₀`, `Φ ((s l, t), x) = x` and `B' (s l) = B (s l)`;
* `K ×ˢ N₁ ⊆ U`, `(l, Φ ((s l, 1), y)) ∈ U` for `l ∈ K` and `y` in the cubes of `c`, and at each
  `(l, y) ∈ U` with `l ∈ K` every `τ l + r • (α l + d (B' (s l)) - τ l)`, `r ∈ [0, 1]`, is
  nondegenerate at `y`.

These are the hypotheses of `exists_stagePath` on `Φ`, `B'`, `N₁` and `U`. -/
theorem exists_stageData_of_cubes (c : BandCore I g a₀ a b) {N : Set M} (hN : IsOpen N)
    (haN : {x | g x ≤ a} ⊆ N) {Λ S : Type*} [TopologicalSpace Λ] [NormedAddCommGroup S]
    [NormedSpace ℝ S] {K P₀ : Set Λ} {s : Λ → S} {τ α : Λ → SmoothTwoForm I M}
    (hnd : ∀ l ∈ K, (τ l).IsNondegenerate) {B : S → SmoothForm I M ℝ 1}
    (hB : IsSmoothFamily 𝓘(ℝ, S) B)
    (hτN : ∀ l, ∀ x ∈ N, (τ l).val x = (α l + mextDerivₗ I 1 (B (s l))).val x)
    {δ δ' : ℝ} (hδδ' : δ ≤ δ') (hδ'2 : δ' ≤ 1 / 2)
    (hδ' : Pairwise fun i j ↦
      Disjoint (c.chart i '' cthickening δ' (closedBall 0 1 ×ˢ {0}))
        (c.chart j '' cthickening δ' (closedBall 0 1 ×ˢ {0})))
    (h : ∀ i, TauCeti.Diffeotopy
      (𝓘(ℝ, S).prod 𝓘(ℝ, (Fin (c.dim i) → ℝ) × (Fin (Module.finrank ℝ E - c.dim i) → ℝ))) ∞
      (S × ((Fin (c.dim i) → ℝ) × (Fin (Module.finrank ℝ E - c.dim i) → ℝ))))
    (hfst : ∀ i t p, (h i (t, p)).1 = p.1) (hdist : ∀ i t p, dist (h i (t, p)) p < δ)
    {corr : ∀ i, S × ((Fin (c.dim i) → ℝ) × (Fin (Module.finrank ℝ E - c.dim i) → ℝ)) →
      ((Fin (c.dim i) → ℝ) × (Fin (Module.finrank ℝ E - c.dim i) → ℝ)) [⋀^Fin 1]→L[ℝ] ℝ}
    (hcorr : ∀ i, ContDiff ℝ ∞ (corr i))
    {C : ∀ i, Set (S × (Fin (c.dim i) → ℝ) × (Fin (Module.finrank ℝ E - c.dim i) → ℝ))}
    (hC : ∀ i, IsCompact (C i))
    (hCδ : ∀ i, ∀ p ∈ C i, p.2 ∈ thickening δ (closedBall 0 1 ×ˢ {0}))
    (hCfix : ∀ i, ∀ p ∉ C i, (∀ t, h i (t, p) = p) ∧ corr i p = 0)
    {R N' : ∀ i, Set (Fin (c.dim i) → ℝ)}
    (hR : ∀ i, ∀ z ∈ thickening δ (closedBall 0 1 ×ˢ {0}), z.1 ∉ R i → a < g (c.chart i z))
    (hRN' : ∀ i, N' i ∈ 𝓝ˢ (R i))
    (hN'fix : ∀ i p, p.2.1 ∈ N' i → (∀ t, h i (t, p) = p) ∧ corr i p = 0)
    (hP₀fix : ∀ i, ∀ l ∈ P₀, ∀ z, (∀ t, h i (t, (s l, z)) = (s l, z)) ∧ corr i (s l, z) = 0)
    {V : ∀ i, Set (Λ × (Fin (c.dim i) → ℝ) × (Fin (Module.finrank ℝ E - c.dim i) → ℝ))}
    (hV : ∀ i, IsOpen (V i))
    (hQV : ∀ i, ∀ l ∈ K, ∀ y ∈ closedBall 0 1 ×ˢ {0}, (l, (h i (1, (s l, y))).2) ∈ V i)
    (hVnd : ∀ i, ∀ p ∈ V i, p.1 ∈ K →
      p.2 ∈ thickening δ' (closedBall 0 1 ×ˢ {0}) ∩ ball 0 2 → ∀ r ∈ Icc (0 : ℝ) 1,
      (MultilinearMap.toBilinMap (@HAdd.hAdd
        (((Fin (c.dim i) → ℝ) × (Fin (Module.finrank ℝ E - c.dim i) → ℝ)) [⋀^Fin 2]→L[ℝ] ℝ)
        (((Fin (c.dim i) → ℝ) × (Fin (Module.finrank ℝ E - c.dim i) → ℝ)) [⋀^Fin 2]→L[ℝ] ℝ) _ _
        (mpullback 𝓘(ℝ, (Fin (c.dim i) → ℝ) × (Fin (Module.finrank ℝ E - c.dim i) → ℝ)) I
          (c.chart i) (τ p.1 + r • (α p.1 + mextDerivₗ I 1 (B (s p.1)) - τ p.1)).val p.2)
        (r • extDeriv (fun z ↦ corr i (s p.1, z)) p.2)).toMultilinearMap).Nondegenerate) :
    ∃ (Φ : (S × unitInterval) × M → M) (B' : S → SmoothForm I M ℝ 1) (N₁ : Set M)
      (U : Set (Λ × M)),
      ContMDiff ((𝓘(ℝ, S).prod (𝓡∂ 1)).prod I) I ∞ Φ ∧
      (∀ p, ∃ f : M ≃ₘ⟮I, I⟯ M, ∀ x, f x = Φ (p, x)) ∧
      (∀ p, IsLocalDiffeomorph I I ∞ fun x ↦ Φ (p, x)) ∧ (∀ q x, Φ ((q, 0), x) = x) ∧
      IsSmoothFamily 𝓘(ℝ, S) B' ∧
      IsOpen N₁ ∧ {x | g x ≤ a} ⊆ N₁ ∧ N₁ ⊆ N ∧ (∀ p, ∀ x ∈ N₁, Φ (p, x) = x) ∧
      (∀ q, ∀ x ∈ N₁, (B' q).val x = (B q).val x) ∧
      (∀ l ∈ P₀, ∀ t x, Φ ((s l, t), x) = x) ∧ (∀ l ∈ P₀, B' (s l) = B (s l)) ∧
      IsOpen U ∧ K ×ˢ N₁ ⊆ U ∧ (∀ l ∈ K, ∀ y ∈ c.cubes, (l, Φ ((s l, 1), y)) ∈ U) ∧
      ∀ p ∈ U, p.1 ∈ K → ∀ r ∈ Icc (0 : ℝ) 1,
        ((τ p.1 + r • (α p.1 + mextDerivₗ I 1 (B' (s p.1)) - τ p.1)).bilinFormAt
          p.2).Nondegenerate := by
  -- Step 1: the space parts of the `C i` lie in the closed `δ'`-thickenings of the cubes.
  have hCsnd (i : c.ι) : IsCompact (Prod.snd '' C i) := (hC i).image continuous_snd
  have hCW (i : c.ι) : Prod.snd '' C i ⊆ cthickening δ' (closedBall 0 1 ×ˢ {0}) := by
    rintro _ ⟨p, hp, rfl⟩
    exact thickening_subset_cthickening _ _ (thickening_mono hδδ' _ (hCδ i p hp))
  have hnotC (i : c.ι) {q : S} {z} (hz : z ∉ Prod.snd '' C i) : (q, z) ∉ C i :=
    fun hqz ↦ hz (mem_image_of_mem Prod.snd hqz)
  -- Step 5: the diffeotopy and the corrected one-forms.
  obtain ⟨Φ, hΦ, hΦf, hΦd, hΦ₀, hΦW, hΦoff, hΦq⟩ := c.exists_diffeotopy_of_cubes h hfst hCsnd
    (fun i t p hp ↦ (hCfix i p (hnotC i (q := p.1) hp)).1 t) hCW hδ'
  obtain ⟨B', hB', hB'off, hB'W, hB'q⟩ := c.exists_oneForm_of_cubes hB hcorr hCsnd
    (fun i q z hz ↦ (hCfix i (q, z) (hnotC i hz)).2) hCW hδ'
  -- Step 6: the open set `N₁`, over which the cube data are trivial.
  obtain ⟨N₁, -, -, hN₁, haN₁, hN₁N, hN₁C⟩ :=
    c.exists_isOpen_compl_image_chart_notMem_interior hN haN hC hCδ hR hRN'
  have hfix (i : c.ι) (q : S) {z} (hz : c.chart i z ∈ N₁) :
      (∀ t, h i (t, (q, z)) = (q, z)) ∧ corr i (q, z) = 0 := by
    by_cases hqz : (q, z) ∈ C i
    · exact hN'fix i (q, z) (interior_subset (hN₁C i (q, z) hqz hz))
    · exact hCfix i (q, z) hqz
  have hΦN₁ (p : S × unitInterval) (x : M) (hx : x ∈ N₁) : Φ (p, x) = x := by
    by_cases hxC : x ∈ ⋃ i, c.chart i '' (Prod.snd '' C i)
    · obtain ⟨i, z, hz, rfl⟩ := mem_iUnion.1 hxC
      rw [hΦW i p.1 p.2 z (hCW i hz), (hfix i p.1 hx).1]
    · exact hΦoff p x hxC
  have hB'N₁ (q : S) (x : M) (hx : x ∈ N₁) : (B' q).val x = (B q).val x := by
    by_cases hxC : x ∈ ⋃ i, c.chart i '' (Prod.snd '' C i)
    · obtain ⟨i, z, hz, rfl⟩ := mem_iUnion.1 hxC
      -- The readings of `B' q` and `B q` at `z` agree, and the chart is a local diffeomorphism.
      refine (mpullback_apply_eq_mpullback_apply_iff
        ((c.isLocalDiffeomorph_chart i z).isInvertible_mfderiv (by simp)).surjective).1 ?_
      rw [← sub_eq_zero, hB'W i q z (hCW i hz), (hfix i q hx).2]
      -- The zeros are of forms on the tangent space at `z` and on the model space, equal by
      -- definition.
      rfl
    · exact hB'off q x hxC
  -- Step 7: the open set `U`.
  obtain ⟨U, -, hU, hKU, hVU, hUnd⟩ := c.exists_isOpen_nondegenerate_of_cubes hnd hτN hN₁ hN₁N
    hB'N₁ hcorr (fun i q z hz ↦ hB'W i q z (thickening_subset_cthickening _ _ hz)) hV hVnd
  refine ⟨Φ, B', N₁, U, hΦ, hΦf, hΦd, hΦ₀, hB', hN₁, haN₁, hN₁N, hΦN₁, hB'N₁,
    fun l hl t x ↦ hΦq (s l) (fun i t z ↦ (hP₀fix i l hl z).1 t) t x,
    fun l hl ↦ hB'q (s l) fun i z ↦ (hP₀fix i l hl z).2, hU, hKU, fun l hl y hy ↦ ?_, hUnd⟩
  -- The displaced cube points: `h i` moves points of the cube by less than `δ ≤ δ' ≤ 1 / 2`.
  obtain ⟨i, z, hz, rfl⟩ := c.mem_cubes_iff.1 hy
  rw [hΦW i (s l) 1 z (self_subset_cthickening _ hz)]
  have hd : dist (h i (1, (s l, z))).2 z < δ := by
    have h₁ := hdist i 1 (s l, z)
    rw [Prod.dist_eq] at h₁
    exact (le_max_right _ _).trans_lt h₁
  refine hVU i _ (hQV i l hl z hz) ⟨mem_thickening_iff.2 ⟨z, hz, hd.trans_le hδδ'⟩, ?_⟩
  have hz1 : ‖z‖ ≤ 1 := by
    rw [Prod.norm_def, (mem_singleton_iff.1 hz.2), norm_zero]
    exact max_le (mem_closedBall_zero_iff.1 hz.1) zero_le_one
  rw [mem_ball_zero_iff]
  have := norm_le_norm_add_norm_sub' (h i (1, (s l, z))).2 z
  rw [← dist_eq_norm] at this
  linarith

section Smooth

open TauCeti

variable {L : Type*} [NormedAddCommGroup L] [NormedSpace ℝ L] [FiniteDimensional ℝ L]

omit [T2Space M] [FiniteDimensional ℝ E] in
/-- Steps 2 to 4 of `BandCore.exists_approximation_family`, in the chart `φ` of one cube:
holonomic approximation of the formal datum read in the chart, made holonomic near the
parameters of `P₀` by a cutoff in the parameter, with the nondegeneracy margin of the reading
of `τ` over `K` and `closedBall 0 2`. -/
private theorem exists_approximation_family_of_chart {m k : ℕ} (hk : 0 < k)
    {φ : (Fin m → ℝ) × (Fin k → ℝ) → M} (hφ : ContMDiff 𝓘(ℝ, (Fin m → ℝ) × (Fin k → ℝ)) I ∞ φ)
    (hφd : IsLocalDiffeomorph 𝓘(ℝ, (Fin m → ℝ) × (Fin k → ℝ)) I ∞ φ)
    {K P₀ : Set L} (hK : IsCompact K) (hP₀ : IsClosed P₀)
    {τ α : L → SmoothTwoForm I M} (hτ : IsSmoothFamily 𝓘(ℝ, L) τ)
    (hα : IsSmoothFamily 𝓘(ℝ, L) α) (hnd : ∀ l ∈ K, (τ l).IsNondegenerate)
    {β : L → SmoothForm I M ℝ 1} (hβ : IsSmoothFamily 𝓘(ℝ, L) β)
    {N : Set M} (hN : IsOpen N)
    (hτN : ∀ l, ∀ x ∈ N, (τ l).val x = (α l + mextDerivₗ I 1 (β l)).val x)
    (hτP₀ : ∀ l ∈ P₀, τ l = α l + mextDerivₗ I 1 (β l))
    {R : Set (Fin m → ℝ)} (hR : IsClosed R) (hSR : sphere 0 1 ⊆ R)
    (hRN : R ×ˢ {0} ⊆ φ ⁻¹' N) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (h : Diffeotopy (𝓘(ℝ, L).prod 𝓘(ℝ, (Fin m → ℝ) × (Fin k → ℝ))) ∞
        (L × (Fin m → ℝ) × (Fin k → ℝ)))
      (corr : L × (Fin m → ℝ) × (Fin k → ℝ) → ((Fin m → ℝ) × (Fin k → ℝ)) [⋀^Fin 1]→L[ℝ] ℝ)
      (C : Set (L × (Fin m → ℝ) × (Fin k → ℝ))) (N' : Set (Fin m → ℝ))
      (V : Set (L × (Fin m → ℝ) × (Fin k → ℝ))),
      (∀ t p, (h (t, p)).1 = p.1) ∧ (∀ t p, dist (h (t, p)) p < δ) ∧ ContDiff ℝ ∞ corr ∧
      IsCompact C ∧
      (∀ p ∈ C, p.2 ∈ thickening δ (closedBall (0 : Fin m → ℝ) 1 ×ˢ {(0 : Fin k → ℝ)})) ∧
      (∀ p ∉ C, (∀ t, h (t, p) = p) ∧ corr p = 0) ∧ N' ∈ 𝓝ˢ R ∧
      (∀ p : L × (Fin m → ℝ) × (Fin k → ℝ), p.2.1 ∈ N' → (∀ t, h (t, p) = p) ∧ corr p = 0) ∧
      (∀ l ∈ P₀, ∀ z, (∀ t, h (t, (l, z)) = (l, z)) ∧ corr (l, z) = 0) ∧ IsOpen V ∧
      (∀ l ∈ K, ∀ y ∈ closedBall (0 : Fin m → ℝ) 1 ×ˢ {(0 : Fin k → ℝ)},
        (l, (h (1, (l, y))).2) ∈ V) ∧
      ∀ p ∈ V, p.1 ∈ K → p.2 ∈ ball 0 2 → ∀ r ∈ Icc (0 : ℝ) 1,
        (MultilinearMap.toBilinMap (@HAdd.hAdd
          (((Fin m → ℝ) × (Fin k → ℝ)) [⋀^Fin 2]→L[ℝ] ℝ)
          (((Fin m → ℝ) × (Fin k → ℝ)) [⋀^Fin 2]→L[ℝ] ℝ) _ _
          (mpullback 𝓘(ℝ, (Fin m → ℝ) × (Fin k → ℝ)) I φ
            (τ p.1 + r • (α p.1 + mextDerivₗ I 1 (β p.1) - τ p.1)).val p.2)
          (r • extDeriv (fun z ↦ corr (p.1, z)) p.2)).toMultilinearMap).Nondegenerate := by
  -- Step 2: the nondegeneracy margin `r₀` of the reading of `τ` over `K` and `closedBall 0 2`.
  have hτD := hτ.mpullback φ hφ
  have hndD (l : L) (hl : l ∈ K) (x : (Fin m → ℝ) × (Fin k → ℝ)) (_ : x ∈ closedBall 0 2) :
      ((SmoothForm.mpullback φ hφ (τ l)).bilinFormAt x).Nondegenerate :=
    (SmoothTwoForm.nondegenerate_bilinFormAt_iff_of_isInvertible_mfderiv
      ((hφd x).isInvertible_mfderiv (by simp)) (η := SmoothForm.mpullback φ hφ (τ l))
      (by rw [SmoothForm.coe_mpullback])).1 ((hnd l hl).nondegenerate_bilinFormAt (φ x))
  obtain ⟨r₀, hr₀, hmargin⟩ :=
    hτD.exists_pos_forall_nondegenerate_sub_smul hK (isCompact_closedBall 0 2) hndD
  have hε₁ : 0 < r₀ / 5 := by positivity
  -- The formal datum of the cube: the reading `f` of `β` and the formal primitive `G`.
  set f : L × (Fin m → ℝ) × (Fin k → ℝ) → ((Fin m → ℝ) × (Fin k → ℝ)) [⋀^Fin 1]→L[ℝ] ℝ :=
    fun p ↦ (SmoothForm.mpullback φ hφ (β p.1)).val p.2
  set G : L × (Fin m → ℝ) × (Fin k → ℝ) →
      (Fin m → ℝ) × (Fin k → ℝ) →L[ℝ] ((Fin m → ℝ) × (Fin k → ℝ)) [⋀^Fin 1]→L[ℝ] ℝ :=
    fun p ↦ formalPrimitive (SmoothForm.mpullback φ hφ (τ p.1 - α p.1)).val
      (SmoothForm.mpullback φ hφ (β p.1)).val p.2
  have hf : ContDiff ℝ ∞ f := (hβ.mpullback φ hφ).contDiff_val
  have hG : ContDiff ℝ ∞ G :=
    contDiff_formalPrimitive ((hτ.sub hα).mpullback φ hφ) (hβ.mpullback φ hφ)
  have hhol (p : L × (Fin m → ℝ) × (Fin k → ℝ))
      (hp : (τ p.1).val (φ p.2) = (α p.1 + mextDerivₗ I 1 (β p.1)).val (φ p.2)) :
      fderiv ℝ (fun x ↦ f (p.1, x)) p.2 = G p :=
    (formalPrimitive_mpullback_eq_fderiv hφ hp).symm
  -- Step 3: a cutoff in the parameter makes the datum holonomic over an open set containing
  -- `P₀`, changing it by less than `r₀ / 5` over `closedBall 0 2`.
  obtain ⟨G', hG', ⟨O, hO, hP₀O, hOf⟩, hGG', hG'T⟩ :=
    exists_contDiff_fderiv_eq_of_fderiv_eq_on_param hf hG (by simp) le_rfl hP₀
      (fun l hl x ↦ hhol (l, x) (by rw [hτP₀ l hl])) (isCompact_closedBall 0 2) hε₁
  set U : Set (L × (Fin m → ℝ) × (Fin k → ℝ)) := univ ×ˢ (φ ⁻¹' N) ∪ O ×ˢ univ
  have hU : IsOpen U := (isOpen_univ.prod (hN.preimage hφ.continuous)).union (hO.prod isOpen_univ)
  have hUf (p) (hp : p ∈ U) : fderiv ℝ (fun x ↦ f (p.1, x)) p.2 = G' p := by
    rcases hp with ⟨-, hp⟩ | ⟨hp, -⟩
    · rw [hGG' p (hhol p (hτN p.1 _ hp))]
      exact hhol p (hτN p.1 _ hp)
    · exact hOf p hp
  -- Step 4: holonomic approximation with accuracy `r₀ / 5` and width `δ`.
  obtain ⟨h, f', V, hfst, hf', ⟨C, hC, hCQ, hCfix⟩, hdist, ⟨N', hN', hN'fix⟩, hP₀fix, hV, hQV,
      happrox⟩ :=
    exists_holonomic_approximation_family hk hf hG' hK hP₀ hR hSR hU
      (fun p hp ↦ .inl ⟨mem_univ _, hRN hp.2⟩) (fun p hp ↦ .inr ⟨hP₀O hp.1, mem_univ _⟩) hUf hε₁ hδ
  refine ⟨h.toProdModel, fun p ↦ f' p - f p, C, N', V, fun t p ↦ ?_, fun t p ↦ ?_, hf'.sub hf,
    hC, hCQ, fun p hp ↦ ?_, hN', fun p hp ↦ ?_, fun l hl z ↦ ?_, hV, fun l hl y hy ↦ ?_, ?_⟩
  · rw [Diffeotopy.toProdModel_apply]
    exact hfst t p
  · rw [Diffeotopy.toProdModel_apply]
    exact hdist t p
  · simp only [Diffeotopy.toProdModel_apply, (hCfix p hp).1, implies_true, true_and]
    exact sub_eq_zero.2 (hCfix p hp).2
  · simp only [Diffeotopy.toProdModel_apply, (hN'fix p hp).1, implies_true, true_and]
    exact sub_eq_zero.2 (hN'fix p hp).2
  · simp only [Diffeotopy.toProdModel_apply, (hP₀fix (l, z) hl).1, implies_true, true_and]
    exact sub_eq_zero.2 (hP₀fix (l, z) hl).2
  · rw [Diffeotopy.toProdModel_apply]
    convert hQV l hl y hy using 1
    exact Prod.ext (hfst 1 (l, y)).symm rfl
  -- The estimate and the nondegeneracy on `V`.
  rintro ⟨l, z⟩ hp hl hz r hr
  have hz2 : z ∈ closedBall 0 2 := ball_subset_closedBall hz
  have hf'l : ContDiff ℝ ∞ fun x ↦ f' (l, x) := hf'.comp (contDiff_const.prodMk contDiff_id)
  -- The approximation read as a one-form on the domain of the chart.
  set b' : SmoothForm 𝓘(ℝ, (Fin m → ℝ) × (Fin k → ℝ)) ((Fin m → ℝ) × (Fin k → ℝ)) ℝ 1 :=
    ⟨fun x ↦ f' (l, x), (isSmoothForm_modelSpace_iff.mpr hf'l).mem_smoothBundleForms⟩
  set η : SmoothTwoForm 𝓘(ℝ, (Fin m → ℝ) × (Fin k → ℝ)) ((Fin m → ℝ) × (Fin k → ℝ)) :=
    SmoothForm.mpullback φ hφ (τ l - α l) - mextDerivₗ 𝓘(ℝ, (Fin m → ℝ) × (Fin k → ℝ)) 1 b'
  have hb' : (mextDerivₗ 𝓘(ℝ, (Fin m → ℝ) × (Fin k → ℝ)) 1 b').val z =
      extDeriv (fun x ↦ f' (l, x)) z := by
    rw [mextDerivₗ_apply, mextDeriv_eq_extDeriv]
  -- The derivative of the approximation is within `2 * r₀ / 5` of the formal primitive.
  have h₁ : ‖fderiv ℝ (fun x ↦ f' (l, x)) z - G (l, z)‖ ≤ 2 * (r₀ / 5) := by
    have h₂ := (happrox (l, z) hp).2
    have h₃ := hG'T (l, z) hz2
    have h₄ := norm_sub_le_norm_sub_add_norm_sub (fderiv ℝ (fun x ↦ f' (l, x)) z) (G' (l, z))
      (G (l, z))
    linarith
  have hη : @norm (((Fin m → ℝ) × (Fin k → ℝ)) [⋀^Fin 2]→L[ℝ] ℝ) _ (η.val z) < r₀ := by
    have h₄ := norm_extDeriv_sub_le_of_norm_fderiv_sub_formalPrimitive_le h₁
    rw [SmoothBundleForm.sub_apply, hb']
    exact (norm_sub_rev _ _).trans_lt (h₄.trans_lt (by linarith))
  have hnd' := hmargin l hl z hz2 η hη r hr
  -- The reading of the segment plus the correction is `τ l - r • η`, as forms on the chart.
  set b : SmoothForm 𝓘(ℝ, (Fin m → ℝ) × (Fin k → ℝ)) ((Fin m → ℝ) × (Fin k → ℝ)) ℝ 1 :=
    SmoothForm.mpullback φ hφ (β l)
  have hform : SmoothForm.mpullback φ hφ (τ l + r • (α l + mextDerivₗ I 1 (β l) - τ l)) +
      r • mextDerivₗ 𝓘(ℝ, (Fin m → ℝ) × (Fin k → ℝ)) 1 (b' - b) =
      SmoothForm.mpullback φ hφ (τ l) - r • η := by
    simp only [η, b, map_add, map_sub, map_smul, SmoothForm.mextDerivₗ_mpullback]
    module
  have hcorr : extDeriv (fun x ↦ f' (l, x) - f (l, x)) z =
      (mextDerivₗ 𝓘(ℝ, (Fin m → ℝ) × (Fin k → ℝ)) 1 (b' - b)).val z := by
    rw [mextDerivₗ_apply, mextDeriv_eq_extDeriv]
    -- The values of `b' - b` are, by definition, those of `f' (l, ·) - f (l, ·)`.
    rfl
  rw [SmoothForm.bilinFormAt_def, ← hform, SmoothBundleForm.add_apply,
    SmoothBundleForm.smul_apply, SmoothForm.coe_mpullback, ← hcorr] at hnd'
  exact hnd'

/-- **Holonomic approximation over all cubes of a band core, for smooth families.** Let `c` be a
band core in a Hausdorff manifold `M` with `g` continuous, `L` a finite-dimensional normed space,
`K ⊆ L` compact and `P₀ ⊆ L` closed. Let `τ`, `α` be smooth families over `L` of two-forms on
`M`, with `τ l` nondegenerate for `l ∈ K`, and `β` a smooth family of one-forms, such that
`τ l = α l + d (β l)` on an open `N ⊇ {g ≤ a}` for every `l`, and on all of `M` for `l ∈ P₀`.
Then there are a smooth `Φ : (L × [0, 1]) × M → M`, a smooth family `B'` over `L` of one-forms
on `M`, an open `N₁ ⊆ M` and an open `U ⊆ L × M` such that

* each slice `x ↦ Φ (p, x)` is a diffeomorphism of `M`, so a local diffeomorphism, and
  `Φ ((l, 0), x) = x`;
* `{g ≤ a} ⊆ N₁ ⊆ N`, and on `N₁` every slice of `Φ` is the identity and `B' l = β l`;
* for `l ∈ P₀`, `Φ ((l, t), x) = x` and `B' l = β l`;
* `K ×ˢ N₁ ⊆ U`, `(l, Φ ((l, 1), y)) ∈ U` for `l ∈ K` and `y` in the cubes of `c`, and at each
  `(l, y) ∈ U` with `l ∈ K` every `τ l + r • (α l + d (B' l) - τ l)`, `r ∈ [0, 1]`, is
  nondegenerate at `y`.

These are the hypotheses of `exists_stagePath` on `Φ`, `B'`, `N₁` and `U`, with `Λ = S = L` and
`s = id`. -/
theorem exists_approximation_family (c : BandCore I g a₀ a b) (hg : Continuous g)
    {K P₀ : Set L} (hK : IsCompact K) (hP₀ : IsClosed P₀)
    {τ α : L → SmoothTwoForm I M} (hτ : IsSmoothFamily 𝓘(ℝ, L) τ)
    (hα : IsSmoothFamily 𝓘(ℝ, L) α) (hnd : ∀ l ∈ K, (τ l).IsNondegenerate)
    {β : L → SmoothForm I M ℝ 1} (hβ : IsSmoothFamily 𝓘(ℝ, L) β)
    {N : Set M} (hN : IsOpen N) (haN : {x | g x ≤ a} ⊆ N)
    (hτN : ∀ l, ∀ x ∈ N, (τ l).val x = (α l + mextDerivₗ I 1 (β l)).val x)
    (hτP₀ : ∀ l ∈ P₀, τ l = α l + mextDerivₗ I 1 (β l)) :
    ∃ (Φ : (L × unitInterval) × M → M) (B' : L → SmoothForm I M ℝ 1) (N₁ : Set M)
      (U : Set (L × M)),
      ContMDiff ((𝓘(ℝ, L).prod (𝓡∂ 1)).prod I) I ∞ Φ ∧
      (∀ p, ∃ f : M ≃ₘ⟮I, I⟯ M, ∀ x, f x = Φ (p, x)) ∧
      (∀ p, IsLocalDiffeomorph I I ∞ fun x ↦ Φ (p, x)) ∧ (∀ q x, Φ ((q, 0), x) = x) ∧
      IsSmoothFamily 𝓘(ℝ, L) B' ∧
      IsOpen N₁ ∧ {x | g x ≤ a} ⊆ N₁ ∧ N₁ ⊆ N ∧ (∀ p, ∀ x ∈ N₁, Φ (p, x) = x) ∧
      (∀ q, ∀ x ∈ N₁, (B' q).val x = (β q).val x) ∧
      (∀ l ∈ P₀, ∀ t x, Φ ((l, t), x) = x) ∧ (∀ l ∈ P₀, B' l = β l) ∧
      IsOpen U ∧ K ×ˢ N₁ ⊆ U ∧ (∀ l ∈ K, ∀ y ∈ c.cubes, (l, Φ ((l, 1), y)) ∈ U) ∧
      ∀ p ∈ U, p.1 ∈ K → ∀ r ∈ Icc (0 : ℝ) 1,
        ((τ p.1 + r • (α p.1 + mextDerivₗ I 1 (B' p.1) - τ p.1)).bilinFormAt
          p.2).Nondegenerate := by
  -- Step 1: the relative sets `R i` with their margins `η i`, the disjoint margin `δ'`, and
  -- `δ ≤ min (min_i η i / 2) δ'`.
  choose η hη _ R _ hRc hSR hRN hRa using fun i ↦ c.exists_relativeSet hg hN haN i
  obtain ⟨δ', hδ', hδ'2, hδ'd⟩ := c.exists_pairwise_disjoint_image_cthickening
  obtain ⟨δ, ⟨hδη, hδδ'⟩, hδ⟩ := ((Filter.eventually_all.2 fun i ↦
    (eventually_le_nhds (half_pos (hη i))).filter_mono nhdsWithin_le_nhds).and
    ((eventually_le_nhds hδ').filter_mono nhdsWithin_le_nhds)).and self_mem_nhdsWithin |>.exists
    (f := 𝓝[>] (0 : ℝ))
  -- Steps 2 to 4 in the chart of each cube.
  choose h corr C N' V hfst hdist hcorr hC hCδ hCfix hN' hN'fix hP₀fix hV hQV hVnd using
    fun i ↦ exists_approximation_family_of_chart (Nat.sub_pos_of_lt (c.dim_lt i))
      (c.isSmoothEmbedding_chart i).contMDiff (c.isLocalDiffeomorph_chart i) hK hP₀ hτ hα hnd hβ
      hN hτN hτP₀ (hRc i).isClosed (hSR i) (hRN i) hδ
  -- Steps 5 to 7.
  exact c.exists_stageData_of_cubes hN haN (s := id) hnd hβ hτN hδδ' hδ'2 hδ'd h hfst hdist hcorr
    hC hCδ hCfix (fun i z hz hzR ↦ (hRa i δ hδ (hδη i) z hz hzR).2) hN' hN'fix hP₀fix hV hQV
    fun i p hp hpK hpz ↦ hVnd i p hp hpK hpz.2

end Smooth

end BandCore

end SymplecticGeometry

end
