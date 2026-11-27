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
import SymplecticGeometry.Geometry.Diffeomorphism.Diffeotopy.Extend
import SymplecticGeometry.Geometry.Diffeomorphism.Diffeotopy.Support
import SymplecticGeometry.Geometry.Manifold.Diffeomorph.Prod.Basic
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Smooth
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.SmoothFamily.PartialDiffeomorph
import SymplecticGeometry.Geometry.Symplectic.HPrinciple.Relative.CubeCoordinates
import SymplecticGeometry.Topology.MetricSpace.Thickening
import TauCeti.Topology.Algebra.Support

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
* A correction `corr i` of one-forms on `D i`, depending smoothly on `q ∈ S`, for each cube,
  vanishing off a compact `C i`, gives one smooth family of one-forms on `M`
  (`BandCore.exists_oneForm_of_cubes`): to a smooth family `B` it adds, for each cube, the
  extension by zero of `corr i (q, ·)` along the inverse of
  the chart (`TauCeti.SmoothForm.extendByZeroAlong`, `BandCore.chartPartialDiffeomorph`). It is
  smooth by `SymplecticGeometry.IsSmoothFamily.extendByZeroAlong`. When the `C i` lie in sets
  `W i` with pairwise disjoint images, the other corrections vanish on `c.chart i '' W i`, so
  there the reading of the new family in the chart of cube `i` is that of `B` plus `corr i`
  (`TauCeti.mpullback_symm_extendByZeroAlong`).

## Main declarations

* `SymplecticGeometry.BandCore.exists_pairwise_disjoint_image_cthickening`: a margin `δ'` with
  `0 < δ' ≤ 1 / 2` such that the images under the charts of the closed `δ'`-thickenings of the
  unit cubes are pairwise disjoint.
* `SymplecticGeometry.BandCore.exists_diffeotopy_of_cubes`: the smooth family of diffeotopies of
  `M`, over `S × [0, 1]`, obtained from one diffeotopy of `S × D i` per cube.
* `SymplecticGeometry.BandCore.exists_oneForm_of_cubes`: the smooth family of one-forms on `M`
  obtained from a smooth family `B` and one correction on `S × D i` per cube.

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

end BandCore

end SymplecticGeometry

end
