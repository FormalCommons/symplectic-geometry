/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Real
public import Mathlib.Geometry.Manifold.SmoothEmbedding
import SymplecticGeometry.Analysis.SpecialFunctions.SmoothTransition
import SymplecticGeometry.Geometry.Manifold.ContMDiff.TimeExtension
import SymplecticGeometry.Topology.Order.NhdsSet
import TauCeti.Geometry.Manifold.ContMDiffMap.Extension
import TauCeti.Geometry.Manifold.SmoothEmbedding.Euclidean
import TauCeti.Geometry.Manifold.TubularNeighborhood.Existence

/-!
# Time extension of isotopies past the ends of `[0, 1]`

These are the first two steps of isotopy extension at every time
(`TauCeti.SmoothIsotopy.exists_diffeotopy_forall_apply_eq`, in `SmoothIsotopy/Family.lean`, where
it is the case of a point as parameter manifold of the parametric statement). Tau Ceti's
`TauCeti.SmoothIsotopy.exists_diffeotopy_apply_eq` runs the motion at the time
`Real.smoothTransition t`, which is flat at both ends of `[0, 1]`; here the motion keeps its own
times on `[0, 1]`, and is first extended a little past both ends.

1. A smooth map on `unitInterval × X`, for a manifold `X` possibly with boundary, extends near a
   compact subset of `X` to a map smooth on `(-δ, 1 + δ) ×ˢ U`
   (`ContMDiff.exists_contMDiffOn_extend_unitInterval`). The target is embedded near the compact
   track into a Euclidean space (Tau Ceti's
   `IsCompact.exists_opens_nonempty_smoothEmbedding_euclidean`), the composite is extended in
   time by Seeley's extension (`SymplecticGeometry.timeExtend`), and a smooth retraction onto the
   image (Tau Ceti's `TauCeti.SmoothEmbedding.exists_contMDiffOn_retraction`) brings it back.
   `SmoothIsotopy/Family.lean` extends a family of isotopies this way; the graph of the extension
   keeps the parameter fixed, and its slices stay embeddings near the compact set for times near
   `[0, 1]` (`TauCeti.exists_pos_forall_isSmoothEmbedding_of_eventuallyEq`).
2. Run at the time `c t`, for a smooth `c : ℝ → (-δ, 1 + δ)` that is the identity on `[0, 1]`
   and constant outside `(-δ / 2, 1 + δ / 2)`
   (`SymplecticGeometry.exists_contDiff_eqOn_id_Icc_mem_Ioo`), such an extension is a motion
   over `ℝ` through embeddings, equal to the original one on `[0, 1]` and stationary outside a
   bounded interval (`TauCeti.exists_contMDiff_forall_isSmoothEmbedding_comp`).

Step 2 adapts the change of time in the proof of Tau Ceti's
`TauCeti.SmoothIsotopy.exists_diffeotopy_apply_eq` (through
`TauCeti.SmoothIsotopy.exists_diffeotopy_apply_eq_of_forall_notMem`), with the cut-off `c` in
place of `Real.smoothTransition`.

## Main results

* `TauCeti.exists_contMDiff_forall_isSmoothEmbedding_comp`: a motion through embeddings at times
  near `[0, 1]`, run at the time of a cut-off, is a motion over `ℝ` through embeddings that is
  stationary outside a bounded interval.
* `ContMDiff.exists_contMDiffOn_extend_unitInterval`: a smooth map on `unitInterval × X` extends
  near a compact subset of `X` to times in an open interval around `[0, 1]`.

## References

* M. W. Hirsch, *Differential Topology*, Graduate Texts in Mathematics 33, Springer (1976),
  Chapter 8, §1, Theorems 1.3 and 1.4.
* R. T. Seeley, *Extension of `C^∞` functions defined in a half space*, Proc. Amer. Math. Soc.
  15 (1964), 625–626.
-/

public section

noncomputable section

open Set Function Manifold
open scoped Manifold ContDiff Topology

namespace TauCeti

variable {E E' H H' P N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'}
  [TopologicalSpace P] [ChartedSpace H' P] [TopologicalSpace N] [ChartedSpace H N]
  [I.Boundaryless] [IsManifold I ∞ N] [T2Space N]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ N] [T2Space N] in
/-- **A motion over `ℝ` from a motion near `[0, 1]`.** Let `G : ℝ × P → N` be smooth on
`(-δ, 1 + δ) ×ˢ V`, with smooth embeddings of `V` as slices at times in `(-δ, 1 + δ)`. There is
a change of time `c : ℝ → ℝ` such that `(t, x) ↦ G (c t, x)` is a smooth motion of `V` over `ℝ`
through smooth embeddings, with `c t = t` for `t ∈ [0, 1]`, and `c` constant on `t ≤ -(δ / 2)`
and on `t ≥ 1 + δ / 2`. -/
theorem exists_contMDiff_forall_isSmoothEmbedding_comp {δ : ℝ} (hδ : 0 < δ)
    {V : TopologicalSpace.Opens P} {G : ℝ × P → N}
    (hG : ContMDiffOn (𝓘(ℝ).prod J) I ∞ G (Ioo (-δ) (1 + δ) ×ˢ (V : Set P)))
    (hemb : ∀ t ∈ Ioo (-δ) (1 + δ), IsSmoothEmbedding J I ∞ (fun x : V ↦ G (t, x))) :
    ∃ c : ℝ → ℝ, ContMDiff (𝓘(ℝ, ℝ).prod J) I ∞ (fun p : ℝ × V ↦ G (c p.1, p.2)) ∧
      (∀ t, IsSmoothEmbedding J I ∞ (fun x : V ↦ G (c t, x))) ∧ (∀ t ∈ Icc (0 : ℝ) 1, c t = t) ∧
      (∀ t ≤ -(δ / 2), c t = c (-(δ / 2))) ∧ ∀ t, 1 + δ / 2 ≤ t → c t = c (1 + δ / 2) := by
  obtain ⟨c, hc, hc_id, hc_mem, hc_out⟩ :=
    SymplecticGeometry.exists_contDiff_eqOn_id_Icc_mem_Ioo zero_le_one (half_pos hδ)
  have hc_mem' (t : ℝ) : c t ∈ Ioo (-δ) (1 + δ) :=
    ⟨by linarith [(hc_mem t).1], by linarith [(hc_mem t).2]⟩
  have hc_lo (t : ℝ) (ht : t ≤ -(δ / 2)) : c t = (0 + 1) / 2 :=
    hc_out t fun h ↦ by linarith [h.1]
  have hc_hi (t : ℝ) (ht : 1 + δ / 2 ≤ t) : c t = (0 + 1) / 2 :=
    hc_out t fun h ↦ by linarith [h.2]
  exact ⟨c, hG.comp_contMDiff ((hc.contMDiff.comp contMDiff_fst).prodMk
      (contMDiff_subtypeVal.comp contMDiff_snd)) fun q ↦ ⟨hc_mem' q.1, q.2.property⟩,
    fun t ↦ hemb (c t) (hc_mem' t), fun t ht ↦ hc_id ht,
    fun t ht ↦ (hc_lo t ht).trans (hc_lo _ le_rfl).symm,
    fun t ht ↦ (hc_hi t ht).trans (hc_hi _ le_rfl).symm⟩

/-- **Extension of a map past both ends of `[0, 1]` near a compact set.** A smooth map
`f : unitInterval × X → N`, from the product of the interval with any manifold `X`, possibly with
boundary, into a finite-dimensional, Hausdorff boundaryless manifold `N`, extends near a compact
`L ⊆ X` past both ends of `[0, 1]`: there are `δ > 0`, an open `U ⊇ L` and a map `G` on `ℝ × X`,
smooth on `(-δ, 1 + δ) ×ˢ U`, with `G (t, x) = f (t, x)` for `t ∈ [0, 1]` and `x ∈ U`. -/
theorem _root_.ContMDiff.exists_contMDiffOn_extend_unitInterval {EX HX X : Type*}
    [NormedAddCommGroup EX] [NormedSpace ℝ EX] [TopologicalSpace HX]
    {IX : ModelWithCorners ℝ EX HX} [TopologicalSpace X] [ChartedSpace HX X] [IsManifold IX ∞ X]
    {f : unitInterval × X → N} (hf : ContMDiff ((𝓡∂ 1).prod IX) I ∞ f) {L : Set X}
    (hL : IsCompact L) :
    ∃ δ > 0, ∃ U : Set X, IsOpen U ∧ L ⊆ U ∧ ∃ G : ℝ × X → N,
      ContMDiffOn (𝓘(ℝ, ℝ).prod IX) I ∞ G (Ioo (-δ) (1 + δ) ×ˢ U) ∧
      ∀ t : unitInterval, ∀ x ∈ U, G (t, x) = f (t, x) := by
  rcases L.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · exact ⟨1, one_pos, ∅, isOpen_empty, subset_rfl, fun p ↦ f (0, p.2),
      (hf.comp (contMDiff_const.prodMk contMDiff_snd)).contMDiffOn, fun _ _ hx ↦ hx.elim⟩
  -- A neighbourhood `W` of the compact track `T` of `L` embeds into a Euclidean space by `e`,
  -- and `r` retracts a neighbourhood `O` of the image of `e`.
  have hT : IsCompact (f '' (univ ×ˢ L)) := (isCompact_univ.prod hL).image hf.continuous
  obtain ⟨W, hTW, -, n, ⟨e⟩⟩ := hT.exists_opens_nonempty_smoothEmbedding_euclidean (I := I)
  have : Nonempty W := ⟨⟨f (0, x₀), hTW ⟨(0, x₀), ⟨mem_univ _, hx₀⟩, rfl⟩⟩⟩
  obtain ⟨O, hO, heO, -, r, hr, hre⟩ := e.exists_contMDiffOn_retraction isOpen_univ (subset_univ _)
  -- `g` is `e` on `W`, extended by `0`.
  let g : N → EuclideanSpace ℝ (Fin n) := extend Subtype.val e 0
  have hgW (y : W) : g y = e y := Subtype.val_injective.extend_apply _ _ y
  have hg : ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ g W :=
    ContMDiffMap.contMDiffOn_extend W ⟨e, e.contMDiff⟩ 0
  -- The tube lemma gives an open `U ⊇ L` whose image stays in `W` at all times.
  obtain ⟨u, U, -, hU, hu, hLU, hUW⟩ := generalized_tube_lemma isCompact_univ hL
    (W.isOpen.preimage hf.continuous) (fun p hp ↦ hTW ⟨p, hp, rfl⟩)
  have hUW' : univ ×ˢ U ⊆ f ⁻¹' W := (prod_mono hu subset_rfl).trans hUW
  -- Seeley's extension in time of `g ∘ f`, smooth although `X` may have boundary.
  let k : ℝ × X → EuclideanSpace ℝ (Fin n) := SymplecticGeometry.timeExtend fun p ↦ g (f p)
  have hk : ContMDiffOn (𝓘(ℝ, ℝ).prod IX) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ k (univ ×ˢ U) :=
    (hg.comp hf.contMDiffOn hUW').timeExtend hU
  have hkf (t : unitInterval) (x : X) (hx : x ∈ U) : k (t, x) = e ⟨f (t, x), hUW' ⟨trivial, hx⟩⟩ :=
    (SymplecticGeometry.timeExtend_apply_coe _ t x).trans (hgW ⟨_, hUW' ⟨trivial, hx⟩⟩)
  -- `r ∘ k` is smooth on the open set `S` where `k` lands in `O`, which contains `[0, 1] ×ˢ U`.
  let S : Set (ℝ × X) := univ ×ˢ U ∩ k ⁻¹' O
  have hS : IsOpen S := hk.continuousOn.isOpen_inter_preimage (isOpen_univ.prod hU) hO
  have hkO (t : unitInterval) (x : X) (hx : x ∈ U) : ((t : ℝ), x) ∈ S :=
    ⟨⟨trivial, hx⟩, by rw [mem_preimage, hkf t x hx]; exact heO (mem_range_self _)⟩
  -- A neighbourhood `(-δ, 1 + δ) ×ˢ V` of `[0, 1] ×ˢ L` inside `S`.
  obtain ⟨u', V, hu', hV, hIu', hLV, hVS⟩ := generalized_tube_lemma isCompact_Icc hL hS
    (fun p hp ↦ hkO ⟨p.1, hp.1⟩ p.2 (hLU hp.2))
  obtain ⟨δ, hδ, hIoo⟩ := hu'.exists_pos_Ioo_subset_of_Icc_subset hIu'
  rw [zero_sub] at hIoo
  have hVU (x : X) (hx : x ∈ V) : x ∈ U :=
    (hVS (mk_mem_prod (a := (0 : ℝ)) (hIoo ⟨by linarith, by linarith⟩) hx)).1.2
  refine ⟨δ, hδ, V, hV, hLV, fun p ↦ r (k p), ?_,
    fun t x hx ↦ by simp only [hkf t x (hVU x hx), hre]⟩
  exact (contMDiff_subtypeVal.comp_contMDiffOn
    (hr.comp (hk.mono inter_subset_left) fun _ hp ↦ hp.2)).mono
    ((prod_mono hIoo subset_rfl).trans hVS)

end TauCeti

end
