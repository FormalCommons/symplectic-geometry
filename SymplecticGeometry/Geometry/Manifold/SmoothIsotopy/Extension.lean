/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Basic
public import TauCeti.Geometry.Manifold.SmoothIsotopy.Basic
import Mathlib.Geometry.Manifold.Algebra.Monoid
import SymplecticGeometry.Analysis.SpecialFunctions.SmoothTransition
import SymplecticGeometry.Geometry.Diffeomorphism.Diffeotopy.Basic
import SymplecticGeometry.Geometry.Diffeomorphism.Diffeotopy.Real
import SymplecticGeometry.Geometry.Manifold.ContMDiff.TimeExtension
import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.Neighborhood
import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Flow
import TauCeti.Geometry.Manifold.ContMDiffMap.Extension
import TauCeti.Geometry.Manifold.Immersion.LocalDiffeomorph
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Injective
import TauCeti.Geometry.Manifold.MFDeriv.Basic
import TauCeti.Geometry.Manifold.PartitionOfUnity.Compact
import TauCeti.Geometry.Manifold.SmoothEmbedding.Euclidean
import TauCeti.Geometry.Manifold.SmoothIsotopy.Velocity.Basic
import TauCeti.Geometry.Manifold.TubularNeighborhood.Existence

/-!
# Isotopy extension at every time

Let `F` be a smooth isotopy from `f₀` to `f₁`, a smooth motion of a boundaryless manifold `P`
through smooth embeddings into a finite-dimensional, Hausdorff, σ-compact boundaryless manifold
`N`. On a compact `A ⊆ P` the motion is the restriction of a compactly
supported diffeotopy `Φ` of `N` at every time: `Φ (t, f₀ x) = F (t, x)` for all `t` and all
`x ∈ A` (`TauCeti.SmoothIsotopy.exists_diffeotopy_forall_apply_eq`). Tau Ceti's
`TauCeti.SmoothIsotopy.exists_diffeotopy_apply_eq` gives this only for the motion run at the time
`Real.smoothTransition t`, which is flat at both ends, so the original times cannot be read off
from it.

The proof has three steps.

1. The motion extends past both ends of `[0, 1]` near `A`
   (`TauCeti.SmoothIsotopy.exists_contMDiff_extend`): there are `δ > 0`, an open `V ⊇ A` and a
   map `G` on `ℝ × P`, smooth on `(-δ, 1 + δ) ×ˢ V`, equal to `F` on `[0, 1] ×ˢ V`, whose slices
   at times in `(-δ, 1 + δ)` are smooth embeddings of `V`. A neighbourhood of the compact track
   of `A` embeds into a Euclidean space (Tau Ceti's
   `IsCompact.exists_opens_nonempty_smoothEmbedding_euclidean`, built on the map of Mathlib's
   `SmoothBumpCovering.embeddingPiTangent`), and the image has a smooth retraction on a
   neighbourhood (`TauCeti.SmoothEmbedding.exists_contMDiffOn_retraction`). Seeley's extension in
   time of the composite with the embedding (`SymplecticGeometry.timeExtend`), followed by the
   retraction, is the extension. Its slices are embeddings near `A` for times near `[0, 1]`
   (`TauCeti.exists_pos_forall_isSmoothEmbedding_of_injOn`).
2. Composed with a smooth `c : ℝ → (-δ, 1 + δ)` that is the identity on `[0, 1]` and constant
   outside `(-δ / 2, 1 + δ / 2)` (*Smooth families*'
   `SymplecticGeometry.exists_contDiff_eqOn_id_Icc_mem_Ioo`), the extension becomes a
   motion over `ℝ` through embeddings, stationary outside a bounded interval and equal to `F` on
   `[0, 1]`.
3. Tau Ceti's `TauCeti.exists_ambientVelocityField` extends its velocity to a compactly
   supported field on `N`, whose time-dependent flow from time `0`
   (`TauCeti.timeDependentFlowDiffeotopy`) is `Φ`. Uniqueness of solutions
   (`TauCeti.timeDependentFlowOf_eq_of_hasMFDerivAt`) gives `Φ (t, f₀ x) = F (t, x)`.

The flow is defined at all real times, so the proof also gives `Φ` as the restriction of a jointly
smooth family of diffeomorphisms `ψ_t` over `ℝ`
(`TauCeti.SmoothIsotopy.exists_contMDiff_diffeomorph_forall_apply_eq`), for arguments that
differentiate in time near the ends of `[0, 1]`.

Steps 2 and 3 adapt the proof of Tau Ceti's `TauCeti.SmoothIsotopy.exists_diffeotopy_apply_eq`
(through `TauCeti.SmoothIsotopy.exists_diffeotopy_apply_eq_of_forall_notMem`), with the cut-off
`c` in place of `Real.smoothTransition`.

## Main results

* `TauCeti.SmoothIsotopy.exists_contMDiff_extend`: a smooth isotopy extends near a compact set to
  times in an open interval around `[0, 1]`, with embedding slices.
* `TauCeti.SmoothIsotopy.exists_contMDiff_diffeomorph_forall_apply_eq`: isotopy extension at every
  time, by a jointly smooth family of diffeomorphisms over `ℝ`.
* `TauCeti.SmoothIsotopy.exists_diffeotopy_forall_apply_eq`: isotopy extension at every time.
* `TauCeti.SmoothIsotopy.exists_contMDiff_comp_eventuallyEq`: for an isotopy between manifolds of
  the same dimension, a smooth family of functions on the source is, near a compact set, the
  composite with the slices of the isotopy of a smooth family of functions on the target that
  vanishes off a compact set. It is `(χ · h_t ∘ f₀⁻¹) ∘ Φ_t⁻¹`, with `Φ` the diffeotopy of isotopy
  extension at every time and `χ` a cutoff; `f₀⁻¹` is smooth on the image of `f₀` because
  `f₀` is an injective local diffeomorphism (Tau Ceti's `IsImmersion.isLocalDiffeomorph` and
  `IsLocalDiffeomorphOn.contMDiffOn_invFunOn`).
* `ContMDiff.exists_diffeotopy_forall_apply_eq`: a smooth path is the track of its starting point
  under a compactly supported diffeotopy. The path is a smooth isotopy of a point, the
  zero-dimensional space `EuclideanSpace ℝ (Fin 0)`; that its slices are smooth embeddings is
  shown as in Tau Ceti's `Topology.IsEmbedding.isSmoothEmbedding_of_subsingleton`, which treats a
  target that is a normed space.

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
  [I.Boundaryless] [J.Boundaryless] [IsManifold J ∞ P] [IsManifold I ∞ N] [T2Space N]

namespace SmoothIsotopy

/-- **Time extension of an isotopy near a compact set.** A smooth isotopy `F` of a boundaryless
manifold into a finite-dimensional, Hausdorff boundaryless manifold extends near a compact
set `A` past both ends of `[0, 1]`: there are `δ > 0`, an open `V ⊇ A` and a map `G`, smooth on
`(-δ, 1 + δ) ×ˢ V`, with `G (t, x) = F (t, x)` for `t ∈ [0, 1]` and `x ∈ V`, whose slices at
times in `(-δ, 1 + δ)` are smooth embeddings of `V`. -/
theorem exists_contMDiff_extend {f₀ f₁ : C^∞⟮J, P; I, N⟯} (F : SmoothIsotopy f₀ f₁)
    {A : Set P} (hA : IsCompact A) :
    ∃ δ > 0, ∃ V : TopologicalSpace.Opens P, A ⊆ V ∧ ∃ G : ℝ × P → N,
      ContMDiffOn (𝓘(ℝ).prod J) I ∞ G (Ioo (-δ) (1 + δ) ×ˢ (V : Set P)) ∧
      (∀ t : unitInterval, ∀ x ∈ V, G (t, x) = F (t, x)) ∧
      ∀ t ∈ Ioo (-δ) (1 + δ), IsSmoothEmbedding J I ∞ (fun x : V ↦ G (t, x)) := by
  have : T2Space P := F.isSmoothEmbedding_left.isEmbedding.t2Space
  rcases A.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · -- For `A = ∅`, the empty open set and the constant motion `f₀` will do.
    refine ⟨1, one_pos, ⊥, empty_subset _, fun p ↦ f₀ p.2,
      (f₀.contMDiff.comp contMDiff_snd).contMDiffOn, fun _ x hx ↦ hx.elim, fun _ _ ↦ ?_⟩
    exact F.isSmoothEmbedding_left.comp_subtypeVal ⊥
  -- The source model is finite-dimensional, since `f₀` is an immersion into `N`.
  have : FiniteDimensional ℝ E' := finiteDimensional_of_injective_mfderiv
    (F.isSmoothEmbedding_left.isImmersion.mfderiv_injective (by simp) x₀)
  -- A neighbourhood `W` of the compact track `T` of `A` embeds into a Euclidean space by `e`,
  -- and `r` retracts a neighbourhood `O` of the image of `e`.
  have hT : IsCompact ((fun p : unitInterval × P ↦ F p) '' (univ ×ˢ A)) :=
    (isCompact_univ.prod hA).image F.contMDiff.continuous
  obtain ⟨W, hTW, -, n, ⟨e⟩⟩ := hT.exists_opens_nonempty_smoothEmbedding_euclidean (I := I)
  have : Nonempty W := ⟨⟨F (0, x₀), hTW ⟨(0, x₀), ⟨mem_univ _, hx₀⟩, rfl⟩⟩⟩
  obtain ⟨O, hO, heO, -, r, hr, hre⟩ := e.exists_contMDiffOn_retraction isOpen_univ (subset_univ _)
  -- `g` is `e` on `W`, extended by `0`.
  let g : N → EuclideanSpace ℝ (Fin n) := extend Subtype.val e 0
  have hgW (y : W) : g y = e y := Subtype.val_injective.extend_apply _ _ y
  have hg : ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ g W :=
    ContMDiffMap.contMDiffOn_extend W ⟨e, e.contMDiff⟩ 0
  -- The tube lemma gives an open `U ⊇ A` whose motion stays in `W`.
  obtain ⟨u, U, -, hU, hu, hAU, hUW⟩ := generalized_tube_lemma isCompact_univ hA
    (W.isOpen.preimage F.contMDiff.continuous) (fun p hp ↦ hTW ⟨p, hp, rfl⟩)
  have hUW' : univ ×ˢ U ⊆ (fun p : unitInterval × P ↦ F p) ⁻¹' W :=
    (prod_mono hu subset_rfl).trans hUW
  -- Seeley's extension in time of `g ∘ F`.
  let k : ℝ × P → EuclideanSpace ℝ (Fin n) := SymplecticGeometry.timeExtend fun p ↦ g (F p)
  have hk : ContMDiffOn (𝓘(ℝ, ℝ).prod J) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ k (univ ×ˢ U) :=
    (hg.comp F.contMDiff.contMDiffOn hUW').timeExtend hU
  have hkF (t : unitInterval) (x : P) (hx : x ∈ U) : k (t, x) = e ⟨F (t, x), hUW' ⟨trivial, hx⟩⟩ :=
    (SymplecticGeometry.timeExtend_apply_coe _ t x).trans (hgW ⟨_, hUW' ⟨trivial, hx⟩⟩)
  -- The extension `G` is `r ∘ k`, smooth on the open set `S` where `k` lands in `O`.
  let G : ℝ × P → N := fun p ↦ r (k p)
  let S : Set (ℝ × P) := univ ×ˢ U ∩ k ⁻¹' O
  have hS : IsOpen S := hk.continuousOn.isOpen_inter_preimage (isOpen_univ.prod hU) hO
  have hG : ContMDiffOn (𝓘(ℝ).prod J) I ∞ G S :=
    contMDiff_subtypeVal.comp_contMDiffOn
      (hr.comp (hk.mono inter_subset_left) fun _ hp ↦ hp.2)
  have hGF (t : unitInterval) (x : P) (hx : x ∈ U) : G (t, x) = F (t, x) := by
    simp only [G, hkF t x hx, hre]
  have hkO (t : unitInterval) (x : P) (hx : x ∈ U) : ((t : ℝ), x) ∈ S :=
    ⟨⟨trivial, hx⟩, by rw [mem_preimage, hkF t x hx]; exact heO (mem_range_self _)⟩
  -- The slices of `G` at times in `[0, 1]` are those of `F` near `A`.
  have hGF' (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (fun x ↦ G (t, x)) =ᶠ[nhdsSet A] fun x ↦ F (⟨t, ht⟩, x) :=
    Filter.eventually_of_mem (hU.mem_nhdsSet.2 hAU) fun x hx ↦ hGF ⟨t, ht⟩ x hx
  obtain ⟨δ, hδ, V, hAV, hVS, hV⟩ := exists_pos_forall_isSmoothEmbedding_of_injOn hS hG hA
    (fun p hp ↦ hkO ⟨p.1, hp.1⟩ p.2 (hAU hp.2))
    (fun t ht x hx y hy hxy ↦ (F.isSmoothEmbedding ⟨t, ht⟩).isEmbedding.injective <| by
      simpa only [toContMDiffMap_apply, (hGF' t ht).self_of_nhdsSet hx,
        (hGF' t ht).self_of_nhdsSet hy] using hxy)
    fun t ht x hx ↦ by
      rw [((hGF' t ht).filter_mono (nhds_le_nhdsSet hx)).mfderiv_eq]
      exact (F.isSmoothEmbedding ⟨t, ht⟩).isImmersion.mfderiv_injective (by simp) x
  have hVU : (V : Set P) ⊆ U := fun x hx ↦
    (hVS ⟨⟨by linarith, by linarith⟩, hx⟩ : ((0 : ℝ), x) ∈ S).1.2
  exact ⟨δ, hδ, V, hAV, G, hG.mono hVS, fun t x hx ↦ hGF t x (hVU hx), hV⟩

/-- **Isotopy extension at every time, over `ℝ`.** A smooth isotopy `F` of a boundaryless
manifold through smooth embeddings into a finite-dimensional, Hausdorff, σ-compact boundaryless
manifold `N` is on any compact subset `A` of the source the restriction of a jointly smooth
family `ψ` of diffeomorphisms of `N` over all real times, with `ψ 0 = id`, fixing every point
outside a compact set: `ψ t (f₀ x) = F (t, x)` for every `t ∈ [0, 1]` and every `x ∈ A`. -/
theorem exists_contMDiff_diffeomorph_forall_apply_eq [SigmaCompactSpace N]
    {f₀ f₁ : C^∞⟮J, P; I, N⟯} (F : SmoothIsotopy f₀ f₁) {A : Set P} (hA : IsCompact A) :
    ∃ ψ : ℝ → N ≃ₘ⟮I, I⟯ N, ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × N ↦ ψ p.1 p.2) ∧
      (∀ y, ψ 0 y = y) ∧ ∃ K : Set N, IsCompact K ∧ (∀ t, ∀ y ∉ K, ψ t y = y) ∧
      ∀ t : unitInterval, ∀ x ∈ A, ψ t (f₀ x) = F (t, x) := by
  obtain ⟨δ, hδ, V, hAV, G, hG, hGF, hemb⟩ := F.exists_contMDiff_extend hA
  obtain ⟨c, hc, hc_id, hc_mem, hc_out⟩ :=
    SymplecticGeometry.exists_contDiff_eqOn_id_Icc_mem_Ioo zero_le_one (half_pos hδ)
  have hc_mem' (t : ℝ) : c t ∈ Ioo (-δ) (1 + δ) :=
    ⟨by linarith [(hc_mem t).1], by linarith [(hc_mem t).2]⟩
  have hc_lo (t : ℝ) (ht : t ≤ -(δ / 2)) : c t = (0 + 1) / 2 :=
    hc_out t fun h ↦ by linarith [h.1]
  have hc_hi (t : ℝ) (ht : 1 + δ / 2 ≤ t) : c t = (0 + 1) / 2 :=
    hc_out t fun h ↦ by linarith [h.2]
  -- The motion `G'` of `V` over `ℝ`.
  let G' : ℝ × V → N := fun q ↦ G (c q.1, q.2)
  have hG' : ContMDiff (𝓘(ℝ, ℝ).prod J) I (⊤ : ℕ∞) G' :=
    hG.comp_contMDiff ((hc.contMDiff.comp contMDiff_fst).prodMk
      (contMDiff_subtypeVal.comp contMDiff_snd)) fun q ↦ ⟨hc_mem' q.1, q.2.property⟩
  have hA' : IsCompact (Subtype.val ⁻¹' A : Set V) := by
    rwa [Subtype.isCompact_iff, image_preimage_eq_of_subset (by rwa [Subtype.range_coe])]
  obtain ⟨X, K, hK, hXK, hX, hvel⟩ := exists_ambientVelocityField (m := ⊤) (n := ⊤) hG'
    (fun t ↦ hemb (c t) (hc_mem' t)) hA' (a := -(δ / 2)) (b := 1 + δ / 2)
    (fun t ht x _ ↦ by simp only [G', hc_lo t ht, hc_lo _ le_rfl])
    (fun t ht x _ ↦ by simp only [G', hc_hi t ht, hc_hi _ le_rfl]) le_top le_top
  have hX₁ := hX.of_le (m := 1) (by simp)
  have hcomplete := isCompleteVectorField_timeDependentSuspensionField hX₁ hK hXK
  refine ⟨fun t ↦ timeDependentFlowDiffeomorph hcomplete le_top hX 0 t,
    contMDiff_timeDependentFlowDiffeomorph le_top hX hcomplete 0,
    fun y ↦ (timeDependentFlowDiffeomorph_apply ..).trans (timeDependentFlowOf_self X 0 y), K, hK,
    fun t y hy ↦ (timeDependentFlowDiffeomorph_apply ..).trans
      (timeDependentFlowOf_eq_self_of_forall_eq_zero hX₁ (fun u ↦ hXK u y hy) 0 t),
    fun t x hx ↦ ?_⟩
  -- The curve `s ↦ G' (s, x)` solves the time-dependent equation, starts at `f₀ x`, and is `F`
  -- on `[0, 1]`.
  have hsol := timeDependentFlowOf_eq_of_hasMFDerivAt hX₁ (a := -1) (b := 2) (s := 0) (t := t)
    (fun u _ ↦ hvel u ⟨x, hAV hx⟩ hx) ⟨by norm_num, by norm_num⟩
    ⟨by linarith [t.property.1], by linarith [t.property.2]⟩
  have hc₀ : c 0 = ((0 : unitInterval) : ℝ) := hc_id ⟨le_rfl, zero_le_one⟩
  simp only [G', hc₀, hc_id t.property, id, hGF _ x (hAV hx), apply_zero] at hsol
  rw [timeDependentFlowDiffeomorph_apply]
  exact hsol

/-- **Isotopy extension at every time.** A smooth isotopy `F` of a boundaryless manifold through
smooth embeddings into a finite-dimensional, Hausdorff, σ-compact boundaryless manifold `N` is
on any compact subset `A` of the source the restriction of a smooth diffeotopy `Φ` of `N`
fixing every point outside a compact set: `Φ (t, f₀ x) = F (t, x)` for every time `t` and every
`x ∈ A`. The source need not be compact. -/
theorem exists_diffeotopy_forall_apply_eq [SigmaCompactSpace N] {f₀ f₁ : C^∞⟮J, P; I, N⟯}
    (F : SmoothIsotopy f₀ f₁) {A : Set P} (hA : IsCompact A) :
    ∃ Φ : Diffeotopy I ∞ N, ∃ K : Set N, IsCompact K ∧ (∀ t, ∀ y ∉ K, Φ (t, y) = y) ∧
      ∀ t, ∀ x ∈ A, Φ (t, f₀ x) = F (t, x) := by
  obtain ⟨ψ, hψ, h₀, K, hK, hψK, hψF⟩ := F.exists_contMDiff_diffeomorph_forall_apply_eq hA
  exact ⟨Diffeotopy.ofReal ψ hψ h₀, K, hK,
    fun t y hy ↦ by rw [Diffeotopy.ofReal_apply, hψK t y hy],
    fun t x hx ↦ by rw [Diffeotopy.ofReal_apply, hψF t x hx]⟩

/-- **Transport of functions along an isotopy.** Let `F` be a smooth isotopy of embeddings of `P`
into a manifold `N` of the same dimension, `A ⊆ P` compact, and `h` a smooth function on
`[0, 1] × P`. There is a smooth function `G` on `N × [0, 1]` that vanishes off a compact set and
satisfies `G (F (t, y), t) = h (t, y)` for every `t` and every `y` near `A`. -/
theorem exists_contMDiff_comp_eventuallyEq [SigmaCompactSpace N] [FiniteDimensional ℝ E']
    {f₀ f₁ : C^∞⟮J, P; I, N⟯} (F : SmoothIsotopy f₀ f₁)
    (hd : Module.finrank ℝ E' = Module.finrank ℝ E) {A : Set P} (hA : IsCompact A)
    {h : unitInterval × P → ℝ} (hh : ContMDiff ((𝓡∂ 1).prod J) 𝓘(ℝ) ∞ h) :
    ∃ (G : N × unitInterval → ℝ) (C : Set N), ContMDiff (I.prod (𝓡∂ 1)) 𝓘(ℝ) ∞ G ∧
      IsCompact C ∧ (∀ p, p.1 ∉ C → G p = 0) ∧
      ∀ t, ∀ x ∈ A, (fun y ↦ G (F (t, y), t)) =ᶠ[𝓝 x] fun y ↦ h (t, y) := by
  rcases isEmpty_or_nonempty P with hP | hP
  · exact ⟨0, ∅, contMDiff_const, isCompact_empty, fun _ _ ↦ rfl, fun _ x ↦ isEmptyElim x⟩
  have := Manifold.locallyCompact_of_finiteDimensional J (M := P)
  obtain ⟨A', hA', hAA'⟩ := exists_compact_superset hA
  obtain ⟨Ψ, -, -, -, hΨ⟩ := F.exists_diffeotopy_forall_apply_eq hA'
  have hf₀ : IsLocalDiffeomorph J I ∞ f₀ :=
    F.isSmoothEmbedding_left.isImmersion.isLocalDiffeomorph hd (by simp)
  have hinj : Injective f₀ := F.isSmoothEmbedding_left.isEmbedding.injective
  -- A cutoff `χ` on `N`, equal to `1` near `f₀ '' A` and supported in `f₀ '' A'`.
  obtain ⟨χ, hχ, hχ1, hχc, hχW, -⟩ :=
    (hA.image f₀.contMDiff.continuous).exists_contMDiff_one_nhds_tsupport_subset
    I (hf₀.isOpenMap _ isOpen_interior) (image_mono hAA')
  -- The function `χ · h_t ∘ f₀⁻¹` on `[0, 1] × N`.
  set g : unitInterval × N → ℝ := fun q ↦ χ q.2 * h (q.1, invFunOn f₀ univ q.2)
  have hg : ContMDiff ((𝓡∂ 1).prod I) 𝓘(ℝ) ∞ g := by
    rintro ⟨t, y⟩
    by_cases hy : y ∈ tsupport χ
    · obtain ⟨p, -, rfl⟩ := hχW hy
      exact (hχ.contMDiffAt.comp _ contMDiffAt_snd).mul (hh.contMDiffAt.comp _
        (contMDiffAt_fst.prodMk ((((hf₀.isLocalDiffeomorphOn univ).contMDiffOn_invFunOn
          isOpen_univ hinj.injOn).contMDiffAt ((hf₀.isOpenMap _ isOpen_univ).mem_nhds
            (mem_image_of_mem f₀ (mem_univ p)))).comp (t, f₀ p) contMDiffAt_snd)))
    · refine contMDiffAt_const (c := (0 : ℝ)).congr_of_eventuallyEq ?_
      filter_upwards [(continuous_snd.tendsto (t, y)).eventually
        (notMem_tsupport_iff_eventuallyEq.1 hy)] with q hq
      simp only [g, show χ q.2 = 0 from hq, zero_mul]
  refine ⟨fun p ↦ g (p.2, Ψ.symm (p.2, p.1)), Ψ.cylinderMap '' (tsupport χ ×ˢ univ),
    hg.comp (contMDiff_snd.prodMk (Ψ.symm.contMDiff.comp (contMDiff_snd.prodMk contMDiff_fst))),
    (hχc.isCompact.prod isCompact_univ).image Ψ.contMDiff_cylinderMap.continuous,
    fun p hp ↦ ?_, fun t x hx ↦ ?_⟩
  · have : Ψ.symm (p.2, p.1) ∉ tsupport χ := fun h ↦ hp ⟨(_, p.2), ⟨h, mem_univ _⟩, by
      rw [Diffeotopy.cylinderMap_apply, Diffeotopy.apply_mk_symm_apply]⟩
    simp only [g, image_eq_zero_of_notMem_tsupport this, zero_mul]
  · filter_upwards [isOpen_interior.mem_nhds (hAA' hx),
      (f₀.contMDiff.continuous.tendsto x).eventually
        (hχ1.filter_mono (nhds_le_nhdsSet (mem_image_of_mem f₀ hx)))]
      with y hy hy1
    simp only [g, ← hΨ t y (interior_subset hy), Diffeotopy.symm_apply_mk_apply, hy1, one_mul,
      hinj.injOn.leftInvOn_invFunOn (mem_univ y)]

end SmoothIsotopy

/-- **Pushing a point along a path.** A smooth path `c` in a finite-dimensional, Hausdorff,
σ-compact boundaryless manifold is the track of its starting point under a smooth diffeotopy `Ψ`
fixing every point outside a compact set: `Ψ (t, c 0) = c t` for every time `t`. -/
theorem _root_.ContMDiff.exists_diffeotopy_forall_apply_eq [SigmaCompactSpace N]
    {c : unitInterval → N} (hc : ContMDiff (𝓡∂ 1) I ∞ c) :
    ∃ Ψ : Diffeotopy I ∞ N, ∃ K : Set N, IsCompact K ∧ (∀ t, ∀ y ∉ K, Ψ (t, y) = y) ∧
      ∀ t, Ψ (t, c 0) = c t := by
  -- `c` is a smooth isotopy of the point `EuclideanSpace ℝ (Fin 0)`.
  let Q := EuclideanSpace ℝ (Fin 0)
  have hemb (t : unitInterval) : IsSmoothEmbedding 𝓘(ℝ, Q) I ∞ (fun _ : Q ↦ c t) := by
    refine ⟨contMDiff_const.isImmersion_of_injective_mfderiv (by simp) fun x ↦ ?_,
      Topology.IsEmbedding.of_subsingleton _⟩
    -- TangentSpace is a type synonym for the model; its subsingleton instance is not inferred.
    have : Subsingleton (TangentSpace 𝓘(ℝ, Q) x) := inferInstanceAs (Subsingleton Q)
    exact injective_of_subsingleton _
  let F : SmoothIsotopy (⟨fun _ ↦ c 0, contMDiff_const⟩ : C^∞⟮𝓘(ℝ, Q), Q; I, N⟯)
      ⟨fun _ ↦ c 1, contMDiff_const⟩ :=
    { toContMDiffMap := ⟨fun p ↦ c p.1, hc.comp contMDiff_fst⟩
      map_zero_left := fun _ ↦ rfl
      map_one_left := fun _ ↦ rfl
      isSmoothEmbedding := hemb }
  obtain ⟨Ψ, K, hK, hΨK, hΨ⟩ := F.exists_diffeotopy_forall_apply_eq (isCompact_singleton (x := 0))
  exact ⟨Ψ, K, hK, hΨK, fun t ↦ hΨ t 0 rfl⟩

end TauCeti

end
