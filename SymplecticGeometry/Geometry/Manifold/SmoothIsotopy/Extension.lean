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
import SymplecticGeometry.Geometry.Diffeomorphism.Diffeotopy.Real
import SymplecticGeometry.Geometry.Manifold.ContMDiff.TimeExtension
import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.Neighborhood
import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Flow
import TauCeti.Geometry.Manifold.Immersion.LocalDiffeomorph
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Injective
import TauCeti.Geometry.Manifold.PartitionOfUnity.Compact
import TauCeti.Geometry.Manifold.SmoothEmbedding.LeftInverse
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
   at times in `(-δ, 1 + δ)` are smooth embeddings of `V`. The isotopy, as a smooth map, extends
   in time near `A` (`ContMDiff.exists_contMDiffOn_extend_of_isCompact`, by Seeley's extension
   composed with an embedding into a Euclidean space and a retraction), and the slices of the
   extension are embeddings near `A` for times near `[0, 1]`
   (`TauCeti.exists_pos_forall_isSmoothEmbedding_of_eventuallyEq`).
2. Composed with a smooth `c : ℝ → (-δ, 1 + δ)` that is the identity on `[0, 1]` and constant
   outside `(-δ / 2, 1 + δ / 2)` (*Smooth families*'
   `SymplecticGeometry.exists_contDiff_eqOn_id_Icc_mem_Ioo`), the extension becomes a
   motion over `ℝ` through embeddings, stationary outside a bounded interval and equal to `F` on
   `[0, 1]` (`TauCeti.exists_contMDiff_forall_isSmoothEmbedding_comp`).
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

* `TauCeti.exists_contMDiff_forall_isSmoothEmbedding_comp`: a motion through embeddings at times
  near `[0, 1]`, run at the time of a cut-off, is a motion over `ℝ` through embeddings that is
  stationary outside a bounded interval.
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
* `ContMDiff.exists_contMDiff_diffeomorph_forall_apply_eq`: a smooth path is the track of its
  starting point under a jointly smooth family of diffeomorphisms over `ℝ`, with `ψ 0` the
  identity, that fixes every point outside a compact set. The path is a smooth isotopy of a
  point, the zero-dimensional space `EuclideanSpace ℝ (Fin 0)`, whose slices are smooth
  embeddings by Tau Ceti's `TauCeti.isSmoothEmbedding_const_of_subsingleton`.

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

omit [FiniteDimensional ℝ E] [I.Boundaryless] [J.Boundaryless] [IsManifold J ∞ P] [IsManifold I ∞ N]
  [T2Space N] in
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
  -- Extend `F` in time near `A`; the slices of the extension at times in `[0, 1]` are those of
  -- `F` near `A`.
  obtain ⟨S, hS, hAS, G, hG, hGF⟩ := F.contMDiff.exists_contMDiffOn_extend_of_isCompact hA
  obtain ⟨δ, hδ, V, hAV, hVS, hV⟩ := exists_pos_forall_isSmoothEmbedding_of_eventuallyEq hS hG hA
    hAS (fun t ↦ by simpa only [toContMDiffMap_apply] using F.isSmoothEmbedding t)
    fun t ht ↦ Filter.eventually_of_mem
      ((hS.preimage (Continuous.prodMk_right t)).mem_nhdsSet.2 fun x hx ↦ hAS ⟨ht, hx⟩)
      fun x hx ↦ hGF ⟨t, ht⟩ x hx
  exact ⟨δ, hδ, V, hAV, G, hG.mono hVS,
    fun t x hx ↦ hGF t x (hVS ⟨⟨by linarith [t.property.1], by linarith [t.property.2]⟩, hx⟩), hV⟩

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
  -- The motion `G'` of `V` over `ℝ`.
  obtain ⟨c, hG', hemb', hc_id, hc_lo, hc_hi⟩ :=
    exists_contMDiff_forall_isSmoothEmbedding_comp hδ hG hemb
  let G' : ℝ × V → N := fun q ↦ G (c q.1, q.2)
  have hA' : IsCompact (Subtype.val ⁻¹' A : Set V) :=
    Topology.IsInducing.subtypeVal.isCompact_preimage' hA (by rwa [Subtype.range_coe])
  obtain ⟨X, K, hK, hXK, hX, hvel⟩ := exists_ambientVelocityField (m := ⊤) (n := ⊤) (G := G')
    hG' hemb' hA' (a := -(δ / 2)) (b := 1 + δ / 2) (fun t ht x _ ↦ by simp only [G', hc_lo t ht])
    (fun t ht x _ ↦ by simp only [G', hc_hi t ht]) le_top le_top
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
  have hc₀ : c 0 = ((0 : unitInterval) : ℝ) := hc_id 0 ⟨le_rfl, zero_le_one⟩
  simp only [G', hc₀, hc_id t t.property, hGF _ x (hAV hx), apply_zero] at hsol
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
σ-compact boundaryless manifold is the track of its starting point under a family `ψ` of
diffeomorphisms over `ℝ`, jointly smooth in time and space, with `ψ 0` the identity, that fixes
every point outside a compact set: `ψ t (c 0) = c t` for every `t ∈ [0, 1]`. -/
theorem _root_.ContMDiff.exists_contMDiff_diffeomorph_forall_apply_eq [SigmaCompactSpace N]
    {c : unitInterval → N} (hc : ContMDiff (𝓡∂ 1) I ∞ c) :
    ∃ ψ : ℝ → N ≃ₘ⟮I, I⟯ N, ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × N ↦ ψ p.1 p.2) ∧
      (∀ y, ψ 0 y = y) ∧ ∃ K : Set N, IsCompact K ∧ (∀ t, ∀ y ∉ K, ψ t y = y) ∧
      ∀ t : unitInterval, ψ t (c 0) = c t := by
  -- `c` is a smooth isotopy of the point `EuclideanSpace ℝ (Fin 0)`.
  let Q := EuclideanSpace ℝ (Fin 0)
  let F : SmoothIsotopy (⟨fun _ ↦ c 0, contMDiff_const⟩ : C^∞⟮𝓘(ℝ, Q), Q; I, N⟯)
      ⟨fun _ ↦ c 1, contMDiff_const⟩ :=
    { toContMDiffMap := ⟨fun p ↦ c p.1, hc.comp contMDiff_fst⟩
      map_zero_left := fun _ ↦ rfl
      map_one_left := fun _ ↦ rfl
      isSmoothEmbedding := fun t ↦ isSmoothEmbedding_const_of_subsingleton (by simp) (c t) }
  obtain ⟨ψ, hψ, hψ0, K, hK, hψK, hψc⟩ :=
    F.exists_contMDiff_diffeomorph_forall_apply_eq (isCompact_singleton (x := 0))
  exact ⟨ψ, hψ, hψ0, K, hK, hψK, fun t ↦ hψc t 0 rfl⟩

end TauCeti

end
