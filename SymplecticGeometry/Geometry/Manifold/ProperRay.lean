/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Connected
public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Homogeneity
import TauCeti.Geometry.Manifold.SmoothEmbedding.Diffeomorph

/-!
# Proper rays from a closed discrete set

This file builds rays, smooth embeddings `ℝ → M` that go to infinity, through the points of a
closed discrete set of a manifold of dimension at least two. Each ray is grown arc by arc.

## Main results

* `exists_diffeomorph_grow_arc`: one arc of growth. Let `W` be a preconnected open set of `M`,
  `s` a closed discrete set and finitely many disjoint arcs with free ends, closed in `W \ s`,
  among them the part `γ '' J` of a smooth embedding `γ` that ends at `γ T`. Some diffeomorphism
  `Ψ` of `M`, the identity outside a compact subset of the open set `U` left from `W` by removing
  `s` and the arcs, makes `Ψ ∘ γ` agree with `γ` up to `T`, run through `U` just after `T`, and
  reach a prescribed point of `U`.

The set `U` is preconnected by `isPreconnected_sdiff_union_iUnion_image_of_one_lt_rank`, and
`Ψ` is the final map of a diffeotopy given by Tau Ceti's homogeneity lemma
`TauCeti.exists_diffeotopy_final_apply_eq_of_isPreconnected`, which moves a point of `γ` just
after `T` to the prescribed point. Since `Ψ` fixes the arcs, the part of `γ` already built does
not move.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Theorem 7.3.1, for the construction of the rays.
* J. W. Milnor, *Topology from the Differentiable Viewpoint*, University Press of Virginia
  (1965), §4, for the homogeneity lemma.
-/

public section

open Function Set Topology Manifold
open scoped ContDiff

namespace SymplecticGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Growing a ray by one arc.** Let `M` be a finite-dimensional Hausdorff boundaryless smooth
manifold whose model space has rank greater than one, `W ⊆ M` open and preconnected and `s`
closed and discrete. For `i` in a finite type let `f i : ℝ → M` be a smooth embedding and
`J i ⊆ ℝ` order-connected with a greatest or a least element, such that the arcs `f i '' J i` lie
in `W \ s`, are pairwise disjoint and are closed in `W \ s`; write
`U := W \ (s ∪ ⋃ i, f i '' J i)`. Let `γ := f i₀`, where `T` is the greatest element of `J i₀`,
and suppose that every point of `γ '' Iic T` in `W` lies on one of the arcs. Then for every
`y ∈ U` there are a diffeomorphism `Ψ` of `M`, the identity outside a
compact subset `K` of `U`, and `δ > 0` such that `Ψ ∘ γ` is a smooth embedding that agrees with
`γ` on `Iic T`, sends `T + δ` to `y`, and maps `Ioc T (T + δ)` into `U`. -/
theorem exists_diffeomorph_grow_arc {ι : Type*} [Finite ι] (hE : 1 < Module.rank ℝ E)
    {W s : Set M} (hW : IsOpen W) (hWc : IsPreconnected W) (hs : IsClosed s)
    (hd : IsDiscrete s) {f : ι → ℝ → M} (hf : ∀ i, IsSmoothEmbedding 𝓘(ℝ) I ∞ (f i))
    {J : ι → Set ℝ} (hJ : ∀ i, (J i).OrdConnected)
    (hb : ∀ i, ∃ b, IsGreatest (J i) b ∨ IsLeast (J i) b) (hJW : ∀ i, f i '' J i ⊆ W \ s)
    (hdisj : Pairwise (Disjoint on fun i ↦ f i '' J i))
    (hcl : ∀ i, closure (f i '' J i) ∩ (W \ s) ⊆ f i '' J i)
    {γ : ℝ → M} {i₀ : ι} (hγ : f i₀ = γ) {T : ℝ} (hT : IsGreatest (J i₀) T)
    (hγW : γ '' Iic T ∩ W ⊆ ⋃ i, f i '' J i) {y : M}
    (hy : y ∈ W \ (s ∪ ⋃ i, f i '' J i)) :
    ∃ (Ψ : M ≃ₘ^∞⟮I, I⟯ M) (K : Set M), IsCompact K ∧ K ⊆ W \ (s ∪ ⋃ i, f i '' J i) ∧
      EqOn Ψ id Kᶜ ∧ ∃ δ > 0, IsSmoothEmbedding 𝓘(ℝ) I ∞ (Ψ ∘ γ) ∧
        EqOn (Ψ ∘ γ) γ (Iic T) ∧ Ψ (γ (T + δ)) = y ∧
        Ψ ∘ γ '' Ioc T (T + δ) ⊆ W \ (s ∪ ⋃ i, f i '' J i) := by
  -- `U` is open, since the arcs are closed in `W \ s`.
  have hUo : IsOpen (W \ (s ∪ ⋃ i, f i '' J i)) := by
    rw [← sdiff_sdiff]
    exact (hW.sdiff hs).sdiff_iUnion_of_closure_inter_subset hcl
  set U := W \ (s ∪ ⋃ i, f i '' J i)
  subst hγ
  have hUc : IsPreconnected U :=
    isPreconnected_sdiff_union_iUnion_image_of_one_lt_rank hE hW hWc hs hd hf hJ hb hJW hdisj hcl
  -- Near `γ T`, the points of `W` off `s` miss the closures of the other arcs.
  set V := (W \ s) \ ⋃ i ∈ {i | i ≠ i₀}, closure (f i '' J i)
  have hTV : f i₀ T ∈ V := by
    have hT' := hJW i₀ (mem_image_of_mem _ hT.1)
    refine ⟨hT', fun h ↦ ?_⟩
    obtain ⟨i, hi, hTi⟩ := mem_iUnion₂.1 h
    exact disjoint_left.1 (hdisj hi) (hcl i ⟨hTi, hT'⟩) (mem_image_of_mem _ hT.1)
  have hVo : IsOpen V := (hW.sdiff hs).sdiff
    ((toFinite _).isClosed_biUnion fun _ _ ↦ isClosed_closure)
  have hTV' : f i₀ ⁻¹' V ∈ 𝓝 T :=
    (hf i₀).isEmbedding.continuous.continuousAt.preimage_mem_nhds (hVo.mem_nhds hTV)
  obtain ⟨ε, hε, hεV⟩ := Metric.mem_nhds_iff.1 hTV'
  -- The part of `γ` just after `T` lies in `U`.
  have hγU : f i₀ '' Ioc T (T + ε / 2) ⊆ U := by
    rintro _ ⟨t, ⟨htT, htε⟩, rfl⟩
    have htV : f i₀ t ∈ V := hεV (by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith)
    refine ⟨htV.1.1, fun h ↦ h.elim htV.1.2 fun h ↦ ?_⟩
    obtain ⟨i, u, hu, hut⟩ := mem_iUnion.1 h
    by_cases hi : i = i₀
    · subst hi
      exact (hT.2 hu).not_gt (((hf i).isEmbedding.injective hut) ▸ htT)
    · exact htV.2 (mem_iUnion₂.2 ⟨i, hi, subset_closure ⟨u, hu, hut⟩⟩)
  have hδU : f i₀ (T + ε / 2) ∈ U := hγU ⟨T + ε / 2, ⟨by linarith, le_rfl⟩, rfl⟩
  obtain ⟨Φ, K, hK, hKU, hΦK, hΦ⟩ :=
    TauCeti.exists_diffeotopy_final_apply_eq_of_isPreconnected (I := I) (n := ∞) (m := ⊤) le_top
      (by simp) hUo hUc hδU hy
  have hΨK : EqOn Φ.final id Kᶜ := fun z hz ↦ by simpa using hΦK 1 hz
  refine ⟨Φ.final, K, hK, hKU, hΨK, ε / 2, half_pos hε,
    TauCeti.isSmoothEmbedding_diffeomorph_comp (hf i₀) Φ.final, fun t ht ↦ hΨK fun htK ↦ ?_,
    hΦ, ?_⟩
  · obtain ⟨i, hi⟩ := mem_iUnion.1 (hγW ⟨mem_image_of_mem _ ht, (hKU htK).1⟩)
    exact (hKU htK).2 (.inr (mem_iUnion.2 ⟨i, hi⟩))
  · rw [image_comp]
    exact ((Φ.mapsTo_final_of_eqOn_compl hKU hΦK).mono_left hγU).image_subset

end SymplecticGeometry

end
