/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Convex.Basic
public import TauCeti.Geometry.Manifold.LocallyFlat.Smooth
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.Order.IntermediateValue

/-!
# Slice charts in which a smooth embedding of `ℝ` is a monotone line

Let `f : ℝ → M` be a `C^n` embedding into a boundaryless manifold, with complement
`F' := h.isImmersion.complement`. Near each `f t`, and inside any prescribed neighbourhood `W` of
it, there is a chart `ψ : M → ℝ × F'` with convex target which flattens `range f` onto `ℝ × {0}`,
which sees of the curve only the image of an open interval `O` around `t`, and in which the curve
reads `s ↦ (g s, 0)` with `g` strictly monotone or strictly antitone on `O`.

The chart is Tau Ceti's slice chart of a smooth embedding
(`TauCeti.IsLocallyFlat.of_isSmoothEmbedding` and `TauCeti.IsLocallyFlat.exists_isSliceChart`),
shrunk with `TauCeti.IsSliceChart.exists_target_eq` to a ball. Before shrinking, the slice
coordinate `g` is continuous and injective near `t`, hence strictly monotone or antitone on an
interval `(a, b)` around `t`
(`ContinuousOn.strictMonoOn_of_injOn_Ioo`); since `f` is an embedding, some open set of `M` meets
the curve exactly in `f '' (a, b)`, and the ball is taken small enough that the chart's source lies
in that open set and in `W`. The parameters that the shrunk chart sees then form an interval, by
monotonicity of `g` and convexity of the ball.

## Main results

* `Manifold.IsSmoothEmbedding.exists_isSliceChart_convex`: the chart above, together with the
  description of the image of `f '' J` in it for every `J : Set ℝ`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Springer GTM 218 (2013),
  Chapter 5, for slice charts of embedded submanifolds.
-/

public section

open Set Topology Metric TauCeti
open scoped Manifold

namespace Manifold.IsSmoothEmbedding

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {n : WithTop ℕ∞} {f : ℝ → M}

/-- **A convex slice chart for a smooth embedding of `ℝ`.** Let `f : ℝ → M` be a `C^n` embedding
into a boundaryless manifold, `F'` the complement of its immersion, `t : ℝ` and `W` a neighbourhood
of `f t`. Then there are a chart `ψ : M → ℝ × F'`, an open interval `O ∋ t` and `g : ℝ → ℝ` such
that `f t ∈ ψ.source ⊆ W`, the target of `ψ` is convex, `ψ` is a slice chart for `range f` onto
`ℝ × {0}`, the source of `ψ` meets `range f` exactly in `f '' O`, `ψ (f s) = (g s, 0)` for
`s ∈ O`, `g` is strictly monotone or strictly antitone on `O`, and for every `J : Set ℝ` the chart
maps the part of `f '' J` in its source onto the part of `(g '' (J ∩ O)) ×ˢ {0}` in its target. -/
theorem exists_isSliceChart_convex [I.Boundaryless] (h : IsSmoothEmbedding 𝓘(ℝ) I n f) (t : ℝ)
    {W : Set M} (hW : W ∈ 𝓝 (f t)) :
    ∃ (ψ : OpenPartialHomeomorph M (ℝ × h.isImmersion.complement)) (O : Set ℝ) (g : ℝ → ℝ),
      f t ∈ ψ.source ∧ ψ.source ⊆ W ∧ Convex ℝ ψ.target ∧
      IsSliceChart ψ (univ ×ˢ {0}) (range f) ∧
      IsOpen O ∧ O.OrdConnected ∧ t ∈ O ∧ ψ.source ∩ range f = f '' O ∧
      (∀ s ∈ O, ψ (f s) = (g s, 0)) ∧ (StrictMonoOn g O ∨ StrictAntiOn g O) ∧
      ∀ J : Set ℝ, ψ '' (ψ.source ∩ f '' J) = ψ.target ∩ (g '' (J ∩ O)) ×ˢ {0} := by
  obtain ⟨φ, hφt, hφ⟩ := (IsLocallyFlat.of_isSmoothEmbedding h).exists_isSliceChart t
  have hfc := h.isEmbedding.continuous
  -- The slice coordinate of the curve in the chart `φ`.
  set g : ℝ → ℝ := fun s => (φ (f s)).1
  have hgφ : ∀ s ∈ f ⁻¹' φ.source, φ (f s) = (g s, 0) := fun s hs =>
    (hφ.mk_fst_zero_eq hs (mem_range_self s)).symm
  have hgc : ContinuousOn g (f ⁻¹' φ.source) :=
    continuous_fst.comp_continuousOn (φ.continuousOn.comp hfc.continuousOn fun _ hs => hs)
  have hgi : InjOn g (f ⁻¹' φ.source) := by
    intro s hs s' hs' hss'
    refine h.isEmbedding.injective (φ.injOn hs hs' ?_)
    rw [hgφ s hs, hgφ s' hs', hss']
  obtain ⟨a, b, hab, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.1
    ((φ.open_source.preimage hfc).mem_nhds hφt)
  have hmono : StrictMonoOn g (Ioo a b) ∨ StrictAntiOn g (Ioo a b) :=
    (hgc.mono hsub).strictMonoOn_of_injOn_Ioo (hab.1.trans hab.2) (hgi.mono hsub)
  -- An open set of `M` meeting the curve exactly in `f '' (a, b)`.
  obtain ⟨U, hU, hfU⟩ := h.isEmbedding.isInducing.isOpen_iff.1 (isOpen_Ioo (a := a) (b := b))
  -- Shrink `φ` to a ball whose points come from `U ∩ interior W`.
  have hVo : IsOpen (φ.target ∩ φ.symm ⁻¹' (U ∩ interior W)) :=
    φ.isOpen_inter_preimage_symm (hU.inter isOpen_interior)
  have hftV : φ (f t) ∈ φ.target ∩ φ.symm ⁻¹' (U ∩ interior W) := by
    refine ⟨φ.map_source hφt, ?_⟩
    rw [mem_preimage, φ.left_inv hφt]
    exact ⟨(hfU ▸ hab : t ∈ f ⁻¹' U), mem_interior_iff_mem_nhds.2 hW⟩
  obtain ⟨r, hr, hrV⟩ := Metric.isOpen_iff.1 hVo _ hftV
  obtain ⟨ψ, hψφ, hψs, hψt, hψ⟩ :=
    hφ.exists_target_eq isOpen_ball (hrV.trans inter_subset_left)
  have hsrc : ∀ x, x ∈ ψ.source ↔ x ∈ φ.source ∧ φ x ∈ ball (φ (f t)) r := fun x => by
    rw [hψs, mem_inter_iff, mem_preimage]
  have hsrcUW : ∀ x ∈ ψ.source, x ∈ U ∧ x ∈ W := by
    intro x hx
    rw [hsrc] at hx
    have hx' := (hrV hx.2).2
    rw [mem_preimage, φ.left_inv hx.1] at hx'
    exact ⟨hx'.1, interior_subset hx'.2⟩
  have hOab : f ⁻¹' ψ.source ⊆ Ioo a b := fun s hs => hfU ▸ (hsrcUW _ hs).1
  have hO : ∀ s, s ∈ f ⁻¹' ψ.source ↔
      s ∈ Ioo a b ∧ (g s, (0 : h.isImmersion.complement)) ∈ ball (φ (f t)) r := by
    intro s
    refine ⟨fun hs => ⟨hOab hs, ?_⟩, fun hs => (hsrc _).2 ⟨hsub hs.1, ?_⟩⟩
    · rw [← hgφ s (hsub (hOab hs))]
      exact ((hsrc _).1 hs).2
    · rw [hgφ s (hsub hs.1)]
      exact hs.2
  have hψg : ∀ s ∈ f ⁻¹' ψ.source, ψ (f s) = (g s, 0) := fun s hs => by
    rw [hψφ]
    exact hgφ s (hsub (hOab hs))
  have himage : ψ.source ∩ range f = f '' (f ⁻¹' ψ.source) :=
    (image_preimage_eq_inter_range).symm
  refine ⟨ψ, f ⁻¹' ψ.source, g, (hsrc _).2 ⟨hφt, mem_ball_self hr⟩,
    fun x hx => (hsrcUW x hx).2, hψt ▸ convex_ball _ _, hψ, ψ.open_source.preimage hfc,
    ⟨fun x hx y hy z hz => ?_⟩, (hsrc _).2 ⟨hφt, mem_ball_self hr⟩, himage, hψg,
    hmono.imp (·.mono hOab) (·.mono hOab), fun J => ?_⟩
  · -- The parameters seen by `ψ` form an interval.
    rw [hO] at hx hy ⊢
    have hz' : z ∈ Ioo a b := ordConnected_Ioo.out hx.1 hy.1 hz
    refine ⟨hz', (convex_ball _ _).segment_subset hx.2 hy.2 ?_⟩
    have hgz : g z ∈ segment ℝ (g x) (g y) := by
      rw [segment_eq_uIcc]
      rcases hmono with hm | hm
      · exact mem_uIcc_of_le (hm.monotoneOn hx.1 hz' hz.1) (hm.monotoneOn hz' hy.1 hz.2)
      · exact mem_uIcc_of_ge (hm.antitoneOn hz' hy.1 hz.2) (hm.antitoneOn hx.1 hz' hz.1)
    have := image_segment ℝ (LinearMap.inl ℝ ℝ h.isImmersion.complement).toAffineMap (g x) (g y) ▸
      mem_image_of_mem _ hgz
    simpa using this
  · ext p
    constructor
    · rintro ⟨x, ⟨hx, s, hs, rfl⟩, rfl⟩
      rw [hψg s hx]
      exact ⟨hψg s hx ▸ ψ.map_source hx, mem_prod.2 ⟨mem_image_of_mem g ⟨hs, hx⟩, rfl⟩⟩
    · rintro ⟨-, hpg⟩
      obtain ⟨⟨s, hs, hsp⟩, hp0⟩ := mem_prod.1 hpg
      refine ⟨f s, ⟨hs.2, mem_image_of_mem f hs.1⟩, ?_⟩
      rw [hψg s hs.2, hsp, ← eq_of_mem_singleton hp0]

end Manifold.IsSmoothEmbedding

end
