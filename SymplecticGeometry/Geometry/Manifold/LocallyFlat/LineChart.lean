/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Convex.Basic
public import TauCeti.Geometry.Manifold.LocallyFlat.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.Order.IntermediateValue

/-!
# Slice charts in which a locally flat embedding of `ℝ` is a monotone line

Let `f : ℝ → M` be a locally flat embedding into a topological space, with complementary model
`F'`. Near each `f t`, and inside any prescribed neighbourhood `W` of it, there is a chart
`ψ : M → ℝ × F'` with convex target which flattens `range f` onto `ℝ × {0}`, which sees of the
curve only the image of an open interval `O` around `t`, and in which the curve reads
`s ↦ (g s, 0)` with `g` strictly monotone or strictly antitone on `O`. A `C^n` embedding of `ℝ`
into a boundaryless manifold is locally flat (`TauCeti.IsLocallyFlat.of_isSmoothEmbedding`), with
the complement of its immersion as `F'`, so the result applies to it.

The chart is Tau Ceti's slice chart (`TauCeti.IsLocallyFlat.exists_isSliceChart`), shrunk with
`TauCeti.IsSliceChart.exists_target_eq` to a ball. Before shrinking, the slice coordinate `g` is
continuous and injective near `t`, hence strictly monotone or antitone on an interval `(a, b)`
around `t` (`ContinuousOn.strictMonoOn_of_injOn_Ioo`); since `f` is an embedding, some open set
of `M` meets the curve exactly in `f '' (a, b)`, and the ball is taken small enough that the
chart's source lies in that open set and in `W`. The parameters that the shrunk chart sees then
form an interval, by monotonicity of `g` and convexity of the ball
(`Set.OrdConnected.preimage_monotoneOn`).

## Main results

* `OpenPartialHomeomorph.image_source_inter_image_eq`: if a chart reads a map `f` as
  `s ↦ (g s, 0)`, it sends the part of `f '' J` in its source onto the part of
  `(g '' (J ∩ f ⁻¹' e.source)) ×ˢ {0}` in its target.
* `TauCeti.IsLocallyFlat.exists_isSliceChart_convex`: the chart above.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Springer GTM 218 (2013),
  Chapter 5, for slice charts of embedded submanifolds.
-/

public section

open Set Topology Metric

namespace OpenPartialHomeomorph

variable {X N A B : Type*} [TopologicalSpace X] [TopologicalSpace A] [TopologicalSpace B] [Zero B]

/-- If a chart `e : X → A × B` reads `f : N → X` as `s ↦ (g s, 0)` wherever `f s` lies in its
source, then for every `J : Set N` it maps the part of `f '' J` in its source onto the part of
`(g '' (J ∩ f ⁻¹' e.source)) ×ˢ {0}` in its target. -/
theorem image_source_inter_image_eq (e : OpenPartialHomeomorph X (A × B)) {f : N → X}
    {g : N → A} (hg : ∀ s ∈ f ⁻¹' e.source, e (f s) = (g s, 0)) (J : Set N) :
    e '' (e.source ∩ f '' J) = e.target ∩ (g '' (J ∩ f ⁻¹' e.source)) ×ˢ {0} := by
  ext p
  constructor
  · rintro ⟨x, ⟨hx, s, hs, rfl⟩, rfl⟩
    rw [hg s hx]
    exact ⟨hg s hx ▸ e.map_source hx, mem_prod.2 ⟨mem_image_of_mem g ⟨hs, hx⟩, rfl⟩⟩
  · rintro ⟨-, hpg⟩
    obtain ⟨⟨s, hs, hsp⟩, hp0⟩ := mem_prod.1 hpg
    refine ⟨f s, ⟨hs.2, mem_image_of_mem f hs.1⟩, ?_⟩
    rw [hg s hs.2, hsp, ← eq_of_mem_singleton hp0]

end OpenPartialHomeomorph

namespace TauCeti.IsLocallyFlat

variable {M : Type*} [TopologicalSpace M] {F' : Type*} [SeminormedAddCommGroup F']
  [NormedSpace ℝ F'] {f : ℝ → M}

/-- **A convex slice chart for a locally flat embedding of `ℝ`.** Let `f : ℝ → M` be locally flat
with complementary model `F'`, `t : ℝ` and `W` a neighbourhood of `f t`. Then there are a chart
`ψ : M → ℝ × F'`, an open interval `O ∋ t` (an open, order-connected set) and `g : ℝ → ℝ` such
that `f t ∈ ψ.source ⊆ W`, the target of `ψ` is convex, `ψ` is a slice chart for `range f` onto
`ℝ × {0}`, the source of `ψ` meets `range f` exactly in `f '' O`, `ψ (f s) = (g s, 0)` for
`s ∈ O`, `g` is strictly monotone or strictly antitone on `O`, and for every `J : Set ℝ` the chart
maps the part of `f '' J` in its source onto the part of `(g '' (J ∩ O)) ×ˢ {0}` in its target. -/
theorem exists_isSliceChart_convex (h : IsLocallyFlat ℝ F' f) (t : ℝ) {W : Set M}
    (hW : W ∈ 𝓝 (f t)) :
    ∃ (ψ : OpenPartialHomeomorph M (ℝ × F')) (O : Set ℝ) (g : ℝ → ℝ),
      f t ∈ ψ.source ∧ ψ.source ⊆ W ∧ Convex ℝ ψ.target ∧
      IsSliceChart ψ (univ ×ˢ {0}) (range f) ∧
      IsOpen O ∧ O.OrdConnected ∧ t ∈ O ∧ ψ.source ∩ range f = f '' O ∧
      (∀ s ∈ O, ψ (f s) = (g s, 0)) ∧ (StrictMonoOn g O ∨ StrictAntiOn g O) ∧
      ∀ J : Set ℝ, ψ '' (ψ.source ∩ f '' J) = ψ.target ∩ (g '' (J ∩ O)) ×ˢ {0} := by
  obtain ⟨φ, hφt, hφ⟩ := h.exists_isSliceChart t
  have hfc := h.continuous
  -- The slice coordinate of the curve in the chart `φ`.
  set g : ℝ → ℝ := fun s => (φ (f s)).1
  have hgφ : ∀ s ∈ f ⁻¹' φ.source, φ (f s) = (g s, 0) := fun s hs =>
    (hφ.mk_fst_zero_eq hs (mem_range_self s)).symm
  have hgc : ContinuousOn g (f ⁻¹' φ.source) :=
    continuous_fst.comp_continuousOn (φ.continuousOn.comp hfc.continuousOn fun _ hs => hs)
  have hgi : InjOn g (f ⁻¹' φ.source) := fun s hs s' hs' hss' =>
    h.isEmbedding.injective (φ.injOn hs hs' (by rw [hgφ s hs, hgφ s' hs', hss']))
  obtain ⟨a, b, hab, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.1
    ((φ.open_source.preimage hfc).mem_nhds hφt)
  have hmono : StrictMonoOn g (Ioo a b) ∨ StrictAntiOn g (Ioo a b) :=
    (hgc.mono hsub).strictMonoOn_of_injOn_Ioo (hab.1.trans hab.2) (hgi.mono hsub)
  -- An open set of `M` meeting the curve exactly in `f '' (a, b)`.
  obtain ⟨U, hU, hfU⟩ := h.isEmbedding.isInducing.isOpen_iff.1 (isOpen_Ioo (a := a) (b := b))
  -- Shrink `φ` to a ball whose points come from `U ∩ interior W`.
  obtain ⟨r, hr, hrV⟩ := Metric.isOpen_iff.1 (φ.isOpen_inter_preimage_symm
    (hU.inter isOpen_interior)) (φ (f t)) ⟨φ.map_source hφt, by
      rw [mem_preimage, φ.left_inv hφt]
      exact ⟨(hfU ▸ hab : t ∈ f ⁻¹' U), mem_interior_iff_mem_nhds.2 hW⟩⟩
  obtain ⟨ψ, hψφ, hψs, hψt, hψ⟩ :=
    hφ.exists_target_eq isOpen_ball (hrV.trans inter_subset_left)
  have hsrcUW : ∀ x ∈ ψ.source, x ∈ U ∧ x ∈ W := fun x hx => by
    rw [hψs] at hx
    have hx' := (hrV hx.2).2
    rw [mem_preimage, φ.left_inv hx.1] at hx'
    exact ⟨hx'.1, interior_subset hx'.2⟩
  have hOab : f ⁻¹' ψ.source ⊆ Ioo a b := fun s hs => hfU ▸ (hsrcUW _ hs).1
  have hO : f ⁻¹' ψ.source = Ioo a b ∩ g ⁻¹' (LinearMap.inl ℝ ℝ F' ⁻¹' ball (φ (f t)) r) := by
    ext s
    rw [hψs]
    refine ⟨fun hs => ⟨hOab (hψs ▸ hs), ?_⟩, fun hs => ⟨hsub hs.1, ?_⟩⟩
    · simpa [← hgφ s hs.1] using hs.2
    · simpa [hgφ s (hsub hs.1)] using hs.2
  have hψg : ∀ s ∈ f ⁻¹' ψ.source, ψ (f s) = (g s, 0) := fun s hs => by
    rw [hψφ]
    exact hgφ s (hsub (hOab hs))
  have hball : (LinearMap.inl ℝ ℝ F' ⁻¹' ball (φ (f t)) r).OrdConnected :=
    ((convex_ball _ _).linear_preimage _).ordConnected
  have hft : f t ∈ ψ.source := hψs ▸ ⟨hφt, mem_ball_self hr⟩
  refine ⟨ψ, f ⁻¹' ψ.source, g, hft, fun x hx => (hsrcUW x hx).2, hψt ▸ convex_ball _ _, hψ,
    ψ.open_source.preimage hfc, ?_, hft, image_preimage_eq_inter_range.symm, hψg,
    hmono.imp (·.mono hOab) (·.mono hOab), fun J => ψ.image_source_inter_image_eq hψg J⟩
  rw [hO]
  rcases hmono with hm | hm
  · obtain ⟨u, hu, hEq⟩ := hball.preimage_monotoneOn hm.monotoneOn
    exact hEq ▸ ordConnected_Ioo.inter hu
  · obtain ⟨u, hu, hEq⟩ := hball.preimage_antitoneOn hm.antitoneOn
    exact hEq ▸ ordConnected_Ioo.inter hu

end TauCeti.IsLocallyFlat

end
