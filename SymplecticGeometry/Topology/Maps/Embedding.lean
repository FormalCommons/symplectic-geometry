/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.OpenPartialHomeomorph.Basic

/-!
# An inducing map cut out by a chart

Let `f : X → Y` be an inducing map and `e` a partial homeomorphism of `Y`. Suppose that
near `z₀`, a parametrization `g : Z → X` which is open at `z₀` is carried by `e ∘ f` to a map
`ι : Z → W` with a continuous left inverse. Then near `f (g z₀)`, the image of `f` is exactly the
set of points that `e` sends into the range of `ι`
(`Topology.IsInducing.exists_isOpen_inter_range_eq`). This is how a chart that straightens a
submanifold along a parametrization is shrunk until the submanifold is a slice of it.

The file also shows that the corestriction of an open embedding to a set containing its range is
an open embedding (`Topology.IsOpenEmbedding.codRestrict`), and that an embedding whose image of a
set `t` is closed maps each closed subset of `t` onto a closed set
(`Topology.IsEmbedding.isClosed_image_of_subset`).
-/

public section

open Set Filter Function
open scoped Topology

/-- The corestriction of an open embedding `f` to a set `s` containing its range is an open
embedding. -/
protected theorem Topology.IsOpenEmbedding.codRestrict {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} (hf : IsOpenEmbedding f) (s : Set Y) (h : ∀ x, f x ∈ s) :
    IsOpenEmbedding (codRestrict f s h) :=
  .of_isEmbedding_isOpenMap (hf.isEmbedding.codRestrict s h) (hf.isOpenMap.codRestrict h)

/-- If `e` is an embedding and `e '' t` is closed, then the image of every closed subset `s` of `t`
is closed. -/
theorem Topology.IsEmbedding.isClosed_image_of_subset {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {e : X → Y} (he : IsEmbedding e) {s t : Set X} (hst : s ⊆ t)
    (hs : IsClosed s) (ht : IsClosed (e '' t)) : IsClosed (e '' s) := by
  refine closure_subset_iff_isClosed.1 fun y hy ↦ ?_
  obtain ⟨x, -, rfl⟩ := ht.closure_subset_iff.2 (image_mono hst) hy
  refine mem_image_of_mem _ ?_
  rw [← hs.closure_eq, he.closure_eq_preimage_closure_image]
  exact hy

namespace Topology.IsInducing

variable {X Y Z W : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  [TopologicalSpace W]

/-- Let `f : X → Y` be an inducing map, `g : Z → X` a map that sends neighbourhoods of `z₀` to
neighbourhoods of `g z₀`, and `e` a partial homeomorphism of `Y` with `e (f (g z)) = ι z` for `z`
near `z₀`, where `ι` has a continuous left inverse. Then some open neighbourhood `U` of
`f (g z₀)` inside the source of `e` meets the image of `f` exactly where `e` takes values in the
range of `ι`. -/
theorem exists_isOpen_inter_range_eq {f : X → Y} (hf : IsInducing f) {g : Z → X} {z₀ : Z}
    (hg : 𝓝 (g z₀) ≤ map g (𝓝 z₀)) (e : OpenPartialHomeomorph Y W) {ι : Z → W} {π : W → Z}
    (hπ : Continuous π) (hπι : LeftInverse π ι)
    (he : ∀ᶠ z in 𝓝 z₀, f (g z) ∈ e.source ∧ e (f (g z)) = ι z) :
    ∃ U : Set Y, IsOpen U ∧ f (g z₀) ∈ U ∧ U ⊆ e.source ∧
      U ∩ range f = U ∩ e ⁻¹' range ι := by
  obtain ⟨B, hBsub, hBo, hz₀B⟩ := mem_nhds_iff.1 he
  -- Points of `X` near `g z₀` are values of `g` on `B`, and are cut out by an open `U₁ ⊆ Y`.
  obtain ⟨V, hVsub, hVo, hV⟩ := mem_nhds_iff.1 (hg (image_mem_map (hBo.mem_nhds hz₀B)))
  obtain ⟨U₁, hU₁o, hfU₁⟩ := hf.isOpen_iff.1 hVo
  have he₀ : e (f (g z₀)) = ι z₀ := (hBsub hz₀B).2
  refine ⟨U₁ ∩ (e.source ∩ e ⁻¹' (π ⁻¹' B)),
    hU₁o.inter (e.isOpen_inter_preimage (hBo.preimage hπ)),
    ⟨show g z₀ ∈ f ⁻¹' U₁ from hfU₁ ▸ hV, (hBsub hz₀B).1, by
      rw [mem_preimage, mem_preimage, he₀, hπι]; exact hz₀B⟩,
    fun x hx ↦ hx.2.1, ?_⟩
  ext x
  simp only [mem_inter_iff, mem_preimage, mem_range]
  constructor
  · -- A point `f q` of `U₁` has `q = g z` with `z ∈ B`, and then `e (f q) = ι z`.
    rintro ⟨hx, q, rfl⟩
    have hq : q ∈ V := hfU₁ ▸ hx.1
    obtain ⟨z, hz, rfl⟩ := hVsub hq
    exact ⟨hx, z, (hBsub hz).2.symm⟩
  · -- A point `x` with `e x = ι z` has `z = π (e x) ∈ B`, so `x = f (g z)`, as `e` is injective
    -- on its source.
    rintro ⟨hx, z, hz⟩
    have hzB : z ∈ B := by
      have h := hx.2.2
      rwa [← hz, hπι] at h
    exact ⟨hx, g z, e.injOn (hBsub hzB).1 hx.2.1 ((hBsub hzB).2.trans hz)⟩

end Topology.IsInducing

end
