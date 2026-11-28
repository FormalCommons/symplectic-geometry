/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothIsotopy.Orientation
import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.Neighborhood
import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.UnivBall
import TauCeti.Topology.MetricSpace.SeparatedBalls

/-!
# The disc theorem for embeddings of a closed ball

Let `M` be a connected, oriented, Hausdorff manifold without boundary, whose model is an inner
product space `E` over `ℝ` of finite dimension, and let `f, g : E → M` be smooth embeddings of
the closed ball `closedBall 0 r`: smooth on an open neighbourhood of the ball, injective on the
ball, with injective differential at each of its points, and orientation-preserving at its centre.
Then a compactly supported diffeotopy of `M` carries `f` to `g` on the ball
(`SymplecticGeometry.exists_diffeotopy_eqOn_closedBall_of_isOrientationPreservingAt`).

Tau Ceti proves this for embeddings of all of `E`, on any compact subset of `E`
(`TauCeti.SmoothEmbedding.exists_diffeotopy_eqOn_of_isOrientationPreservingAt`). Here the
embeddings of the ball are reduced to that case. The map `f` embeds some open neighbourhood of the
ball smoothly (the library's `TauCeti.exists_isOpen_isSmoothEmbedding_of_injOn`), which
contains a ball `ball 0 ρ` with `r < ρ`. Precomposed with Mathlib's diffeomorphism
`OpenPartialHomeomorph.univBall 0 ρ` of `E` onto that ball, it becomes a smooth embedding of `E`
(`Manifold.IsSmoothEmbedding.comp_univBall`), still orientation-preserving at `0`, since the
derivative of `univBall 0 ρ` at `0` is `ρ • id`. Tau Ceti's theorem, applied to the two
composites on the compact preimage of the closed ball, gives the diffeotopy.

The inner product is used only for the smoothness of `univBall`: the ball of a general norm need
not be a smooth domain.

## Main results

* `SymplecticGeometry.exists_diffeotopy_eqOn_closedBall_of_isOrientationPreservingAt`: the disc
  theorem for embeddings of a closed ball.

## References

* [M. W. Hirsch, *Differential Topology*][Hirsch1976], Chapter 8, Theorem 3.1.
* [R. S. Palais, *Extending diffeomorphisms*][Palais1960].
-/

public section

open Set Metric Function OpenPartialHomeomorph TauCeti
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace SymplecticGeometry

variable [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {ι : Type*} [Fintype ι]

/-- **The disc theorem for embeddings of a closed ball** (Palais). Let `M` be a preconnected,
Hausdorff manifold without boundary, whose model is an inner product space `E` over `ℝ` of finite
dimension, with an orientation `oM`, and let `o` be an orientation of `E`. Let `f` and `g` be
smooth on an open set `U` containing the closed ball `closedBall 0 r`, with `0 ≤ r`, injective on
that ball, with injective differential at each of its points, and preserving the orientations at
the centre `0`. Then there are a smooth diffeotopy `Φ` of `M`, starting at the identity, and a
compact set `K` outside which every `Φ t` is the identity, such that the final diffeomorphism of
`Φ` composed with `f` is `g` on the ball.

Milestone: *Disc theorem*. -/
theorem exists_diffeotopy_eqOn_closedBall_of_isOrientationPreservingAt [T2Space M]
    [PreconnectedSpace M] {r : ℝ} (hr : 0 ≤ r) {U : Set E} (hU : IsOpen U)
    (hrU : closedBall (0 : E) r ⊆ U) {f g : E → M}
    (hf : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ f U) (hg : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ g U)
    (hfi : InjOn f (closedBall 0 r)) (hgi : InjOn g (closedBall 0 r))
    (hfd : ∀ x ∈ closedBall (0 : E) r, Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f x))
    (hgd : ∀ x ∈ closedBall (0 : E) r, Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) g x))
    (o : Manifold.Orientation 𝓘(ℝ, E) E ι) (oM : Manifold.Orientation 𝓘(ℝ, E) M ι)
    (hfo : o.IsOrientationPreservingAt oM f 0) (hgo : o.IsOrientationPreservingAt oM g 0) :
    ∃ Φ : Diffeotopy 𝓘(ℝ, E) ∞ M, ∃ K : Set M, IsCompact K ∧ (∀ t, ∀ y ∉ K, Φ (t, y) = y) ∧
      EqOn (Φ.final ∘ f) g (closedBall 0 r) := by
  have hB := isCompact_closedBall (0 : E) r
  -- Both maps are smooth embeddings of open neighbourhoods of the ball.
  obtain ⟨Vf, hBVf, -, hVf⟩ := exists_isOpen_isSmoothEmbedding_of_injOn hU hf hB hrU hfi hfd
  obtain ⟨Vg, hBVg, -, hVg⟩ := exists_isOpen_isSmoothEmbedding_of_injOn hU hg hB hrU hgi hgd
  -- A slightly larger open ball lies in both neighbourhoods.
  obtain ⟨ρ, hrρ, hρ⟩ := (Vf ⊓ Vg).isOpen.exists_gt_closedBall_subset (x := (0 : E))
    (subset_inter hBVf hBVg)
  have hρ0 : 0 < ρ := hr.trans_lt hrρ
  have hball : ball (0 : E) ρ ⊆ Vf ⊓ Vg := ball_subset_closedBall.trans hρ
  -- Precomposed with `univBall 0 ρ`, they are smooth embeddings of `E`.
  let F := SmoothEmbedding.ofIsSmoothEmbedding _
    (hVf.comp_univBall hρ0 (hball.trans inter_subset_left) le_rfl)
  let G := SmoothEmbedding.ofIsSmoothEmbedding _
    (hVg.comp_univBall hρ0 (hball.trans inter_subset_right) le_rfl)
  -- `univBall 0 ρ` fixes `0` and has derivative `ρ • id` there, so it preserves `o` at `0`.
  have hψo : o.IsOrientationPreservingAt o (univBall (0 : E) ρ) 0 :=
    isOrientationPreservingAt_univBall_zero hρ0 o
  have hFo : o.IsOrientationPreservingAt oM F 0 := by
    simpa [F] using (univBall_apply_zero (0 : E) ρ ▸ hfo).comp hψo
  have hGo : o.IsOrientationPreservingAt oM G 0 := by
    simpa [G] using (univBall_apply_zero (0 : E) ρ ▸ hgo).comp hψo
  -- Apply Tau Ceti's theorem on the preimage of the closed ball.
  have hBρ : closedBall (0 : E) r ⊆ (univBall (0 : E) ρ).target :=
    univBall_target (0 : E) hρ0 ▸ closedBall_subset_ball hrρ
  obtain ⟨Φ, K, hK, hΦK, hΦ⟩ := F.exists_diffeotopy_eqOn_of_isOrientationPreservingAt G o oM
    hFo hGo (hB.image_of_continuousOn ((continuousOn_univBall_symm 0 ρ).mono
      (closedBall_subset_ball hrρ)))
  refine ⟨Φ, K, hK, hΦK, fun x hx ↦ ?_⟩
  have h := hΦ (mem_image_of_mem _ hx)
  simp only [comp_apply, F, G, SmoothEmbedding.coe_ofIsSmoothEmbedding,
    (univBall (0 : E) ρ).right_inv (hBρ hx)] at h
  exact h

end SymplecticGeometry

end
