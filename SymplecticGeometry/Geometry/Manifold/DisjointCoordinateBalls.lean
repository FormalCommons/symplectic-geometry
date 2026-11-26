/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.ConnectedSum.Sphere
import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.UnivBall
import TauCeti.Analysis.Normed.Module.Ball
import SymplecticGeometry.Analysis.Normed.Module.Ball.Homeomorph

/-!
# Pairwise disjoint coordinate balls inside a coordinate ball

Let `E` be a nonzero real inner product space and `e : E → M` a coordinate ball of a manifold
`M` modelled on `I`: an open embedding that is a `C^n` local diffeomorphism. For a vector
`v ≠ 0`, the balls of radius `‖v‖ / 2` about the points `j • v`, `j : ℕ`, are pairwise disjoint
(Tau Ceti's `TauCeti.pairwise_disjoint_ball_add_natCast_smul`). Composing `e` with Mathlib's
maps `OpenPartialHomeomorph.univBall` of `E` onto these balls gives infinitely many coordinate
balls of `M` with pairwise disjoint ranges, all inside the range of `e`.

Applied to Tau Ceti's coordinate ball `TauCeti.sphereBall v` of the unit sphere, whose range is
the complement of `v`, this gives infinitely many coordinate balls of the sphere with pairwise
disjoint ranges, none of which contains `v`. The balls `sphereBall v` themselves do not do this,
since the ranges of any two of them meet.

## Main results

* `Topology.IsOpenEmbedding.exists_pairwise_disjoint_range_subset_range`: a coordinate ball
  contains infinitely many coordinate balls with pairwise disjoint ranges.
* `SymplecticGeometry.exists_pairwise_disjoint_range_subset_compl_sphere`: the unit sphere has
  infinitely many coordinate balls with pairwise disjoint ranges that miss a given point.
-/

public section

open Set Metric Function Topology OpenPartialHomeomorph TauCeti
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace Topology.IsOpenEmbedding

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω} {e : E → M}

/-- Let `E` be a nonzero real inner product space, `n ≤ ∞`, and `e : E → M` an open embedding
that is a `C^n` local diffeomorphism. Then there are maps `b j : E → M`, for `j : ℕ`, each an open
embedding and a `C^n` local diffeomorphism, whose ranges are pairwise disjoint and contained in
the range of `e`. -/
theorem exists_pairwise_disjoint_range_subset_range [Nontrivial E] (he : IsOpenEmbedding e)
    (hd : IsLocalDiffeomorph 𝓘(ℝ, E) I n e) (hn : n ≤ ∞) :
    ∃ b : ℕ → E → M, (∀ j, IsOpenEmbedding (b j)) ∧
      (∀ j, IsLocalDiffeomorph 𝓘(ℝ, E) I n (b j)) ∧
      (∀ j, range (b j) ⊆ range e) ∧ Pairwise (Disjoint on fun j ↦ range (b j)) := by
  -- The balls of radius `‖v‖ / 2` about the points `j • v` are pairwise disjoint.
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  have hρ : 0 < ‖v‖ / 2 := by positivity
  refine ⟨fun j ↦ e ∘ univBall (0 + (j : ℝ) • v) (‖v‖ / 2),
    fun j ↦ he.comp ((univBall _ _).isOpenEmbedding (univBall_source _ _)),
    fun j x ↦ (isLocalDiffeomorph_univBall hn x).comp (hg := hd _),
    fun j ↦ range_comp_subset_range _ _, fun j k hjk ↦ ?_⟩
  simp only [onFun, range_comp, range_univBall _ hρ]
  exact (disjoint_image_iff he.injective).2 (pairwise_disjoint_ball_add_natCast_smul 0 v hjk)

end Topology.IsOpenEmbedding

namespace SymplecticGeometry

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] {n : ℕ} [NeZero n]
  [Fact (Module.finrank ℝ F = n + 1)]

/-- Let `F` be a real inner product space of dimension `n + 1`, with `n ≠ 0`, and `v` a point of
its unit sphere. For `m ≤ ∞` there are maps `b j` from `EuclideanSpace ℝ (Fin n)` to the sphere,
for `j : ℕ`, each an open embedding and a `C^m` local diffeomorphism, whose ranges are pairwise
disjoint and do not contain `v`. -/
theorem exists_pairwise_disjoint_range_subset_compl_sphere (v : sphere (0 : F) 1) {m : ℕ∞ω}
    (hm : m ≤ ∞) :
    ∃ b : ℕ → EuclideanSpace ℝ (Fin n) → sphere (0 : F) 1, (∀ j, IsOpenEmbedding (b j)) ∧
      (∀ j, IsLocalDiffeomorph (𝓡 n) (𝓡 n) m (b j)) ∧
      (∀ j, range (b j) ⊆ {v}ᶜ) ∧ Pairwise (Disjoint on fun j ↦ range (b j)) := by
  rw [← range_sphereBall (n := n) v]
  exact (isOpenEmbedding_sphereBall v).exists_pairwise_disjoint_range_subset_range
    (isLocalDiffeomorph_sphereBall v m) hm

end SymplecticGeometry

end
