/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Orientation.CoordinateBall
public import TauCeti.Geometry.Manifold.Orientation.Preserving
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Injective
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic

/-!
# Oriented charts on balls

On a smooth manifold `M` without boundary modelled on a nontrivial finite-dimensional real inner
product space `E`, with orientations of `E` and of `M`, every point `x` has, inside any
neighbourhood of it, a chart `e` of the maximal smooth atlas whose target is a ball about
`e x = 0` and which preserves orientation at every point of its source
(`TauCeti.Manifold.Orientation.exists_mem_maximalAtlas_isOrientationPreservingAt`).

The chart is the inverse of Tau Ceti's oriented coordinate ball
`TauCeti.Manifold.Orientation.exists_isOpenEmbedding_isLocalDiffeomorph_isOrientationPreservingAt`
restricted to a ball small enough to land in the neighbourhood. An injective local
diffeomorphism on the ball is a partial diffeomorphism onto its image
(`IsLocalDiffeomorphOn.partialDiffeomorphOfInjOn`), whose inverse is a local diffeomorphism at
every point, hence a chart of the maximal atlas
(`IsManifold.mem_maximalAtlas_iff_forall_isLocalDiffeomorphAt`), and preserves orientation
(`TauCeti.Manifold.Orientation.IsOrientationPreservingAt.partialDiffeomorph_symm`).

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 15.
-/

public section

open Set Topology
open scoped Manifold ContDiff

namespace TauCeti.Manifold.Orientation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {ι : Type*} [Fintype ι]

/-- **Oriented charts on balls.** If `E` is nontrivial, every point `x` of a smooth manifold `M`
without boundary modelled on `E` has, inside any neighbourhood `U` of `x`, a chart `e` of the
maximal smooth atlas with `e x = 0`, whose target is a ball `Metric.ball 0 r` and which preserves
given orientations of `M` and of `E` at every point of its source. -/
theorem exists_mem_maximalAtlas_isOrientationPreservingAt
    (oE : Manifold.Orientation 𝓘(ℝ, E) E ι) (oM : Manifold.Orientation 𝓘(ℝ, E) M ι) {x : M}
    {U : Set M} (hU : U ∈ 𝓝 x) :
    ∃ (e : OpenPartialHomeomorph M E) (r : ℝ), 0 < r ∧
      e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M ∧ x ∈ e.source ∧ e x = 0 ∧ e.source ⊆ U ∧
        e.target = Metric.ball 0 r ∧ ∀ y ∈ e.source, oM.IsOrientationPreservingAt oE e y := by
  have : Nonempty M := ⟨x⟩
  obtain ⟨f, hf0, hf, df, hfo⟩ :=
    exists_isOpenEmbedding_isLocalDiffeomorph_isOrientationPreservingAt oE oM x
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.1
    (hf.continuous.continuousAt.preimage_mem_nhds (hf0 ▸ hU : U ∈ 𝓝 (f 0)))
  let Φ := (df.isLocalDiffeomorphOn (Metric.ball 0 r)).partialDiffeomorphOfInjOn
    Metric.isOpen_ball hf.injective.injOn
  have hsrc : Φ.source = Metric.ball 0 r := by simp [Φ]
  have hcoe : ⇑Φ = f := by simp [Φ]
  have h0 : (0 : E) ∈ Φ.source := hsrc ▸ Metric.mem_ball_self hr
  have hesrc : Φ.symm.toOpenPartialHomeomorph.source = Φ.target := by simp
  refine ⟨Φ.symm.toOpenPartialHomeomorph, r, hr, ?_, ?_, ?_, ?_, by simpa using hsrc,
    fun y hy ↦ ?_⟩
  · rw [IsManifold.mem_maximalAtlas_iff_forall_isLocalDiffeomorphAt]
    intro y hy
    rw [PartialDiffeomorph.toFun'_toOpenPartialHomeomorph]
    exact PartialDiffeomorph.isLocalDiffeomorphAt _ _ _ Φ.symm (hesrc ▸ hy)
  · rw [hesrc, ← hf0, ← hcoe]
    exact Φ.map_source h0
  · rw [← hf0, ← hcoe]
    simpa using Φ.left_inv h0
  · rw [hesrc, ← Φ.image_source_eq_target, hsrc, hcoe]
    exact image_subset_iff.2 hrU
  · rw [hesrc] at hy
    simpa using (hcoe ▸ hfo _).partialDiffeomorph_symm hy (by simp)

end TauCeti.Manifold.Orientation
