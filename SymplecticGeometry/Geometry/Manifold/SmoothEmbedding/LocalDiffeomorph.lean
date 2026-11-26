/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Geometry.Manifold.SmoothEmbedding
import TauCeti.Geometry.Manifold.Immersion.Differential

/-!
# Injective local diffeomorphisms are smooth embeddings

A local diffeomorphism `g : M → N` has invertible differentials and is an open map. When it is
injective, it is therefore an open topological embedding
(`Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap`), and, when `M` and `N` have no
boundary and `N` has a finite-dimensional model, an immersion by Tau Ceti's
`ContMDiff.isImmersion_of_injective_mfderiv`. So it is a smooth embedding. The models of `M` and
`N` may differ. Tau Ceti's `Geometry/Manifold/SmoothEmbedding/LocalDiffeomorph.lean` and
`Geometry/Manifold/Immersion/LocalDiffeomorph.lean` treat local diffeomorphisms composed with
smooth embeddings and immersions.

## Main results

* `IsLocalDiffeomorph.isSmoothEmbedding`: an injective local diffeomorphism between boundaryless
  manifolds, with a finite-dimensional target model, is a smooth embedding.

## References

* M. Hirsch, *Differential Topology*, Springer GTM 33 (1976), Chapter 1, for immersions and
  embeddings.
-/

public section

open scoped Manifold ContDiff

variable {𝕜 : Type*} [RCLike 𝕜] {E E' H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [FiniteDimensional 𝕜 E'] [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E' G} [I.Boundaryless] [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N]
  {n : ℕ∞ω} [IsManifold I n M] [IsManifold J n N]

/-- **Injective local diffeomorphisms are smooth embeddings.** A `C^n` local diffeomorphism
`g : M → N`, `1 ≤ n`, that is injective is a smooth embedding, when `M` and `N` have no boundary
and `N` has a finite-dimensional model. -/
theorem IsLocalDiffeomorph.isSmoothEmbedding {g : M → N} (hg : IsLocalDiffeomorph I J n g)
    (hn : 1 ≤ n) (hinj : Function.Injective g) : Manifold.IsSmoothEmbedding I J n g := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  refine ⟨hg.contMDiff.isImmersion_of_injective_mfderiv hn fun x ↦ ?_,
    (Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap hg.contMDiff.continuous hinj
      hg.isOpenMap).isEmbedding⟩
  rw [← hg.mfderivToContinuousLinearEquiv_coe hn0 x]
  exact (hg.mfderivToContinuousLinearEquiv hn0 x).injective

end
