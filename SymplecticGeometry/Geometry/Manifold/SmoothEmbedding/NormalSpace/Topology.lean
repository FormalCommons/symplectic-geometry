/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.Topology

/-!
# Continuity of normal-bundle maps for ambient maps that are `C¹` along the embedding

Let `f : M → N` and `g : M' → N'` be smooth embeddings, and `u : M → M'`, `v : N → N'` maps with
`v ∘ f = g ∘ u`. Tau Ceti's `TauCeti.SmoothEmbedding.normalBundleMap` is the map of intrinsic
normal bundles `ν f → ν g` that the differentials of `v` induce, and Tau Ceti's
`TauCeti.SmoothEmbedding.continuous_normalBundleMap` shows that it is continuous, for the
quotient topologies of these bundles, when `v` is `C¹` on all of `N`.

Only the differentials of `v` at the points `f x` enter the map, and this file shows that it is
continuous as soon as `v` is `C¹` at each of these points
(`TauCeti.SmoothEmbedding.continuous_normalBundleMap_of_contMDiffAt`). With
`ContMDiffAt.congr_of_eventuallyEq`, this covers an ambient map that agrees, near the image of
`f`, with a map that is `C¹` there.

The proof is that of Tau Ceti's `TauCeti.SmoothEmbedding.continuous_normalBundleMap`, with the
continuity of `v` and of its tangent map taken pointwise, at the points over the image of `f`,
through `ContMDiffAt.continuousAt` and `ContMDiffAt.continuousAt_tangentMap`.

## Main results

* `TauCeti.SmoothEmbedding.continuous_normalBundleMap_of_contMDiffAt`: the normal-bundle map of a
  commuting square is continuous when the ambient map is `C¹` at each point of the image of the
  source embedding.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 6 (normal bundles).
-/

public section

open Bundle Function
open scoped Manifold ContDiff

namespace TauCeti.SmoothEmbedding

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F H G M N K E' F' H' G' M' N' K' : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F G}
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold J 1 N]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  [TopologicalSpace H'] [TopologicalSpace G']
  {I' : ModelWithCorners 𝕜 E' H'} {J' : ModelWithCorners 𝕜 F' G'}
  [TopologicalSpace M'] [ChartedSpace H' M']
  [TopologicalSpace N'] [ChartedSpace G' N'] [IsManifold J' 1 N'] {n m : ℕ∞ω}

/-- For smooth embeddings `f : M → N` and `g : M' → N'` and maps `u : M → M'`, `v : N → N'` with
`v ∘ f = g ∘ u`, the induced map of intrinsic normal bundles is continuous as soon as `v` is `C¹`
at each point `f x` of the image of `f`. -/
theorem continuous_normalBundleMap_of_contMDiffAt
    (f : SmoothEmbedding I J n M N) (g : SmoothEmbedding I' J' m M' N')
    (hn : n ≠ 0) (hm : m ≠ 0) {u : M → M'} {v : N → N'}
    (hv : ∀ x, ContMDiffAt J J' 1 v (f x)) (h : v ∘ f = g ∘ u) :
    Continuous (f.normalBundleMap (K := K) (K' := K') g hn hm h) := by
  let T : TotalSpace F ((f : M → N) *ᵖ (TangentSpace J)) →
      TotalSpace F' ((g : M' → N') *ᵖ (TangentSpace J')) := fun p =>
    ⟨u p.proj, tangentSpaceCast J' (v (f p.proj)) (g (u p.proj))
      (mfderiv J J' v (f p.proj) p.snd)⟩
  have hT : Continuous T := by
    apply (inducing_pullbackTotalSpaceEmbedding F' (TangentSpace J')
      (g : M' → N')).continuous_iff.mpr
    have heq : pullbackTotalSpaceEmbedding g ∘ T =
        fun p => (u p.proj, tangentMap J J' v (Pullback.lift f p)) := by
      funext p
      -- The two tangent vectors have equal base points by the commuting square, and then
      -- `tangentSpaceCast` is the identity.
      simp only [Function.comp_apply, pullbackTotalSpaceEmbedding, T, tangentMap,
        Pullback.lift]
      congr 1
      apply TotalSpace.ext (congrFun h p.proj).symm
      rfl
    rw [heq]
    have hvf : Continuous (v ∘ f) := continuous_iff_continuousAt.2 fun x ↦
      (hv x).continuousAt.comp f.contMDiff.continuous.continuousAt
    have hu : Continuous u := g.isEmbedding.continuous_iff.2 (h ▸ hvf)
    refine (hu.comp (Pullback.continuous_proj F (TangentSpace J) f)).prodMk
      (continuous_iff_continuousAt.2 fun p ↦ ?_)
    exact (ContMDiffAt.continuousAt_tangentMap (x₀ := Pullback.lift f p) (hv p.proj)
      le_rfl).comp (Pullback.continuous_lift F (TangentSpace J) f).continuousAt
  rw [f.continuous_normalBundle_iff hn]
  convert (g.isQuotientMap_normalQuotientMap (K := K') hm).continuous.comp hT using 1
  funext p
  exact f.normalBundleMap_normalQuotientMap g hn hm h p

end TauCeti.SmoothEmbedding

end
