/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.Topology

/-!
# Continuity of maps out of the intrinsic normal bundle

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

For a family `g x : T_(f x) N → E₂ x` of continuous linear maps whose kernels are the tangent
ranges of `f`, Tau Ceti's `Manifold.IsImmersion.normalSpaceEquivOfKer` gives isomorphisms of the
normal spaces with the fibres `E₂ x`. They form a continuous map on total spaces, for the
quotient topology, as soon as `⟨x, v⟩ ↦ ⟨x, g x v⟩` is continuous on the pulled-back tangent
bundle (`TauCeti.SmoothEmbedding.continuous_normalSpaceEquivOfKer`). This needs no bundle
structure on the normal bundle; its proof is that of Tau Ceti's
`TauCeti.SmoothEmbedding.contMDiff_normalSpaceEquivOfKer`, with continuity in place of
smoothness.

## Main results

* `TauCeti.SmoothEmbedding.continuous_normalBundleMap_of_contMDiffAt`: the normal-bundle map of a
  commuting square is continuous when the ambient map is `C¹` at each point of the image of the
  source embedding.
* `TauCeti.SmoothEmbedding.continuous_normalSpaceEquivOfKer`: the isomorphisms
  `Manifold.IsImmersion.normalSpaceEquivOfKer` of a family of maps with kernels the tangent ranges
  form a continuous map on total spaces when the family is continuous on the pulled-back tangent
  bundle.

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

section KerEquiv

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F] {W : Type*} {E₂ : M → Type*}
  [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)] [∀ x, FiniteDimensional 𝕜 (E₂ x)]
  [∀ x, TopologicalSpace (E₂ x)] [∀ x, IsTopologicalAddGroup (E₂ x)]
  [∀ x, ContinuousSMul 𝕜 (E₂ x)] [∀ x, T2Space (E₂ x)] [TopologicalSpace (TotalSpace W E₂)]

/-- For a smooth embedding `f` and a family of continuous linear maps
`g x : T_(f x) N → E₂ x` whose kernels are the tangent ranges of `f`, if
`⟨x, v⟩ ↦ ⟨x, g x v⟩` is continuous on the pulled-back ambient tangent bundle, then so is the
induced map `⟨x, [v]⟩ ↦ ⟨x, g x v⟩` from the normal bundle of `f`, with its quotient topology,
to `E₂`. The label `K` of the normal total space is arbitrary, and no bundle structure on the
normal bundle is needed. -/
theorem continuous_normalSpaceEquivOfKer (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (g : ∀ x, TangentSpace J (f x) →L[𝕜] E₂ x)
    (hg : ∀ x v, g x v = 0 ↔ v ∈ f.isImmersion.tangentRange x hn)
    (hgdim : ∀ x, Module.finrank 𝕜 (f.isImmersion.NormalSpace x hn) = Module.finrank 𝕜 (E₂ x))
    (hgs : Continuous fun p : TotalSpace F ((f : M → N) *ᵖ (TangentSpace J)) ↦
      TotalSpace.mk' W (E := E₂) p.proj (g p.proj p.snd)) :
    Continuous fun p : TotalSpace K (fun x ↦ f.isImmersion.NormalSpace x hn) ↦
      TotalSpace.mk' W (E := E₂) p.proj
        (f.isImmersion.normalSpaceEquivOfKer p.proj hn (g p.proj) (hg p.proj) (hgdim p.proj)
          p.snd) := by
  rw [f.continuous_normalBundle_iff hn]
  refine hgs.congr fun ⟨x, v⟩ ↦ ?_
  rw [Function.comp_apply, normalQuotientMap_apply]
  exact congrArg (TotalSpace.mk' W x)
    (f.isImmersion.normalSpaceEquivOfKer_normalClass x hn (g x) (hg x) (hgdim x) v).symm

end KerEquiv

end TauCeti.SmoothEmbedding

end
