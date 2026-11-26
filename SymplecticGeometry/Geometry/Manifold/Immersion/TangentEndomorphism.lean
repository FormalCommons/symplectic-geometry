/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Normed.Module.ContinuousInverse
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import Mathlib.Geometry.Manifold.VectorBundle.Hom
import TauCeti.Geometry.Manifold.ContMDiff.LeftInverse
import TauCeti.Topology.VectorBundle.Coordinates
import SymplecticGeometry.Topology.FiberBundle.Basic

/-!
# Endomorphism fields related through a split-injective differential

Let `f : M → N` be `C^n` near `x₀`, with a differential at `x₀` that has a continuous linear left
inverse, and let `A x` be an endomorphism of `T_x M` and `B x` one of `T_{f x} N` such that
`df_x ∘ A x = B x ∘ df_x` near `x₀`. If `B` is `C^m` at `x₀` as a section along `f`, with
`m + 1 ≤ n`, then `A` is `C^m` at `x₀` as a section of the endomorphism bundle of `TM`
(`ContMDiffAt.tangentEnd_of_mfderiv`). No regularity of `A` is assumed in advance.

In tangent coordinates the differential is a `C^m` family of split injections, so post-composing
with it is a `C^m` family of split injections between spaces of operators, and Tau Ceti's
`ContMDiffAt.of_clm_apply` tests the regularity of `A` after it. The proof adapts Tau Ceti's
`ContMDiffAt.vectorField_of_mfderiv`, which treats vector fields, to endomorphism fields.

## Main results

* `ContMDiffAt.tangentEnd_of_mfderiv`: an endomorphism field of `TM` related through a
  split-injective differential to a `C^m` endomorphism field along `f` is `C^m`.
* `ContMDiff.tangentEnd_of_mfderiv`: its global form.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Springer GTM 218 (2013),
  Chapter 8 (vector fields related along an immersion).
-/

public section

open Bundle Filter ContinuousLinearMap
open scoped Manifold ContDiff Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners 𝕜 F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  [IsManifold I 1 M] [IsManifold J 1 N]
  {n m : ℕ∞ω} {f : M → N} {x₀ : M}

/-- An endomorphism field `A` of `TM` is `C^m` at `x₀` if `df ∘ A = B ∘ df` near `x₀` for an
endomorphism field `B` of `TN` along `f` that is `C^m` at `x₀`, provided `f` is `C^n` at `x₀`,
`m + 1 ≤ n`, and the differential of `f` at `x₀` has a continuous linear left inverse. -/
theorem ContMDiffAt.tangentEnd_of_mfderiv (hf : ContMDiffAt I J n f x₀) (hmn : m + 1 ≤ n)
    (hinj : (mfderiv I J f x₀).HasLeftInverse)
    {A : Π x : M, TangentSpace I x →L[𝕜] TangentSpace I x}
    {B : Π x : M, TangentSpace J (f x) →L[𝕜] TangentSpace J (f x)}
    (hB : ContMDiffAt I (J.prod 𝓘(𝕜, F →L[𝕜] F)) m
      (fun x ↦ TotalSpace.mk' (F →L[𝕜] F)
        (E := fun y : N ↦ TangentSpace J y →L[𝕜] TangentSpace J y) (f x) (B x)) x₀)
    (hAB : ∀ᶠ x in 𝓝 x₀, mfderiv I J f x ∘L A x = B x ∘L mfderiv I J f x) :
    ContMDiffAt I (I.prod 𝓘(𝕜, E →L[𝕜] E)) m
      (fun x ↦ TotalSpace.mk' (E →L[𝕜] E)
        (E := fun x : M ↦ TangentSpace I x →L[𝕜] TangentSpace I x) x (A x)) x₀ := by
  -- In tangent coordinates, the differential is a `C^m` family `D` of split injections.
  have hD := hf.mfderiv_const hmn
  have hx := FiberBundle.mem_baseSet_trivializationAt' (F := E) (E := TangentSpace I) x₀
  have hy := FiberBundle.mem_baseSet_trivializationAt' (F := F) (E := TangentSpace J) (f x₀)
  obtain ⟨P, hP⟩ : (inTangentCoordinates I J id f (mfderiv I J f) x₀ x₀).HasLeftInverse := by
    rw [inTangentCoordinates, id_eq, hasLeftInverse_inCoordinates_iff hx hy]
    exact hinj
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  -- Post-composition with `D x` is a `C^m` family of split injections between operator spaces.
  have hC : ContMDiffAt I 𝓘(𝕜, (E →L[𝕜] E) →L[𝕜] E →L[𝕜] F) m
      (fun x ↦ (inTangentCoordinates I J id f (mfderiv I J f) x₀ x).postcomp E) x₀ :=
    hD.clm_postcomp
  refine ContMDiffAt.of_clm_apply ?_ hC
    ⟨P.postcomp E, fun T ↦ ContinuousLinearMap.ext fun v ↦ hP (T v)⟩
  refine (((contMDiffAt_hom_bundle _).1 hB).2.clm_comp hD).congr_of_eventuallyEq ?_
  have hsrc := (trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds hx
  have htgt := hf.continuousAt.eventually_mem_baseSet_trivializationAt F (TangentSpace J)
  -- In coordinates, `D ∘ A = B ∘ D` near `x₀`, read off the relation `df ∘ A = B ∘ df`.
  filter_upwards [hsrc, htgt, hAB] with x hx' hy' hx''
  simp only [postcomp_apply, inTangentCoordinates, id_eq]
  rw [← inCoordinates_comp _ _ hx', hx'', inCoordinates_comp _ _ hy']

/-- An endomorphism field `A` of `TM` is `C^m` if `df ∘ A = B ∘ df` for a `C^m` endomorphism
field `B` of `TN` along `f`, provided `f` is `C^n`, `m + 1 ≤ n`, and every differential of `f`
has a continuous linear left inverse. -/
theorem ContMDiff.tangentEnd_of_mfderiv (hf : ContMDiff I J n f) (hmn : m + 1 ≤ n)
    (hinj : ∀ x, (mfderiv I J f x).HasLeftInverse)
    {A : Π x : M, TangentSpace I x →L[𝕜] TangentSpace I x}
    {B : Π x : M, TangentSpace J (f x) →L[𝕜] TangentSpace J (f x)}
    (hB : ContMDiff I (J.prod 𝓘(𝕜, F →L[𝕜] F)) m
      (fun x ↦ TotalSpace.mk' (F →L[𝕜] F)
        (E := fun y : N ↦ TangentSpace J y →L[𝕜] TangentSpace J y) (f x) (B x)))
    (hAB : ∀ x, mfderiv I J f x ∘L A x = B x ∘L mfderiv I J f x) :
    ContMDiff I (I.prod 𝓘(𝕜, E →L[𝕜] E)) m
      (fun x ↦ TotalSpace.mk' (E →L[𝕜] E)
        (E := fun x : M ↦ TangentSpace I x →L[𝕜] TangentSpace I x) x (A x)) := fun x ↦
  (hf x).tangentEnd_of_mfderiv hmn (hinj x) (hB x) (.of_forall hAB)
