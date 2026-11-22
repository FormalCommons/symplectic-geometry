/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorField.Pullback
public import SymplecticGeometry.Geometry.Manifold.Immersion.Chart
public import TauCeti.Geometry.Manifold.VectorField.Immersion

/-!
# Extending tangent vectors of an immersion to related vector fields

Let `f : M → N` be a `C^n` immersion at `x`. Read in its normal-form charts `φ` on `M` and `ψ`
on `N`, `f` is the inclusion `u ↦ L (u, 0)` of `E` into `E''`, through a linear equivalence
`L : E × F ≃ E''`; so `dψ ∘ df = L (·, 0) ∘ dφ` on the source of `φ`
(`Manifold.IsImmersionAtOfComplement.mfderiv_extend_comp_mfderiv`, in
`SymplecticGeometry.Geometry.Manifold.Immersion.Chart`).

Hence the constant field `L (a, 0)` of `E''`, pulled back to `N` by `ψ`, is a `C^m` vector field
on `N` (for `m + 1 ≤ n`) whose values at the points `f z`, `z` near `x`, are tangent to `f`. With
`a = dφ_x v`, it takes the value `df_x v` at `f x`
(`Manifold.IsImmersionAtOfComplement.exists_vectorField_eventually_mem_range_mfderiv`). Tau Ceti's
`ContMDiffAt.exists_vectorField_mfderiv_eventuallyEq` lifts it to a field on `M` that it is
related to near `x`. So every tangent vector `v` at `x` is the value of a `C^m` vector field on
`M` that is `f`-related near `x` to a `C^m` vector field on `N`
(`Manifold.IsImmersionAt.exists_vectorField_mfderiv_eventuallyEq`). This is what naturality
statements for tensors built from Lie brackets, such as the Nijenhuis tensor, need along an
immersion.

## Main results

* `Manifold.IsImmersionAtOfComplement.exists_vectorField_eventually_mem_range_mfderiv`: an
  ambient `C^m` vector field, tangent to `f` near `x`, through a given tangent image at `f x`.
* `Manifold.IsImmersionAt.exists_vectorField_mfderiv_eventuallyEq`: every tangent vector at `x`
  is the value of a `C^m` field that is related near `x` to a `C^m` field on the target.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Springer GTM 218 (2013),
  Chapter 4 (the rank theorem) and Chapter 8 (vector fields tangent to submanifolds).
-/

public section

noncomputable section

open Set Function Filter Manifold VectorField
open scoped ContDiff Manifold Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners 𝕜 E'' G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {n m : WithTop ℕ∞} {f : M → N} {x : M}

namespace Manifold.IsImmersionAtOfComplement

variable (h : IsImmersionAtOfComplement F I J n f x)
include h

/-- **Tangent extensions.** Let `f` be a `C^n` immersion at `x` and `m + 1 ≤ n`. Every tangent
image `df_x v` is the value at `f x` of a vector field `V` on `N` that is `C^m` at `f x` and
tangent to `f` near `x`: `V (f z)` lies in the range of `df_z` for `z` near `x`. -/
theorem exists_vectorField_eventually_mem_range_mfderiv [IsManifold J 1 N] [CompleteSpace E'']
    (hmn : m + 1 ≤ n) (v : TangentSpace I x) :
    ∃ V : Π y : N, TangentSpace J y, ContMDiffAt J J.tangent m (T% V) (f x) ∧
      (∀ᶠ z in 𝓝 x, V (f z) ∈ LinearMap.range (mfderiv I J f z).toLinearMap) ∧
      V (f x) = mfderiv I J f x v := by
  have hn : n ≠ 0 := fun h0 ↦ by simp [h0] at hmn
  have h1 : (1 : WithTop ℕ∞) ≤ n := ENat.one_le_iff_ne_zero_withTop.2 hn
  have hψ := IsManifold.maximalAtlas_subset_of_le h1 h.codChart_mem_maximalAtlas
  have hφ := IsManifold.maximalAtlas_subset_of_le h1 h.domChart_mem_maximalAtlas
  set ψ := h.codChart.extend J
  set φ := h.domChart.extend I
  set A := (h.equiv : E × F →L[𝕜] E'').comp (ContinuousLinearMap.inl 𝕜 E F)
  set c : E'' := A (mfderiv I 𝓘(𝕜, E) φ x v)
  set V : Π y : N, TangentSpace J y :=
    mpullback J 𝓘(𝕜, E'') ψ (fun _ ↦ c : Π w : E'', TangentSpace 𝓘(𝕜, E'') w)
  -- `V (f z)` is the tangent image of the vector of `M` that `φ` reads as `dφ_x v`.
  have hV (z : M) (hz : z ∈ h.domChart.source) :
      V (f z) = mfderiv I J f z ((mfderiv I 𝓘(𝕜, E) φ z).inverse (mfderiv I 𝓘(𝕜, E) φ x v)) := by
    have hψz := isInvertible_mfderiv_extend hψ (h.source_subset_preimage_source hz)
    have hφz := isInvertible_mfderiv_extend hφ hz
    set w := (mfderiv I 𝓘(𝕜, E) φ z).inverse (mfderiv I 𝓘(𝕜, E) φ x v)
    have hcomp : mfderiv J 𝓘(𝕜, E'') ψ (f z) (mfderiv I J f z w) = c := by
      have := DFunLike.congr_fun (h.mfderiv_extend_comp_mfderiv hn hz) w
      -- `ContinuousLinearMap.comp_apply` does not rewrite the inner composite, whose source is
      -- the tangent space `TangentSpace I z` rather than `E`; it holds by definition.
      rw [ContinuousLinearMap.comp_apply] at this
      exact this.trans (congrArg A (hφz.self_apply_inverse _))
    refine (VectorField.mpullback_apply (I := J) (I' := 𝓘(𝕜, E'')) (f := ψ) (V := fun _ ↦ c)
      (x := f z)).trans ?_
    rw [← hcomp, hψz.inverse_apply_self]
  refine ⟨V, ?_, ?_, ?_⟩
  · exact ContMDiffAt.mpullback_vectorField_preimage
      (contMDiffAt_vectorSpace_iff_contDiffAt.2 contDiffAt_const)
      (h.codChart.contMDiffAt_extend h.codChart_mem_maximalAtlas h.mem_codChart_source)
      (isInvertible_mfderiv_extend hψ h.mem_codChart_source) hmn
  · filter_upwards [h.domChart.open_source.mem_nhds h.mem_domChart_source] with z hz
    exact ⟨_, (hV z hz).symm⟩
  · rw [hV x h.mem_domChart_source,
      (isInvertible_mfderiv_extend hφ h.mem_domChart_source).inverse_apply_self]

end Manifold.IsImmersionAtOfComplement

namespace Manifold.IsImmersionAt

variable [CompleteSpace E] [CompleteSpace E''] [IsManifold I 1 M] [IsManifold J 1 N]

/-- **Related extensions of a tangent vector.** Let `f` be a `C^n` immersion at `x` and
`m + 1 ≤ n`. Every tangent vector `v` at `x` is the value at `x` of a vector field `X` on `M`,
`C^m` at `x`, that is `f`-related near `x` to a vector field `V` on `N`, `C^m` at `f x`:
`df_z (X z) = V (f z)` for `z` near `x`. -/
theorem exists_vectorField_mfderiv_eventuallyEq (h : IsImmersionAt I J n f x) (hmn : m + 1 ≤ n)
    (v : TangentSpace I x) :
    ∃ (X : Π z : M, TangentSpace I z) (V : Π y : N, TangentSpace J y),
      ContMDiffAt I I.tangent m (T% X) x ∧ ContMDiffAt J J.tangent m (T% V) (f x) ∧
        X x = v ∧ ∀ᶠ z in 𝓝 x, mfderiv I J f z (X z) = V (f z) := by
  have hn : n ≠ 0 := fun h0 ↦ by simp [h0] at hmn
  obtain ⟨V, hV, htan, hVx⟩ :=
    h.isImmersionAtOfComplement_complement.exists_vectorField_eventually_mem_range_mfderiv hmn v
  have hinj := isDiffImmersionAt_iff.mp (h.isDiffImmersionAt hn)
  obtain ⟨X, hX, hXV⟩ := h.contMDiffAt.exists_vectorField_mfderiv_eventuallyEq hmn hinj hV htan
  exact ⟨X, V, hX, hV, h.mfderiv_injective hn (hXV.self_of_nhds.trans hVx), hXV⟩

end Manifold.IsImmersionAt
