/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Operator.Fredholm.Basic
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Index
import TauCeti.Analysis.Fredholm.SemiFredholm

/-!
# Fredholm operators: surjectivity from the index, and connected families

Two general facts about Fredholm operators.

## Main results

* `ContinuousLinearMap.surjective_iff_index_eq_finrank_ker`: a continuous linear map with a
  finite-dimensional cokernel is onto exactly when its index is the dimension of its kernel. One
  direction is Tau Ceti's `ContinuousLinearMap.index_of_surjective`.
* `ContinuousOn.isFredholm_of_isPreconnected_of_continuousLinearEquiv`: Tau Ceti's
  `ContinuousOn.isFredholm_of_isPreconnected`, for operators into a normed space that is only
  isomorphic to a Hilbert space. Along a preconnected family of operators with closed range and
  finite-dimensional kernel, Fredholmness spreads from one member to all of them.
-/

public section

namespace ContinuousLinearMap

open Module

/-- A continuous linear map with a finite-dimensional cokernel is onto if and only if its index
equals the dimension of its kernel. -/
theorem surjective_iff_index_eq_finrank_ker {𝕜 E F : Type*} [DivisionRing 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
    [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] (T : E →L[𝕜] F)
    [FiniteDimensional 𝕜 (F ⧸ T.range)] :
    Function.Surjective T ↔ T.index = (finrank 𝕜 T.ker : ℤ) := by
  refine ⟨T.index_of_surjective, fun h ↦ ?_⟩
  have h0 : finrank 𝕜 (F ⧸ T.range) = 0 := by
    rw [index_eq_finrank_sub] at h
    omega
  rw [← coe_coe, ← LinearMap.range_eq_top, ← Submodule.Quotient.subsingleton_iff]
  exact finrank_zero_iff.1 h0

/-- A Fredholm operator whose index equals the dimension of its kernel is onto. -/
theorem IsFredholm.surjective_of_index_eq_finrank_ker {𝕜 E F : Type*}
    [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
    [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] {T : E →L[𝕜] F}
    (hT : T.IsFredholm) (h : T.index = (finrank 𝕜 T.ker : ℤ)) : Function.Surjective T :=
  have := hT.finite_coker
  T.surjective_iff_index_eq_finrank_ker.2 h

end ContinuousLinearMap

open ContinuousLinearMap in
/-- **Fredholmness along a connected family, into a space isomorphic to a Hilbert space.** Let
`T x` be operators from a Banach space `E` to a normed space `F` isomorphic to a Hilbert space,
with closed range and finite-dimensional kernel, depending continuously on `x` in a preconnected
set `s`. If one member `T x₀` is Fredholm, then every member is. -/
theorem ContinuousOn.isFredholm_of_isPreconnected_of_continuousLinearEquiv
    {𝕜 E F H X : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H] [TopologicalSpace X]
    (φ : F ≃L[𝕜] H) {s : Set X} {T : X → E →L[𝕜] F} (hT : ContinuousOn T s)
    (hker : ∀ x ∈ s, FiniteDimensional 𝕜 (T x).ker)
    (hrange : ∀ x ∈ s, IsClosed ((T x).range : Set F)) (hs : IsPreconnected s) {x₀ x : X}
    (hx₀ : x₀ ∈ s) (h₀ : IsFredholm (T x₀)) (hx : x ∈ s) : IsFredholm (T x) := by
  refine (isFredholm_equiv_comp (f' := φ)).1 <|
    (continuousOn_const.clm_comp hT).isFredholm_of_isPreconnected
      (fun y hy ↦ ?_) (fun y hy ↦ ?_) hs hx₀ (isFredholm_equiv_comp (f' := φ).2 h₀) hx
  · have : ((φ : F →L[𝕜] H) ∘L T y).ker = (T y).ker := Submodule.ext fun w ↦ by simp
    exact this ▸ hker y hy
  · have : (((φ : F →L[𝕜] H) ∘L T y).range : Set H) = φ '' (T y).range := by
      rw [LinearMap.coe_range, LinearMap.coe_range, coe_coe, coe_coe, coe_comp,
        ContinuousLinearEquiv.coe_coe, Set.range_comp]
    exact this ▸ φ.toHomeomorph.isClosedMap _ (hrange y hy)
