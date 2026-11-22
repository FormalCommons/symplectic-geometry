/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Topology.MetricSpace.Holder
import TauCeti.Analysis.Calculus.IteratedFDeriv.Basic

/-!
# Iterated derivatives of a continuous linear map plus a function

The iterated derivatives of positive order of a continuous linear map `L` are constant
(`ContinuousLinearMap.iteratedFDeriv_succ_eq`), so adding `L` to a differentiable function adds
them to its derivatives of positive order (`ContinuousLinearMap.iteratedFDeriv_succ_add_apply`)
and does not change their Hölder constants
(`ContinuousLinearMap.holderOnWith_iteratedFDeriv_succ_add_left_iff`).

These declarations are a part of Tau Ceti's file
`TauCeti/Analysis/Calculus/IteratedFDeriv/Basic.lean`, on its main branch, as of the commit
`0fef288e2f0539135f050168f1153e762b0189a8` (Tau Ceti's pull request #40860), and are not yet in
the pinned release. They keep their Tau Ceti names, namespaces, statements and proofs unchanged,
so that moving Tau Ceti past them deletes this file without renames.
-/

public section

open scoped NNReal Topology

namespace TauCeti

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The iterated derivatives of positive order of a continuous linear map are constant. -/
theorem _root_.ContinuousLinearMap.iteratedFDeriv_succ_eq (L : E →L[𝕜] F) (n : ℕ) (x y : E) :
    iteratedFDeriv 𝕜 (n + 1) L x = iteratedFDeriv 𝕜 (n + 1) L y := by
  have hL : fderiv 𝕜 L = fun _ ↦ L := funext fun _ ↦ L.fderiv
  rw [iteratedFDeriv_succ_eq_comp_right, iteratedFDeriv_succ_eq_comp_right, Function.comp_apply,
    Function.comp_apply, hL]
  rcases n with _ | n
  · simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply]
  · rw [iteratedFDeriv_succ_const, Pi.zero_apply, Pi.zero_apply]

/-- Where `f` is differentiable near `x`, the iterated derivatives of positive order of
`y ↦ L y + f y`, for a continuous linear map `L`, are those of `L` plus those of `f`. No higher
differentiability of `f` is needed, since `D (L + f) = L + D f` near `x` and `L` is constant. -/
theorem _root_.ContinuousLinearMap.iteratedFDeriv_succ_add_apply (L : E →L[𝕜] F) {f : E → F}
    {x : E} (hf : ∀ᶠ y in 𝓝 x, DifferentiableAt 𝕜 f y) (n : ℕ) :
    iteratedFDeriv 𝕜 (n + 1) (fun y ↦ L y + f y) x =
      iteratedFDeriv 𝕜 (n + 1) L x + iteratedFDeriv 𝕜 (n + 1) f x := by
  have hD : fderiv 𝕜 (fun y ↦ L y + f y) =ᶠ[𝓝 x] fun y ↦ fderiv 𝕜 f y + L :=
    hf.mono fun y hy ↦ by rw [fderiv_fun_add L.differentiableAt hy, L.fderiv, add_comm]
  have hL : fderiv 𝕜 L = fun _ ↦ L := funext fun _ ↦ L.fderiv
  simp only [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply,
    (hD.iteratedFDeriv 𝕜 n).eq_of_nhds, hL]
  rcases n with _ | n
  · simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply, map_add, add_comm]
  · rw [iteratedFDeriv_succ_add_const, iteratedFDeriv_succ_const, Pi.zero_apply,
      LinearIsometryEquiv.map_zero, zero_add]

/-- Adding a continuous linear map `L` to a function `f` that is differentiable near every point
of `s` does not change the Hölder constants on `s` of its derivatives of positive order. -/
theorem _root_.ContinuousLinearMap.holderOnWith_iteratedFDeriv_succ_add_left_iff {n : ℕ}
    (L : E →L[𝕜] F) {f : E → F} {C r : ℝ≥0} {s : Set E}
    (hf : ∀ x ∈ s, ∀ᶠ y in 𝓝 x, DifferentiableAt 𝕜 f y) :
    HolderOnWith C r (iteratedFDeriv 𝕜 (n + 1) (fun y ↦ L y + f y)) s ↔
      HolderOnWith C r (iteratedFDeriv 𝕜 (n + 1) f) s := by
  unfold HolderOnWith
  refine forall₂_congr fun x hx ↦ forall₂_congr fun y hy ↦ ?_
  rw [L.iteratedFDeriv_succ_add_apply (hf x hx), L.iteratedFDeriv_succ_add_apply (hf y hy),
    L.iteratedFDeriv_succ_eq n y x, edist_add_left]

end TauCeti

end
