/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Holder.Iterated
import TauCeti.Topology.MetricSpace.Holder

/-!
# Hölder continuity of `C^{k,α}` maps, and the supported `C^{k,α}` subspace

For `α ≤ 1`, an element of `TauCeti.CkHolderSpace k α E F` is itself globally `α`-Hölder
(`TauCeti.CkHolderSpace.holderWith`). The subspace `TauCeti.supportedCkHolderSubmodule` of
elements vanishing off a set is closed (`TauCeti.isClosed_supportedCkHolderSubmodule`), hence
complete when `F` is, and its elements have compact support when the set is compact
(`TauCeti.hasCompactSupport_of_mem_supportedCkHolderSubmodule`).

These declarations are a part of Tau Ceti's file
`TauCeti/Analysis/Holder/Iterated.lean`, on its main branch, as of the commit
`0fef288e2f0539135f050168f1153e762b0189a8` (Tau Ceti's pull request #40860), and are not yet in
the pinned release. They keep their Tau Ceti names, namespaces, statements and proofs unchanged,
so that moving Tau Ceti past them deletes this file without renames.

## References

D. Gilbarg and N. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
Section 4.1; A. Lunardi, *Analytic Semigroups and Optimal Regularity in Parabolic Problems*,
Chapter 0.
-/

public section

namespace TauCeti

open scoped NNReal

universe u v

namespace CkHolderSpace

variable {k : ℕ} {α : ℝ≥0} {E : Type u} {F : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A bounded `C^{k,α}` map is itself globally `α`-Hölder, with constant `3 ‖f‖`, when `α ≤ 1`. -/
theorem holderWith (f : CkHolderSpace k α E F) (hα : α ≤ 1) : HolderWith (3 * ‖f‖₊) α f := by
  have h := f.holderWith_iteratedFDeriv_of_le hα (Nat.zero_le k)
  rw [iteratedFDeriv_zero_eq_comp] at h
  exact (continuousMultilinearCurryFin0 ℝ E F).symm.isometry.holderWith_comp_iff.mp h

end CkHolderSpace

/-- An element of the supported Hölder submodule of a compact set has compact support. -/
theorem hasCompactSupport_of_mem_supportedCkHolderSubmodule {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {k : ℕ} {α : ℝ≥0} {s : Set E} {f : CkHolderSpace k α E F} (hs : IsCompact s)
    (hf : f ∈ supportedCkHolderSubmodule k α s) : HasCompactSupport f :=
  HasCompactSupport.of_support_subset_isCompact hs
    (support_subset_of_mem_supportedCkHolderSubmodule hf)

/-- The supported `C^{k,α}` subspace is closed, as an intersection of kernels of evaluations. -/
theorem isClosed_supportedCkHolderSubmodule {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (k : ℕ) (α : ℝ≥0) (s : Set E) :
    IsClosed (supportedCkHolderSubmodule (F := F) k α s : Set (CkHolderSpace k α E F)) := by
  have h : (supportedCkHolderSubmodule (F := F) k α s : Set (CkHolderSpace k α E F)) =
      ⋂ x ∈ sᶜ, (fun f ↦ CkHolderSpace.toBoundedContinuousFunctionCLM f x) ⁻¹' {0} := by
    ext f
    simp
  rw [h]
  exact isClosed_biInter fun x _ ↦ isClosed_singleton.preimage
    ((continuous_eval_const x).comp (ContinuousLinearMap.continuous _))

/-- The supported `C^{k,α}` subspace is a Banach space when the codomain is. -/
instance instCompleteSpaceSupportedCkHolderSubmodule {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (k : ℕ) (α : ℝ≥0) (s : Set E) :
    CompleteSpace (supportedCkHolderSubmodule (F := F) k α s) :=
  (isClosed_supportedCkHolderSubmodule k α s).completeSpace_coe

end TauCeti

end
