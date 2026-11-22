/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Add

/-!
# Strict derivatives of `y ↦ y + f y`

If `f` has a strict derivative of norm less than one at `x`, then `y ↦ y + f y` has an
invertible strict derivative there
(`HasStrictFDerivAt.exists_continuousLinearEquiv_id_add`).

These declarations are a part of Tau Ceti's file
`TauCeti/Analysis/Calculus/ContinuousLinearMapInverse.lean`, on its main branch, as of the commit
`0fef288e2f0539135f050168f1153e762b0189a8` (Tau Ceti's pull request #40860), and are not yet in
the pinned release. They keep their Tau Ceti names, namespaces, statements and proofs unchanged,
so that moving Tau Ceti past them deletes this file without renames.
-/

public section

open ContinuousLinearMap

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- A strict derivative of norm less than one is a small perturbation of the identity: if `f` has
strict derivative `f'` at `x` with `‖f'‖ < 1`, then `y ↦ y + f y` has an invertible strict
derivative at `x`, namely `1 + f'`. -/
theorem HasStrictFDerivAt.exists_continuousLinearEquiv_id_add [CompleteSpace E] {f : E → E}
    {f' : E →L[𝕜] E} {x : E} (hf : HasStrictFDerivAt f f' x) (hf' : ‖f'‖ < 1) :
    ∃ L : E ≃L[𝕜] E, HasStrictFDerivAt (fun y ↦ y + f y) (L : E →L[𝕜] E) x := by
  set L := ContinuousLinearEquiv.unitsEquiv 𝕜 E (Units.oneSub (-f') (by rwa [norm_neg]))
  have hL : (L : E →L[𝕜] E) = ContinuousLinearMap.id 𝕜 E + f' := by
    ext v
    simp [L, ContinuousLinearEquiv.unitsEquiv_apply]
  exact ⟨L, hL ▸ (hasStrictFDerivAt_id x).add hf⟩

end
