/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Pompeiu.Holder.Higher
import SymplecticGeometry.Analysis.Holder.Iterated

/-!
# The Cauchy transform of supported `C^{k,α}` data

The Cauchy transform of `C^{k,α}` data vanishing off a compact set is globally `C^{k+1}`
(`TauCeti.contDiff_cauchyTransform_of_mem_supportedCkHolderSubmodule`).

These declarations are a part of Tau Ceti's file
`TauCeti/Analysis/Complex/Pompeiu/Holder/Higher.lean`, on its main branch, as of the commit
`0fef288e2f0539135f050168f1153e762b0189a8` (Tau Ceti's pull request #40860), and are not yet in
the pinned release. They keep their Tau Ceti names, namespaces, statements and proofs unchanged,
so that moving Tau Ceti past them deletes this file without renames.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, Appendix B.
* D. Gilbarg and N. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Lemma 4.4.
-/

public section

open scoped NNReal

namespace TauCeti

section Operator

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F]
  [IsScalarTower ℝ ℂ F] [FiniteDimensional ℂ F] {k : ℕ} {α : ℝ≥0}

/-- The Cauchy transform of `C^{k,α}` data vanishing off a compact set is globally `C^{k+1}`. -/
theorem contDiff_cauchyTransform_of_mem_supportedCkHolderSubmodule (hα : 0 < α) (hα1 : α < 1)
    {s : Set ℂ} (hs : IsCompact s) {f : CkHolderSpace k α ℂ F}
    (hf : f ∈ supportedCkHolderSubmodule k α s) : ContDiff ℝ (k + 1 : ℕ) (cauchyTransform f) :=
  (hasCompactSupport_of_mem_supportedCkHolderSubmodule hs
    hf).contDiff_cauchyTransform_of_holderWith_iteratedFDeriv hα hα1 f.contDiff
    f.memHolder_iteratedFDeriv.holderWith

end Operator

end TauCeti

end
