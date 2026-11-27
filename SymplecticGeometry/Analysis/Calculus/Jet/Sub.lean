/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Calculus.Jet.Equivalence

import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Equal jets and the jet of the difference

Tau Ceti's `TauCeti.SameJetAt 𝕜 n x f g` says that `f` and `g` have the same derivatives of
order at most `n` at `x`. When both maps are `C^n` at `x`, the derivatives of `f - g` there are
the differences of theirs (`iteratedFDeriv_sub_apply`), so this holds exactly when the
derivatives of `f - g` of order at most `n` vanish at `x`.

## Main results

* `TauCeti.sameJetAt_iff_iteratedFDeriv_sub_eq_zero`: for `f` and `g` that are `C^n` at `x`,
  they have the same jet of order `n` at `x` if and only if the iterated derivatives of `f - g`
  of order at most `n` vanish at `x`.
-/

public section

namespace TauCeti

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {n : ℕ} {x : E} {f g : E → F}

/-- Two maps that are `C^n` at `x` have the same jet of order `n` at `x` if and only if the
iterated derivatives of their difference of order at most `n` vanish at `x`. -/
theorem sameJetAt_iff_iteratedFDeriv_sub_eq_zero (hf : ContDiffAt 𝕜 n f x)
    (hg : ContDiffAt 𝕜 n g x) :
    SameJetAt 𝕜 n x f g ↔ ∀ i ≤ n, iteratedFDeriv 𝕜 i (f - g) x = 0 := by
  rw [sameJetAt_iff]
  refine forall₂_congr fun i hi ↦ ?_
  have hi' : (i : WithTop ℕ∞) ≤ n := by exact_mod_cast hi
  rw [iteratedFDeriv_sub_apply (hf.of_le hi') (hg.of_le hi'), sub_eq_zero]

end TauCeti

end
