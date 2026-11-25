/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.Basic
import Mathlib.Analysis.Calculus.FDeriv.Pi

/-!
# Conjugate Wirtinger derivatives along coordinate lines

For a function `g : (ι → ℂ) → F` on the coordinate space of a finite type `ι`, this file relates
the conjugate Wirtinger derivative of the restriction `w ↦ g (update x i w)` of `g` to the complex
line through `x` along the `i`-th coordinate to the conjugate Wirtinger derivative of `g` itself.

## Main results

* `TauCeti.conjWirtingerDeriv_comp_update`: the conjugate Wirtinger derivative of
  `w ↦ g (update x i w)` at `ζ` in the direction `v` is that of `g` at `update x i ζ` in the
  direction `Pi.single i v`.
-/

public section

open Function

namespace TauCeti

/-- **The conjugate Wirtinger derivative along a coordinate line.** The conjugate Wirtinger
derivative at `ζ` in the direction `v` of the restriction `w ↦ g (update x i w)` of `g` to the
complex line through `x` along the `i`-th coordinate is the conjugate Wirtinger derivative of `g`
at `update x i ζ` in the direction `Pi.single i v`. -/
theorem conjWirtingerDeriv_comp_update {ι : Type*} [Fintype ι] [DecidableEq ι]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] {g : (ι → ℂ) → F} {x : ι → ℂ} {i : ι}
    {ζ : ℂ} (hg : DifferentiableAt ℝ g (update x i ζ)) (v : ℂ) :
    conjWirtingerDeriv (fun w ↦ g (update x i w)) ζ v =
      conjWirtingerDeriv g (update x i ζ) (Pi.single i v) := by
  rw [← comp_def, conjWirtingerDeriv_comp_eq_comp_fderiv hg
    (hasFDerivAt_update (𝕜 := ℂ) x ζ).differentiableAt, fderiv_update,
    ContinuousLinearMap.comp_apply]
  congr 1
  ext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [hj]

end TauCeti

end
