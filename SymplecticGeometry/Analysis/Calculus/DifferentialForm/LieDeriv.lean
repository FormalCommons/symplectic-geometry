/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.DifferentialForm.Basic
public import Mathlib.Analysis.RCLike.Basic
import TauCeti.Analysis.Calculus.DifferentialForm.Const
import TauCeti.Analysis.Calculus.DifferentialForm.LieDeriv
import TauCeti.Analysis.Calculus.MeanValue

/-!
# Closed forms are invariant along their kernel directions

A differential form `α` on a normed space that is closed, and into which a fixed vector `w`
inserts to zero (`ι_w α = 0`), does not change in the direction `w`. For the constant vector
field `w`, the Lie derivative `L_w α` is the directional derivative `Dα · w`, and Cartan's formula
`L_w α = ι_w dα + d (ι_w α)` makes both terms on the right vanish.

## Main results

* `fderiv_apply_eq_zero_of_extDeriv_eq_zero`: if `α` is closed at `x` and `ι_w α = 0` near `x`,
  then `Dα(x) w = 0`.
* `apply_add_eq_of_extDeriv_eq_zero`: if `α` is differentiable and closed on an open set `U` and
  `ι_w α = 0` on `U`, then `α (z + w) = α z` whenever the segment from `z` to `z + w` lies in `U`.

Both apply Tau Ceti's flat Cartan formula `TauCeti.lieDerivForm_eq_curryLeft_extDeriv_add`; the
second integrates the first along the segment with `TauCeti.apply_add_eq_of_fderiv_apply_eq_zero`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Theorem 14.35
  (Cartan's formula)
-/

public section

open Set Filter
open scoped Topology

section Field

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {k : ℕ}

/-- **A closed form is invariant along its kernel directions.** Let `α` be a differential form on
a normed space, differentiable and closed at `x`, and let `w` be a fixed vector with `ι_w α = 0`
near `x`. Then the derivative of `α` at `x` along `w` vanishes. This is Cartan's formula
`L_w α = ι_w dα + d (ι_w α)` for the constant vector field `w`, whose Lie derivative is the
directional derivative. -/
theorem fderiv_apply_eq_zero_of_extDeriv_eq_zero {α : E → E [⋀^Fin (k + 1)]→L[𝕜] F} {x w : E}
    (hα : DifferentiableAt 𝕜 α x) (hd : extDeriv α x = 0)
    (hw : ∀ᶠ y in 𝓝 x, (α y).curryLeft w = 0) : fderiv 𝕜 α x w = 0 := by
  have h := TauCeti.lieDerivForm_eq_curryLeft_extDeriv_add (V := fun _ ↦ w) hα
    (differentiableAt_const w)
  have h0 : extDeriv (fun y ↦ (α y).curryLeft w) x = 0 := by
    rw [Filter.EventuallyEq.extDeriv_eq (ω₂ := fun _ ↦ 0) hw]
    simp
  simpa [TauCeti.lieDerivForm_def, hd, h0] using h

end Field

section RCLike

variable {𝕂 E F : Type*} [RCLike 𝕂] [NormedAddCommGroup E] [NormedSpace 𝕂 E]
  [NormedAddCommGroup F] [NormedSpace 𝕂 F] {k : ℕ}

/-- **A closed form is constant along its kernel directions.** Let `α` be a differential form that
is differentiable and closed on an open set `U` of a normed space, and let `w` be a fixed vector
with `ι_w α = 0` on `U`. If the segment from `z` to `z + w` lies in `U`, then `α` takes the same
value at `z` and at `z + w`. -/
theorem apply_add_eq_of_extDeriv_eq_zero {α : E → E [⋀^Fin (k + 1)]→L[𝕂] F} {U : Set E}
    (hU : IsOpen U) (hα : ∀ y ∈ U, DifferentiableAt 𝕂 α y) (hd : ∀ y ∈ U, extDeriv α y = 0)
    {z w : E} (hw : ∀ y ∈ U, (α y).curryLeft w = 0)
    (hzw : ∀ t ∈ Icc (0 : ℝ) 1, z + (t : 𝕂) • w ∈ U) : α (z + w) = α z :=
  TauCeti.apply_add_eq_of_fderiv_apply_eq_zero (fun t ht ↦ hα _ (hzw t ht)) fun t ht ↦
    fderiv_apply_eq_zero_of_extDeriv_eq_zero (hα _ (hzw t ht)) (hd _ (hzw t ht))
      (eventually_of_mem (hU.mem_nhds (hzw t ht)) hw)

end RCLike

end
