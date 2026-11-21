/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.DifferentialForm.Basic
public import Mathlib.Analysis.RCLike.Basic
public import TauCeti.Analysis.Calculus.DifferentialForm.LieDeriv
import TauCeti.Analysis.Calculus.DifferentialForm.Const
import TauCeti.Analysis.Calculus.MeanValue

/-!
# The flat Lie derivative of forms: linearity in the field, and closed forms

Facts about Tau Ceti's Lie derivative of differential forms on a normed space,
`TauCeti.lieDerivFormWithin` and `TauCeti.lieDerivForm`.

The first section completes its linearity in the vector field. Tau Ceti proves additivity
(`TauCeti.lieDerivFormWithin_add_left`, `TauCeti.lieDerivForm_add_left`); here the Lie
derivative along the zero field vanishes, and a constant multiple of the field gives that
multiple of the Lie derivative, `L_{c V} ω = c L_V ω`. Neither statement asks for any
differentiability, since the derivative of a constant multiple of a field is that multiple of its
derivative (`fderivWithin_const_smul_field`). These proofs follow Tau Ceti's
`TauCeti.mlieBracket_const_smul_left_field`.

The second section shows that a closed form `α` into which a fixed vector `w` inserts to zero
(`ι_w α = 0`) does not change in the direction `w`. For the constant vector field `w`, the Lie
derivative `L_w α` is the directional derivative `Dα · w`, and Cartan's formula
`L_w α = ι_w dα + d (ι_w α)` makes both terms on the right vanish.

## Main results

* `TauCeti.lieDerivFormWithin_zero_left`, `TauCeti.lieDerivForm_zero_left`: the Lie derivative
  along the zero field vanishes.
* `TauCeti.lieDerivFormWithin_const_smul_left`, `TauCeti.lieDerivForm_const_smul_left`:
  homogeneity in the field.
* `fderiv_apply_eq_zero_of_extDeriv_eq_zero`: if `α` is closed at `x` and `ι_w α = 0` near `x`,
  then `Dα(x) w = 0`.
* `apply_add_eq_of_extDeriv_eq_zero`: if `α` is differentiable and closed on an open set `U` and
  `ι_w α = 0` on `U`, then `α (z + w) = α z` whenever the segment from `z` to `z + w` lies in `U`.

The last two apply Tau Ceti's flat Cartan formula `TauCeti.lieDerivForm_eq_curryLeft_extDeriv_add`;
the second integrates the first along the segment with
`TauCeti.apply_add_eq_of_fderiv_apply_eq_zero`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Chapter 14,
  including Theorem 14.35 (Cartan's formula)
-/

public section

open Set Filter
open scoped Topology

namespace TauCeti

section LinearInField

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {k : ℕ} {s : Set E} {x : E}

/-- The Lie derivative within a set of a form along the zero vector field vanishes. -/
@[simp]
theorem lieDerivFormWithin_zero_left (ω : E → E [⋀^Fin k]→L[𝕜] F) (s : Set E) (x : E) :
    lieDerivFormWithin 0 ω s x = 0 := by
  simp [lieDerivFormWithin_def, fderivWithin_zero]

/-- The Lie derivative of a form along the zero vector field vanishes. -/
@[simp]
theorem lieDerivForm_zero_left (ω : E → E [⋀^Fin k]→L[𝕜] F) :
    lieDerivForm 0 ω = 0 := by
  rw [← lieDerivFormWithin_univ]
  exact funext (lieDerivFormWithin_zero_left ω univ)

/-- The Lie derivative within a set commutes with constant multiples of the vector field, where
derivatives within the set are unique. -/
@[simp]
theorem lieDerivFormWithin_const_smul_left (c : 𝕜) (V : E → E) (ω : E → E [⋀^Fin k]→L[𝕜] F)
    (hs : UniqueDiffWithinAt 𝕜 s x) :
    lieDerivFormWithin (c • V) ω s x = c • lieDerivFormWithin V ω s x := by
  simp only [lieDerivFormWithin_def, fderivWithin_const_smul_field c hs, Pi.smul_apply, map_smul,
    smul_add]

/-- The Lie derivative commutes with constant multiples of the vector field:
`L_{c V} ω = c L_V ω`. -/
@[simp]
theorem lieDerivForm_const_smul_left (c : 𝕜) (V : E → E) (ω : E → E [⋀^Fin k]→L[𝕜] F) :
    lieDerivForm (c • V) ω = c • lieDerivForm V ω := by
  ext x : 1
  simpa only [lieDerivFormWithin_univ, Pi.smul_apply] using
    lieDerivFormWithin_const_smul_left c V ω (uniqueDiffWithinAt_univ (x := x))

end LinearInField

end TauCeti

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
