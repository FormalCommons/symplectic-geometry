/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-!
# Subtracting a constant on a manifold

For a map `f : M → E'` from a manifold to a normed space and a constant `c : E'`, subtracting
`c` does not change the derivative of `f`.

## Main results

* `HasMFDerivWithinAt.sub_const`, `HasMFDerivAt.sub_const`: a derivative of `f` is one of
  `fun y ↦ f y - c`.
* `mdifferentiableWithinAt_sub_const_iff`, `mdifferentiableAt_sub_const_iff`: `fun y ↦ f y - c`
  is differentiable exactly where `f` is.
* `mfderivWithin_sub_const`, `mfderiv_sub_const`:
  `mfderiv I 𝓘(𝕜, E') (fun y ↦ f y - c) x = mfderiv I 𝓘(𝕜, E') f x`, and its form within a set,
  with no hypothesis on `f` or on the set.

These are the manifold analogues of Mathlib's `HasFDerivAt.sub_const`, `fderiv_sub_const` and
`fderivWithin_sub_const`, and of its `differentiableAt_add_const_iff` for subtraction
(`Mathlib/Analysis/Calculus/FDeriv/Add.lean`). The proofs follow those of Mathlib's
`mfderivWithin_neg` and `mfderiv_neg`, splitting on whether `f` is differentiable; in the
differentiable case, `mfderivWithin_sub_const` reduces to Mathlib's `fderivWithin_sub_const` in
the chart. Tau Ceti's `TauCeti.mvfderiv_add_const` is the analogous statement for its `mvfderiv`.
-/

public section

open scoped Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {f : M → E'} {s : Set M} {x : M} {f' : TangentSpace I x →L[𝕜] E'}

/-- Subtracting a constant does not change a derivative within a set. -/
theorem HasMFDerivWithinAt.sub_const (hf : HasMFDerivWithinAt I 𝓘(𝕜, E') f s x f') (c : E') :
    HasMFDerivWithinAt I 𝓘(𝕜, E') (fun y ↦ f y - c) s x f' :=
  (hf.sub (hasMFDerivWithinAt_const c s x)).congr_mfderiv (sub_zero f')

/-- Subtracting a constant does not change a derivative. -/
theorem HasMFDerivAt.sub_const (hf : HasMFDerivAt I 𝓘(𝕜, E') f x f') (c : E') :
    HasMFDerivAt I 𝓘(𝕜, E') (fun y ↦ f y - c) x f' :=
  (hf.sub (hasMFDerivAt_const c x)).congr_mfderiv (sub_zero f')

/-- A map is differentiable within a set exactly when it is after subtracting a constant. -/
@[simp]
theorem mdifferentiableWithinAt_sub_const_iff (c : E') :
    MDifferentiableWithinAt I 𝓘(𝕜, E') (fun y ↦ f y - c) s x ↔
      MDifferentiableWithinAt I 𝓘(𝕜, E') f s x := by
  refine ⟨fun h ↦ ?_, fun h ↦ (h.hasMFDerivWithinAt.sub_const c).mdifferentiableWithinAt⟩
  have h' := h.add (mdifferentiableWithinAt_const (c := c))
  rwa [show ((fun y ↦ f y - c) + fun _ ↦ c) = f from funext fun y ↦ sub_add_cancel (f y) c] at h'

/-- A map is differentiable at a point exactly when it is after subtracting a constant. -/
@[simp]
theorem mdifferentiableAt_sub_const_iff (c : E') :
    MDifferentiableAt I 𝓘(𝕜, E') (fun y ↦ f y - c) x ↔ MDifferentiableAt I 𝓘(𝕜, E') f x := by
  simp only [← mdifferentiableWithinAt_univ, mdifferentiableWithinAt_sub_const_iff]

/-- Subtracting a constant does not change the derivative within a set. -/
theorem mfderivWithin_sub_const (c : E') :
    mfderivWithin I 𝓘(𝕜, E') (fun y ↦ f y - c) s x = mfderivWithin I 𝓘(𝕜, E') f s x := by
  by_cases hf : MDifferentiableWithinAt I 𝓘(𝕜, E') f s x
  · have hf' := (mdifferentiableWithinAt_sub_const_iff c).2 hf
    simp only [mfderivWithin, hf, hf', ite_true, writtenInExtChartAt, extChartAt_model_space_eq_id,
      PartialEquiv.refl_coe]
    exact fderivWithin_sub_const (f := f ∘ (extChartAt I x).symm) c
  · exact (mfderivWithin_zero_of_not_mdifferentiableWithinAt
      ((mdifferentiableWithinAt_sub_const_iff c).not.2 hf)).trans
      (mfderivWithin_zero_of_not_mdifferentiableWithinAt hf).symm

/-- Subtracting a constant does not change the derivative: the manifold analogue of
`fderiv_sub_const`. -/
theorem mfderiv_sub_const (c : E') :
    mfderiv I 𝓘(𝕜, E') (fun y ↦ f y - c) x = mfderiv I 𝓘(𝕜, E') f x := by
  rw [← mfderivWithin_univ, mfderivWithin_sub_const, mfderivWithin_univ]

end
