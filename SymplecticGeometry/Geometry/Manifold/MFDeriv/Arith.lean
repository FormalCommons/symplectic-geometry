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
`c` does not change the derivative of `f`, and subtracting `f` from `c` negates it.

## Main results

* `HasMFDerivWithinAt.sub_const`, `HasMFDerivAt.sub_const`: a derivative of `f` is one of
  `fun y ↦ f y - c`.
* `mdifferentiableWithinAt_sub_const_iff`, `mdifferentiableAt_sub_const_iff`: `fun y ↦ f y - c`
  is differentiable exactly where `f` is.
* `mfderivWithin_sub_const`, `mfderiv_sub_const`:
  `mfderiv I 𝓘(𝕜, E') (fun y ↦ f y - c) x = mfderiv I 𝓘(𝕜, E') f x`, and its form within a set,
  with no hypothesis on `f` or on the set.
* `HasMFDerivWithinAt.const_sub`, `HasMFDerivAt.const_sub`: if `f'` is a derivative of `f`,
  then `-f'` is one of `fun y ↦ c - f y`.
* `mdifferentiableWithinAt_const_sub_iff`, `mdifferentiableAt_const_sub_iff`:
  `fun y ↦ c - f y` is differentiable exactly where `f` is.
* `mfderivWithin_const_sub`, `mfderiv_const_sub`:
  `mfderiv I 𝓘(𝕜, E') (fun y ↦ c - f y) x = -mfderiv I 𝓘(𝕜, E') f x`, and its form within a
  set that has unique derivatives at `x`.

These are the manifold analogues of Mathlib's `HasFDerivAt.sub_const`, `fderiv_sub_const` and
`fderivWithin_sub_const`, of its `differentiableAt_add_const_iff` for subtraction, and of its
`HasFDerivAt.const_sub`, `differentiableWithinAt_const_sub_iff`, `fderiv_const_sub` and
`fderivWithin_const_sub` (`Mathlib/Analysis/Calculus/FDeriv/Add.lean`). The proofs follow
those of Mathlib's `mfderivWithin_neg` and `mfderiv_neg`, splitting on whether `f` is
differentiable; in the differentiable case, `mfderivWithin_sub_const` reduces to Mathlib's
`fderivWithin_sub_const` in the chart. Tau Ceti's `TauCeti.mvfderiv_add_const` is the analogous
statement for its `mvfderiv`.
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

/-- If `f'` is a derivative of `f` within a set, then `-f'` is one of `fun y ↦ c - f y`. -/
theorem HasMFDerivWithinAt.const_sub (hf : HasMFDerivWithinAt I 𝓘(𝕜, E') f s x f') (c : E') :
    HasMFDerivWithinAt I 𝓘(𝕜, E') (fun y ↦ c - f y) s x (-f') :=
  ((hasMFDerivWithinAt_const c s x).sub hf).congr_mfderiv (zero_sub f')

/-- If `f'` is a derivative of `f`, then `-f'` is one of `fun y ↦ c - f y`. -/
theorem HasMFDerivAt.const_sub (hf : HasMFDerivAt I 𝓘(𝕜, E') f x f') (c : E') :
    HasMFDerivAt I 𝓘(𝕜, E') (fun y ↦ c - f y) x (-f') :=
  ((hasMFDerivAt_const c x).sub hf).congr_mfderiv (zero_sub f')

/-- A map is differentiable within a set exactly when it is after subtracting it from a
constant. -/
@[simp]
theorem mdifferentiableWithinAt_const_sub_iff (c : E') :
    MDifferentiableWithinAt I 𝓘(𝕜, E') (fun y ↦ c - f y) s x ↔
      MDifferentiableWithinAt I 𝓘(𝕜, E') f s x :=
  ⟨fun h ↦ by simpa using (h.hasMFDerivWithinAt.const_sub c).mdifferentiableWithinAt,
    fun h ↦ (h.hasMFDerivWithinAt.const_sub c).mdifferentiableWithinAt⟩

/-- A map is differentiable at a point exactly when it is after subtracting it from a
constant. -/
@[simp]
theorem mdifferentiableAt_const_sub_iff (c : E') :
    MDifferentiableAt I 𝓘(𝕜, E') (fun y ↦ c - f y) x ↔ MDifferentiableAt I 𝓘(𝕜, E') f x := by
  simp only [← mdifferentiableWithinAt_univ, mdifferentiableWithinAt_const_sub_iff]

/-- Subtracting a map from a constant negates its derivative within a set that has unique
derivatives at the point: the manifold analogue of `fderivWithin_const_sub`. -/
theorem mfderivWithin_const_sub (hs : UniqueMDiffWithinAt I s x) (c : E') :
    mfderivWithin I 𝓘(𝕜, E') (fun y ↦ c - f y) s x = -mfderivWithin I 𝓘(𝕜, E') f s x := by
  by_cases hf : MDifferentiableWithinAt I 𝓘(𝕜, E') f s x
  · exact (hf.hasMFDerivWithinAt.const_sub c).mfderivWithin hs
  · exact (mfderivWithin_zero_of_not_mdifferentiableWithinAt
      ((mdifferentiableWithinAt_const_sub_iff c).not.2 hf)).trans
      (neg_eq_zero.2 (mfderivWithin_zero_of_not_mdifferentiableWithinAt hf)).symm

/-- Subtracting a map from a constant negates its derivative: the manifold analogue of
`fderiv_const_sub`. -/
theorem mfderiv_const_sub (c : E') :
    mfderiv I 𝓘(𝕜, E') (fun y ↦ c - f y) x = -mfderiv I 𝓘(𝕜, E') f x := by
  rw [← mfderivWithin_univ, mfderivWithin_const_sub (uniqueMDiffWithinAt_univ I),
    mfderivWithin_univ]

end
