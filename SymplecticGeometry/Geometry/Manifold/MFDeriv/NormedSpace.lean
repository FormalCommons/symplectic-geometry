/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Products with values in a normed algebra, and subtracting a constant

Mathlib's `MDifferentiableAt.smul` needs the scalar factor to take values in the base field. Here
`MDifferentiableWithinAt.smul_algebra` and its forms at a point, on a set and on the whole
manifold show that `a • g` is differentiable where `a` and `g` are, for `a` with values in a
normed `𝕜`-algebra `𝕜'` that acts on the normed space where `g` takes its values; an example is
`ℂ` acting on a complex normed space regarded as a real one. Read in charts, this is
`DifferentiableWithinAt.smul`. Tau Ceti proves the same fact at a point inside the proof of
`TauCeti.mvfderiv_smul_algebra`, and the proof here follows that step.

Mathlib's `mvfderiv_mul` is the product rule for scalar functions on a manifold. This file gives
the product rule for functions with values in a normed algebra that need not be commutative, such
as the algebra `V →L[𝕜] V` of continuous endomorphisms: `mvfderiv_fun_mul_apply'`. Mathlib states
this rule for `HasMFDerivAt` as `HasMFDerivAt.mul'`
(`Mathlib/Geometry/Manifold/MFDeriv/SpecificFunctions.lean`); the lemma here is its form for
`mvfderiv`, applied to a tangent vector.

It is Tau Ceti's Leibniz rule `TauCeti.mvfderiv_smul_algebra`, for the algebra acting on itself by
left multiplication, evaluated at a tangent vector.

`mvfderiv_sub_const` says that subtracting a constant does not change `mvfderiv`, with no
hypothesis on the function. It is the form for subtraction of Tau Ceti's
`TauCeti.mvfderiv_add_const`, from which it follows, and the manifold version of Mathlib's
`fderiv_sub_const`.
-/

public section

open scoped Manifold

section SMulAlgebra

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {𝕜' : Type*} [NormedRing 𝕜'] [NormedAlgebra 𝕜 𝕜'] [Module 𝕜' F] [IsBoundedSMul 𝕜' F]
  [IsScalarTower 𝕜 𝕜' F] {a : M → 𝕜'} {g : M → F} {s : Set M} {x : M}

/-- The product of a function with values in a normed algebra `𝕜'` and a function with values in a
normed space on which `𝕜'` acts is differentiable within `s` at `x` if both factors are. This
generalizes `MDifferentiableWithinAt.smul` from scalars in the base field. -/
@[to_fun]
theorem MDifferentiableWithinAt.smul_algebra (ha : MDifferentiableWithinAt I 𝓘(𝕜, 𝕜') a s x)
    (hg : MDifferentiableWithinAt I 𝓘(𝕜, F) g s x) :
    MDifferentiableWithinAt I 𝓘(𝕜, F) (a • g) s x :=
  mdifferentiableWithinAt_iff.2 ⟨ha.continuousWithinAt.smul hg.continuousWithinAt,
    ha.differentiableWithinAt_writtenInExtChartAt.smul
      hg.differentiableWithinAt_writtenInExtChartAt⟩

/-- The product of a function with values in a normed algebra `𝕜'` and a function with values in a
normed space on which `𝕜'` acts is differentiable at `x` if both factors are. This generalizes
`MDifferentiableAt.smul` from scalars in the base field. -/
@[to_fun]
theorem MDifferentiableAt.smul_algebra (ha : MDifferentiableAt I 𝓘(𝕜, 𝕜') a x)
    (hg : MDifferentiableAt I 𝓘(𝕜, F) g x) : MDifferentiableAt I 𝓘(𝕜, F) (a • g) x := by
  rw [← mdifferentiableWithinAt_univ] at ha hg ⊢
  exact ha.smul_algebra hg

/-- The product of a function with values in a normed algebra `𝕜'` and a function with values in a
normed space on which `𝕜'` acts is differentiable on `s` if both factors are. -/
@[to_fun]
theorem MDifferentiableOn.smul_algebra (ha : MDifferentiableOn I 𝓘(𝕜, 𝕜') a s)
    (hg : MDifferentiableOn I 𝓘(𝕜, F) g s) : MDifferentiableOn I 𝓘(𝕜, F) (a • g) s :=
  fun y hy ↦ (ha y hy).smul_algebra (hg y hy)

/-- The product of a function with values in a normed algebra `𝕜'` and a function with values in a
normed space on which `𝕜'` acts is differentiable if both factors are. -/
@[to_fun]
theorem MDifferentiable.smul_algebra (ha : MDifferentiable I 𝓘(𝕜, 𝕜') a)
    (hg : MDifferentiable I 𝓘(𝕜, F) g) : MDifferentiable I 𝓘(𝕜, F) (a • g) :=
  fun y ↦ (ha y).smul_algebra (hg y)

end SMulAlgebra

section SubConst

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Subtracting a constant does not change the derivative of a vector-valued function, read in
the target space. No differentiability is needed. This is the manifold version of
`fderiv_sub_const`. -/
@[simp]
theorem mvfderiv_sub_const (g : M → F) (c : F) (x : M) :
    mvfderiv I (fun y ↦ g y - c) x = mvfderiv I g x := by
  simp_rw [sub_eq_add_neg]
  exact TauCeti.mvfderiv_add_const g (-c) x

end SubConst

namespace SymplecticGeometry

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedRing F] [NormedAlgebra 𝕜 F]

/-- The **product rule** for functions on a manifold with values in a normed algebra, which need
not be commutative: the derivative of `y ↦ p y * q y` along `v` is `p' v * q x + p x * q' v`. -/
theorem mvfderiv_fun_mul_apply' {p q : M → F} {x : M}
    (hp : MDifferentiableAt I 𝓘(𝕜, F) p x) (hq : MDifferentiableAt I 𝓘(𝕜, F) q x)
    (v : TangentSpace I x) :
    mvfderiv I (fun y ↦ p y * q y) x v = mvfderiv I p x v * q x + p x * mvfderiv I q x v := by
  have h := congr($(TauCeti.mvfderiv_smul_algebra (𝕜' := F) hp hq) v)
  rw [add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul, smul_eq_mul, add_comm] at h
  exact h

end SymplecticGeometry
