/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.ContinuousAlternatingMap
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import TauCeti.Geometry.Manifold.DifferentialForm.Basic

/-!
# Rough differential forms

Facts about Tau Ceti's rough forms `TauCeti.RoughForm` that Tau Ceti does not state.

A rough form cast along an equality of degrees `p = q` by `LinearEquiv.cast` evaluates as the
original form on the reindexed vectors (`TauCeti.RoughForm.cast_apply`), as Tau Ceti's
`TauCeti.SmoothForm.cast_apply` says for smooth forms.

A rough `k`-form `φ` on `M` with values in `F` is a section of the bundle of continuous
alternating maps on the tangent spaces. If that section is differentiable at `x`, then
evaluating `φ` on `k` vector fields that are differentiable at `x` gives an `F`-valued function
differentiable at `x` (`TauCeti.RoughForm.mdifferentiableAt_apply_vectorField`). This is the
rough-form version of Tau Ceti's `TauCeti.SmoothForm.mdifferentiableAt_apply_vectorField`, and
its proof is the same, through Mathlib's `MDifferentiableAt.continuousAlternatingMap_bundle_apply`.

Taking the `0`-form of a function commutes with addition, negation and subtraction
(`TauCeti.RoughForm.ofFunction_add`, `TauCeti.RoughForm.ofFunction_neg`,
`TauCeti.RoughForm.ofFunction_sub`), as Tau Ceti's `TauCeti.RoughForm.ofFunction_smul` says for
scalar multiplication.

## Main results

* `TauCeti.RoughForm.cast_apply`: evaluation of a rough form cast along an equality of degrees.
* `TauCeti.RoughForm.mdifferentiableAt_apply_vectorField`: a rough form differentiable at `x`,
  evaluated on vector fields differentiable at `x`, is differentiable at `x`.
* `TauCeti.RoughForm.mdifferentiableAt_apply_two`: the same for a two-form on two vector fields,
  as the function `y ↦ φ y ![A y, B y]`.
* `TauCeti.RoughForm.ofFunction_add`, `TauCeti.RoughForm.ofFunction_neg`,
  `TauCeti.RoughForm.ofFunction_sub`: the `0`-form of `f + g`, `-f` and `f - g`.
-/

public section

open Bundle
open scoped Manifold

namespace TauCeti.RoughForm

section Cast

variable {E H M V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [ContinuousConstSMul ℝ V]

/-- A rough form cast along an equality of degrees `p = q` takes on `w` the value of the
original form on `w` reindexed along `Fin.cast h`, as `TauCeti.SmoothForm.cast_apply` says for
smooth forms. -/
theorem cast_apply {p q : ℕ} (h : p = q) (α : RoughForm I M V p) (x : M)
    (w : Fin q → TangentSpace I x) :
    LinearEquiv.cast (R := ℝ) (M := fun k ↦ RoughForm I M V k) h α x w =
      α x (w ∘ Fin.cast h) := by
  subst h
  simp only [LinearEquiv.cast_apply, cast_eq, Function.comp_def, Fin.cast_eq_self]

end Cast

section OfFunction

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]

/-- The `0`-form of a sum of functions is the sum of their `0`-forms. -/
theorem ofFunction_add [ContinuousAdd F] (f g : M → F) :
    ofFunction I (f + g) = ofFunction I f + ofFunction I g :=
  funext fun x ↦ ContinuousAlternatingMap.ext fun v ↦ by simp

variable [IsTopologicalAddGroup F]

/-- The `0`-form of `-f` is minus the `0`-form of `f`. -/
theorem ofFunction_neg (f : M → F) : ofFunction I (-f) = -ofFunction I f :=
  funext fun x ↦ ContinuousAlternatingMap.ext fun v ↦ by simp

/-- The `0`-form of a difference of functions is the difference of their `0`-forms. -/
theorem ofFunction_sub (f g : M → F) :
    ofFunction I (f - g) = ofFunction I f - ofFunction I g :=
  funext fun x ↦ ContinuousAlternatingMap.ext fun v ↦ by simp

end OfFunction

section VectorField

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

/-- If a rough `k`-form `φ` is differentiable at `x`, as a section of the bundle of alternating
maps, then its values on `k` vector fields differentiable at `x` form a function differentiable
at `x`. -/
theorem mdifferentiableAt_apply_vectorField {φ : RoughForm I M F k}
    {V : Fin k → (y : M) → TangentSpace I y} {x : M}
    (hφ : MDiffAt (fun y ↦
      (TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F) y (φ y) :
        TotalSpace (E [⋀^Fin k]→L[ℝ] F)
          (fun y ↦ TangentSpace I y [⋀^Fin k]→L[ℝ] Bundle.Trivial M F y))) x)
    (hV : ∀ i, MDifferentiableAt I I.tangent (fun y ↦ (V i y : TangentBundle I M)) x) :
    MDifferentiableAt I 𝓘(ℝ, F) (fun y ↦ φ y (V · y)) x := by
  have h := hφ.continuousAlternatingMap_bundle_apply (b := id) hV
  simpa using ((mdifferentiableAt_totalSpace _ _).1 h).2

/-- If a rough two-form `φ` is differentiable at `x`, as a section of the bundle of alternating
maps, then its values `y ↦ φ y ![A y, B y]` on two vector fields `A` and `B` differentiable at
`x` form a function differentiable at `x`. -/
theorem mdifferentiableAt_apply_two {φ : RoughForm I M F 2}
    {A B : (y : M) → TangentSpace I y} {x : M}
    (hφ : MDiffAt (fun y ↦
      (TotalSpace.mk' (E [⋀^Fin 2]→L[ℝ] F) y (φ y) :
        TotalSpace (E [⋀^Fin 2]→L[ℝ] F)
          (fun y ↦ TangentSpace I y [⋀^Fin 2]→L[ℝ] Bundle.Trivial M F y))) x)
    (hA : MDifferentiableAt I I.tangent (fun y ↦ (A y : TangentBundle I M)) x)
    (hB : MDifferentiableAt I I.tangent (fun y ↦ (B y : TangentBundle I M)) x) :
    MDifferentiableAt I 𝓘(ℝ, F) (fun y ↦ φ y ![A y, B y]) x := by
  have hev (y : M) : (fun k ↦ ![A, B] k y) = ![A y, B y] := (FinVec.etaExpand_eq _).symm
  simpa [hev] using mdifferentiableAt_apply_vectorField (V := ![A, B]) hφ
    (fun k ↦ by fin_cases k; exacts [hA, hB])

end VectorField

end TauCeti.RoughForm

end
