/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Descent
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Semibasic
import TauCeti.Geometry.Manifold.IsManifold.Basic

/-!
# Basic forms: vanishing on the kernel and invariance

Tau Ceti's `TauCeti.RoughForm.IsBasic I' f α` says that the value of `α` at a point depends only
on the image of the point under `f` and on the images of the arguments under the derivative of
`f`. This file draws two consequences, for any map `f : M → M'`:

* `TauCeti.RoughForm.IsBasic.apply_eq_zero_of_mfderiv_eq_zero`: a basic form vanishes as soon as
  one of its arguments lies in the kernel of the derivative of `f`. In other words
  (`TauCeti.RoughForm.IsBasic.isSemibasic`), it is semibasic for `f`
  (`TauCeti.RoughForm.IsSemibasic`).
* `TauCeti.RoughForm.IsBasic.mpullback_eq`: for a differentiable `f`, a basic form is invariant
  under every differentiable self-map `σ` with `f ∘ σ = f`.

These are the two conditions of Tau Ceti's `TauCeti.RoughForm.isBasic_of_mpullback_eq`, which
gives the converse when the self-maps over `f` act transitively on its fibres.

Tau Ceti's `TauCeti.RoughForm.isBasic_mpullback` says that the pullback along any map `f` of a
form on its target is basic for `f`. With `TauCeti.RoughForm.IsBasic.isSemibasic`, this gives
`TauCeti.RoughForm.isSemibasicAt_mpullback` and `TauCeti.RoughForm.isSemibasic_mpullback`: such
a pullback is semibasic for `f`, with no differentiability asked of `f`.
`TauCeti.SmoothForm.isSemibasic_mpullback` is the same for the smooth pullback along a smooth
`f`.

## References

* S. Kobayashi and K. Nomizu, *Foundations of Differential Geometry*, Vol. I, Interscience, 1963,
  Chapter II, §5.
-/

public section

open Manifold

namespace TauCeti.RoughForm

variable {E H M E' H' M' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  [TopologicalSpace M'] [ChartedSpace H' M']
  {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] {k : ℕ} {f : M → M'}
  {α : RoughForm I M V k}

/-- A form that is basic for `f` vanishes as soon as one of its arguments lies in the kernel of
the derivative of `f`. -/
theorem IsBasic.apply_eq_zero_of_mfderiv_eq_zero (hα : IsBasic I' f α) {x : M}
    {v : Fin k → TangentSpace I x} {j : Fin k} (hv : mfderiv I I' f x (v j) = 0) :
    α x v = 0 := by
  rw [isBasic_iff.mp hα rfl v (Function.update v j 0) fun i ↦ ?_, (α x).map_update_zero]
  rcases eq_or_ne i j with rfl | hi
  · simp [hv]
  · simp [Function.update_of_ne hi]

/-- A form that is basic for `f` is semibasic for `f`: at every point, it vanishes as soon as one
of its arguments lies in the kernel of the derivative of `f`. -/
theorem IsBasic.isSemibasic (hα : IsBasic I' f α) : IsSemibasic I' f α :=
  isSemibasic_iff.mpr fun _ _ _ hv ↦ hα.apply_eq_zero_of_mfderiv_eq_zero hv

/-- A form that is basic for a differentiable map `f` is invariant under every differentiable
self-map `σ` over `f`, that is, with `f ∘ σ = f`. -/
theorem IsBasic.mpullback_eq (hα : IsBasic I' f α) (hf : MDifferentiable I I' f) {σ : M → M}
    (hσ : MDifferentiable I I σ) (hfσ : f ∘ σ = f) : mpullback I I σ α = α := by
  ext x v
  rw [mpullback_apply]
  refine isBasic_iff.mp hα (congrFun hfσ x) _ _ fun i ↦ ?_
  -- By the chain rule, `df_x` factors through the derivative of `σ`.
  have hcomp := mfderiv_comp x (hf (σ x)) (hσ x)
  rw [hfσ] at hcomp
  exact (congrArg (· (v i)) hcomp).symm

variable (I' f) in
/-- **Pullbacks from the base are semibasic.** For any map `f : M → M'` and any form `ω` on `M'`,
the pullback of `ω` along `f` is semibasic for `f` at every point `x`. -/
@[simp]
theorem isSemibasicAt_mpullback (ω : RoughForm I' M' V k) (x : M) :
    IsSemibasicAt I' f (mpullback I I' f ω) x :=
  isSemibasic_def.mp (isBasic_mpullback ω).isSemibasic x

variable (I' f) in
/-- **Pullbacks from the base are semibasic.** For any map `f : M → M'` and any form `ω` on `M'`,
the pullback of `ω` along `f` is semibasic for `f`. -/
@[simp]
theorem isSemibasic_mpullback (ω : RoughForm I' M' V k) :
    IsSemibasic I' f (mpullback I I' f ω) :=
  (isBasic_mpullback ω).isSemibasic

end TauCeti.RoughForm

namespace TauCeti.SmoothForm

open scoped ContDiff

variable {E H M E' H' M' F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' 1 M']
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

/-- **Smooth pullbacks from the base are semibasic.** For a smooth map `f : M → M'` and a smooth
form `φ` on `M'`, the smooth pullback of `φ` along `f` is semibasic for `f`. -/
theorem isSemibasic_mpullback {f : M → M'} (hf : ContMDiff I I' ∞ f) (φ : SmoothForm I' M' F k) :
    RoughForm.IsSemibasic (F := F) I' f (mpullback f hf φ).val := by
  rw [coe_mpullback]
  exact RoughForm.isSemibasic_mpullback (I := I) (V := F) I' f φ.val

end TauCeti.SmoothForm

end
