/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import TauCeti.Analysis.Calculus.FDeriv.ContinuousLinearMap
import TauCeti.Analysis.Calculus.IteratedFDeriv.Basic
import TauCeti.Analysis.Calculus.SecondDerivative

/-!
# Derivatives of a composite

For `g : F → G` and `f : E → F`, both `C²`, Tau Ceti's second-order chain rule
`TauCeti.fderiv_fderiv_comp_apply` writes the second derivative of `g ∘ f` as
`D²g(f x)(Df v, Df w) + Dg(f x)(D²f(v, w))`. This file turns it into a bound on the operator
norm:

`‖D²(g ∘ f)(x)‖ ≤ ‖D²g(f x)‖ ‖Df(x)‖² + ‖Dg(f x)‖ ‖D²f(x)‖`

(`SymplecticGeometry.norm_fderiv_fderiv_comp_le`).

When `f : E → 𝕜` is scalar and `φ : 𝕜 → F` is a function of one variable, the derivative of
`φ ∘ f` is `(Df x).smulRight (φ'(f x))` (`SymplecticGeometry.fderiv_scalar_comp`), so its norm
is `‖φ'(f x)‖ ‖Df(x)‖` (`SymplecticGeometry.norm_fderiv_scalar_comp`); and the bound above, read
with Tau Ceti's `TauCeti.norm_fderiv_fderiv` and Mathlib's
`norm_iteratedFDeriv_eq_norm_iteratedDeriv`, becomes
`‖D²(φ ∘ f)(x)‖ ≤ ‖φ''(f x)‖ ‖Df(x)‖² + ‖φ'(f x)‖ ‖D²f(x)‖`
(`SymplecticGeometry.norm_fderiv_fderiv_scalar_comp_le`), the norm form of Tau Ceti's
`TauCeti.fderiv_fderiv_scalar_comp_apply`.

If `g` is a left inverse of `h` near `x`, and `T` has the same value and derivative as
`h` at `x`, then `g ∘ T` has derivative the identity at `x`
(`SymplecticGeometry.fderiv_comp_eq_id_of_eventuallyEq_id`).

At a critical point `φ b` of `f`, Tau Ceti's `TauCeti.fderiv_fderiv_comp_apply_of_fderiv_eq_zero`
writes the second derivative of `f ∘ φ` at `b` as `D²f(φ b)(Dφ v, Dφ w)`. When `Dφ(b)` is onto,
the kernel of `D²(f ∘ φ)(b)` is therefore the preimage under `Dφ(b)` of the kernel of
`D²f(φ b)` (`SymplecticGeometry.ker_fderiv_fderiv_comp_of_fderiv_eq_zero`); the proof follows
Tau Ceti's `TauCeti.ker_criticalHessian_comp`, which shows the same for the critical Hessian
along a submersion of manifolds. One order higher, differentiating the second-order chain rule
once more at `b` shows that, if moreover `Dφ(b) v` lies in the kernel of `D²f(φ b)`, then
`D³(f ∘ φ)(b)(v, v, v) = D³f(φ b)(Dφ v, Dφ v, Dφ v)`
(`SymplecticGeometry.fderiv_fderiv_fderiv_comp_apply_of_fderiv_eq_zero`): the remaining terms
contain `Df(φ b)`, or `D²f(φ b)` with `Dφ(b) v` in a slot, which vanishes by the symmetry of the
second derivative.
-/

public section

namespace SymplecticGeometry

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G]
  [NormedSpace 𝕜 G] {x : E}

/-- **The second derivative of a composite.** For `g` `C²` at `f x` and `f` `C²` at `x`, the
second derivative of `g ∘ f` at `x` has norm at most
`‖D²g(f x)‖ ‖Df(x)‖² + ‖Dg(f x)‖ ‖D²f(x)‖`. -/
theorem norm_fderiv_fderiv_comp_le {g : F → G} {f : E → F} (hg : ContDiffAt 𝕜 2 g (f x))
    (hf : ContDiffAt 𝕜 2 f x) :
    ‖fderiv 𝕜 (fderiv 𝕜 (g ∘ f)) x‖ ≤
      ‖fderiv 𝕜 (fderiv 𝕜 g) (f x)‖ * ‖fderiv 𝕜 f x‖ ^ 2 +
        ‖fderiv 𝕜 g (f x)‖ * ‖fderiv 𝕜 (fderiv 𝕜 f) x‖ := by
  refine ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity) fun v w ↦ ?_
  rw [TauCeti.fderiv_fderiv_comp_apply hg hf]
  refine (norm_add_le _ _).trans ?_
  have h1 := (fderiv 𝕜 f x).le_opNorm v
  have h2 := (fderiv 𝕜 f x).le_opNorm w
  have h3 := (fderiv 𝕜 (fderiv 𝕜 g) (f x)).le_opNorm₂ (fderiv 𝕜 f x v) (fderiv 𝕜 f x w)
  have h4 := (fderiv 𝕜 g (f x)).le_opNorm (fderiv 𝕜 (fderiv 𝕜 f) x v w)
  have h5 := (fderiv 𝕜 (fderiv 𝕜 f) x).le_opNorm₂ v w
  calc _ ≤ ‖fderiv 𝕜 (fderiv 𝕜 g) (f x)‖ * ‖fderiv 𝕜 f x v‖ * ‖fderiv 𝕜 f x w‖ +
        ‖fderiv 𝕜 g (f x)‖ * ‖fderiv 𝕜 (fderiv 𝕜 f) x v w‖ := add_le_add h3 h4
    _ ≤ ‖fderiv 𝕜 (fderiv 𝕜 g) (f x)‖ * (‖fderiv 𝕜 f x‖ * ‖v‖) * (‖fderiv 𝕜 f x‖ * ‖w‖) +
        ‖fderiv 𝕜 g (f x)‖ * (‖fderiv 𝕜 (fderiv 𝕜 f) x‖ * ‖v‖ * ‖w‖) := by gcongr
    _ = _ := by ring

variable {f : E → 𝕜} {φ : 𝕜 → F}

/-- The derivative of `φ ∘ f`, for `φ` of one variable differentiable at `f x` and `f : E → 𝕜`
differentiable at `x`, is `Df(x)` scaled by `φ'(f x)`. -/
theorem fderiv_scalar_comp (hφ : DifferentiableAt 𝕜 φ (f x)) (hf : DifferentiableAt 𝕜 f x) :
    fderiv 𝕜 (φ ∘ f) x = (fderiv 𝕜 f x).smulRight (deriv φ (f x)) := by
  rw [fderiv_comp x hφ hf, ← toSpanSingleton_deriv, ContinuousLinearMap.toSpanSingleton_comp]

/-- The derivative of `φ ∘ f`, for `φ` of one variable differentiable at `f x` and `f : E → 𝕜`
differentiable at `x`, has norm `‖φ'(f x)‖ ‖Df(x)‖`. -/
theorem norm_fderiv_scalar_comp (hφ : DifferentiableAt 𝕜 φ (f x))
    (hf : DifferentiableAt 𝕜 f x) :
    ‖fderiv 𝕜 (φ ∘ f) x‖ = ‖deriv φ (f x)‖ * ‖fderiv 𝕜 f x‖ := by
  rw [fderiv_scalar_comp hφ hf, ContinuousLinearMap.norm_smulRight_apply, mul_comm]

/-- **The second derivative of a composite with a function of one variable.** For `φ` of one
variable `C²` at `f x` and `f : E → 𝕜` `C²` at `x`, the second derivative of `φ ∘ f` at `x` has
norm at most `‖φ''(f x)‖ ‖Df(x)‖² + ‖φ'(f x)‖ ‖D²f(x)‖`. -/
theorem norm_fderiv_fderiv_scalar_comp_le (hφ : ContDiffAt 𝕜 2 φ (f x))
    (hf : ContDiffAt 𝕜 2 f x) :
    ‖fderiv 𝕜 (fderiv 𝕜 (φ ∘ f)) x‖ ≤
      ‖iteratedDeriv 2 φ (f x)‖ * ‖fderiv 𝕜 f x‖ ^ 2 +
        ‖deriv φ (f x)‖ * ‖fderiv 𝕜 (fderiv 𝕜 f) x‖ := by
  rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv, ← TauCeti.norm_fderiv_fderiv,
    norm_deriv_eq_norm_fderiv]
  exact norm_fderiv_fderiv_comp_le hφ hf

/-- Let `g : F → E` be a left inverse of `h : E → F` near `x`, differentiable at `h x`, and let
`T : E → F` have the same value and the same derivative as `h` at `x`, with `h` and `T`
differentiable at `x`. Then `g ∘ T` has derivative the identity at `x`. -/
theorem fderiv_comp_eq_id_of_eventuallyEq_id {g : F → E} {h T : E → F}
    (hg : DifferentiableAt 𝕜 g (h x)) (hh : DifferentiableAt 𝕜 h x)
    (hT : DifferentiableAt 𝕜 T x) (hTx : T x = h x) (hT' : fderiv 𝕜 T x = fderiv 𝕜 h x)
    (hgh : g ∘ h =ᶠ[nhds x] id) : fderiv 𝕜 (g ∘ T) x = ContinuousLinearMap.id 𝕜 E := by
  rw [fderiv_comp x (hTx ▸ hg) hT, hT', hTx, ← fderiv_comp x hg hh, hgh.fderiv_eq, fderiv_id]

/-- **The kernel of the Hessian after a change of coordinates.** Let `f` be `C²` at `φ b` with
`Df(φ b) = 0`, and let `φ` be `C²` at `b` with `Dφ(b)` onto. Then a vector `v` lies in the kernel
of the second derivative of `f ∘ φ` at `b` exactly when `Dφ(b) v` lies in the kernel of the second
derivative of `f` at `φ b`. -/
theorem ker_fderiv_fderiv_comp_of_fderiv_eq_zero {f : E → G} {φ : F → E} {b : F}
    (hf : ContDiffAt 𝕜 2 f (φ b)) (hφ : ContDiffAt 𝕜 2 φ b) (hc : fderiv 𝕜 f (φ b) = 0)
    (hsurj : Function.Surjective (fderiv 𝕜 φ b)) :
    (fderiv 𝕜 (fderiv 𝕜 (f ∘ φ)) b).ker =
      (fderiv 𝕜 (fderiv 𝕜 f) (φ b)).ker.comap (fderiv 𝕜 φ b).toLinearMap := by
  ext v
  simp only [Submodule.mem_comap, LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
  refine ⟨fun hv ↦ ContinuousLinearMap.ext fun e ↦ ?_, fun hv ↦ ContinuousLinearMap.ext fun w ↦ ?_⟩
  · obtain ⟨w, rfl⟩ := hsurj e
    have := congr($hv w)
    rwa [TauCeti.fderiv_fderiv_comp_apply_of_fderiv_eq_zero hf hφ hc] at this
  · rw [TauCeti.fderiv_fderiv_comp_apply_of_fderiv_eq_zero hf hφ hc, hv,
      zero_apply, zero_apply]

open Topology in
/-- **The third derivative of a composite at a critical point, along a Hessian-kernel vector.**
Let `f` be `C^{minSmoothness 𝕜 3}` at `φ b` (so `C³` over `ℝ` or `ℂ`) with `Df(φ b) = 0`, let `φ`
be `C³` at `b`, and let `v` be such that `Dφ(b) v` lies in the kernel of `D²f(φ b)`. Then
`D³(f ∘ φ)(b)(v, v, v) = D³f(φ b)(Dφ(b) v, Dφ(b) v, Dφ(b) v)`: the other terms of the third-order
chain rule contain `Df(φ b)` or `D²f(φ b)` with `Dφ(b) v` in one of its slots. -/
theorem fderiv_fderiv_fderiv_comp_apply_of_fderiv_eq_zero {n : WithTop ℕ∞} {f : E → G}
    {φ : F → E} {b : F} (hf : ContDiffAt 𝕜 n f (φ b)) (hn : minSmoothness 𝕜 3 ≤ n)
    (hφ : ContDiffAt 𝕜 3 φ b) (hc : fderiv 𝕜 f (φ b) = 0) {v : F}
    (hv : fderiv 𝕜 (fderiv 𝕜 f) (φ b) (fderiv 𝕜 φ b v) = 0) :
    fderiv 𝕜 (fderiv 𝕜 (fderiv 𝕜 (f ∘ φ))) b v v v =
      fderiv 𝕜 (fderiv 𝕜 (fderiv 𝕜 f)) (φ b) (fderiv 𝕜 φ b v) (fderiv 𝕜 φ b v)
        (fderiv 𝕜 φ b v) := by
  have hf3 : ContDiffAt 𝕜 3 f (φ b) := hf.of_le (le_minSmoothness.trans hn)
  have hsymm := hf.isSymmSndFDerivAt ((minSmoothness_monotone (by norm_num)).trans hn)
  -- Derivatives at `b` of the four factors of the second-order chain rule.
  have hφ0 : HasFDerivAt φ (fderiv 𝕜 φ b) b := (hφ.differentiableAt (by norm_num)).hasFDerivAt
  have hA : HasFDerivAt (fun y ↦ fderiv 𝕜 f (φ y))
      ((fderiv 𝕜 (fderiv 𝕜 f) (φ b)).comp (fderiv 𝕜 φ b)) b :=
    (hf3.hasFDerivAt_fderiv (by norm_num)).comp b hφ0
  have hQ : HasFDerivAt (fun y ↦ fderiv 𝕜 (fderiv 𝕜 f) (φ y))
      ((fderiv 𝕜 (fderiv 𝕜 (fderiv 𝕜 f)) (φ b)).comp (fderiv 𝕜 φ b)) b :=
    ((hf3.fderiv_right (m := 2) (by norm_num)).hasFDerivAt_fderiv le_rfl).comp b hφ0
  have hB := hφ.hasFDerivAt_fderiv_apply (by norm_num) v
  have hC := ((hφ.fderiv_right (m := 2) (by norm_num)).hasFDerivAt_fderiv_apply le_rfl v).clm_apply
    (hasFDerivAt_const v b)
  -- Near `b`, the second derivative of `f ∘ φ` along `v` is given by the chain rule.
  have hev : (fun y ↦ fderiv 𝕜 (fderiv 𝕜 f) (φ y) (fderiv 𝕜 φ y v) (fderiv 𝕜 φ y v) +
      fderiv 𝕜 f (φ y) (fderiv 𝕜 (fderiv 𝕜 φ) y v v)) =ᶠ[𝓝 b]
      fun y ↦ fderiv 𝕜 (fderiv 𝕜 (f ∘ φ)) y v v := by
    filter_upwards [hφ0.continuousAt.eventually (hf3.eventually (by simp)),
      hφ.eventually (by simp)] with y hfy hφy
    exact (TauCeti.fderiv_fderiv_comp_apply (hfy.of_le (by norm_num))
      (hφy.of_le (by norm_num)) v v).symm
  have hD := (((hQ.clm_apply hB).clm_apply hB).add (hA.clm_apply hC)).congr_of_eventuallyEq
    hev.symm
  have hH : DifferentiableAt 𝕜 (fderiv 𝕜 (fderiv 𝕜 (f ∘ φ))) b :=
    (((hf3.comp b hφ).fderiv_right (m := 2) (by norm_num)).fderiv_right (m := 1)
      (by norm_num)).differentiableAt (by norm_num)
  rw [← TauCeti.fderiv_clm_apply_const_apply₂ hH, hD.fderiv]
  simp [hc, hv, hsymm.eq _ (fderiv 𝕜 φ b v)]

end SymplecticGeometry

end
