/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Complex.LeviForm.Basic

import SymplecticGeometry.Analysis.Calculus.FDeriv.Prod
import TauCeti.Analysis.Normed.Operator.Prod

/-!
# The Levi form of a function of two real functions

For real functions `f` and `g` on a complex normed space `V` and a function `h` of two real
variables, all of class `C²`, this file computes the diagonal of the Levi form of
`y ↦ h (f y, g y)`. It is the chain rule for second derivatives, `D²(h ∘ F) = D²h (DF, DF) +
Dh (D²F)` with `F = (f, g)`, read on `v` and on `I • v`:

`Re L(h(f, g))(v, v) = ∂₁h · Re L f(v, v) + ∂₂h · Re L g(v, v)
  + (D²h (Df v, Dg v)² + D²h (Df (I v), Dg (I v))²) / 4`.

It is the two-variable form of Tau Ceti's composition rule `TauCeti.leviForm_scalar_comp_apply`.
The second derivative of `F` is computed componentwise by
`SymplecticGeometry.fderiv_fderiv_prodMk_apply`.

## Main results

* `TauCeti.re_leviForm_comp_prodMk_apply_self`: the formula above.
-/

public section

open Complex

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {f g : V → ℝ} {x : V}

/-- **The Levi form of a function of two real functions.** If `f` and `g` are `C²` at `x` and
`h : ℝ × ℝ → ℝ` is `C²` at `(f x, g x)`, the real part of the Levi form of `y ↦ h (f y, g y)` on
`v` is `∂₁h · Re L f(v, v) + ∂₂h · Re L g(v, v)` plus a quarter of the second derivative of `h`
evaluated twice on `(Df v, Dg v)` and twice on `(Df (I • v), Dg (I • v))`. Here
`∂₁h = Dh (1, 0)` and `∂₂h = Dh (0, 1)` are the partial derivatives of `h` at `(f x, g x)`. -/
theorem re_leviForm_comp_prodMk_apply_self {h : ℝ × ℝ → ℝ} (hh : ContDiffAt ℝ 2 h (f x, g x))
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) (v : V) :
    (leviForm (fun y ↦ h (f y, g y)) x v v).re =
      fderiv ℝ h (f x, g x) (1, 0) * (leviForm f x v v).re +
        fderiv ℝ h (f x, g x) (0, 1) * (leviForm g x v v).re +
        (fderiv ℝ (fderiv ℝ h) (f x, g x) (fderiv ℝ f x v, fderiv ℝ g x v)
            (fderiv ℝ f x v, fderiv ℝ g x v) +
          fderiv ℝ (fderiv ℝ h) (f x, g x) (fderiv ℝ f x (I • v), fderiv ℝ g x (I • v))
            (fderiv ℝ f x (I • v), fderiv ℝ g x (I • v))) / 4 := by
  have hF : ContDiffAt ℝ 2 (fun y ↦ (f y, g y)) x := hf.prodMk hg
  have hDF (u : V) : fderiv ℝ (fun y ↦ (f y, g y)) x u = (fderiv ℝ f x u, fderiv ℝ g x u) := by
    rw [DifferentiableAt.fderiv_prodMk (hf.differentiableAt (by norm_num))
      (hg.differentiableAt (by norm_num)), ContinuousLinearMap.prod_apply]
  have hlin (a : ℝ × ℝ) : fderiv ℝ h (f x, g x) a =
      a.1 * fderiv ℝ h (f x, g x) (1, 0) + a.2 * fderiv ℝ h (f x, g x) (0, 1) := by
    simpa using (fderiv ℝ h (f x, g x)).apply_mk_eq_smul_add_smul a.1 a.2
  have key (u : V) := Function.comp_def h _ ▸
    fderiv_fderiv_comp_apply (f := h) (φ := fun y ↦ (f y, g y)) hh hF u u
  simp only [re_leviForm_apply]
  rw [key, key, hDF, hDF, hlin (fderiv ℝ (fderiv ℝ (fun y ↦ (f y, g y))) x v v),
    hlin (fderiv ℝ (fderiv ℝ (fun y ↦ (f y, g y))) x (I • v) (I • v)),
    SymplecticGeometry.fderiv_fderiv_prodMk_apply hf hg,
    SymplecticGeometry.fderiv_fderiv_prodMk_apply hf hg]
  ring

end TauCeti

end
