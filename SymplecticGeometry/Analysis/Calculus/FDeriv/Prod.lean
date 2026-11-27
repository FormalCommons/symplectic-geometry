/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import TauCeti.Analysis.Calculus.SecondDerivative

/-!
# Derivatives of products of functions of separate variables, and second derivatives of pairs

For `h : E → 𝕜` and `g : F → 𝕜`, the function `x ↦ g x.2 * h x.1` on `E × F`. Its derivative is
`hasFDerivAt_comp_snd_mul_comp_fst`. Its first and second derivatives along vectors `(v, 0)`
involve only `h`, and those along vectors `(0, v)` only `g`:

* `fderiv_comp_snd_mul_comp_fst_apply_mk_zero`, `fderiv_comp_snd_mul_comp_fst_apply_zero_mk`;
* `fderiv_fderiv_comp_snd_mul_comp_fst_apply_mk_zero`,
  `fderiv_fderiv_comp_snd_mul_comp_fst_apply_zero_mk`.

For `E = 𝕜`, `fderiv_comp_snd_mul_comp_fst_apply_one_zero` and
`fderiv_fderiv_comp_snd_mul_comp_fst_apply_one_zero` state the derivatives along `(1, 0)` with
`deriv`.

The second derivatives restrict to the fibres `x ↦ (x, b)` and `y ↦ (a, y)` with Tau Ceti's
`TauCeti.fderiv_fderiv_comp_apply` and `TauCeti.fderiv_fderiv_slice_right_apply`, and pull out
the constant factor with `TauCeti.fderiv_fderiv_const_smul`.

For `f : E → F` and `g : E → G`, `fderiv_fderiv_prodMk_apply` computes the second derivative of
`y ↦ (f y, g y)` componentwise, in the `fderiv (fderiv ·)` form of Tau Ceti's Levi form API. It
is the case `i = 2` of Mathlib's `iteratedFDeriv_prodMk`, read through `iteratedFDeriv_two_apply`.
-/

public section

namespace SymplecticGeometry

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {g : F → 𝕜} {h : E → 𝕜} {a : E} {b : F}

/-- The derivative of `x ↦ g x.2 * h x.1` at `(a, b)` sends `(u, v)` to
`g b * Dh(a) u + h a * Dg(b) v`. -/
theorem hasFDerivAt_comp_snd_mul_comp_fst (hg : DifferentiableAt 𝕜 g b)
    (hh : DifferentiableAt 𝕜 h a) :
    HasFDerivAt (fun x : E × F ↦ g x.2 * h x.1)
      (g b • (fderiv 𝕜 h a).comp (ContinuousLinearMap.fst 𝕜 E F) +
        h a • (fderiv 𝕜 g b).comp (ContinuousLinearMap.snd 𝕜 E F)) (a, b) :=
  (hg.hasFDerivAt.comp (a, b) hasFDerivAt_snd).mul (hh.hasFDerivAt.comp (a, b) hasFDerivAt_fst)

/-- The derivative of `x ↦ g x.2 * h x.1` at `(a, b)` along `(v, 0)` is `g b * Dh(a) v`. -/
theorem fderiv_comp_snd_mul_comp_fst_apply_mk_zero (hg : DifferentiableAt 𝕜 g b)
    (hh : DifferentiableAt 𝕜 h a) (v : E) :
    fderiv 𝕜 (fun x : E × F ↦ g x.2 * h x.1) (a, b) (v, 0) = g b * fderiv 𝕜 h a v := by
  simp [(hasFDerivAt_comp_snd_mul_comp_fst hg hh).fderiv]

/-- The derivative of `x ↦ g x.2 * h x.1` at `(a, b)` along `(0, v)` is `h a * Dg(b) v`. -/
theorem fderiv_comp_snd_mul_comp_fst_apply_zero_mk (hg : DifferentiableAt 𝕜 g b)
    (hh : DifferentiableAt 𝕜 h a) (v : F) :
    fderiv 𝕜 (fun x : E × F ↦ g x.2 * h x.1) (a, b) (0, v) = h a * fderiv 𝕜 g b v := by
  simp [(hasFDerivAt_comp_snd_mul_comp_fst hg hh).fderiv]

/-- The function `x ↦ g x.2 * h x.1` is `Cⁿ` at `(a, b)` when `g` is `Cⁿ` at `b` and `h` is `Cⁿ`
at `a`. -/
theorem contDiffAt_comp_snd_mul_comp_fst {n : WithTop ℕ∞} (hg : ContDiffAt 𝕜 n g b)
    (hh : ContDiffAt 𝕜 n h a) :
    ContDiffAt 𝕜 n (fun x : E × F ↦ g x.2 * h x.1) (a, b) :=
  (hg.comp (a, b) contDiffAt_snd).mul (hh.comp (a, b) contDiffAt_fst)

/-- The second derivative of `x ↦ g x.2 * h x.1` at `(a, b)` along `(v, 0)` and `(w, 0)` is
`g b * D²h(a) v w`. -/
theorem fderiv_fderiv_comp_snd_mul_comp_fst_apply_mk_zero (hg : ContDiffAt 𝕜 2 g b)
    (hh : ContDiffAt 𝕜 2 h a) (v w : E) :
    fderiv 𝕜 (fderiv 𝕜 (fun x : E × F ↦ g x.2 * h x.1)) (a, b) (v, 0) (w, 0) =
      g b * fderiv 𝕜 (fderiv 𝕜 h) a v w := by
  have hD : fderiv 𝕜 (fun x : E ↦ (x, b)) = fun _ ↦ ContinuousLinearMap.inl 𝕜 E F :=
    funext fun x ↦ (hasFDerivAt_prodMk_left x b).fderiv
  have H := TauCeti.fderiv_fderiv_comp_apply (φ := fun x : E ↦ (x, b))
    (contDiffAt_comp_snd_mul_comp_fst hg hh) (contDiffAt_id.prodMk contDiffAt_const) v w
  have hslice : ((fun x : E × F ↦ g x.2 * h x.1) ∘ fun x ↦ (x, b)) = g b • h :=
    funext fun x ↦ by simp
  simpa [hD, hslice, TauCeti.fderiv_fderiv_const_smul] using H.symm

/-- The second derivative of `x ↦ g x.2 * h x.1` at `(a, b)` along `(0, v)` and `(0, w)` is
`h a * D²g(b) v w`. -/
theorem fderiv_fderiv_comp_snd_mul_comp_fst_apply_zero_mk (hg : ContDiffAt 𝕜 2 g b)
    (hh : ContDiffAt 𝕜 2 h a) (v w : F) :
    fderiv 𝕜 (fderiv 𝕜 (fun x : E × F ↦ g x.2 * h x.1)) (a, b) (0, v) (0, w) =
      h a * fderiv 𝕜 (fderiv 𝕜 g) b v w := by
  have hslice : (fun y ↦ g y * h a) = h a • g := funext fun y ↦ by simp [mul_comm]
  rw [← TauCeti.fderiv_fderiv_slice_right_apply (contDiffAt_comp_snd_mul_comp_fst hg hh), hslice,
    TauCeti.fderiv_fderiv_const_smul]
  simp

/-- For `h : 𝕜 → 𝕜`, the derivative of `x ↦ g x.2 * h x.1` at `(a, b)` along `(1, 0)` is
`g b * h' a`. -/
theorem fderiv_comp_snd_mul_comp_fst_apply_one_zero {h : 𝕜 → 𝕜} {a : 𝕜}
    (hg : DifferentiableAt 𝕜 g b) (hh : DifferentiableAt 𝕜 h a) :
    fderiv 𝕜 (fun x : 𝕜 × F ↦ g x.2 * h x.1) (a, b) (1, 0) = g b * deriv h a := by
  simp [fderiv_comp_snd_mul_comp_fst_apply_mk_zero hg hh]

/-- For `h : 𝕜 → 𝕜`, the second derivative of `x ↦ g x.2 * h x.1` at `(a, b)` along `(1, 0)`
twice is `g b * h'' a`. -/
theorem fderiv_fderiv_comp_snd_mul_comp_fst_apply_one_zero {h : 𝕜 → 𝕜} {a : 𝕜}
    (hg : ContDiffAt 𝕜 2 g b) (hh : ContDiffAt 𝕜 2 h a) :
    fderiv 𝕜 (fderiv 𝕜 (fun x : 𝕜 × F ↦ g x.2 * h x.1)) (a, b) (1, 0) (1, 0) =
      g b * deriv (deriv h) a := by
  rw [fderiv_fderiv_comp_snd_mul_comp_fst_apply_mk_zero hg hh,
    TauCeti.fderiv_fderiv_apply_one_one]

section ProdMk

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] {f : E → F} {g : E → G} {x : E}

/-- The second derivative of `y ↦ (f y, g y)` is the pair of the second derivatives of `f`
and `g`, when both are `C²` at `x`. -/
theorem fderiv_fderiv_prodMk_apply (hf : ContDiffAt 𝕜 2 f x) (hg : ContDiffAt 𝕜 2 g x)
    (u w : E) :
    fderiv 𝕜 (fderiv 𝕜 fun y ↦ (f y, g y)) x u w =
      (fderiv 𝕜 (fderiv 𝕜 f) x u w, fderiv 𝕜 (fderiv 𝕜 g) x u w) := by
  simpa [iteratedFDeriv_two_apply] using
    congr($(iteratedFDeriv_prodMk hf hg le_rfl) ![u, w])

end ProdMk

end SymplecticGeometry

end
