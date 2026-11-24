/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Complex.Beltrami.Linear
import TauCeti.Analysis.Complex.UpperHalfPlane.Cayley

/-!
# The Beltrami coefficient of a positively oriented complex structure on the plane

Let `K` be a real-linear complex structure on `ℂ` with `K 1 ≠ -i`. Tau Ceti's
`TauCeti.Beltrami.linearMap_apply_eq_I_mul` shows that the map `z ↦ z + ν conj z`, with
`ν = (i - K 1) / (conj (K 1) - i)`, intertwines `K` with multiplication by `i`, so the
complex-linear functionals for `K` are the multiples of `dz + ν dz̄`. For a structure tamed by the
standard area form this `ν` is Tau Ceti's scalar coefficient `TauCeti.Beltrami.coefficientEquiv`
(`TauCeti.Beltrami.coefficientEquiv_eq_div`).

The operator `∂bar + μ ∂` with `μ = -ν = (K 1 - i) / (conj (K 1) - i)` is the one whose kernel
consists of the functions with `K`-complex-linear differential. Its coefficient is the Cayley
transform of `K 1` up to a conjugate denominator, so `‖μ‖ < 1` exactly when `K 1` lies in the
upper half plane, that is, when `K` induces the standard orientation of `ℂ`, or equivalently when
the standard area form tames `K` (`TauCeti.stdComplexSymplecticForm_tames_iff_im_pos`). This is
`TauCeti.Beltrami.norm_beltrami_lt_one_of_im_pos`; it does not ask that `K` square to `-1`.

## Main results

* `TauCeti.Beltrami.coefficientEquiv_eq_div`: Tau Ceti's coefficient of a tame structure `J` is
  `(i - J 1) / (conj (J 1) - i)`.
* `TauCeti.Beltrami.norm_beltrami_lt_one_of_im_pos`: if `0 < Im (K 1)`, then
  `‖(K 1 - i) / (conj (K 1) - i)‖ < 1`.

## References

* [D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*][McDuffSalamon2012],
  Appendix C.
-/

public section

open Complex
open scoped ComplexConjugate

namespace TauCeti.Beltrami

/-- Tau Ceti's scalar Beltrami coefficient of a structure `J` tamed by the standard area form is
`(i - J 1) / (conj (J 1) - i)`, the coefficient of `linearMap_apply_eq_I_mul`. -/
theorem coefficientEquiv_eq_div (J : AlmostComplexStructure ℂ)
    (hJ : stdComplexSymplecticForm.Tames J) :
    (coefficientEquiv ⟨J, hJ⟩).val = (I - J 1) / (conj (J 1) - I) := by
  refine eq_div_of_mul_eq (fun h ↦ ?_) (coefficientEquiv_mul_conj_sub_I J hJ)
  -- `Im (conj (J 1) - i) = -Im (J 1) - 1 < 0`.
  have him := congrArg Complex.im h
  simp only [sub_im, conj_im, I_im, zero_im] at him
  linarith [(stdComplexSymplecticForm_tames_iff_im_pos J).1 hJ]

/-- If a real-linear endomorphism `K` of `ℂ` sends `1` to the open upper half plane, as a complex
structure inducing the standard orientation does, then the coefficient
`μ = (K 1 - i) / (conj (K 1) - i)` of the operator `∂bar + μ ∂` of `K`, the negative of its
Beltrami coefficient, has norm less than one. -/
theorem norm_beltrami_lt_one_of_im_pos {K : ℂ →L[ℝ] ℂ} (hK : 0 < (K 1).im) :
    ‖(K 1 - I) / (conj (K 1) - I)‖ < 1 := by
  have hc : conj (K 1) - I = conj (K 1 + I) := by simp [sub_eq_add_neg]
  rw [hc, norm_div, Complex.norm_conj, norm_sub_I_div_norm_add_I_lt_one_iff
    (add_I_ne_zero_of_im_nonneg hK.le)]
  exact hK

end TauCeti.Beltrami

end
