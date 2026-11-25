/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.ComplexLinearPart
import TauCeti.Analysis.Complex.Wirtinger.Basic

/-!
# The `(0,1)`-projection of a complex structure on the plane, in Wirtinger form

A real-linear map `L : ℂ → ℂ` is `L v = v a + conj v b`, with `a = ∂L` and `b = ∂bar L` the values
at `1` of its complex-linear and complex-antilinear parts: this is Tau Ceti's
`TauCeti.fderiv_apply_eq_smul_wirtingerDeriv_add_smul_conjWirtingerDeriv` for the map `L`
itself. For a second real-linear map `K`, write `p` and `q` for these values of `K`. The
`(0,1)`-projection `½ (L + i L K)` of `L` for `K` then has complex-antilinear part
`½ ((1 + i conj p) b + i q a)`
(`ContinuousLinearMap.complexAntilinearPart_half_smul_add_I_smul_comp_apply_one`),
for any `K`.

When `K` is a complex structure (`K ∘ K = -1`), `p` is purely imaginary
(`ContinuousLinearMap.conj_complexLinearPart_one_eq_neg`) and `p² = -1 - |q|²`
(`ContinuousLinearMap.complexLinearPart_one_sq`). If moreover `K 1 ≠ -i`, then
`1 + i conj p ≠ 0` (`ContinuousLinearMap.one_add_I_mul_conj_complexLinearPart_one_ne_zero`), and
`(1 + i conj p) μ = i q` for `μ = (K 1 - i) / (conj (K 1) - i)`, the negative of the Beltrami
coefficient `ν = (i - K 1) / (conj (K 1) - i)` of `K`
(`ContinuousLinearMap.one_add_I_mul_conj_complexLinearPart_one_mul_div_eq`). So the
`(0,1)`-projection for `K`, followed by the complex-antilinear part, sends `L` to the
complex-antilinear map `v ↦ conj v · c (∂bar L + μ ∂L)` with `c = ½ (1 + i conj p) ≠ 0`
(`ContinuousLinearMap.complexAntilinearPartL_half_smul_add_I_smul_comp_apply`): this is the
pointwise form of a Cauchy–Riemann operator for `K` read against the standard structure of `ℂ`.

## References

* [D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*][McDuffSalamon2012],
  Appendix C.1.
-/

public section

open ComplexConjugate

namespace Complex

/-- If `w ≠ -i`, then `conj w - i ≠ 0`. -/
theorem conj_sub_I_ne_zero {w : ℂ} (hw : w ≠ -I) : conj w - I ≠ 0 := fun h ↦
  hw (by simpa using congrArg conj (sub_eq_zero.1 h))

end Complex

namespace ContinuousLinearMap

/-- For a real-linear complex structure `K` on `ℂ`, with `p` and `q` the values at `1` of its
complex-linear and complex-antilinear parts, `p² = -1 - conj q * q`. -/
theorem complexLinearPart_one_sq {K : ℂ →L[ℝ] ℂ} (hK : ∀ v, K (K v) = -v) :
    K.complexLinearPart 1 ^ 2 =
      -1 - conj (K.complexAntilinearPart 1) * K.complexAntilinearPart 1 := by
  have hK' (v : ℂ) := by
    have := TauCeti.fderiv_apply_eq_smul_wirtingerDeriv_add_smul_conjWirtingerDeriv (f := K) 0 v
    rwa [TauCeti.wirtingerDeriv_eq_complexLinearPart,
      TauCeti.conjWirtingerDeriv_eq_complexAntilinearPart, K.fderiv] at this
  have h1 := hK 1
  have h2 := hK Complex.I
  generalize K.complexLinearPart 1 = p at hK' ⊢
  generalize K.complexAntilinearPart 1 = q at hK' ⊢
  simp only [hK', smul_eq_mul, map_add, map_mul, map_neg, Complex.conj_I, neg_neg, map_one,
    one_mul] at h1 h2
  linear_combination (1 / 2 : ℂ) * h1 + (-Complex.I / 2) * h2 +
    (1 + p ^ 2 - p * q + conj q * q - q * conj p) / 2 * Complex.I_sq

/-- For a real-linear complex structure `K` on `ℂ`, the value at `1` of its complex-linear part is
purely imaginary. -/
theorem conj_complexLinearPart_one_eq_neg {K : ℂ →L[ℝ] ℂ} (hK : ∀ v, K (K v) = -v) :
    conj (K.complexLinearPart 1) = -K.complexLinearPart 1 := by
  have hp2 := complexLinearPart_one_sq hK
  generalize K.complexLinearPart 1 = p at hp2 ⊢
  generalize K.complexAntilinearPart 1 = q at hp2
  have hre := congrArg Complex.re hp2
  have him := congrArg Complex.im hp2
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.neg_re, Complex.neg_im, Complex.one_re, Complex.one_im, Complex.conj_re,
    Complex.conj_im] at hre him
  have hx : p.re = 0 := by
    rcases mul_eq_zero.1 (show p.re * p.im = 0 by linarith) with h | h
    · exact h
    · rw [h] at hre
      nlinarith [sq_nonneg p.re, sq_nonneg q.re, sq_nonneg q.im]
  apply Complex.ext <;> simp [hx]

/-- For a real-linear complex structure `K` on `ℂ` with `K 1 ≠ -i`, and `p` the value at `1` of
its complex-linear part, `1 + i conj p ≠ 0`. -/
theorem one_add_I_mul_conj_complexLinearPart_one_ne_zero {K : ℂ →L[ℝ] ℂ}
    (hK : ∀ v, K (K v) = -v) (hK1 : K 1 ≠ -Complex.I) :
    1 + Complex.I * conj (K.complexLinearPart 1) ≠ 0 := by
  have hc := conj_complexLinearPart_one_eq_neg hK
  have hp2 := complexLinearPart_one_sq hK
  rw [← K.complexLinearPart_add_complexAntilinearPart_apply 1] at hK1
  generalize K.complexLinearPart 1 = p at hc hp2 hK1 ⊢
  generalize K.complexAntilinearPart 1 = q at hp2 hK1
  rw [hc]
  intro h
  have hp : p = -Complex.I := by linear_combination Complex.I * h + p * Complex.I_sq
  rw [hp] at hp2
  have hq : q = 0 := by
    have hq : conj q * q = 0 := by linear_combination hp2 - Complex.I_sq
    rw [mul_comm, Complex.mul_conj] at hq
    exact Complex.normSq_eq_zero.1 (by exact_mod_cast hq)
  exact hK1 (by rw [hp, hq, add_zero])

/-- Let `K` be a real-linear complex structure on `ℂ` with `K 1 ≠ -i`, and let `p` and `q` be the
values at `1` of its complex-linear and complex-antilinear parts. Then `(1 + i conj p) μ = i q`
for `μ = (K 1 - i) / (conj (K 1) - i)`, the negative of the Beltrami coefficient of `K`. -/
theorem one_add_I_mul_conj_complexLinearPart_one_mul_div_eq {K : ℂ →L[ℝ] ℂ}
    (hK : ∀ v, K (K v) = -v) (hK1 : K 1 ≠ -Complex.I) :
    (1 + Complex.I * conj (K.complexLinearPart 1)) * ((K 1 - Complex.I) / (conj (K 1) - Complex.I))
      = Complex.I * K.complexAntilinearPart 1 := by
  have hden := Complex.conj_sub_I_ne_zero hK1
  have hc := conj_complexLinearPart_one_eq_neg hK
  have hp2 := complexLinearPart_one_sq hK
  rw [← K.complexLinearPart_add_complexAntilinearPart_apply 1] at hden ⊢
  generalize K.complexLinearPart 1 = p at hc hp2 hden ⊢
  generalize K.complexAntilinearPart 1 = q at hp2 hden ⊢
  rw [map_add, hc] at hden ⊢
  rw [mul_div_assoc', div_eq_iff hden]
  linear_combination (-Complex.I) * hp2 + (p + q) * Complex.I_sq

/-- For real-linear maps `L K : ℂ → ℂ`, the complex-antilinear part at `1` of `½ (L + i L K)`, the
`(0,1)`-projection of `L` for `K` when `K` is a complex structure, is
`½ ((1 + i conj p) b + i q a)`, where `a`, `b` are the values at `1` of the ℂ-linear and
ℂ-antilinear parts of `L` and `p`, `q` those of `K`. -/
theorem complexAntilinearPart_half_smul_add_I_smul_comp_apply_one (L K : ℂ →L[ℝ] ℂ) :
    ((2⁻¹ : ℝ) • (L + Complex.I • L.comp K)).complexAntilinearPart 1 =
      2⁻¹ * ((1 + Complex.I * conj (K.complexLinearPart 1)) * L.complexAntilinearPart 1 +
        Complex.I * K.complexAntilinearPart 1 * L.complexLinearPart 1) := by
  have hL (v : ℂ) := by
    have := TauCeti.fderiv_apply_eq_smul_wirtingerDeriv_add_smul_conjWirtingerDeriv (f := L) 0 v
    rwa [TauCeti.wirtingerDeriv_eq_complexLinearPart,
      TauCeti.conjWirtingerDeriv_eq_complexAntilinearPart, L.fderiv] at this
  have hK (v : ℂ) := by
    have := TauCeti.fderiv_apply_eq_smul_wirtingerDeriv_add_smul_conjWirtingerDeriv (f := K) 0 v
    rwa [TauCeti.wirtingerDeriv_eq_complexLinearPart,
      TauCeti.conjWirtingerDeriv_eq_complexAntilinearPart, K.fderiv] at this
  generalize L.complexLinearPart 1 = a at hL ⊢
  generalize L.complexAntilinearPart 1 = b at hL ⊢
  generalize K.complexLinearPart 1 = p at hK ⊢
  generalize K.complexAntilinearPart 1 = q at hK ⊢
  simp only [complexAntilinearPart_apply, smul_apply, add_apply, comp_apply, smul_eq_mul, hL, hK,
    map_add, map_mul, map_neg, Complex.conj_I, neg_neg, map_one, Complex.real_smul]
  push_cast
  linear_combination (a - b + Complex.I * (p * a - q * a - conj p * b + conj q * b)) / 4 *
    Complex.I_sq

/-- **The `(0,1)`-projection for a complex structure, in Wirtinger form.** Let `K` be a real-linear
complex structure on `ℂ` with `K 1 ≠ -i`, and `p` the value at `1` of its complex-linear part.
For every real-linear `L : ℂ → ℂ`, the complex-antilinear part of `½ (L + i L K)` sends `v` to
`conj v · ½ (1 + i conj p) (∂bar L + μ ∂L)`, where `∂L = L.complexLinearPart 1`,
`∂bar L = L.complexAntilinearPart 1` and `μ = (K 1 - i) / (conj (K 1) - i)`. -/
theorem complexAntilinearPartL_half_smul_add_I_smul_comp_apply {K : ℂ →L[ℝ] ℂ}
    (hK : ∀ v, K (K v) = -v) (hK1 : K 1 ≠ -Complex.I) (L : ℂ →L[ℝ] ℂ) (v : ℂ) :
    complexAntilinearPartL ((2⁻¹ : ℝ) • (L + Complex.I • L.comp K)) v =
      conj v * (2⁻¹ * (1 + Complex.I * conj (K.complexLinearPart 1)) *
        (L.complexAntilinearPart 1 +
          (K 1 - Complex.I) / (conj (K 1) - Complex.I) * L.complexLinearPart 1)) := by
  rw [complexAntilinearPartL_apply_apply, ← complexAntilinearPart_apply]
  conv_lhs => rw [← mul_one v, ← smul_eq_mul, map_smulₛₗ, smul_eq_mul,
    complexAntilinearPart_half_smul_add_I_smul_comp_apply_one]
  have hμ := one_add_I_mul_conj_complexLinearPart_one_mul_div_eq hK hK1
  linear_combination (-2⁻¹ * conj v * L.complexLinearPart 1) * hμ

end ContinuousLinearMap

end
