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

Under the same hypotheses, that complex-antilinear part vanishes exactly when `L` is complex
linear for `K`, `L ∘ K = i L`
(`ContinuousLinearMap.complexAntilinearPartL_half_smul_add_I_smul_comp_eq_zero_iff`): the
`(0,1)`-projection for `K` is complex antilinear for `K`, and a map that is complex linear for
`i` and antilinear for `K` vanishes when `K 1 ≠ -i`.

## References

* [D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*][McDuffSalamon2012],
  Appendix C.1.
-/

public section

open ComplexConjugate

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
  have hden : conj (K 1) - Complex.I ≠ 0 := fun h ↦ hK1 (by
    simpa using congrArg conj (sub_eq_zero.1 h))
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
    map_add, map_mul, Complex.conj_I, map_one, Complex.real_smul]
  push_cast
  ring_nf
  simp only [Complex.I_sq, Complex.I_pow_three, map_neg, Complex.conj_I, neg_neg]
  ring

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

/-- **Complex linearity for `K` from the `(0,1)`-projection.** Let `K` be a real-linear complex
structure on `ℂ` with `K 1 ≠ -i`. A real-linear `L : ℂ → ℂ` is complex linear for `K`, that is
`L (K v) = i L v` for all `v`, exactly when the `(0,1)`-projection `½ (L + i L K)` of `L` for `K`
has no complex-antilinear part.

Without `K 1 ≠ -i` this fails: for `K v = -i v` and `L = id`, the projection is `L` itself, which
is complex linear, but `L (K 1) = -i ≠ i L 1`. -/
theorem complexAntilinearPartL_half_smul_add_I_smul_comp_eq_zero_iff {K : ℂ →L[ℝ] ℂ}
    (hK : ∀ v, K (K v) = -v) (hK1 : K 1 ≠ -Complex.I) (L : ℂ →L[ℝ] ℂ) :
    complexAntilinearPartL ((2⁻¹ : ℝ) • (L + Complex.I • L.comp K)) = 0 ↔
      ∀ v, L (K v) = Complex.I • L v := by
  set N := (2⁻¹ : ℝ) • (L + Complex.I • L.comp K)
  have hNv (v : ℂ) : N v = (2⁻¹ : ℝ) • (L v + Complex.I • L (K v)) := rfl
  rw [complexAntilinearPartL_eq_zero_iff]
  constructor
  · intro h
    -- `N` is complex linear, so `N v = v N 1`.
    have hlin (v : ℂ) : N v = v * N 1 := by
      conv_lhs => rw [← Complex.re_add_im v]
      rw [show (v.re : ℂ) + v.im * Complex.I = v.re • (1 : ℂ) + v.im • (Complex.I • 1) by
        simp [Complex.real_smul]]
      rw [map_add, map_smul, map_smul, h, smul_eq_mul, Complex.real_smul, Complex.real_smul]
      conv_rhs => rw [← Complex.re_add_im v]
      ring
    -- `N` is complex antilinear for `K`: `N (K 1) = -i N 1`.
    have hNK : N (K 1) = -Complex.I * N 1 := by
      rw [hNv, hNv, hK]
      simp only [map_neg, smul_eq_mul, Complex.real_smul]
      push_cast
      linear_combination (2⁻¹ : ℂ) * L (K 1) * Complex.I_sq
    -- So `(K 1 + i) N 1 = 0`, and `N = 0` since `K 1 ≠ -i`.
    have h1 : N 1 = 0 := by
      have : (K 1 + Complex.I) * N 1 = 0 := by rw [add_mul, ← hlin, hNK]; ring
      exact (mul_eq_zero.1 this).resolve_left fun h ↦ hK1 (eq_neg_of_add_eq_zero_left h)
    intro v
    have h0 := hlin v
    rw [h1, mul_zero, hNv, Complex.real_smul, mul_eq_zero] at h0
    have h0 := h0.resolve_left (by norm_num)
    rw [smul_eq_mul]
    linear_combination (-Complex.I) * h0 + L (K v) * Complex.I_sq
  · intro h v
    have hz (v : ℂ) : N v = 0 := by
      rw [hNv, h, smul_smul, Complex.I_mul_I, neg_one_smul, add_neg_cancel, smul_zero]
    rw [hz, hz, smul_zero]

end ContinuousLinearMap

end
