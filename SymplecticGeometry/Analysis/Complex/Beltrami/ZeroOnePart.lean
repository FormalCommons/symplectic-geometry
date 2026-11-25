/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.ComplexLinearPart

/-!
# The `(0,1)`-projection of a complex structure on the plane, in Wirtinger form

A real-linear map `L : ℂ → ℂ` is `L v = a v + b conj v`, with `a = ∂L` and `b = ∂bar L` the values
at `1` of its complex-linear and complex-antilinear parts
(`ContinuousLinearMap.apply_eq_mul_add_conj_mul`). For a
second real-linear map `K`, write `p` and `q` for these values of `K`. The `(0,1)`-projection
`½ (L + i L K)` of `L` for `K` then has complex-antilinear part
`½ ((1 + i conj p) b + i q a)`
(`ContinuousLinearMap.complexAntilinearPart_half_smul_add_I_smul_comp_apply_one`),
for any `K`.

When `K` is a complex structure (`K ∘ K = -1`), `p` is purely imaginary and `p² = -1 - |q|²`
(`ContinuousLinearMap.conj_complexLinearPart_one_and_sq_of_apply_apply`). If moreover
`K 1 ≠ -i`, then `1 + i conj p ≠ 0`, and the quotient `i q / (1 + i conj p)` is
`μ = (K 1 - i) / (conj (K 1) - i)`, the negative of the Beltrami coefficient
`ν = (i - K 1) / (conj (K 1) - i)` of `K`
(`ContinuousLinearMap.one_add_I_mul_conj_complexLinearPart_one_mul_div_eq`). So the
`(0,1)`-projection for `K`, followed by the complex-antilinear part, sends `L` to
`c (∂bar L + μ ∂L)` with `c = ½ (1 + i conj p) ≠ 0`: this is the pointwise form of a
Cauchy–Riemann operator for `K` read against the standard structure of `ℂ`.

## References

* [D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*][McDuffSalamon2012],
  Appendix C.1.
-/

public section

open ComplexConjugate

namespace ContinuousLinearMap

/-- A real-linear map `Ψ : ℂ → ℂ` is `Ψ v = v a + conj v b`, where `a` and `b` are the values at
`1` of its complex-linear and complex-antilinear parts. -/
theorem apply_eq_mul_add_conj_mul (Ψ : ℂ →L[ℝ] ℂ) (v : ℂ) :
    Ψ v = v * Ψ.complexLinearPart 1 + conj v * Ψ.complexAntilinearPart 1 := by
  rw [← Ψ.complexLinearPart_add_complexAntilinearPart_apply v]
  congr 1
  · conv_lhs => rw [← mul_one v, ← smul_eq_mul, map_smul, smul_eq_mul]
  · conv_lhs => rw [← mul_one v, ← smul_eq_mul, map_smulₛₗ, smul_eq_mul]

/-- For a real-linear complex structure `K` on `ℂ`, the value `p` at `1` of its complex-linear
part is purely imaginary, and `p² = -1 - conj q * q` for the value `q` at `1` of its
complex-antilinear part. -/
theorem conj_complexLinearPart_one_and_sq_of_apply_apply {K : ℂ →L[ℝ] ℂ} (hK : ∀ v, K (K v) = -v) :
    conj (K.complexLinearPart 1) = -K.complexLinearPart 1 ∧
      K.complexLinearPart 1 ^ 2 = -1 - conj (K.complexAntilinearPart 1) *
        K.complexAntilinearPart 1 := by
  have h1 := hK 1
  have h2 := hK Complex.I
  have hK' := K.apply_eq_mul_add_conj_mul
  generalize K.complexLinearPart 1 = p at hK' ⊢
  generalize K.complexAntilinearPart 1 = q at hK' ⊢
  simp only [hK', map_add, map_mul, map_neg, Complex.conj_I, neg_neg, map_one, one_mul] at h1 h2
  have hp2 : p ^ 2 = -1 - conj q * q := by
    linear_combination (norm := skip) (1 / 2 : ℂ) * h1 + (-Complex.I / 2) * h2
    ring_nf; simp only [Complex.I_sq]; ring_nf
  refine ⟨?_, hp2⟩
  have := congrArg Complex.re hp2
  have h' := congrArg Complex.im hp2
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.neg_re, Complex.neg_im, Complex.one_re, Complex.one_im, Complex.conj_re,
    Complex.conj_im] at this h'
  have hx : p.re = 0 := by
    rcases mul_eq_zero.1 (show p.re * p.im = 0 by linarith) with h | h
    · exact h
    · rw [h] at this
      nlinarith [sq_nonneg p.re, sq_nonneg q.re, sq_nonneg q.im]
  apply Complex.ext <;> simp [hx]

/-- Let `K` be a real-linear complex structure on `ℂ` with `K 1 ≠ -i`, and let `p` and `q` be the
values at `1` of its complex-linear and complex-antilinear parts. Then `1 + i conj p ≠ 0`, and
`(1 + i conj p) μ = i q` for `μ = (K 1 - i) / (conj (K 1) - i)`, the negative of the Beltrami
coefficient of `K`. -/
theorem one_add_I_mul_conj_complexLinearPart_one_mul_div_eq {K : ℂ →L[ℝ] ℂ} (hK : ∀ v, K (K v) = -v)
    (hK1 : K 1 ≠ -Complex.I) :
    1 + Complex.I * conj (K.complexLinearPart 1) ≠ 0 ∧
    (1 + Complex.I * conj (K.complexLinearPart 1)) * ((K 1 - Complex.I) / (conj (K 1) - Complex.I))
      = Complex.I * K.complexAntilinearPart 1 := by
  obtain ⟨hc, hp2⟩ := conj_complexLinearPart_one_and_sq_of_apply_apply hK
  have hden : conj (K 1) - Complex.I ≠ 0 := by
    intro h
    apply hK1
    have : conj (K 1) = Complex.I := sub_eq_zero.1 h
    simpa using congrArg conj this
  rw [K.apply_eq_mul_add_conj_mul 1] at hK1 hden ⊢
  generalize K.complexLinearPart 1 = p at hc hp2 hK1 hden ⊢
  generalize K.complexAntilinearPart 1 = q at hc hp2 hK1 hden ⊢
  simp only [map_one, one_mul, map_add] at hK1 hden ⊢
  rw [hc] at hden ⊢
  refine ⟨fun h ↦ hK1 ?_, ?_⟩
  · have hp : p = -Complex.I := by
      linear_combination (norm := skip) Complex.I * h
      ring_nf; simp only [Complex.I_sq]; ring_nf
    have hq : conj q * q = 0 := by
      rw [hp] at hp2
      linear_combination (norm := skip) hp2
      ring_nf; simp only [Complex.I_sq]; ring_nf
    have hq0 : q = 0 := by
      rw [mul_comm, Complex.mul_conj] at hq
      exact Complex.normSq_eq_zero.1 (by exact_mod_cast hq)
    rw [hp, hq0, add_zero]
  · rw [mul_div_assoc', div_eq_iff hden]
    linear_combination (norm := skip) (-Complex.I) * hp2
    ring_nf; simp only [Complex.I_sq]; ring_nf
/-- For real-linear maps `L K : ℂ → ℂ`, the complex-antilinear part at `1` of `½ (L + i L K)`, the
`(0,1)`-projection of `L` for `K` when `K` is a complex structure, is
`½ ((1 + i conj p) b + i q a)`, where `a`, `b` are the values at `1` of the ℂ-linear and
ℂ-antilinear parts of `L` and `p`, `q` those of `K`. -/
theorem complexAntilinearPart_half_smul_add_I_smul_comp_apply_one (L K : ℂ →L[ℝ] ℂ) :
    ((2⁻¹ : ℝ) • (L + Complex.I • L.comp K)).complexAntilinearPart 1 =
      2⁻¹ * ((1 + Complex.I * conj (K.complexLinearPart 1)) * L.complexAntilinearPart 1 +
        Complex.I * K.complexAntilinearPart 1 * L.complexLinearPart 1) := by
  have hL := L.apply_eq_mul_add_conj_mul
  have hK := K.apply_eq_mul_add_conj_mul
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

end ContinuousLinearMap

end
