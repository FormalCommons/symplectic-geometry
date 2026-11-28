/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.InnerProductSpace.Rayleigh
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Sqrt
import TauCeti.Analysis.Matrix.EuclideanLin
import TauCeti.Analysis.Matrix.Exponential.EuclideanCLM
import TauCeti.Analysis.Normed.Operator.Exponential
import TauCeti.LinearAlgebra.Basis.Diagonal
import SymplecticGeometry.Analysis.Matrix.Spectrum
import SymplecticGeometry.Analysis.SpecificLimits.ExpWeightedMean

/-!
# The exponential curve of a Hermitian matrix

For a Hermitian matrix `A` over `ℝ` or `ℂ` and a vector `x` of `EuclideanSpace 𝕜 n`, this file
describes the curve `w t = toEuclideanLin (exp (t • A)) x`, `t : ℝ`, in the orthonormal
eigenvector basis `hA.eigenvectorBasis` of `A`: its coordinates are those of `x` multiplied by
`Real.exp (t * λ i)`, `λ = hA.eigenvalues`. So `‖w t‖ ^ 2` is a sum of exponentials, and the
Rayleigh quotient `(toEuclideanCLM A).rayleighQuotient (w t)` is the mean of the eigenvalues
weighted by `exp (2 t λ i) ‖x_i‖ ^ 2`, `x_i` the coordinates of `x`. As `t → ∞` it tends to the
largest eigenvalue `λ i` with `x_i ≠ 0` (`Real.tendsto_sum_mul_exp_div_sum_exp`). If all those
eigenvalues are negative, `w t` decreases in norm and tends to `0`, and
`Matrix.IsHermitian.mem_iSup_eigenspace` places `x` in the sum of the eigenspaces of negative
eigenvalues. This is the linear algebra of [GeorgoulasRobbinSalamon2021], Lemma 8.4.

On an eigenvector the exponential acts by the exponential of the eigenvalue: this is Tau Ceti's
`ContinuousLinearMap.exp_apply_of_apply_eq_smul`, read on matrices through
`Matrix.toEuclideanCLM_exp`. The coordinate formula follows Tau Ceti's
`LinearMap.IsSymmetric.eigenvectorBasis_repr_flow_neg_apply` (`TauCeti/Analysis/ODE/Linear.lean`),
proved there for a symmetric operator on a real inner product space: here the field is `ℝ` or
`ℂ`, and the operator is a matrix.

## Main results

* `Matrix.IsHermitian.toEuclideanLin_exp_smul_eigenvectorBasis`: `exp (t • A)` acts on the
  `i`-th eigenvector by `Real.exp (t * λ i)`.
* `Matrix.IsHermitian.repr_toEuclideanLin_exp_smul`: the coordinates of `w t` in the
  eigenvector basis.
* `Matrix.IsHermitian.norm_sq_toEuclideanLin_exp_smul`,
  `Matrix.IsHermitian.re_inner_toEuclideanLin_exp_smul`: `‖w t‖ ^ 2` and `re ⟪A (w t), w t⟫`
  as sums of exponentials.
* `Matrix.IsHermitian.tendsto_rayleighQuotient_toEuclideanLin_exp_smul`: the Rayleigh quotient
  of `A` along `w t` tends to the largest eigenvalue on which `x` has a nonzero coordinate.
* `Matrix.IsHermitian.antitone_norm_toEuclideanLin_exp_smul`,
  `Matrix.IsHermitian.tendsto_toEuclideanLin_exp_smul_zero`: if those eigenvalues are `≤ 0`,
  `‖w t‖` is antitone; if they are `< 0`, `w t → 0`.

## References

* [V. Georgoulas, J. W. Robbin, D. A. Salamon, *The moment-weight inequality and the
  Hilbert–Mumford criterion*][GeorgoulasRobbinSalamon2021], Lemma 8.4.
-/

public section

open NormedSpace Filter Finset
open scoped Topology InnerProductSpace

namespace Matrix.IsHermitian

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜] {A : Matrix n n 𝕜}
  (hA : A.IsHermitian)
include hA

/-- On the `i`-th vector of the eigenvector basis of a Hermitian matrix `A`, `exp (t • A)` acts
by `Real.exp (t * hA.eigenvalues i)`. -/
theorem toEuclideanLin_exp_smul_eigenvectorBasis (t : ℝ) (i : n) :
    toEuclideanLin (NormedSpace.exp (t • A)) (hA.eigenvectorBasis i) =
      (Real.exp (t * hA.eigenvalues i) : 𝕜) • hA.eigenvectorBasis i := by
  rw [← toEuclideanCLM_apply, toEuclideanCLM_exp,
    ContinuousLinearMap.exp_apply_of_apply_eq_smul _ (μ := ((t * hA.eigenvalues i : ℝ) : 𝕜))]
  · rw [Real.exp_eq_exp_ℝ, ← RCLike.algebraMap_eq_ofReal, algebraMap_exp_comm]
  · rw [toEuclideanCLM_apply, RCLike.real_smul_eq_coe_smul (K := 𝕜) t A, map_smul,
      LinearMap.smul_apply, hA.toEuclideanLin_eigenvectorBasis, smul_smul, RCLike.ofReal_mul]

/-- The coordinates of `exp (t • A) x` in the eigenvector basis of a Hermitian matrix `A` are
those of `x` multiplied by `Real.exp (t * hA.eigenvalues i)`. -/
theorem repr_toEuclideanLin_exp_smul (t : ℝ) (x : EuclideanSpace 𝕜 n) (i : n) :
    hA.eigenvectorBasis.repr (toEuclideanLin (NormedSpace.exp (t • A)) x) i =
      Real.exp (t * hA.eigenvalues i) * hA.eigenvectorBasis.repr x i := by
  simpa using hA.eigenvectorBasis.toBasis.repr_apply_eq_mul_of_apply_eq_smul
    hA.eigenvectorBasis.toBasis (g := toEuclideanLin (NormedSpace.exp (t • A)))
    (w := fun j ↦ (Real.exp (t * hA.eigenvalues j) : 𝕜))
    (fun j ↦ by rw [OrthonormalBasis.coe_toBasis, hA.toEuclideanLin_exp_smul_eigenvectorBasis])
    x i

/-- The squared coordinates of `exp (t • A) x` in the eigenvector basis of a Hermitian matrix `A`
are those of `x` multiplied by `Real.exp (2 * t * hA.eigenvalues i)`. -/
theorem norm_repr_toEuclideanLin_exp_smul_sq (t : ℝ) (x : EuclideanSpace 𝕜 n) (i : n) :
    ‖hA.eigenvectorBasis.repr (toEuclideanLin (NormedSpace.exp (t • A)) x) i‖ ^ 2 =
      Real.exp (2 * t * hA.eigenvalues i) * ‖hA.eigenvectorBasis.repr x i‖ ^ 2 := by
  rw [repr_toEuclideanLin_exp_smul, norm_mul, mul_pow, RCLike.norm_ofReal,
    abs_of_pos (Real.exp_pos _), ← Real.exp_natCast_mul]
  ring_nf

/-- Along the exponential curve of a Hermitian matrix `A`, the squared norm is a sum of
exponentials: `‖exp (t • A) x‖ ^ 2 = ∑ i, exp (2 t λ i) ‖x_i‖ ^ 2`, with `λ i` the eigenvalues
and `x_i` the coordinates of `x` in the eigenvector basis. -/
theorem norm_sq_toEuclideanLin_exp_smul (t : ℝ) (x : EuclideanSpace 𝕜 n) :
    ‖toEuclideanLin (NormedSpace.exp (t • A)) x‖ ^ 2 =
      ∑ i, Real.exp (2 * t * hA.eigenvalues i) * ‖hA.eigenvectorBasis.repr x i‖ ^ 2 := by
  rw [← hA.eigenvectorBasis.repr.norm_map, EuclideanSpace.norm_sq_eq]
  exact sum_congr rfl fun i _ ↦ hA.norm_repr_toEuclideanLin_exp_smul_sq t x i

/-- Along the exponential curve of a Hermitian matrix `A`, the quadratic form of `A` is a sum of
exponentials: `re ⟪A (exp (t • A) x), exp (t • A) x⟫ = ∑ i, λ i exp (2 t λ i) ‖x_i‖ ^ 2`, with
`λ i` the eigenvalues and `x_i` the coordinates of `x` in the eigenvector basis. -/
theorem re_inner_toEuclideanLin_exp_smul (t : ℝ) (x : EuclideanSpace 𝕜 n) :
    RCLike.re ⟪toEuclideanLin A (toEuclideanLin (NormedSpace.exp (t • A)) x),
        toEuclideanLin (NormedSpace.exp (t • A)) x⟫_𝕜 =
      ∑ i, hA.eigenvalues i * Real.exp (2 * t * hA.eigenvalues i) *
        ‖hA.eigenvectorBasis.repr x i‖ ^ 2 := by
  rw [hA.re_inner_toEuclideanLin_self]
  exact sum_congr rfl fun i _ ↦ by rw [hA.norm_repr_toEuclideanLin_exp_smul_sq, ← mul_assoc]

/-- **The Rayleigh quotient along the exponential curve of a Hermitian matrix.** If `a` is the
largest eigenvalue `hA.eigenvalues i` among those with `x_i ≠ 0`, `x_i` the coordinates of `x`
in the eigenvector basis, then the Rayleigh quotient of `A` at `exp (t • A) x` tends to `a` as
`t → ∞`. -/
theorem tendsto_rayleighQuotient_toEuclideanLin_exp_smul {x : EuclideanSpace 𝕜 n} {a : ℝ}
    (hle : ∀ i, hA.eigenvectorBasis.repr x i ≠ 0 → hA.eigenvalues i ≤ a)
    (ha : ∃ i, hA.eigenvectorBasis.repr x i ≠ 0 ∧ hA.eigenvalues i = a) :
    Tendsto (fun t : ℝ ↦ (toEuclideanCLM (n := n) (𝕜 := 𝕜) A).rayleighQuotient
      (toEuclideanLin (NormedSpace.exp (t • A)) x)) atTop (𝓝 a) := by
  have h := (Real.tendsto_sum_mul_exp_div_sum_exp
    (p := fun i ↦ ‖hA.eigenvectorBasis.repr x i‖ ^ 2)
    (c := hA.eigenvalues) (fun i ↦ by positivity) (by simpa using hle)
    (by simpa using ha)).comp (tendsto_id.const_mul_atTop two_pos)
  refine h.congr fun t ↦ ?_
  rw [Function.comp_apply, id, ContinuousLinearMap.rayleighQuotient,
    ContinuousLinearMap.reApplyInnerSelf_apply, toEuclideanCLM_apply,
    hA.re_inner_toEuclideanLin_exp_smul, hA.norm_sq_toEuclideanLin_exp_smul]
  congr 1 <;> exact sum_congr rfl fun i _ ↦ by ring

/-- The Rayleigh quotient of a Hermitian matrix `A` at `exp (t • A) x` tends to the largest
eigenvalue `hA.eigenvalues i` with `x_i ≠ 0`, `x_i` the coordinates of `x` in the eigenvector
basis. -/
theorem tendsto_rayleighQuotient_toEuclideanLin_exp_smul_sup' {x : EuclideanSpace 𝕜 n}
    (hs : {i | hA.eigenvectorBasis.repr x i ≠ 0}.toFinset.Nonempty) :
    Tendsto (fun t : ℝ ↦ (toEuclideanCLM (n := n) (𝕜 := 𝕜) A).rayleighQuotient
      (toEuclideanLin (NormedSpace.exp (t • A)) x)) atTop
      (𝓝 ({i | hA.eigenvectorBasis.repr x i ≠ 0}.toFinset.sup' hs hA.eigenvalues)) := by
  obtain ⟨j, hj, hja⟩ := exists_mem_eq_sup' hs hA.eigenvalues
  exact hA.tendsto_rayleighQuotient_toEuclideanLin_exp_smul
    (fun i hi ↦ le_sup' hA.eigenvalues (by simpa using hi)) ⟨j, by simpa using hj, hja.symm⟩

/-- If every eigenvalue `hA.eigenvalues i` with `x_i ≠ 0` is `≤ 0`, `x_i` the coordinates of `x`
in the eigenvector basis of a Hermitian matrix `A`, then `t ↦ ‖exp (t • A) x‖` is antitone. -/
theorem antitone_norm_toEuclideanLin_exp_smul {x : EuclideanSpace 𝕜 n}
    (hle : ∀ i, hA.eigenvectorBasis.repr x i ≠ 0 → hA.eigenvalues i ≤ 0) :
    Antitone fun t : ℝ ↦ ‖toEuclideanLin (NormedSpace.exp (t • A)) x‖ := by
  intro s t hst
  rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero,
    hA.norm_sq_toEuclideanLin_exp_smul, hA.norm_sq_toEuclideanLin_exp_smul]
  refine sum_le_sum fun i _ ↦ ?_
  by_cases h : hA.eigenvectorBasis.repr x i = 0
  · simp [h]
  have := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hst) (hle i h)
  have h2 : 2 * t * hA.eigenvalues i ≤ 2 * s * hA.eigenvalues i := by nlinarith
  exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr h2) (sq_nonneg _)

/-- If every eigenvalue `hA.eigenvalues i` with `x_i ≠ 0` is negative, `x_i` the coordinates of
`x` in the eigenvector basis of a Hermitian matrix `A`, then `exp (t • A) x → 0` as `t → ∞`. -/
theorem tendsto_toEuclideanLin_exp_smul_zero {x : EuclideanSpace 𝕜 n}
    (hlt : ∀ i, hA.eigenvectorBasis.repr x i ≠ 0 → hA.eigenvalues i < 0) :
    Tendsto (fun t : ℝ ↦ toEuclideanLin (NormedSpace.exp (t • A)) x) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hsq : Tendsto (fun t : ℝ ↦ ‖toEuclideanLin (NormedSpace.exp (t • A)) x‖ ^ 2) atTop
      (𝓝 0) := by
    simp only [hA.norm_sq_toEuclideanLin_exp_smul]
    rw [show (𝓝 (0 : ℝ)) = 𝓝 (∑ _i : n, (0 : ℝ)) by simp]
    refine tendsto_finsetSum _ fun i _ ↦ ?_
    by_cases h : hA.eigenvectorBasis.repr x i = 0
    · simp [h]
    have he := (tendsto_id.const_mul_atTop two_pos).atTop_mul_const_of_neg (hlt i h)
    simpa using (Real.tendsto_exp_atBot.comp he).mul_const (‖hA.eigenvectorBasis.repr x i‖ ^ 2)
  simpa [Function.comp_def, Real.sqrt_sq_eq_abs] using (Real.continuous_sqrt.tendsto 0).comp hsq

end Matrix.IsHermitian

end
