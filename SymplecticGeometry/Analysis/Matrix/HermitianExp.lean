/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Sqrt
import TauCeti.Analysis.Normed.Algebra.MatrixExponential
import SymplecticGeometry.Analysis.SpecificLimits.ExpWeightedMean

/-!
# The exponential curve of a Hermitian matrix

For a Hermitian matrix `A` over `ℝ` or `ℂ` and a vector `x` of `EuclideanSpace 𝕜 n`, this file
describes the curve `w t = toEuclideanLin (exp (t • A)) x`, `t : ℝ`, in the orthonormal
eigenvector basis `hA.eigenvectorBasis` of `A`: its coordinates are those of `x` multiplied by
`Real.exp (t * λ i)`, `λ = hA.eigenvalues`. So `‖w t‖ ^ 2` is a sum of exponentials, and the
Rayleigh quotient `re ⟪w t, A (w t)⟫ / ‖w t‖ ^ 2` is the mean of the eigenvalues weighted by
`exp (2 t λ i) ‖x_i‖ ^ 2`, `x_i` the coordinates of `x`. As `t → ∞` it tends to the largest
eigenvalue `λ i` with `x_i ≠ 0` (`Real.tendsto_sum_mul_exp_div_sum_exp`). If all those
eigenvalues are negative, `x` lies in the sum of the eigenspaces of negative eigenvalues, and
`w t` decreases in norm and tends to `0`. This is the linear algebra of
[GeorgoulasRobbinSalamon2021], Lemma 8.4.

The exponential acts on an eigenvector `x` of a matrix `M`, `M *ᵥ x = μ • x`, by `exp μ`
(`Matrix.exp_mulVec_of_mulVec_eq_smul`), the matrix form of Tau Ceti's
`ContinuousLinearMap.exp_apply_of_apply_eq_smul`. It is proved by writing `M` as the scalar
matrix `μ` plus a matrix that kills `x`, which Tau Ceti's
`Matrix.exp_mulVec_eq_self_of_mulVec_eq_zero` handles.

The coordinate formula follows Tau Ceti's
`LinearMap.IsSymmetric.eigenvectorBasis_repr_flow_neg_apply` (`TauCeti/Analysis/ODE/Linear.lean`),
proved there for a symmetric operator on a real inner product space: here the field is `ℝ` or
`ℂ`, and the operator is a matrix.

## Main results

* `Matrix.exp_mulVec_of_mulVec_eq_smul`: `exp M *ᵥ x = exp μ • x` if `M *ᵥ x = μ • x`.
* `Matrix.IsHermitian.repr_toEuclideanLin_exp_smul`: the coordinates of `w t` in the
  eigenvector basis.
* `Matrix.IsHermitian.norm_sq_toEuclideanLin_exp_smul`,
  `Matrix.IsHermitian.re_inner_toEuclideanLin_exp_smul`: `‖w t‖ ^ 2` and `re ⟪w t, A (w t)⟫`
  as sums of exponentials.
* `Matrix.IsHermitian.tendsto_rayleigh_toEuclideanLin_exp_smul`: the Rayleigh quotient along
  `w t` tends to the largest eigenvalue on which `x` has a nonzero coordinate.
* `Matrix.IsHermitian.antitone_norm_toEuclideanLin_exp_smul`,
  `Matrix.IsHermitian.tendsto_toEuclideanLin_exp_smul_zero`: if those eigenvalues are `≤ 0`,
  `‖w t‖` is antitone; if they are `< 0`, `w t → 0`.
* `Matrix.IsHermitian.mem_iSup_eigenspace`: if those eigenvalues lie in a set `S`, `x` lies in
  the sum of the eigenspaces of the eigenvalues in `S`.

## References

* [V. Georgoulas, J. W. Robbin, D. A. Salamon, *The moment-weight inequality and the
  Hilbert–Mumford criterion*][GeorgoulasRobbinSalamon2021], Lemma 8.4.
-/

public section

open NormedSpace Filter Finset
open scoped Topology InnerProductSpace

namespace Matrix

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]

/-- The exponential of a matrix acts on an eigenvector of eigenvalue `μ` by `exp μ`. -/
theorem exp_mulVec_of_mulVec_eq_smul {M : Matrix n n 𝕜} {x : n → 𝕜} {μ : 𝕜}
    (hx : M *ᵥ x = μ • x) : exp M *ᵥ x = exp μ • x := by
  have hN : (M - scalar n μ) *ᵥ x = 0 := by
    rw [sub_mulVec, hx, scalar_apply]
    ext i; simp
  rw [← add_sub_cancel (scalar n μ) M,
    exp_add_of_commute _ _ (scalar_commute μ (fun _ ↦ Commute.all _ _) _), ← mulVec_mulVec,
    exp_mulVec_eq_self_of_mulVec_eq_zero hN, scalar_apply, exp_diagonal]
  ext i; simp [mulVec_diagonal, Pi.coe_exp]

namespace IsHermitian

variable {A : Matrix n n 𝕜} (hA : A.IsHermitian)

/-- On the `i`-th eigenvector of a Hermitian matrix `A`, `exp (t • A)` acts by
`Real.exp (t * hA.eigenvalues i)`. -/
theorem exp_smul_mulVec_eigenvectorBasis (t : ℝ) (i : n) :
    NormedSpace.exp (t • A) *ᵥ ⇑(hA.eigenvectorBasis i) =
      (Real.exp (t * hA.eigenvalues i) : 𝕜) • ⇑(hA.eigenvectorBasis i) := by
  rw [exp_mulVec_of_mulVec_eq_smul (μ := ((t * hA.eigenvalues i : ℝ) : 𝕜))]
  · rw [Real.exp_eq_exp_ℝ, ← RCLike.algebraMap_eq_ofReal, algebraMap_exp_comm]
  · rw [smul_mulVec, hA.mulVec_eigenvectorBasis, smul_smul,
      RCLike.real_smul_eq_coe_smul (K := 𝕜), RCLike.ofReal_mul]

/-- If a matrix `M` acts on each vector of the eigenvector basis of `A` by a scalar `f i`, it
multiplies the coordinates in that basis by `f i`. -/
theorem repr_toEuclideanLin_of_mulVec_eigenvectorBasis {M : Matrix n n 𝕜} {f : n → 𝕜}
    (hM : ∀ i, M *ᵥ ⇑(hA.eigenvectorBasis i) = f i • ⇑(hA.eigenvectorBasis i))
    (x : EuclideanSpace 𝕜 n) (i : n) :
    hA.eigenvectorBasis.repr (toEuclideanLin M x) i = f i * hA.eigenvectorBasis.repr x i := by
  have hx : toEuclideanLin M x =
      ∑ j, (f j * hA.eigenvectorBasis.repr x j) • hA.eigenvectorBasis j := by
    conv_lhs => rw [← hA.eigenvectorBasis.sum_repr x]
    refine (map_sum _ _ _).trans (sum_congr rfl fun j _ ↦ ?_)
    rw [map_smul, mul_comm, ← smul_smul, toLpLin_apply, WithLp.ofLp_toLp]
    rw [hM, WithLp.toLp_smul, WithLp.toLp_ofLp]
  simp [hx, map_sum, map_smul, OrthonormalBasis.repr_self, Pi.single_apply]

/-- The coordinates of `exp (t • A) x` in the eigenvector basis of a Hermitian matrix `A` are
those of `x` multiplied by `Real.exp (t * hA.eigenvalues i)`. -/
theorem repr_toEuclideanLin_exp_smul (t : ℝ) (x : EuclideanSpace 𝕜 n) (i : n) :
    hA.eigenvectorBasis.repr (toEuclideanLin (NormedSpace.exp (t • A)) x) i =
      Real.exp (t * hA.eigenvalues i) * hA.eigenvectorBasis.repr x i :=
  hA.repr_toEuclideanLin_of_mulVec_eigenvectorBasis (hA.exp_smul_mulVec_eigenvectorBasis t) x i

/-- The coordinates of `A x` in the eigenvector basis of a Hermitian matrix `A` are those of `x`
multiplied by the eigenvalues. -/
theorem repr_toEuclideanLin (x : EuclideanSpace 𝕜 n) (i : n) :
    hA.eigenvectorBasis.repr (toEuclideanLin A x) i =
      hA.eigenvalues i * hA.eigenvectorBasis.repr x i :=
  hA.repr_toEuclideanLin_of_mulVec_eigenvectorBasis
    (fun j ↦ by rw [hA.mulVec_eigenvectorBasis, RCLike.real_smul_eq_coe_smul (K := 𝕜)]) x i

/-- Along the exponential curve of a Hermitian matrix `A`, the squared norm is a sum of
exponentials: `‖exp (t • A) x‖ ^ 2 = ∑ i, exp (2 t λ i) ‖x_i‖ ^ 2`, with `λ i` the eigenvalues
and `x_i` the coordinates of `x` in the eigenvector basis. -/
theorem norm_sq_toEuclideanLin_exp_smul (t : ℝ) (x : EuclideanSpace 𝕜 n) :
    ‖toEuclideanLin (NormedSpace.exp (t • A)) x‖ ^ 2 =
      ∑ i, Real.exp (2 * t * hA.eigenvalues i) * ‖hA.eigenvectorBasis.repr x i‖ ^ 2 := by
  rw [← hA.eigenvectorBasis.repr.norm_map, EuclideanSpace.norm_sq_eq]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [repr_toEuclideanLin_exp_smul, norm_mul, mul_pow, RCLike.norm_ofReal,
    abs_of_pos (Real.exp_pos _), ← Real.exp_natCast_mul]
  ring_nf

/-- Along the exponential curve of a Hermitian matrix `A`, the numerator of the Rayleigh
quotient is a sum of exponentials:
`re ⟪exp (t • A) x, A (exp (t • A) x)⟫ = ∑ i, λ i exp (2 t λ i) ‖x_i‖ ^ 2`. -/
theorem re_inner_toEuclideanLin_exp_smul (t : ℝ) (x : EuclideanSpace 𝕜 n) :
    RCLike.re ⟪toEuclideanLin (NormedSpace.exp (t • A)) x,
        toEuclideanLin A (toEuclideanLin (NormedSpace.exp (t • A)) x)⟫_𝕜 =
      ∑ i, hA.eigenvalues i * Real.exp (2 * t * hA.eigenvalues i) *
        ‖hA.eigenvectorBasis.repr x i‖ ^ 2 := by
  rw [← hA.eigenvectorBasis.repr.inner_map_map, PiLp.inner_apply, map_sum]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [repr_toEuclideanLin, repr_toEuclideanLin_exp_smul]
  set z := hA.eigenvectorBasis.repr x i
  have he : Real.exp (2 * t * hA.eigenvalues i) = Real.exp (t * hA.eigenvalues i) ^ 2 := by
    rw [← Real.exp_natCast_mul]; ring_nf
  rw [RCLike.inner_apply', map_mul (starRingEnd 𝕜), RCLike.conj_ofReal, he,
    show (Real.exp (t * hA.eigenvalues i) : 𝕜) * (starRingEnd 𝕜) z *
        (hA.eigenvalues i * (Real.exp (t * hA.eigenvalues i) * z)) =
      ((hA.eigenvalues i * Real.exp (t * hA.eigenvalues i) ^ 2 : ℝ) : 𝕜) *
        ((starRingEnd 𝕜) z * z) by push_cast; ring,
    RCLike.conj_mul, ← RCLike.ofReal_pow, ← RCLike.ofReal_mul, RCLike.ofReal_re]

/-- **The Rayleigh quotient along the exponential curve of a Hermitian matrix.** If `a` is the
largest eigenvalue `hA.eigenvalues i` among those with `x_i ≠ 0`, `x_i` the coordinates of `x`
in the eigenvector basis, then `re ⟪w t, A (w t)⟫ / ‖w t‖ ^ 2 → a` as `t → ∞`, for
`w t = exp (t • A) x`. -/
theorem tendsto_rayleigh_toEuclideanLin_exp_smul {x : EuclideanSpace 𝕜 n} {a : ℝ}
    (hle : ∀ i, hA.eigenvectorBasis.repr x i ≠ 0 → hA.eigenvalues i ≤ a)
    (ha : ∃ i, hA.eigenvectorBasis.repr x i ≠ 0 ∧ hA.eigenvalues i = a) :
    Tendsto (fun t : ℝ ↦ RCLike.re ⟪toEuclideanLin (NormedSpace.exp (t • A)) x,
        toEuclideanLin A (toEuclideanLin (NormedSpace.exp (t • A)) x)⟫_𝕜 /
          ‖toEuclideanLin (NormedSpace.exp (t • A)) x‖ ^ 2) atTop (𝓝 a) := by
  have h := (Real.tendsto_sum_mul_exp_div_sum_exp (p := fun i ↦ ‖hA.eigenvectorBasis.repr x i‖ ^ 2)
    (c := hA.eigenvalues) (fun i ↦ by positivity) (by simpa using hle)
    (by simpa using ha)).comp (tendsto_id.const_mul_atTop two_pos)
  refine h.congr fun t ↦ ?_
  dsimp only [Function.comp_apply, id]
  rw [hA.re_inner_toEuclideanLin_exp_smul, hA.norm_sq_toEuclideanLin_exp_smul]
  congr 1 <;> exact sum_congr rfl fun i _ ↦ by ring

/-- The Rayleigh quotient along the exponential curve `exp (t • A) x` of a Hermitian matrix `A`
tends to the largest eigenvalue `hA.eigenvalues i` with `x_i ≠ 0`, `x_i` the coordinates of `x`
in the eigenvector basis. -/
theorem tendsto_rayleigh_toEuclideanLin_exp_smul_sup' {x : EuclideanSpace 𝕜 n}
    (hs : {i | hA.eigenvectorBasis.repr x i ≠ 0}.toFinset.Nonempty) :
    Tendsto (fun t : ℝ ↦ RCLike.re ⟪toEuclideanLin (NormedSpace.exp (t • A)) x,
        toEuclideanLin A (toEuclideanLin (NormedSpace.exp (t • A)) x)⟫_𝕜 /
          ‖toEuclideanLin (NormedSpace.exp (t • A)) x‖ ^ 2) atTop
      (𝓝 ({i | hA.eigenvectorBasis.repr x i ≠ 0}.toFinset.sup' hs hA.eigenvalues)) := by
  obtain ⟨j, hj, hja⟩ := exists_mem_eq_sup' hs hA.eigenvalues
  exact hA.tendsto_rayleigh_toEuclideanLin_exp_smul
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

/-- If every eigenvalue `hA.eigenvalues i` with `x_i ≠ 0` lies in `S`, `x_i` the coordinates of
`x` in the eigenvector basis of a Hermitian matrix `A`, then `x` lies in the sum of the
eigenspaces of `A` for the eigenvalues in `S`. -/
theorem mem_iSup_eigenspace {S : Set ℝ} {x : EuclideanSpace 𝕜 n}
    (hS : ∀ i, hA.eigenvectorBasis.repr x i ≠ 0 → hA.eigenvalues i ∈ S) :
    x ∈ ⨆ μ ∈ S, Module.End.eigenspace (toEuclideanLin A) (μ : 𝕜) := by
  rw [← hA.eigenvectorBasis.sum_repr x]
  refine Submodule.sum_mem _ fun i _ ↦ ?_
  by_cases h : hA.eigenvectorBasis.repr x i = 0
  · simp [h]
  refine Submodule.smul_mem _ _ (Submodule.mem_iSup_of_mem (hA.eigenvalues i)
    (Submodule.mem_iSup_of_mem (hS i h) ?_))
  rw [Module.End.mem_eigenspace_iff, toLpLin_apply, hA.mulVec_eigenvectorBasis,
    RCLike.real_smul_eq_coe_smul (K := 𝕜), WithLp.toLp_smul, WithLp.toLp_ofLp]

end IsHermitian

end Matrix

end
