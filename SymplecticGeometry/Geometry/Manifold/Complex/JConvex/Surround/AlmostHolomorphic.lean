/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import TauCeti.Analysis.Complex.Wirtinger.Basic
public import TauCeti.Analysis.InnerProductSpace.Euclidean.Complex

import Mathlib.Analysis.Analytic.CPolynomial
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import TauCeti.Analysis.Calculus.IteratedFDeriv.SymmetricFinite

/-!
# Almost holomorphic Taylor extensions

For a finite type `ι'`, write a point `z` of `EuclideanSpace ℂ ι'` as `x + i y`, with `x` and
`y` in `EuclideanSpace ℝ ι'` the two components of Tau Ceti's
`TauCeti.complexEuclideanEquivRealProd ι' z`. For a map `f : EuclideanSpace ℝ ι' → W` into a
complex normed space, the truncated Taylor extension of order `N` is
`taylorExtension N f (x + i y) = ∑_{j ≤ N} (i ^ j / j!) • D^j f(x) (y, …, y)`,
the Taylor polynomial of `f` at `x`, of order `N`, evaluated at the imaginary increment `i y`.
It is the classical almost analytic extension of `f`, truncated at order `N`, and it restricts
to `f` on the real points.

## Main definitions and results

* `SymplecticGeometry.taylorExtension N f`: the truncated Taylor extension of `f`
  (`SymplecticGeometry.taylorExtension_def`);
* `SymplecticGeometry.taylorExtension_ofReal`: on a real point `x + i 0` it equals `f x`;
* `SymplecticGeometry.taylorExtension_zero`: of order zero, it is `f` applied to the real part;
* `SymplecticGeometry.contDiff_taylorExtension`: if `f` is `C^(r + N)`, then
  `taylorExtension N f` is `C^r` over `ℝ`;
* `SymplecticGeometry.fderiv_taylorExtension_apply_real`,
  `SymplecticGeometry.fderiv_taylorExtension_apply_imag`: its real derivative at `x + i y` in a
  real direction `u` and in the imaginary direction `i u`, for `f` of class `C^(N + 1)`;
* `SymplecticGeometry.conjWirtingerDeriv_taylorExtension_apply_real`: in a real direction `u`,
  the conjugate Wirtinger derivative of `taylorExtension N f` at `x + i y` is
  `(2⁻¹ * i ^ N / N!) • D^(N+1) f(x) (u, y, …, y)`, so it vanishes to order `N` on the real
  points.

The last formula is the standard computation for almost analytic extensions: the derivative in
the direction `i u` shifts the order of each term down by one, by the symmetry of the iterated
derivatives of `f` (Tau Ceti's `ContDiffAt.iteratedFDeriv_comp_perm_of_le`), so that in
`Df(z) u + i • Df(z) (i u)` every term but the one with `D^(N+1) f` cancels.

## References

* [K. Cieliebak, Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012]:
  the proof of Proposition 5.55 builds its charts from such extensions.
-/

public section

namespace SymplecticGeometry

open TauCeti

variable {ι' : Type*} [Fintype ι'] {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- The truncated Taylor extension of order `N` of `f : ℝⁿ → W` to `ℂⁿ`: at `z = x + i y` it is
`∑_{j ≤ N} (i ^ j / j!) • D^j f(x) (y, …, y)`, the Taylor polynomial of `f` at `x` of order `N`
evaluated at the increment `i y`. -/
noncomputable def taylorExtension (N : ℕ) (f : EuclideanSpace ℝ ι' → W)
    (z : EuclideanSpace ℂ ι') : W :=
  ∑ j ∈ Finset.range (N + 1), (Complex.I ^ j / j.factorial) •
    iteratedFDeriv ℝ j f (complexEuclideanEquivRealProd ι' z).1
      (fun _ ↦ (complexEuclideanEquivRealProd ι' z).2)

theorem taylorExtension_def (N : ℕ) (f : EuclideanSpace ℝ ι' → W) (z : EuclideanSpace ℂ ι') :
    taylorExtension N f z = ∑ j ∈ Finset.range (N + 1), (Complex.I ^ j / j.factorial) •
      iteratedFDeriv ℝ j f (complexEuclideanEquivRealProd ι' z).1
        (fun _ ↦ (complexEuclideanEquivRealProd ι' z).2) :=
  (rfl)

/-- On a real point `x + i 0`, the truncated Taylor extension of `f` is `f x`. -/
@[simp]
theorem taylorExtension_ofReal (N : ℕ) (f : EuclideanSpace ℝ ι' → W)
    (x : EuclideanSpace ℝ ι') :
    taylorExtension N f ((complexEuclideanEquivRealProd ι').symm (x, 0)) = f x := by
  rw [taylorExtension_def, ContinuousLinearEquiv.apply_symm_apply,
    Finset.sum_eq_single_of_mem 0 (by simp)]
  · simp
  · intro j _ hj
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
    rw [← Pi.zero_def, ContinuousMultilinearMap.map_zero, smul_zero]

/-- The truncated Taylor extension of order zero is `f` applied to the real part. -/
@[simp]
theorem taylorExtension_zero (f : EuclideanSpace ℝ ι' → W) (z : EuclideanSpace ℂ ι') :
    taylorExtension 0 f z = f (complexEuclideanEquivRealProd ι' z).1 := by
  simp [taylorExtension_def]

/-- If `f` is `C^(r + N)`, then its truncated Taylor extension of order `N` is `C^r` over `ℝ`. -/
theorem contDiff_taylorExtension {N : ℕ} {r : WithTop ℕ∞} {f : EuclideanSpace ℝ ι' → W}
    (hf : ContDiff ℝ (r + N) f) : ContDiff ℝ r (taylorExtension N f) := by
  have hre : ContDiff ℝ r fun z : EuclideanSpace ℂ ι' ↦ (complexEuclideanEquivRealProd ι' z).1 :=
    (complexEuclideanEquivRealProd ι').contDiff.fst
  have him : ContDiff ℝ r fun z : EuclideanSpace ℂ ι' ↦ (complexEuclideanEquivRealProd ι' z).2 :=
    (complexEuclideanEquivRealProd ι').contDiff.snd
  refine ContDiff.sum fun j hj ↦ ContDiff.const_smul _ ?_
  have hD : ContDiff ℝ r (iteratedFDeriv ℝ j f) :=
    hf.iteratedFDeriv_right (add_le_add_right (by exact_mod_cast Finset.mem_range_succ_iff.1 hj) _)
  exact ContinuousMultilinearMap.analyticOnNhd_apply.contDiff.comp
    ((hD.comp hre).prodMk (contDiff_pi.2 fun _ ↦ him))

/-- Multiplication by `i` carries `x + i y` to `-y + i x`. -/
theorem _root_.TauCeti.I_smul_complexEuclideanEquivRealProd_symm (x y : EuclideanSpace ℝ ι') :
    Complex.I • (complexEuclideanEquivRealProd ι').symm (x, y) =
      (complexEuclideanEquivRealProd ι').symm (-y, x) := by
  ext i
  simp only [PiLp.smul_apply, complexEuclideanEquivRealProd_symm_apply, smul_eq_mul,
    PiLp.neg_apply, Complex.ofReal_neg]
  linear_combination (y i : ℂ) * Complex.I_sq

/-- If `f` is `C^(k + 1)` at `x`, then by the symmetry of `D^(k+1) f(x)`, replacing one of `k + 1`
equal arguments `y` by `u` gives the same value wherever `u` is placed:
`∑ᵢ D^(k+1) f(x) (y, …, u, …, y) = (k + 1) • D^(k+1) f(x) (u, y, …, y)`. The left side is the
derivative of `y ↦ D^(k+1) f(x) (y, …, y)` in the direction `u`. -/
theorem _root_.ContDiffAt.sum_iteratedFDeriv_update_const {𝕜 E F : Type*}
    [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : E → F} {x : E} {k : ℕ}
    (hf : ContDiffAt 𝕜 (k + 1) f x) (y u : E) :
    ∑ i, iteratedFDeriv 𝕜 (k + 1) f x (Function.update (fun _ ↦ y) i u) =
      (k + 1) • iteratedFDeriv 𝕜 (k + 1) f x (Fin.cons u fun _ ↦ y) := by
  have hupd (i : Fin (k + 1)) : Function.update (fun _ ↦ y) i u =
      (Fin.cons u fun _ ↦ y : Fin (k + 1) → E) ∘ Equiv.swap 0 i := by
    funext l
    cases l using Fin.cases <;> cases i using Fin.cases <;>
      simp [Equiv.swap_apply_def, Function.update_apply, Fin.succ_ne_zero, eq_comm]
    split_ifs <;> simp
  simp_rw [hupd, hf.iteratedFDeriv_comp_perm_of_le (k := k + 1) (by simp)]
  simp

/-- The real derivative of the truncated Taylor extension at `x + i y` in a real direction `u`:
`∑_{j ≤ N} (i ^ j / j!) • D^(j+1) f(x) (u, y, …, y)`. -/
theorem fderiv_taylorExtension_apply_real {N : ℕ} {f : EuclideanSpace ℝ ι' → W}
    (hf : ContDiff ℝ (N + 1) f) (x y u : EuclideanSpace ℝ ι') :
    fderiv ℝ (taylorExtension N f) ((complexEuclideanEquivRealProd ι').symm (x, y))
        ((complexEuclideanEquivRealProd ι').symm (u, 0)) =
      ∑ j ∈ Finset.range (N + 1), (Complex.I ^ j / j.factorial) •
        iteratedFDeriv ℝ (j + 1) f x (Fin.cons u fun _ ↦ y) := by
  set e := complexEuclideanEquivRealProd ι'
  have hF : DifferentiableAt ℝ (taylorExtension N f) (e.symm (x, y)) :=
    ((contDiff_taylorExtension (r := 1) (by rwa [add_comm])).differentiable one_ne_zero) _
  have hline : HasFDerivAt (fun x' ↦ e.symm (x', y))
      (e.symm.toContinuousLinearMap.comp
        (.inl ℝ (EuclideanSpace ℝ ι') (EuclideanSpace ℝ ι'))) x :=
    e.symm.hasFDerivAt.comp x (hasFDerivAt_prodMk_left x y)
  have heq : (taylorExtension N f ∘ fun x' ↦ e.symm (x', y)) = fun x' ↦
      ∑ j ∈ Finset.range (N + 1), (Complex.I ^ j / j.factorial) •
        iteratedFDeriv ℝ j f x' (fun _ ↦ y) := by
    funext x'
    simp [taylorExtension_def, e]
  have hsum := HasFDerivAt.fun_sum (u := Finset.range (N + 1)) fun j hj ↦
    (((hf.differentiable_iteratedFDeriv (m := j) (by norm_cast; simp at hj; omega)) x).hasFDerivAt
      |>.continuousMultilinear_apply_const (fun _ ↦ y)).const_smul
        (Complex.I ^ j / (j.factorial : ℂ))
  replace hsum := hsum.congr_of_eventuallyEq
    (f₁ := taylorExtension N f ∘ fun x' ↦ e.symm (x', y)) (.of_eq (by rw [heq]; rfl))
  have h := congrArg (· u) ((hF.hasFDerivAt.comp x hline).unique hsum)
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.inl_apply,
    ContinuousLinearEquiv.coe_coe, FunLike.coe_sum, Finset.sum_apply,
    FunLike.coe_smul, Pi.smul_apply,
    ContinuousLinearMap.flipMultilinear_apply_apply] at h
  rw [h]
  simp_rw [iteratedFDeriv_succ_apply_left, Fin.cons_zero, Fin.tail_cons]

/-- The real derivative of the truncated Taylor extension at `x + i y` in an imaginary direction
`i u`: `∑_{j < N} (i ^ (j + 1) / j!) • D^(j+1) f(x) (u, y, …, y)`. -/
theorem fderiv_taylorExtension_apply_imag {N : ℕ} {f : EuclideanSpace ℝ ι' → W}
    (hf : ContDiff ℝ (N + 1) f) (x y u : EuclideanSpace ℝ ι') :
    fderiv ℝ (taylorExtension N f) ((complexEuclideanEquivRealProd ι').symm (x, y))
        ((complexEuclideanEquivRealProd ι').symm (0, u)) =
      ∑ j ∈ Finset.range N, (Complex.I ^ (j + 1) / j.factorial) •
        iteratedFDeriv ℝ (j + 1) f x (Fin.cons u fun _ ↦ y) := by
  set e := complexEuclideanEquivRealProd ι'
  have hF : DifferentiableAt ℝ (taylorExtension N f) (e.symm (x, y)) :=
    ((contDiff_taylorExtension (r := 1) (by rwa [add_comm])).differentiable one_ne_zero) _
  have hline : HasFDerivAt (fun y' ↦ e.symm (x, y'))
      (e.symm.toContinuousLinearMap.comp
        (.inr ℝ (EuclideanSpace ℝ ι') (EuclideanSpace ℝ ι'))) y :=
    e.symm.hasFDerivAt.comp y (hasFDerivAt_prodMk_right x y)
  have heq : (taylorExtension N f ∘ fun y' ↦ e.symm (x, y')) = fun y' ↦
      ∑ j ∈ Finset.range (N + 1), (Complex.I ^ j / j.factorial) •
        iteratedFDeriv ℝ j f x (fun _ ↦ y') := by
    funext y'
    simp [taylorExtension_def, e]
  let d (n : ℕ) : EuclideanSpace ℝ ι' →L[ℝ] Fin n → EuclideanSpace ℝ ι' :=
    ContinuousLinearMap.pi fun _ ↦ ContinuousLinearMap.id ℝ _
  have hsum := HasFDerivAt.fun_sum (u := Finset.range (N + 1)) fun j _ ↦
    (((iteratedFDeriv ℝ j f x).hasFDerivAt (d j y)).comp y (d j).hasFDerivAt).const_smul
        (Complex.I ^ j / (j.factorial : ℂ))
  replace hsum := hsum.congr_of_eventuallyEq
    (f₁ := taylorExtension N f ∘ fun y' ↦ e.symm (x, y')) (.of_eq (by rw [heq]; rfl))
  have h := congrArg (· u) ((hF.hasFDerivAt.comp y hline).unique hsum)
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.inr_apply,
    ContinuousLinearEquiv.coe_coe, FunLike.coe_sum, Finset.sum_apply,
    FunLike.coe_smul, Pi.smul_apply, ContinuousMultilinearMap.linearDeriv_apply,
    d, ContinuousLinearMap.coe_pi', ContinuousLinearMap.id_apply] at h
  rw [h, Finset.sum_range_succ']
  simp only [Finset.univ_eq_empty, Finset.sum_empty, smul_zero, add_zero]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  rw [((hf.of_le (by norm_cast; simp at hj; omega)).contDiffAt).sum_iteratedFDeriv_update_const,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, Nat.factorial_succ]
  congr 1
  push_cast
  field_simp

/-- The conjugate Wirtinger derivative of the truncated Taylor extension of a `C^(N + 1)` map
at `x + i y`, in a real direction `u`: only the term of order `N + 1` survives, and it is
`(2⁻¹ * i ^ N / N!) • D^(N+1) f(x) (u, y, …, y)`. -/
theorem conjWirtingerDeriv_taylorExtension_apply_real {N : ℕ} {f : EuclideanSpace ℝ ι' → W}
    (hf : ContDiff ℝ (N + 1) f) (x y u : EuclideanSpace ℝ ι') :
    conjWirtingerDeriv (taylorExtension N f) ((complexEuclideanEquivRealProd ι').symm (x, y))
        ((complexEuclideanEquivRealProd ι').symm (u, 0)) =
      ((2 : ℂ)⁻¹ * Complex.I ^ N / N.factorial) •
        iteratedFDeriv ℝ (N + 1) f x (Fin.cons u fun _ ↦ y) := by
  rw [conjWirtingerDeriv_apply, I_smul_complexEuclideanEquivRealProd_symm, neg_zero,
    fderiv_taylorExtension_apply_real hf, fderiv_taylorExtension_apply_imag hf,
    Finset.sum_range_succ, Finset.smul_sum, add_right_comm, ← Finset.sum_add_distrib,
    Finset.sum_eq_zero, zero_add, smul_smul]
  · ring_nf
  · intro j _
    rw [smul_smul, ← add_smul]
    convert zero_smul ℂ _
    linear_combination (Complex.I ^ j / j.factorial) * Complex.I_sq

end SymplecticGeometry

end
