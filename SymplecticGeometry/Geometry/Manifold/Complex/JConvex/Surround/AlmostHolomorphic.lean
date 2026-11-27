/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import TauCeti.Analysis.Complex.Wirtinger.Basic
public import TauCeti.Analysis.InnerProductSpace.Euclidean.Complex
public import SymplecticGeometry.Analysis.InnerProductSpace.Euclidean.ComplexExtension

import Mathlib.Analysis.Analytic.CPolynomial
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.MetricSpace.Thickening
import SymplecticGeometry.Analysis.Calculus.IteratedFDeriv.Symmetric
import SymplecticGeometry.Analysis.Calculus.FDeriv.ContinuousMultilinearMap
import SymplecticGeometry.Analysis.Complex.Wirtinger.Basic
import SymplecticGeometry.Analysis.Complex.Wirtinger.VanishingOrder
import SymplecticGeometry.Analysis.Normed.Module.Multilinear.Basic
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.Analysis.Calculus.IteratedFDeriv.Flat
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
* `SymplecticGeometry.fderiv_taylorExtension_ofReal`: for `1 ≤ N`, its real derivative at a real
  point `x + i 0` is the complex-linear extension of the derivative of `f` at `x`;
* `SymplecticGeometry.fderiv_taylorExtension_comp_ofReal`: if `f` is the restriction to the real
  points of a map `h` whose derivative at a real point `x + i 0` commutes with multiplication by
  `i`, and `1 ≤ N`, then `taylorExtension N f` and `h` have the same derivative at `x + i 0`;
* `SymplecticGeometry.conjWirtingerDeriv_taylorExtension_apply_real`: in a real direction `u`,
  the conjugate Wirtinger derivative of `taylorExtension N f` at `x + i y` is
  `(2⁻¹ * i ^ N / N!) • D^(N+1) f(x) (u, y, …, y)`, so it vanishes to order `N` on the real
  points; `SymplecticGeometry.conjWirtingerDeriv_taylorExtension_apply` gives it in every
  direction, by conjugate linearity;
* `SymplecticGeometry.norm_conjWirtingerDeriv_taylorExtension_le`: for `K` compact, there is `C`
  with `‖∂̄ (taylorExtension N f) (x + i y)‖ ≤ C * ‖y‖ ^ N` for `x ∈ K`;
* `SymplecticGeometry.complexAntilinearPartL_fderiv_taylorExtension`: the same defect, as the
  real-linear map `ContinuousLinearMap.complexAntilinearPartL` of the derivative, is a fixed
  real-linear map applied to `D^(N+1) f(x) (·, y, …, y)`;
* `SymplecticGeometry.norm_fderiv_complexAntilinearPartL_fderiv_taylorExtension_le`: for `f` of
  class `C^(N + 2)` and `K` compact, there is `C` with a bound `C * ‖y‖ ^ (N - 1)` on the
  derivative of `∂̄ (taylorExtension N f)` (as the real-linear map
  `ContinuousLinearMap.complexAntilinearPartL` of the derivative) at `x + i y`, for `x ∈ K` and
  `‖y‖ ≤ 1`. The derivative of `∂̄` grows like `‖y‖ ^ N` for large `y`, hence `‖y‖ ≤ 1`.
* `SymplecticGeometry.exists_norm_iteratedFDeriv_le_of_iteratedFDeriv_eq_zero`: a map into a real
  normed space that is `C^(N + 1)` on an open set `U`, with derivatives of order at most `N` zero
  at the real points of `U`, has `‖D^j D (x + i y)‖ ≤ C * ‖y‖ ^ (N + 1 - j)` for `j ≤ N + 1` on a
  neighbourhood of any compact set of real points in `U`. It follows from Tau Ceti's
  `TauCeti.norm_iteratedFDeriv_sub_le_of_iteratedFDeriv_eq_zero` on a ball about a point of the
  compact set, between `x` and `x + i y`.
* `SymplecticGeometry.iteratedFDeriv_eq_zero_of_norm_conjWirtingerDeriv_le`: a map `D` into a
  complex normed space that is `C^N` on an open set `U`, vanishes at the real points of
  `U`, and has `‖∂̄ D (x + i y)‖ ≤ C * ‖y‖ ^ N` on `U`, has derivatives of every order `j ≤ N`
  zero at the real points of `U`; `SymplecticGeometry.fderiv_eq_zero_of_norm_conjWirtingerDeriv_le`
  is the case `j = 1`;
* `SymplecticGeometry.exists_norm_iteratedFDeriv_le_of_norm_conjWirtingerDeriv_le`: the two
  results above together. If `D` is moreover `C^(N + 1)`, then
  `‖D^j D (x + i y)‖ ≤ C' * ‖y‖ ^ (N + 1 - j)` for `j ≤ N + 1` near any compact set of real
  points in `U`;
* `SymplecticGeometry.exists_norm_conjWirtingerDeriv_le_of_norm_iteratedFDeriv_sub_le`: if the
  first two derivatives of `e₁ - e₂` are `O(‖y‖ ^ (N + 1 - j))` on an open set, as
  `SymplecticGeometry.exists_norm_iteratedFDeriv_le_of_norm_conjWirtingerDeriv_le` gives them
  for `1 ≤ N`, then the bounds `C₁ * ‖y‖ ^ N` on `∂̄ e₁` and `C₁ * ‖y‖ ^ (N - 1)` on its
  derivative pass to `e₂`, with another constant.

For `SymplecticGeometry.iteratedFDeriv_eq_zero_of_norm_conjWirtingerDeriv_le`, fix a real point
`x` of `U`. The iterated derivative `D^j D(x)` vanishes on real arguments, since `D` vanishes on
the real points of `U`. In its last argument it is `D^(j-1) (DD)(x)`, and the complex antilinear
part of `DD`, which is `∂̄ D`, is `O(‖z - x‖ ^ N)`, so its derivatives of order `j - 1 < N`
vanish at `x` (`ContDiffAt.iteratedFDeriv_fderiv_apply_I_smul_of_isBigO_conjWirtingerDeriv`):
hence `D^j D(x)` is complex linear in its last argument, and by symmetry in each argument. Such a
multilinear map is zero (`ContinuousMultilinearMap.eq_zero_of_map_update_I_smul`).

The formula of `SymplecticGeometry.conjWirtingerDeriv_taylorExtension_apply_real` is the standard
computation for almost analytic extensions: the derivative in the direction `i u` shifts the
order of each term down by one, by the symmetry of the iterated derivatives of `f`
(`ContDiffAt.sum_iteratedFDeriv_update_const`), so that in
`Df(z) u + i • Df(z) (i u)` every term but the one with `D^(N+1) f` cancels.

## References

* [K. Cieliebak, Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012]:
  the proof of Proposition 5.55 builds its charts from such extensions.
-/

public section

namespace SymplecticGeometry

open TauCeti Topology

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
  have heq : (fun x' ↦ (taylorExtension N f ∘ e.symm) (x', y)) = fun x' ↦
      ∑ j ∈ Finset.range (N + 1), (Complex.I ^ j / j.factorial) •
        iteratedFDeriv ℝ j f x' (fun _ ↦ y) := by
    funext x'
    simp [taylorExtension_def, e]
  have hsum := HasFDerivAt.fun_sum (u := Finset.range (N + 1)) fun j hj ↦
    (((hf.differentiable_iteratedFDeriv (m := j) (by norm_cast; simp at hj; omega)) x).hasFDerivAt
      |>.continuousMultilinear_apply_const (fun _ ↦ y)).const_smul
        (Complex.I ^ j / (j.factorial : ℂ))
  have h := congrArg (· u) (fderiv_slice_left (hF.comp (x, y) e.symm.differentiableAt))
  simp only [Pi.smul_apply] at hsum
  rw [e.symm.comp_right_fderiv, heq, hsum.fderiv] at h
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.inl_apply,
    ContinuousLinearEquiv.coe_coe, FunLike.coe_sum, Finset.sum_apply,
    FunLike.coe_smul, Pi.smul_apply,
    ContinuousLinearMap.flipMultilinear_apply_apply] at h
  rw [← h]
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
  have heq : (fun y' ↦ (taylorExtension N f ∘ e.symm) (x, y')) = fun y' ↦
      ∑ j ∈ Finset.range (N + 1), (Complex.I ^ j / j.factorial) •
        iteratedFDeriv ℝ j f x (fun _ ↦ y') := by
    funext y'
    simp [taylorExtension_def, e]
  have hsum := HasFDerivAt.fun_sum (u := Finset.range (N + 1)) fun j _ ↦
    (HasFDerivAt.multilinear_comp (f := iteratedFDeriv ℝ j f x) (g := fun _ ↦ id)
      (fun _ ↦ hasFDerivAt_id y)).const_smul (Complex.I ^ j / (j.factorial : ℂ))
  have h := congrArg (· u) (fderiv_slice_right (hF.comp (x, y) e.symm.differentiableAt))
  simp only [Pi.smul_apply, id_eq] at hsum
  rw [e.symm.comp_right_fderiv, heq, hsum.fderiv] at h
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.inr_apply,
    ContinuousLinearEquiv.coe_coe, FunLike.coe_sum, Finset.sum_apply,
    FunLike.coe_smul, Pi.smul_apply, ContinuousMultilinearMap.toContinuousLinearMap_apply,
    ContinuousLinearMap.coe_id', id_eq] at h
  rw [← h, Finset.sum_range_succ']
  simp only [Finset.univ_eq_empty, Finset.sum_empty, smul_zero, add_zero]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  rw [hf.contDiffAt.sum_iteratedFDeriv_update_const
      (by rw [minSmoothness_of_isRCLikeNormedField]; norm_cast; simp at hj; omega),
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, Nat.factorial_succ]
  congr 1
  push_cast
  field_simp

/-- At a real point `x + i 0`, the real derivative of the truncated Taylor extension of order
`N ≥ 1` of a `C^(N + 1)` map `f` is the complex-linear extension of the derivative of `f` at `x`.
For `N = 0` this fails: the extension is then constant in the imaginary directions. -/
theorem fderiv_taylorExtension_ofReal {N : ℕ} (hN : 1 ≤ N) {f : EuclideanSpace ℝ ι' → W}
    (hf : ContDiff ℝ (N + 1) f) (x : EuclideanSpace ℝ ι') :
    fderiv ℝ (taylorExtension N f) ((complexEuclideanEquivRealProd ι').symm (x, 0)) =
      ContinuousLinearMap.complexExtension ι' W (fderiv ℝ f x) := by
  set e := complexEuclideanEquivRealProd ι'
  -- At `y = 0`, only the first-order term of each sum survives.
  have hsum (M : ℕ) (c : ℕ → ℂ) (hM : 0 < M) (u : EuclideanSpace ℝ ι') :
      ∑ j ∈ Finset.range M, c j • iteratedFDeriv ℝ (j + 1) f x (Fin.cons u fun _ ↦ 0) =
        c 0 • fderiv ℝ f x u := by
    rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.2 hM)]
    · simp
    · intro j _ hj
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
      rw [(iteratedFDeriv ℝ (k + 2) f x).map_coord_zero (1 : Fin (k + 2)) (by simp), smul_zero]
  ext z
  obtain ⟨⟨u, v⟩, rfl⟩ := e.symm.surjective z
  rw [ContinuousLinearMap.complexExtension_apply_symm,
    show e.symm (u, v) = e.symm (u, 0) + e.symm (0, v) by rw [← map_add]; simp, map_add,
    fderiv_taylorExtension_apply_real hf, fderiv_taylorExtension_apply_imag hf,
    hsum _ _ (Nat.succ_pos N), hsum _ _ hN]
  simp

/-- Let `h : ℂⁿ → W` be real differentiable at a real point `x + i 0`, with a derivative there
that commutes with multiplication by `i`, and let its restriction `y ↦ h (y + i 0)` to the real
points be `C^(N + 1)` with `1 ≤ N`. Then the truncated Taylor extension of order `N` of this
restriction has the same real derivative as `h` at `x + i 0`. (Their values there agree by
`taylorExtension_ofReal`.) For `N = 0` this fails: the extension is then constant in the
imaginary directions. -/
theorem fderiv_taylorExtension_comp_ofReal {N : ℕ} (hN : 1 ≤ N) {h : EuclideanSpace ℂ ι' → W}
    (hf : ContDiff ℝ (N + 1) fun y ↦ h ((complexEuclideanEquivRealProd ι').symm (y, 0)))
    {x : EuclideanSpace ℝ ι'}
    (hx : DifferentiableAt ℝ h ((complexEuclideanEquivRealProd ι').symm (x, 0)))
    (hI : ∀ v, fderiv ℝ h ((complexEuclideanEquivRealProd ι').symm (x, 0)) (Complex.I • v) =
      Complex.I • fderiv ℝ h ((complexEuclideanEquivRealProd ι').symm (x, 0)) v) :
    fderiv ℝ (taylorExtension N fun y ↦ h ((complexEuclideanEquivRealProd ι').symm (y, 0)))
        ((complexEuclideanEquivRealProd ι').symm (x, 0)) =
      fderiv ℝ h ((complexEuclideanEquivRealProd ι').symm (x, 0)) := by
  set e := complexEuclideanEquivRealProd ι'
  rw [fderiv_taylorExtension_ofReal hN hf]
  refine (ContinuousLinearMap.complexExtension_unique _ hI fun u ↦ ?_).symm
  -- The derivative of `h ∘ ofReal` is that of `h` in the real directions.
  rw [show (fun y ↦ h (e.symm (y, 0))) = fun y ↦ (h ∘ e.symm) (y, 0) from rfl,
    fderiv_slice_left (hx.comp _ e.symm.differentiableAt), e.symm.comp_right_fderiv]
  simp [e]

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

/-- The conjugate Wirtinger derivative of the truncated Taylor extension of a `C^(N + 1)` map
at `x + i y`, in any direction `u + i w`: it is
`(2⁻¹ * i ^ N / N!) • (D^(N+1) f(x) (u, y, …, y) - i • D^(N+1) f(x) (w, y, …, y))`. -/
theorem conjWirtingerDeriv_taylorExtension_apply {N : ℕ} {f : EuclideanSpace ℝ ι' → W}
    (hf : ContDiff ℝ (N + 1) f) (z v : EuclideanSpace ℂ ι') :
    conjWirtingerDeriv (taylorExtension N f) z v =
      ((2 : ℂ)⁻¹ * Complex.I ^ N / N.factorial) •
        (iteratedFDeriv ℝ (N + 1) f (complexEuclideanEquivRealProd ι' z).1
            (Fin.cons (complexEuclideanEquivRealProd ι' v).1
              fun _ ↦ (complexEuclideanEquivRealProd ι' z).2) -
          Complex.I • iteratedFDeriv ℝ (N + 1) f (complexEuclideanEquivRealProd ι' z).1
            (Fin.cons (complexEuclideanEquivRealProd ι' v).2
              fun _ ↦ (complexEuclideanEquivRealProd ι' z).2)) := by
  set e := complexEuclideanEquivRealProd ι'
  have hv : v = e.symm ((e v).1, 0) + Complex.I • e.symm ((e v).2, 0) := by
    rw [I_smul_complexEuclideanEquivRealProd_symm, neg_zero, ← map_add, Prod.mk_add_mk, add_zero,
      zero_add, ContinuousLinearEquiv.symm_apply_apply]
  have hz : z = e.symm ((e z).1, (e z).2) := by simp
  conv_lhs => rw [hv, map_add, map_smulₛₗ, hz, conjWirtingerDeriv_taylorExtension_apply_real hf,
    conjWirtingerDeriv_taylorExtension_apply_real hf]
  rw [Complex.conj_I, neg_smul, smul_comm Complex.I, ← sub_eq_add_neg, smul_sub]

/-- The conjugate Wirtinger derivative of the truncated Taylor extension of order `N` of a
`C^(N + 1)` map vanishes to order `N` on the real points, uniformly over a compact set of real
parts: for `K` compact there is `C` with `‖∂̄ (taylorExtension N f) (x + i y)‖ ≤ C * ‖y‖ ^ N`
whenever `x ∈ K`. -/
theorem norm_conjWirtingerDeriv_taylorExtension_le {N : ℕ} {f : EuclideanSpace ℝ ι' → W}
    (hf : ContDiff ℝ (N + 1) f) {K : Set (EuclideanSpace ℝ ι')} (hK : IsCompact K) :
    ∃ C, ∀ z, (complexEuclideanEquivRealProd ι' z).1 ∈ K →
      ‖conjWirtingerDeriv (taylorExtension N f) z‖ ≤
        C * ‖(complexEuclideanEquivRealProd ι' z).2‖ ^ N := by
  set e := complexEuclideanEquivRealProd ι'
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn
    (hf.continuous_iteratedFDeriv le_rfl).continuousOn
  set c : ℂ := (2 : ℂ)⁻¹ * Complex.I ^ N / N.factorial
  refine ⟨‖c‖ * (2 * max M 0), fun z hz ↦ ?_⟩
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v ↦ ?_
  have hD : ∀ a, ‖iteratedFDeriv ℝ (N + 1) f (e z).1 (Fin.cons a fun _ ↦ (e z).2)‖ ≤
      max M 0 * (‖a‖ * ‖(e z).2‖ ^ N) := fun a ↦ by
    refine ((iteratedFDeriv ℝ (N + 1) f (e z).1).norm_map_cons_le _ _).trans ?_
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_assoc]
    gcongr
    exact (hM _ hz).trans (le_max_left _ _)
  rw [conjWirtingerDeriv_taylorExtension_apply hf, norm_smul]
  calc ‖c‖ * ‖_ - _‖ ≤ ‖c‖ * (max M 0 * (‖(e v).1‖ * ‖(e z).2‖ ^ N) +
        max M 0 * (‖(e v).2‖ * ‖(e z).2‖ ^ N)) := by
        gcongr
        refine (norm_sub_le _ _).trans (add_le_add (hD _) ?_)
        rw [norm_smul, Complex.norm_I, one_mul]
        exact hD _
    _ ≤ ‖c‖ * (max M 0 * (‖v‖ * ‖(e z).2‖ ^ N) + max M 0 * (‖v‖ * ‖(e z).2‖ ^ N)) := by
        gcongr
        · exact norm_complexEuclideanEquivRealProd_fst_le v
        · exact norm_complexEuclideanEquivRealProd_snd_le v
    _ = _ := by ring

/-- The bundled conjugate Wirtinger derivative of the truncated Taylor extension of a
`C^(N + 1)` map at `z = x + i y` is `c • (L ∘ re - i • L ∘ im)`, where `c = 2⁻¹ * i ^ N / N!`,
`re` and `im` are the real and imaginary parts, and `L` is the real-linear map
`D^(N+1) f(x) (·, y, …, y)`. -/
theorem complexAntilinearPartL_fderiv_taylorExtension {N : ℕ} {f : EuclideanSpace ℝ ι' → W}
    (hf : ContDiff ℝ (N + 1) f) (z : EuclideanSpace ℂ ι') :
    ContinuousLinearMap.complexAntilinearPartL (fderiv ℝ (taylorExtension N f) z) =
      ((2 : ℂ)⁻¹ * Complex.I ^ N / N.factorial) •
        (((iteratedFDeriv ℝ (N + 1) f (complexEuclideanEquivRealProd ι' z).1).curryLeft
            |>.flipMultilinear fun _ ↦ (complexEuclideanEquivRealProd ι' z).2) ∘L
            (.fst ℝ _ _ ∘L (complexEuclideanEquivRealProd ι').toContinuousLinearMap) -
          Complex.I • ((iteratedFDeriv ℝ (N + 1) f (complexEuclideanEquivRealProd ι' z).1).curryLeft
            |>.flipMultilinear fun _ ↦ (complexEuclideanEquivRealProd ι' z).2) ∘L
            (.snd ℝ _ _ ∘L (complexEuclideanEquivRealProd ι').toContinuousLinearMap)) := by
  ext v
  rw [← conjWirtingerDeriv_apply_eq_complexAntilinearPartL,
    conjWirtingerDeriv_taylorExtension_apply hf]
  simp [smul_sub]

/-- The derivative of the conjugate Wirtinger derivative of the truncated Taylor extension of
order `N` of a `C^(N + 2)` map, taken in the bundled real-linear form
`z ↦ complexAntilinearPartL (fderiv ℝ (taylorExtension N f) z)`, vanishes to order `N - 1` on
the real points: for `K` compact there is `C` with `‖D(∂̄ (taylorExtension N f)) (x + i y)‖ ≤
C * ‖y‖ ^ (N - 1)` whenever `x ∈ K` and `‖y‖ ≤ 1`. The bound `‖y‖ ≤ 1` is needed: away from the
real points, the term of order `‖y‖ ^ N`, which comes from `D^(N+2) f`, dominates. -/
theorem norm_fderiv_complexAntilinearPartL_fderiv_taylorExtension_le {N : ℕ}
    {f : EuclideanSpace ℝ ι' → W} (hf : ContDiff ℝ (N + 2) f) {K : Set (EuclideanSpace ℝ ι')}
    (hK : IsCompact K) :
    ∃ C, ∀ z, (complexEuclideanEquivRealProd ι' z).1 ∈ K →
      ‖(complexEuclideanEquivRealProd ι' z).2‖ ≤ 1 →
      ‖fderiv ℝ (fun z ↦ ContinuousLinearMap.complexAntilinearPartL
          (fderiv ℝ (taylorExtension N f) z)) z‖ ≤
        C * ‖(complexEuclideanEquivRealProd ι' z).2‖ ^ (N - 1) := by
  set e := complexEuclideanEquivRealProd ι'
  have hf1 : ContDiff ℝ (N + 1) f := hf.of_le (by norm_cast; omega)
  set re : EuclideanSpace ℂ ι' →L[ℝ] EuclideanSpace ℝ ι' := .fst ℝ _ _ ∘L e.toContinuousLinearMap
  set im : EuclideanSpace ℂ ι' →L[ℝ] EuclideanSpace ℝ ι' := .snd ℝ _ _ ∘L e.toContinuousLinearMap
  -- `A L` is the map `v ↦ c • (L (re v) - i • L (im v))`.
  set A : (EuclideanSpace ℝ ι' →L[ℝ] W) →L[ℝ] EuclideanSpace ℂ ι' →L[ℝ] W :=
    ((2 : ℂ)⁻¹ * Complex.I ^ N / N.factorial) • ((ContinuousLinearMap.compL ℝ _ _ W).flip re -
      Complex.I • (ContinuousLinearMap.compL ℝ _ _ W).flip im)
  -- `Φ M` is `M` with its first argument split off and moved to the values.
  set Φ := (ContinuousLinearMap.flipMultilinearEquiv ℝ (fun _ : Fin N ↦ EuclideanSpace ℝ ι')
      (EuclideanSpace ℝ ι') W).toContinuousLinearMap ∘L
    (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (N + 1) ↦ EuclideanSpace ℝ ι')
      W).toContinuousLinearEquiv.toContinuousLinearMap
  have hΦ (M) : ‖Φ M‖ ≤ ‖M‖ :=
    (ContinuousLinearMap.norm_flipMultilinear_le _).trans M.curryLeft_norm.le
  set D := iteratedFDeriv ℝ (N + 1) f
  have hD : Differentiable ℝ D := hf.differentiable_iteratedFDeriv (by norm_cast; omega)
  have hQ : (fun z ↦ ContinuousLinearMap.complexAntilinearPartL
      (fderiv ℝ (taylorExtension N f) z)) = fun z ↦ A (Φ (D (re z)) fun _ ↦ im z) := by
    funext z
    rw [complexAntilinearPartL_fderiv_taylorExtension hf1]
    ext1 v
    simp [A, Φ, re, im, D, e]
  obtain ⟨M₁, hM₁⟩ := hK.exists_bound_of_continuousOn
    (hf1.continuous_iteratedFDeriv le_rfl).continuousOn
  obtain ⟨M₂, hM₂⟩ := hK.exists_bound_of_continuousOn ((hf.iteratedFDeriv_right (i := N + 1)
    (m := 1) (le_of_eq (by push_cast; ring))).continuous_fderiv one_ne_zero).continuousOn
  refine ⟨‖A‖ * (max M₂ 0 * ‖re‖ + N * (max M₁ 0 * ‖im‖)), fun z hz hy ↦ ?_⟩
  have hR : HasFDerivAt (fun z ↦ Φ (D (re z))) (Φ ∘L (fderiv ℝ D (re z) ∘L re)) z :=
    Φ.hasFDerivAt.comp z ((hD (re z)).hasFDerivAt.comp z re.hasFDerivAt)
  have hQd : DifferentiableAt ℝ (fun z ↦ Φ (D (re z)) fun _ ↦ im z) z :=
    (hR.continuousMultilinearMap_apply fun _ ↦ im.hasFDerivAt).differentiableAt
  have hA := A.hasFDerivAt.comp z hQd.hasFDerivAt
  simp only [Function.comp_def] at hA
  rw [hQ, hA.fderiv]
  refine (A.opNorm_comp_le _).trans ?_
  have hb := hR.norm_fderiv_continuousMultilinearMap_apply_le im.hasFDerivAt
  have h2 : ‖Φ (D (re z))‖ ≤ max M₁ 0 := (hΦ _).trans ((hM₁ _ hz).trans (le_max_left _ _))
  have him : im z = (e z).2 := by simp [im]
  have h3 : ‖im z‖ ^ N ≤ ‖im z‖ ^ (N - 1) := pow_le_pow_of_le_one (norm_nonneg _) hy (by omega)
  rw [← him, mul_assoc]
  refine mul_le_mul_of_nonneg_left (hb.trans ?_) (norm_nonneg A)
  refine le_of_le_of_eq (b := max M₂ 0 * ‖re‖ * ‖im z‖ ^ (N - 1) +
    N * (max M₁ 0 * ‖im z‖ ^ (N - 1) * ‖im‖)) ?_ (by ring)
  gcongr ?_ * ?_ + _ * (?_ * _ * _)
  · refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h ↦ ?_
    refine (hΦ _).trans (((fderiv ℝ D (re z)).le_opNorm _).trans ?_)
    rw [mul_assoc]
    gcongr
    · exact (hM₂ _ hz).trans (le_max_left _ _)
    · exact re.le_opNorm h

/-- A map `D` that is `C^(N + 1)` over `ℝ` on an open set `U`, and whose derivatives of order at
most `N` vanish at the real points of `U`, vanishes to order `N + 1` near a compact set `K ⊆ U` of
real points: there are a neighbourhood `U'` of `K` and a constant `C` with
`‖D^j D (x + i y)‖ ≤ C * ‖y‖ ^ (N + 1 - j)` for all `x + i y ∈ U'` and `j ≤ N + 1`. -/
theorem exists_norm_iteratedFDeriv_le_of_iteratedFDeriv_eq_zero {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {N : ℕ} {D : EuclideanSpace ℂ ι' → F}
    {U K : Set (EuclideanSpace ℂ ι')} (hU : IsOpen U) (hD : ContDiffOn ℝ (N + 1) D U)
    (hK : IsCompact K) (hKU : K ⊆ U) (hKre : ∀ z ∈ K, (complexEuclideanEquivRealProd ι' z).2 = 0)
    (h0 : ∀ x ∈ U, (complexEuclideanEquivRealProd ι' x).2 = 0 →
      ∀ j ≤ N, iteratedFDeriv ℝ j D x = 0) :
    ∃ U' ∈ 𝓝ˢ K, ∃ C, ∀ z ∈ U', ∀ j ≤ N + 1,
      ‖iteratedFDeriv ℝ j D z‖ ≤ C * ‖(complexEuclideanEquivRealProd ι' z).2‖ ^ (N + 1 - j) := by
  set e := complexEuclideanEquivRealProd ι'
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hKU
  obtain ⟨M, hM⟩ := (hK.cthickening (r := δ)).exists_bound_of_continuousOn
    fun w hw ↦ ((hD.contDiffAt (hU.mem_nhds (hδU hw))).continuousAt_iteratedFDeriv
      le_rfl).continuousWithinAt
  refine ⟨Metric.thickening δ K, Metric.thickening_mem_nhdsSet K hδ, M, fun z hz j hj ↦ ?_⟩
  obtain ⟨k, hk, hzk⟩ := Metric.mem_thickening_iff.1 hz
  have hball : Metric.ball k δ ⊆ Metric.cthickening δ K :=
    (Metric.ball_subset_thickening hk δ).trans (Metric.thickening_subset_cthickening _ _)
  -- `x` is the real part of `z`, as a point of `ℂⁿ`.
  set x := e.symm ((e z).1, 0)
  have hzx : ‖z - x‖ = ‖(e z).2‖ := by
    rw [← e.symm_apply_apply z, ← map_sub, e.symm_apply_apply, Prod.mk_sub_mk, sub_self,
      sub_zero, norm_complexEuclideanEquivRealProd_symm_zero_mk]
  have hx : x ∈ Metric.ball k δ := by
    have hk' : k = e.symm ((e k).1, 0) := by
      rw [← hKre k hk]
      simp
    rw [Metric.mem_ball, dist_eq_norm, hk', ← map_sub, Prod.mk_sub_mk, sub_zero,
      norm_complexEuclideanEquivRealProd_symm_mk_zero]
    refine lt_of_le_of_lt ?_ (dist_eq_norm z k ▸ hzk)
    simpa using norm_complexEuclideanEquivRealProd_fst_le (z - k)
  rcases hj.eq_or_lt with rfl | hj
  · simpa using hM z (hball hzk)
  have hx0 := h0 x (hδU (hball hx)) (by simp [x])
  have h := norm_iteratedFDeriv_sub_le_of_iteratedFDeriv_eq_zero (s := Metric.ball k δ) (k := N)
    (fun w hw ↦ hD.contDiffAt (hU.mem_nhds (hδU (hball hw)))) (convex_ball k δ) hx
    (fun w hw ↦ hM w (hball hw)) (fun i _ hi ↦ hx0 i hi) (N - j) (by omega) z hzk
  rwa [Nat.sub_sub_self (by omega), hx0 j (by omega), sub_zero, hzx,
    show N - j + 1 = N + 1 - j by omega] at h

/-- A map `D` that is `C^N` over `ℝ` on an open set `U`, vanishes at the real points of `U`,
and whose conjugate Wirtinger derivative satisfies `‖∂̄ D (x + i y)‖ ≤ C * ‖y‖ ^ N` on `U`, has
iterated derivatives of every order `j ≤ N` equal to zero at each real point of `U`. -/
theorem iteratedFDeriv_eq_zero_of_norm_conjWirtingerDeriv_le {N : ℕ} {C : ℝ}
    {D : EuclideanSpace ℂ ι' → W} {U : Set (EuclideanSpace ℂ ι')} (hU : IsOpen U)
    (hD : ContDiffOn ℝ N D U)
    (hD0 : ∀ x ∈ U, (complexEuclideanEquivRealProd ι' x).2 = 0 → D x = 0)
    (hC : ∀ z ∈ U,
      ‖conjWirtingerDeriv D z‖ ≤ C * ‖(complexEuclideanEquivRealProd ι' z).2‖ ^ N)
    {x : EuclideanSpace ℂ ι'} (hxU : x ∈ U) (hx : (complexEuclideanEquivRealProd ι' x).2 = 0)
    {j : ℕ} (hj : j ≤ N) :
    iteratedFDeriv ℝ j D x = 0 := by
  set e := complexEuclideanEquivRealProd ι'
  have hDx : ContDiffAt ℝ N D x := hD.contDiffAt (hU.mem_nhds hxU)
  refine ContinuousMultilinearMap.eq_zero_of_map_update_I_smul ?_ fun y ↦ ?_
  · -- Complex linearity in each argument.
    intro m i v
    obtain _ | k := j
    · exact i.elim0
    -- `∂̄ D z` is `O(‖z - x‖ ^ N)`, since `x` is real.
    have hO : (fun z ↦ conjWirtingerDeriv D z) =O[𝓝 x] fun z ↦ ‖z - x‖ ^ N := by
      refine Asymptotics.IsBigO.of_bound (max C 0) ?_
      filter_upwards [hU.mem_nhds hxU] with z hz
      have him : (e z).2 = (e (z - x)).2 := by rw [map_sub, Prod.snd_sub, hx, sub_zero]
      calc _ ≤ max C 0 * ‖(e z).2‖ ^ N := (hC z hz).trans (by gcongr; exact le_max_left _ _)
        _ ≤ max C 0 * ‖‖z - x‖ ^ N‖ := by
            rw [norm_pow, norm_norm, him]
            gcongr
            exact norm_complexEuclideanEquivRealProd_snd_le _
    -- So the derivative of order `k` of `fderiv ℝ D` at `x` takes complex-linear values.
    have hQ := ContDiffAt.iteratedFDeriv_fderiv_apply_I_smul_of_isBigO_conjWirtingerDeriv
      (hDx.of_le (by exact_mod_cast hj)) hO (by omega)
    -- By symmetry, the argument `i` can be moved to the last place.
    have hlast (w : EuclideanSpace ℂ ι') : iteratedFDeriv ℝ (k + 1) D x (Function.update m i w) =
        iteratedFDeriv ℝ k (fderiv ℝ D) x (Fin.init (m ∘ Equiv.swap i (Fin.last k))) w := by
      rw [← hDx.iteratedFDeriv_comp_perm_of_le
          (by rw [minSmoothness_of_isRCLikeNormedField]; exact_mod_cast (by omega)) _
          (Equiv.swap i (Fin.last k)),
        Function.update_comp_equiv, Equiv.symm_swap, Equiv.swap_apply_left,
        iteratedFDeriv_succ_apply_right, Fin.init_update_last, Function.update_self]
    rw [hlast, hlast, hQ]
  · -- Vanishing on real arguments: `D` vanishes on the real points `y + i 0` of `U`.
    set L : EuclideanSpace ℝ ι' →L[ℝ] EuclideanSpace ℂ ι' :=
      e.symm.toContinuousLinearMap ∘L .inl ℝ _ _
    have hL (y) : L y = e.symm (y, 0) := by simp [L]
    have hLx : L (e x).1 = x := by rw [hL, ← hx]; simp
    have hxL : (e x).1 ∈ L ⁻¹' U := by simpa [hLx]
    have hU' : IsOpen (L ⁻¹' U) := hU.preimage L.continuous
    have h := L.iteratedFDerivWithin_comp_right hD hU.uniqueDiffOn hU'.uniqueDiffOn hxL
      (i := j) (by exact_mod_cast hj)
    rw [iteratedFDerivWithin_congr (f := 0) (f₁ := D ∘ L)
        (fun y hy ↦ hD0 (L y) hy (by simp [hL, e])) hxL,
      iteratedFDerivWithin_zero, hLx, iteratedFDerivWithin_of_isOpen j hU hxU] at h
    simpa [hL] using congr($h.symm y)

/-- Under the hypotheses of `iteratedFDeriv_eq_zero_of_norm_conjWirtingerDeriv_le`, with
`1 ≤ N`, the derivative of `D` vanishes at each real point of `U`. -/
theorem fderiv_eq_zero_of_norm_conjWirtingerDeriv_le {N : ℕ} {C : ℝ}
    {D : EuclideanSpace ℂ ι' → W} {U : Set (EuclideanSpace ℂ ι')} (hU : IsOpen U)
    (hD : ContDiffOn ℝ N D U)
    (hD0 : ∀ x ∈ U, (complexEuclideanEquivRealProd ι' x).2 = 0 → D x = 0)
    (hC : ∀ z ∈ U,
      ‖conjWirtingerDeriv D z‖ ≤ C * ‖(complexEuclideanEquivRealProd ι' z).2‖ ^ N)
    {x : EuclideanSpace ℂ ι'} (hxU : x ∈ U) (hx : (complexEuclideanEquivRealProd ι' x).2 = 0)
    (hN : 1 ≤ N) :
    fderiv ℝ D x = 0 := by
  rw [← norm_eq_zero, ← norm_iteratedFDeriv_one,
    iteratedFDeriv_eq_zero_of_norm_conjWirtingerDeriv_le hU hD hD0 hC hxU hx hN, norm_zero]

/-- A map `D` into a complex normed space that is `C^(N + 1)` over `ℝ` on an open set `U`,
vanishes at the real points of `U`, and whose conjugate Wirtinger derivative satisfies
`‖∂̄ D (x + i y)‖ ≤ C * ‖y‖ ^ N` on `U`, vanishes to order `N + 1` near a compact set `K ⊆ U` of
real points: there are a neighbourhood `U'` of `K` and a constant `C'` with
`‖D^j D (x + i y)‖ ≤ C' * ‖y‖ ^ (N + 1 - j)` for all `x + i y ∈ U'` and `j ≤ N + 1`. -/
theorem exists_norm_iteratedFDeriv_le_of_norm_conjWirtingerDeriv_le {N : ℕ} {C : ℝ}
    {D : EuclideanSpace ℂ ι' → W} {U K : Set (EuclideanSpace ℂ ι')} (hU : IsOpen U)
    (hD : ContDiffOn ℝ (N + 1) D U)
    (hD0 : ∀ x ∈ U, (complexEuclideanEquivRealProd ι' x).2 = 0 → D x = 0)
    (hC : ∀ z ∈ U,
      ‖conjWirtingerDeriv D z‖ ≤ C * ‖(complexEuclideanEquivRealProd ι' z).2‖ ^ N)
    (hK : IsCompact K) (hKU : K ⊆ U)
    (hKre : ∀ z ∈ K, (complexEuclideanEquivRealProd ι' z).2 = 0) :
    ∃ U' ∈ 𝓝ˢ K, ∃ C', ∀ z ∈ U', ∀ j ≤ N + 1,
      ‖iteratedFDeriv ℝ j D z‖ ≤ C' * ‖(complexEuclideanEquivRealProd ι' z).2‖ ^ (N + 1 - j) :=
  exists_norm_iteratedFDeriv_le_of_iteratedFDeriv_eq_zero hU hD hK hKU hKre
    fun _ hxU hx _ hj ↦ iteratedFDeriv_eq_zero_of_norm_conjWirtingerDeriv_le hU
      (hD.of_le (by exact_mod_cast N.le_succ)) hD0 hC hxU hx hj

/-- **Agreement of order `N + 1` carries the `∂̄` bounds.** Let `e₁ e₂` be `C²` over `ℝ` on an
open set `U`, with `‖D^j (e₁ - e₂) (x + i y)‖ ≤ C * ‖y‖ ^ (N + 1 - j)` on `U` for `j = 1, 2`.
If `‖∂̄ e₁ (x + i y)‖ ≤ C₁ * ‖y‖ ^ N` and the derivative of `∂̄ e₁` (in the bundled real-linear
form `ContinuousLinearMap.complexAntilinearPartL` of the derivative) is at most
`C₁ * ‖y‖ ^ (N - 1)` on `U`, then `e₂` has the same two bounds on `U` with some constant `C₂`. -/
theorem exists_norm_conjWirtingerDeriv_le_of_norm_iteratedFDeriv_sub_le {N : ℕ} {C C₁ : ℝ}
    {e₁ e₂ : EuclideanSpace ℂ ι' → W} {U : Set (EuclideanSpace ℂ ι')} (hU : IsOpen U)
    (he₁ : ContDiffOn ℝ 2 e₁ U) (he₂ : ContDiffOn ℝ 2 e₂ U)
    (hC : ∀ z ∈ U, ∀ j ∈ Finset.Icc 1 2, ‖iteratedFDeriv ℝ j (e₁ - e₂) z‖ ≤
      C * ‖(complexEuclideanEquivRealProd ι' z).2‖ ^ (N + 1 - j))
    (hC₁ : ∀ z ∈ U,
      ‖conjWirtingerDeriv e₁ z‖ ≤ C₁ * ‖(complexEuclideanEquivRealProd ι' z).2‖ ^ N)
    (hC₁' : ∀ z ∈ U,
      ‖fderiv ℝ (fun w ↦ ContinuousLinearMap.complexAntilinearPartL (fderiv ℝ e₁ w)) z‖ ≤
        C₁ * ‖(complexEuclideanEquivRealProd ι' z).2‖ ^ (N - 1)) :
    ∃ C₂, ∀ z ∈ U,
      ‖conjWirtingerDeriv e₂ z‖ ≤ C₂ * ‖(complexEuclideanEquivRealProd ι' z).2‖ ^ N ∧
      ‖fderiv ℝ (fun w ↦ ContinuousLinearMap.complexAntilinearPartL (fderiv ℝ e₂ w)) z‖ ≤
        C₂ * ‖(complexEuclideanEquivRealProd ι' z).2‖ ^ (N - 1) := by
  set P : (EuclideanSpace ℂ ι' →L[ℝ] W) →L[ℝ] EuclideanSpace ℂ ι' →L[ℝ] W :=
    ContinuousLinearMap.complexAntilinearPartL
  set t := fun z ↦ ‖(complexEuclideanEquivRealProd ι' z).2‖
  refine ⟨C₁ + max 1 ‖P‖ * max C 0, fun z hz ↦ ?_⟩
  have h₁ := he₁.contDiffAt (hU.mem_nhds hz)
  have h₂ := he₂.contDiffAt (hU.mem_nhds hz)
  have hC' : C ≤ max C 0 := le_max_left _ _
  have hP : 1 ≤ max 1 ‖P‖ := le_max_left _ _
  have hP' : ‖P‖ ≤ max 1 ‖P‖ := le_max_right _ _
  have h1 := hC z hz 1 (by simp)
  rw [norm_iteratedFDeriv_one, Nat.add_sub_cancel] at h1
  have h2 := hC z hz 2 (by simp)
  rw [show N + 1 - 2 = N - 1 by omega] at h2
  constructor
  · calc _ ≤ _ := norm_conjWirtingerDeriv_le_add_norm_fderiv_sub
          (h₁.differentiableAt two_ne_zero) (h₂.differentiableAt two_ne_zero)
      _ ≤ C₁ * t z ^ N + 1 * (max C 0 * t z ^ N) := by
        rw [one_mul]
        gcongr
        · exact hC₁ z hz
        · exact h1.trans (by gcongr)
      _ ≤ _ := by rw [add_mul, mul_assoc]; gcongr
  · calc _ ≤ _ := norm_fderiv_complexAntilinearPartL_fderiv_le_add_norm_iteratedFDeriv_sub h₁ h₂
      _ ≤ C₁ * t z ^ (N - 1) + ‖P‖ * (max C 0 * t z ^ (N - 1)) := by
        gcongr
        · exact hC₁' z hz
        · exact h2.trans (by gcongr)
      _ ≤ _ := by rw [add_mul, mul_assoc]; gcongr

end SymplecticGeometry

end
