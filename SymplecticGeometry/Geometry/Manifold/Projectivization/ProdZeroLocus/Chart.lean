/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Analytic.Polynomial
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import TauCeti.Analysis.MvPolynomial.Jacobian
public import TauCeti.LinearAlgebra.Projectivization.AffineChart
public import TauCeti.RingTheory.MvPolynomial.Jacobian.Basic

import SymplecticGeometry.RingTheory.MvPolynomial.WeightedHomogeneous
import TauCeti.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# Bihomogeneous equations in a product of affine charts

Let `p : ι → MvPolynomial (Fin (m + 1) ⊕ Fin (n + 1)) 𝕜` be a family of polynomials in two blocks
of homogeneous coordinates, each `p k` bihomogeneous: weighted homogeneous of degree `d₁ k` for
the weights `Sum.elim 1 0` and of degree `d₂ k` for the weights `Sum.elim 0 1`. Fix
`i : Fin (m + 1)` and `j : Fin (n + 1)`. This file reads `p` in the product of the standard
affine charts `affineChart i` and `affineChart j` of the two projective spaces, and compares
the derivative of these chart equations with the cone Jacobian `TauCeti.jacobiMatrixAt`.

## Main definitions and results

* `SymplecticGeometry.prodChartEquations i j p`: the chart equations
  `(u, u') ↦ fun k ↦ eval (Sum.elim (i.insertNth 1 u) (j.insertNth 1 u')) (p k)`.
* `SymplecticGeometry.contDiff_prodChartEquations`,
  `SymplecticGeometry.fderiv_prodChartEquations_apply` and
  `SymplecticGeometry.hasStrictFDerivAt_prodChartEquations`: they are polynomial, hence analytic,
  their derivative is the cone Jacobian at the chart point restricted to the vectors vanishing in
  the coordinates `Sum.inl i` and `Sum.inr j`, and it is a strict derivative.
* `SymplecticGeometry.surjective_fderiv_prodChartEquations_affineChart_iff`: **the regularity
  test**. At a common zero `(v, w)` with `v i ≠ 0` and `w j ≠ 0`, the derivative of the chart
  equations at the chart coordinates of `(mk v, mk w)` is surjective if and only if the cone
  Jacobian at `Sum.elim v w` is. The two Euler relations put two vectors in the kernel of the
  cone Jacobian that fill in the two missing coordinates.
* `SymplecticGeometry.mulVec_surjective_jacobiMatrixAt_sumElim_iff_of_mk_eq_mk`: surjectivity of
  the cone Jacobian depends only on the pair of projective points, since scaling the two blocks
  separately scales its rows and columns by nonzero factors
  (`SymplecticGeometry.jacobiMatrixAt_sumElim_smul_mul`).
* `SymplecticGeometry.card_le_of_mulVec_surjective_jacobiMatrixAt_sumElim`: where the cone
  Jacobian is surjective at a common zero, there are at most `m + n` equations.

For a single equation `f`, indexed by a one-element type, surjectivity of the cone Jacobian is
the nonvanishing of some evaluated partial derivative of `f`: this is Tau Ceti's
`TauCeti.mulVec_surjective_jacobiMatrixAt_iff_exists_eval_pderiv_ne_zero`, which holds for any
type of variables, so it applies here as it is.

The proofs follow Tau Ceti's single-space versions:
`TauCeti.surjective_fderiv_eval_dehomogenize_affineChart_iff` and its neighbours in
`TauCeti/Geometry/Manifold/Projectivization/Polynomial.lean` for the regularity test,
`TauCeti.mulVec_surjective_jacobiMatrixAt_iff_of_mk_eq_mk` in
`TauCeti/RingTheory/MvPolynomial/Jacobian/Basic.lean` for the independence of representatives,
and `TauCeti.card_le_of_surjective_jacobiMatrixAt` in
`TauCeti/Geometry/Manifold/Projectivization/ZeroLocus.lean` for the count of equations.

## References

* [P. Griffiths and J. Harris, *Principles of Algebraic Geometry*][GriffithsHarris1978],
  Chapter 0, §1, for homogeneous coordinate charts.
-/

public section

open MvPolynomial Projectivization Matrix TauCeti
open scoped ContDiff

namespace SymplecticGeometry

variable {𝕜 ι : Type*} [RCLike 𝕜] {m n : ℕ}

/-- The equations `p` read in the product of the standard affine charts where the homogeneous
coordinate `i` of the first factor and `j` of the second are `1`. -/
noncomputable def prodChartEquations (i : Fin (m + 1)) (j : Fin (n + 1))
    (p : ι → MvPolynomial (Fin (m + 1) ⊕ Fin (n + 1)) 𝕜) :
    (Fin m → 𝕜) × (Fin n → 𝕜) → ι → 𝕜 :=
  fun u k ↦ eval (Sum.elim (i.insertNth 1 u.1) (j.insertNth 1 u.2)) (p k)

/-- The value of the chart equations, by definition. -/
theorem prodChartEquations_apply (i : Fin (m + 1)) (j : Fin (n + 1))
    (p : ι → MvPolynomial (Fin (m + 1) ⊕ Fin (n + 1)) 𝕜) (u : (Fin m → 𝕜) × (Fin n → 𝕜))
    (k : ι) :
    prodChartEquations i j p u k =
      eval (Sum.elim (i.insertNth 1 u.1) (j.insertNth 1 u.2)) (p k) := (rfl)

/-- The linear part of `u ↦ Sum.elim (i.insertNth 1 u.1) (j.insertNth 1 u.2)`. -/
private noncomputable def chartLin (i : Fin (m + 1)) (j : Fin (n + 1)) :
    (Fin m → 𝕜) × (Fin n → 𝕜) →L[𝕜] (Fin (m + 1) ⊕ Fin (n + 1) → 𝕜) :=
  ContinuousLinearMap.pi fun x ↦ Sum.elim
    (fun a ↦ Fin.insertNth (α := fun _ ↦ (Fin m → 𝕜) × (Fin n → 𝕜) →L[𝕜] 𝕜) i 0
      (fun b ↦ (ContinuousLinearMap.proj b).comp (ContinuousLinearMap.fst 𝕜 _ _)) a)
    (fun a ↦ Fin.insertNth (α := fun _ ↦ (Fin m → 𝕜) × (Fin n → 𝕜) →L[𝕜] 𝕜) j 0
      (fun b ↦ (ContinuousLinearMap.proj b).comp (ContinuousLinearMap.snd 𝕜 _ _)) a) x

private theorem chartLin_apply (i : Fin (m + 1)) (j : Fin (n + 1))
    (u : (Fin m → 𝕜) × (Fin n → 𝕜)) :
    chartLin (𝕜 := 𝕜) i j u = Sum.elim (i.insertNth 0 u.1) (j.insertNth 0 u.2) := by
  ext (a | a)
  · refine Fin.succAboveCases i ?_ (fun b ↦ ?_) a <;> simp [chartLin]
  · refine Fin.succAboveCases j ?_ (fun b ↦ ?_) a <;> simp [chartLin]

private theorem sumElim_insertNth_eq (i : Fin (m + 1)) (j : Fin (n + 1))
    (u : (Fin m → 𝕜) × (Fin n → 𝕜)) :
    Sum.elim (i.insertNth 1 u.1) (j.insertNth 1 u.2) =
      Sum.elim (i.insertNth 1 0) (j.insertNth 1 0) + chartLin (𝕜 := 𝕜) i j u := by
  rw [chartLin_apply]
  ext (a | a)
  · refine Fin.succAboveCases i ?_ (fun b ↦ ?_) a <;> simp
  · refine Fin.succAboveCases j ?_ (fun b ↦ ?_) a <;> simp

/-- The chart equations are polynomial, hence analytic. -/
theorem contDiff_prodChartEquations [Fintype ι] (i : Fin (m + 1)) (j : Fin (n + 1))
    (p : ι → MvPolynomial (Fin (m + 1) ⊕ Fin (n + 1)) 𝕜) {r : ℕ∞ω} :
    ContDiff 𝕜 r (prodChartEquations i j p) := by
  have hg : ContDiff 𝕜 r fun u : (Fin m → 𝕜) × (Fin n → 𝕜) ↦
      Sum.elim (i.insertNth 1 u.1) (j.insertNth 1 u.2) := by
    simp_rw [sumElim_insertNth_eq]
    exact contDiff_const.add (chartLin (𝕜 := 𝕜) i j).contDiff
  exact contDiff_pi.2 fun k ↦ (AnalyticOnNhd.eval_mvPolynomial (p k)).contDiff.comp hg

/-- The derivative of the chart equations at `a` sends `(x, y)` to the cone Jacobian at the
chart point `Sum.elim (i.insertNth 1 a.1) (j.insertNth 1 a.2)` applied to the vector with
`x` and `y` in the retained coordinates and `0` in the coordinates `i` and `j`. -/
theorem fderiv_prodChartEquations_apply (i : Fin (m + 1)) (j : Fin (n + 1))
    (p : ι → MvPolynomial (Fin (m + 1) ⊕ Fin (n + 1)) 𝕜) (a x : (Fin m → 𝕜) × (Fin n → 𝕜)) :
    fderiv 𝕜 (prodChartEquations i j p) a x =
      jacobiMatrixAt p (Sum.elim (i.insertNth 1 a.1) (j.insertNth 1 a.2)) *ᵥ
        Sum.elim (i.insertNth 0 x.1) (j.insertNth 0 x.2) := by
  set c := Sum.elim (i.insertNth 1 (0 : Fin m → 𝕜)) (j.insertNth 1 (0 : Fin n → 𝕜))
  have hg : HasFDerivAt (fun u : (Fin m → 𝕜) × (Fin n → 𝕜) ↦
      Sum.elim (i.insertNth 1 u.1) (j.insertNth 1 u.2)) (chartLin (𝕜 := 𝕜) i j) a := by
    simp_rw [sumElim_insertNth_eq]
    exact (chartLin (𝕜 := 𝕜) i j).hasFDerivAt.const_add c
  have h := (TauCeti.hasFDerivAt_eval_family p _).comp a hg
  have e : prodChartEquations i j p = (fun y ↦ fun k ↦ eval y (p k)) ∘
      fun u : (Fin m → 𝕜) × (Fin n → 𝕜) ↦ Sum.elim (i.insertNth 1 u.1) (j.insertNth 1 u.2) :=
    funext fun u ↦ funext fun k ↦ prodChartEquations_apply i j p u k
  rw [e, h.fderiv]
  have := congrArg (fun T : (_ →ₗ[𝕜] ι → 𝕜) ↦ T (chartLin (𝕜 := 𝕜) i j x))
    (TauCeti.fderiv_eval_family p (Sum.elim (i.insertNth 1 a.1) (j.insertNth 1 a.2)))
  simp only [ContinuousLinearMap.coe_coe, Matrix.mulVecLin_apply] at this
  rw [ContinuousLinearMap.comp_apply, ← chartLin_apply, ← this,
    (TauCeti.hasFDerivAt_eval_family p _).fderiv]

/-- The chart equations have a strict derivative everywhere. -/
theorem hasStrictFDerivAt_prodChartEquations [Finite ι] (i : Fin (m + 1)) (j : Fin (n + 1))
    (p : ι → MvPolynomial (Fin (m + 1) ⊕ Fin (n + 1)) 𝕜) (a : (Fin m → 𝕜) × (Fin n → 𝕜)) :
    HasStrictFDerivAt (prodChartEquations i j p) (fderiv 𝕜 (prodChartEquations i j p) a) a := by
  cases nonempty_fintype ι
  exact (contDiff_prodChartEquations i j p (r := 1)).contDiffAt.hasStrictFDerivAt_fderiv
    one_ne_zero

section Bihomogeneous

variable {d₁ d₂ : ι → ℕ}

/-- At a zero in the chart, the derivative of the chart equations is surjective exactly when the
cone Jacobian at the chart point is: the two Euler relations give two vectors in its kernel whose
coordinates `Sum.inl i` and `Sum.inr j` are `1` and `0`, and `0` and `1`. -/
theorem surjective_fderiv_prodChartEquations_iff {i : Fin (m + 1)} {j : Fin (n + 1)}
    {p : ι → MvPolynomial (Fin (m + 1) ⊕ Fin (n + 1)) 𝕜}
    (hp₁ : ∀ k, (p k).IsWeightedHomogeneous (Sum.elim 1 0) (d₁ k))
    (hp₂ : ∀ k, (p k).IsWeightedHomogeneous (Sum.elim 0 1) (d₂ k))
    {a : (Fin m → 𝕜) × (Fin n → 𝕜)} (ha : ∀ k, prodChartEquations i j p a k = 0) :
    Function.Surjective (fderiv 𝕜 (prodChartEquations i j p) a) ↔
      Function.Surjective
        (jacobiMatrixAt p (Sum.elim (i.insertNth 1 a.1) (j.insertNth 1 a.2))).mulVec := by
  set b := Sum.elim (i.insertNth 1 a.1) (j.insertNth 1 a.2)
  have hb : ∀ k, eval b (p k) = 0 := fun k ↦ (prodChartEquations_apply i j p a k).symm.trans (ha k)
  rw [show ⇑(fderiv 𝕜 (prodChartEquations i j p) a) = fun x ↦
      jacobiMatrixAt p b *ᵥ Sum.elim (i.insertNth 0 x.1) (j.insertNth 0 x.2) from
    funext (fderiv_prodChartEquations_apply i j p a)]
  refine ⟨fun h y ↦ ?_, fun h y ↦ ?_⟩
  · obtain ⟨x, hx⟩ := h y
    exact ⟨_, hx⟩
  obtain ⟨z, rfl⟩ := h y
  have h₁ := jacobiMatrixAt_mulVec_weight_mul_eq_zero hp₁ hb
  have h₂ := jacobiMatrixAt_mulVec_weight_mul_eq_zero hp₂ hb
  refine ⟨(fun c ↦ z (.inl (i.succAbove c)) - z (.inl i) * a.1 c,
    fun c ↦ z (.inr (j.succAbove c)) - z (.inr j) * a.2 c), ?_⟩
  have hz : Sum.elim (i.insertNth 0 fun c ↦ z (.inl (i.succAbove c)) - z (.inl i) * a.1 c)
      (j.insertNth 0 fun c ↦ z (.inr (j.succAbove c)) - z (.inr j) * a.2 c) =
      z - z (.inl i) • (fun x ↦ ((Sum.elim 1 0 x : ℕ) : 𝕜) * b x) -
        z (.inr j) • (fun x ↦ ((Sum.elim 0 1 x : ℕ) : 𝕜) * b x) := by
    ext (c | c)
    · refine Fin.succAboveCases i ?_ (fun e ↦ ?_) c <;> simp [b]
    · refine Fin.succAboveCases j ?_ (fun e ↦ ?_) c <;> simp [b]
  simp only [hz, mulVec_sub, mulVec_smul, h₁, h₂, smul_zero, sub_zero]

/-- How the cone Jacobian of a bihomogeneous family changes when the two blocks of the point
are scaled by `s` and `t`: the entry in row `k` and column `x`, multiplied by `s` if `x` lies in
the first block and by `t` if it lies in the second, is `s ^ d₁ k * t ^ d₂ k` times the entry at
the unscaled point. -/
theorem jacobiMatrixAt_sumElim_smul_mul {K : Type*} [Field K]
    {p : ι → MvPolynomial (Fin (m + 1) ⊕ Fin (n + 1)) K}
    (hp₁ : ∀ k, (p k).IsWeightedHomogeneous (Sum.elim 1 0) (d₁ k))
    (hp₂ : ∀ k, (p k).IsWeightedHomogeneous (Sum.elim 0 1) (d₂ k)) (s t : K)
    (v : Fin (m + 1) → K) (w : Fin (n + 1) → K) (k : ι) (x : Fin (m + 1) ⊕ Fin (n + 1)) :
    s ^ (Sum.elim 1 0 x : ℕ) * t ^ (Sum.elim 0 1 x : ℕ) *
        jacobiMatrixAt p (Sum.elim (s • v) (t • w)) k x =
      s ^ d₁ k * t ^ d₂ k * jacobiMatrixAt p (Sum.elim v w) k x := by
  have h₁ := (hp₁ k).aeval_pow_mul_pderiv s
    (fun y ↦ t ^ (Sum.elim 0 1 y : ℕ) * Sum.elim v w y) x
  have h₂ := (hp₂ k).aeval_pow_mul_pderiv t (Sum.elim v w) x
  have hz : (fun y ↦ s ^ (Sum.elim 1 0 y : ℕ) * (t ^ (Sum.elim 0 1 y : ℕ) * Sum.elim v w y)) =
      Sum.elim (s • v) (t • w) := by
    ext (c | c) <;> simp
  simp only [hz, aeval_eq_eval] at h₁ h₂
  simp only [jacobiMatrixAt_apply]
  linear_combination t ^ (Sum.elim 0 1 x : ℕ) * h₁ + s ^ d₁ k * h₂

/-- Scaling the two blocks of the point by nonzero scalars does not change whether the cone
Jacobian of a bihomogeneous family is surjective. -/
theorem mulVec_surjective_jacobiMatrixAt_sumElim_smul_iff {K : Type*} [Field K]
    {p : ι → MvPolynomial (Fin (m + 1) ⊕ Fin (n + 1)) K}
    (hp₁ : ∀ k, (p k).IsWeightedHomogeneous (Sum.elim 1 0) (d₁ k))
    (hp₂ : ∀ k, (p k).IsWeightedHomogeneous (Sum.elim 0 1) (d₂ k)) {s t : K} (hs : s ≠ 0)
    (ht : t ≠ 0) (v : Fin (m + 1) → K) (w : Fin (n + 1) → K) :
    (jacobiMatrixAt p (Sum.elim (s • v) (t • w))).mulVec.Surjective ↔
      (jacobiMatrixAt p (Sum.elim v w)).mulVec.Surjective := by
  have key (s t : K) (hs : s ≠ 0) (ht : t ≠ 0) (v : Fin (m + 1) → K) (w : Fin (n + 1) → K)
      (h : (jacobiMatrixAt p (Sum.elim v w)).mulVec.Surjective) :
      (jacobiMatrixAt p (Sum.elim (s • v) (t • w))).mulVec.Surjective := fun y ↦ by
    obtain ⟨x, hx⟩ := h fun k ↦ (s ^ d₁ k * t ^ d₂ k)⁻¹ * y k
    refine ⟨fun c ↦ s ^ (Sum.elim 1 0 c : ℕ) * t ^ (Sum.elim 0 1 c : ℕ) * x c, funext fun k ↦ ?_⟩
    have hk := congr_fun hx k
    have hst : s ^ d₁ k * t ^ d₂ k ≠ 0 := mul_ne_zero (pow_ne_zero _ hs) (pow_ne_zero _ ht)
    simp only [mulVec, dotProduct] at hk ⊢
    calc ∑ c, jacobiMatrixAt p (Sum.elim (s • v) (t • w)) k c *
          (s ^ (Sum.elim 1 0 c : ℕ) * t ^ (Sum.elim 0 1 c : ℕ) * x c)
        = ∑ c, s ^ d₁ k * t ^ d₂ k * (jacobiMatrixAt p (Sum.elim v w) k c * x c) :=
          Finset.sum_congr rfl fun c _ ↦ by
            linear_combination x c * jacobiMatrixAt_sumElim_smul_mul hp₁ hp₂ s t v w k c
      _ = y k := by rw [← Finset.mul_sum, hk, mul_inv_cancel_left₀ hst]
  refine ⟨fun h ↦ ?_, key s t hs ht v w⟩
  simpa [smul_smul, hs, ht] using key s⁻¹ t⁻¹ (inv_ne_zero hs) (inv_ne_zero ht) _ _ h

/-- Whether the cone Jacobian of a bihomogeneous family is surjective at a pair of nonzero
vectors depends only on the pair of projective points they represent. -/
theorem mulVec_surjective_jacobiMatrixAt_sumElim_iff_of_mk_eq_mk {K : Type*} [Field K]
    {p : ι → MvPolynomial (Fin (m + 1) ⊕ Fin (n + 1)) K}
    (hp₁ : ∀ k, (p k).IsWeightedHomogeneous (Sum.elim 1 0) (d₁ k))
    (hp₂ : ∀ k, (p k).IsWeightedHomogeneous (Sum.elim 0 1) (d₂ k))
    {v v' : Fin (m + 1) → K} {w w' : Fin (n + 1) → K} (hv : v ≠ 0) (hv' : v' ≠ 0)
    (hw : w ≠ 0) (hw' : w' ≠ 0) (h₁ : mk K v hv = mk K v' hv') (h₂ : mk K w hw = mk K w' hw') :
    (jacobiMatrixAt p (Sum.elim v w)).mulVec.Surjective ↔
      (jacobiMatrixAt p (Sum.elim v' w')).mulVec.Surjective := by
  obtain ⟨s, rfl⟩ := (mk_eq_mk_iff' K v v' hv hv').mp h₁
  obtain ⟨t, rfl⟩ := (mk_eq_mk_iff' K w w' hw hw').mp h₂
  exact mulVec_surjective_jacobiMatrixAt_sumElim_smul_iff hp₁ hp₂ (left_ne_zero_of_smul hv)
    (left_ne_zero_of_smul hw) v' w'

/-- Scaling the two blocks of the point by `s` and `t` multiplies the value of an equation of
bidegree `(d₁ k, d₂ k)` by `s ^ d₁ k * t ^ d₂ k`. -/
private theorem eval_sumElim_smul {K : Type*} [Field K]
    {p : ι → MvPolynomial (Fin (m + 1) ⊕ Fin (n + 1)) K}
    (hp₁ : ∀ k, (p k).IsWeightedHomogeneous (Sum.elim 1 0) (d₁ k))
    (hp₂ : ∀ k, (p k).IsWeightedHomogeneous (Sum.elim 0 1) (d₂ k)) (s t : K)
    (v : Fin (m + 1) → K) (w : Fin (n + 1) → K) (k : ι) :
    eval (Sum.elim (s • v) (t • w)) (p k) = s ^ d₁ k * t ^ d₂ k * eval (Sum.elim v w) (p k) := by
  have h₁ := (hp₁ k).aeval_pow_mul s (fun y ↦ t ^ (Sum.elim 0 1 y : ℕ) * Sum.elim v w y)
  have h₂ := (hp₂ k).aeval_pow_mul t (Sum.elim v w)
  have hz : (fun y ↦ s ^ (Sum.elim 1 0 y : ℕ) * (t ^ (Sum.elim 0 1 y : ℕ) * Sum.elim v w y)) =
      Sum.elim (s • v) (t • w) := by
    ext (c | c) <;> simp
  simp only [hz, aeval_eq_eval] at h₁ h₂
  rw [h₁, h₂, mul_assoc]

/-- **The regularity test in a product of affine charts.** At a common zero `(v, w)` of a
bihomogeneous family with `v i ≠ 0` and `w j ≠ 0`, the derivative of the chart equations at the
chart coordinates of `(mk v, mk w)` is surjective exactly when the cone Jacobian at
`Sum.elim v w` is. -/
theorem surjective_fderiv_prodChartEquations_affineChart_iff {i : Fin (m + 1)} {j : Fin (n + 1)}
    {p : ι → MvPolynomial (Fin (m + 1) ⊕ Fin (n + 1)) 𝕜}
    (hp₁ : ∀ k, (p k).IsWeightedHomogeneous (Sum.elim 1 0) (d₁ k))
    (hp₂ : ∀ k, (p k).IsWeightedHomogeneous (Sum.elim 0 1) (d₂ k))
    {v : Fin (m + 1) → 𝕜} {w : Fin (n + 1) → 𝕜} (hv : v ≠ 0) (hw : w ≠ 0) (hi : v i ≠ 0)
    (hj : w j ≠ 0) (hpvw : ∀ k, eval (Sum.elim v w) (p k) = 0) :
    Function.Surjective (fderiv 𝕜 (prodChartEquations i j p)
      (affineChart i (mk 𝕜 v hv), affineChart j (mk 𝕜 w hw))) ↔
      Function.Surjective (jacobiMatrixAt p (Sum.elim v w)).mulVec := by
  have hb : Sum.elim (i.insertNth 1 (affineChart i (mk 𝕜 v hv)))
      (j.insertNth 1 (affineChart j (mk 𝕜 w hw))) = Sum.elim ((v i)⁻¹ • v) ((w j)⁻¹ • w) := by
    rw [affineChart_mk, affineChart_mk, Fin.insertNth_one_div_eq_inv_smul i v hi,
      Fin.insertNth_one_div_eq_inv_smul j w hj]
  rw [surjective_fderiv_prodChartEquations_iff hp₁ hp₂ fun k ↦ by
      rw [prodChartEquations_apply, hb, eval_sumElim_smul hp₁ hp₂, hpvw, mul_zero], hb,
    mulVec_surjective_jacobiMatrixAt_sumElim_smul_iff hp₁ hp₂ (inv_ne_zero hi) (inv_ne_zero hj)]

/-- At a common zero `(v, w)` of a bihomogeneous family at which the cone Jacobian is surjective,
there are at most `m + n` equations. -/
theorem card_le_of_mulVec_surjective_jacobiMatrixAt_sumElim [Fintype ι]
    {p : ι → MvPolynomial (Fin (m + 1) ⊕ Fin (n + 1)) 𝕜}
    (hp₁ : ∀ k, (p k).IsWeightedHomogeneous (Sum.elim 1 0) (d₁ k))
    (hp₂ : ∀ k, (p k).IsWeightedHomogeneous (Sum.elim 0 1) (d₂ k))
    {v : Fin (m + 1) → 𝕜} {w : Fin (n + 1) → 𝕜} (hv : v ≠ 0) (hw : w ≠ 0)
    (hpvw : ∀ k, eval (Sum.elim v w) (p k) = 0)
    (hJ : Function.Surjective (jacobiMatrixAt p (Sum.elim v w)).mulVec) :
    Fintype.card ι ≤ m + n := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hw
  have h := LinearMap.finrank_le_finrank_of_surjective
    (f := (fderiv 𝕜 (prodChartEquations i j p)
      (affineChart i (mk 𝕜 v hv), affineChart j (mk 𝕜 w hw))).toLinearMap)
    ((surjective_fderiv_prodChartEquations_affineChart_iff hp₁ hp₂ hv hw hi hj hpvw).mpr hJ)
  simpa using h

end Bihomogeneous

end SymplecticGeometry

end
