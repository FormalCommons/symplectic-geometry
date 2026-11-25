/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Equivariant.Basic
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Wedge.Smooth.Graded
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import SymplecticGeometry.Analysis.Calculus.IteratedDeriv.Support
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Smooth

/-!
# The functional calculus of an even form

For a smooth function `F : ℝ → ℝ`, a smooth function `f` on `M` and a smooth two-form `τ`, the
form of mixed degree `F(f + τ)` is defined by its Taylor expansion around `f`,
`F(f + τ) = ∑ k, F⁽ᵏ⁾(f) τ ^ k / k!`. The sum is finite, since `τ ^ k` has degree `2 k`, which
exceeds the dimension of the model space once `k` does. The exponential `e ^ (σ - ħ H)` of an
equivariant symplectic form is the case `F = Real.exp`, `f = -ħ H`, `τ = σ`.

All components of `F(f + τ)` have even degree, so the Cartan differential is a derivation on its
products (`SymplecticGeometry.cartanDiff_mul_of_even`).

If `τ` is closed and `ħ ι_X τ = d f`, so that `f + τ` is equivariantly closed, then so is
`F(f + τ)`. In the algebra of forms of mixed degree, `F(f + τ)` is the sum of the products
`(k !)⁻¹ τ ^ k F⁽ᵏ⁾(f)`. By the chain rule, `d_ħ F⁽ᵏ⁾(f) = ħ ι_X τ F⁽ᵏ⁺¹⁾(f)`, and since `τ` is
closed and of even degree, `d_ħ τ ^ (k + 1) = -(k + 1) ħ τ ^ k ι_X τ`
(`SymplecticGeometry.cartanDiff_of_pow_succ`). The Cartan differentials of
the terms of degree `2 k` and `2 k + 2` cancel in degree `2 k + 1`, and the sum telescopes to a
multiple of `τ ^ n ι_X τ F⁽ⁿ⁺¹⁾(f)` for `n = finrank ℝ E`, a form of degree `2 n + 1`, which is
zero.

## Main definitions

* `SymplecticGeometry.formCalculusCoeff F hF f k`: the smooth function `F⁽ᵏ⁾ ∘ f`.
* `SymplecticGeometry.formCalculus F hF f τ`: the form `F(f + τ)` of mixed degree.

## Main results

* `SymplecticGeometry.formCalculus_apply`: its component of degree `2 k` is `F⁽ᵏ⁾(f) τ ^ k / k!`,
  and `SymplecticGeometry.formCalculus_apply_of_odd`: its components of odd degree vanish.
* `SymplecticGeometry.formCalculus_zero_component`: its component of degree `0` is `F ∘ f`.
* `SymplecticGeometry.formCalculus_id`: for `F = id` it is `f + τ`, and
  `SymplecticGeometry.formCalculus_const`: for a constant `F = c` it is `c`.
* `SymplecticGeometry.formCalculus_eq_sum_pow`: `F(f + τ)` as a polynomial in `τ` with
  coefficients the functions `F⁽ᵏ⁾ ∘ f / k!`, in the algebra of forms of mixed degree.
* `SymplecticGeometry.formCalculus_mul`: the calculus is multiplicative,
  `(F G)(f + τ) = F(f + τ) G(f + τ)`, by the Leibniz rule
  `SymplecticGeometry.formCalculusCoeff_mul` for its coefficients.
* `SymplecticGeometry.formCalculus_sub`: the calculus is additive,
  `(F - G)(f + τ) = F(f + τ) - G(f + τ)`,
  from `SymplecticGeometry.formCalculusCoeff_sub`.
* `SymplecticGeometry.tsupport_formCalculus_subset`: each component vanishes outside
  `f ⁻¹' tsupport F`.
* `SymplecticGeometry.cartanDiff_of_formCalculusCoeff`: the Cartan differential of the
  coefficients `F⁽ᵏ⁾(f)`.
* `SymplecticGeometry.cartanDiff_formCalculus`: `F(f + τ)` is equivariantly closed when `f + τ`
  is.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §5.6.
* N. Berline, E. Getzler and M. Vergne, *Heat Kernels and Dirac Operators*, Grundlehren der
  mathematischen Wissenschaften 298, Springer, 1992, §7.2.
-/

public section

noncomputable section

open scoped ContDiff Manifold DirectSum Nat

open TauCeti Module

namespace SymplecticGeometry

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- The smooth function `x ↦ F⁽ᵏ⁾ (f x)`, the `k`-th derivative of a smooth function
`F : ℝ → ℝ` composed with a smooth function `f` on `M`. -/
def formCalculusCoeff (F : ℝ → ℝ) (hF : ContDiff ℝ ∞ F) (f : C^∞⟮I, M; ℝ⟯) (k : ℕ) :
    C^∞⟮I, M; ℝ⟯ :=
  ⟨fun x ↦ iteratedDeriv k F (f x), by
    rw [iteratedDeriv_eq_iterate]
    exact (hF.iterate_deriv k).contMDiff.comp f.contMDiff⟩

/-- The value of `F⁽ᵏ⁾ ∘ f` at `x` is `F⁽ᵏ⁾ (f x)`. -/
@[simp]
theorem formCalculusCoeff_apply (F : ℝ → ℝ) (hF : ContDiff ℝ ∞ F) (f : C^∞⟮I, M; ℝ⟯) (k : ℕ)
    (x : M) : formCalculusCoeff F hF f k x = iteratedDeriv k F (f x) :=
  (rfl)

section

variable [IsManifold I 1 M]

/-- The **functional calculus** `F(f + τ) = ∑ k, F⁽ᵏ⁾(f) τ ^ k / k!` of a smooth function
`F : ℝ → ℝ` at the sum of a smooth function `f` and a smooth two-form `τ`, a form of mixed degree
whose component of degree `2 k` is `F⁽ᵏ⁾(f) τ ^ k / k!`. The sum stops at `k = finrank ℝ E`,
beyond which the terms vanish in finite dimension (`formCalculus_apply`). -/
def formCalculus (F : ℝ → ℝ) (hF : ContDiff ℝ ∞ F) (f : C^∞⟮I, M; ℝ⟯)
    (τ : SmoothForm I M ℝ 2) : ⨁ k, SmoothForm I M ℝ k :=
  ∑ k ∈ Finset.range (finrank ℝ E + 1), DirectSum.of (fun k ↦ SmoothForm I M ℝ k) (2 * k)
    ((k ! : ℝ)⁻¹ • SmoothForm.funSMulₗ (formCalculusCoeff F hF f k) (τ.wedgePow k))

/-- The functional calculus is the finite sum of its homogeneous terms of degree `2 k`, for
`k ≤ finrank ℝ E`. -/
theorem formCalculus_def (F : ℝ → ℝ) (hF : ContDiff ℝ ∞ F) (f : C^∞⟮I, M; ℝ⟯)
    (τ : SmoothForm I M ℝ 2) :
    formCalculus F hF f τ =
      ∑ k ∈ Finset.range (finrank ℝ E + 1), DirectSum.of (fun k ↦ SmoothForm I M ℝ k) (2 * k)
        ((k ! : ℝ)⁻¹ • SmoothForm.funSMulₗ (formCalculusCoeff F hF f k) (τ.wedgePow k)) :=
  (rfl)

variable (F : ℝ → ℝ) (hF : ContDiff ℝ ∞ F) (f : C^∞⟮I, M; ℝ⟯) (τ : SmoothForm I M ℝ 2)

/-- The components of odd degree of `F(f + τ)` vanish. -/
theorem formCalculus_apply_of_odd : ∀ k, Odd k → formCalculus F hF f τ k = 0 := by
  intro k hk
  rw [formCalculus_def, DirectSum.sum_apply]
  refine Finset.sum_eq_zero fun m _ ↦ DirectSum.of_eq_of_ne _ _ _ ?_
  rintro rfl
  exact Nat.not_odd_iff_even.mpr (even_two_mul m) hk

variable [FiniteDimensional ℝ E]

/-- The component of degree `2 k` of `F(f + τ)` is `F⁽ᵏ⁾(f) τ ^ k / k!`, for every `k`. -/
@[simp]
theorem formCalculus_apply (k : ℕ) :
    formCalculus F hF f τ (2 * k) =
      (k ! : ℝ)⁻¹ • SmoothForm.funSMulₗ (formCalculusCoeff F hF f k) (τ.wedgePow k) := by
  rw [formCalculus_def, DirectSum.sum_apply, Finset.sum_eq_single k]
  · exact DirectSum.of_eq_same _ _
  · intro m _ hm
    exact DirectSum.of_eq_of_ne _ _ _ (by omega)
  · intro hk
    rw [Finset.mem_range, not_lt] at hk
    rw [SmoothForm.eq_zero_of_finrank_lt (by omega) (τ.wedgePow k), map_zero, smul_zero,
      map_zero, DirectSum.zero_apply]

/-- The component of degree `0` of `F(f + τ)` is the function `F ∘ f`. -/
@[simp]
theorem formCalculus_zero_component :
    formCalculus F hF f τ 0 = SmoothForm.ofFunction ⟨F ∘ f, hF.contMDiff.comp f.contMDiff⟩ := by
  -- The degree `2 * 0` of `formCalculus_apply` reduces to `0`.
  refine (formCalculus_apply F hF f τ 0).trans ?_
  rw [Nat.factorial_zero, Nat.cast_one, inv_one, one_smul, SmoothForm.wedgePow_zero,
    SmoothForm.funSMulₗ_ofFunction, mul_one]
  exact congrArg _ (ContMDiffMap.ext fun x ↦ by simp)

/-- The functional calculus of the identity is `f + τ`. -/
@[simp]
theorem formCalculus_id :
    formCalculus id contDiff_id f τ =
      DirectSum.of (fun k ↦ SmoothForm I M ℝ k) 0 (SmoothForm.ofFunction f) +
        DirectSum.of _ 2 τ := by
  have hcoeff : ∀ k, formCalculusCoeff id contDiff_id f k =
      if k = 0 then f else if k = 1 then 1 else 0 := fun k ↦ by
    ext x
    split_ifs <;> simp_all [iteratedDeriv_id]
  rw [formCalculus_def, Finset.sum_eq_add 0 1 zero_ne_one]
  · simp only [hcoeff, Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, inv_one, one_smul,
      SmoothForm.funSMulₗ_one, SmoothForm.wedgePow_one, SmoothForm.wedgePow_zero, one_ne_zero,
      ↓reduceIte]
    rw [SmoothForm.funSMulₗ_ofFunction, mul_one]
    -- The degrees `2 * 0` and `2 * 1` reduce to `0` and `2`.
    rfl
  · intro k _ ⟨h0, h1⟩
    simp [hcoeff, h0, h1]
  · simp
  · intro h
    rw [Finset.mem_range, not_lt] at h
    rw [SmoothForm.eq_zero_of_finrank_lt (by omega) (τ.wedgePow 1), map_zero, smul_zero,
      map_zero]

omit [FiniteDimensional ℝ E] in
/-- The functional calculus of the constant function `c` is the constant `c`. -/
@[simp]
theorem formCalculus_const (c : ℝ) :
    formCalculus (fun _ ↦ c) contDiff_const f τ = algebraMap ℝ (⨁ k, SmoothForm I M ℝ k) c := by
  rw [formCalculus_def, Finset.sum_eq_single 0, SmoothForm.algebraMap_apply_eq_of_ofFunction]
  · rw [Nat.factorial_zero, Nat.cast_one, inv_one, one_smul, SmoothForm.wedgePow_zero,
      SmoothForm.funSMulₗ_ofFunction, mul_one]
    exact congrArg _ (congrArg _ (ContMDiffMap.ext fun x ↦ by simp))
  · intro k _ hk
    have : formCalculusCoeff (fun _ ↦ c) contDiff_const f k = 0 := by
      ext x
      simp [iteratedDeriv_const, hk]
    rw [this, SmoothForm.funSMulₗ_zero, smul_zero, map_zero]
  · simp

omit [IsManifold I 1 M] [FiniteDimensional ℝ E] in
/-- The **Leibniz rule** for the coefficients of the functional calculus:
`(F G)⁽ᵐ⁾ ∘ f = ∑ i ≤ m, (m choose i) (F⁽ⁱ⁾ ∘ f) (G⁽ᵐ⁻ⁱ⁾ ∘ f)`. -/
theorem formCalculusCoeff_mul (G : ℝ → ℝ) (hG : ContDiff ℝ ∞ G) (hFG : ContDiff ℝ ∞ (F * G))
    (m : ℕ) :
    formCalculusCoeff (F * G) hFG f m =
      ∑ i ∈ Finset.range (m + 1),
        m.choose i • (formCalculusCoeff F hF f i * formCalculusCoeff G hG f (m - i)) := by
  ext x
  rw [formCalculusCoeff_apply, iteratedDeriv_mul (hF.contDiffAt.of_le (by simp))
    (hG.contDiffAt.of_le (by simp))]
  conv_rhs => rw [← ContMDiffMap.coeFnRingHom_apply, map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_nsmul, Pi.smul_apply, map_mul, Pi.mul_apply, ContMDiffMap.coeFnRingHom_apply,
    ContMDiffMap.coeFnRingHom_apply, formCalculusCoeff_apply, formCalculusCoeff_apply, nsmul_eq_mul,
    mul_assoc]

omit [IsManifold I 1 M] [FiniteDimensional ℝ E] in
/-- The coefficients of the functional calculus are additive in the function:
`(F - G)⁽ᵏ⁾ ∘ f = F⁽ᵏ⁾ ∘ f - G⁽ᵏ⁾ ∘ f`. -/
theorem formCalculusCoeff_sub (G : ℝ → ℝ) (hG : ContDiff ℝ ∞ G) (hFG : ContDiff ℝ ∞ (F - G))
    (k : ℕ) :
    formCalculusCoeff (F - G) hFG f k =
      formCalculusCoeff F hF f k - formCalculusCoeff G hG f k := by
  ext x
  conv_rhs => rw [← ContMDiffMap.coeFnRingHom_apply, map_sub, Pi.sub_apply,
    ContMDiffMap.coeFnRingHom_apply, ContMDiffMap.coeFnRingHom_apply]
  rw [formCalculusCoeff_apply, formCalculusCoeff_apply, formCalculusCoeff_apply,
    iteratedDeriv_sub (hF.contDiffAt.of_le (by simp)) (hG.contDiffAt.of_le (by simp))]

omit [FiniteDimensional ℝ E] in
/-- `F(f + τ)` is the polynomial `∑ k ≤ finrank ℝ E, (k!)⁻¹ τ ^ k (F⁽ᵏ⁾ ∘ f)` in the two-form `τ`,
computed in the algebra of forms of mixed degree, whose coefficients are the functions
`F⁽ᵏ⁾ ∘ f` as forms of degree `0`. -/
theorem formCalculus_eq_sum_pow :
    formCalculus F hF f τ = ∑ k ∈ Finset.range (finrank ℝ E + 1),
      (k ! : ℝ)⁻¹ • (DirectSum.of (fun k ↦ SmoothForm I M ℝ k) 2 τ ^ k *
        SmoothForm.ofFunctionRingHom (formCalculusCoeff F hF f k)) := by
  rw [formCalculus_def]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [SmoothForm.ofFunctionRingHom_apply, SmoothForm.of_pow_eq_of_wedgePow,
    SmoothForm.of_mul_of_zero_ofFunction, DirectSum.of_smul]

omit [FiniteDimensional ℝ E] in
/-- The functional calculus is **multiplicative**: `(F G)(f + τ) = F(f + τ) G(f + τ)`. -/
theorem formCalculus_mul (G : ℝ → ℝ) (hG : ContDiff ℝ ∞ G) (hFG : ContDiff ℝ ∞ (F * G)) :
    formCalculus (F * G) hFG f τ = formCalculus F hF f τ * formCalculus G hG f τ := by
  let X := DirectSum.of (fun k ↦ SmoothForm I M ℝ k) 2 τ
  let C := SmoothForm.ofFunctionRingHom (I := I) (M := M)
  let n := finrank ℝ E
  let cF := formCalculusCoeff F hF f
  let cG := formCalculusCoeff G hG f
  let h : ℕ → ℕ → ⨁ k, SmoothForm I M ℝ k := fun a b ↦
    ((a ! : ℝ)⁻¹ * (b ! : ℝ)⁻¹) • (X ^ (a + b) * C (cF a * cG b))
  -- Expand the product of the two polynomials in `X` into the terms `h a b`, and drop those
  -- with `a + b > n`.
  have hprod : formCalculus F hF f τ * formCalculus G hG f τ =
      ∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (n + 1 - a), h a b := by
    rw [formCalculus_eq_sum_pow F hF, formCalculus_eq_sum_pow G hG, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a ha ↦ ?_
    rw [Finset.mem_range] at ha
    symm
    refine Finset.sum_subset (fun b hb ↦ by simp only [Finset.mem_range] at hb ⊢; omega)
      (fun b hb hb' ↦ ?_) |>.trans (Finset.sum_congr rfl fun b _ ↦ ?_)
    · -- Here `n < a + b` with `a, b ≤ n`, so `n > 0`, the model space is finite-dimensional,
      -- and `X ^ (a + b)` has degree above its dimension.
      simp only [Finset.mem_range] at hb hb'
      have : FiniteDimensional ℝ E := Module.finite_of_finrank_pos (by omega)
      have hX : X ^ (a + b) = 0 := SmoothForm.of_pow_eq_zero_of_finrank_lt τ (by omega)
      simp only [h, hX, zero_mul, smul_zero]
    · -- The functions commute with `X`, so each product of terms is `h a b`.
      rw [smul_mul_smul_comm, mul_assoc, ← mul_assoc (C (cF a)),
        (SmoothForm.commute_ofFunctionRingHom _ _).eq, mul_assoc, ← map_mul, ← mul_assoc,
        ← pow_add]
  -- Regroup by `m = a + b`, and compare with `F G` term by term through the Leibniz rule.
  rw [hprod, ← Finset.sum_range_diag_flip, formCalculus_eq_sum_pow (F * G) hFG]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  rw [formCalculusCoeff_mul F hF f G hG hFG, map_sum, Finset.mul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [Finset.mem_range, Nat.lt_succ_iff] at hi
  rw [map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ, mul_smul_comm, smul_smul]
  simp only [h, cF, cG, Nat.add_sub_cancel' hi]
  congr 1
  -- The coefficients agree: `(m!)⁻¹ (m choose i) = (i!)⁻¹ ((m - i)!)⁻¹`.
  have hm := Nat.choose_mul_factorial_mul_factorial hi
  have : (m ! : ℝ) ≠ 0 := by positivity
  field_simp
  exact_mod_cast hm

omit [FiniteDimensional ℝ E] in
/-- The functional calculus is additive in the function:
`(F - G)(f + τ) = F(f + τ) - G(f + τ)`. -/
theorem formCalculus_sub (G : ℝ → ℝ) (hG : ContDiff ℝ ∞ G) (hFG : ContDiff ℝ ∞ (F - G)) :
    formCalculus (F - G) hFG f τ = formCalculus F hF f τ - formCalculus G hG f τ := by
  rw [formCalculus_eq_sum_pow, formCalculus_eq_sum_pow F hF, formCalculus_eq_sum_pow G hG,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [formCalculusCoeff_sub F hF f G hG hFG, map_sub, mul_sub, smul_sub]

/-- Each component of `F(f + τ)` vanishes outside `f ⁻¹' tsupport F`. -/
theorem tsupport_formCalculus_subset (k : ℕ) :
    tsupport (α := E [⋀^Fin k]→L[ℝ] ℝ) (formCalculus F hF f τ k).val ⊆ f ⁻¹' tsupport F := by
  refine closure_minimal (fun x hx ↦ ?_) ((isClosed_tsupport F).preimage f.contMDiff.continuous)
  by_contra hfx
  refine hx ?_
  obtain hk | hk := Nat.even_or_odd k
  · obtain ⟨m, rfl⟩ := hk.two_dvd
    rw [formCalculus_apply]
    have h : iteratedDeriv m F (f x) = 0 :=
      Function.notMem_support.mp fun h ↦ hfx (support_iteratedDeriv_subset m h)
    simp [h]
    -- The zero of the fibre is the zero of `E [⋀^Fin (2 * m)]→L[ℝ] ℝ`.
    rfl
  · rw [formCalculus_apply_of_odd F hF f τ k hk]
    -- The zero of the fibre is the zero of `E [⋀^Fin k]→L[ℝ] ℝ`.
    rfl

end

section CartanDiff

variable [IsManifold I 2 M] {X : (x : M) → TangentSpace I x}
  {hX : ContMDiff I I.tangent ∞ (fun x ↦ (X x : TangentBundle I M))} {ħ : ℝ}

/-- The Cartan differential of the coefficient `F⁽ᵏ⁾(f)`, when `ħ ι_X τ = d f`: by the chain
rule it is `ħ ι_X τ F⁽ᵏ⁺¹⁾(f)`. -/
theorem cartanDiff_of_formCalculusCoeff (F : ℝ → ℝ) (hF : ContDiff ℝ ∞ F)
    {f : C^∞⟮I, M; ℝ⟯} {τ : SmoothForm I M ℝ 2}
    (hf : ħ • SmoothForm.interiorProduct ⟨X, hX⟩ τ = mextDerivₗ I 0 (SmoothForm.ofFunction f))
    (k : ℕ) :
    cartanDiff X hX ħ (DirectSum.of (fun k ↦ SmoothForm I M ℝ k) 0
        (SmoothForm.ofFunction (formCalculusCoeff F hF f k))) =
      ħ • (DirectSum.of _ 1 (SmoothForm.interiorProduct ⟨X, hX⟩ τ) *
        DirectSum.of _ 0 (SmoothForm.ofFunction (formCalculusCoeff F hF f (k + 1)))) := by
  have hd : ∀ x, HasDerivAt (iteratedDeriv k F) (formCalculusCoeff F hF f (k + 1) x) (f x) :=
    fun x ↦ by
      rw [formCalculusCoeff_apply, iteratedDeriv_succ]
      exact ((hF.differentiable_iteratedDeriv k
        (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top k))).differentiableAt).hasDerivAt
  rw [cartanDiff_of_zero, SmoothForm.mextDerivₗ_ofFunction_comp_of_hasDerivAt
      (fun x ↦ formCalculusCoeff_apply F hF f k x) hd, ← hf, map_smul,
    SmoothForm.of_mul_of_zero_ofFunction, DirectSum.of_smul]

/-- **The functional calculus preserves equivariant closedness.** If a two-form `τ` is closed and
a smooth function `f` satisfies `ħ ι_X τ = d f`, so that `f + τ` is equivariantly closed, then
`F(f + τ)` is equivariantly closed: `d_ħ F(f + τ) = 0`. Here `F(f + τ)` is the sum of
`formCalculus`, cut off at `k = finrank ℝ E`. -/
theorem cartanDiff_formCalculus [FiniteDimensional ℝ E] (F : ℝ → ℝ) (hF : ContDiff ℝ ∞ F)
    {f : C^∞⟮I, M; ℝ⟯} {τ : SmoothForm I M ℝ 2} (hτ : mextDerivₗ I 2 τ = 0)
    (hf : ħ • SmoothForm.interiorProduct ⟨X, hX⟩ τ = mextDerivₗ I 0 (SmoothForm.ofFunction f)) :
    cartanDiff X hX ħ (formCalculus F hF f τ) = 0 := by
  set T := DirectSum.of (fun k ↦ SmoothForm I M ℝ k) 2 τ
  set U := DirectSum.of (fun k ↦ SmoothForm I M ℝ k) 1 (SmoothForm.interiorProduct ⟨X, hX⟩ τ)
  set C : ℕ → ⨁ k, SmoothForm I M ℝ k := fun k ↦
    DirectSum.of _ 0 (SmoothForm.ofFunction (formCalculusCoeff F hF f k))
  -- `B n = τ ^ n ι_X τ F⁽ⁿ⁺¹⁾(f)`; the Cartan differential of the sum telescopes in these.
  set B : ℕ → ⨁ k, SmoothForm I M ℝ k := fun n ↦ T ^ n * U * C (n + 1)
  have hC : ∀ k, cartanDiff X hX ħ (C k) = ħ • (U * C (k + 1)) :=
    cartanDiff_of_formCalculusCoeff F hF hf
  have hev : ∀ m k, Odd k → (T ^ m) k = 0 := fun m k hk ↦ by
    rw [SmoothForm.of_pow_eq_of_wedgePow]
    refine DirectSum.of_eq_of_ne _ _ _ ?_
    rintro rfl
    exact Nat.not_odd_iff_even.mpr (even_two_mul m) hk
  have hterm0 : cartanDiff X hX ħ (T ^ 0 * C 0) = ħ • B 0 := by
    rw [pow_zero, one_mul, hC]
    simp only [B, pow_zero, one_mul]
  have hT : cartanDiff X hX ħ T = (-ħ) • U := by
    rw [cartanDiff_of_succ, hτ, map_zero, zero_sub, neg_smul]
  have htermsucc : ∀ n, cartanDiff X hX ħ (T ^ (n + 1) * C (n + 1)) =
      ħ • B (n + 1) - ((n + 1 : ℕ) : ℝ) • ħ • B n := fun n ↦ by
    rw [cartanDiff_mul_of_even (hev _), cartanDiff_of_pow_succ even_two, hT, hC]
    simp only [B, T, smul_mul_assoc, mul_smul_comm, mul_assoc]
    module
  have hsum : ∀ n, ∑ k ∈ Finset.range (n + 1),
      (k ! : ℝ)⁻¹ • cartanDiff X hX ħ (T ^ k * C k) = ((n ! : ℝ)⁻¹ * ħ) • B n := fun n ↦ by
    induction n with
    | zero => rw [Finset.sum_range_one, hterm0, Nat.factorial_zero, Nat.cast_one, inv_one, one_mul,
        one_smul]
    | succ n ih =>
      rw [Finset.sum_range_succ, ih, htermsucc]
      match_scalars
      · rw [Nat.factorial_succ]
        push_cast
        field_simp
        ring
      · ring
  have hB : B (finrank ℝ E) = 0 := by
    simp only [B, T, U, C, SmoothForm.of_pow_eq_of_wedgePow, SmoothForm.of_mul_of_eq_of_wedge]
    rw [SmoothForm.eq_zero_of_finrank_lt (by omega) (SmoothForm.wedge _ _), map_zero]
  rw [formCalculus_eq_sum_pow, map_sum]
  simp only [SmoothForm.ofFunctionRingHom_apply, map_smul]
  rw [hsum, hB, smul_zero]

end CartanDiff

end SymplecticGeometry

end
