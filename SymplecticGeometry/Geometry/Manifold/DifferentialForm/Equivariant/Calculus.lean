/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
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

## Main definitions

* `SymplecticGeometry.formCalculusCoeff F hF f k`: the smooth function `F⁽ᵏ⁾ ∘ f`.
* `SymplecticGeometry.formCalculus F hF f τ`: the form `F(f + τ)` of mixed degree.

## Main results

* `SymplecticGeometry.formCalculus_apply`: its component of degree `2 k` is `F⁽ᵏ⁾(f) τ ^ k / k!`,
  and `SymplecticGeometry.formCalculus_apply_of_odd`: its components of odd degree vanish.
* `SymplecticGeometry.formCalculus_zero_component`: its component of degree `0` is `F ∘ f`.
* `SymplecticGeometry.formCalculus_id`: for `F = id` it is `f + τ`, and
  `SymplecticGeometry.formCalculus_const`: for a constant `F = c` it is `c`.
* `SymplecticGeometry.formCalculus_mul`: the calculus is multiplicative,
  `(F G)(f + τ) = F(f + τ) G(f + τ)`, by the Leibniz rule
  `SymplecticGeometry.formCalculusCoeff_mul` for its coefficients.
* `SymplecticGeometry.tsupport_formCalculus_subset`: each component vanishes outside
  `f ⁻¹' tsupport F`.

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

omit [FiniteDimensional ℝ E] in
/-- `F(f + τ)` as a polynomial in the two-form `τ`, with the functions `F⁽ᵏ⁾ ∘ f / k!` as
coefficients, in the algebra of forms of mixed degree. -/
private theorem formCalculus_eq_sum_pow :
    formCalculus F hF f τ = ∑ k ∈ Finset.range (finrank ℝ E + 1),
      (k ! : ℝ)⁻¹ • (DirectSum.of (fun k ↦ SmoothForm I M ℝ k) 2 τ ^ k *
        DirectSum.of _ 0 (SmoothForm.ofFunction (formCalculusCoeff F hF f k))) := by
  rw [formCalculus_def]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [SmoothForm.of_pow_eq_of_wedgePow, SmoothForm.of_mul_of_zero_ofFunction, DirectSum.of_smul]

omit [FiniteDimensional ℝ E] in
/-- The functional calculus is **multiplicative**: `(F G)(f + τ) = F(f + τ) G(f + τ)`. -/
theorem formCalculus_mul (G : ℝ → ℝ) (hG : ContDiff ℝ ∞ G) (hFG : ContDiff ℝ ∞ (F * G)) :
    formCalculus (F * G) hFG f τ = formCalculus F hF f τ * formCalculus G hG f τ := by
  let X := DirectSum.of (fun k ↦ SmoothForm I M ℝ k) 2 τ
  let C : C^∞⟮I, M; ℝ⟯ →+ ⨁ k, SmoothForm I M ℝ k :=
    AddMonoidHom.mk' (fun g ↦ DirectSum.of (fun k ↦ SmoothForm I M ℝ k) 0
      (SmoothForm.ofFunction g)) fun g g' ↦ by
        simp only [SmoothForm.ofFunction_eq_funSMulₗ_one g,
          SmoothForm.ofFunction_eq_funSMulₗ_one g', SmoothForm.ofFunction_eq_funSMulₗ_one (g + g'),
          SmoothForm.funSMulₗ_add, map_add]
  have hC : ∀ g g', C g * C g' = C (g * g') := fun g g' ↦ by
    simp only [C, AddMonoidHom.mk'_apply, SmoothForm.of_mul_of_zero_ofFunction,
      SmoothForm.funSMulₗ_ofFunction, mul_comm g']
  have hCX : ∀ g b, Commute (C g) (X ^ b) := fun g b ↦ by
    simp only [C, X, AddMonoidHom.mk'_apply]
    exact (SmoothForm.commute_of_of_of_even Even.zero (SmoothForm.ofFunction g) τ).pow_right b
  let n := finrank ℝ E
  have hX : ∀ m, n < m → m ≤ 2 * n → X ^ m = 0 := fun m h₁ h₂ ↦ by
    have : FiniteDimensional ℝ E := Module.finite_of_finrank_pos (by omega)
    rw [SmoothForm.of_pow_eq_of_wedgePow,
      SmoothForm.eq_zero_of_finrank_lt (by omega) (τ.wedgePow m), map_zero]
  let cF := formCalculusCoeff F hF f
  let cG := formCalculusCoeff G hG f
  let h : ℕ → ℕ → ⨁ k, SmoothForm I M ℝ k := fun a b ↦
    ((a ! : ℝ)⁻¹ * (b ! : ℝ)⁻¹) • (X ^ (a + b) * C (cF a * cG b))
  have hFC : formCalculus F hF f τ = ∑ k ∈ Finset.range (n + 1), (k ! : ℝ)⁻¹ • (X ^ k * C (cF k)) :=
    formCalculus_eq_sum_pow F hF f τ
  have hGC : formCalculus G hG f τ = ∑ k ∈ Finset.range (n + 1), (k ! : ℝ)⁻¹ • (X ^ k * C (cG k)) :=
    formCalculus_eq_sum_pow G hG f τ
  have hFGC : formCalculus (F * G) hFG f τ = ∑ k ∈ Finset.range (n + 1),
      (k ! : ℝ)⁻¹ • (X ^ k * C (formCalculusCoeff (F * G) hFG f k)) :=
    formCalculus_eq_sum_pow (F * G) hFG f τ
  have hprod : formCalculus F hF f τ * formCalculus G hG f τ =
      ∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (n + 1 - a), h a b := by
    rw [hFC, hGC, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a ha ↦ ?_
    rw [Finset.mem_range] at ha
    symm
    refine Finset.sum_subset (fun b hb ↦ by simp only [Finset.mem_range] at hb ⊢; omega)
      (fun b hb hb' ↦ ?_) |>.trans (Finset.sum_congr rfl fun b _ ↦ ?_)
    · simp only [Finset.mem_range] at hb hb'
      simp only [h, hX (a + b) (by omega) (by omega), zero_mul, smul_zero]
    · rw [smul_mul_smul_comm, mul_assoc, ← mul_assoc (C (cF a)), (hCX _ _).eq, mul_assoc, hC,
        ← mul_assoc, ← pow_add]
  rw [hprod, ← Finset.sum_range_diag_flip, hFGC]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  rw [formCalculusCoeff_mul F hF f G hG hFG, map_sum, Finset.mul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [Finset.mem_range, Nat.lt_succ_iff] at hi
  rw [map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ, mul_smul_comm, smul_smul]
  simp only [h, cF, cG, Nat.add_sub_cancel' hi]
  congr 1
  have hm := Nat.choose_mul_factorial_mul_factorial hi
  have : (m ! : ℝ) ≠ 0 := by positivity
  field_simp
  exact_mod_cast hm

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

end SymplecticGeometry

end
