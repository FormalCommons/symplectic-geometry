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
