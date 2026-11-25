/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Equivariant.Calculus
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Smooth
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Integration.Regularity
import SymplecticGeometry.Analysis.Calculus.Hadamard

/-!
# The localization lemma

Let `θ` be a smooth one-form with zero Lie derivative along a smooth vector field `X`, let
`s = θ(X)` be the function `ι_X θ`, and let `ħ` be real. The Cartan differential of `θ` is the
even form `η = d_ħ θ = dθ - ħ s`, the sum of the function `-ħ s` and the closed two-form `dθ`.
By Cartan's formula `ι_X dθ = -d s`, so `η` is equivariantly closed, and so is every
`F(η) = formCalculus F hF (-ħ • s) (dθ)`.

If `u G(u) = 1 - F(u)` for a smooth `G` (such a `G` exists exactly when `F 0 = 1`), then by the
multiplicativity of the calculus `1 - F(η) = η G(η) = d_ħ (θ G(η))`. Multiplying by an
equivariantly closed form `β`, the difference `β - F(η) β` is `d_ħ (θ G(η) β)`, whose top
component is exact. So on a compact boundaryless manifold, `F(η) β` and `β` have the same
integral. This is the deformation argument of Berline, Getzler and Vergne, §7.2, with a general
function `F` in place of the exponential.

For `F 0 = 1`, the function `G` comes from Hadamard's lemma `ContDiff.exists_contDiff_sub_eq_smul`,
which makes it smooth also at `0`, whether or not `F' 0 = 0`.

## Main results

* `SymplecticGeometry.cartanDiff_of_one_eq_formCalculus_id`: `d_ħ θ` is `-ħ s + dθ`.
* `SymplecticGeometry.cartanDiff_formCalculus_of_mlieDerivForm_eq_zero`: `F(d_ħ θ)` is
  equivariantly closed for an invariant `θ`.
* `SymplecticGeometry.one_sub_formCalculus_eq_cartanDiff_mul`: `1 - F(η) = η G(η)` when
  `u G(u) = 1 - F(u)`, with `η = d_ħ θ`.
* `SymplecticGeometry.sub_formCalculus_eq_cartanDiff`: `1 - F(η) = d_ħ (θ G(η))` when
  `u G(u) = 1 - F(u)`.
* `SymplecticGeometry.integralTopForm_formCalculus_mul`: the localization lemma, that
  `F(η) β` and `β` have the same integral for `F 0 = 1` and `d_ħ β = 0`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §5.6.
* N. Berline, E. Getzler and M. Vergne, *Heat Kernels and Dirac Operators*, Grundlehren der
  mathematischen Wissenschaften 298, Springer, 1992, §7.2.
-/

public section

noncomputable section

open scoped ContDiff Manifold DirectSum

open TauCeti

namespace SymplecticGeometry

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {X : (x : M) → TangentSpace I x} {ħ : ℝ}

section LowRegularity

variable [IsManifold I 2 M]
  {hX : ContMDiff I I.tangent ∞ (fun x ↦ (X x : TangentBundle I M))}

/-- The Cartan differential of a one-form `θ` is the even form `-ħ θ(X) + dθ`, the functional
calculus of the identity at the function `-ħ θ(X)` and the two-form `dθ`. -/
theorem cartanDiff_of_one_eq_formCalculus_id [FiniteDimensional ℝ E]
    (θ : SmoothForm I M ℝ 1) :
    cartanDiff X hX ħ (DirectSum.of (fun k ↦ SmoothForm I M ℝ k) 1 θ) =
      formCalculus id contDiff_id
        (-ħ • SmoothForm.ofFunctionEquiv.symm (SmoothForm.interiorProduct ⟨X, hX⟩ θ))
        (mextDerivₗ I 1 θ) := by
  rw [formCalculus_id, cartanDiff_of_succ, ← SmoothForm.ofFunctionEquiv_apply, map_smul,
    LinearEquiv.apply_symm_apply, DirectSum.of_smul, neg_smul, neg_add_eq_sub]

/-- For a one-form `θ` with zero Lie derivative along `X`, the function `-ħ θ(X)` and the closed
two-form `dθ` satisfy `ħ ι_X dθ = d (-ħ θ(X))`, by Cartan's formula. -/
theorem smul_interiorProduct_mextDerivₗ_of_mlieDerivForm_eq_zero {θ : SmoothForm I M ℝ 1}
    (hθ : mlieDerivForm X θ.val = 0) :
    ħ • SmoothForm.interiorProduct ⟨X, hX⟩ (mextDerivₗ I 1 θ) =
      mextDerivₗ I 0 (SmoothForm.ofFunction
        (-ħ • SmoothForm.ofFunctionEquiv.symm (SmoothForm.interiorProduct ⟨X, hX⟩ θ))) := by
  have hL : SmoothForm.lieDeriv ⟨X, hX⟩ θ = 0 := by
    rw [SmoothForm.lieDeriv_eq_zero_iff, ContMDiffSection.coeFn_mk]
    exact hθ
  rw [SmoothForm.lieDeriv_eq_interiorProduct_add, add_eq_zero_iff_eq_neg] at hL
  rw [hL, ← SmoothForm.ofFunctionEquiv_apply, map_smul, LinearEquiv.apply_symm_apply, map_smul,
    smul_neg]
  exact (neg_smul _ _).symm

/-- For a one-form `θ` with zero Lie derivative along `X`, every functional calculus
`F(d_ħ θ) = F(-ħ θ(X) + dθ)` is equivariantly closed. -/
theorem cartanDiff_formCalculus_of_mlieDerivForm_eq_zero [FiniteDimensional ℝ E]
    (F : ℝ → ℝ) (hF : ContDiff ℝ ∞ F) {θ : SmoothForm I M ℝ 1}
    (hθ : mlieDerivForm X θ.val = 0) :
    cartanDiff X hX ħ (formCalculus F hF
      (-ħ • SmoothForm.ofFunctionEquiv.symm (SmoothForm.interiorProduct ⟨X, hX⟩ θ))
      (mextDerivₗ I 1 θ)) = 0 :=
  cartanDiff_formCalculus F hF (LinearMap.congr_fun (mextDerivₗ_comp_mextDerivₗ I 1) θ)
    (smul_interiorProduct_mextDerivₗ_of_mlieDerivForm_eq_zero hθ)

/-- If `u G(u) = 1 - F(u)`, then `1 - F(d_ħ θ)` is the product of `d_ħ θ` and `G(d_ħ θ)`, by the
multiplicativity of the functional calculus. -/
theorem one_sub_formCalculus_eq_cartanDiff_mul [FiniteDimensional ℝ E] (F : ℝ → ℝ)
    (hF : ContDiff ℝ ∞ F) (G : ℝ → ℝ) (hG : ContDiff ℝ ∞ G) (hFG : ∀ u, u * G u = 1 - F u)
    (θ : SmoothForm I M ℝ 1) :
    1 - formCalculus F hF
        (-ħ • SmoothForm.ofFunctionEquiv.symm (SmoothForm.interiorProduct ⟨X, hX⟩ θ))
        (mextDerivₗ I 1 θ) =
      cartanDiff X hX ħ (DirectSum.of (fun k ↦ SmoothForm I M ℝ k) 1 θ) *
        formCalculus G hG
          (-ħ • SmoothForm.ofFunctionEquiv.symm (SmoothForm.interiorProduct ⟨X, hX⟩ θ))
          (mextDerivₗ I 1 θ) := by
  set f := -ħ • SmoothForm.ofFunctionEquiv.symm (SmoothForm.interiorProduct ⟨X, hX⟩ θ)
  have hcongr : ∀ (K L : ℝ → ℝ) (hK : ContDiff ℝ ∞ K) (hL : ContDiff ℝ ∞ L), K = L →
      formCalculus K hK f (mextDerivₗ I 1 θ) = formCalculus L hL f (mextDerivₗ I 1 θ) := by
    rintro K L hK hL rfl
    rfl
  have h1 : (1 : ⨁ k, SmoothForm I M ℝ k) =
      formCalculus (fun _ ↦ 1) contDiff_const f (mextDerivₗ I 1 θ) := by
    rw [formCalculus_const, map_one]
  rw [cartanDiff_of_one_eq_formCalculus_id, h1,
    ← formCalculus_sub _ _ _ _ F hF (contDiff_const.sub hF),
    ← formCalculus_mul _ _ _ _ G hG (contDiff_id.mul hG)]
  exact hcongr _ _ _ _ (funext fun u ↦ (hFG u).symm)

/-- If `u G(u) = 1 - F(u)` for smooth `F` and `G`, and `θ` is a one-form with zero Lie derivative
along `X`, then `1 - F(η) = d_ħ (θ G(η))` for `η = d_ħ θ = -ħ θ(X) + dθ`. Such a `G` exists when
`F 0 = 1`, by Hadamard's lemma. -/
theorem sub_formCalculus_eq_cartanDiff [FiniteDimensional ℝ E] (F : ℝ → ℝ)
    (hF : ContDiff ℝ ∞ F) (G : ℝ → ℝ) (hG : ContDiff ℝ ∞ G) (hFG : ∀ u, u * G u = 1 - F u)
    {θ : SmoothForm I M ℝ 1} (hθ : mlieDerivForm X θ.val = 0) :
    1 - formCalculus F hF
        (-ħ • SmoothForm.ofFunctionEquiv.symm (SmoothForm.interiorProduct ⟨X, hX⟩ θ))
        (mextDerivₗ I 1 θ) =
      cartanDiff X hX ħ (DirectSum.of (fun k ↦ SmoothForm I M ℝ k) 1 θ *
        formCalculus G hG
          (-ħ • SmoothForm.ofFunctionEquiv.symm (SmoothForm.interiorProduct ⟨X, hX⟩ θ))
          (mextDerivₗ I 1 θ)) := by
  rw [cartanDiff_of_mul, cartanDiff_formCalculus_of_mlieDerivForm_eq_zero G hG hθ, mul_zero,
    smul_zero, add_zero, one_sub_formCalculus_eq_cartanDiff_mul F hF G hG hFG]

end LowRegularity

/-- **The localization lemma.** Let `θ` be a one-form with zero Lie derivative along `X`, and
`F : ℝ → ℝ` smooth with `F 0 = 1`. On a compact boundaryless manifold of dimension `m`, for every
equivariantly closed form `β`, the top components of `F(d_ħ θ) β` and of `β` have the same
integral, where `F(d_ħ θ) = F(-ħ θ(X) + dθ)` is the functional calculus. -/
theorem integralTopForm_formCalculus_mul [FiniteDimensional ℝ E] [IsManifold I ∞ M]
    {hX : ContMDiff I I.tangent ∞ (fun x ↦ (X x : TangentBundle I M))}
    [CompactSpace M] [T2Space M] [BoundarylessManifold I M] {m : ℕ}
    (o : Manifold.Orientation I M (Fin m)) (F : ℝ → ℝ) (hF : ContDiff ℝ ∞ F) (hF0 : F 0 = 1)
    {θ : SmoothForm I M ℝ 1} (hθ : mlieDerivForm X θ.val = 0)
    {β : ⨁ k, SmoothForm I M ℝ k} (hβ : cartanDiff X hX ħ β = 0) :
    integralTopForm o ((formCalculus F hF
        (-ħ • SmoothForm.ofFunctionEquiv.symm (SmoothForm.interiorProduct ⟨X, hX⟩ θ))
        (mextDerivₗ I 1 θ) * β) m).val = integralTopForm o (β m).val := by
  -- Hadamard's lemma gives a smooth `G` with `u G(u) = 1 - F(u)`.
  obtain ⟨g, hg, hFg⟩ := ContDiff.exists_contDiff_sub_eq_smul (n := ⊤) (hF.of_le (by simp)) 0
  set G : ℝ → ℝ := fun u ↦ -g u
  have hG : ContDiff ℝ ∞ G := hg.neg
  have hFG : ∀ u, u * G u = 1 - F u := fun u ↦ by
    have h := hFg u
    rw [sub_zero, hF0] at h
    rw [mul_neg, ← smul_eq_mul, ← h, neg_sub]
  set f := -ħ • SmoothForm.ofFunctionEquiv.symm (SmoothForm.interiorProduct ⟨X, hX⟩ θ)
  set T := DirectSum.of (fun k ↦ SmoothForm I M ℝ k) 1 θ
  -- `β - F(η) β = (1 - F(η)) β = d_ħ (θ G(η) β)`, since `G(η) β` is equivariantly closed.
  have hGβ : cartanDiff X hX ħ (formCalculus G hG f (mextDerivₗ I 1 θ) * β) = 0 := by
    rw [cartanDiff_mul_of_even (formCalculus_apply_of_odd G hG f _),
      cartanDiff_formCalculus_of_mlieDerivForm_eq_zero G hG hθ, hβ, zero_mul, mul_zero, add_zero]
  have hexact : β - formCalculus F hF f (mextDerivₗ I 1 θ) * β =
      cartanDiff X hX ħ (T * (formCalculus G hG f (mextDerivₗ I 1 θ) * β)) := by
    rw [cartanDiff_of_mul, hGβ, mul_zero, smul_zero, add_zero, ← mul_assoc,
      ← one_sub_formCalculus_eq_cartanDiff_mul F hF G hG hFG, sub_mul, one_mul]
  have h0 := integralTopForm_cartanDiff_eq_zero (X := X) (hX := hX) (ħ := ħ) o
    (T * (formCalculus G hG f (mextDerivₗ I 1 θ) * β))
  rw [← hexact, DirectSum.sub_apply, Submodule.coe_sub,
    integralTopForm_sub_of_compactSpace o ((β m).isSmoothForm.of_le (by simp))
      ((_ : SmoothForm I M ℝ m).isSmoothForm.of_le (by simp)), sub_eq_zero] at h0
  exact h0.symm

end SymplecticGeometry

end
