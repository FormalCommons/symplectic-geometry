/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import TauCeti.Geometry.Manifold.DifferentialForm.HomotopyOperator
public import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import TauCeti.Geometry.Manifold.IsManifold.Basic

/-!
# The homotopy operator on smooth forms

Tau Ceti's homotopy operator `TauCeti.homotopyOperator` takes a `(k + 1)`-form `φ` on the
cylinder `M × [0, 1]` to the `k`-form `x ↦ ∫₀¹ φ(x, t)(∂ₜ, ·) dt` on `M`. It is defined on rough
forms; this file bundles it as a linear map `TauCeti.SmoothForm.homotopyOperator` on smooth forms,
on a smooth manifold `M` possibly with boundary or corners. Smoothness of `h φ` is
`TauCeti.IsSmoothForm.homotopyOperator`, and linearity is `TauCeti.homotopyOperator_add` with
`TauCeti.homotopyOperator_smul`.

## Main definitions

* `TauCeti.SmoothForm.homotopyOperator`: the homotopy operator, as a linear map from smooth
  `(k + 1)`-forms on `M × [0, 1]` to smooth `k`-forms on `M`.

## Main results

* `TauCeti.SmoothForm.coe_homotopyOperator`: its underlying rough form is
  `TauCeti.homotopyOperator`.
* `TauCeti.SmoothForm.mextDerivₗ_homotopyOperator_add_homotopyOperator_mextDerivₗ`: for a form
  `φ` with values in a Banach space, `d (h φ) + h (d φ) = ι₁^* φ - ι₀^* φ`, where
  `ιₜ x = (x, t)`; it is Tau Ceti's
  `TauCeti.mextDeriv_homotopyOperator_add_homotopyOperator_mextDeriv` on smooth forms.
* `TauCeti.SmoothForm.mextDerivₗ_homotopyOperator`: its case of a closed form,
  `d (h φ) = ι₁^* φ - ι₀^* φ`.
* `TauCeti.SmoothForm.mextDerivₗ_homotopyOperator_mpullback_of_contraction`: for a smooth
  `Φ : M × [0, 1] → M` from a constant map to the identity and a closed form `z` of positive
  degree with values in a Banach space, `h (Φ^* z)` is a primitive of `z`.
* `TauCeti.SmoothForm.mextDerivₗ_homotopyOperator_mpullback`: for a smooth
  `Φ : M × [0, 1] → M` from a smooth map `g` to the identity and a closed form `z` with values
  in a Banach space, `d (h (Φ^* z)) = z - g^* z`.
* `TauCeti.SmoothForm.mpullback_homotopyOperator`: naturality, `g^* (h φ) = h ((g × id)^* φ)`;
  it is Tau Ceti's `TauCeti.homotopyOperator_mpullback_prodMap_id_of_isSmoothForm` on smooth
  forms.
* `TauCeti.norm_homotopyOperator_apply_le`: a pointwise bound for `h φ` from a bound for `φ` on
  the unit time vector followed by spatial vectors.
* `TauCeti.norm_homotopyOperator_mpullback_apply_le`: for `Φ : M × [0, 1] → N` and a form `φ` on
  `N`, the operator norm of `h (Φ^* φ)` at `x` is bounded by the supremum over `t` of
  `‖φ (Φ (x, t))‖ ‖DΦ (x, t) ∂ₜ‖ ‖DΦ (x, t) ∘ inl‖ ^ k`. Its proof follows Tau Ceti's
  `TauCeti.norm_cylinderHomotopy_pullback_le`, the same bound for the flat cylinder homotopy
  operator on `E × ℝ`.

## References

* [R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982], §4.
* [A. Weil, *Sur les théorèmes de de Rham*][Weil1952], §2 (the homotopy operator of a
  contraction).
-/

public section

noncomputable section

open Set
open scoped Manifold ContDiff

namespace TauCeti

namespace SmoothForm

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

/-- The **homotopy operator** on smooth forms: the linear map taking a smooth `(k + 1)`-form `φ`
on the cylinder `M × [0, 1]` to the smooth `k`-form `x ↦ ∫₀¹ φ(x, t)(∂ₜ, ·) dt` on `M`, where
`∂ₜ` is the unit time vector (`TauCeti.homotopyOperator`). -/
def homotopyOperator :
    SmoothForm (I.prod (𝓡∂ 1)) (M × Icc (0 : ℝ) 1) F (k + 1) →ₗ[ℝ] SmoothForm I M F k where
  toFun φ := ⟨TauCeti.homotopyOperator φ.val,
    (IsSmoothForm.homotopyOperator φ.isSmoothForm).mem_smoothBundleForms⟩
  map_add' φ ψ := Subtype.ext <| TauCeti.homotopyOperator_add
    (φ.isSmoothForm.of_le (by simp)) (ψ.isSmoothForm.of_le (by simp))
  map_smul' c φ := Subtype.ext <| TauCeti.homotopyOperator_smul c φ.val

/-- The underlying rough form of the homotopy operator of a smooth form is Tau Ceti's homotopy
operator of its rough form. -/
@[simp]
theorem coe_homotopyOperator (φ : SmoothForm (I.prod (𝓡∂ 1)) (M × Icc (0 : ℝ) 1) F (k + 1)) :
    (homotopyOperator φ).val = TauCeti.homotopyOperator φ.val :=
  (rfl)

/-- **The homotopy formula.** For a smooth form `φ` on `M × [0, 1]` with values in a Banach
space, `d (h φ) + h (d φ) = ι₁^* φ - ι₀^* φ`, where `ιₜ x = (x, t)`: the homotopy operator is a
cochain homotopy between the pullbacks along the two ends of the cylinder. -/
theorem mextDerivₗ_homotopyOperator_add_homotopyOperator_mextDerivₗ [CompleteSpace F]
    (φ : SmoothForm (I.prod (𝓡∂ 1)) (M × Icc (0 : ℝ) 1) F (k + 1)) :
    mextDerivₗ I k (homotopyOperator φ) +
        homotopyOperator (mextDerivₗ (I.prod (𝓡∂ 1)) (k + 1) φ) =
      mpullback (fun x : M ↦ (x, (1 : Icc (0 : ℝ) 1))) (contMDiff_id.prodMk contMDiff_const) φ -
        mpullback (fun x : M ↦ (x, (0 : Icc (0 : ℝ) 1))) (contMDiff_id.prodMk contMDiff_const)
          φ := by
  refine Subtype.ext (funext fun x ↦ ?_)
  rw [Submodule.coe_add, Pi.add_apply, mextDerivₗ_apply, coe_homotopyOperator,
    coe_homotopyOperator, mextDerivₗ_apply,
    mextDeriv_homotopyOperator_add_homotopyOperator_mextDeriv (φ.isSmoothForm.of_le (by simp)) x,
    Submodule.coe_sub, Pi.sub_apply, coe_mpullback, coe_mpullback]

/-- **The homotopy formula for closed forms.** For a closed smooth form `φ` on `M × [0, 1]` with
values in a Banach space, the exterior derivative of `h φ` is the difference `ι₁^* φ - ι₀^* φ`
of the slices of `φ` at the ends, where `ιₜ x = (x, t)`. -/
theorem mextDerivₗ_homotopyOperator [CompleteSpace F]
    {φ : SmoothForm (I.prod (𝓡∂ 1)) (M × Icc (0 : ℝ) 1) F (k + 1)}
    (hφ : mextDerivₗ (I.prod (𝓡∂ 1)) (k + 1) φ = 0) :
    mextDerivₗ I k (homotopyOperator φ) =
      mpullback (fun x : M ↦ (x, (1 : Icc (0 : ℝ) 1))) (contMDiff_id.prodMk contMDiff_const) φ -
        mpullback (fun x : M ↦ (x, (0 : Icc (0 : ℝ) 1))) (contMDiff_id.prodMk contMDiff_const)
          φ := by
  rw [← mextDerivₗ_homotopyOperator_add_homotopyOperator_mextDerivₗ, hφ, map_zero, add_zero]

/-- **The homotopy formula for a homotopy to the identity.** Let `Φ : M × [0, 1] → M` be a smooth
homotopy from a smooth map `g`, `Φ (x, 0) = g x`, to the identity, `Φ (x, 1) = x`. For a closed
`(k + 1)`-form `z` with values in a Banach space, `d (h (Φ^* z)) = z - g^* z`. -/
theorem mextDerivₗ_homotopyOperator_mpullback [CompleteSpace F] {g : M → M}
    (hg : ContMDiff I I ∞ g) {Φ : M × unitInterval → M} (hΦ : ContMDiff (I.prod (𝓡∂ 1)) I ∞ Φ)
    (h₀ : ∀ x, Φ (x, 0) = g x) (h₁ : ∀ x, Φ (x, 1) = x) {z : SmoothForm I M F (k + 1)}
    (hz : mextDerivₗ I (k + 1) z = 0) :
    mextDerivₗ I k (homotopyOperator (mpullback Φ hΦ z)) = z - mpullback g hg z := by
  have hclosed : mextDerivₗ (I.prod (𝓡∂ 1)) (k + 1) (mpullback Φ hΦ z) = 0 := by
    rw [mextDerivₗ_mpullback, hz, map_zero]
  rw [mextDerivₗ_homotopyOperator hclosed, mpullback_mpullback, mpullback_mpullback]
  -- The end slices of the homotopy are the identity and `g`.
  have hid : Φ ∘ (fun x : M ↦ (x, (1 : unitInterval))) = id := funext h₁
  have hg' : Φ ∘ (fun x : M ↦ (x, (0 : unitInterval))) = g := funext h₀
  simp_rw [hid, hg', mpullback_id, LinearMap.id_apply]

/-- Let `Φ : M × [0, 1] → M` be a smooth contraction of `M` to `c`, with `Φ (x, 0) = c` and
`Φ (x, 1) = x`. For a closed `(k + 1)`-form `z` with values in a Banach space, the form
`h (Φ^* z)` is a primitive of `z`. -/
theorem mextDerivₗ_homotopyOperator_mpullback_of_contraction [CompleteSpace F] {c : M}
    {Φ : M × unitInterval → M} (hΦ : ContMDiff (I.prod (𝓡∂ 1)) I ∞ Φ) (h₀ : ∀ x, Φ (x, 0) = c)
    (h₁ : ∀ x, Φ (x, 1) = x) {z : SmoothForm I M F (k + 1)} (hz : mextDerivₗ I (k + 1) z = 0) :
    mextDerivₗ I k (homotopyOperator (mpullback Φ hΦ z)) = z := by
  rw [mextDerivₗ_homotopyOperator_mpullback contMDiff_const hΦ h₀ h₁ hz, mpullback_const,
    sub_zero]

/-- **Naturality of the homotopy operator.** For a smooth map `g : M' → M` and a smooth form `φ`
on `M × [0, 1]`, `g^* (h φ) = h ((g × id)^* φ)`. -/
theorem mpullback_homotopyOperator {E' H' M' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace M']
    [ChartedSpace H' M'] [IsManifold I' ∞ M'] [CompleteSpace F] {g : M' → M}
    (hg : ContMDiff I' I ∞ g) (φ : SmoothForm (I.prod (𝓡∂ 1)) (M × Icc (0 : ℝ) 1) F (k + 1)) :
    mpullback g hg (homotopyOperator φ) =
      homotopyOperator (mpullback (Prod.map g id) (hg.prodMap contMDiff_id) φ) :=
  Subtype.ext <| by
    rw [coe_mpullback, coe_homotopyOperator, coe_homotopyOperator, coe_mpullback,
      homotopyOperator_mpullback_prodMap_id_of_isSmoothForm (hg.mdifferentiable (by simp))
        (φ.isSmoothForm.of_le (by simp))]

end SmoothForm

section Norm

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

/-- **A pointwise bound for the homotopy operator.** Let `φ` be a `(k + 1)`-form on `M × [0, 1]`
and `C ≥ 0`. If, at every time `t`, the value of `φ (x, t)` on the unit time vector `∂ₜ`
followed by vectors `(vᵢ, 0)` is at most `C ∏ ‖vᵢ‖`, then `h φ` has operator norm at most `C`
at `x`. Tangent spaces are identified with the model spaces, which carry their norms. -/
theorem norm_homotopyOperator_apply_le
    {φ : RoughForm (I.prod (𝓡∂ 1)) (M × Icc (0 : ℝ) 1) F (k + 1)} {x : M} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ (t : Icc (0 : ℝ) 1) (v : Fin k → E),
      ‖φ (x, t) (Matrix.vecCons ((0 : E), (1 : TangentSpace (𝓡∂ 1) t))
        fun i ↦ ((v i : E), (0 : EuclideanSpace ℝ (Fin 1))))‖ ≤ C * ∏ i, ‖v i‖) :
    @norm (E [⋀^Fin k]→L[ℝ] F) _ (homotopyOperator φ x) ≤ C := by
  rw [homotopyOperator_apply]
  refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := C) fun t _ ↦ ?_).trans
    (by simp)
  exact ContinuousAlternatingMap.opNorm_le_bound _ hC fun v ↦ h _ v

/-- **A pointwise bound for the homotopy operator of a pullback.** Let `Φ : M × [0, 1] → N` and
let `φ` be a `(k + 1)`-form on `N`. If, for every time `t`, the product of `‖φ (Φ (x, t))‖`, of
the norm of the time derivative `DΦ (x, t) ∂ₜ` and of the `k`-th power of the norm of the
spatial derivative `DΦ (x, t) ∘ inl` is at most `C`, then `h (Φ^* φ)` has operator norm at most
`C` at `x`. Only one argument of `Φ^* φ` sees the time direction, which gives this bound rather
than one in terms of the full derivative of `Φ`. Tangent spaces are identified with the model
spaces, which carry their norms. -/
theorem norm_homotopyOperator_mpullback_apply_le {E' H' N : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace N]
    [ChartedSpace H' N] (Φ : M × Icc (0 : ℝ) 1 → N) (φ : RoughForm I' N F (k + 1)) (x : M)
    {C : ℝ}
    (h : ∀ t : Icc (0 : ℝ) 1,
      @norm (E' [⋀^Fin (k + 1)]→L[ℝ] F) _ (φ (Φ (x, t))) *
          @norm E' _ (mfderiv (I.prod (𝓡∂ 1)) I' Φ (x, t) ((0 : E), (1 : TangentSpace (𝓡∂ 1) t))) *
          @norm (E →L[ℝ] E') _
            ((mfderiv (I.prod (𝓡∂ 1)) I' Φ (x, t)).comp (.inl ℝ E (EuclideanSpace ℝ (Fin 1)))) ^ k
        ≤ C) :
    @norm (E [⋀^Fin k]→L[ℝ] F) _ (homotopyOperator (mpullback (I.prod (𝓡∂ 1)) I' Φ φ) x) ≤ C := by
  have hC : 0 ≤ C := (h 0).trans' (mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (pow_nonneg (norm_nonneg _) _))
  refine norm_homotopyOperator_apply_le hC fun t v ↦ ?_
  -- The derivative and the form at `Φ (x, t)`, with their model-space types made explicit.
  let D : E × EuclideanSpace ℝ (Fin 1) →L[ℝ] E' := mfderiv (I.prod (𝓡∂ 1)) I' Φ (x, t)
  let α : E' [⋀^Fin (k + 1)]→L[ℝ] F := φ (Φ (x, t))
  let L : E →L[ℝ] E' := D.comp (.inl ℝ E (EuclideanSpace ℝ (Fin 1)))
  rw [mpullback_apply]
  refine (α.le_opNorm _).trans ?_
  rw [Fin.prod_univ_succ]
  -- The first vector is `DΦ ∂ₜ`, and the others are `L vᵢ`.
  calc _ ≤ ‖α‖ * (@norm E' _ (mfderiv (I.prod (𝓡∂ 1)) I' Φ (x, t)
          ((0 : E), (1 : TangentSpace (𝓡∂ 1) t))) * ∏ i, (‖L‖ * ‖v i‖)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) fun i _ ↦ L.le_opNorm (v i))
          (norm_nonneg _)) (norm_nonneg _)
    _ ≤ C * ∏ i, ‖v i‖ := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
          ← mul_assoc, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right (h t) (by positivity)

end Norm

end TauCeti
