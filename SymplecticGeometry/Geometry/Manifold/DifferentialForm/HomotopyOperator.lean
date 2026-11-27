/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.HomotopyOperator
public import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import TauCeti.Geometry.Manifold.IsManifold.Basic
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Smooth
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Pullback.Smooth
import TauCeti.Geometry.Manifold.DifferentialForm.Squared

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
* `SmoothForm.mextDerivₗ_homotopyOperator_mpullback_add_homotopyOperator_mpullback_mextDerivₗ`:
  for a smooth `Φ : M × [0, 1] → N` from a smooth map `g₀` to a smooth map `g₁` and any form
  `z` on `N` with values in a Banach space, `d (h (Φ^* z)) + h (Φ^* (d z)) = g₁^* z - g₀^* z`.
  It is Tau Ceti's
  `TauCeti.mextDeriv_homotopyOperator_mpullback_add_homotopyOperator_mpullback_mextDeriv` on
  smooth forms.
* `TauCeti.SmoothForm.mextDerivₗ_homotopyOperator_mpullback`: its case of a closed form `z`,
  `d (h (Φ^* z)) = g₁^* z - g₀^* z`.
* `TauCeti.SmoothForm.mextDerivₗ_homotopyOperator_mpullback_of_contraction`: for a smooth
  `Φ : M × [0, 1] → M` from a constant map to the identity and a closed form `z` of positive
  degree with values in a Banach space, `h (Φ^* z)` is a primitive of `z`.
* `TauCeti.SmoothForm.exists_mextDerivₗ_eq_mpullback_sub_of_homotopy`: for a smooth
  `Φ : M × [0, 1] → M` from the identity to a smooth map `f` and a closed form `z` with values in
  a Banach space, `f^* z - z = d γ` for a form `γ`, namely `h (Φ^* z)`, that vanishes at every
  point that `Φ` keeps fixed.
* `TauCeti.SmoothForm.mpullback_homotopyOperator`: naturality, `g^* (h φ) = h ((g × id)^* φ)`;
  it is Tau Ceti's `TauCeti.homotopyOperator_mpullback_prodMap_id_of_isSmoothForm` on smooth
  forms.
* `TauCeti.norm_homotopyOperator_apply_le`: a pointwise bound for `h φ` from a bound for `φ` on
  the unit time vector followed by spatial vectors.
* `TauCeti.norm_homotopyOperator_mpullback_apply_le`: for `Φ : M × [0, 1] → N` and a form `φ` on
  `N`, the operator norm of `h (Φ^* φ)` at `x` is at most any bound, over all
  times `t`, of `‖φ (Φ (x, t))‖ ‖DΦ (x, t) ∂ₜ‖ ‖DΦ (x, t) ∘ inl‖ ^ k`. Its proof follows Tau Ceti's
  `TauCeti.norm_cylinderHomotopy_pullback_le`, the same bound for the flat cylinder homotopy
  operator on `E × ℝ`.
* `TauCeti.eventually_homotopyOperator_mpullback_eq_zero`: for a continuous
  `Φ : M × [0, 1] → N` mapping `S × [0, 1]` into an open set on which `φ` vanishes, with `S`
  compact, `h (Φ^* φ)` vanishes on a neighbourhood of `S`.
* `TauCeti.SmoothForm.mextDerivₗ_apply_eq_zero_of_eventuallyEq_mextDerivₗ`: a form that is `dβ`
  near `x` is closed at `x`, since `d` is local and `d² = 0`.
* `TauCeti.SmoothForm.eventually_homotopyOperator_mpullback_mextDerivₗ_eq_zero`: for a smooth
  `Φ : M × [0, 1] → N` mapping `S × [0, 1]` into an open set on which `τ = dβ`, with `S`
  compact, `h (Φ^* dτ)` vanishes on a neighbourhood of `S`.
* `TauCeti.SmoothForm.exists_mextDerivₗ_eq_sub_homotopyOperator_mpullback_on`: for a smooth
  homotopy `Φ : M × [0, 1] → M` to the identity, if `τ = dβ` on `W` and `Φ (·, 0)` maps `W₀`
  into `W`, then `τ - h (Φ^* dτ)` is exact on `W₀`.

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
  {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' ∞ N]

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
  rw [SmoothBundleForm.add_apply, mextDerivₗ_apply, coe_homotopyOperator,
    coe_homotopyOperator, mextDerivₗ_apply,
    mextDeriv_homotopyOperator_add_homotopyOperator_mextDeriv (φ.isSmoothForm.of_le (by simp)) x,
    SmoothBundleForm.sub_apply, coe_mpullback, coe_mpullback]

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

/-- **The homotopy formula along a smooth homotopy.** Let `Φ : M × [0, 1] → N` be a smooth
homotopy from a smooth map `g₀`, `Φ (x, 0) = g₀ x`, to a smooth map `g₁`, `Φ (x, 1) = g₁ x`. For
a smooth `(k + 1)`-form `z` on `N` with values in a Banach space, closed or not,
`d (h (Φ^* z)) + h (Φ^* (d z)) = g₁^* z - g₀^* z`. It is Tau Ceti's
`TauCeti.mextDeriv_homotopyOperator_mpullback_add_homotopyOperator_mpullback_mextDeriv` on smooth
forms. -/
theorem mextDerivₗ_homotopyOperator_mpullback_add_homotopyOperator_mpullback_mextDerivₗ
    [CompleteSpace F] {g₀ g₁ : M → N} (hg₀ : ContMDiff I I' ∞ g₀) (hg₁ : ContMDiff I I' ∞ g₁)
    {Φ : M × unitInterval → N} (hΦ : ContMDiff (I.prod (𝓡∂ 1)) I' ∞ Φ)
    (h₀ : ∀ x, Φ (x, 0) = g₀ x) (h₁ : ∀ x, Φ (x, 1) = g₁ x) (z : SmoothForm I' N F (k + 1)) :
    mextDerivₗ I k (homotopyOperator (mpullback Φ hΦ z)) +
        homotopyOperator (mpullback Φ hΦ (mextDerivₗ I' (k + 1) z)) =
      mpullback g₁ hg₁ z - mpullback g₀ hg₀ z := by
  have h := mextDeriv_homotopyOperator_mpullback_add_homotopyOperator_mpullback_mextDeriv
    (hΦ.of_le (by simp)) (z.isSmoothForm.of_le (by simp))
  rw [show (fun x : M ↦ Φ (x, 1)) = g₁ from funext h₁,
    show (fun x : M ↦ Φ (x, 0)) = g₀ from funext h₀] at h
  exact Subtype.ext (by simpa using h)

/-- **The homotopy formula for closed forms along a smooth homotopy.** Let
`Φ : M × [0, 1] → N` be a smooth homotopy from a smooth map `g₀`, `Φ (x, 0) = g₀ x`, to a smooth
map `g₁`, `Φ (x, 1) = g₁ x`. For a closed `(k + 1)`-form `z` on `N` with values in a Banach
space, `d (h (Φ^* z)) = g₁^* z - g₀^* z`. -/
theorem mextDerivₗ_homotopyOperator_mpullback [CompleteSpace F] {g₀ g₁ : M → N}
    (hg₀ : ContMDiff I I' ∞ g₀) (hg₁ : ContMDiff I I' ∞ g₁) {Φ : M × unitInterval → N}
    (hΦ : ContMDiff (I.prod (𝓡∂ 1)) I' ∞ Φ) (h₀ : ∀ x, Φ (x, 0) = g₀ x)
    (h₁ : ∀ x, Φ (x, 1) = g₁ x) {z : SmoothForm I' N F (k + 1)}
    (hz : mextDerivₗ I' (k + 1) z = 0) :
    mextDerivₗ I k (homotopyOperator (mpullback Φ hΦ z)) =
      mpullback g₁ hg₁ z - mpullback g₀ hg₀ z := by
  rw [← mextDerivₗ_homotopyOperator_mpullback_add_homotopyOperator_mpullback_mextDerivₗ
    hg₀ hg₁ hΦ h₀ h₁, hz, map_zero, map_zero, add_zero]

/-- Let `Φ : M × [0, 1] → M` be a smooth contraction of `M` to `c`, with `Φ (x, 0) = c` and
`Φ (x, 1) = x`. For a closed `(k + 1)`-form `z` with values in a Banach space, the form
`h (Φ^* z)` is a primitive of `z`. -/
theorem mextDerivₗ_homotopyOperator_mpullback_of_contraction [CompleteSpace F] {c : M}
    {Φ : M × unitInterval → M} (hΦ : ContMDiff (I.prod (𝓡∂ 1)) I ∞ Φ) (h₀ : ∀ x, Φ (x, 0) = c)
    (h₁ : ∀ x, Φ (x, 1) = x) {z : SmoothForm I M F (k + 1)} (hz : mextDerivₗ I (k + 1) z = 0) :
    mextDerivₗ I k (homotopyOperator (mpullback Φ hΦ z)) = z := by
  rw [mextDerivₗ_homotopyOperator_mpullback contMDiff_const contMDiff_id hΦ h₀ h₁ hz,
    mpullback_const, sub_zero, mpullback_id, LinearMap.id_apply]

/-- **A primitive of `f^* z - z` vanishing where the homotopy is stationary.** Let
`Φ : M × [0, 1] → M` be a smooth homotopy from the identity, `Φ (x, 0) = x`, to a smooth map `f`,
`Φ (x, 1) = f x`. For a closed `(k + 1)`-form `z` with values in a Banach space, there is a smooth
`k`-form `γ` with `d γ = f^* z - z` that vanishes at every `x` whose path `Φ (x, ·)` stays at `x`.
One such form is `γ = h (Φ^* z)`. -/
theorem exists_mextDerivₗ_eq_mpullback_sub_of_homotopy [CompleteSpace F] {f : M → M}
    (hf : ContMDiff I I ∞ f) {Φ : M × unitInterval → M} (hΦ : ContMDiff (I.prod (𝓡∂ 1)) I ∞ Φ)
    (h₀ : ∀ x, Φ (x, 0) = x) (h₁ : ∀ x, Φ (x, 1) = f x) {z : SmoothForm I M F (k + 1)}
    (hz : mextDerivₗ I (k + 1) z = 0) :
    ∃ γ : SmoothForm I M F k, mextDerivₗ I k γ = mpullback f hf z - z ∧
      ∀ x, (∀ t, Φ (x, t) = x) → γ.val x = 0 := by
  refine ⟨homotopyOperator (mpullback Φ hΦ z), ?_, fun x hx ↦ ?_⟩
  · rw [mextDerivₗ_homotopyOperator_mpullback contMDiff_id hf hΦ h₀ h₁ hz, mpullback_id,
      LinearMap.id_apply]
  · rw [coe_homotopyOperator, coe_mpullback]
    exact TauCeti.homotopyOperator_mpullback_apply_eq_zero hx _

/-- **Naturality of the homotopy operator.** For a smooth map `g : M' → M` and a smooth form `φ`
on `M × [0, 1]`, `g^* (h φ) = h ((g × id)^* φ)`. -/
theorem mpullback_homotopyOperator {E' H' M' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace M']
    [ChartedSpace H' M'] [IsManifold I' ∞ M'] [CompleteSpace F] {g : M' → M}
    (hg : ContMDiff I' I ∞ g) (φ : SmoothForm (I.prod (𝓡∂ 1)) (M × Icc (0 : ℝ) 1) F (k + 1)) :
    mpullback g hg (homotopyOperator φ) =
      homotopyOperator (mpullback (Prod.map g id) (hg.prodMap contMDiff_id) φ) :=
  (mpullback_eq_iff _).2 <| by
    rw [coe_homotopyOperator, coe_homotopyOperator, coe_mpullback,
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

section Vanishing

open scoped Topology

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}
  {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]

/-- The homotopy operator of a pullback `Φ^* φ` vanishes at `x` when `φ` vanishes at every point
`Φ (x, t)` of the path of `x`. -/
theorem homotopyOperator_mpullback_apply_eq_zero_of_forall {Φ : M × Icc (0 : ℝ) 1 → N}
    {φ : RoughForm I' N F (k + 1)} {x : M} (h : ∀ t, φ (Φ (x, t)) = 0) :
    homotopyOperator (mpullback (I.prod (𝓡∂ 1)) I' Φ φ) x = 0 :=
  homotopyOperator_apply_eq_zero fun t v ↦ by
    rw [mpullback_apply_congr (η := 0) (h t)]
    simp

/-- Let `Φ : M × [0, 1] → N` be continuous and let `φ` be a form on `N` that vanishes on an open
set `U`. If `Φ` maps `S × [0, 1]` into `U` for a compact `S ⊆ M`, then the homotopy operator of
`Φ^* φ` vanishes on a neighbourhood of `S`. -/
theorem eventually_homotopyOperator_mpullback_eq_zero {Φ : M × Icc (0 : ℝ) 1 → N}
    (hΦ : Continuous Φ) {φ : RoughForm I' N F (k + 1)} {U : Set N} (hU : IsOpen U)
    (hφ : ∀ y ∈ U, φ y = 0) {S : Set M} (hS : IsCompact S) (hSU : ∀ x ∈ S, ∀ t, Φ (x, t) ∈ U) :
    ∀ᶠ x in 𝓝ˢ S, homotopyOperator (mpullback (I.prod (𝓡∂ 1)) I' Φ φ) x = 0 := by
  -- By the tube lemma, a neighbourhood `u` of `S` has `u × [0, 1]` inside `Φ⁻¹ U`.
  obtain ⟨u, v, hu, -, hSu, hv, huv⟩ := generalized_tube_lemma hS isCompact_univ
    (hU.preimage hΦ) fun p hp ↦ hSU p.1 hp.1 p.2
  exact Filter.mem_of_superset (hu.mem_nhdsSet.2 hSu) fun x hx ↦
    homotopyOperator_mpullback_apply_eq_zero_of_forall fun t ↦
      hφ _ (huv ⟨hx, hv (mem_univ t)⟩)

end Vanishing

namespace SmoothForm

section Exact

open scoped Topology

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}
  {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' ∞ N]

/-- A smooth form that agrees near `x` with the exterior derivative of a smooth form is closed at
`x`: if `τ = dβ` on a neighbourhood of `x`, then `dτ` vanishes at `x`. -/
theorem mextDerivₗ_apply_eq_zero_of_eventuallyEq_mextDerivₗ {τ : SmoothForm I M F (k + 1)}
    {β : SmoothForm I M F k} {x : M} (h : ∀ᶠ y in 𝓝 x, τ.val y = (mextDerivₗ I k β).val y) :
    (mextDerivₗ I (k + 1) τ).val x = 0 := by
  rw [mextDerivₗ_apply, mextDeriv_congr_of_eventuallyEq h, mextDerivₗ_apply,
    SmoothForm.mextDeriv_mextDeriv, Pi.zero_apply]

/-- Let `Φ : M × [0, 1] → N` be smooth, and let a smooth form `τ` on `N` be `dβ` on an open set
`W`. If `Φ` maps `S × [0, 1]` into `W` for a compact `S ⊆ M`, then `h (Φ^* dτ)` vanishes on a
neighbourhood of `S`. -/
theorem eventually_homotopyOperator_mpullback_mextDerivₗ_eq_zero {Φ : M × unitInterval → N}
    (hΦ : ContMDiff (I.prod (𝓡∂ 1)) I' ∞ Φ) {τ : SmoothForm I' N F (k + 1)}
    {β : SmoothForm I' N F k} {W : Set N} (hW : IsOpen W)
    (hβ : ∀ y ∈ W, (mextDerivₗ I' k β).val y = τ.val y) {S : Set M} (hS : IsCompact S)
    (hΦS : ∀ x ∈ S, ∀ t, Φ (x, t) ∈ W) :
    ∀ᶠ x in 𝓝ˢ S, (homotopyOperator (mpullback Φ hΦ (mextDerivₗ I' (k + 1) τ))).val x = 0 := by
  simp only [coe_homotopyOperator, coe_mpullback]
  exact TauCeti.eventually_homotopyOperator_mpullback_eq_zero hΦ.continuous hW
    (fun y hy ↦ mextDerivₗ_apply_eq_zero_of_eventuallyEq_mextDerivₗ <|
      Filter.eventually_of_mem (hW.mem_nhds hy) fun z hz ↦ (hβ z hz).symm) hS hΦS

/-- Let `Φ : M × [0, 1] → M` be a smooth homotopy to the identity, `Φ (x, 1) = x`, and let a
smooth form `τ` with values in a Banach space be `dβ` on a set `W`. If `Φ (·, 0)` maps a set `W₀`
into `W`, then `τ - h (Φ^* dτ)` is `dγ` on `W₀` for a smooth form `γ` on `M`. -/
theorem exists_mextDerivₗ_eq_sub_homotopyOperator_mpullback_on [CompleteSpace F]
    {Φ : M × unitInterval → M} (hΦ : ContMDiff (I.prod (𝓡∂ 1)) I ∞ Φ) (h₁ : ∀ x, Φ (x, 1) = x)
    {τ : SmoothForm I M F (k + 1)} {β : SmoothForm I M F k} {W : Set M}
    (hβ : ∀ x ∈ W, (mextDerivₗ I k β).val x = τ.val x) {W₀ : Set M}
    (hW₀ : ∀ x ∈ W₀, Φ (x, 0) ∈ W) :
    ∃ γ : SmoothForm I M F k, ∀ x ∈ W₀, (mextDerivₗ I k γ).val x =
      (τ - homotopyOperator (mpullback Φ hΦ (mextDerivₗ I (k + 1) τ))).val x := by
  have hg : ContMDiff I I ∞ fun x : M ↦ Φ (x, 0) := hΦ.comp (contMDiff_id.prodMk contMDiff_const)
  -- The homotopy formula gives `τ - h (Φ^* dτ) = g^* τ + d (h (Φ^* τ))`, with `g = Φ (·, 0)`.
  have hη : homotopyOperator (mpullback Φ hΦ (mextDerivₗ I (k + 1) τ)) =
      τ - mpullback _ hg τ - mextDerivₗ I k (homotopyOperator (mpullback Φ hΦ τ)) := by
    have h := mextDerivₗ_homotopyOperator_mpullback_add_homotopyOperator_mpullback_mextDerivₗ hg
      contMDiff_id hΦ (fun _ ↦ rfl) h₁ τ
    rw [mpullback_id, LinearMap.id_apply] at h
    rw [← h]
    abel
  refine ⟨mpullback _ hg β + homotopyOperator (mpullback Φ hΦ τ), fun x hx ↦ ?_⟩
  -- At a point of `W₀`, the form `g^* dβ = d (g^* β)` agrees with `g^* τ`.
  have hgx : (mpullback _ hg (mextDerivₗ I k β)).val x = (mpullback _ hg τ).val x := by
    rw [coe_mpullback, coe_mpullback]
    exact mpullback_apply_congr (hβ _ (hW₀ x hx))
  rw [hη, map_add, mextDerivₗ_mpullback]
  simp only [SmoothBundleForm.add_apply, SmoothBundleForm.sub_apply, hgx]
  abel

end Exact

end SmoothForm

end TauCeti
