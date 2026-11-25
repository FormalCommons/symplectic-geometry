/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import SymplecticGeometry.Geometry.Manifold.IsManifold.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.HomotopyOperator
public import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth

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

end TauCeti
