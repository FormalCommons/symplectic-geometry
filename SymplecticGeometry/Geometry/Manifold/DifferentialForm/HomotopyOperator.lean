/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.HomotopyOperator
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
* `TauCeti.SmoothForm.mextDerivₗ_homotopyOperator`: for a closed form `φ` with values in a Banach
  space, `d (h φ) = ι₁^* φ - ι₀^* φ`, where `ιₜ x = (x, t)`.

## References

* [R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982], §4.
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
    -- `IsSmoothForm.homotopyOperator` at `r = ⊤` is stated for a `C^(⊤ + 1)` manifold.
    haveI : IsManifold I ((⊤ : ℕ∞) + 1 : WithTop ℕ∞) M := IsManifold.of_le (n := ∞) (by simp)
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
  have hclosed : mextDeriv φ.val = 0 := by
    rw [← mextDerivₗ_apply, hφ, Submodule.coe_zero]
  refine Subtype.ext (funext fun x ↦ ?_)
  rw [mextDerivₗ_apply, coe_homotopyOperator,
    mextDeriv_homotopyOperator (φ.isSmoothForm.of_le (by simp)) hclosed x, Submodule.coe_sub,
    Pi.sub_apply, coe_mpullback, coe_mpullback]

end SmoothForm

end TauCeti
