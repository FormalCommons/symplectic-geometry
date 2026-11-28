/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
public import TauCeti.Geometry.Manifold.DifferentialForm.Closed
public import TauCeti.Geometry.Manifold.DifferentialForm.Regularity
public import TauCeti.Geometry.Symplectic.Liouville.VectorField
public import TauCeti.Geometry.Symplectic.Manifold.Flat
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Smooth
import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Leibniz
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# Rescaling the primitive of a Liouville field

Let `X` be a Liouville vector field of a closed two-form `σ`, so that `λ = ι_X σ` is a primitive
of `σ`, and let `h` be a smooth function. This file studies the two-form `d(h λ)`
(`SymplecticGeometry.rescaledForm σ X h`) and the vector field
`(h / (h + dh(X))) X` (`SymplecticGeometry.rescaledField X h`). By the Leibniz rule,
`d(h λ) = dh ∧ λ + h σ`, and since `λ(X) = σ(X, X) = 0`, contracting with `X` gives
`ι_X d(h λ) = (h + dh(X)) λ`. So where `h + dh(X)` does not vanish, the rescaled field is the
field dual to the primitive `h λ` of the rescaled form, and it is a Liouville field of that form.

## Main declarations

* `SymplecticGeometry.rescaledForm`: the two-form `d(h ι_X σ)`, with `rescaledForm_def` and the
  pointwise formula `rescaledForm_apply`.
* `SymplecticGeometry.rescaledField`: the field `x ↦ (h x / (h x + dh_x (X x))) • X x`, with
  `rescaledField_apply`, and its smoothness `contMDiff_rescaledField`.
* `SymplecticGeometry.interior_rescaledField_rescaledForm`: `ι_Y d(h λ) = h λ` for the rescaled
  field `Y`, when `h + dh(X)` vanishes nowhere.
* `SymplecticGeometry.isLiouvilleVectorField_rescaledField`: the rescaled field is a Liouville
  field of the rescaled form.
* `SymplecticGeometry.isNondegenerate_rescaledForm` and `isSymplectic_rescaledForm`: the rescaled
  form is nondegenerate when neither `h` nor `h + dh(X)` vanishes anywhere, and then it is
  symplectic if `σ` is.
* `SymplecticGeometry.rescaledForm_one`, `rescaledField_one`: rescaling by `1` changes nothing.
* `SymplecticGeometry.rescaledForm_add`, `rescaledForm_smul` and
  `rescaledForm_one_sub_smul_one_add_smul`: the rescaled form is linear in `h`, so that
  `t ↦ rescaledForm σ X ((1 - t) • 1 + t • h)` interpolates linearly between `σ` and
  `rescaledForm σ X h`.

## Implementation notes

The field `X` and the function `h` are bundled smooth objects, so that `h • ι_X σ` is a smooth
one-form (Tau Ceti's `TauCeti.SmoothForm.funSMulₗ` and `TauCeti.SmoothTwoForm.interiorₗ`), and the
rescaled form is its exterior derivative `TauCeti.mextDerivₗ`. No Weinstein structure is needed:
only the Liouville condition enters. Nondegeneracy is proved pointwise on the kernel: if
`ι_v d(h λ) = 0`, evaluating on `X` gives `(h + dh(X)) λ(v) = 0`, so `λ(v) = 0`; then
`ι_v σ = -(dh(v) / h) λ`, so `v` is a multiple of `X` by nondegeneracy of `σ`, and evaluating `dh`
on it gives `dh(v) = 0`, hence `v = 0`. The Leibniz rule is Tau Ceti's
`TauCeti.mextDeriv_fun_smul_apply`.

## References

* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  Lemma 12.1 (i) and Remark 12.2 (a): rescaling the Liouville form of a Weinstein structure by a
  positive function. Here only `h + dh(X) ≠ 0` (and `h ≠ 0` for nondegeneracy) is assumed,
  which holds for a positive `h` with `dh(X) ≥ 0`.
-/

public section

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace TauCeti.IsLiouvilleVectorField

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- For a closed smooth two-form `σ` and a smooth Liouville vector field `X` of `σ`, the one-form
`ι_X σ` is a primitive of `σ`: `d(ι_X σ) = σ`, as smooth forms. -/
theorem mextDerivₗ_interiorₗ {σ : SmoothTwoForm I M} (hσ : σ.IsClosed)
    {X : Cₛ^∞⟮I; E, TangentSpace I (M := M)⟯} (hX : IsLiouvilleVectorField σ.val X) :
    mextDerivₗ I 1 (σ.interiorₗ X) = σ :=
  Subtype.ext <| by
    rw [mextDerivₗ_apply, SmoothTwoForm.coe_interiorₗ]
    exact (isLiouvilleVectorField_iff_mextDeriv_interior_eq σ.mdifferentiable
      (X.contMDiff.mdifferentiable (by simp)) ((SmoothForm.isClosed_def _).1 hσ)).1 hX

end TauCeti.IsLiouvilleVectorField

namespace SymplecticGeometry

open TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ### The rescaled form -/

/-- The **rescaled form** `d(h ι_X σ)` of a two-form `σ`, a vector field `X` and a function `h`.
When `X` is a Liouville field of a closed form `σ`, it is `dh ∧ ι_X σ + h σ`
(`SymplecticGeometry.rescaledForm_apply_of_isLiouvilleVectorField`). -/
def rescaledForm (σ : SmoothTwoForm I M) (X : Cₛ^∞⟮I; E, TangentSpace I (M := M)⟯)
    (h : C^∞⟮I, M; ℝ⟯) : SmoothTwoForm I M :=
  mextDerivₗ I 1 (SmoothForm.funSMulₗ h (σ.interiorₗ X))

variable {σ : SmoothTwoForm I M} {X : Cₛ^∞⟮I; E, TangentSpace I (M := M)⟯} {h : C^∞⟮I, M; ℝ⟯}

/-- The rescaled form is, by definition, `d(h ι_X σ)`. -/
theorem rescaledForm_def (σ : SmoothTwoForm I M) (X : Cₛ^∞⟮I; E, TangentSpace I (M := M)⟯)
    (h : C^∞⟮I, M; ℝ⟯) :
    rescaledForm σ X h = mextDerivₗ I 1 (SmoothForm.funSMulₗ h (σ.interiorₗ X)) :=
  (rfl)

/-- The rescaled form is the exterior derivative of the rough one-form `x ↦ h x • (ι_X σ)_x`. -/
theorem coe_rescaledForm (σ : SmoothTwoForm I M) (X : Cₛ^∞⟮I; E, TangentSpace I (M := M)⟯)
    (h : C^∞⟮I, M; ℝ⟯) :
    (rescaledForm σ X h).val = mextDeriv (fun x ↦ h x • RoughForm.interior X σ.val x) := by
  rw [rescaledForm_def, mextDerivₗ_apply, SmoothForm.coe_funSMulₗ, SmoothTwoForm.coe_interiorₗ]

/-- The rescaled form is closed. -/
theorem isClosed_rescaledForm (σ : SmoothTwoForm I M) (X : Cₛ^∞⟮I; E, TangentSpace I (M := M)⟯)
    (h : C^∞⟮I, M; ℝ⟯) : (rescaledForm σ X h).IsClosed :=
  SmoothForm.isClosed_mextDerivₗ _

/-- **The Leibniz rule for the rescaled form.** With `λ = ι_X σ`,
`d(h λ)(v, w) = dh(v) λ(w) - dh(w) λ(v) + h dλ(v, w)`. -/
theorem rescaledForm_apply (σ : SmoothTwoForm I M) (X : Cₛ^∞⟮I; E, TangentSpace I (M := M)⟯)
    (h : C^∞⟮I, M; ℝ⟯) (x : M) (v w : TangentSpace I x) :
    (rescaledForm σ X h).val x ![v, w] =
      mvfderiv I h x v * σ.val x ![X x, w] - mvfderiv I h x w * σ.val x ![X x, v] +
        h x * mextDeriv (RoughForm.interior X σ.val) x ![v, w] := by
  have hα := (σ.interiorₗ X).mdifferentiableAt x
  rw [SmoothTwoForm.coe_interiorₗ] at hα
  rw [coe_rescaledForm, mextDeriv_fun_smul_apply (h.contMDiff.mdifferentiableAt (by simp)) hα v w,
    RoughForm.interior_apply, RoughForm.interior_apply]

/-- **The rescaled form of a Liouville field.** If `X` is a Liouville field of a closed form `σ`
and `λ = ι_X σ`, then `d(h λ) = dh ∧ λ + h σ`:
`d(h λ)(v, w) = dh(v) σ(X, w) - dh(w) σ(X, v) + h σ(v, w)`. -/
theorem rescaledForm_apply_of_isLiouvilleVectorField (hσ : σ.IsClosed)
    (hX : IsLiouvilleVectorField σ.val X) (x : M) (v w : TangentSpace I x) :
    (rescaledForm σ X h).val x ![v, w] =
      mvfderiv I h x v * σ.val x ![X x, w] - mvfderiv I h x w * σ.val x ![X x, v] +
        h x * σ.val x ![v, w] := by
  rw [rescaledForm_apply]
  congr 2
  rw [← SmoothTwoForm.coe_interiorₗ, ← mextDerivₗ_apply, hX.mextDerivₗ_interiorₗ hσ]

/-- Rescaling the primitive of a Liouville field by the constant function `1` gives back the
form. -/
@[simp]
theorem rescaledForm_one (hσ : σ.IsClosed) (hX : IsLiouvilleVectorField σ.val X) :
    rescaledForm σ X 1 = σ := by
  rw [rescaledForm_def, SmoothForm.funSMulₗ_one, hX.mextDerivₗ_interiorₗ hσ]

/-- The rescaled form is additive in the function. -/
theorem rescaledForm_add (σ : SmoothTwoForm I M) (X : Cₛ^∞⟮I; E, TangentSpace I (M := M)⟯)
    (h₁ h₂ : C^∞⟮I, M; ℝ⟯) :
    rescaledForm σ X (h₁ + h₂) = rescaledForm σ X h₁ + rescaledForm σ X h₂ := by
  simp only [rescaledForm_def, SmoothForm.funSMulₗ_add, map_add]

/-- The rescaled form commutes with constant multiples of the function. -/
theorem rescaledForm_smul (σ : SmoothTwoForm I M) (X : Cₛ^∞⟮I; E, TangentSpace I (M := M)⟯)
    (c : ℝ) (h : C^∞⟮I, M; ℝ⟯) :
    rescaledForm σ X (c • h) = c • rescaledForm σ X h := by
  have hc : SmoothForm.funSMulₗ (c • h) (σ.interiorₗ X) =
      c • SmoothForm.funSMulₗ h (σ.interiorₗ X) :=
    Subtype.ext <| funext fun x ↦ by
      simp only [SmoothForm.coe_funSMulₗ, ContMDiffMap.coe_smul, Pi.smul_apply, smul_eq_mul,
        Submodule.coe_smul, mul_smul]
  rw [rescaledForm_def, rescaledForm_def, hc, map_smul]

/-- **The rescaled form is affine in the function.** For a Liouville field `X` of a closed form
`σ`, rescaling by `(1 - t) • 1 + t • h` gives `(1 - t) • σ + t • rescaledForm σ X h`. -/
theorem rescaledForm_one_sub_smul_one_add_smul (hσ : σ.IsClosed)
    (hX : IsLiouvilleVectorField σ.val X) (h : C^∞⟮I, M; ℝ⟯) (t : ℝ) :
    rescaledForm σ X ((1 - t) • 1 + t • h) = (1 - t) • σ + t • rescaledForm σ X h := by
  rw [rescaledForm_add, rescaledForm_smul, rescaledForm_smul, rescaledForm_one hσ hX]

/-! ### The rescaled field -/

/-- The **rescaled field** `(h / (h + dh(X))) X` of a vector field `X` and a function `h`. -/
def rescaledField (X : (x : M) → TangentSpace I x) (h : M → ℝ) : (x : M) → TangentSpace I x :=
  fun x ↦ (h x / (h x + mvfderiv I h x (X x))) • X x

omit [IsManifold I ∞ M] in
/-- The value of the rescaled field at a point. -/
theorem rescaledField_apply (X : (x : M) → TangentSpace I x) (h : M → ℝ) (x : M) :
    rescaledField X h x = (h x / (h x + mvfderiv I h x (X x))) • X x :=
  (rfl)

omit [IsManifold I ∞ M] in
/-- Rescaling by the constant function `1` leaves the field unchanged. -/
@[simp]
theorem rescaledField_one (X : (x : M) → TangentSpace I x) : rescaledField X 1 = X := by
  funext x
  rw [rescaledField_apply, Pi.one_apply, Pi.one_def, mvfderiv_const]
  simp

/-- The rescaled field of smooth `X` and `h` is smooth where `h + dh(X)` vanishes nowhere. -/
theorem contMDiff_rescaledField (hne : ∀ x, h x + mvfderiv I h x (X x) ≠ 0) :
    ContMDiff I I.tangent ∞ (T% (rescaledField X h)) := by
  have hc : ContMDiff I 𝓘(ℝ, ℝ) ∞ fun x ↦ h x / (h x + mvfderiv I h x (X x)) :=
    h.contMDiff.div₀ (h.contMDiff.add
      ((h.contMDiff.contMDiff_mvfderiv_apply (by simp)).comp X.contMDiff)) hne
  exact hc.smul_section X.contMDiff

/-! ### The rescaled structure -/

/-- **The contraction of the rescaled form with the rescaled field.** If `X` is a Liouville field
of a closed form `σ` and `h + dh(X)` vanishes nowhere, then
`ι_Y d(h ι_X σ) = h ι_X σ` for `Y = (h / (h + dh(X))) X`. -/
theorem interior_rescaledField_rescaledForm (hσ : σ.IsClosed)
    (hX : IsLiouvilleVectorField σ.val X) (hne : ∀ x, h x + mvfderiv I h x (X x) ≠ 0) :
    RoughForm.interior (rescaledField X h) (rescaledForm σ X h).val =
      (SmoothForm.funSMulₗ h (σ.interiorₗ X)).val := by
  funext x
  ext v
  have hv : v = ![v 0] := (FinVec.etaExpand_eq v).symm
  rw [hv, RoughForm.interior_apply, SmoothForm.coe_funSMulₗ, SmoothTwoForm.coe_interiorₗ,
    ContinuousAlternatingMap.smul_apply, RoughForm.interior_apply, rescaledField_apply]
  -- The pair `![c • X x, v 0]`, written so that the formula of the rescaled form applies.
  rw [show (Matrix.vecCons ((h x / (h x + mvfderiv I h x (X x))) • X x) ![v 0] :
      Fin 2 → TangentSpace I x) = ![(h x / (h x + mvfderiv I h x (X x))) • X x, v 0] from rfl,
    rescaledForm_apply_of_isLiouvilleVectorField hσ hX]
  set c := h x / (h x + mvfderiv I h x (X x))
  have hc : c * (h x + mvfderiv I h x (X x)) = h x := div_mul_cancel₀ _ (hne x)
  -- Read the values of `σ` at `x` through its bilinear form, which is linear in each slot.
  simp only [← SmoothBundleForm.eval₂_apply, ← SmoothForm.bilinFormAt_apply, map_smul,
    LinearMap.smul_apply, SmoothForm.isAlt_bilinFormAt σ x (X x), smul_eq_mul]
  have hB : σ.val x ![X x, v 0] = σ.bilinFormAt x (X x) (v 0) := by
    rw [SmoothForm.bilinFormAt_apply, SmoothBundleForm.eval₂_apply]
  linear_combination σ.bilinFormAt x (X x) (v 0) * hc - h x * hB

/-- **The rescaled field is a Liouville field of the rescaled form**, when `X` is a Liouville
field of a closed form `σ` and `h + dh(X)` vanishes nowhere. -/
theorem isLiouvilleVectorField_rescaledField (hσ : σ.IsClosed)
    (hX : IsLiouvilleVectorField σ.val X) (hne : ∀ x, h x + mvfderiv I h x (X x) ≠ 0) :
    IsLiouvilleVectorField (rescaledForm σ X h).val (rescaledField X h) := by
  rw [coe_rescaledForm]
  refine isLiouvilleVectorField_mextDeriv_of_interior_eq ?_
    ((contMDiff_rescaledField hne).mdifferentiable (by simp)) ?_
  · have hs := (SmoothForm.funSMulₗ h (σ.interiorₗ X)).isSmoothForm
    rw [SmoothForm.coe_funSMulₗ, SmoothTwoForm.coe_interiorₗ] at hs
    exact hs.of_le (by simp)
  · simpa only [← coe_rescaledForm, SmoothForm.coe_funSMulₗ, SmoothTwoForm.coe_interiorₗ] using
      interior_rescaledField_rescaledForm hσ hX hne

/-- **The rescaled form is nondegenerate** when `σ` is closed and nondegenerate, `X` is a
Liouville field of `σ`, and neither `h` nor `h + dh(X)` vanishes. -/
theorem isNondegenerate_rescaledForm (hσ : σ.IsClosed) (hnd : σ.IsNondegenerate)
    (hX : IsLiouvilleVectorField σ.val X) (hh : ∀ x, h x ≠ 0)
    (hne : ∀ x, h x + mvfderiv I h x (X x) ≠ 0) :
    (rescaledForm σ X h).IsNondegenerate := by
  rw [SmoothTwoForm.isNondegenerate_iff_separatingLeft] at hnd ⊢
  intro x v hv
  set B := σ.bilinFormAt x
  set a := mvfderiv I h x v
  set b := mvfderiv I h x (X x)
  -- The rescaled form at `x`, through the bilinear form `B` of `σ`.
  have hR (w : TangentSpace I x) :
      (rescaledForm σ X h).eval₂ x v w = a * B (X x) w - mvfderiv I h x w * B (X x) v +
        h x * B v w := by
    rw [SmoothBundleForm.eval₂_apply, rescaledForm_apply_of_isLiouvilleVectorField hσ hX]
    simp only [B, a, SmoothForm.bilinFormAt_apply, SmoothBundleForm.eval₂_apply]
  have hBX : B (X x) (X x) = 0 := SmoothForm.isAlt_bilinFormAt σ x (X x)
  have hswap : B v (X x) = -B (X x) v := by
    simpa only [B, SmoothForm.bilinFormAt_apply] using SmoothBundleForm.eval₂_swap σ x v (X x)
  -- Evaluating on `X` gives `(h + dh(X)) λ(v) = 0`.
  have hlam : B (X x) v = 0 := by
    have h₁ := hR (X x)
    rw [hv, hBX, hswap] at h₁
    exact (mul_eq_zero.1 (by linear_combination h₁)).resolve_left (hne x)
  -- Then `ι_v σ = -(dh(v) / h) ι_X σ`, so `v + (dh(v) / h) X` is in the kernel of `σ`.
  have hker : v + (a / h x) • X x = 0 := by
    refine hnd x _ fun w ↦ ?_
    have hw := hR w
    rw [hv, hlam] at hw
    rw [← SmoothForm.bilinFormAt_apply, map_add, map_smul, LinearMap.add_apply,
      LinearMap.smul_apply, smul_eq_mul]
    field_simp [hh x]
    linear_combination -hw
  -- Evaluating `dh` on `v = -(dh(v) / h) X` gives `dh(v) (h + dh(X)) = 0`, so `dh(v) = 0`.
  have hv' : v = -(a / h x) • X x := by rw [neg_smul, eq_neg_iff_add_eq_zero, hker]
  have ha : a = 0 := by
    have h₂ : a = -(a / h x) * b := by
      conv_lhs => rw [show a = mvfderiv I h x v from rfl, hv']
      rw [map_smul, smul_eq_mul]
    have h₃ : a * (h x + b) = 0 := by
      field_simp [hh x] at h₂
      linear_combination h₂
    exact (mul_eq_zero.1 h₃).resolve_right (hne x)
  rw [hv', ha, zero_div, neg_zero, zero_smul]

/-- **The rescaled form is symplectic** when `σ` is, `X` is a Liouville field of `σ`, and neither
`h` nor `h + dh(X)` vanishes. -/
theorem isSymplectic_rescaledForm (hσ : σ.IsSymplectic) (hX : IsLiouvilleVectorField σ.val X)
    (hh : ∀ x, h x ≠ 0) (hne : ∀ x, h x + mvfderiv I h x (X x) ≠ 0) :
    (rescaledForm σ X h).IsSymplectic :=
  ⟨isClosed_rescaledForm σ X h,
    isNondegenerate_rescaledForm hσ.isClosed hσ.isNondegenerate hX hh hne⟩

end SymplecticGeometry

end
