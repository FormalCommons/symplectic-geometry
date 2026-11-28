/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Liouville.Rescale
public import SymplecticGeometry.Geometry.Symplectic.Weinstein.Homotopy
import SymplecticGeometry.Geometry.Manifold.Flow.Complete
import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Differential
import TauCeti.Geometry.Manifold.VectorBundle.Scalar

/-!
# Rescaling the Liouville form of a Weinstein structure

Let `(ω, X, f)` be a Weinstein structure and `h` a smooth positive function with `dh(X) ≥ 0`.
Replacing the primitive `λ = ι_X ω` by `h λ` gives the form `d(h λ)`
(`SymplecticGeometry.rescaledForm`) with the Liouville field `(h / (h + dh(X))) X`
(`SymplecticGeometry.rescaledField`). This file shows that, with the same function `f`, they form
a Weinstein structure again, joined to `(ω, X, f)` by a Weinstein homotopy that keeps `f` fixed.

## Main declarations

* `SymplecticGeometry.IsWeinsteinStructure.rescale`: `(d(h λ), (h / (h + dh(X))) X, f)` is a
  Weinstein structure.
* `SymplecticGeometry.IsWeinsteinStructure.isWeinsteinHomotopy_rescale`: rescaling by
  `1 - t + t h`, `t ∈ [0, 1]`, is a Weinstein homotopy with the function `f` at every time. Its
  forms are `(1 - t) ω + t d(h λ)`; it starts at `(ω, X, f)` and ends at the rescaled structure.
* `SymplecticGeometry.IsWeinsteinStructure.areWeinsteinHomotopic_rescale`: the two structures are
  Weinstein homotopic.

## Implementation notes

The rescaled field is `X` times the smooth function `h / (h + dh(X))`, which takes values in
`(0, 1]` when `h > 0` and `dh(X) ≥ 0`. So it is complete by
`TauCeti.IsCompleteVectorField.smul_of_pos_of_le`, and gradient-like for `f` by
`TauCeti.IsGradientLike.smul`. The rescaled form is symplectic and the rescaled field is
Liouville for it by `SymplecticGeometry.isSymplectic_rescaledForm` and
`SymplecticGeometry.isLiouvilleVectorField_rescaledField`. The field and the function `h` are
bundled smooth objects, as `SymplecticGeometry.rescaledForm` asks; a Weinstein structure whose
field is smooth gives such a bundled field.

In the homotopy, the function at time `t` is `(1 - t) • 1 + t • h`, whose derivative is
`t • dh`; it is positive with nonnegative derivative along `X`, so each member is a rescaled
structure. The forms are affine in `t` by
`SymplecticGeometry.rescaledForm_one_sub_smul_one_add_smul`, hence a smooth family. The function
is `f` at every time, so every regular barrier of the constant family `fun _ ↦ f`, such as the one
that `SymplecticGeometry.IsWeinsteinHomotopy.refl` provides, is a regular barrier of the
homotopy, and homotopies of this kind glue by `SymplecticGeometry.IsWeinsteinHomotopy.trans` at
any such barrier.

## References

* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  Lemma 12.1 (i), Remark 12.2 (a) and Corollary 12.3 (i): rescaling the Liouville form of a
  Weinstein structure by a positive function that does not decrease along the Liouville field.
-/

public section

noncomputable section

open Bundle TauCeti
open scoped Manifold

namespace SymplecticGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) (⊤ : ℕ∞) M]


namespace IsWeinsteinStructure

variable {ω : SmoothTwoForm 𝓘(ℝ, E) M} {X : Cₛ^(⊤ : ℕ∞)⟮𝓘(ℝ, E); E, TangentSpace 𝓘(ℝ, E) (M := M)⟯}
  {f : M → ℝ} {h : C^(⊤ : ℕ∞)⟮𝓘(ℝ, E), M; ℝ⟯}

/-- **Rescaling the Liouville form of a Weinstein structure.** If `(ω, X, f)` is a Weinstein
structure and `h` is a smooth positive function with `dh(X) ≥ 0`, then the form `d(h ι_X ω)` and
the field `(h / (h + dh(X))) X` form a Weinstein structure with the same function `f`. -/
theorem rescale [T2Space M] (hW : IsWeinsteinStructure ω X f) (hpos : ∀ x, 0 < h x)
    (hX : ∀ x, 0 ≤ mvfderiv 𝓘(ℝ, E) h x (X x)) :
    IsWeinsteinStructure (rescaledForm ω X h) (rescaledField X h) f := by
  have hden (x : M) : 0 < h x + mvfderiv 𝓘(ℝ, E) h x (X x) := by
    linarith [hpos x, hX x]
  have hne (x : M) : h x + mvfderiv 𝓘(ℝ, E) h x (X x) ≠ 0 := (hden x).ne'
  -- The factor `a = h / (h + dh(X))` is smooth, with values in `(0, 1]`.
  have ha : Continuous fun x ↦ h x / (h x + mvfderiv 𝓘(ℝ, E) h x (X x)) :=
    (contMDiff_div_self_add_mvfderiv hne).continuous
  have ha₀ (x : M) : 0 < h x / (h x + mvfderiv 𝓘(ℝ, E) h x (X x)) := div_pos (hpos x) (hden x)
  have ha₁ (x : M) : h x / (h x + mvfderiv 𝓘(ℝ, E) h x (X x)) ≤ 1 :=
    (div_le_one (hden x)).2 (by linarith [hX x])
  have hY : rescaledField X h = fun x ↦ (h x / (h x + mvfderiv 𝓘(ℝ, E) h x (X x))) • X x :=
    rescaledField_def X h
  exact
    { isSymplectic := isSymplectic_rescaledForm hW.isSymplectic hW.isLiouvilleVectorField
        (fun x ↦ (hpos x).ne') hne
      contMDiff_field := contMDiff_rescaledField hne
      isLiouvilleVectorField := isLiouvilleVectorField_rescaledField hW.isSymplectic.isClosed
        hW.isLiouvilleVectorField hne
      isCompleteVectorField := hY ▸ hW.isCompleteVectorField.smul_of_pos_of_le
        (hW.contMDiff_field.of_le (by simp)) ha ha₀ ha₁
      isProperMap := hW.isProperMap
      bddBelow := hW.bddBelow
      isGeneralizedMorse := hW.isGeneralizedMorse
      isGradientLike := hY ▸ hW.isGradientLike.smul ha ha₀ }

/-- **Rescaling the Liouville form is a Weinstein homotopy.** If `(ω, X, f)` is a Weinstein
structure and `h` is a smooth positive function with `dh(X) ≥ 0`, then rescaling by
`(1 - t) • 1 + t • h` gives a Weinstein homotopy, with forms `(1 - t) • ω + t • d(h ι_X ω)` and
the function `f` at every time `t ∈ [0, 1]`. It starts at `(ω, X, f)`
(`SymplecticGeometry.rescaledField_one`) and ends at the structure of
`SymplecticGeometry.IsWeinsteinStructure.rescale`. -/
theorem isWeinsteinHomotopy_rescale [T2Space M] (hW : IsWeinsteinStructure ω X f)
    (hpos : ∀ x, 0 < h x) (hX : ∀ x, 0 ≤ mvfderiv 𝓘(ℝ, E) h x (X x)) :
    IsWeinsteinHomotopy (fun t ↦ (1 - (t : ℝ)) • ω + (t : ℝ) • rescaledForm ω X h)
      (fun t ↦ rescaledField X ((1 - (t : ℝ)) • 1 + (t : ℝ) • h : C^(⊤ : ℕ∞)⟮𝓘(ℝ, E), M; ℝ⟯))
      (fun _ ↦ f) := by
  -- The interpolating function at time `t`, its values and its derivative along `X`.
  let g (t : ℝ) : C^(⊤ : ℕ∞)⟮𝓘(ℝ, E), M; ℝ⟯ := (1 - t) • 1 + t • h
  have hgx (t : ℝ) (x : M) : g t x = 1 - t + t * h x := by simp [g]
  have hdg (t : ℝ) (x : M) :
      mvfderiv 𝓘(ℝ, E) (g t) x (X x) = t * mvfderiv 𝓘(ℝ, E) h x (X x) := by
    -- The derivative is linear on smooth functions, and vanishes on constants.
    rw [← ContMDiffMap.mvfderivCLM_apply (n := (⊤ : ℕ∞)) (by simp), map_add, map_smul, map_smul,
      ContMDiffMap.mvfderivCLM_apply, ContMDiffMap.mvfderivCLM_apply, ContMDiffMap.coe_one,
      Pi.one_def, mvfderiv_const, smul_zero, zero_add,
      FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  have hgpos (t : unitInterval) (x : M) : 0 < g t x := by
    rw [hgx]
    rcases eq_or_lt_of_le (unitInterval.le_one t) with ht | ht
    · rw [ht]; linarith [hpos x]
    · nlinarith [hpos x, (unitInterval.nonneg t)]
  have hdgX (t : unitInterval) (x : M) : 0 ≤ mvfderiv 𝓘(ℝ, E) (g t) x (X x) := by
    rw [hdg]; exact mul_nonneg (unitInterval.nonneg t) (hX x)
  have hT : ContMDiff (𝓡∂ 1) 𝓘(ℝ) (⊤ : ℕ∞) fun t : unitInterval ↦ (t : ℝ) :=
    contMDiff_subtypeVal_Icc
  -- The field at `(t, x)` is `X x` times a smooth function of `(t, x)`.
  have hmul : ContMDiff ((𝓡∂ 1).prod 𝓘(ℝ, E)) 𝓘(ℝ) (⊤ : ℕ∞) fun p : unitInterval × M ↦
      (1 - (p.1 : ℝ) + p.1 * h p.2) /
        (1 - (p.1 : ℝ) + p.1 * h p.2 + p.1 * mvfderiv 𝓘(ℝ, E) h p.2 (X p.2)) := by
    have h₁ : ContMDiff ((𝓡∂ 1).prod 𝓘(ℝ, E)) 𝓘(ℝ) (⊤ : ℕ∞) fun p : unitInterval × M ↦
        (p.1 : ℝ) := hT.comp contMDiff_fst
    have h₂ : ContMDiff ((𝓡∂ 1).prod 𝓘(ℝ, E)) 𝓘(ℝ) (⊤ : ℕ∞) fun p : unitInterval × M ↦
        h p.2 := h.contMDiff.comp contMDiff_snd
    have h₃ : ContMDiff ((𝓡∂ 1).prod 𝓘(ℝ, E)) 𝓘(ℝ) (⊤ : ℕ∞) fun p : unitInterval × M ↦
        mvfderiv 𝓘(ℝ, E) h p.2 (X p.2) :=
      ((h.contMDiff.contMDiff_mvfderiv_apply (by simp)).comp X.contMDiff).comp contMDiff_snd
    refine (contMDiff_const.sub h₁ |>.add (h₁.mul h₂)).div₀
      ((contMDiff_const.sub h₁ |>.add (h₁.mul h₂)).add (h₁.mul h₃)) fun p ↦ ?_
    have h₄ := hgpos p.1 p.2
    have h₅ := hdgX p.1 p.2
    rw [hgx] at h₄
    rw [hdg] at h₅
    exact (add_pos_of_pos_of_nonneg h₄ h₅).ne'
  refine ⟨((isSmoothFamily_const ω).fun_smul (contMDiff_const.sub hT)).add
      ((isSmoothFamily_const _).fun_smul hT), ?_,
    hW.isGeneralizedMorse.contMDiff.comp contMDiff_snd, fun t ↦ ?_,
    (IsWeinsteinHomotopy.refl hW).exists_isRegularBarrier⟩
  · refine (hmul.smul_totalSpace (hW.contMDiff_field.comp contMDiff_snd)).congr fun p ↦ ?_
    -- Both sides are `X p.2` times the factor, written through `g` on the left.
    rw [rescaledField_apply, ← hgx, ← hdg]
    rfl
  · rw [← rescaledForm_one_sub_smul_one_add_smul hW.isSymplectic.isClosed
      hW.isLiouvilleVectorField]
    exact hW.rescale (hgpos t) (hdgX t)

/-- A Weinstein structure `(ω, X, f)` is Weinstein homotopic to its rescaling
`(d(h ι_X ω), (h / (h + dh(X))) X, f)` by a smooth positive function `h` with `dh(X) ≥ 0`. -/
theorem areWeinsteinHomotopic_rescale [T2Space M] (hW : IsWeinsteinStructure ω X f)
    (hpos : ∀ x, 0 < h x) (hX : ∀ x, 0 ≤ mvfderiv 𝓘(ℝ, E) h x (X x)) :
    AreWeinsteinHomotopic ω X f (rescaledForm ω X h) (rescaledField X h) f := by
  have := (hW.isWeinsteinHomotopy_rescale hpos hX).areWeinsteinHomotopic
  simpa using this

end IsWeinsteinStructure

end SymplecticGeometry

end
