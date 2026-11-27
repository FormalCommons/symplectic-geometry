/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.DifferentialForm.Basic
public import Mathlib.Analysis.Normed.Module.Alternating.Uncurry.Fin
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.SmoothFamily.Basic
import TauCeti.Geometry.Manifold.ContMDiff.MFDeriv
import TauCeti.Geometry.Manifold.ContMDiff.Prod
import TauCeti.Geometry.Manifold.DifferentialForm.Naturality

/-!
# The formal primitive of a two-form

Let `τ` be a two-form and `β` a one-form on a real normed space `E`, both read as maps into
spaces of continuous alternating maps. To find a one-form whose exterior derivative is close to
`τ`, the h-principle first solves the equation `dβ' = τ` formally: in place of the derivative of
an unknown `β'` it asks for a field `G` of linear maps `E →L[ℝ] E [⋀^Fin 1]→L[ℝ] F` whose
alternation `alternatizeUncurryFin (G x)` is `τ x`, the alternation of `fderiv ℝ β' x` being
`extDeriv β' x`. With `β` as the zeroth-order part, the formal datum is
`SymplecticGeometry.formalPrimitive τ β`,

  `G x = fderiv ℝ β x + 2⁻¹ • curryLeft (τ x - dβ x)`,

which corrects the derivative of `β` by the right inverse `a ↦ 2⁻¹ • curryLeft a` of the
alternation of bilinear maps (Mathlib's `ContinuousAlternatingMap.alternatizeUncurryFin_curryLeft`
says that the alternation of `curryLeft a` is `2 • a`). Then:

* the alternation of `G x` is `τ x`, and `G x = fderiv ℝ β x` wherever `dβ x = τ x`, so the datum
  is holonomic, the derivative of its zeroth-order part, on every set on which `β` is a primitive
  of `τ`;
* in particular, for forms `σ`, `α`, `β` on a manifold `M` read along a smooth map `φ : E → M`,
  the formal primitive of the reading of `σ - α` with zeroth-order part the reading of `β` is
  holonomic at every `x` with `σ = α + dβ` at `φ x`, since pullback commutes with `d` (Tau Ceti's
  `TauCeti.SmoothForm.mextDerivₗ_mpullback`);
* if the derivative of a one-form `f` is within `ε` of `G x` at `x`, then `df` is within `2 * ε`
  of `τ` at `x`, by Mathlib's bound `ContinuousAlternatingMap.norm_alternatizeUncurryFin_le` on
  the alternation;
* for smooth families `τ` and `β` of forms over a parameter manifold `N`, the datum
  `(t, x) ↦ formalPrimitive (τ t) (β t) x` is smooth on `N × E`.

Holonomic approximation then turns this formal solution into a genuine one near a core, as in the
proof of the handle-core lemma and of Gromov's theorem on symplectic forms on open manifolds
(Eliashberg–Mishachev, §10.2).

## Main definitions

* `SymplecticGeometry.formalPrimitive τ β`: the formal primitive of `τ` with zeroth-order part
  `β`.

## Main results

* `SymplecticGeometry.alternatizeUncurryFin_formalPrimitive`: its alternation is `τ`.
* `SymplecticGeometry.formalPrimitive_eq_fderiv`: it is the derivative of `β` where `dβ = τ`.
* `SymplecticGeometry.formalPrimitive_mpullback_eq_fderiv`: the same for forms on a manifold read
  along a smooth map.
* `SymplecticGeometry.norm_extDeriv_sub_le_of_norm_fderiv_sub_formalPrimitive_le`: a derivative
  within `ε` of it has exterior derivative within `2 * ε` of `τ`.
* `SymplecticGeometry.contMDiff_formalPrimitive`: it is smooth in the parameter and the point
  together, for smooth families of forms.
* `SymplecticGeometry.contDiff_formalPrimitive`: the same as a `ContDiff` statement, when the
  parameter space is a normed space.

## References

* [Y. Eliashberg and N. Mishachev, *Introduction to the h-principle*][EliashbergMishachev2002],
  §10.2.
-/

public section

open ContinuousAlternatingMap TauCeti
open scoped Manifold ContDiff

namespace SymplecticGeometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- **The formal primitive of a two-form.** For a two-form `τ` and a one-form `β` on `E`, the
field of linear maps `x ↦ fderiv ℝ β x + 2⁻¹ • curryLeft (τ x - dβ x)`: the derivative of `β`,
corrected so that its alternation is `τ x`. It is a formal solution of `dβ' = τ` with
zeroth-order part `β`. -/
noncomputable def formalPrimitive (τ : E → E [⋀^Fin 2]→L[ℝ] F) (β : E → E [⋀^Fin 1]→L[ℝ] F)
    (x : E) : E →L[ℝ] E [⋀^Fin 1]→L[ℝ] F :=
  fderiv ℝ β x + (2 : ℝ)⁻¹ • curryLeft (τ x - extDeriv β x)

theorem formalPrimitive_def (τ : E → E [⋀^Fin 2]→L[ℝ] F) (β : E → E [⋀^Fin 1]→L[ℝ] F) (x : E) :
    formalPrimitive τ β x = fderiv ℝ β x + (2 : ℝ)⁻¹ • curryLeft (τ x - extDeriv β x) :=
  (rfl)

variable {τ : E → E [⋀^Fin 2]→L[ℝ] F} {β : E → E [⋀^Fin 1]→L[ℝ] F}

/-- The alternation of the formal primitive of `τ` is `τ`. -/
@[simp]
theorem alternatizeUncurryFin_formalPrimitive (x : E) :
    alternatizeUncurryFin (formalPrimitive τ β x) = τ x := by
  rw [formalPrimitive_def, alternatizeUncurryFin_add, alternatizeUncurryFin_smul,
    alternatizeUncurryFin_curryLeft, ← extDeriv, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  norm_num

/-- **The formal primitive is holonomic where `β` is a primitive.** At a point where
`dβ x = τ x`, the formal primitive of `τ` with zeroth-order part `β` is the derivative of `β`. -/
theorem formalPrimitive_eq_fderiv {x : E} (hx : extDeriv β x = τ x) :
    formalPrimitive τ β x = fderiv ℝ β x := by
  rw [formalPrimitive_def, hx, sub_self, curryLeft_zero]
  exact (congrArg _ (smul_zero (2 : ℝ)⁻¹)).trans (add_zero _)

/-- **The formal primitive of a reading is holonomic where the reading is a primitive.** Let
`φ : E → M` be smooth, and `σ`, `α` two-forms and `β` a one-form on `M` with `σ = α + dβ` at
`φ x`. Then, at `x`, the formal primitive of the pullback of `σ - α` along `φ`, with zeroth-order
part the pullback of `β`, is the derivative of the pullback of `β`. -/
theorem formalPrimitive_mpullback_eq_fderiv {EM H M : Type*} [NormedAddCommGroup EM]
    [NormedSpace ℝ EM] [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ EM H} [IsManifold I ∞ M]
    {φ : E → M} (hφ : ContMDiff 𝓘(ℝ, E) I ∞ φ) {σ α : SmoothForm I M F 2}
    {β : SmoothForm I M F 1} {x : E} (hx : σ.val (φ x) = (α + mextDerivₗ I 1 β).val (φ x)) :
    formalPrimitive (SmoothForm.mpullback φ hφ (σ - α)).val (SmoothForm.mpullback φ hφ β).val x =
      fderiv ℝ (SmoothForm.mpullback φ hφ β).val x := by
  refine formalPrimitive_eq_fderiv ?_
  rw [← mextDeriv_eq_extDeriv, ← mextDerivₗ_apply, SmoothForm.mextDerivₗ_mpullback,
    SmoothForm.coe_mpullback, SmoothForm.coe_mpullback]
  exact mpullback_apply_congr (by simp [hx])

/-- **Approximating the formal primitive.** If the derivative of a one-form `f` at `x` is within
`ε` of the formal primitive of `τ`, then the exterior derivative of `f` at `x` is within `2 * ε`
of `τ x`. -/
theorem norm_extDeriv_sub_le_of_norm_fderiv_sub_formalPrimitive_le
    {f : E → E [⋀^Fin 1]→L[ℝ] F} {x : E} {ε : ℝ}
    (h : ‖fderiv ℝ f x - formalPrimitive τ β x‖ ≤ ε) :
    ‖extDeriv f x - τ x‖ ≤ 2 * ε := by
  have := norm_alternatizeUncurryFin_le (fderiv ℝ f x - formalPrimitive τ β x)
  rw [← alternatizeUncurryFinCLM_apply, map_sub, alternatizeUncurryFinCLM_apply,
    alternatizeUncurryFinCLM_apply, alternatizeUncurryFin_formalPrimitive, ← extDeriv] at this
  norm_num at this
  linarith

variable {EN HN N : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
  [TopologicalSpace N] [ChartedSpace HN N] {J : ModelWithCorners ℝ EN HN} [IsManifold J 1 N]

/-- **Smoothness of the formal primitive in the parameter.** For smooth families `τ` of two-forms
and `β` of one-forms on `E` over a manifold `N`, the formal primitive
`formalPrimitive (τ t) (β t) x` is smooth in `(t, x) ∈ N × E`. -/
theorem contMDiff_formalPrimitive {τ : N → SmoothForm 𝓘(ℝ, E) E F 2}
    {β : N → SmoothForm 𝓘(ℝ, E) E F 1} (hτ : IsSmoothFamily J τ) (hβ : IsSmoothFamily J β) :
    ContMDiff (J.prod 𝓘(ℝ, E)) 𝓘(ℝ, E →L[ℝ] E [⋀^Fin 1]→L[ℝ] F) ∞
      fun p : N × E ↦ formalPrimitive (τ p.1).val (β p.1).val p.2 := by
  -- Read the values of the forms as maps into fixed spaces of alternating maps.
  set b : N → E → E [⋀^Fin 1]→L[ℝ] F := fun t ↦ (β t).val
  set c : N → E → E [⋀^Fin 2]→L[ℝ] F := fun t ↦ (τ t).val
  have hb : ContMDiff (J.prod 𝓘(ℝ, E)) 𝓘(ℝ, E [⋀^Fin 1]→L[ℝ] F) ∞
      fun p : N × E ↦ b p.1 p.2 :=
    hβ.contMDiff_val
  have hc : ContMDiff (J.prod 𝓘(ℝ, E)) 𝓘(ℝ, E [⋀^Fin 2]→L[ℝ] F) ∞
      fun p : N × E ↦ c p.1 p.2 :=
    hτ.contMDiff_val
  -- The derivative in the point is smooth in the parameter and the point together.
  have hD : ContMDiff (J.prod 𝓘(ℝ, E)) 𝓘(ℝ, E →L[ℝ] E [⋀^Fin 1]→L[ℝ] F) ∞
      fun p : N × E ↦ fderiv ℝ (b p.1) p.2 :=
    fun p ↦ (hb p).fderiv_right le_rfl
  -- The right inverse `a ↦ 2⁻¹ • curryLeft a` of the alternation is continuous linear.
  have hJ : ContMDiff 𝓘(ℝ, E [⋀^Fin 2]→L[ℝ] F) 𝓘(ℝ, E →L[ℝ] E [⋀^Fin 1]→L[ℝ] F) ∞
      fun a ↦ (2 : ℝ)⁻¹ • curryLeft (𝕜 := ℝ) (E := E) (F := F) (n := 1) a :=
    ContinuousLinearMap.contMDiff (𝕜 := ℝ) (E := E [⋀^Fin 2]→L[ℝ] F)
      (F := E →L[ℝ] E [⋀^Fin 1]→L[ℝ] F) (n := ∞)
      ((2 : ℝ)⁻¹ • (curryLeftLI (n := 1)).toContinuousLinearMap)
  exact hD.add (hJ.comp (hc.sub ((alternatizeUncurryFinCLM ℝ E F).contMDiff.comp hD)))

/-- **Smoothness of the formal primitive in a parameter from a normed space.** For smooth families
`τ` of two-forms and `β` of one-forms on `E` over a normed space `L`, the formal primitive
`formalPrimitive (τ t) (β t) x` is a `C^∞` function of `(t, x) ∈ L × E`. -/
theorem contDiff_formalPrimitive {L : Type*} [NormedAddCommGroup L] [NormedSpace ℝ L]
    {τ : L → SmoothForm 𝓘(ℝ, E) E F 2} {β : L → SmoothForm 𝓘(ℝ, E) E F 1}
    (hτ : IsSmoothFamily 𝓘(ℝ, L) τ) (hβ : IsSmoothFamily 𝓘(ℝ, L) β) :
    ContDiff ℝ ∞ fun p : L × E ↦ formalPrimitive (τ p.1).val (β p.1).val p.2 :=
  contMDiff_iff_contDiff.mp (contMDiff_prod_modelWithCornersSelf_iff.mp
    (contMDiff_formalPrimitive hτ hβ))

end SymplecticGeometry

end
