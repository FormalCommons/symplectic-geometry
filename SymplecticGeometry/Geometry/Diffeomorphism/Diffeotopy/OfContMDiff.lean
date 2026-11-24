/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Diffeomorphism.Diffeotopy.Real
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.UnitInterval

/-!
# Diffeotopies from families of diffeomorphisms

A family `ψ : unitInterval → M ≃ₘ M` of diffeomorphisms of a boundaryless manifold, modelled on
a complete space, that is jointly smooth in `(t, x)` and starts at the identity is a diffeotopy.
The point is that the inverses `(t, y) ↦ ψ_t⁻¹ y` are jointly smooth too, also at the ends of the
interval, where the inverse function theorem on the manifold with boundary `unitInterval × M`
does not apply.

## Main definitions

* `TauCeti.Diffeotopy.ofContMDiff ψ hψ h₀`: the diffeotopy `(t, x) ↦ ψ_t x` of a jointly smooth
  family `ψ` over `[0, 1]` with `ψ 0 = id`.

## Main results

* `Diffeomorph.contMDiff_symm_eval_unitInterval`: the inverses of a jointly smooth family of
  diffeomorphisms over `[0, 1]` are jointly smooth.
* `TauCeti.Diffeotopy.ofContMDiff_eq_ofReal`: on the restriction of a family over `ℝ`, the
  constructor agrees with `TauCeti.Diffeotopy.ofReal`.

## Implementation notes

The map `(t, x) ↦ (t, ψ_t x)` of `unitInterval × M` is a local diffeomorphism, also at the ends
of the interval (`ContMDiff.isLocalDiffeomorph_prodMk_unitInterval`), and it is bijective, so it
is a diffeomorphism (`IsLocalDiffeomorph.diffeomorphOfBijective`). Its inverse is
`(t, y) ↦ (t, ψ_t⁻¹ y)`. This proof of `Diffeomorph.contMDiff_symm_eval_unitInterval` adapts that
of Tau Ceti's `Diffeomorph.contMDiff_symm_family`, in
`TauCeti/Geometry/Manifold/Diffeomorph/Family.lean`, which needs a boundaryless parameter
manifold, to the parameter space `[0, 1]`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §3.1.
-/

public noncomputable section

open Set Filter Function
open scoped Manifold ContDiff Topology

section SymmEval

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [BoundarylessManifold I M]

/-- On a boundaryless manifold modelled on a complete space, the inverses of a jointly smooth
family of diffeomorphisms over `[0, 1]` are jointly smooth: `(t, y) ↦ ψ_t⁻¹ y` is smooth on
`unitInterval × M`. -/
theorem Diffeomorph.contMDiff_symm_eval_unitInterval {ψ : unitInterval → M ≃ₘ⟮I, I⟯ M}
    (hψ : ContMDiff ((𝓡∂ 1).prod I) I ∞ (fun p : unitInterval × M ↦ ψ p.1 p.2)) :
    ContMDiff ((𝓡∂ 1).prod I) I ∞ (fun p : unitInterval × M ↦ (ψ p.1).symm p.2) := by
  have hF := hψ.isLocalDiffeomorph_prodMk_unitInterval fun t ↦ (ψ t).isLocalDiffeomorph
  have hbij : Bijective fun p : unitInterval × M ↦ (p.1, ψ p.1 p.2) :=
    bijective_iff_has_inverse.2 ⟨fun p ↦ (p.1, (ψ p.1).symm p.2), fun p ↦ by simp,
      fun p ↦ by simp⟩
  set D := hF.diffeomorphOfBijective hbij
  have hD (p : unitInterval × M) : D.symm p = (p.1, (ψ p.1).symm p.2) := by
    have h : D (p.1, (ψ p.1).symm p.2) = p := by simp [D]
    calc D.symm p = D.symm (D (p.1, (ψ p.1).symm p.2)) := by rw [h]
      _ = (p.1, (ψ p.1).symm p.2) := D.symm_apply_apply _
  have h : (fun p : unitInterval × M ↦ (ψ p.1).symm p.2) = fun p ↦ (D.symm p).2 := by
    ext p
    rw [hD]
  rw [h]
  exact contMDiff_snd.comp D.symm.contMDiff

end SymmEval

namespace TauCeti.Diffeotopy

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [BoundarylessManifold I M]
  (ψ : unitInterval → M ≃ₘ⟮I, I⟯ M)
  (hψ : ContMDiff ((𝓡∂ 1).prod I) I ∞ (fun p : unitInterval × M ↦ ψ p.1 p.2))
  (h₀ : ∀ x, ψ 0 x = x)

/-- The diffeotopy `(t, x) ↦ ψ_t x` of a jointly smooth family `ψ` of diffeomorphisms over
`[0, 1]` with `ψ 0 = id`. Its inverse is jointly smooth by
`Diffeomorph.contMDiff_symm_eval_unitInterval`. -/
def ofContMDiff : Diffeotopy I ∞ M where
  toDiffeomorph :=
    { toFun := fun p ↦ (p.1, ψ p.1 p.2)
      invFun := fun p ↦ (p.1, (ψ p.1).symm p.2)
      left_inv := fun p ↦ by simp
      right_inv := fun p ↦ by simp
      contMDiff_toFun := contMDiff_fst.prodMk hψ
      contMDiff_invFun := contMDiff_fst.prodMk (Diffeomorph.contMDiff_symm_eval_unitInterval hψ) }
  fst_apply _ := rfl
  snd_apply_zero' := h₀

/-- The diffeotopy `ofContMDiff ψ hψ h₀` sends `(t, x)` to `ψ_t x`. -/
@[simp]
theorem ofContMDiff_apply (p : unitInterval × M) : ofContMDiff ψ hψ h₀ p = ψ p.1 p.2 :=
  (rfl)

/-- The time-`t` slice of `ofContMDiff ψ hψ h₀` is `ψ_t`. -/
@[simp]
theorem timeSlice_ofContMDiff (t : unitInterval) : (ofContMDiff ψ hψ h₀).timeSlice t = ψ t :=
  Diffeomorph.ext fun x ↦ by rw [timeSlice_apply, ofContMDiff_apply]

/-- The inverse of the level-preserving diffeomorphism of `ofContMDiff ψ hψ h₀` sends `(t, y)` to
`(t, ψ_t⁻¹ y)`. -/
@[simp]
theorem toDiffeomorph_symm_ofContMDiff_apply (p : unitInterval × M) :
    (ofContMDiff ψ hψ h₀).toDiffeomorph.symm p = (p.1, (ψ p.1).symm p.2) :=
  (rfl)

/-- The inverse of `ofContMDiff ψ hψ h₀` sends `(t, y)` to `ψ_t⁻¹ y`. -/
theorem symm_ofContMDiff_apply (p : unitInterval × M) :
    (ofContMDiff ψ hψ h₀).symm p = (ψ p.1).symm p.2 := by
  rw [symm_apply, toDiffeomorph_symm_ofContMDiff_apply]

/-- The final map of `ofContMDiff ψ hψ h₀` is `ψ_1`. -/
@[simp]
theorem final_ofContMDiff : (ofContMDiff ψ hψ h₀).final = ψ 1 := by
  rw [final_def, timeSlice_ofContMDiff]

/-- On the restriction to `[0, 1]` of a jointly smooth family `φ` over `ℝ`, the constructor
`ofContMDiff` agrees with `ofReal`. -/
theorem ofContMDiff_eq_ofReal (φ : ℝ → M ≃ₘ⟮I, I⟯ M)
    (hφ : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M ↦ φ p.1 p.2)) (hφ₀ : ∀ x, φ 0 x = x)
    (hφ' : ContMDiff ((𝓡∂ 1).prod I) I ∞ (fun p : unitInterval × M ↦ φ p.1 p.2))
    (hφ₀' : ∀ x, φ ((0 : unitInterval) : ℝ) x = x) :
    ofContMDiff (fun t : unitInterval ↦ φ t) hφ' hφ₀' = ofReal φ hφ hφ₀ :=
  ext fun p ↦ by rw [ofContMDiff_apply, ofReal_apply]

end TauCeti.Diffeotopy

end
