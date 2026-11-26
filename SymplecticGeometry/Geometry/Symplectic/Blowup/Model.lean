/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Complex.Blowup.Model
public import SymplecticGeometry.Geometry.Manifold.Projectivization.FubiniStudy.Normalization
public import SymplecticGeometry.LinearAlgebra.Symplectic.Standard.Basic
public import SymplecticGeometry.Geometry.Manifold.ContMDiff.RestrictScalars
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Pullback.Smooth

/-!
# The forms `ω̃_λ` on the model blowup

For `n : ℕ` and `E := Fin (n + 1) → ℂ`, let `π : BlowupModel n → E` be the blowdown and
`pr : BlowupModel n → ℙ ℂ E` the projection of the model blowup of `E` at `0`
(`Geometry/Manifold/Complex/Blowup/Model.lean`), seen as real manifolds with the real structure
of the complex manifold (the scoped instance `TauCeti.ComplexManifold.isManifold_real`). Following
McDuff–Salamon, §7.1, this file defines on the model the closed two-forms
`ω̃_λ = π^* ω₀ + λ² pr^* ω_FS`, computes their restriction to the exceptional divisor `Z`, and
sets up the neighbourhoods `L(ε)` of `Z`.

## Main definitions and results

* `SymplecticGeometry.BlowupModel.ω₀E n`: the standard symplectic form `ω₀` of `E`, as a constant
  smooth form, and `SymplecticGeometry.BlowupModel.constSmooth_stdComplexPiSymplecticForm_eq`: for
  any finite `ι`, the constant form `stdComplexPiSymplecticForm ι` is the pull-back of the
  constant form `stdForm ι` along `complexToRealEuclidean ι`, by
  `TauCeti.SymplecticForm.IsSymplectomorphism.mpullback_constSmooth`.
* `SymplecticGeometry.BlowupModel.closedNbhd n ε` and `SymplecticGeometry.BlowupModel.openNbhd n ε`:
  the points whose blowdown has Euclidean norm `≤ ε`, resp. `< ε`; the first is compact
  (`isCompact_closedNbhd`, since `ℙ ℂ E` is compact and the model is closed in `ℙ ℂ E × E`), the
  second open, and both contain the exceptional divisor for `0 < ε`.
* `SymplecticGeometry.BlowupModel.blowupForm n l`: the form `π^* ω₀ + l² pr^* ω_FS`, and
  `SymplecticGeometry.BlowupModel.isClosed_blowupForm`: it is closed.
* `SymplecticGeometry.BlowupModel.mpullback_zeroSection_blowupForm`: on the exceptional divisor
  it restricts to `l² ω_FS`, since `π` is constant there; hence
  `SymplecticGeometry.BlowupModel.integralTopForm_blowupForm_line`: every projective line of the
  divisor has area `π l²`, by `integralTopForm_mpullback_map_fubiniStudyForm`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §7.1.
-/

public section

open Set Projectivization TauCeti
open scoped Manifold ContDiff LinearAlgebra.Projectivization TauCeti.ComplexManifold

namespace SymplecticGeometry

namespace BlowupModel

variable (n : ℕ)

/-! ### The standard form of `E` -/

/-- The standard symplectic form `ω₀ = stdComplexPiSymplecticForm` of `E = ℂⁿ⁺¹`, as a constant
smooth two-form on `E`. -/
noncomputable def ω₀E : SmoothTwoForm 𝓘(ℝ, Fin (n + 1) → ℂ) (Fin (n + 1) → ℂ) :=
  (stdComplexPiSymplecticForm (Fin (n + 1))).constSmooth

theorem ω₀E_def : ω₀E n = (stdComplexPiSymplecticForm (Fin (n + 1))).constSmooth :=
  (rfl)

/-- For a finite type `ι`, the constant form `stdComplexPiSymplecticForm ι` on `ι → ℂ` is the
pull-back of the constant form `stdForm ι` of `StdSpace ι` along the real-linear identification
`complexToRealEuclidean ι`. At `ι = Fin (n + 1)` its left side is `ω₀E n` (`ω₀E_def`). -/
theorem constSmooth_stdComplexPiSymplecticForm_eq (ι : Type*) [Fintype ι] :
    (stdComplexPiSymplecticForm ι).constSmooth = SmoothForm.mpullback (complexToRealEuclidean ι)
      (complexToRealEuclidean ι).contDiff.contMDiff (stdForm ι).constSmooth :=
  (SymplecticForm.IsSymplectomorphism.mpullback_constSmooth
    (SymplecticForm.isSymplectomorphism_iff.2
      stdForm_complexToRealEuclidean)).symm

/-! ### The neighbourhoods `L(ε)` of the exceptional divisor -/

/-- `L(ε)`: the points of the model blowup whose blowdown has Euclidean norm at most `ε`. -/
def closedNbhd (ε : ℝ) : Set (BlowupModel n) :=
  blowdown ⁻¹' {z | ‖complexToRealEuclidean (Fin (n + 1)) z‖ ≤ ε}

/-- The points of the model blowup whose blowdown has Euclidean norm less than `ε`. -/
def openNbhd (ε : ℝ) : Set (BlowupModel n) :=
  blowdown ⁻¹' {z | ‖complexToRealEuclidean (Fin (n + 1)) z‖ < ε}

variable {n}

@[simp]
theorem mem_closedNbhd_iff {ε : ℝ} {p : BlowupModel n} :
    p ∈ closedNbhd n ε ↔ ‖complexToRealEuclidean (Fin (n + 1)) p.blowdown‖ ≤ ε :=
  Iff.rfl

@[simp]
theorem mem_openNbhd_iff {ε : ℝ} {p : BlowupModel n} :
    p ∈ openNbhd n ε ↔ ‖complexToRealEuclidean (Fin (n + 1)) p.blowdown‖ < ε :=
  Iff.rfl

theorem openNbhd_subset_closedNbhd (ε : ℝ) : openNbhd n ε ⊆ closedNbhd n ε :=
  fun _ hp ↦ (mem_closedNbhd_iff).2 (mem_openNbhd_iff.1 hp).le

theorem isOpen_openNbhd (ε : ℝ) : IsOpen (openNbhd n ε) :=
  isOpen_lt
    ((complexToRealEuclidean (Fin (n + 1))).continuous.comp continuous_blowdown).norm
    continuous_const

theorem isClosed_closedNbhd (ε : ℝ) : IsClosed (closedNbhd n ε) :=
  isClosed_le
    ((complexToRealEuclidean (Fin (n + 1))).continuous.comp continuous_blowdown).norm
    continuous_const

/-- `L(ε)` is compact: it is the part of the closed incidence set lying over a compact subset of
`ℙ ℂ E × E`. -/
theorem isCompact_closedNbhd (ε : ℝ) : IsCompact (closedNbhd n ε) := by
  have hK : IsCompact {z : Fin (n + 1) → ℂ | ‖complexToRealEuclidean (Fin (n + 1)) z‖ ≤ ε} := by
    have := (complexToRealEuclidean (Fin (n + 1))).toHomeomorph.isCompact_preimage.2
      (isCompact_closedBall (0 : StdSpace (Fin (n + 1))) ε)
    simpa [Metric.closedBall, Set.preimage] using this
  have h : closedNbhd n ε = Subtype.val ⁻¹' (univ ×ˢ
      {z : Fin (n + 1) → ℂ | ‖complexToRealEuclidean (Fin (n + 1)) z‖ ≤ ε}) := by
    ext p
    simp [blowdown_def]
  rw [h]
  exact (isClosed_blowupModel n).isClosedEmbedding_subtypeVal.isCompact_preimage
    (isCompact_univ.prod hK)

/-- For `0 < ε`, the exceptional divisor lies in the open neighbourhood of radius `ε`. -/
theorem exceptionalDivisor_subset_openNbhd {ε : ℝ} (hε : 0 < ε) :
    exceptionalDivisor n ⊆ openNbhd n ε := fun p hp ↦ by
  rw [mem_exceptionalDivisor_iff] at hp
  simpa [hp] using hε

/-- For `0 < ε`, the exceptional divisor lies in `L(ε)`. -/
theorem exceptionalDivisor_subset_closedNbhd {ε : ℝ} (hε : 0 < ε) :
    exceptionalDivisor n ⊆ closedNbhd n ε :=
  (exceptionalDivisor_subset_openNbhd hε).trans (openNbhd_subset_closedNbhd ε)

/-! ### The forms `ω̃_λ` -/

variable (n) in
/-- The form `ω̃_l = π^* ω₀ + l² pr^* ω_FS` on the model blowup, for `l : ℝ`, where `π` is the
blowdown, `pr` the projection to `ℙ ℂ E` and `ω_FS` the Fubini–Study form. -/
noncomputable def blowupForm (l : ℝ) : SmoothTwoForm 𝓘(ℝ, Fin (n + 1) → ℂ) (BlowupModel n) :=
  SmoothForm.mpullback blowdown ((contMDiff_blowdown ∞).restrictScalars' ℝ) (ω₀E n) +
    l ^ 2 • SmoothForm.mpullback pr ((contMDiff_pr ∞).restrictScalars' ℝ) (fubiniStudyForm n)

theorem blowupForm_def (l : ℝ) :
    blowupForm n l =
      SmoothForm.mpullback blowdown ((contMDiff_blowdown ∞).restrictScalars' ℝ) (ω₀E n) +
      l ^ 2 • SmoothForm.mpullback pr ((contMDiff_pr ∞).restrictScalars' ℝ) (fubiniStudyForm n) :=
  (rfl)

/-- The form `ω̃_l` is closed, as the sum of pull-backs of the closed forms `ω₀` and `ω_FS`. -/
theorem isClosed_blowupForm (l : ℝ) : (blowupForm n l).IsClosed := by
  rw [blowupForm_def]
  exact ((SymplecticForm.isClosed_constSmooth _).mpullback _ _).add
    (((isSymplectic_fubiniStudyForm n).isClosed.mpullback _ _).smul _)

/-- On the exceptional divisor, `ω̃_l` restricts to `l² ω_FS`: its pull-back along the zero
section is `l² • fubiniStudyForm n`, since the blowdown is constant on the divisor and `pr` is a
left inverse of the zero section. -/
theorem mpullback_zeroSection_blowupForm (l : ℝ) :
    SmoothForm.mpullback zeroSection ((contMDiff_zeroSection ∞).restrictScalars' ℝ)
        (blowupForm n l) =
      l ^ 2 • fubiniStudyForm n := by
  rw [blowupForm_def, map_add, map_smul, SmoothForm.mpullback_mpullback,
    SmoothForm.mpullback_mpullback]
  have h₁ : (blowdown ∘ zeroSection : ℙ ℂ (Fin (n + 1) → ℂ) → Fin (n + 1) → ℂ) = fun _ ↦ 0 :=
    funext blowdown_zeroSection
  have h₂ : (pr ∘ zeroSection : ℙ ℂ (Fin (n + 1) → ℂ) → ℙ ℂ (Fin (n + 1) → ℂ)) = id :=
    funext pr_zeroSection
  rw [SmoothForm.mpullback_congr _
    (contMDiff_const (I := 𝓘(ℝ, Fin n → ℂ)) (I' := 𝓘(ℝ, Fin (n + 1) → ℂ))) h₁,
    SmoothForm.mpullback_congr _ contMDiff_id h₂,
    SmoothForm.mpullback_id, ω₀E_def, SmoothForm.mpullback_const, LinearMap.id_apply, zero_add]

/-- Every projective line of the exceptional divisor has area `π l²` for `ω̃_l`: for an injective
linear map `f : ℂ² → E`, the integral of `ω̃_l` over the line `ℙ(f(ℂ²))`, embedded in the divisor
by the zero section and oriented by its complex structure, is `π * l ^ 2`. -/
theorem integralTopForm_blowupForm_line (l : ℝ) (f : (Fin 2 → ℂ) →ₗ[ℂ] Fin (n + 1) → ℂ)
    (hf : Function.Injective f) :
    integralTopForm (complexCurveOrientation (Fin 1 → ℂ) (ℙ ℂ (Fin 2 → ℂ)))
      (SmoothForm.mpullback (zeroSection ∘ map f hf)
        (((contMDiff_zeroSection ∞).restrictScalars' ℝ).comp
          (contMDiff_map_restrictScalars f hf ∞))
        (blowupForm n l)).val = Real.pi * l ^ 2 := by
  rw [← SmoothForm.mpullback_mpullback (map f hf) zeroSection
    (contMDiff_map_restrictScalars f hf ∞)
    ((contMDiff_zeroSection ∞).restrictScalars' ℝ), mpullback_zeroSection_blowupForm, map_smul,
    SetLike.val_smul, integralTopForm_smul, integralTopForm_mpullback_map_fubiniStudyForm,
    mul_comm]

end BlowupModel

end SymplecticGeometry

end
