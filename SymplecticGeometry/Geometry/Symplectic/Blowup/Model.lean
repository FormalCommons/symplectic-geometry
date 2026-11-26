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
public import SymplecticGeometry.Geometry.Manifold.Projectivization.FubiniStudy.Kahler
public import TauCeti.Geometry.Symplectic.Manifold.Kahler
public import SymplecticGeometry.Geometry.Symplectic.Complex.Radial
public import SymplecticGeometry.Geometry.Manifold.Diffeomorph.Basic
public import SymplecticGeometry.Geometry.Manifold.Diffeomorph.Opens
public import SymplecticGeometry.Geometry.Manifold.Diffeomorph.RestrictScalars
import SymplecticGeometry.Geometry.Symplectic.Manifold.AlmostComplex.Pseudoholomorphic
import SymplecticGeometry.Analysis.Complex.Euclidean.Space
public import TauCeti.Geometry.Symplectic.Manifold.SymplecticMap
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Pullback.Smooth

/-!
# The forms `ω̃_λ` on the model blowup

For `n : ℕ` and `E := Fin (n + 1) → ℂ`, let `π : BlowupModel n → E` be the blowdown and
`pr : BlowupModel n → ℙ ℂ E` the projection of the model blowup of `E` at `0`
(`Geometry/Manifold/Complex/Blowup/Model.lean`), seen as real manifolds with the real structure
of the complex manifold (the scoped instance `TauCeti.ComplexManifold.isManifold_real`). Following
McDuff–Salamon, §7.1, this file defines on the model the closed two-forms
`ω̃_λ = π^* ω₀ + λ² pr^* ω_FS`, shows that they are Kähler for `λ ≠ 0`, computes their restriction
to the exceptional divisor `Z`, and sets up the neighbourhoods `L(ε)` of `Z`.

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
* `SymplecticGeometry.BlowupModel.isKahler_blowupForm`: for `l ≠ 0`, `ω̃_l` is Kähler for the
  complex structure of the model, and so `SymplecticGeometry.BlowupModel.isSymplectic_blowupForm`:
  it is symplectic. Since `π` and `pr` are holomorphic and `ω₀`, `ω_FS` are compatible with
  their complex structures (`SymplecticGeometry.BlowupModel.compatible_ω₀E`,
  `isKahler_fubiniStudyForm`), both terms are invariant under `i` and nonnegative on `(v, i v)`
  (`TauCeti.SmoothTwoForm.Invariant.mpullback`, `TauCeti.SmoothTwoForm.Tames.eval₂_mpullback_pos`
  and `TauCeti.SmoothTwoForm.Tames.eval₂_mpullback_nonneg`); one of them is positive for `v ≠ 0`,
  since the inclusion `(pr, π)` into `ℙ ℂ E × E` is an immersion
  (`mfderiv_pr_eq_zero_and_mfderiv_blowdown_eq_zero_iff`).
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

/-- The standard form `ω₀E n` is compatible with the complex structure of `E`, multiplication by
`i`. -/
theorem compatible_ω₀E :
    (ω₀E n).Compatible
      (SmoothAlmostComplexStructure.ofComplexManifold (Fin (n + 1) → ℂ) (Fin (n + 1) → ℂ)) := by
  rw [ω₀E_def, SmoothAlmostComplexStructure.ofComplexManifold_self_eq_constSmooth]
  exact SymplecticForm.compatible_constSmooth_iff.2 stdComplexPiSymplecticForm_compatible

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

open SmoothAlmostComplexStructure in
/-- For `l ≠ 0`, the form `ω̃_l` is Kähler for the complex structure of the model blowup: it is
closed, invariant under `i`, and `ω̃_l(v, i v) > 0` for every nonzero tangent vector `v`. -/
theorem isKahler_blowupForm {l : ℝ} (hl : l ≠ 0) :
    (blowupForm n l).IsKahler (ofComplexManifold (Fin (n + 1) → ℂ) (BlowupModel n)) := by
  have hb : IsPseudoholomorphic (ofComplexManifold (Fin (n + 1) → ℂ) (BlowupModel n))
      (ofComplexManifold (Fin (n + 1) → ℂ) (Fin (n + 1) → ℂ)) blowdown :=
    isPseudoholomorphic_ofComplexManifold_iff.2 ((contMDiff_blowdown ∞).mdifferentiable (by simp))
  have hp : IsPseudoholomorphic (ofComplexManifold (Fin (n + 1) → ℂ) (BlowupModel n))
      (ofComplexManifold (Fin n → ℂ) (ℙ ℂ (Fin (n + 1) → ℂ))) pr :=
    isPseudoholomorphic_ofComplexManifold_iff.2 ((contMDiff_pr ∞).mdifferentiable (by simp))
  have hω := compatible_ω₀E (n := n)
  have hFS := (isKahler_fubiniStudyForm (n := n)).compatible
  refine SmoothTwoForm.isKahler_ofComplexManifold_iff.2 ⟨isClosed_blowupForm l, ⟨?_, ?_⟩⟩
  · refine SmoothTwoForm.invariant_iff.2 fun x v w ↦ ?_
    rw [blowupForm_def, SmoothBundleForm.eval₂_add, SmoothBundleForm.eval₂_add,
      SmoothForm.eval₂_smul, SmoothForm.eval₂_smul, (hω.invariant.mpullback hb _).apply,
      (hFS.invariant.mpullback hp _).apply]
  · -- Both terms are nonnegative on `(v, i v)`, and one of them is positive, since the real
    -- differentials of `pr` and of the blowdown do not both vanish on `v ≠ 0`.
    refine SmoothTwoForm.tames_iff.2 fun x v hv ↦ ?_
    rw [blowupForm_def, SmoothBundleForm.eval₂_add, SmoothForm.eval₂_smul, smul_eq_mul]
    have hb₀ := hω.tames.eval₂_mpullback_nonneg (hb.isPseudoholomorphicAt x)
      ((contMDiff_blowdown ∞).restrictScalars' ℝ) v
    have hp₀ := hFS.tames.eval₂_mpullback_nonneg (hp.isPseudoholomorphicAt x)
      ((contMDiff_pr ∞).restrictScalars' ℝ) v
    have hl₂ : 0 < l ^ 2 := pow_pos (abs_pos.2 hl) 2 |>.trans_eq (by simp)
    by_cases h : mfderiv 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) blowdown x v = 0
    · refine add_pos_of_nonneg_of_pos hb₀ (mul_pos hl₂ ?_)
      exact hFS.tames.eval₂_mpullback_pos (hp.isPseudoholomorphicAt x) _ fun h' ↦
        hv (mfderiv_pr_eq_zero_and_mfderiv_blowdown_eq_zero_iff.1 ⟨h', h⟩)
    · exact add_pos_of_pos_of_nonneg
        (hω.tames.eval₂_mpullback_pos (hb.isPseudoholomorphicAt x) _ h) (mul_nonneg hl₂.le hp₀)

/-- For `l ≠ 0`, the form `ω̃_l` on the model blowup is symplectic. -/
theorem isSymplectic_blowupForm {l : ℝ} (hl : l ≠ 0) : (blowupForm n l).IsSymplectic :=
  (isKahler_blowupForm hl).isSymplectic

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

/-! ### The forms `ω̃_λ` off the divisor, and the shell -/

section Shell

open TopologicalSpace

variable (n) in
/-- The blowdown off the exceptional divisor, `blowdownDiffeomorph n`, as a diffeomorphism of real
manifolds onto the punctured space `E ∖ 0 = puncturedSpace E`, on which the radial forms and maps
of `Geometry/Symplectic/Complex/Radial.lean` live. -/
noncomputable def blowdownPuncturedDiffeomorph :
    (⟨(exceptionalDivisor n)ᶜ, isClosed_exceptionalDivisor.isOpen_compl⟩ : Opens (BlowupModel n))
      ≃ₘ⟮𝓘(ℝ, Fin (n + 1) → ℂ), 𝓘(ℝ, Fin (n + 1) → ℂ)⟯ puncturedSpace (Fin (n + 1) → ℂ) :=
  (((blowdownDiffeomorph n).restrictScalars' ℝ).ofLE le_top).restrictOpens le_rfl
    (fun _ hz ↦ mem_puncturedSpace.1 hz) fun p ↦
      iff_of_true p.property (by
        rw [mem_puncturedSpace, Diffeomorph.coe_ofLE, Diffeomorph.coe_restrictScalars']
        exact (blowdownDiffeomorph n p).property)

@[simp]
theorem coe_blowdownPuncturedDiffeomorph_apply
    (p : (⟨(exceptionalDivisor n)ᶜ, isClosed_exceptionalDivisor.isOpen_compl⟩ :
      Opens (BlowupModel n))) :
    (blowdownPuncturedDiffeomorph n p : Fin (n + 1) → ℂ) = p.val.blowdown := by
  rw [blowdownPuncturedDiffeomorph, Diffeomorph.coe_restrictOpens_apply, Diffeomorph.coe_ofLE,
    Diffeomorph.coe_restrictScalars', coe_blowdownDiffeomorph]

@[simp]
theorem coe_blowdownPuncturedDiffeomorph_symm_apply (z : puncturedSpace (Fin (n + 1) → ℂ)) :
    ((blowdownPuncturedDiffeomorph n).symm z : BlowupModel n) =
      ⟨(mk ℂ z (mem_puncturedSpace.1 z.property), z), mk_self_mem_blowupModel _⟩ := by
  rw [blowdownPuncturedDiffeomorph, Diffeomorph.coe_restrictOpens_symm_apply, Diffeomorph.ofLE_symm,
    Diffeomorph.coe_ofLE, Diffeomorph.restrictScalars'_symm, Diffeomorph.coe_restrictScalars',
    blowdownDiffeomorph_symm_apply]

/-- The radial potential `s ↦ s + l² log s` is smooth on `(0, ∞)`. -/
theorem contDiffOn_add_mul_log (l : ℝ) :
    ContDiffOn ℝ ∞ (fun s ↦ s + l ^ 2 * Real.log s) (Ioi 0) :=
  contDiffOn_id.add (contDiffOn_const.mul (Real.contDiffOn_log.mono fun _ hs ↦ ne_of_gt hs))

/-- Off the exceptional divisor, `ω̃_l` is the form of the radial potential `|z|² + l² log |z|²`:
its pull-back along the inverse of the blowdown, from `E ∖ 0` to the complement of the divisor,
is `radialPotentialForm` of `s ↦ s + l² log s`. -/
theorem mpullback_blowdownDiffeomorph_symm_blowupForm (l : ℝ) :
    SmoothForm.mpullback (blowdownPuncturedDiffeomorph n).symm
        (blowdownPuncturedDiffeomorph n).symm.contMDiff
        (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal (blowupForm n l)) =
      radialPotentialForm (Fin (n + 1)) (fun s ↦ s + l ^ 2 * Real.log s)
        (contDiffOn_add_mul_log l) := by
  have hlog : ContDiffOn ℝ ∞ Real.log (Ioi 0) :=
    Real.contDiffOn_log.mono fun _ hs ↦ ne_of_gt hs
  rw [radialPotentialForm_add (g₁ := fun s ↦ s) contDiffOn_id (contDiffOn_const.mul hlog),
    radialPotentialForm_const_mul _ hlog, radialPotentialForm_log n hlog]
  erw [radialPotentialForm_id]
  rw [blowupForm_def, map_add, map_smul, map_add, map_smul, SmoothForm.mpullback_mpullback,
    SmoothForm.mpullback_mpullback, SmoothForm.mpullback_mpullback,
    SmoothForm.mpullback_mpullback, ← mpullback_mkNonzero_fubiniStudyForm, ω₀E_def]
  congr 1
  · refine SmoothForm.mpullback_congr _ _ (funext fun z ↦ ?_) _
    rw [Function.comp_apply, Function.comp_apply, coe_blowdownPuncturedDiffeomorph_symm_apply,
      blowdown_mk]
  · refine congrArg _ (SmoothForm.mpullback_congr _ _ (funext fun z ↦ ?_) _)
    rw [Function.comp_apply, Function.comp_apply, coe_blowdownPuncturedDiffeomorph_symm_apply,
      pr_mk, mkNonzero_apply]

/-- The radial map `F_l z = √(1 + l² / |z|²) z` of the profile `h s = s + l²`, composed with the
blowdown, pulls `ω₀` back to `ω̃_l` off the exceptional divisor. -/
theorem mpullback_radialMap_blowdown (l : ℝ) :
    SmoothForm.mpullback
        (radialMap (fun s ↦ s + l ^ 2) (fun _ hs ↦ add_pos_of_pos_of_nonneg hs (sq_nonneg l)) ∘
          blowdownPuncturedDiffeomorph n)
        ((contMDiff_radialMap (h := fun s ↦ s + l ^ 2) (contDiffOn_id.add contDiffOn_const) _).comp
          (blowdownPuncturedDiffeomorph n).contMDiff)
        (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal (ω₀E n)) =
      SmoothForm.mpullback Subtype.val contMDiff_subtypeVal (blowupForm n l) := by
  have hgh : ∀ s ∈ Ioi (0 : ℝ), deriv (fun s ↦ s + l ^ 2 * Real.log s) s = (s + l ^ 2) / s :=
    fun s hs ↦ by
      have hs : s ≠ 0 := ne_of_gt hs
      rw [deriv_fun_add (f := fun s ↦ s) differentiableAt_id
          ((Real.differentiableAt_log hs).const_mul _),
        deriv_const_mul_field, Real.deriv_log, deriv_id'']
      field_simp
  have hs : ContDiffOn ℝ ∞ (fun s ↦ s + l ^ 2) (Ioi 0) := contDiffOn_id.add contDiffOn_const
  rw [← SmoothForm.mpullback_mpullback _ _ (blowdownPuncturedDiffeomorph n).contMDiff
      (contMDiff_radialMap hs _), ω₀E_def,
    mpullback_radialMap_stdForm (ι := Fin (n + 1)) hs _ (contDiffOn_add_mul_log l) hgh,
    ← mpullback_blowdownDiffeomorph_symm_blowupForm, SmoothForm.mpullback_mpullback_symm]

variable (n) in
/-- The radial map `F_l z = √(1 + l² / |z|²) z` composed with the blowdown, as a diffeomorphism
from the complement of the exceptional divisor onto the shell `{w | l² < |w|²}` of `E`, the shell
of the profile `s ↦ s + l²` (`radialShell`). It carries `ω̃_l` to `ω₀`
(`isSymplectomorphism_radialBlowdownDiffeomorph`). -/
noncomputable def radialBlowdownDiffeomorph (l : ℝ) :
    (⟨(exceptionalDivisor n)ᶜ, isClosed_exceptionalDivisor.isOpen_compl⟩ : Opens (BlowupModel n))
      ≃ₘ⟮𝓘(ℝ, Fin (n + 1) → ℂ), 𝓘(ℝ, Fin (n + 1) → ℂ)⟯
      radialShell (Fin (n + 1)) (fun s ↦ s + l ^ 2) (contDiffOn_id.add contDiffOn_const)
        (fun _ _ ↦ by simp) :=
  (blowdownPuncturedDiffeomorph n).trans
    (radialMapDiffeomorph _ _ _ (fun _ hs ↦ add_pos_of_pos_of_nonneg hs (sq_nonneg l)) _)

theorem coe_radialBlowdownDiffeomorph_apply (l : ℝ)
    (p : (⟨(exceptionalDivisor n)ᶜ, isClosed_exceptionalDivisor.isOpen_compl⟩ :
      Opens (BlowupModel n))) :
    (radialBlowdownDiffeomorph n l p : Fin (n + 1) → ℂ) =
      radialMap (fun s ↦ s + l ^ 2) (fun _ hs ↦ add_pos_of_pos_of_nonneg hs (sq_nonneg l))
        (blowdownPuncturedDiffeomorph n p) := by
  rw [radialBlowdownDiffeomorph, Diffeomorph.coe_trans, Function.comp_apply,
    coe_radialMapDiffeomorph_apply]

/-- The map `F_l ∘ π` adds `l²` to the squared Euclidean norm of the blowdown. -/
theorem norm_sq_radialBlowdownDiffeomorph (l : ℝ)
    (p : (⟨(exceptionalDivisor n)ᶜ, isClosed_exceptionalDivisor.isOpen_compl⟩ :
      Opens (BlowupModel n))) :
    ‖complexToRealEuclidean (Fin (n + 1)) (radialBlowdownDiffeomorph n l p)‖ ^ 2 =
      ‖complexToRealEuclidean (Fin (n + 1)) p.val.blowdown‖ ^ 2 + l ^ 2 := by
  rw [coe_radialBlowdownDiffeomorph_apply, norm_radialMap, coe_blowdownPuncturedDiffeomorph_apply]

/-- **`F_l ∘ π` is a symplectomorphism**: off the exceptional divisor it carries `ω̃_l` to the
standard form `ω₀` of `E`, restricted to the shell `{w | l² < |w|²}`. -/
theorem isSymplectomorphism_radialBlowdownDiffeomorph (l : ℝ) :
    SmoothTwoForm.IsSymplectomorphism
      (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal (blowupForm n l))
      (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal (ω₀E n))
      (radialBlowdownDiffeomorph n l) := by
  rw [SmoothTwoForm.isSymplectomorphism_iff_mpullback_eq, ← mpullback_radialMap_blowdown l]
  exact SmoothForm.mpullback_mpullback_of_comp_eq _ _ _ _
    (funext fun p ↦ coe_radialBlowdownDiffeomorph_apply l p) _

/-- `F_l ∘ π` maps the complement of the divisor into `{w | l < |w|}`, for `0 ≤ l`. -/
theorem lt_norm_radialBlowdownDiffeomorph {l : ℝ} (hl : 0 ≤ l)
    (p : (⟨(exceptionalDivisor n)ᶜ, isClosed_exceptionalDivisor.isOpen_compl⟩ :
      Opens (BlowupModel n))) :
    l < ‖complexToRealEuclidean (Fin (n + 1)) (radialBlowdownDiffeomorph n l p)‖ := by
  refine (pow_lt_pow_iff_left₀ hl (norm_nonneg _) two_ne_zero).1 ?_
  rw [norm_sq_radialBlowdownDiffeomorph, lt_add_iff_pos_left]
  have := norm_sq_complexToRealEuclidean_pos (blowdownPuncturedDiffeomorph n p)
  rwa [coe_blowdownPuncturedDiffeomorph_apply] at this

/-- For `0 ≤ ε`, a point off the divisor lies in the open neighbourhood of radius `ε` exactly when
its image under `F_l ∘ π` has Euclidean norm less than `√(l² + ε²)`. -/
theorem mem_openNbhd_iff_radialBlowdownDiffeomorph (l : ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (p : (⟨(exceptionalDivisor n)ᶜ, isClosed_exceptionalDivisor.isOpen_compl⟩ :
      Opens (BlowupModel n))) :
    p.val ∈ openNbhd n ε ↔
      ‖complexToRealEuclidean (Fin (n + 1)) (radialBlowdownDiffeomorph n l p)‖ <
        √(l ^ 2 + ε ^ 2) := by
  rw [mem_openNbhd_iff, Real.lt_sqrt (norm_nonneg _), norm_sq_radialBlowdownDiffeomorph,
    add_comm (l ^ 2) (ε ^ 2), add_lt_add_iff_right,
    pow_lt_pow_iff_left₀ (norm_nonneg _) hε two_ne_zero]

/-- For `0 ≤ ε`, a point off the divisor lies in `L(ε)` exactly when its image under `F_l ∘ π`
has Euclidean norm at most `√(l² + ε²)`. -/
theorem mem_closedNbhd_iff_radialBlowdownDiffeomorph (l : ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (p : (⟨(exceptionalDivisor n)ᶜ, isClosed_exceptionalDivisor.isOpen_compl⟩ :
      Opens (BlowupModel n))) :
    p.val ∈ closedNbhd n ε ↔
      ‖complexToRealEuclidean (Fin (n + 1)) (radialBlowdownDiffeomorph n l p)‖ ≤
        √(l ^ 2 + ε ^ 2) := by
  rw [mem_closedNbhd_iff, Real.le_sqrt (norm_nonneg _) (by positivity),
    norm_sq_radialBlowdownDiffeomorph, add_comm (l ^ 2) (ε ^ 2), add_le_add_iff_right,
    pow_le_pow_iff_left₀ (norm_nonneg _) hε two_ne_zero]

/-- For `0 ≤ l`, every `w` with `l < |w|` lies in the shell of `F_l ∘ π`. -/
theorem mem_radialShell_add_sq {l : ℝ} (hl : 0 ≤ l) {w : Fin (n + 1) → ℂ}
    (hw : l < ‖complexToRealEuclidean (Fin (n + 1)) w‖) :
    w ∈ radialShell (Fin (n + 1)) (fun s ↦ s + l ^ 2) (contDiffOn_id.add contDiffOn_const)
      (fun _ _ ↦ by simp) := by
  rw [mem_radialShell, ← norm_sq_complexToRealEuclidean]
  exact ⟨_, sub_pos.2 (pow_lt_pow_left₀ hw hl two_ne_zero), sub_add_cancel _ _⟩

/-- **The closed shell.** For `0 ≤ l` and `0 ≤ ε`, `F_l ∘ π` maps `L(ε) ∖ Z` onto the shell
`l < |w| ≤ √(l² + ε²)` of `E`; with `isSymplectomorphism_radialBlowdownDiffeomorph`,
`(L(ε) ∖ Z, ω̃_l)` is symplectomorphic to this shell with `ω₀`. -/
theorem image_closedNbhd_radialBlowdownDiffeomorph {l ε : ℝ} (hl : 0 ≤ l) (hε : 0 ≤ ε) :
    (fun p ↦ (radialBlowdownDiffeomorph n l p : Fin (n + 1) → ℂ)) '' {p | p.val ∈ closedNbhd n ε} =
      {w | l < ‖complexToRealEuclidean (Fin (n + 1)) w‖ ∧
        ‖complexToRealEuclidean (Fin (n + 1)) w‖ ≤ √(l ^ 2 + ε ^ 2)} := by
  ext w
  refine ⟨?_, fun hw ↦ ?_⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨lt_norm_radialBlowdownDiffeomorph hl p,
      (mem_closedNbhd_iff_radialBlowdownDiffeomorph l hε p).1 hp⟩
  · obtain ⟨p, hp⟩ := (radialBlowdownDiffeomorph n l).surjective ⟨w, mem_radialShell_add_sq hl hw.1⟩
    have hp' : (radialBlowdownDiffeomorph n l p : Fin (n + 1) → ℂ) = w := congrArg Subtype.val hp
    exact ⟨p, (mem_closedNbhd_iff_radialBlowdownDiffeomorph l hε p).2 (hp' ▸ hw.2), hp'⟩

variable (n) in
/-- The open shell `l < |w| < √(l² + ε²)` of `E`, for the Euclidean norm `|w|`. -/
def openShell (l ε : ℝ) : Opens (Fin (n + 1) → ℂ) :=
  ⟨{w | l < ‖complexToRealEuclidean (Fin (n + 1)) w‖ ∧
      ‖complexToRealEuclidean (Fin (n + 1)) w‖ < √(l ^ 2 + ε ^ 2)},
    (isOpen_lt continuous_const (complexToRealEuclidean (Fin (n + 1))).continuous.norm).inter
      (isOpen_lt (complexToRealEuclidean (Fin (n + 1))).continuous.norm continuous_const)⟩

@[simp]
theorem mem_openShell_iff {l ε : ℝ} {w : Fin (n + 1) → ℂ} :
    w ∈ openShell n l ε ↔ l < ‖complexToRealEuclidean (Fin (n + 1)) w‖ ∧
      ‖complexToRealEuclidean (Fin (n + 1)) w‖ < √(l ^ 2 + ε ^ 2) :=
  Iff.rfl

variable (n) in
/-- **The open shell.** For `0 ≤ l` and `0 ≤ ε`, the map `F_l ∘ π` as a diffeomorphism from the
open neighbourhood of radius `ε` minus the exceptional divisor onto the open shell
`l < |w| < √(l² + ε²)` of `E`. It carries `ω̃_l` to `ω₀`
(`isSymplectomorphism_shellSymplectomorph`). -/
noncomputable def shellSymplectomorph (l ε : ℝ) (hl : 0 ≤ l) (hε : 0 ≤ ε) :
    (⟨openNbhd n ε \ exceptionalDivisor n,
        (isOpen_openNbhd ε).sdiff isClosed_exceptionalDivisor⟩ : Opens (BlowupModel n))
      ≃ₘ⟮𝓘(ℝ, Fin (n + 1) → ℂ), 𝓘(ℝ, Fin (n + 1) → ℂ)⟯ openShell n l ε :=
  (radialBlowdownDiffeomorph n l).restrictOpens (fun _ hp ↦ hp.2)
    (fun _ hw ↦ mem_radialShell_add_sq hl hw.1) fun p ↦
      ⟨fun hp ↦ ⟨lt_norm_radialBlowdownDiffeomorph hl p,
          (mem_openNbhd_iff_radialBlowdownDiffeomorph l hε p).1 hp.1⟩,
        fun hw ↦ ⟨(mem_openNbhd_iff_radialBlowdownDiffeomorph l hε p).2 hw.2, p.property⟩⟩

theorem coe_shellSymplectomorph_apply {l ε : ℝ} (hl : 0 ≤ l) (hε : 0 ≤ ε)
    (p : (⟨openNbhd n ε \ exceptionalDivisor n,
        (isOpen_openNbhd ε).sdiff isClosed_exceptionalDivisor⟩ : Opens (BlowupModel n))) :
    (shellSymplectomorph n l ε hl hε p : Fin (n + 1) → ℂ) =
      radialMap (fun s ↦ s + l ^ 2) (fun _ hs ↦ add_pos_of_pos_of_nonneg hs (sq_nonneg l))
        (blowdownPuncturedDiffeomorph n ⟨p.val, p.property.2⟩) := by
  rw [shellSymplectomorph, Diffeomorph.coe_restrictOpens_apply,
    coe_radialBlowdownDiffeomorph_apply]

/-- **The shell symplectomorphism.** `shellSymplectomorph` carries `ω̃_l` on the open
neighbourhood of radius `ε` minus the exceptional divisor to `ω₀` on the open shell
`l < |w| < √(l² + ε²)`. -/
theorem isSymplectomorphism_shellSymplectomorph {l ε : ℝ} (hl : 0 ≤ l) (hε : 0 ≤ ε) :
    SmoothTwoForm.IsSymplectomorphism
      (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal (blowupForm n l))
      (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal (ω₀E n))
      (shellSymplectomorph n l ε hl hε) := by
  have hU : (⟨openNbhd n ε \ exceptionalDivisor n,
      (isOpen_openNbhd ε).sdiff isClosed_exceptionalDivisor⟩ : Opens (BlowupModel n)) ≤
      ⟨(exceptionalDivisor n)ᶜ, isClosed_exceptionalDivisor.isOpen_compl⟩ := fun _ hp ↦ hp.2
  have h := SmoothTwoForm.isSymplectomorphism_iff_mpullback_eq.1
    (isSymplectomorphism_radialBlowdownDiffeomorph (n := n) l)
  have hΨ := (radialBlowdownDiffeomorph n l).contMDiff
  rw [SmoothTwoForm.isSymplectomorphism_iff_mpullback_eq, SmoothForm.mpullback_mpullback,
    SmoothForm.mpullback_congr _ ((contMDiff_subtypeVal.comp hΨ).comp (contMDiff_inclusion hU))
      (show Subtype.val ∘ ⇑(shellSymplectomorph n l ε hl hε) =
          (Subtype.val ∘ ⇑(radialBlowdownDiffeomorph n l)) ∘ Opens.inclusion hU from
        funext fun x ↦ Diffeomorph.coe_restrictOpens_apply _ hU _ _ x),
    ← SmoothForm.mpullback_mpullback _ _ (contMDiff_inclusion hU) (contMDiff_subtypeVal.comp hΨ),
    ← SmoothForm.mpullback_mpullback _ _ hΨ contMDiff_subtypeVal, h,
    SmoothForm.mpullback_mpullback]
  exact SmoothForm.mpullback_congr _ _ (funext fun _ ↦ rfl) _

end Shell

end BlowupModel

end SymplecticGeometry

end
