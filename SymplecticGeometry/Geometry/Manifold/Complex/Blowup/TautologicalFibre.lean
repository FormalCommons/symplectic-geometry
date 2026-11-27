/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Complex.Blowup.Lift
public import SymplecticGeometry.Geometry.Manifold.Complex.Blowup.Tautological
import SymplecticGeometry.Geometry.Manifold.ContMDiff.RestrictScalars
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.MFDeriv.RestrictScalars

/-!
# A fibre of the tautological line as a curve in the model blowup

For a nonzero vector `v` of `E := Fin (n + 1) → ℂ`, the lift `curveLift (· • v)` of the complex
line `t ↦ t • v` through `0` parametrizes the fibre of the tautological line over the line
`ℓ = mk ℂ v hv`: its line is `ℓ` at every `t`, `t = 0` included, its blowdown is `t • v`, and it
meets the exceptional divisor only at `t = 0`, in the point `zeroSection ℓ`. This file gives the
API of this map that the computation of the class of the blowup form on a fibre uses: smoothness,
and its real derivative at `0`, which, read in the normal space of the exceptional divisor through
`normalSpaceZeroSectionRealEquiv`, is `t ↦ t • v` (McDuff–Salamon, §7.1). This is the form of the
derivative hypothesis of the slice lemma
`TauCeti.SmoothEmbedding.singularCohomologyMap_slice_eq_of_hasFDerivAt`.

## Main results

* `SymplecticGeometry.BlowupModel.curveLift_smul_zero`: the value at `0` is `zeroSection ℓ`.
* `SymplecticGeometry.BlowupModel.pr_curveLift_smul`: the line of every point is `ℓ`.
* `SymplecticGeometry.BlowupModel.curveLift_smul_mem_exceptionalDivisor_iff`: the map meets the
  exceptional divisor only at `0`.
* `SymplecticGeometry.BlowupModel.contMDiff_curveLift_smul` and
  `SymplecticGeometry.BlowupModel.contMDiff_curveLift_smul_real`: it is holomorphic, hence smooth
  over `ℝ`.
* `SymplecticGeometry.BlowupModel.exists_hasMFDerivAt_curveLift_smul_zero`: a real derivative
  `A` at `0` that, followed by the normal class map of `zeroSectionRealEmbedding n` at `ℓ` and
  by `normalSpaceZeroSectionRealEquiv n hn ℓ`, sends `t` to `t • v`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §7.1
-/

public section

namespace SymplecticGeometry

namespace BlowupModel

open Projectivization Filter
open scoped Manifold ContDiff LinearAlgebra.Projectivization

variable {n : ℕ} {v : Fin (n + 1) → ℂ}

/-- The lift of the line `t ↦ t • v` sends `0` to the point `zeroSection ℓ` of the exceptional
divisor over the line `ℓ` spanned by `v`. -/
theorem curveLift_smul_zero (hv : v ≠ 0) :
    curveLift (· • v) (0 : ℂ) = zeroSection (mk ℂ v hv) := by
  classical
  -- The line `t ↦ t • v` has a simple zero at `0`.
  have h1 : analyticOrderAt (fun t : ℂ ↦ t • v) 0 = (1 : ℕ) := by
    rw [analyticOrderAt_fun_smul_const (f := fun t : ℂ ↦ t) analyticAt_id, ite_eq_right hv]
    exact analyticOrderAt_id
  rw [curveLift_apply_self (by fun_prop) (zero_smul ℂ v) h1]
  congr 1
  rw [mk_eq_mk_iff' ℂ _ _ _ hv]
  exact ⟨1, by simp [iteratedDeriv_one, deriv_smul_const]⟩

/-- The lift of the line `t ↦ t • v` lies, at every `t`, on the line `ℓ` spanned by `v`. -/
@[simp]
theorem pr_curveLift_smul (hv : v ≠ 0) (t : ℂ) :
    (curveLift (· • v) t).pr = mk ℂ v hv := by
  rcases eq_or_ne t 0 with rfl | ht
  · rw [curveLift_smul_zero hv, pr_zeroSection]
  · rw [pr_curveLift_of_ne_zero (smul_ne_zero ht hv), mk_eq_mk_iff' ℂ _ _ _ hv]
    exact ⟨t, rfl⟩

/-- The lift of the line `t ↦ t • v` through a nonzero `v` meets the exceptional divisor only at
`t = 0`. -/
theorem curveLift_smul_mem_exceptionalDivisor_iff (hv : v ≠ 0) {t : ℂ} :
    curveLift (· • v) t ∈ exceptionalDivisor n ↔ t = 0 := by
  simp [hv]

/-- The lift of the line `t ↦ t • v` through a nonzero `v` is holomorphic. -/
theorem contMDiff_curveLift_smul (hv : v ≠ 0) {r : ℕ∞ω} :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) r (curveLift (· • v)) := fun t ↦
  contMDiffAt_curveLift (by fun_prop)
    ((AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero t fun _ ↦ by fun_prop).not.2
      fun h ↦ hv (by simpa using congrFun h 1))

/-- The lift of the line `t ↦ t • v` through a nonzero `v` is smooth over `ℝ`. -/
theorem contMDiff_curveLift_smul_real (hv : v ≠ 0) {r : ℕ∞ω} :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) r (curveLift (· • v)) :=
  ContMDiff.restrictScalars' ℝ (contMDiff_curveLift_smul hv)

/-- The lift of the line `t ↦ t • v` through a nonzero `v` has at `0` a real derivative, a
real-linear map `A : ℂ →L[ℝ] E`, which, followed by the normal class map of the real zero section
`zeroSectionRealEmbedding n` at the line `ℓ` spanned by `v` and by
`normalSpaceZeroSectionRealEquiv n hn ℓ`, sends `t` to `t • v`. -/
theorem exists_hasMFDerivAt_curveLift_smul_zero {hn : (∞ : ℕ∞ω) ≠ 0} (hv : v ≠ 0) :
    ∃ A : ℂ →L[ℝ] Fin (n + 1) → ℂ,
      HasMFDerivAt 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) (curveLift (· • v)) 0 A ∧
      ∀ t : ℂ, normalSpaceZeroSectionRealEquiv n hn (mk ℂ v hv)
          ((zeroSectionRealEmbedding n).isImmersion.normalClassL (mk ℂ v hv) hn (A t)) =
        ⟨t • v, by
          rw [submodule_mk]
          exact Submodule.smul_mem _ t (Submodule.mem_span_singleton_self v)⟩ := by
  have hF := ((contMDiff_curveLift_smul_real (r := 1) hv).mdifferentiable one_ne_zero) 0
  refine ⟨mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) (curveLift (· • v)) 0, hF.hasMFDerivAt,
    fun t ↦ ?_⟩
  refine (congrArg _ (Manifold.IsImmersion.normalClassL_apply _ _ _ _)).trans
    ((normalSpaceZeroSectionRealEquiv_normalClass _ _).trans (Subtype.ext ?_))
  dsimp only
  have hb : MDifferentiableAt 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) blowdown
      (zeroSection (mk ℂ v hv)) :=
    (contMDiff_blowdown 1).mdifferentiable one_ne_zero _
  rw [← hb.mfderiv_modelWithCornersSelf_restrictScalars_apply ℝ]
  have hb' : MDifferentiableAt 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) blowdown
      (curveLift (· • v) (0 : ℂ)) :=
    (ContMDiff.restrictScalars' ℝ (contMDiff_blowdown (n := n) 1)).mdifferentiable
      one_ne_zero _
  have hfun : blowdown ∘ curveLift (n := n) (· • v) = fun t : ℂ ↦ t • v := by
    funext s
    simp
  rw [← curveLift_smul_zero hv]
  -- The steps go through the tangent spaces of `ℂ` and of `E`, which are `ℂ` and `E`.
  exact (mfderiv_comp_apply 0 hb' hF t).symm.trans
    ((congrArg (fun g ↦ mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) g 0 t) hfun).trans
      ((mvfderiv_apply_eq_mfderiv_apply _ _ _).symm.trans
        ((TauCeti.mvfderiv_eq_fderiv_apply _ _ _).trans
          (by rw [fderiv_smul_const differentiableAt_id, fderiv_fun_id]; simp))))

end BlowupModel

end SymplecticGeometry

end
