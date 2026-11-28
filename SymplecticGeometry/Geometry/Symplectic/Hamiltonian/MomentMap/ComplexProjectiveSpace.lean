/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap.ComplexProjectiveSpace
public import SymplecticGeometry.Geometry.Manifold.Projectivization.Hopf
import TauCeti.Geometry.Manifold.Instances.ComplexProjectiveSpace.Hopf
import TauCeti.Geometry.Manifold.Instances.Sphere.SkewHermitian
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# The generators of the unitary action on `ℙ ℂ (Fin (n + 1) → ℂ)`

Tau Ceti's infinitesimal action `TauCeti.ComplexProjectiveSpace.unitaryAction n` of the unitary
Lie algebra `𝔲(n + 1)` on the sphere-quotient model `CPⁿ` is defined by the Hamiltonian vector
fields of the components of its moment map, and Tau Ceti computes it through the Hopf projection
`mk n` of the unit sphere: `X` generates at `[u]` the image of the tangent vector `X u` under the
differential of `mk n` (`TauCeti.ComplexProjectiveSpace.unitaryAction_apply_mk`).

This file reads those generators on the projectivization `ℙ ℂ (Fin (n + 1) → ℂ)` through the
library's diffeomorphism `TauCeti.ComplexProjectiveSpace.diffeomorphProjectivization n`: there
`X` generates at the line `[y]` through a nonzero vector `y` the image of `X y` under the
differential of the projection `Projectivization.mkNonzero ℂ n` at `y`. Informally this is the
derivative at `t = 0` of `t ↦ [exp(t X) y]`, the generator of the linear action of the unitary
group; the statement itself uses no group action.

## Main results

* `TauCeti.ComplexProjectiveSpace.mfderiv_diffeomorphProjectivization_unitaryAction`: the
  differential of `diffeomorphProjectivization n` sends the generator of `X` at the preimage of
  `[y]` to the image of `X y` under the differential of `mkNonzero ℂ n` at `y`.

The proof first takes `y = u` on the unit sphere, where the diffeomorphism after `mk n` is
`mkNonzero ℂ n` after the inclusion of the sphere, so that the chain rule applies; a general `y`
is a nonzero multiple of a unit vector, along which `Projectivization.mfderivMk_smul_smul`
transports the result.

## References

* [A. Cannas da Silva, *Lectures on Symplectic Geometry*][CannasdaSilva2001Lectures], Section 27.1
  (the unitary action on complex projective space).
-/

public section

open Metric Matrix Projectivization TauCeti
open scoped Manifold LinearAlgebra.Projectivization

namespace TauCeti.ComplexProjectiveSpace

variable {n : ℕ}

/-- A unit vector of `EuclideanSpace ℂ (Fin (n + 1))`, read as a nonzero vector of `ℂⁿ⁺¹`. -/
private def sphereToPunctured (u : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) :
    puncturedSpace (Fin (n + 1) → ℂ) :=
  ⟨WithLp.ofLp (u : EuclideanSpace ℂ (Fin (n + 1))), mem_puncturedSpace.2
    ((WithLp.ofLp_eq_zero _).not.2 (ne_zero_of_mem_sphere one_ne_zero u))⟩

/-- The case of a unit vector: the generator of `X` at `mk n u` is sent to the image of `X u`
under the derivative of the projection `w ↦ [w]` at `u`. -/
private theorem mfderiv_diffeomorphProjectivization_unitaryAction_mk
    (X : unitaryLieAlgebra (Fin (n + 1))) (u : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) :
    mfderiv 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin n → ℂ) (diffeomorphProjectivization n) (mk n u)
        (unitaryAction n X (mk n u)) =
      mfderivMk (WithLp.ofLp (u : EuclideanSpace ℂ (Fin (n + 1))))
        ((X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) *ᵥ
          WithLp.ofLp (u : EuclideanSpace ℂ (Fin (n + 1)))) := by
  obtain ⟨v, hv⟩ := exists_mvfderiv_coe_sphere_eq_toEuclideanCLM_of_conjTranspose_eq_neg
    (n := 2 * n + 1) (conjTranspose_coe_unitaryLieAlgebra X) u
  have hcomp : diffeomorphProjectivization n ∘ mk n = mkNonzero ℂ n ∘ sphereToPunctured :=
    funext fun u ↦
      (diffeomorphProjectivization_mk n u).trans (mkNonzero_apply (sphereToPunctured u)).symm
  have hι : MDifferentiableAt (𝓡 (2 * n + 1)) 𝓘(ℝ, Fin (n + 1) → ℂ) sphereToPunctured u := by
    refine ((TauCeti.ContMDiff.subtypeVal_comp_iff _ _).1 ?_ u).mdifferentiableAt
      (n := 1) one_ne_zero
    exact ((PiLp.continuousLinearEquiv 2 ℝ fun _ : Fin (n + 1) ↦ ℂ) :
      EuclideanSpace ℂ (Fin (n + 1)) →L[ℝ] Fin (n + 1) → ℂ).contMDiff.comp contMDiff_coe_sphere
  rw [unitaryAction_apply_mk X u hv]
  refine (mfderiv_comp_apply u ((diffeomorphProjectivization n).mdifferentiable (by simp) _)
    ((contMDiff_mk 1 u).mdifferentiableAt one_ne_zero) v).symm.trans ?_
  rw [hcomp]
  refine (mfderiv_comp_apply u
    ((contMDiff_mkNonzero ℂ n 1 _).mdifferentiableAt one_ne_zero) hι v).trans ?_
  refine (mfderiv_mkNonzero_apply _ _).trans (congrArg _ ?_)
  rw [← TauCeti.Manifold.mfderiv_subtype_val_comp_apply, ← mvfderiv_apply_eq_mfderiv_apply]
  -- `Subtype.val ∘ sphereToPunctured` is, by definition, `WithLp.ofLp` after the inclusion of
  -- the sphere.
  refine ((PiLp.continuousLinearEquiv 2 ℝ fun _ : Fin (n + 1) ↦ ℂ).mvfderiv_comp_apply
    ((↑) : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1 → EuclideanSpace ℂ (Fin (n + 1))) u
    v).trans ?_
  rw [hv, PiLp.coe_continuousLinearEquiv, ofLp_toEuclideanCLM]

/-- **The generators of the unitary action, read on `ℙ ℂ (Fin (n + 1) → ℂ)`.** For
`X ∈ 𝔲(n + 1)` and a nonzero vector `y` of `ℂⁿ⁺¹`, the differential of the diffeomorphism
`diffeomorphProjectivization n : CPⁿ ≃ ℙ ℂ (Fin (n + 1) → ℂ)` sends the value of the vector field
`unitaryAction n X` at the point corresponding to the line `[y]` to the image of `X y` under the
differential of the projection `mkNonzero ℂ n` at `y`. -/
theorem mfderiv_diffeomorphProjectivization_unitaryAction (X : unitaryLieAlgebra (Fin (n + 1)))
    (y : puncturedSpace (Fin (n + 1) → ℂ)) :
    mfderiv 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin n → ℂ) (diffeomorphProjectivization n)
        ((diffeomorphProjectivization n).symm (mkNonzero ℂ n y))
        (unitaryAction n X ((diffeomorphProjectivization n).symm (mkNonzero ℂ n y))) =
      mfderiv 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin n → ℂ) (mkNonzero ℂ n) y
        ((X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) *ᵥ (y : Fin (n + 1) → ℂ)) := by
  have hy : (y : Fin (n + 1) → ℂ) ≠ 0 := mem_puncturedSpace.1 y.property
  have hy' : WithLp.toLp 2 (y : Fin (n + 1) → ℂ) ≠ 0 := (WithLp.toLp_eq_zero _).not.2 hy
  set r := ‖WithLp.toLp 2 (y : Fin (n + 1) → ℂ)‖
  have hc : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hy')
  -- The unit vector `y / ‖y‖` of `EuclideanSpace ℂ (Fin (n + 1))`.
  let u : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1 :=
    ⟨(r⁻¹ : ℂ) • WithLp.toLp 2 (y : Fin (n + 1) → ℂ),
      mem_sphere_zero_iff_norm.2 (by simpa [r] using norm_smul_inv_norm (𝕜 := ℂ) hy')⟩
  have hu : WithLp.ofLp (u : EuclideanSpace ℂ (Fin (n + 1))) =
      (r⁻¹ : ℂ) • (y : Fin (n + 1) → ℂ) := by
    simp [u]
  have hp : (diffeomorphProjectivization n).symm (mkNonzero ℂ n y) = mk n u := by
    rw [coe_diffeomorphProjectivization_symm, Homeomorph.symm_apply_eq,
      ← coe_diffeomorphProjectivization, diffeomorphProjectivization_mk, mkNonzero_apply,
      mk_eq_mk_iff']
    exact ⟨(r : ℂ), by rw [hu, smul_smul, mul_inv_cancel₀ hc, one_smul]⟩
  rw [hp, mfderiv_diffeomorphProjectivization_unitaryAction_mk, mfderiv_mkNonzero_apply, hu,
    mulVec_smul, mfderivMk_smul_smul hy (inv_ne_zero hc)]

end TauCeti.ComplexProjectiveSpace

end
