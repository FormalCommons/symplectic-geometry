/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Projectivization.Hopf
public import TauCeti.Geometry.Lie.FundamentalVectorField
import SymplecticGeometry.Geometry.Manifold.ContMDiff.RestrictScalars
import TauCeti.Geometry.Manifold.ContMDiff.Subtype

/-!
# Smooth linear actions on projective space

Let a group `G` act `𝕜`-linearly on `V = 𝕜ⁿ⁺¹`, for `𝕜 = ℝ` or `ℂ` (more generally a nontrivially
normed field that is a finite-dimensional normed `ℝ`-algebra). Mathlib then lets `G` act on
`ℙ 𝕜 V` by `g • [v] = [g • v]` (`Projectivization.instMulAction`, `Projectivization.smul_mk`).
This file studies that action jointly in `g` and the point, when `G` is a manifold over `ℝ` and
`ℙ 𝕜 V` carries its underlying real manifold structure, and computes its infinitesimal
generators.

* `Projectivization.instContMDiffSMul`: if `(g, v) ↦ g • v` is `C^r` on `G × V`, then
  `(g, x) ↦ g • x` is `C^r` on `G × ℙ 𝕜 V`. On the affine open of a coordinate `j`, the action is
  `(g, x) ↦ [g • L x]`, where `L x` is the lift of `x` normalized by `1` in coordinate `j` (the
  lift of Tau Ceti's `Projectivization.exists_contMDiffAt_eventually_eq_mk`), and the projection
  `mkNonzero` from the nonzero vectors is smooth (`contMDiff_mkNonzero`).
* `Projectivization.fundamentalVectorField_mk`: the fundamental vector field of `ξ` at `[y]` is
  the image under the differential of `mkNonzero` at `y` of the fundamental vector field of `ξ`
  for the linear action at `y`, by the chain rule along the factorization of the orbit map of
  `[y]` through that of `y`.
* `Projectivization.fundamentalVectorField_mk_of_smul_eq`: for an action through
  `ρ : G → (V →L[ℝ] V)`, differentiable at `1`, that vector at `y` is `dρ₁ ξ y`, by Tau Ceti's
  `TauCeti.fundamentalVectorField_eq_mfderiv_apply`.

A representation `ρ : G →* Matrix.GeneralLinearGroup (Fin (n + 1)) ℂ` gives such a linear action,
`DistribMulAction.compHom _ ρ`, which commutes with the scalars by `SMul.comp.smulCommClass ρ`,
and so an action of `G` on `ℙ ℂ (Fin (n + 1) → ℂ)`.

## References

* [P. Griffiths, J. Harris, *Principles of Algebraic Geometry*][GriffithsHarris1978], Chapter 0,
  §1.
-/

public section

open Function Manifold TauCeti
open scoped Manifold ContDiff LinearAlgebra.Projectivization Topology

namespace Projectivization

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜] {n : ℕ}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [DistribMulAction G (Fin (n + 1) → 𝕜)] [SMulCommClass G 𝕜 (Fin (n + 1) → 𝕜)]

variable {r : ℕ∞ω}

/-- **Joint smoothness of a linear action on projective space.** If a group acts `𝕜`-linearly
on `𝕜ⁿ⁺¹` and the action `(g, v) ↦ g • v` is `C^r`, then the induced action
`(g, [v]) ↦ [g • v]` on `ℙ 𝕜 (Fin (n + 1) → 𝕜)` is `C^r` for the underlying real manifold
structure. -/
instance instContMDiffSMul [FiniteDimensional ℝ 𝕜]
    [ContMDiffSMul I 𝓘(ℝ, Fin (n + 1) → 𝕜) r G (Fin (n + 1) → 𝕜)] :
    ContMDiffSMul I 𝓘(ℝ, Fin n → 𝕜) r G (ℙ 𝕜 (Fin (n + 1) → 𝕜)) where
  contMDiff_smul := by
    rintro ⟨g₀, x₀⟩
    obtain ⟨j, hj⟩ := exists_mem_affineOpen x₀
    have hU : affineOpen j ∈ 𝓝 x₀ := (isOpen_affineOpen j).mem_nhds hj
    -- The affine lift of the chart of `j`, a real-smooth section of the projection near `x₀`.
    set L : ℙ 𝕜 (Fin (n + 1) → 𝕜) → Fin (n + 1) → 𝕜 := fun x ↦
      Fin.insertNth (α := fun _ ↦ 𝕜) j 1 (affineChart j x)
    have hL0 (x) : L x ≠ 0 := Fin.insertNth_one_ne_zero j _
    have hLs : ContMDiffAt 𝓘(ℝ, Fin n → 𝕜) 𝓘(ℝ, Fin (n + 1) → 𝕜) r L x₀ :=
      ((contMDiffOn_insertNth_affineChart j r).restrictScalars' ℝ).contMDiffAt hU
    -- Near `(g₀, x₀)` the action is `(g, x) ↦ [g • L x]`, read in the punctured space.
    set F : G × ℙ 𝕜 (Fin (n + 1) → 𝕜) → puncturedSpace (Fin (n + 1) → 𝕜) := fun p ↦
      ⟨p.1 • L p.2, mem_puncturedSpace.2 ((smul_ne_zero_iff_ne p.1).2 (hL0 p.2))⟩
    have hF : ContMDiffAt (I.prod 𝓘(ℝ, Fin n → 𝕜)) 𝓘(ℝ, Fin (n + 1) → 𝕜) r F (g₀, x₀) :=
      (TauCeti.ContMDiffAt.subtypeVal_comp_iff _ F _).1
        ((ContMDiffSMul.contMDiff_smul (I := I) (I' := 𝓘(ℝ, Fin (n + 1) → 𝕜))).contMDiffAt.comp
          (g₀, x₀) (contMDiffAt_fst.prodMk (hLs.comp (g₀, x₀) contMDiffAt_snd)))
    refine ((contMDiff_mkNonzero 𝕜 n r).contMDiffAt.comp (g₀, x₀) hF).congr_of_eventuallyEq ?_
    have hsnd : ContinuousAt (fun p : G × ℙ 𝕜 (Fin (n + 1) → 𝕜) ↦ p.2) (g₀, x₀) :=
      continuousAt_snd
    filter_upwards [hsnd.preimage_mem_nhds hU] with p hp
    have hx : p.2 = mk 𝕜 (L p.2) (hL0 p.2) :=
      ((affineChart (K := 𝕜) j).left_inv (by rwa [affineChart_source])).symm.trans
        (affineChart_symm_apply j _)
    rw [comp_apply, mkNonzero_apply]
    conv_lhs => rw [hx]
    exact smul_mk p.1 (hL0 p.2)

/-- **Fundamental vector fields of a linear action on projective space.** If a group acts
`𝕜`-linearly on `𝕜ⁿ⁺¹` and the orbit map of `y ≠ 0` is differentiable at `1`, the fundamental
vector field of `ξ` at `[y]` is the image under the differential of the projection `mkNonzero` at
`y` of the fundamental vector field of `ξ` at `y` for the linear action. -/
theorem fundamentalVectorField_mk (ξ : GroupLieAlgebra I G) {y : Fin (n + 1) → 𝕜} (hy : y ≠ 0)
    (h : MDifferentiableAt I 𝓘(ℝ, Fin (n + 1) → 𝕜) (fun g : G ↦ g • y) 1) :
    fundamentalVectorField 𝓘(ℝ, Fin n → 𝕜) ξ (mk 𝕜 y hy) =
      mfderiv 𝓘(ℝ, Fin (n + 1) → 𝕜) 𝓘(ℝ, Fin n → 𝕜) (mkNonzero 𝕜 n)
        ⟨y, mem_puncturedSpace.2 hy⟩ (fundamentalVectorField 𝓘(ℝ, Fin (n + 1) → 𝕜) ξ y) := by
  set y' : puncturedSpace (Fin (n + 1) → 𝕜) := ⟨y, mem_puncturedSpace.2 hy⟩
  -- The orbit map of `[y]` factors through the orbit map `φ` of `y` in the punctured space.
  set φ : G → puncturedSpace (Fin (n + 1) → 𝕜) := fun g ↦
    ⟨g • y, mem_puncturedSpace.2 ((smul_ne_zero_iff_ne g).2 hy)⟩
  have horbit : (fun g : G ↦ g • mk 𝕜 y hy) = mkNonzero 𝕜 n ∘ φ :=
    funext fun g ↦ by rw [comp_apply, mkNonzero_apply]; exact smul_mk g hy
  have hval : (Subtype.val ∘ φ) = fun g : G ↦ g • y := rfl
  have hφ : MDifferentiableAt I 𝓘(ℝ, Fin (n + 1) → 𝕜) φ 1 :=
    Manifold.mdifferentiableAt_subtype_val_comp_iff.1 (hval ▸ h)
  have hφ1 : φ 1 = y' := Subtype.ext (one_smul G y)
  have hval1 : mfderiv I 𝓘(ℝ, Fin (n + 1) → 𝕜) (Subtype.val ∘ φ) 1 ξ =
      mfderiv I 𝓘(ℝ, Fin (n + 1) → 𝕜) φ 1 ξ :=
    (mfderiv_comp_apply 1 (contMDiff_subtypeVal.mdifferentiableAt one_ne_zero) hφ ξ).trans
      (Manifold.mfderiv_subtype_val_apply _ _)
  rw [fundamentalVectorField_apply, fundamentalVectorField_apply, ← hval, horbit]
  exact (mfderiv_comp_apply_of_eq 1 ((contMDiff_mkNonzero 𝕜 n 1).mdifferentiableAt one_ne_zero) hφ
    hφ1 ξ).trans (congrArg (mfderiv 𝓘(ℝ, Fin (n + 1) → 𝕜) 𝓘(ℝ, Fin n → 𝕜) (mkNonzero 𝕜 n) y')
      hval1.symm)

/-- **Fundamental vector fields of a representation on projective space.** If a group acts on
`𝕜ⁿ⁺¹` through `ρ : G → (𝕜ⁿ⁺¹ →L[ℝ] 𝕜ⁿ⁺¹)`, by `𝕜`-linear maps, and `ρ` is differentiable at `1`,
the fundamental vector field of `ξ` at `[y]` is the image of `dρ₁(ξ) y` under the differential of
the projection `mkNonzero` at `y`. -/
theorem fundamentalVectorField_mk_of_smul_eq
    {ρ : G → (Fin (n + 1) → 𝕜) →L[ℝ] Fin (n + 1) → 𝕜} (hρ : ∀ g v, g • v = ρ g v)
    (hd : MDifferentiableAt I 𝓘(ℝ, (Fin (n + 1) → 𝕜) →L[ℝ] Fin (n + 1) → 𝕜) ρ 1)
    (ξ : GroupLieAlgebra I G) {y : Fin (n + 1) → 𝕜} (hy : y ≠ 0) :
    fundamentalVectorField 𝓘(ℝ, Fin n → 𝕜) ξ (mk 𝕜 y hy) =
      mfderiv 𝓘(ℝ, Fin (n + 1) → 𝕜) 𝓘(ℝ, Fin n → 𝕜) (mkNonzero 𝕜 n) ⟨y, mem_puncturedSpace.2 hy⟩
        (tangentSpaceCastModel 𝓘(ℝ, (Fin (n + 1) → 𝕜) →L[ℝ] Fin (n + 1) → 𝕜) (ρ 1)
          (mfderiv I 𝓘(ℝ, (Fin (n + 1) → 𝕜) →L[ℝ] Fin (n + 1) → 𝕜) ρ 1 ξ) y) := by
  have horbit : MDifferentiableAt I 𝓘(ℝ, Fin (n + 1) → 𝕜) (fun g : G ↦ g • y) 1 := by
    simp_rw [hρ]
    exact (ContinuousLinearMap.apply ℝ (Fin (n + 1) → 𝕜) y).mdifferentiableAt.comp 1 hd
  rw [fundamentalVectorField_mk ξ hy horbit, fundamentalVectorField_eq_mfderiv_apply hρ hd]

end Projectivization
