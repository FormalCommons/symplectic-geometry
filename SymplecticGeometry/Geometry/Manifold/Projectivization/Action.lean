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
normed field that is a normed `ℝ`-algebra). Mathlib then lets `G` act on
`ℙ 𝕜 V` by `g • [v] = [g • v]` (`Projectivization.instMulAction`, `Projectivization.smul_mk`).
This file studies that action jointly in `g` and the point, when `G` is a manifold over `ℝ` and
`ℙ 𝕜 V` carries its underlying real manifold structure, and computes its infinitesimal
generators.

* `Projectivization.contMDiffAt_of_eventually_eq_mk_restrictScalars`: a map into `ℙ 𝕜 V` that is
  given near `x` by nonzero homogeneous coordinates, real-`C^r` at `x`, is real-`C^r` at `x`, for
  a source that is a real manifold. It factors through the projection `mkNonzero` from the
  nonzero vectors (`contMDiff_mkNonzero`). Tau Ceti's
  `Projectivization.contMDiffAt_of_eventually_eq_mk` is the version over `𝕜`.
* `Projectivization.instContMDiffSMul`: if `(g, v) ↦ g • v` is `C^r` on `G × V`, then
  `(g, x) ↦ g • x` is `C^r` on `G × ℙ 𝕜 V`. Near `x₀` the action is `(g, x) ↦ [g • L x]`, for the
  homogeneous coordinates `L` of the identity that Tau Ceti's
  `Projectivization.exists_contMDiffAt_eventually_eq_mk` gives.
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

/-- A map to projective space that near `x` sends `y` to the line through `F y`, for nonzero
homogeneous coordinates `F` that are `C^r` at `x` over `ℝ`, is `C^r` at `x` for the underlying
real manifold structure. This is the form of Tau Ceti's
`Projectivization.contMDiffAt_of_eventually_eq_mk` for a source that is a manifold over `ℝ`. -/
theorem contMDiffAt_of_eventually_eq_mk_restrictScalars {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] {f : M → ℙ 𝕜 (Fin (n + 1) → 𝕜)} {F : M → Fin (n + 1) → 𝕜} {x : M}
    (hF : ContMDiffAt I 𝓘(ℝ, Fin (n + 1) → 𝕜) r F x)
    (hf : ∀ᶠ y in 𝓝 x, ∃ hy : F y ≠ 0, f y = mk 𝕜 (F y) hy) :
    ContMDiffAt I 𝓘(ℝ, Fin n → 𝕜) r f x := by
  classical
  have hx : F x ≠ 0 := hf.self_of_nhds.1
  -- `F` read in the punctured space, with the value `F x` where `F` vanishes.
  set F' : M → puncturedSpace (Fin (n + 1) → 𝕜) := fun y ↦
    if hy : F y = 0 then ⟨F x, mem_puncturedSpace.2 hx⟩ else ⟨F y, mem_puncturedSpace.2 hy⟩
  have hF' : ContMDiffAt I 𝓘(ℝ, Fin (n + 1) → 𝕜) r F' x := by
    refine (TauCeti.ContMDiffAt.subtypeVal_comp_iff _ F' x).1 (hF.congr_of_eventuallyEq ?_)
    filter_upwards [hf] with y ⟨hy, _⟩
    simp [F', hy]
  refine ((contMDiff_mkNonzero 𝕜 n r).contMDiffAt.comp x hF').congr_of_eventuallyEq ?_
  filter_upwards [hf] with y ⟨hy, hfy⟩
  simp [F', hy, hfy, mkNonzero_apply]

/-- **Joint smoothness of a linear action on projective space.** If a group acts `𝕜`-linearly
on `𝕜ⁿ⁺¹` and the action `(g, v) ↦ g • v` is `C^r`, then the induced action
`(g, [v]) ↦ [g • v]` on `ℙ 𝕜 (Fin (n + 1) → 𝕜)` is `C^r` for the underlying real manifold
structure. -/
instance instContMDiffSMul [ContMDiffSMul I 𝓘(ℝ, Fin (n + 1) → 𝕜) r G (Fin (n + 1) → 𝕜)] :
    ContMDiffSMul I 𝓘(ℝ, Fin n → 𝕜) r G (ℙ 𝕜 (Fin (n + 1) → 𝕜)) where
  contMDiff_smul := by
    rintro ⟨g₀, x₀⟩
    -- Homogeneous coordinates of the identity near `x₀`, real-smooth at `x₀`.
    obtain ⟨L, hL, hLx⟩ :=
      exists_contMDiffAt_eventually_eq_mk (contMDiffAt_id (I := 𝓘(𝕜, Fin n → 𝕜)) (x := x₀) (n := r))
    refine contMDiffAt_of_eventually_eq_mk_restrictScalars (F := fun p ↦ p.1 • L p.2)
      ((ContMDiffSMul.contMDiff_smul (I := I) (I' := 𝓘(ℝ, Fin (n + 1) → 𝕜))).contMDiffAt.comp
        (g₀, x₀) (contMDiffAt_fst.prodMk ((hL.restrictScalars' ℝ).comp (g₀, x₀) contMDiffAt_snd)))
      ?_
    filter_upwards [continuousAt_snd.preimage_mem_nhds hLx] with p ⟨hp, hpx⟩
    refine ⟨(smul_ne_zero_iff_ne p.1).2 hp, ?_⟩
    rw [id] at hpx
    conv_lhs => rw [hpx]
    exact smul_mk p.1 hp

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
