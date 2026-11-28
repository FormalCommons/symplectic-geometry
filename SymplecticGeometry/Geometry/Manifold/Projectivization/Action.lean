/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Projectivization.Hopf
public import TauCeti.Geometry.Lie.FundamentalVectorField
import SymplecticGeometry.Geometry.Manifold.ContMDiff.RestrictScalars
import SymplecticGeometry.Geometry.Manifold.ContMDiff.Opens

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
* `Projectivization.instContMDiffSMulSubgroup`: the same for the action of a subgroup of `G`,
  which goes through `G`.
* `Projectivization.instContMDiffConstSMulReal`: each `g` acts by a real-`C^r` map, with no
  assumption on how the action depends on `g`: Tau Ceti's `ContMDiffConstSMul.restrictScalars`
  applied to its `Projectivization.instContMDiffConstSMul` over `𝕜`.
* `Projectivization.fundamentalVectorField_mk`: the fundamental vector field of `ξ` at `[y]` is
  the image under the differential of `mkNonzero` at `y` of the fundamental vector field of `ξ`
  for the linear action at `y`. Both the inclusion of the punctured space and `mkNonzero` are
  equivariant (`mkNonzero_smul`), so Tau Ceti's `TauCeti.mfderiv_fundamentalVectorField_of_map_smul`
  applies to each.
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
  obtain ⟨F', hF', hFF'⟩ :=
    hF.exists_subtypeVal_comp_eventuallyEq (mem_puncturedSpace.2 hf.self_of_nhds.1)
  refine ((contMDiff_mkNonzero 𝕜 n r).contMDiffAt.comp x hF').congr_of_eventuallyEq ?_
  filter_upwards [hf, hFF'] with y ⟨hy, hfy⟩ hy'
  rw [comp_apply] at hy'
  simp only [comp_apply, mkNonzero_apply, hfy, hy']

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

/-- A subgroup `K` of `G` whose linear action on `𝕜ⁿ⁺¹` is `C^r` acts on
`ℙ 𝕜 (Fin (n + 1) → 𝕜)` by a `C^r` action. The action of `K` on `ℙ 𝕜 (Fin (n + 1) → 𝕜)` that
instance search finds goes through `G`, so `Projectivization.instContMDiffSMul` does not apply to
it as it stands. -/
instance instContMDiffSMulSubgroup {K : Subgroup G} [TopologicalSpace K] [ChartedSpace H K]
    [ContMDiffSMul I 𝓘(ℝ, Fin (n + 1) → 𝕜) r K (Fin (n + 1) → 𝕜)] :
    ContMDiffSMul I 𝓘(ℝ, Fin n → 𝕜) r K (ℙ 𝕜 (Fin (n + 1) → 𝕜)) :=
  instContMDiffSMul

/-- A group acting `𝕜`-linearly on `𝕜ⁿ⁺¹` acts on `ℙ 𝕜 (Fin (n + 1) → 𝕜)` by maps that are `C^r`
for the underlying real manifold structure, since they are `C^r` over `𝕜`
(`Projectivization.instContMDiffConstSMul`, `ContMDiffConstSMul.restrictScalars`). -/
instance instContMDiffConstSMulReal :
    ContMDiffConstSMul 𝓘(ℝ, Fin n → 𝕜) r G (ℙ 𝕜 (Fin (n + 1) → 𝕜)) :=
  ContMDiffConstSMul.restrictScalars ℝ (𝕜' := 𝕜) inferInstance

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
  have hval : (Subtype.val ∘ fun g : G ↦ g • y') = fun g : G ↦ g • y :=
    funext fun g ↦ puncturedSpace.coe_smul g y'
  have horbit : MDifferentiableAt I 𝓘(ℝ, Fin (n + 1) → 𝕜) (fun g : G ↦ g • y') 1 :=
    Manifold.mdifferentiableAt_subtype_val_comp_iff.1 (hval ▸ h)
  -- The inclusion of the punctured space is equivariant, and its differential fixes every
  -- tangent vector, so it identifies the two fundamental vector fields of `ξ` at `y`.
  have hP : fundamentalVectorField 𝓘(ℝ, Fin (n + 1) → 𝕜) ξ y' =
      fundamentalVectorField 𝓘(ℝ, Fin (n + 1) → 𝕜) ξ y :=
    (Manifold.mfderiv_subtype_val_apply y' _).symm.trans
      (mfderiv_fundamentalVectorField_of_map_smul
        (contMDiff_subtypeVal.mdifferentiableAt one_ne_zero) horbit
        (fun g ↦ puncturedSpace.coe_smul g y') ξ)
  rw [← hP, mfderiv_fundamentalVectorField_of_map_smul
    ((contMDiff_mkNonzero 𝕜 n 1).mdifferentiableAt one_ne_zero) horbit
    (fun g ↦ mkNonzero_smul g y') ξ, mkNonzero_apply]

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
