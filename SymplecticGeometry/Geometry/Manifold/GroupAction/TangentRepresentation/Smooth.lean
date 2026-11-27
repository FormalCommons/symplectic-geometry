/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Lie.FundamentalVectorField.Isotropy
public import TauCeti.Geometry.Lie.Subgroup.Differential
public import TauCeti.Geometry.Manifold.GroupAction.TangentRepresentation
public import SymplecticGeometry.Geometry.Lie.Subgroup.IdentityComponent

import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import TauCeti.Geometry.Lie.Exponential.Derivative.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic

/-!
# Smoothness of the tangent representation of a stabilizer

Let a Lie group `G` act smoothly on a manifold `M`, let `x : M`, and give the stabilizer
`G_x` the structure of an embedded Lie subgroup. Tau Ceti's `TauCeti.tangentRepresentation` lets
`h ∈ G_x` act on `T_x M` by the derivative of `h • ·` at `x`. This file shows that this
representation is smooth, and computes its derivative at `1`: an element `ζ` of the tangent space
at `1` of `G_x` acts by the linearized isotropy action `TauCeti.isotropyLinearization` of its
image `ξ` in the isotropy algebra `𝔤_x` under the differential of the inclusion `G_x → G`.

## Main results

* `TauCeti.contMDiff_tangentRepresentation`: `h ↦ d(h • ·)_x` is smooth on `G_x`.
* `TauCeti.contMDiff_tangentRepresentation_apply`: `(h, v) ↦ d(h • ·)_x v` is smooth on
  `G_x × T_x M`.
* `TauCeti.mfderiv_tangentRepresentation_apply_one`: the derivative at `1` of `h ↦ d(h • ·)_x v`
  in the direction `ζ` is `A_ξ v`, where `ξ ∈ 𝔤_x` is the image of `ζ` and `A_ξ` its linearized
  isotropy action.

The proof of smoothness adapts that of Tau Ceti's `TauCeti.continuous_tangentRepresentation`,
with Mathlib's `ContMDiffAt.mfderiv` for the smooth dependence of a derivative on a parameter.
The derivative is computed along the exponential lines of `G_x`, which the inclusion carries to
those of `G` (`TauCeti.Lie.EmbeddedLieSubgroupData.coe_mulInvariantExp`), where Tau Ceti's
`TauCeti.hasDerivAt_mfderiv_mulInvariantExp_smul_smul_isotropyLinearization` applies.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Chapters 20
  and 21.
-/

public section

noncomputable section

open MulAction
open scoped ContDiff Manifold

namespace TauCeti

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M]
  [MulAction G M] [ContMDiffSMul I I' ∞ G M] {x : M}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Smoothness of the tangent representation.** For a smooth action of `G` on `M` and an
embedded Lie subgroup structure on the stabilizer `G_x`, the map `h ↦ d(h • ·)_x` from `G_x` to
the operators on `T_x M` is smooth. -/
theorem contMDiff_tangentRepresentation [IsManifold I ∞ G]
    (d : Lie.EmbeddedLieSubgroupData I (stabilizer G x) F)
    (hd : ∀ g ∈ stabilizer G x, MDifferentiableAt I' I' (fun y : M ↦ g • y) x) :
    let _ := d.chartedSpace
    -- `T_x M` is `E'` by definition, which `show` exposes to the model `𝓘(ℝ, E' →L[ℝ] E')`.
    ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, E' →L[ℝ] E') ∞
      fun h : stabilizer G x ↦ show E' →L[ℝ] E' from tangentRepresentation hd h := by
  let _ := d.chartedSpace
  dsimp only
  intro h₀
  -- The derivative of `g • ·` at `x`, read in the tangent coordinates of the base points `x`
  -- and `g • x`, is smooth in `g` at `h₀`.
  have hf : ContMDiffAt (I.prod I') I' ∞ (Function.uncurry fun (g : G) (y : M) ↦ g • y)
      ((h₀ : G), x) :=
    (ContMDiffSMul.contMDiff_smul (I := I) (I' := I') (n := ∞) (G := G) (M := M)).contMDiffAt
  have h := ContMDiffAt.mfderiv (fun (g : G) (y : M) ↦ g • y) (fun _ ↦ x) hf
    (contMDiffAt_const (n := ∞)) (by simp)
  -- On the stabilizer both base points are `x`, so the coordinate changes are the identity.
  have hcomp : inTangentCoordinates I' I' (fun _ : G ↦ x) (fun g : G ↦ g • x)
      (fun g : G ↦ mfderiv I' I' (fun y : M ↦ g • y) x) (h₀ : G) ∘ Subtype.val =
        fun h : stabilizer G x ↦ show E' →L[ℝ] E' from tangentRepresentation hd h :=
    funext fun g ↦ (Manifold.inTangentCoordinates_eq_self_of_eq (x₀ := (h₀ : G)) (x := g) _ _ _
      rfl (g.property.trans h₀.property.symm)).trans (tangentRepresentation_apply hd g).symm
  rw [← hcomp]
  exact h.comp h₀ (d.contMDiff_subtypeVal h₀)

/-- **Joint smoothness of the tangent representation.** For a smooth action of `G` on `M` and an
embedded Lie subgroup structure on the stabilizer `G_x`, the map `(h, v) ↦ d(h • ·)_x v` on
`G_x × T_x M` is smooth. -/
theorem contMDiff_tangentRepresentation_apply [IsManifold I ∞ G]
    (d : Lie.EmbeddedLieSubgroupData I (stabilizer G x) F)
    (hd : ∀ g ∈ stabilizer G x, MDifferentiableAt I' I' (fun y : M ↦ g • y) x) :
    let _ := d.chartedSpace
    -- `T_x M` is `E'` by definition, which `show` exposes to the model `𝓘(ℝ, E')`.
    ContMDiff (𝓘(ℝ, F).prod 𝓘(ℝ, E')) 𝓘(ℝ, E') ∞
      fun p : stabilizer G x × E' ↦ show E' from tangentRepresentation hd p.1 p.2 := by
  let _ := d.chartedSpace
  exact ((contMDiff_tangentRepresentation d hd).comp contMDiff_fst).clm_apply contMDiff_snd

variable [FiniteDimensional ℝ E] [LieGroup I ∞ G] [T2Space G] [FiniteDimensional ℝ E']
  [I'.Boundaryless] [T2Space M] [FiniteDimensional ℝ F]

/-- **The derivative at `1` of the tangent representation.** For a smooth action of `G` on `M`
and an embedded Lie subgroup structure on the stabilizer `G_x`, the derivative at `1` of
`h ↦ d(h • ·)_x v` in the direction `ζ` is `A_ξ v`, where `ξ ∈ 𝔤_x` is the image of `ζ` under the
differential at `1` of the inclusion `G_x → G` and `A_ξ` is the linearized isotropy action
`TauCeti.isotropyLinearization`. -/
theorem mfderiv_tangentRepresentation_apply_one
    (d : Lie.EmbeddedLieSubgroupData I (stabilizer G x) F)
    (hd : ∀ g ∈ stabilizer G x, MDifferentiableAt I' I' (fun y : M ↦ g • y) x) :
    let _ := d.chartedSpace
    ∀ (ζ : GroupLieAlgebra 𝓘(ℝ, F) (stabilizer G x)) (v : E'),
      mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E')
          (fun h : stabilizer G x ↦ show E' from tangentRepresentation hd h v) 1 ζ =
        isotropyLinearization I' x
          ⟨(stabilizer G x).subtype.groupLieAlgebraMap 𝓘(ℝ, F) I ζ,
            d.groupLieAlgebraMap_subtype_mem_isotropy (I' := I') ζ⟩ v := by
  let _ := d.chartedSpace
  let _ := d.lieGroup
  dsimp only
  intro ζ v
  -- The inclusion carries the exponential line of `ζ` in `G_x` to that of `ξ` in `G`.
  have hexp (t : ℝ) : ((mulInvariantExp (t • ζ) : stabilizer G x) : G) =
      mulInvariantExp (t • (stabilizer G x).subtype.groupLieAlgebraMap 𝓘(ℝ, F) I ζ) := by
    rw [d.coe_mulInvariantExp, map_smul]
  have hφ : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, E')
      (fun h : stabilizer G x ↦ show E' from tangentRepresentation hd h v) 1 :=
    (((contMDiff_tangentRepresentation_apply d hd).comp
      (contMDiff_id.prodMk contMDiff_const)).mdifferentiable (by simp)) 1
  refine (hφ.hasMFDerivAt.hasDerivAt_comp_mulInvariantExp_smul_zero ζ).unique ?_
  have hfun : (fun t : ℝ ↦ show E' from tangentRepresentation hd (mulInvariantExp (t • ζ)) v) =
      fun t : ℝ ↦ show E' from mfderiv I' I' (fun y : M ↦ mulInvariantExp
        (t • (stabilizer G x).subtype.groupLieAlgebraMap 𝓘(ℝ, F) I ζ) • y) x v :=
    funext fun t ↦ (congrArg (fun L ↦ L v) (tangentRepresentation_apply hd _)).trans
      (congrArg (fun g : G ↦ show E' from mfderiv I' I' (g • ·) x v) (hexp t))
  rw [hfun]
  exact hasDerivAt_mfderiv_mulInvariantExp_smul_smul_apply
    ⟨_, d.groupLieAlgebraMap_subtype_mem_isotropy (I' := I') ζ⟩ v

end TauCeti
