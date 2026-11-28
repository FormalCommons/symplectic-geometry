/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.FiberBundle.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Basic
public import TauCeti.Geometry.Manifold.FiberBundle.Principal.FundamentalVectorField
public import TauCeti.Topology.FiberBundle.Principal.Basic

/-!
# The fibre coordinate of an equivariant trivialization

Let `P` be a smooth principal `G`-bundle with charted total space
`TauCeti.ManifoldTotalSpace G P`, and `e` an equivariant trivialization of `P`
(`Trivialization.IsEquivariant`). Its fibre coordinate `θ x = (e x).2 ∈ G`, read on the charted
total space, is `Bundle.Trivialization.manifoldSnd e`, defined for any fibre bundle in
`FiberBundle/Basic.lean`. It satisfies `θ (x • g) = θ x * g` over the base set of `e`
(`Bundle.Trivialization.manifoldSnd_op_smul`). This file records two consequences of this identity
for `θ` differentiable over the base set of `e`, stated for an arbitrary form or for none:

* `Bundle.Trivialization.mpullback_op_smul_mpullback_snd`: at a point over the base set, the
  action of `g` pulls back `θ^* η` to `θ^* (R_g^* η)`, for every form `η` on `G`, `R_g` being
  right multiplication by `g`;
* `Bundle.Trivialization.mfderiv_snd_rightFundamentalVectorField`: the derivative of `θ` maps the
  fundamental vector field of `ξ` at `x` to the left-invariant vector field of `ξ` at `θ x`, since
  `θ` maps the orbit of `x` to the left translate of `G` by `θ x`.

They give the local connection forms of `Principal/CircleConnection.lean`, for the angular form of
the circle and for the trivialization of a local section as well as those of the atlas. For the
trivializations of the atlas, Tau Ceti states the same facts of its fibre coordinate
`TauCeti.ManifoldTotalSpace.fiberCoord` (`TauCeti.PrincipalBundle.fiberCoord_op_smul`,
`TauCeti.PrincipalBundle.mfderiv_fiberCoord_rightFundamentalVectorField`).

## References

* S. Kobayashi and K. Nomizu, *Foundations of Differential Geometry*, Vol. I, Interscience, 1963,
  Chapter II, §1 (the local connection forms of a principal bundle over a trivialization).
-/

public section

open Bundle Manifold MulOpposite TauCeti
open scoped Manifold ContDiff Topology

namespace Bundle.Trivialization

variable {EB HB B : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  {IB : ModelWithCorners ℝ EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  {EG HG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [TopologicalSpace HG] {IG : ModelWithCorners ℝ EG HG} [TopologicalSpace G] [ChartedSpace HG G]
  [Group G] [LieGroup IG ∞ G]
  {P : B → Type*} [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle G P] [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P]
  (e : Trivialization G (π G P)) [e.IsEquivariant]

omit [∀ b, TopologicalSpace (P b)] [FiberBundle G P] [PrincipalBundle G P] in
/-- Over the base set of an equivariant trivialization `e`, the fibre coordinate of `x • g` is that
of `x` times `g`. -/
theorem manifoldSnd_op_smul {x : ManifoldTotalSpace G P}
    (hx : ((ManifoldTotalSpace.homeomorph G P).symm x).proj ∈ e.baseSet) (g : G) :
    e.manifoldSnd (op g • x) = e.manifoldSnd x * g := by
  rw [manifoldSnd_apply, manifoldSnd_apply, ManifoldTotalSpace.homeomorph_symm_smul]
  exact e.snd_apply_smul hx _ g

/-- Let `e` be an equivariant trivialization whose fibre coordinate `θ` is differentiable over its
base set. At a point `x` over the base set, the action of `g` pulls back `θ^* η` to
`θ^* (R_g^* η)`, for every form `η` on `G`, where `R_g` is right multiplication by `g`. -/
theorem mpullback_op_smul_mpullback_snd {F : Type*} [AddCommGroup F] [Module ℝ F]
    [TopologicalSpace F] {k : ℕ} {x : ManifoldTotalSpace G P}
    (hθ : ∀ x : ManifoldTotalSpace G P,
      ((ManifoldTotalSpace.homeomorph G P).symm x).proj ∈ e.baseSet →
        MDifferentiableAt (IB.prod IG) IG e.manifoldSnd x)
    (hx : ((ManifoldTotalSpace.homeomorph G P).symm x).proj ∈ e.baseSet) (g : G)
    (η : RoughForm IG G F k) :
    TauCeti.mpullback (IB.prod IG) (IB.prod IG) (fun y : ManifoldTotalSpace G P ↦ op g • y)
      (TauCeti.mpullback (IB.prod IG) IG e.manifoldSnd η) x =
      TauCeti.mpullback (IB.prod IG) IG e.manifoldSnd
        (TauCeti.mpullback IG IG (fun w : G ↦ w * g) η) x := by
  have hS := e.open_baseSet.preimage
    ((FiberBundle.continuous_proj G P).comp (ManifoldTotalSpace.homeomorph G P).symm.continuous)
  have hgx : ((ManifoldTotalSpace.homeomorph G P).symm (op g • x)).proj ∈ e.baseSet := by
    simpa [ManifoldTotalSpace.homeomorph_symm_smul] using hx
  have hsmul : MDifferentiableAt (IB.prod IG) (IB.prod IG)
      (fun y : ManifoldTotalSpace G P ↦ op g • y) x :=
    (contMDiff_const_smul (I := IB.prod IG) (n := 1) (op g) x).mdifferentiableAt one_ne_zero
  have hmul : MDifferentiableAt IG IG (fun w : G ↦ w * g) (e.manifoldSnd x) :=
    (contMDiff_mul_right (I := IG) (n := 1) (a := g) _).mdifferentiableAt one_ne_zero
  -- Near `x`, the fibre coordinate of `y • g` is that of `y` times `g`.
  have heq : e.manifoldSnd ∘ (fun y ↦ op g • y) =ᶠ[𝓝 x]
      (fun w : G ↦ w * g) ∘ e.manifoldSnd := by
    filter_upwards [hS.mem_nhds hx] with y hy
    exact e.manifoldSnd_op_smul hy g
  rw [← mpullback_comp_at hsmul (hθ _ hgx), heq.mpullback_eq, mpullback_comp_at (hθ _ hx) hmul]

/-- Let `e` be an equivariant trivialization, and `x` a point over its base set at which the fibre
coordinate `θ` of `e` is differentiable. The derivative of `θ` at `x` maps the fundamental vector
field of `ξ` to the left-invariant vector field of `ξ` at `θ x`. -/
theorem mfderiv_snd_rightFundamentalVectorField {x : ManifoldTotalSpace G P}
    (hx : ((ManifoldTotalSpace.homeomorph G P).symm x).proj ∈ e.baseSet)
    (hθ : MDifferentiableAt (IB.prod IG) IG e.manifoldSnd x)
    (ξ : GroupLieAlgebra IG G) :
    mfderiv (IB.prod IG) IG e.manifoldSnd x (rightFundamentalVectorField (IB.prod IG) ξ x) =
      mulInvariantVectorField ξ (e.manifoldSnd x) :=
  (mfderiv_rightFundamentalVectorField_of_map_op_smul hθ
    (PrincipalBundle.mdifferentiableAt_orbit (n := ∞) (by simp) x 1)
    (fun g ↦ e.manifoldSnd_op_smul hx g) ξ).trans
    (congrFun (rightFundamentalVectorField_eq_mulInvariantVectorField ξ) _)

end Bundle.Trivialization

end
