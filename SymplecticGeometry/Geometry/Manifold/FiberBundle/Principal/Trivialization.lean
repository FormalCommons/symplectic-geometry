/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Basic
public import TauCeti.Geometry.Manifold.FiberBundle.Principal.FundamentalVectorField
public import TauCeti.Topology.FiberBundle.Principal.Basic

/-!
# The fibre coordinate of an equivariant trivialization

Let `P` be a smooth principal `G`-bundle with charted total space
`TauCeti.ManifoldTotalSpace G P`, and `e` an equivariant trivialization of `P`
(`Trivialization.IsEquivariant`). Its fibre coordinate `θ x = (e x).2 ∈ G` satisfies
`θ (x • g) = θ x * g` over the base set of `e`. This file records two consequences of this identity
for `θ` differentiable over the base set of `e`, stated for an arbitrary form or for none:

* `Trivialization.mpullback_op_smul_mpullback_snd`: at a point over the base set, the action of
  `g` pulls back `θ^* η` to `θ^* (R_g^* η)`, for every form `η` on `G`, `R_g` being right
  multiplication by `g`;
* `Trivialization.mfderiv_snd_rightFundamentalVectorField`: the derivative of `θ` maps the
  fundamental vector field of `ξ` at `x` to the left-invariant vector field of `ξ` at `θ x`, since
  `θ` maps the orbit of `x` to the left translate of `G` by `θ x`.

They give the local connection forms of `Principal/CircleConnection.lean` and
`Principal/Connection/Existence.lean`, for the angular form of the circle and the Maurer–Cartan
form of `G`.

## References

* S. Kobayashi and K. Nomizu, *Foundations of Differential Geometry*, Vol. I, Interscience, 1963,
  Chapter II, §1 (the local connection forms of a principal bundle over a trivialization).
-/

public section

open Bundle Manifold MulOpposite TauCeti
open scoped Manifold ContDiff Topology

variable {EB HB B : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  {IB : ModelWithCorners ℝ EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  {EG HG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [TopologicalSpace HG] {IG : ModelWithCorners ℝ EG HG} [TopologicalSpace G] [ChartedSpace HG G]
  [Group G] [LieGroup IG ∞ G]
  {P : B → Type*} [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle G P] [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P]
  {e : Trivialization G (π G P)} [e.IsEquivariant]

namespace Trivialization

/-- Let `e` be an equivariant trivialization whose fibre coordinate `θ` is differentiable over its
base set. At a point `x` over the base set, the action of `g` pulls back `θ^* η` to
`θ^* (R_g^* η)`, for every form `η` on `G`, where `R_g` is right multiplication by `g`. -/
theorem mpullback_op_smul_mpullback_snd {F : Type*} [AddCommGroup F] [Module ℝ F]
    [TopologicalSpace F] {k : ℕ} {x : ManifoldTotalSpace G P}
    (hθ : ∀ x : ManifoldTotalSpace G P,
      ((ManifoldTotalSpace.homeomorph G P).symm x).proj ∈ e.baseSet →
        MDifferentiableAt (IB.prod IG) IG (fun x : ManifoldTotalSpace G P ↦
          (e ((ManifoldTotalSpace.homeomorph G P).symm x)).2) x)
    (hx : ((ManifoldTotalSpace.homeomorph G P).symm x).proj ∈ e.baseSet) (g : G)
    (η : RoughForm IG G F k) :
    TauCeti.mpullback (IB.prod IG) (IB.prod IG) (fun y : ManifoldTotalSpace G P ↦ op g • y)
      (TauCeti.mpullback (IB.prod IG) IG (fun x : ManifoldTotalSpace G P ↦
        (e ((ManifoldTotalSpace.homeomorph G P).symm x)).2) η) x =
      TauCeti.mpullback (IB.prod IG) IG (fun x : ManifoldTotalSpace G P ↦
        (e ((ManifoldTotalSpace.homeomorph G P).symm x)).2)
        (TauCeti.mpullback IG IG (fun w : G ↦ w * g) η) x := by
  set θ := fun x : ManifoldTotalSpace G P ↦ (e ((ManifoldTotalSpace.homeomorph G P).symm x)).2
  have hS := e.open_baseSet.preimage
    ((FiberBundle.continuous_proj G P).comp (ManifoldTotalSpace.homeomorph G P).symm.continuous)
  have hgx : ((ManifoldTotalSpace.homeomorph G P).symm (op g • x)).proj ∈ e.baseSet := by
    simpa [ManifoldTotalSpace.homeomorph_symm_smul] using hx
  have hsmul : MDifferentiableAt (IB.prod IG) (IB.prod IG)
      (fun y : ManifoldTotalSpace G P ↦ op g • y) x :=
    (contMDiff_const_smul (I := IB.prod IG) (n := 1) (op g) x).mdifferentiableAt one_ne_zero
  have hmul : MDifferentiableAt IG IG (fun w : G ↦ w * g) (θ x) :=
    (contMDiff_mul_right (I := IG) (n := 1) (a := g) _).mdifferentiableAt one_ne_zero
  -- Near `x`, the fibre coordinate of `y • g` is that of `y` times `g`.
  have heq : θ ∘ (fun y ↦ op g • y) =ᶠ[𝓝 x] (fun w : G ↦ w * g) ∘ θ := by
    filter_upwards [hS.mem_nhds hx] with y hy
    simp only [Function.comp_apply, θ, ManifoldTotalSpace.homeomorph_symm_smul]
    exact e.snd_apply_smul hy _ g
  rw [← mpullback_comp_at hsmul (hθ _ hgx), heq.mpullback_eq, mpullback_comp_at (hθ _ hx) hmul]

/-- Let `e` be an equivariant trivialization, and `x` a point over its base set at which the fibre
coordinate `θ` of `e` is differentiable. The derivative of `θ` at `x` maps the fundamental vector
field of `ξ` to the left-invariant vector field of `ξ` at `θ x`. -/
theorem mfderiv_snd_rightFundamentalVectorField {x : ManifoldTotalSpace G P}
    (hx : ((ManifoldTotalSpace.homeomorph G P).symm x).proj ∈ e.baseSet)
    (hθ : MDifferentiableAt (IB.prod IG) IG (fun x : ManifoldTotalSpace G P ↦
      (e ((ManifoldTotalSpace.homeomorph G P).symm x)).2) x)
    (ξ : GroupLieAlgebra IG G) :
    mfderiv (IB.prod IG) IG (fun x : ManifoldTotalSpace G P ↦
        (e ((ManifoldTotalSpace.homeomorph G P).symm x)).2) x
      (rightFundamentalVectorField (IB.prod IG) ξ x) =
      mulInvariantVectorField ξ ((e ((ManifoldTotalSpace.homeomorph G P).symm x)).2) := by
  set θ := fun x : ManifoldTotalSpace G P ↦ (e ((ManifoldTotalSpace.homeomorph G P).symm x)).2
  have horb := PrincipalBundle.mdifferentiableAt_orbit (IB := IB) (IG := IG) (n := ∞)
    (by simp) x 1
  have hθx : MDifferentiableAt (IB.prod IG) IG θ (op (1 : G) • x) := by
    rw [op_one, one_smul]
    exact hθ
  -- Along the orbit of `x`, the fibre coordinate is left multiplication by `θ x`.
  have hcomp : θ ∘ (fun g : G ↦ op g • x) = fun g ↦ θ x * g :=
    funext fun g ↦ by
      simp only [Function.comp_apply, θ, ManifoldTotalSpace.homeomorph_symm_smul]
      exact e.snd_apply_smul hx _ g
  rw [GroupLieAlgebra.mulInvariantVectorField_apply, rightFundamentalVectorField_apply, ← hcomp,
    mfderiv_comp_of_eq hθx horb rfl, op_one, one_smul]
  -- `ContinuousLinearMap.comp_apply` does not rewrite here: the inner derivative lands in the
  -- tangent space at `op 1 • x`, which is `x` only after `one_smul`.
  rfl

end Trivialization

end
