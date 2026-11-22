/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.LieDeriv
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Descent
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import TauCeti.Geometry.Manifold.FiberBundle.Principal.FundamentalVectorField
import TauCeti.Geometry.Lie.Exponential.Derivative.Basic
import TauCeti.Geometry.Manifold.DifferentialForm.Flow

/-!
# Basic forms on smooth principal bundles

Let `P` be a smooth principal `G`-bundle over `B`, with charted total space
`TauCeti.ManifoldTotalSpace G P` and projection `π`. The projection is invariant under the right
action of `G`, so a form pulled back from `B` is invariant. Conversely, a form on the total space
that is invariant under the action and vanishes as soon as one of its arguments is vertical is
basic for `π` (`TauCeti.RoughForm.IsBasic`), hence a pull-back from `B` when Tau Ceti's descent
applies: the points of a fibre are related by the action, through the division map
`TauCeti.PrincipalBundle.division`.

## Main results

* `TauCeti.PrincipalBundle.proj_comp_op_smul`: the projection is invariant under the action.
* `TauCeti.PrincipalBundle.exists_op_smul_eq_of_proj_eq`: two points of one fibre differ by the
  action.
* `TauCeti.PrincipalBundle.mpullback_op_smul_mpullback_proj`: forms pulled back from the base are
  invariant under the action.
* `TauCeti.PrincipalBundle.isBasic_of_mpullback_op_smul`: an invariant form that vanishes on
  vertical vectors is basic for the projection. It is Tau Ceti's
  `TauCeti.RoughForm.isBasic_of_mpullback_eq` for the right translations of a principal bundle.
* `TauCeti.PrincipalBundle.mlieDerivForm_rightFundamentalVectorField_eq_zero`: an invariant form
  has vanishing Lie derivative along every fundamental vector field.

## Implementation notes

The proof of `mlieDerivForm_rightFundamentalVectorField_eq_zero` adapts that of Tau Ceti's
`TauCeti.mlieDerivForm_fundamentalVectorField_eq_zero`, for left actions of a Lie group, to the
right action on a principal bundle: the form is constant along the flow `x ↦ x • exp (t ξ)` of
the fundamental vector field of `ξ`
(`TauCeti.PrincipalBundle.isMIntegralCurve_op_mulInvariantExp_smul`), and its Lie derivative is
the velocity at `0` of its pull-backs along this flow (`TauCeti.hasDerivAt_mpullback_of_eq_id`).

## References

* S. Kobayashi and K. Nomizu, *Foundations of Differential Geometry*, Vol. I, Interscience, 1963,
  Chapter II, §5 (tensorial forms of type `ad` on a principal bundle; basic forms are the
  pull-backs of forms on the base).
-/

public section

noncomputable section

open Bundle Manifold MulOpposite
open scoped Manifold ContDiff

namespace TauCeti.PrincipalBundle

variable {B G : Type*}
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners ℝ EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  {EG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG] {HG : Type*} [TopologicalSpace HG]
  {IG : ModelWithCorners ℝ EG HG} [Group G] [TopologicalSpace G] [ChartedSpace HG G]
  {P : B → Type*} [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle G P] [∀ b, MulAction Gᵐᵒᵖ (P b)]

omit [TopologicalSpace B] [∀ b, TopologicalSpace (P b)] [FiberBundle G P] [TopologicalSpace G] in
/-- The projection of the charted total space of a principal bundle is invariant under the right
action. -/
@[simp]
theorem proj_comp_op_smul (g : G) :
    (fun y : ManifoldTotalSpace G P ↦ ((ManifoldTotalSpace.homeomorph G P).symm y).proj) ∘
      (fun x ↦ op g • x) =
      fun y ↦ ((ManifoldTotalSpace.homeomorph G P).symm y).proj := by
  funext x
  simp [ManifoldTotalSpace.homeomorph_symm_smul]

section Basic

variable [IsManifold IB ∞ B] [ContMDiffMul IG ∞ G] [ContMDiffFiberBundle ∞ G P IB IG]
  [PrincipalBundle G P]

omit [IsManifold IB ∞ B] [ContMDiffMul IG ∞ G] [ContMDiffFiberBundle ∞ G P IB IG] in
/-- Two points of the charted total space of a principal bundle with the same projection differ by
the right action of an element of the structure group. -/
theorem exists_op_smul_eq_of_proj_eq {x y : ManifoldTotalSpace G P}
    (hxy : ((ManifoldTotalSpace.homeomorph G P).symm x).proj =
      ((ManifoldTotalSpace.homeomorph G P).symm y).proj) :
    ∃ g : G, op g • y = x := by
  obtain ⟨⟨b, p⟩, rfl⟩ := (ManifoldTotalSpace.homeomorph G P).surjective x
  obtain ⟨⟨b', q⟩, rfl⟩ := (ManifoldTotalSpace.homeomorph G P).surjective y
  simp only [Homeomorph.symm_apply_apply] at hxy
  subst hxy
  exact ⟨division G q p, by rw [ManifoldTotalSpace.smul_homeomorph, smul_division]⟩

/-- A form pulled back from the base of a smooth principal bundle is invariant under the right
action. -/
@[simp]
theorem mpullback_op_smul_mpullback_proj {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {k : ℕ} (g : G) (a : SmoothForm IB B F k) :
    SmoothForm.mpullback (fun x : ManifoldTotalSpace G P ↦ op g • x)
      (contMDiff_const_smul (op g)) (SmoothForm.mpullback
        (fun y : ManifoldTotalSpace G P ↦ ((ManifoldTotalSpace.homeomorph G P).symm y).proj)
        (ManifoldTotalSpace.contMDiff_proj ∞ G P IB IG) a) =
      SmoothForm.mpullback
        (fun y : ManifoldTotalSpace G P ↦ ((ManifoldTotalSpace.homeomorph G P).symm y).proj)
        (ManifoldTotalSpace.contMDiff_proj ∞ G P IB IG) a := by
  simp only [SmoothForm.mpullback_mpullback, proj_comp_op_smul]

/-- **Invariant forms that vanish on vertical vectors are basic.** On a smooth principal bundle, a
smooth form that is invariant under the right action of `G` and vanishes as soon as one of its
arguments is vertical, that is, in the kernel of the derivative of the projection, is basic for
the projection. -/
theorem isBasic_of_mpullback_op_smul {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {k : ℕ} {β : SmoothForm (IB.prod IG) (ManifoldTotalSpace G P) F k}
    (hβ : ∀ g : G, SmoothForm.mpullback (fun x : ManifoldTotalSpace G P ↦ op g • x)
      (contMDiff_const_smul (op g)) β = β)
    (hvert : ∀ x (v : Fin k → TangentSpace (IB.prod IG) x) j,
      mfderiv (IB.prod IG) IB (fun y : ManifoldTotalSpace G P ↦
        ((ManifoldTotalSpace.homeomorph G P).symm y).proj) x (v j) = 0 → β.val x v = 0) :
    RoughForm.IsBasic (V := F) IB
      (fun y : ManifoldTotalSpace G P ↦ ((ManifoldTotalSpace.homeomorph G P).symm y).proj)
      β.val := by
  refine RoughForm.isBasic_of_mpullback_eq
    (σ := fun (g : G) (x : ManifoldTotalSpace G P) ↦ op g • x)
    ((ManifoldTotalSpace.contMDiff_proj ∞ G P IB IG).mdifferentiable (by simp))
    (fun g ↦ (contMDiff_const_smul (I := IB.prod IG) (n := ∞) (op g)).mdifferentiable (by simp))
    proj_comp_op_smul (fun x y hxy ↦ Or.inr (exists_op_smul_eq_of_proj_eq hxy.symm)) hvert
    fun g ↦ ?_
  rw [← SmoothForm.coe_mpullback _ (contMDiff_const_smul (op g)), hβ]

end Basic

section LieDeriv

variable [IsManifold IB ∞ B] [CompleteSpace EG] [LieGroup IG ∞ G]
  [ContMDiffFiberBundle ∞ G P IB IG] [PrincipalBundle G P]

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

/-- **Invariant forms have vanishing Lie derivative along fundamental vector fields.** On a smooth
principal bundle whose base and structure group are modelled without boundary, a smooth form that
is invariant under the right action has vanishing Lie derivative along the fundamental vector
field of every `ξ` in the Lie algebra. This is the right-action counterpart of Tau Ceti's
`TauCeti.mlieDerivForm_fundamentalVectorField_eq_zero`. -/
theorem mlieDerivForm_rightFundamentalVectorField_eq_zero [IB.Boundaryless] [IG.Boundaryless]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}
    {β : SmoothForm (IB.prod IG) (ManifoldTotalSpace G P) F k}
    (hβ : ∀ g : G, SmoothForm.mpullback (fun x : ManifoldTotalSpace G P ↦ op g • x)
      (contMDiff_const_smul (op g)) β = β)
    (ξ : GroupLieAlgebra IG G) :
    mlieDerivForm (rightFundamentalVectorField (IB.prod IG) ξ) β.val = 0 := by
  have : T2Space G := IG.t2Space_of_lieGroup ∞
  funext x
  -- The flow of the field is `x ↦ x • exp (t ξ)`, along which `β` is constant.
  have hψ : ContMDiff (𝓘(ℝ).prod (IB.prod IG)) (IB.prod IG) ∞
      (fun p : ℝ × ManifoldTotalSpace G P ↦ op (mulInvariantExp (p.1 • ξ)) • p.2) :=
    contMDiff_op_smul.comp
      (contMDiff_snd.prodMk ((contMDiff_mulInvariantExp_smul ξ).comp contMDiff_fst))
  have h := hasDerivAt_mpullback_of_eq_id (α := β.val)
    (V := rightFundamentalVectorField (IB.prod IG) ξ)
    (ψ := fun (t : ℝ) (y : ManifoldTotalSpace G P) ↦ op (mulInvariantExp (t • ξ)) • y) (t := 0) x
    (.of_forall fun y ↦ by simp [mulInvariantExp_zero]) ((hψ (0, x)).of_le (by simp))
    (.of_forall fun y ↦ isMIntegralCurve_op_mulInvariantExp_smul ξ y 0)
    (β.mdifferentiable x)
  have hconst : (fun t : ℝ ↦ TauCeti.mpullback (IB.prod IG) (IB.prod IG)
      (fun y : ManifoldTotalSpace G P ↦ op (mulInvariantExp (t • ξ)) • y) β.val x) =
        fun _ ↦ β.val x := by
    funext t
    rw [← SmoothForm.coe_mpullback _ (contMDiff_const_smul (op (mulInvariantExp (t • ξ)))), hβ]
  rw [hconst] at h
  exact h.unique (hasDerivAt_const 0 _)

end LieDeriv

end TauCeti.PrincipalBundle
