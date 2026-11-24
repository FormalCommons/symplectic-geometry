/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Coupling.Basic
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.SmoothFamily.Basic
import SymplecticGeometry.Geometry.Manifold.FiberBundle.Principal.BasicForm

/-!
# Existence of coupling forms

Let `P` be a smooth principal `Circle`-bundle over `B`, with projection `π`, and let `a < b`. This
file constructs coupling forms (`SymplecticGeometry.IsCouplingForm`) on
`ManifoldTotalSpace Circle P × Set.Icc a b`, the existence half of McDuff–Salamon's
Proposition 5.1.9.

The construction starts from a connection form `α⁰` (`SymplecticGeometry.IsCircleConnectionForm`)
with curvature `F`, and a family `τ` of two-forms on `B` whose classes satisfy the cohomological
condition `[τ t] - [τ a] = -(t - a) c₁(P)`. That condition makes the forms
`τ t - τ a - (t - a) (2π)⁻¹ F` exact, with a smooth family of primitives `β t`. The one-form
`A = (2π)⁻¹ (t - a) pr^* α⁰ + pr^* π^* β_t` on the product then gives the coupling form
`pr^* π^* τ_a + d A`.

## Main definitions

* `SymplecticGeometry.couplingOneForm α β hβ`: the one-form `A` above, for a one-form `α` on the
  total space and a smooth family `β` of one-forms on `B`.

## Main results

* `SymplecticGeometry.couplingOneForm_apply`: the value of `A` at `(p, t)` on a tangent vector
  `v` is `(2π)⁻¹ (t - a) α(v₁) + β_t(dπ v₁)`, where `v₁` is the component of `v` along `P`.
* `SymplecticGeometry.mpullback_slice_couplingOneForm`: the slice of `A` at `t`, its pull-back
  along `p ↦ (p, t)`, is `(2π)⁻¹ (t - a) α + π^* β_t`.
* `SymplecticGeometry.IsCircleConnectionForm.mpullback_smul_couplingOneForm`: for a connection
  form `α`, the form `A` is invariant under the circle action on the first factor.
* `SymplecticGeometry.IsCircleConnectionForm.couplingOneForm_apply_couplingField`: for a
  connection form `α`, the value of `A` on the field `(X, 0)` of `SymplecticGeometry.couplingField`
  is `t - a` at `(p, t)`.

## Implementation notes

The second term of `A` is Tau Ceti's vertical form `TauCeti.verticalForm` of the family
`t ↦ π^* β_t`, as a smooth form `TauCeti.SmoothForm.ofSlices` on `Set.Icc a b × P`, pulled back
along `Prod.swap`, since families of forms put the parameter first. The first term is the
pull-back of `α` along the first projection multiplied by the smooth function
`(p, t) ↦ (2π)⁻¹ (t - a)` (`TauCeti.SmoothForm.funSMulₗ`).

The factor `(2π)⁻¹` comes from the normalization of connection forms: they take the value `1` on
the fundamental field of `circleLieGenerator`, while the field `X` of a coupling form is that of
`circlePeriodOneGenerator = 2π • circleLieGenerator`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Proposition 5.1.9.
-/

public section

noncomputable section

open Bundle Manifold MulOpposite TauCeti
open scoped Manifold ContDiff

namespace SymplecticGeometry

variable {EB HB B : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  {IB : ModelWithCorners ℝ EB HB} [TopologicalSpace B] [ChartedSpace HB B] [IsManifold IB ∞ B]
  {P : B → Type*} [TopologicalSpace (TotalSpace Circle P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle Circle P]
  [ContMDiffFiberBundle ∞ Circle P IB (𝓡 1)]
  {a b : ℝ} [Fact (a < b)]

/-! ### The one-form `A` -/

/-- The pull-backs `t ↦ π^* β_t` to the total space of a smooth family `β` of forms on the base
form a smooth family. -/
private theorem isSmoothFamily_mpullback_proj {β : Set.Icc a b → SmoothForm IB B ℝ 1}
    (hβ : IsSmoothFamily (𝓡∂ 1) β) :
    IsSmoothFamily (𝓡∂ 1) fun t ↦ SmoothForm.mpullback (fun y : ManifoldTotalSpace Circle P ↦
      ((ManifoldTotalSpace.homeomorph Circle P).symm y).proj)
        (ManifoldTotalSpace.contMDiff_proj ∞ Circle P IB (𝓡 1)) (β t) :=
  hβ.mpullback _ _

/-- The one-form `A = (2π)⁻¹ (t - a) pr^* α + pr^* π^* β_t` on `P × [a, b]`, for a one-form `α`
on the total space of `P` and a smooth family `β` of one-forms on `B` indexed by `[a, b]`. Here
`pr` is the projection to the total space, and the second term is the vertical form of the
family `t ↦ π^* β_t`, read through the swap of the two factors. -/
def couplingOneForm (α : SmoothForm (IB.prod (𝓡 1)) (ManifoldTotalSpace Circle P) ℝ 1)
    (β : Set.Icc a b → SmoothForm IB B ℝ 1) (hβ : IsSmoothFamily (𝓡∂ 1) β) :
    SmoothForm ((IB.prod (𝓡 1)).prod (𝓡∂ 1)) (ManifoldTotalSpace Circle P × Set.Icc a b) ℝ 1 :=
  have hc : ContMDiff ((IB.prod (𝓡 1)).prod (𝓡∂ 1)) 𝓘(ℝ, ℝ) ∞
      fun x : ManifoldTotalSpace Circle P × Set.Icc a b ↦ (2 * Real.pi)⁻¹ * ((x.2 : ℝ) - a) :=
    contMDiff_const.mul ((contMDiff_subtypeVal_Icc.comp contMDiff_snd).sub contMDiff_const)
  ⟨fun x ↦ ((2 * Real.pi)⁻¹ * ((x.2 : ℝ) - a)) •
        (SmoothForm.mpullback Prod.fst contMDiff_fst α).val x +
      (SmoothForm.mpullback Prod.swap (contMDiff_snd.prodMk contMDiff_fst)
        (SmoothForm.ofSlices (J := 𝓡∂ 1) _
          (isSmoothFamily_iff_contMDiff.mp (isSmoothFamily_mpullback_proj hβ)))).val x,
    (((SmoothForm.mpullback Prod.fst contMDiff_fst α).isSmoothForm.fun_smul hc).add
      (SmoothForm.mpullback Prod.swap (contMDiff_snd.prodMk contMDiff_fst)
        (SmoothForm.ofSlices (J := 𝓡∂ 1) _
          (isSmoothFamily_iff_contMDiff.mp (isSmoothFamily_mpullback_proj hβ)))).isSmoothForm
      ).mem_smoothBundleForms⟩

variable {α : SmoothForm (IB.prod (𝓡 1)) (ManifoldTotalSpace Circle P) ℝ 1}
  {β : Set.Icc a b → SmoothForm IB B ℝ 1} (hβ : IsSmoothFamily (𝓡∂ 1) β)

/-- The definition of `SymplecticGeometry.couplingOneForm`, on underlying forms. -/
theorem couplingOneForm_def :
    (couplingOneForm α β hβ).val = fun x : ManifoldTotalSpace Circle P × Set.Icc a b ↦
      ((2 * Real.pi)⁻¹ * ((x.2 : ℝ) - a)) • mpullback _ (IB.prod (𝓡 1)) Prod.fst α.val x +
        mpullback _ ((𝓡∂ 1).prod (IB.prod (𝓡 1))) Prod.swap
          (verticalForm (𝓡∂ 1) fun t ↦ (SmoothForm.mpullback
            (fun y : ManifoldTotalSpace Circle P ↦
              ((ManifoldTotalSpace.homeomorph Circle P).symm y).proj)
            (ManifoldTotalSpace.contMDiff_proj ∞ Circle P IB (𝓡 1)) (β t)).val) x := by
  rw [couplingOneForm]
  simp only [SmoothForm.coe_mpullback, SmoothForm.coe_ofSlices]

/-- The value of `A = couplingOneForm α β hβ` at `(p, t)` on a tangent vector `v`:
`(2π)⁻¹ (t - a) α(v₁) + β_t(dπ v₁)`, where `v₁` is the component of `v` along the total space. -/
theorem couplingOneForm_apply (x : ManifoldTotalSpace Circle P × Set.Icc a b)
    (v : Fin 1 → TangentSpace ((IB.prod (𝓡 1)).prod (𝓡∂ 1)) x) :
    (couplingOneForm α β hβ).val x v =
      (2 * Real.pi)⁻¹ * ((x.2 : ℝ) - a) * α.val x.1 (fun i ↦ (v i).1) +
        (β x.2).val ((ManifoldTotalSpace.homeomorph Circle P).symm x.1).proj
          (fun i ↦ mfderiv (IB.prod (𝓡 1)) IB (fun y : ManifoldTotalSpace Circle P ↦
            ((ManifoldTotalSpace.homeomorph Circle P).symm y).proj) x.1 (v i).1) := by
  have hswap := mpullback_verticalForm_apply (J := 𝓡∂ 1) (f := Prod.swap)
    (fun t ↦ (SmoothForm.mpullback (fun y : ManifoldTotalSpace Circle P ↦
        ((ManifoldTotalSpace.homeomorph Circle P).symm y).proj)
      (ManifoldTotalSpace.contMDiff_proj ∞ Circle P IB (𝓡 1)) (β t)).val)
    ((contMDiff_snd.prodMk contMDiff_fst).mdifferentiableAt (n := 1) one_ne_zero (x := x))
  have hcomp : (Prod.snd ∘ Prod.swap :
      ManifoldTotalSpace Circle P × Set.Icc a b → ManifoldTotalSpace Circle P) = Prod.fst :=
    funext fun _ ↦ Prod.snd_swap
  rw [couplingOneForm_def, ContinuousAlternatingMap.add_apply, hswap, hcomp]
  simp only [SmoothForm.coe_mpullback, mfderiv_fst, ContinuousAlternatingMap.smul_apply,
    TauCeti.mpullback_apply, smul_eq_mul, mul_assoc]
  -- the tangent space of the product is the product of the tangent spaces, on which
  -- `ContinuousLinearMap.fst` is the first projection by definition
  rfl

/-- **The slices of `A`.** The pull-back of `A = couplingOneForm α β hβ` along `p ↦ (p, t)` is
`(2π)⁻¹ (t - a) α + π^* β_t`. -/
theorem mpullback_slice_couplingOneForm (t : Set.Icc a b) :
    SmoothForm.mpullback (fun p : ManifoldTotalSpace Circle P ↦ (p, t))
        (contMDiff_id.prodMk contMDiff_const) (couplingOneForm α β hβ) =
      ((2 * Real.pi)⁻¹ * ((t : ℝ) - a)) • α +
        SmoothForm.mpullback (fun y : ManifoldTotalSpace Circle P ↦
            ((ManifoldTotalSpace.homeomorph Circle P).symm y).proj)
          (ManifoldTotalSpace.contMDiff_proj ∞ Circle P IB (𝓡 1)) (β t) := by
  refine Subtype.ext <| funext fun p ↦ ContinuousAlternatingMap.ext fun v ↦ ?_
  rw [SmoothForm.mpullback_apply, couplingOneForm_apply]
  simp [mfderiv_prod_left]
  -- the first component of `ContinuousLinearMap.inl _ _ _ w` is `w`, by definition
  rfl

variable [∀ b, MulAction Circleᵐᵒᵖ (P b)] [PrincipalBundle Circle P]

namespace IsCircleConnectionForm

/-- **Invariance of `A`.** For a connection form `α`, the one-form `A = couplingOneForm α β hβ` is
invariant under the circle action `(p, t) ↦ (p • z, t)` on the first factor. -/
theorem mpullback_smul_couplingOneForm (hα : IsCircleConnectionForm α) (z : Circle) :
    SmoothForm.mpullback (fun x : ManifoldTotalSpace Circle P × Set.Icc a b ↦ (op z • x.1, x.2))
        (((contMDiff_const_smul (op z)).comp contMDiff_fst).prodMk contMDiff_snd)
        (couplingOneForm α β hβ) =
      couplingOneForm α β hβ := by
  refine Subtype.ext <| funext fun x ↦ ContinuousAlternatingMap.ext fun v ↦ ?_
  have hz : ContMDiff (IB.prod (𝓡 1)) (IB.prod (𝓡 1)) ∞
      (fun y : ManifoldTotalSpace Circle P ↦ op z • y) := contMDiff_const_smul (op z)
  have hD : mfderiv ((IB.prod (𝓡 1)).prod (𝓡∂ 1)) ((IB.prod (𝓡 1)).prod (𝓡∂ 1))
      (fun x : ManifoldTotalSpace Circle P × Set.Icc a b ↦ (op z • x.1, x.2)) x =
      (mfderiv (IB.prod (𝓡 1)) (IB.prod (𝓡 1)) (fun y ↦ op z • y) x.1).prodMap
        (mfderiv (𝓡∂ 1) (𝓡∂ 1) id x.2) :=
    mfderiv_prodMap (hz.mdifferentiableAt (by simp)) mdifferentiableAt_id
  have h₁ (w : Fin 1 → TangentSpace (IB.prod (𝓡 1)) x.1) :
      α.val (op z • x.1) (fun i ↦ mfderiv (IB.prod (𝓡 1)) (IB.prod (𝓡 1))
        (fun y : ManifoldTotalSpace Circle P ↦ op z • y) x.1 (w i)) = α.val x.1 w := by
    rw [← SmoothForm.mpullback_apply _ hz, hα.mpullback_op_smul]
  have h₂ (w : Fin 1 → TangentSpace (IB.prod (𝓡 1)) x.1) :
      (β x.2).val ((ManifoldTotalSpace.homeomorph Circle P).symm (op z • x.1)).proj
        (fun i ↦ mfderiv (IB.prod (𝓡 1)) IB (fun y : ManifoldTotalSpace Circle P ↦
          ((ManifoldTotalSpace.homeomorph Circle P).symm y).proj) (op z • x.1)
          (mfderiv (IB.prod (𝓡 1)) (IB.prod (𝓡 1))
            (fun y : ManifoldTotalSpace Circle P ↦ op z • y) x.1 (w i))) =
      (β x.2).val ((ManifoldTotalSpace.homeomorph Circle P).symm x.1).proj
        (fun i ↦ mfderiv (IB.prod (𝓡 1)) IB (fun y : ManifoldTotalSpace Circle P ↦
          ((ManifoldTotalSpace.homeomorph Circle P).symm y).proj) x.1 (w i)) := by
    have h := congrArg (fun φ ↦ φ.val x.1 w)
      (PrincipalBundle.mpullback_op_smul_mpullback_proj (IG := 𝓡 1) z (β x.2))
    rwa [SmoothForm.mpullback_apply, SmoothForm.mpullback_apply, SmoothForm.mpullback_apply] at h
  rw [SmoothForm.mpullback_apply, couplingOneForm_apply, couplingOneForm_apply, hD]
  exact congrArg₂ _ (congrArg _ (h₁ fun i ↦ (v i).1)) (h₂ fun i ↦ (v i).1)

/-- **The value of `A` on the coupling field.** For a connection form `α`, the one-form
`A = couplingOneForm α β hβ` takes the value `t - a` on the field `(X, 0)` at `(p, t)`. -/
theorem couplingOneForm_apply_couplingField (hα : IsCircleConnectionForm α)
    (x : ManifoldTotalSpace Circle P × Set.Icc a b) :
    (couplingOneForm α β hβ).val x ![couplingField IB P a b x] = (x.2 : ℝ) - a := by
  have hX : rightFundamentalVectorField (IB.prod (𝓡 1)) circlePeriodOneGenerator x.1 =
      (2 * Real.pi) • rightFundamentalVectorField (IB.prod (𝓡 1)) circleLieGenerator x.1 := by
    rw [circlePeriodOneGenerator_def, rightFundamentalVectorField_smul, Pi.smul_apply]
  have hv : (fun i ↦ (![couplingField IB P a b x] i).1) =
      ![rightFundamentalVectorField (IB.prod (𝓡 1)) circlePeriodOneGenerator x.1] := by
    funext i
    fin_cases i
    exact couplingField_fst x
  have hπ : (fun i ↦ mfderiv (IB.prod (𝓡 1)) IB (fun y : ManifoldTotalSpace Circle P ↦
      ((ManifoldTotalSpace.homeomorph Circle P).symm y).proj) x.1
        ((![couplingField IB P a b x] i).1)) = 0 := by
    funext i
    fin_cases i
    simp
  rw [couplingOneForm_apply, hv, hπ, hX, ContinuousAlternatingMap.vecCons_smul,
    hα.apply_rightFundamentalVectorField, ContinuousAlternatingMap.map_zero]
  field_simp
  ring

end IsCircleConnectionForm

end SymplecticGeometry

end
