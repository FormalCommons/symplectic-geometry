/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Coupling.Basic
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.SmoothFamily.Basic
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Smooth
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.DegreeOne
import SymplecticGeometry.Geometry.Manifold.DeRham.SmoothFamily.GoodCover
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Pullback.Descent
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Pullback.Smooth
import SymplecticGeometry.Geometry.Manifold.FiberBundle.Principal.BasicForm
import SymplecticGeometry.Geometry.Manifold.MFDeriv.Prod
import SymplecticGeometry.Geometry.Manifold.DeRham.GoodCover.Compact
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Vertical
import SymplecticGeometry.Topology.Algebra.Module.Alternating.Basic

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
* `SymplecticGeometry.couplingForm α β hβ σ`: the two-form `pr^* π^* σ + d A`, for a two-form
  `σ` on `B`.

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
* `SymplecticGeometry.IsCircleConnectionForm.isCouplingForm_couplingForm`: for a connection form
  `α` with curvature `F`, a closed two-form `σ` on `B`, and a smooth family `β` with
  `d β_t = τ t - σ - (t - a) (2π)⁻¹ F`, the form `pr^* π^* σ + d A` is a coupling form for `τ`.
  Its contraction with `(X, 0)` is computed by Cartan's identity for the invariant one-form `A`
  (`TauCeti.PrincipalBundle.mextDeriv_apply_rightFundamentalVectorField_prod`), which holds
  although the interval has boundary.
* `SymplecticGeometry.exists_isCouplingForm`: over a compact Hausdorff boundaryless base, a
  smooth family `τ` of symplectic forms satisfying the cohomological condition has a coupling
  form, and it is symplectic. The primitives `β t` come from
  `SymplecticGeometry.exists_isSmoothFamily_mextDerivₗ_eq`, since a compact manifold has a
  finite good cover (`SymplecticGeometry.hasFiniteGoodCover_of_compactSpace`), and the coupling
  form is symplectic by `SymplecticGeometry.IsCouplingForm.isSymplectic`.

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

/-- The one-form `A = (2π)⁻¹ (t - a) pr^* α + pr^* π^* β_t` on `P × [a, b]`, for a one-form `α`
on the total space of `P` and a smooth family `β` of one-forms on `B` indexed by `[a, b]`. Here
`pr` is the projection to the total space, and the second term is the vertical form of the
family `t ↦ π^* β_t`, read through the swap of the two factors. -/
def couplingOneForm (α : SmoothForm (IB.prod (𝓡 1)) (ManifoldTotalSpace Circle P) ℝ 1)
    (β : Set.Icc a b → SmoothForm IB B ℝ 1) (hβ : IsSmoothFamily (𝓡∂ 1) β) :
    SmoothForm ((IB.prod (𝓡 1)).prod (𝓡∂ 1)) (ManifoldTotalSpace Circle P × Set.Icc a b) ℝ 1 :=
  SmoothForm.funSMulₗ ⟨fun x : ManifoldTotalSpace Circle P × Set.Icc a b ↦
          (2 * Real.pi)⁻¹ * ((x.2 : ℝ) - a),
      contMDiff_const.mul ((contMDiff_subtypeVal_Icc.comp contMDiff_snd).sub contMDiff_const)⟩
    (SmoothForm.mpullback Prod.fst contMDiff_fst α) +
  SmoothForm.mpullback Prod.swap (contMDiff_snd.prodMk contMDiff_fst)
    (SmoothForm.ofSlices (J := 𝓡∂ 1) _ (isSmoothFamily_iff_contMDiff.mp
      (hβ.mpullback (ManifoldTotalSpace.projContMDiffMap ∞ Circle P IB (𝓡 1))
        (ManifoldTotalSpace.projContMDiffMap ∞ Circle P IB (𝓡 1)).contMDiff)))

variable {α : SmoothForm (IB.prod (𝓡 1)) (ManifoldTotalSpace Circle P) ℝ 1}
  {β : Set.Icc a b → SmoothForm IB B ℝ 1} (hβ : IsSmoothFamily (𝓡∂ 1) β)

/-- The definition of `SymplecticGeometry.couplingOneForm`. -/
theorem couplingOneForm_def :
    couplingOneForm α β hβ =
      SmoothForm.funSMulₗ ⟨fun x : ManifoldTotalSpace Circle P × Set.Icc a b ↦
          (2 * Real.pi)⁻¹ * ((x.2 : ℝ) - a),
          contMDiff_const.mul ((contMDiff_subtypeVal_Icc.comp contMDiff_snd).sub contMDiff_const)⟩
        (SmoothForm.mpullback Prod.fst contMDiff_fst α) +
      SmoothForm.mpullback Prod.swap (contMDiff_snd.prodMk contMDiff_fst)
        (SmoothForm.ofSlices (J := 𝓡∂ 1) _ (isSmoothFamily_iff_contMDiff.mp
          (hβ.mpullback (ManifoldTotalSpace.projContMDiffMap ∞ Circle P IB (𝓡 1))
            (ManifoldTotalSpace.projContMDiffMap ∞ Circle P IB (𝓡 1)).contMDiff))) :=
  (rfl)

/-- The underlying rough form of `SymplecticGeometry.couplingOneForm`: at `x`, the sum of
`(2π)⁻¹ (x.2 - a)` times the pull-back of `α` along the first projection, and of the pull-back
along the swap of the vertical form of `t ↦ π^* β_t`. -/
theorem coe_couplingOneForm :
    (couplingOneForm α β hβ).val = fun x : ManifoldTotalSpace Circle P × Set.Icc a b ↦
      ((2 * Real.pi)⁻¹ * ((x.2 : ℝ) - a)) • mpullback _ (IB.prod (𝓡 1)) Prod.fst α.val x +
        mpullback _ ((𝓡∂ 1).prod (IB.prod (𝓡 1))) Prod.swap
          (verticalForm (𝓡∂ 1) fun t ↦ (SmoothForm.mpullback
            (ManifoldTotalSpace.projContMDiffMap ∞ Circle P IB (𝓡 1))
            (ManifoldTotalSpace.projContMDiffMap ∞ Circle P IB (𝓡 1)).contMDiff (β t)).val) x := by
  rw [couplingOneForm_def, SmoothForm.add_toRoughForm, SmoothForm.coe_mpullback (f := Prod.swap),
    SmoothForm.coe_ofSlices]
  exact congrArg (· + _) ((SmoothForm.coe_funSMulₗ _ _).trans
    (by rw [SmoothForm.coe_mpullback, ContMDiffMap.coeFn_mk]))

/-- The value of `A = couplingOneForm α β hβ` at `(p, t)` on a tangent vector `v`:
`(2π)⁻¹ (t - a) α(v₁) + β_t(dπ v₁)`, where `v₁` is the component of `v` along the total space. -/
theorem couplingOneForm_apply (x : ManifoldTotalSpace Circle P × Set.Icc a b)
    (v : Fin 1 → TangentSpace ((IB.prod (𝓡 1)).prod (𝓡∂ 1)) x) :
    (couplingOneForm α β hβ).val x v =
      (2 * Real.pi)⁻¹ * ((x.2 : ℝ) - a) * α.val x.1 (fun i ↦ (v i).1) +
        (β x.2).val (ManifoldTotalSpace.projContMDiffMap ∞ Circle P IB (𝓡 1) x.1)
          (fun i ↦ mfderiv (IB.prod (𝓡 1)) IB
            (ManifoldTotalSpace.projContMDiffMap ∞ Circle P IB (𝓡 1)) x.1 (v i).1) := by
  have hswap := mpullback_verticalForm_apply (J := 𝓡∂ 1) (f := Prod.swap)
    (fun t ↦ (SmoothForm.mpullback (ManifoldTotalSpace.projContMDiffMap ∞ Circle P IB (𝓡 1))
      (ManifoldTotalSpace.projContMDiffMap ∞ Circle P IB (𝓡 1)).contMDiff (β t)).val)
    ((contMDiff_snd.prodMk contMDiff_fst).mdifferentiableAt (n := 1) one_ne_zero (x := x))
  have hcomp : (Prod.snd ∘ Prod.swap :
      ManifoldTotalSpace Circle P × Set.Icc a b → ManifoldTotalSpace Circle P) = Prod.fst :=
    funext fun _ ↦ Prod.snd_swap
  rw [coe_couplingOneForm, ContinuousAlternatingMap.add_apply, hswap, hcomp]
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
        SmoothForm.mpullback (ManifoldTotalSpace.projContMDiffMap ∞ Circle P IB (𝓡 1))
          (ManifoldTotalSpace.projContMDiffMap ∞ Circle P IB (𝓡 1)).contMDiff (β t) := by
  refine SmoothBundleForm.ext_fin_one fun p v ↦ ?_
  rw [SmoothForm.mpullback_apply, couplingOneForm_apply]
  simp only [mfderiv_prodMk_left_apply, SmoothBundleForm.add_apply,
    SmoothBundleForm.smul_apply, SmoothForm.coe_mpullback, ContinuousAlternatingMap.add_apply,
    ContinuousAlternatingMap.smul_apply, smul_eq_mul, mpullback_apply]

/-! ### The coupling form `pr^* π^* σ + d A` -/

variable (α β) in
/-- The two-form `pr^* π^* σ + d A` on `P × [a, b]`, for a two-form `σ` on `B`, where `pr` is the
projection to the total space, `π` the projection of `P`, and `A = couplingOneForm α β hβ`. For a
connection form `α`, a closed `σ` and primitives `β t` of `τ t - σ - (t - a) (2π)⁻¹ F`, it is a
coupling form for `τ` (`IsCircleConnectionForm.isCouplingForm_couplingForm`). -/
def couplingForm (σ : SmoothTwoForm IB B) :
    SmoothTwoForm ((IB.prod (𝓡 1)).prod (𝓡∂ 1)) (ManifoldTotalSpace Circle P × Set.Icc a b) :=
  SmoothForm.mpullback Prod.fst contMDiff_fst
      (SmoothForm.mpullback (ManifoldTotalSpace.projContMDiffMap ∞ Circle P IB (𝓡 1))
        (ManifoldTotalSpace.projContMDiffMap ∞ Circle P IB (𝓡 1)).contMDiff σ) +
    mextDerivₗ ((IB.prod (𝓡 1)).prod (𝓡∂ 1)) 1 (couplingOneForm α β hβ)

/-- The definition of `SymplecticGeometry.couplingForm`. -/
theorem couplingForm_def (σ : SmoothTwoForm IB B) :
    couplingForm α β hβ σ =
      SmoothForm.mpullback Prod.fst contMDiff_fst
          (SmoothForm.mpullback (ManifoldTotalSpace.projContMDiffMap ∞ Circle P IB (𝓡 1))
            (ManifoldTotalSpace.projContMDiffMap ∞ Circle P IB (𝓡 1)).contMDiff σ) +
        mextDerivₗ ((IB.prod (𝓡 1)).prod (𝓡∂ 1)) 1 (couplingOneForm α β hβ) :=
  (rfl)

/-- The form `pr^* π^* σ + d A` is closed when `σ` is. -/
theorem isClosed_couplingForm {σ : SmoothTwoForm IB B} (hσ : σ.IsClosed) :
    (couplingForm α β hβ σ).IsClosed :=
  ((hσ.mpullback _ _).mpullback _ _).add (SmoothForm.isClosed_mextDerivₗ _)

/-- **The slices of `pr^* π^* σ + d A`.** Its pull-back along `p ↦ (p, t)` is
`π^* (σ + d β_t) + (2π)⁻¹ (t - a) d α`. -/
theorem mpullback_slice_couplingForm (σ : SmoothTwoForm IB B) (t : Set.Icc a b) :
    SmoothForm.mpullback (fun p : ManifoldTotalSpace Circle P ↦ (p, t))
        (contMDiff_id.prodMk contMDiff_const) (couplingForm α β hβ σ) =
      SmoothForm.mpullback (ManifoldTotalSpace.projContMDiffMap ∞ Circle P IB (𝓡 1))
        (ManifoldTotalSpace.projContMDiffMap ∞ Circle P IB (𝓡 1)).contMDiff
        (σ + mextDerivₗ IB 1 (β t)) +
      ((2 * Real.pi)⁻¹ * ((t : ℝ) - a)) • mextDerivₗ (IB.prod (𝓡 1)) 1 α := by
  rw [couplingForm_def, map_add, SmoothForm.mpullback_mpullback, ← SmoothForm.mextDerivₗ_mpullback,
    mpullback_slice_couplingOneForm, map_add, map_smul, SmoothForm.mextDerivₗ_mpullback, map_add]
  -- the composite `Prod.fst ∘ (·, t)` is the identity of the total space
  rw [SmoothForm.mpullback_eq_self_of_eq_id _ (by rfl)]
  abel

variable [∀ b, MulAction Circleᵐᵒᵖ (P b)] [PrincipalBundle Circle P]

namespace IsCircleConnectionForm

/-- **Invariance of `A`.** For a connection form `α`, the one-form `A = couplingOneForm α β hβ` is
invariant under the circle action `(p, t) ↦ (p • z, t)` on the first factor. -/
theorem mpullback_smul_couplingOneForm (hα : IsCircleConnectionForm α) (z : Circle) :
    SmoothForm.mpullback (fun x : ManifoldTotalSpace Circle P × Set.Icc a b ↦ (op z • x.1, x.2))
        (((contMDiff_const_smul (op z)).comp contMDiff_fst).prodMk contMDiff_snd)
        (couplingOneForm α β hβ) =
      couplingOneForm α β hβ := by
  refine SmoothBundleForm.ext fun x v ↦ ?_
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
      (β x.2).val (ManifoldTotalSpace.projContMDiffMap ∞ Circle P IB (𝓡 1) (op z • x.1))
        (fun i ↦ mfderiv (IB.prod (𝓡 1)) IB
          (ManifoldTotalSpace.projContMDiffMap ∞ Circle P IB (𝓡 1)) (op z • x.1)
          (mfderiv (IB.prod (𝓡 1)) (IB.prod (𝓡 1))
            (fun y : ManifoldTotalSpace Circle P ↦ op z • y) x.1 (w i))) =
      (β x.2).val (ManifoldTotalSpace.projContMDiffMap ∞ Circle P IB (𝓡 1) x.1)
        (fun i ↦ mfderiv (IB.prod (𝓡 1)) IB
          (ManifoldTotalSpace.projContMDiffMap ∞ Circle P IB (𝓡 1)) x.1 (w i)) := by
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
  have hv : (fun i ↦ (![couplingField IB P a b x] i).1) =
      ![rightFundamentalVectorField (IB.prod (𝓡 1)) circlePeriodOneGenerator x.1] := by
    funext i
    fin_cases i
    exact couplingField_fst x
  have hπ : (fun i ↦ mfderiv (IB.prod (𝓡 1)) IB
      (ManifoldTotalSpace.projContMDiffMap ∞ Circle P IB (𝓡 1)) x.1
        ((![couplingField IB P a b x] i).1)) = 0 := by
    funext i
    fin_cases i
    -- Tau Ceti's lemma is stated with the projection written out
    rw [Matrix.cons_val_fin_one, couplingField_fst, ManifoldTotalSpace.coe_projContMDiffMap]
    exact PrincipalBundle.mfderiv_proj_rightFundamentalVectorField _ _
  rw [couplingOneForm_apply, hv, hπ, rightFundamentalVectorField_circlePeriodOneGenerator,
    Pi.smul_apply, ContinuousAlternatingMap.vecCons_smul,
    hα.apply_rightFundamentalVectorField, ContinuousAlternatingMap.map_zero]
  field_simp
  ring

/-- **Invariance of `pr^* π^* σ + d A`.** For a connection form `α`, the form
`couplingForm α β hβ σ` is invariant under the circle action `(p, t) ↦ (p • z, t)` on the first
factor. -/
theorem mpullback_smul_couplingForm (hα : IsCircleConnectionForm α) (σ : SmoothTwoForm IB B)
    (z : Circle) :
    SmoothForm.mpullback (fun x : ManifoldTotalSpace Circle P × Set.Icc a b ↦ (op z • x.1, x.2))
        (((contMDiff_const_smul (op z)).comp contMDiff_fst).prodMk contMDiff_snd)
        (couplingForm α β hβ σ) =
      couplingForm α β hβ σ := by
  have h := PrincipalBundle.mpullback_op_smul_mpullback_proj (IG := 𝓡 1) (P := P) z σ
  rw [couplingForm_def, map_add, ← SmoothForm.mextDerivₗ_mpullback,
    hα.mpullback_smul_couplingOneForm hβ,
    SmoothForm.mpullback_mpullback_of_comp_eq _ contMDiff_fst contMDiff_fst
      (contMDiff_const_smul (op z)) rfl, h]

variable [IB.Boundaryless]

/-- **The Hamiltonian identity of `pr^* π^* σ + d A`.** For a connection form `α`, the contraction
of `couplingForm α β hβ σ` with the field `(X, 0)` is `-dt`. The term `pr^* π^* σ` vanishes on
the vertical field, and by Cartan's identity for the invariant form `A`, the contraction of `d A`
is `-d (A (X, 0)) = -d (t - a)`. -/
theorem interior_couplingForm (hα : IsCircleConnectionForm α) (σ : SmoothTwoForm IB B) :
    RoughForm.interior (couplingField IB P a b) (couplingForm α β hβ σ).val =
      -mextDeriv (RoughForm.ofFunction ((IB.prod (𝓡 1)).prod (𝓡∂ 1))
        fun x : ManifoldTotalSpace Circle P × Set.Icc a b ↦ (x.2 : ℝ)) := by
  funext x
  ext v
  rw [RoughForm.interior_apply, couplingForm_def, SmoothBundleForm.add_apply]
  have h0 : (SmoothForm.mpullback Prod.fst contMDiff_fst
      (SmoothForm.mpullback (ManifoldTotalSpace.projContMDiffMap ∞ Circle P IB (𝓡 1))
        (ManifoldTotalSpace.projContMDiffMap ∞ Circle P IB (𝓡 1)).contMDiff σ)).val x
        ![couplingField IB P a b x, v] = 0 := by
    rw [SmoothForm.mpullback_mpullback, SmoothForm.coe_mpullback]
    refine (RoughForm.isBasic_mpullback _).apply_eq_zero_of_mfderiv_eq_zero (j := 0) ?_
    rw [mfderiv_comp x (ManifoldTotalSpace.mdifferentiable_projContMDiffMap x.1)
      mdifferentiableAt_fst, ContinuousLinearMap.comp_apply, mfderiv_fst,
      Matrix.cons_val_zero]
    have h : mfderiv (IB.prod (𝓡 1)) IB (ManifoldTotalSpace.projContMDiffMap ∞ Circle P IB (𝓡 1))
        x.1 (couplingField IB P a b x).1 = 0 := by
      -- Tau Ceti's lemma is stated with the projection written out
      rw [couplingField_fst, ManifoldTotalSpace.coe_projContMDiffMap,
        PrincipalBundle.mfderiv_proj_rightFundamentalVectorField]
    -- `ContinuousLinearMap.fst` takes the first component by definition; `coe_fst'` does not
    -- fire, since the vector is typed as a tangent vector of the product
    exact h
  have hX : couplingField IB P a b = _ := funext couplingField_def
  have hC : mextDeriv (couplingOneForm α β hβ).val x ![couplingField IB P a b x, v] =
      -mvfderiv ((IB.prod (𝓡 1)).prod (𝓡∂ 1)) (fun q ↦
        (couplingOneForm α β hβ).val q ![couplingField IB P a b q]) x v := by
    rw [hX]
    exact PrincipalBundle.mextDeriv_apply_rightFundamentalVectorField_prod
      (hα.mpullback_smul_couplingOneForm hβ) circlePeriodOneGenerator x v
  have hA : (fun q ↦ (couplingOneForm α β hβ).val q ![couplingField IB P a b q]) =
      fun q ↦ (q.2 : ℝ) - a :=
    funext (hα.couplingOneForm_apply_couplingField hβ)
  rw [ContinuousAlternatingMap.add_apply, h0, zero_add, Pi.neg_apply,
    ContinuousAlternatingMap.neg_apply, mextDeriv_ofFunction_apply, mextDerivₗ_apply, hC, hA]
  simp only [sub_eq_add_neg, mvfderiv_add_const, mvfderiv_apply_eq_mfderiv_apply]

/-- **The coupling form of a connection form and a family of primitives.** Let `α` be a connection
form with curvature `F`, let `τ` be a family of two-forms on `B` indexed by `[a, b]`, and let `σ`
be a closed two-form on `B`. If `β` is a smooth family of one-forms with
`d β_t = τ t - σ - (t - a) (2π)⁻¹ F` for every `t`, then `pr^* π^* σ + d A`, with
`A = couplingOneForm α β hβ`, is a coupling form for `τ`. Evaluating the hypothesis at `t = a`
shows `τ a = σ + d β_a`, so `σ` is `τ a` up to an exact form. -/
theorem isCouplingForm_couplingForm (hα : IsCircleConnectionForm α)
    {τ : Set.Icc a b → SmoothTwoForm IB B} {σ : SmoothTwoForm IB B} (hσ : σ.IsClosed)
    (hdβ : ∀ t, mextDerivₗ IB 1 (β t) = τ t - σ - ((t : ℝ) - a) • (2 * Real.pi)⁻¹ • hα.curvature) :
    IsCouplingForm (couplingForm α β hβ σ) τ where
  isClosed := isClosed_couplingForm hβ hσ
  mpullback_smul := hα.mpullback_smul_couplingForm hβ σ
  interior_eq := hα.interior_couplingForm hβ σ
  mpullback_slice t := by
    rw [mpullback_slice_couplingForm, hdβ, ← hα.mpullback_curvature, ← map_smul, ← map_add]
    congr 1
    module

end IsCircleConnectionForm

/-- **Existence of coupling forms.** Let `P` be a smooth principal `Circle`-bundle over a compact
Hausdorff boundaryless manifold `B`, modelled on a finite-dimensional space, and let `τ` be a
family of symplectic forms `τ t` on `B`, smooth in `t ∈ [a, b]`, whose de Rham classes satisfy
`[τ t] - [τ s] = -(t - s) c₁(P)` for all `t` and `s`. Then there is a coupling form `σ` for `τ`
on `P × [a, b]`, and `σ` is symplectic.

Milestone: *Minimal coupling*. -/
theorem exists_isCouplingForm [IB.Boundaryless] [FiniteDimensional ℝ EB] [CompactSpace B]
    [T2Space B]
    {τ : Set.Icc a b → SmoothTwoForm IB B} (hτ : IsSmoothFamily (𝓡∂ 1) τ)
    (hτs : ∀ t, (τ t).IsSymplectic)
    (hcoh : ∀ t s, deRhamCohomology.mk IB 2 ⟨τ t, (hτs t).isClosed.mem_closedForms⟩ -
        deRhamCohomology.mk IB 2 ⟨τ s, (hτs s).isClosed.mem_closedForms⟩ =
      -((t : ℝ) - s) • realFirstChernClass IB P) :
    ∃ σ : SmoothTwoForm ((IB.prod (𝓡 1)).prod (𝓡∂ 1))
        (ManifoldTotalSpace Circle P × Set.Icc a b),
      IsCouplingForm σ τ ∧ σ.IsSymplectic := by
  obtain ⟨α, hα⟩ := exists_isCircleConnectionForm (IB := IB) (P := P)
  let a' : Set.Icc a b := ⟨a, Set.left_mem_Icc.2 (Fact.out : a < b).le⟩
  -- the forms `τ t - τ a - (t - a) (2π)⁻¹ F` are a smooth family of exact forms
  have hη : IsSmoothFamily (𝓡∂ 1) fun t : Set.Icc a b ↦
      τ t - τ a' - ((t : ℝ) - a) • (2 * Real.pi)⁻¹ • hα.curvature :=
    (hτ.sub (isSmoothFamily_const _)).sub ((isSmoothFamily_const _).fun_smul
      (contMDiff_subtypeVal_Icc.sub contMDiff_const))
  have hex (t : Set.Icc a b) :
      τ t - τ a' - ((t : ℝ) - a) • (2 * Real.pi)⁻¹ • hα.curvature ∈ exactForms IB B (1 + 1) := by
    convert (hα.mk_sub_mk_eq_smul_realFirstChernClass_iff _ _ _).1 (hcoh t a') using 1
    module
  obtain ⟨β, hβ, hdβ⟩ :=
    exists_isSmoothFamily_mextDerivₗ_eq hasFiniteGoodCover_of_compactSpace hη hex
  have h := hα.isCouplingForm_couplingForm hβ (hτs a').isClosed hdβ
  exact ⟨_, h, h.isSymplectic fun t ↦ (hτs t).isNondegenerate⟩

end SymplecticGeometry

end
