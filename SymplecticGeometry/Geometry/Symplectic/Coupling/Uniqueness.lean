/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.IntervalContraction
public import SymplecticGeometry.Geometry.Symplectic.Coupling.Basic
import TauCeti.Topology.Algebra.Module.Alternating.Basic

/-!
# Uniqueness of coupling forms

Two coupling forms `ω₀` and `ω₁` on `P × [a, b]` for the same family `τ` of nondegenerate forms
on the base are related by an equivariant diffeomorphism of `P × [a, b]` that preserves the
coordinate `t` of the interval (McDuff–Salamon, Proposition 5.1.9). The proof is Moser's
argument along the segment `ω₀ + s • (ω₁ - ω₀)`, with a primitive of `ω₁ - ω₀` that is invariant
under the circle action and makes the Moser field tangent to the levels `t = const`.

This file builds that primitive. It is `K (ω₁ - ω₀)`, for the homotopy operator `K` of the
contraction of `P × [a, b]` onto its bottom level `P × {a}`
(`SymplecticGeometry.prodIccHomotopyOperator`). The contraction does not move the point of `P`,
so `K η` is invariant under the circle action when `η` is
(`SymplecticGeometry.mpullback_smul_prodIccHomotopyOperator`), and, for a two-form `η`, `K η`
vanishes on the fundamental field `(X, 0)` when `ι_{(X, 0)} η = 0`
(`SymplecticGeometry.prodIccHomotopyOperator_apply_couplingField`).

For two coupling forms for the same family, the difference `δ = ω₁ - ω₀` is closed, invariant,
vanishes on the bottom level and has `ι_{(X, 0)} δ = 0`, so `σ = K δ` is an invariant primitive of
`δ` that vanishes on `(X, 0)`
(`SymplecticGeometry.IsCouplingForm.mextDerivₗ_prodIccHomotopyOperator_sub`,
`SymplecticGeometry.IsCouplingForm.prodIccHomotopyOperator_sub_apply_couplingField`). The forms
`ω₀ + s • δ` are coupling forms (`SymplecticGeometry.IsCouplingForm.lineMap`), hence symplectic
over a family of nondegenerate forms (`SymplecticGeometry.IsCouplingForm.isSymplectic`). A vector
`Y` with `ι_Y η = -σ` at a point, for a coupling form `η`, has `dt(Y) = 0`
(`SymplecticGeometry.IsCouplingForm.mfderiv_snd_eq_zero_of_apply_eq_neg`): the Moser field of
the segment is tangent to the levels of `t`.

No flow is run on the manifold with boundary `P × [a, b]`: the Moser data are first extended to
the boundaryless `P × ℝ`, by the time extension `TauCeti.SmoothForm.timeExtendIcc` and the
extension `SymplecticGeometry.prodIccExtension` of closed forms. Both keep invariance under the
circle action (`SymplecticGeometry.mpullback_smul_timeExtendIcc`,
`SymplecticGeometry.mpullback_smul_prodIccExtension`). For coupling forms `ω₀` and `ω₁` for
the same family, the extension `ω̃₀` of `ω₀` and the time extension `σ̃` of
`σ = K (ω₁ - ω₀)` are invariant under the circle action
(`SymplecticGeometry.IsCouplingForm.mpullback_smul_timeExtendIcc_prodIccHomotopyOperator_sub`).
The form `σ̃` restricts to `σ`, vanishes on the direction of `ℝ`
(`TauCeti.SmoothForm.isFstSemibasic_timeExtendIcc`) and on `(X, 0)`
(`IsCouplingForm.timeExtendIcc_prodIccHomotopyOperator_sub_apply_prodVectorField`).

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Proposition 5.1.9 (uniqueness of coupling forms) and §3.2 (Moser's argument).
-/

public section

noncomputable section

open Bundle Manifold MulOpposite TauCeti Set
open scoped Manifold ContDiff Fact.Manifold

namespace SymplecticGeometry

variable {EB HB B : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  {IB : ModelWithCorners ℝ EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  {P : B → Type*} [TopologicalSpace (TotalSpace Circle P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle Circle P] [∀ b, MulAction Circleᵐᵒᵖ (P b)] [IsManifold IB ∞ B]
  [PrincipalBundle Circle P] [ContMDiffFiberBundle ∞ Circle P IB (𝓡 1)]
  {a b : ℝ} [Fact (a < b)]

/-! ### The homotopy operator and the circle action -/

section Homotopy

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {k : ℕ}

/-- **Invariance of `K η`.** If a form `η` on `P × [a, b]` is invariant under the action of
`z : Circle` on the total space, then so is `K η`. -/
theorem mpullback_smul_prodIccHomotopyOperator (z : Circle)
    {η : SmoothForm ((IB.prod (𝓡 1)).prod (𝓡∂ 1)) (ManifoldTotalSpace Circle P × Icc a b) F
      (k + 1)}
    (hη : SmoothForm.mpullback (fun x : ManifoldTotalSpace Circle P × Icc a b ↦ (op z • x.1, x.2))
      (((contMDiff_const_smul (op z)).comp contMDiff_fst).prodMk contMDiff_snd) η = η) :
    SmoothForm.mpullback (fun x : ManifoldTotalSpace Circle P × Icc a b ↦ (op z • x.1, x.2))
        (((contMDiff_const_smul (op z)).comp contMDiff_fst).prodMk contMDiff_snd)
        (prodIccHomotopyOperator (IB.prod (𝓡 1)) (ManifoldTotalSpace Circle P) a b F k η) =
      prodIccHomotopyOperator (IB.prod (𝓡 1)) (ManifoldTotalSpace Circle P) a b F k η := by
  have hmap : (fun x : ManifoldTotalSpace Circle P × Icc a b ↦ (op z • x.1, x.2)) =
      Prod.map (op z • ·) id :=
    -- `Prod.map f id` sends `x` to `(f x.1, x.2)`, by definition
    rfl
  simp only [hmap] at hη ⊢
  rw [mpullback_prodMap_prodIccHomotopyOperator (contMDiff_const_smul (op z)), hη]

omit [PrincipalBundle Circle P] in
/-- **`K η` vanishes on `(X, 0)` when `η` does.** If the contraction of a two-form `η` on
`P × [a, b]` with the fundamental field `(X, 0)` vanishes, then `K η` vanishes on `(X, 0)`. -/
theorem prodIccHomotopyOperator_apply_couplingField
    {η : SmoothForm ((IB.prod (𝓡 1)).prod (𝓡∂ 1)) (ManifoldTotalSpace Circle P × Icc a b) F 2}
    (hη : ∀ x v, η.val x ![couplingField IB P a b x, v] = 0)
    (x : ManifoldTotalSpace Circle P × Icc a b) :
    (prodIccHomotopyOperator (IB.prod (𝓡 1)) (ManifoldTotalSpace Circle P) a b F 1 η).val x
      ![couplingField IB P a b x] = 0 := by
  refine (prodIccHomotopyOperator_apply_apply η x _).trans ?_
  refine (intervalIntegral.integral_congr (g := fun _ ↦ (0 : F)) fun r _ ↦ ?_).trans
    intervalIntegral.integral_zero
  dsimp only
  generalize projIcc 0 1 zero_le_one r = u
  -- the contraction does not move the point of `P`, so its derivative fixes `(X, 0)`
  have hX : mfderiv (((IB.prod (𝓡 1)).prod (𝓡∂ 1)).prod (𝓡∂ 1)) ((IB.prod (𝓡 1)).prod (𝓡∂ 1))
      (prodIccContraction (ManifoldTotalSpace Circle P) a b) (x, u)
        (couplingField IB P a b x, 0) =
      couplingField IB P a b (prodIccContraction (ManifoldTotalSpace Circle P) a b (x, u)) := by
    have h := mfderiv_prodIccContraction (x, u)
      (rightFundamentalVectorField (IB.prod (𝓡 1)) circlePeriodOneGenerator x.1) 0 0
    rw [zero_smul, zero_smul, mul_zero, mul_zero, add_zero, zero_smul] at h
    rw [couplingField_def, couplingField_def, prodIccContraction_fst]
    -- the zero vectors of the interval's tangent spaces are the zero of the model space
    exact h
  rw [hX, ContinuousAlternatingMap.apply_vecCons_swap, hη, neg_zero]

end Homotopy

/-! ### The extensions to `P × ℝ` and the circle action -/

section Extension

variable [IB.Boundaryless] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

/-- **Invariance of the time extension.** If a form `η` on `P × [a, b]` is invariant under the
action of `z : Circle` on the total space, then so is its time extension to `P × ℝ`
(`TauCeti.SmoothForm.timeExtendIcc`). -/
theorem mpullback_smul_timeExtendIcc (z : Circle)
    {η : SmoothForm ((IB.prod (𝓡 1)).prod (𝓡∂ 1)) (ManifoldTotalSpace Circle P × Icc a b) F k}
    (hη : SmoothForm.mpullback (fun x : ManifoldTotalSpace Circle P × Icc a b ↦ (op z • x.1, x.2))
      (((contMDiff_const_smul (op z)).comp contMDiff_fst).prodMk contMDiff_snd) η = η) :
    SmoothForm.mpullback (fun x : ManifoldTotalSpace Circle P × ℝ ↦ (op z • x.1, x.2))
        (((contMDiff_const_smul (op z)).comp contMDiff_fst).prodMk contMDiff_snd)
        (SmoothForm.timeExtendIcc η) =
      SmoothForm.timeExtendIcc η := by
  have hmap : (fun x : ManifoldTotalSpace Circle P × Icc a b ↦ (op z • x.1, x.2)) =
      Prod.map (op z • ·) id :=
    -- `Prod.map f id` sends `x` to `(f x.1, x.2)`, by definition
    rfl
  have hmap' : (fun x : ManifoldTotalSpace Circle P × ℝ ↦ (op z • x.1, x.2)) =
      Prod.map (op z • ·) id :=
    -- `Prod.map f id` sends `x` to `(f x.1, x.2)`, by definition
    rfl
  simp only [hmap, hmap'] at hη ⊢
  rw [← SmoothForm.timeExtendIcc_mpullback_prodMap (contMDiff_const_smul (op z)), hη]

/-- **Invariance of the extended form.** If a `(k + 1)`-form `η` on `P × [a, b]` is invariant
under the action of `z : Circle` on the total space, then so is its extension to `P × ℝ`
(`SymplecticGeometry.prodIccExtension`). This applies to coupling forms
(`SymplecticGeometry.IsCouplingForm.mpullback_smul`). -/
theorem mpullback_smul_prodIccExtension [CompleteSpace F] (z : Circle)
    {η : SmoothForm ((IB.prod (𝓡 1)).prod (𝓡∂ 1)) (ManifoldTotalSpace Circle P × Icc a b) F
      (k + 1)}
    (hη : SmoothForm.mpullback (fun x : ManifoldTotalSpace Circle P × Icc a b ↦ (op z • x.1, x.2))
      (((contMDiff_const_smul (op z)).comp contMDiff_fst).prodMk contMDiff_snd) η = η) :
    SmoothForm.mpullback (fun x : ManifoldTotalSpace Circle P × ℝ ↦ (op z • x.1, x.2))
        (((contMDiff_const_smul (op z)).comp contMDiff_fst).prodMk contMDiff_snd)
        (prodIccExtension (IB.prod (𝓡 1)) (ManifoldTotalSpace Circle P) a b F k η) =
      prodIccExtension (IB.prod (𝓡 1)) (ManifoldTotalSpace Circle P) a b F k η := by
  have hmap : (fun x : ManifoldTotalSpace Circle P × Icc a b ↦ (op z • x.1, x.2)) =
      Prod.map (op z • ·) id :=
    -- `Prod.map f id` sends `x` to `(f x.1, x.2)`, by definition
    rfl
  have hmap' : (fun x : ManifoldTotalSpace Circle P × ℝ ↦ (op z • x.1, x.2)) =
      Prod.map (op z • ·) id :=
    -- `Prod.map f id` sends `x` to `(f x.1, x.2)`, by definition
    rfl
  simp only [hmap, hmap'] at hη ⊢
  rw [mpullback_prodMap_prodIccExtension (contMDiff_const_smul (op z)), hη]

end Extension

/-! ### The primitive of the difference of two coupling forms -/

namespace IsCouplingForm

variable {η ω₀ ω₁ :
    SmoothTwoForm ((IB.prod (𝓡 1)).prod (𝓡∂ 1)) (ManifoldTotalSpace Circle P × Icc a b)}
  {τ : Icc a b → SmoothTwoForm IB B}

/-- Two coupling forms for the same family agree on the bottom level: the pull-back of their
difference along the projection `(p, t) ↦ (p, a)` vanishes. -/
theorem mpullback_bot_sub (h₀ : IsCouplingForm ω₀ τ) (h₁ : IsCouplingForm ω₁ τ) :
    SmoothForm.mpullback (I := (IB.prod (𝓡 1)).prod (𝓡∂ 1)) (I' := (IB.prod (𝓡 1)).prod (𝓡∂ 1))
      (fun x : ManifoldTotalSpace Circle P × Icc a b ↦ (x.1, ⊥))
      (contMDiff_fst.prodMk contMDiff_const) (ω₁ - ω₀) = 0 := by
  have hp := SmoothForm.mpullback_mpullback (I := (IB.prod (𝓡 1)).prod (𝓡∂ 1))
    (I' := IB.prod (𝓡 1)) (I'' := (IB.prod (𝓡 1)).prod (𝓡∂ 1))
    (Prod.fst : ManifoldTotalSpace Circle P × Icc a b → ManifoldTotalSpace Circle P)
    (fun p : ManifoldTotalSpace Circle P ↦ (p, (⊥ : Icc a b)))
    contMDiff_fst (contMDiff_id.prodMk contMDiff_const) (ω₁ - ω₀)
  -- the projection to the bottom level factors through the projection to `P`
  have hb : (fun p : ManifoldTotalSpace Circle P ↦ (p, (⊥ : Icc a b))) ∘ Prod.fst =
      fun x : ManifoldTotalSpace Circle P × Icc a b ↦ (x.1, ⊥) :=
    rfl
  simp only [hb] at hp
  rw [← hp, map_sub, h₀.mpullback_slice, h₁.mpullback_slice, sub_self, map_zero]

/-- **The primitive of the difference.** For two coupling forms `ω₀` and `ω₁` for the same
family, `K (ω₁ - ω₀)` is a primitive of `ω₁ - ω₀`. -/
theorem mextDerivₗ_prodIccHomotopyOperator_sub (h₀ : IsCouplingForm ω₀ τ)
    (h₁ : IsCouplingForm ω₁ τ) :
    mextDerivₗ ((IB.prod (𝓡 1)).prod (𝓡∂ 1)) 1
        (prodIccHomotopyOperator (IB.prod (𝓡 1)) (ManifoldTotalSpace Circle P) a b ℝ 1
          (ω₁ - ω₀)) =
      ω₁ - ω₀ := by
  rw [mextDerivₗ_prodIccHomotopyOperator
      ((SmoothForm.isClosed_iff_mextDerivₗ_eq_zero _).mp (h₁.isClosed.sub h₀.isClosed)),
    mpullback_bot_sub h₀ h₁, sub_zero]

/-- The primitive `K (ω₁ - ω₀)` of the difference of two coupling forms is invariant under the
circle action. -/
theorem mpullback_smul_prodIccHomotopyOperator_sub (h₀ : IsCouplingForm ω₀ τ)
    (h₁ : IsCouplingForm ω₁ τ) (z : Circle) :
    SmoothForm.mpullback (fun x : ManifoldTotalSpace Circle P × Icc a b ↦ (op z • x.1, x.2))
        (((contMDiff_const_smul (op z)).comp contMDiff_fst).prodMk contMDiff_snd)
        (prodIccHomotopyOperator (IB.prod (𝓡 1)) (ManifoldTotalSpace Circle P) a b ℝ 1
          (ω₁ - ω₀)) =
      prodIccHomotopyOperator (IB.prod (𝓡 1)) (ManifoldTotalSpace Circle P) a b ℝ 1 (ω₁ - ω₀) :=
  mpullback_smul_prodIccHomotopyOperator z
    (by rw [map_sub, h₀.mpullback_smul, h₁.mpullback_smul])

/-- The primitive `K (ω₁ - ω₀)` of the difference of two coupling forms vanishes on the
fundamental field `(X, 0)`, since both forms have the same contraction `-dt` with it. -/
theorem prodIccHomotopyOperator_sub_apply_couplingField (h₀ : IsCouplingForm ω₀ τ)
    (h₁ : IsCouplingForm ω₁ τ) (x : ManifoldTotalSpace Circle P × Icc a b) :
    (prodIccHomotopyOperator (IB.prod (𝓡 1)) (ManifoldTotalSpace Circle P) a b ℝ 1
      (ω₁ - ω₀)).val x ![couplingField IB P a b x] = 0 :=
  prodIccHomotopyOperator_apply_couplingField (fun y v ↦ by
    simp only [Submodule.coe_sub, Pi.sub_apply, ContinuousAlternatingMap.sub_apply,
      h₀.apply_couplingField, h₁.apply_couplingField]
    exact sub_self _) x

/-- **The Moser field is tangent to the levels of `t`.** Let `η` be a coupling form and `σ` a
one-form that vanishes on the fundamental field `(X, 0)` at a point `x`. A tangent vector `Y` at
`x` with `ι_Y η = -σ` there has `dt(Y) = 0`. -/
theorem mfderiv_snd_eq_zero_of_apply_eq_neg (h : IsCouplingForm η τ)
    {σ : SmoothForm ((IB.prod (𝓡 1)).prod (𝓡∂ 1)) (ManifoldTotalSpace Circle P × Icc a b) ℝ 1}
    {x : ManifoldTotalSpace Circle P × Icc a b}
    (hσ : σ.val x ![couplingField IB P a b x] = 0)
    {Y : TangentSpace ((IB.prod (𝓡 1)).prod (𝓡∂ 1)) x}
    (hY : ∀ v, η.val x ![Y, v] = -σ.val x ![v]) :
    mfderiv ((IB.prod (𝓡 1)).prod (𝓡∂ 1)) 𝓘(ℝ)
      (fun y : ManifoldTotalSpace Circle P × Icc a b ↦ (y.2 : ℝ)) x Y = 0 := by
  have hX := h.apply_couplingField x Y
  rw [ContinuousAlternatingMap.apply_vecCons_swap, hY, hσ, neg_zero, neg_zero] at hX
  exact neg_eq_zero.mp hX.symm

/-! ### The extended Moser data on `P × ℝ` -/

section Extension

variable [IB.Boundaryless]

/-- **Invariance of the extended primitive.** For two coupling forms `ω₀` and `ω₁` for the same
family, the extension to `P × ℝ` of the primitive `K (ω₁ - ω₀)` is invariant under the action of
every `z : Circle` on the total space. -/
theorem mpullback_smul_timeExtendIcc_prodIccHomotopyOperator_sub (h₀ : IsCouplingForm ω₀ τ)
    (h₁ : IsCouplingForm ω₁ τ) (z : Circle) :
    SmoothForm.mpullback (fun x : ManifoldTotalSpace Circle P × ℝ ↦ (op z • x.1, x.2))
        (((contMDiff_const_smul (op z)).comp contMDiff_fst).prodMk contMDiff_snd)
        (SmoothForm.timeExtendIcc
          (prodIccHomotopyOperator (IB.prod (𝓡 1)) (ManifoldTotalSpace Circle P) a b ℝ 1
            (ω₁ - ω₀))) =
      SmoothForm.timeExtendIcc
        (prodIccHomotopyOperator (IB.prod (𝓡 1)) (ManifoldTotalSpace Circle P) a b ℝ 1
          (ω₁ - ω₀)) :=
  mpullback_smul_timeExtendIcc z (mpullback_smul_prodIccHomotopyOperator_sub h₀ h₁ z)

/-- **The extended primitive vanishes on `(X, 0)`.** For two coupling forms `ω₀` and `ω₁` for the
same family, the extension to `P × ℝ` of the primitive `K (ω₁ - ω₀)` vanishes on the field
`(X, 0)`, where `X` is the period-one fundamental vector field of the circle action. -/
theorem timeExtendIcc_prodIccHomotopyOperator_sub_apply_prodVectorField
    (h₀ : IsCouplingForm ω₀ τ) (h₁ : IsCouplingForm ω₁ τ) (p : ManifoldTotalSpace Circle P × ℝ) :
    (SmoothForm.timeExtendIcc
        (prodIccHomotopyOperator (IB.prod (𝓡 1)) (ManifoldTotalSpace Circle P) a b ℝ 1
          (ω₁ - ω₀))).val p
      ![Manifold.prodVectorField
        (rightFundamentalVectorField (IB.prod (𝓡 1)) circlePeriodOneGenerator) 0 p] = 0 := by
  refine SmoothForm.timeExtendIcc_apply_cons_prodVectorField_eq_zero _ (fun q w ↦ ?_) p ![]
  have hX : Manifold.prodVectorField
      (rightFundamentalVectorField (IB.prod (𝓡 1)) circlePeriodOneGenerator) 0 q =
      couplingField IB P a b q :=
    Prod.ext (by rw [Manifold.prodVectorField_fst, couplingField_fst]) (by
      rw [Manifold.prodVectorField_snd, couplingField_snd, Pi.zero_apply]
      -- the zero of the tangent space of the interval is the zero of its model space
      rfl)
  rw [hX, Subsingleton.elim w ![]]
  exact prodIccHomotopyOperator_sub_apply_couplingField h₀ h₁ q

end Extension

end IsCouplingForm

end SymplecticGeometry

end
