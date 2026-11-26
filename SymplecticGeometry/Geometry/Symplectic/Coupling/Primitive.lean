/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.IntervalContraction
public import SymplecticGeometry.Geometry.Symplectic.Coupling.Basic
import SymplecticGeometry.Geometry.Manifold.VectorField.Prod

/-!
# The invariant primitive of the difference of two coupling forms

The first steps of the uniqueness of coupling forms (McDuff–Salamon, Proposition 5.1.9), which
`Coupling/Uniqueness.lean` completes: for two coupling forms `ω₀` and `ω₁` on `P × [a, b]` for
the same family of forms on the base, a primitive of `ω₁ - ω₀` that is invariant under the circle
action and vanishes on the fundamental field `(X, 0)`, and the facts about the extensions to
`P × ℝ` that do not involve the Moser flow.

## Main results

* `SymplecticGeometry.mpullback_smul_prodIccHomotopyOperator`: the homotopy operator `K` of the
  contraction of `P × [a, b]` onto `P × {a}` (`SymplecticGeometry.prodIccHomotopyOperator`)
  takes invariant forms to invariant forms, since the contraction does not move the point of `P`.
* `SymplecticGeometry.prodIccHomotopyOperator_apply_couplingField`: for a two-form `η` with
  `ι_{(X, 0)} η = 0`, the one-form `K η` vanishes on `(X, 0)`.
* `SymplecticGeometry.mpullback_smul_timeExtendIcc`,
  `SymplecticGeometry.mpullback_smul_prodIccExtension`: the time extension
  `TauCeti.SmoothForm.timeExtendIcc` and the extension `SymplecticGeometry.prodIccExtension` of
  closed forms to `P × ℝ` keep invariance under the circle action.
* `SymplecticGeometry.IsCouplingForm.mextDerivₗ_prodIccHomotopyOperator_sub`,
  `SymplecticGeometry.IsCouplingForm.mpullback_smul_prodIccHomotopyOperator_sub`,
  `SymplecticGeometry.IsCouplingForm.prodIccHomotopyOperator_sub_apply_couplingField`: for two
  coupling forms for the same family, `σ = K (ω₁ - ω₀)` is a primitive of `ω₁ - ω₀`, invariant
  under the circle action, that vanishes on `(X, 0)`.
* `SymplecticGeometry.IsCouplingForm.prodIccHomotopyOperator_apply_couplingField_eq_sub`: for a
  coupling form `η`, the one-form `K η` takes the value `t - a` on `(X, 0)`.
* `SymplecticGeometry.IsCouplingForm.mfderiv_snd_eq_zero_of_apply_eq_neg`: a vector `Y` with
  `ι_Y η = -σ` at a point, for a coupling form `η` and a one-form `σ` that vanishes on `(X, 0)`
  there, has `dt(Y) = 0`, so the Moser field of the segment `ω₀ + s • (ω₁ - ω₀)` is tangent to the
  levels of `t`.
* `SymplecticGeometry.IsCouplingForm.mpullback_bot_apply_prodVectorField_eq_zero`: the pull-back
  of a coupling form along the projection of `P × ℝ` onto the bottom level vanishes on `(X, 0)`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Proposition 5.1.9 (uniqueness of coupling forms).
-/

public section

noncomputable section

open Bundle Manifold MulOpposite TauCeti Set
open scoped Manifold ContDiff Fact.Manifold Topology

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
      Prod.map (op z • ·) id := by
    simp only [Prod.map_def, id_eq]
  simp only [hmap] at hη ⊢
  rw [mpullback_prodMap_prodIccHomotopyOperator (contMDiff_const_smul (op z)), hη]

omit [IsManifold IB ∞ B] [PrincipalBundle Circle P] [ContMDiffFiberBundle ∞ Circle P IB (𝓡 1)] in
/-- The fundamental field `(X, 0)` on `P × [a, b]` is the product of the period-one fundamental
vector field on `P` with the zero field on the interval. -/
theorem prodVectorField_eq_couplingField (x : ManifoldTotalSpace Circle P × Icc a b) :
    Manifold.prodVectorField
        (rightFundamentalVectorField (IB.prod (𝓡 1)) circlePeriodOneGenerator) 0 x =
      couplingField IB P a b x := by
  rw [Manifold.prodVectorField_apply, couplingField_def, Pi.zero_apply]
  -- the zero of the tangent space of the interval is the zero of its model space
  rfl

omit [IsManifold IB ∞ B] [PrincipalBundle Circle P] [ContMDiffFiberBundle ∞ Circle P IB (𝓡 1)] in
/-- The contraction of `P × [a, b]` onto its bottom level does not move the point of `P`, so its
derivative sends the fundamental field `(X, 0)` at `(x, u)` to `(X, 0)` at the image point. -/
theorem mfderiv_prodIccContraction_couplingField (x : ManifoldTotalSpace Circle P × Icc a b)
    (u : unitInterval) :
    mfderiv (((IB.prod (𝓡 1)).prod (𝓡∂ 1)).prod (𝓡∂ 1)) ((IB.prod (𝓡 1)).prod (𝓡∂ 1))
        (prodIccContraction (ManifoldTotalSpace Circle P) a b) (x, u)
        (couplingField IB P a b x, 0) =
      couplingField IB P a b (prodIccContraction (ManifoldTotalSpace Circle P) a b (x, u)) := by
  have h := mfderiv_prodIccContraction (x, u)
    (rightFundamentalVectorField (IB.prod (𝓡 1)) circlePeriodOneGenerator x.1) 0 0
  rw [zero_smul, zero_smul, mul_zero, mul_zero, add_zero, zero_smul] at h
  rw [couplingField_def, couplingField_def, prodIccContraction_fst]
  -- the zero vectors of the interval's tangent spaces are the zero of the model space
  exact h

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
  -- the family of the one vector `(X, 0)` is `![(X, 0)]`
  simp only [Matrix.cons_val_fin_one]
  rw [mfderiv_prodIccContraction_couplingField]
  simp only [← Matrix.vec_single_eq_const]
  rw [ContinuousAlternatingMap.apply_vecCons_swap, hη, neg_zero]

end Homotopy

/-! ### The extensions to `P × ℝ` and the circle action -/

section Extension

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

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
      Prod.map (op z • ·) id := by
    simp only [Prod.map_def, id_eq]
  have hmap' : (fun x : ManifoldTotalSpace Circle P × ℝ ↦ (op z • x.1, x.2)) =
      Prod.map (op z • ·) id := by
    simp only [Prod.map_def, id_eq]
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
      Prod.map (op z • ·) id := by
    simp only [Prod.map_def, id_eq]
  have hmap' : (fun x : ManifoldTotalSpace Circle P × ℝ ↦ (op z • x.1, x.2)) =
      Prod.map (op z • ·) id := by
    simp only [Prod.map_def, id_eq]
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

/-- **The contraction of `K η` with `(X, 0)` is the height.** For a coupling form `η`, the one-form
`K η` takes the value `t - a` on the fundamental field `(X, 0)` at a point `(x, t)`. -/
theorem prodIccHomotopyOperator_apply_couplingField_eq_sub (h : IsCouplingForm η τ)
    (x : ManifoldTotalSpace Circle P × Icc a b) :
    (prodIccHomotopyOperator (IB.prod (𝓡 1)) (ManifoldTotalSpace Circle P) a b ℝ 1 η).val x
      ![couplingField IB P a b x] = (x.2 : ℝ) - a := by
  refine (prodIccHomotopyOperator_apply_apply η x _).trans ?_
  refine (intervalIntegral.integral_congr (g := fun _ ↦ (x.2 : ℝ) - a) fun r _ ↦ ?_).trans
    (by simp)
  dsimp only
  generalize projIcc 0 1 zero_le_one r = u
  -- the image of the unit time vector is `t - a` times the unit vector of the interval
  have h₁ : mfderiv (((IB.prod (𝓡 1)).prod (𝓡∂ 1)).prod (𝓡∂ 1)) ((IB.prod (𝓡 1)).prod (𝓡∂ 1))
      (prodIccContraction (ManifoldTotalSpace Circle P) a b) (x, u)
      ((0 : TangentSpace ((IB.prod (𝓡 1)).prod (𝓡∂ 1)) x), (1 : TangentSpace (𝓡∂ 1) u)) =
      ((0 : TangentSpace (IB.prod (𝓡 1)) x.1), ((u : ℝ) * 0 + ((x.2 : ℝ) - a) * 1) •
        (1 : TangentSpace (𝓡∂ 1)
          (prodIccContraction (ManifoldTotalSpace Circle P) a b (x, u)).2)) := by
    have h := mfderiv_prodIccContraction (x, u) (0 : TangentSpace (IB.prod (𝓡 1)) x.1) 0 1
    rw [zero_smul, one_smul] at h
    -- `0 : TangentSpace _ x` is the pair of zeros, by definition
    exact h
  -- the family of the one vector `(X, 0)` is `![(X, 0)]`
  simp only [Matrix.cons_val_fin_one]
  rw [mfderiv_prodIccContraction_couplingField]
  simp only [← Matrix.vec_single_eq_const]
  rw [ContinuousAlternatingMap.apply_vecCons_swap,
    h.apply_couplingField_eq_neg_mfderiv_snd, h₁]
  -- the values of the forms and of `mfderiv Subtype.val` are real numbers
  exact (congrArg (fun c : ℝ ↦ -(-c)) (mfderiv_subtypeVal_Icc_smul_one _ _)).trans (by ring)

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

/-- **The pull-back to the bottom level vanishes on `(X, 0)`.** For a coupling form `η`, the
pull-back of `η` along the projection `(x, t) ↦ (x, a)` of `P × ℝ` onto the bottom level vanishes
on the field `(X, 0)`: the projection sends `(X, 0)` to `(X, 0)`, and every tangent vector to one
with no component along the interval. -/
theorem mpullback_bot_apply_prodVectorField_eq_zero (h : IsCouplingForm η τ)
    (p : ManifoldTotalSpace Circle P × ℝ) (w : TangentSpace ((IB.prod (𝓡 1)).prod 𝓘(ℝ, ℝ)) p) :
    (SmoothForm.mpullback (fun x : ManifoldTotalSpace Circle P × ℝ ↦ (x.1, (⊥ : Icc a b)))
      (contMDiff_fst.prodMk contMDiff_const) η).val p
      ![Manifold.prodVectorField
        (rightFundamentalVectorField (IB.prod (𝓡 1)) circlePeriodOneGenerator) 0 p, w] = 0 := by
  -- the projection keeps the component along `P` and kills the one along `ℝ`
  have hpr : ∀ v : TangentSpace ((IB.prod (𝓡 1)).prod 𝓘(ℝ, ℝ)) p,
      mfderiv ((IB.prod (𝓡 1)).prod 𝓘(ℝ, ℝ)) ((IB.prod (𝓡 1)).prod (𝓡∂ 1))
        (fun x : ManifoldTotalSpace Circle P × ℝ ↦ (x.1, (⊥ : Icc a b))) p v =
      ((v.1, 0) : TangentSpace ((IB.prod (𝓡 1)).prod (𝓡∂ 1)) (p.1, (⊥ : Icc a b))) := by
    intro v
    rw [mfderiv_prodMk mdifferentiableAt_fst mdifferentiableAt_const, mfderiv_const]
    exact Prod.ext (mfderiv_fst_apply p v) rfl
  have hX0 : mfderiv ((IB.prod (𝓡 1)).prod 𝓘(ℝ, ℝ)) ((IB.prod (𝓡 1)).prod (𝓡∂ 1))
      (fun x : ManifoldTotalSpace Circle P × ℝ ↦ (x.1, (⊥ : Icc a b))) p
      (Manifold.prodVectorField
        (rightFundamentalVectorField (IB.prod (𝓡 1)) circlePeriodOneGenerator) 0 p) =
      couplingField IB P a b (p.1, ⊥) := by
    rw [hpr, couplingField_def, Manifold.prodVectorField_fst]
    -- `(p.1, ⊥).1` is `p.1`, and the zeros of the tangent spaces of the interval agree
    rfl
  rw [SmoothForm.coe_mpullback, TauCeti.mpullback_apply_pair, hX0, hpr w]
  refine (h.apply_couplingField_eq_neg_mfderiv_snd _ _).trans ?_
  -- the second component of `(w.1, 0)` is the zero vector
  exact neg_eq_zero.mpr (map_zero _)

end IsCouplingForm

end SymplecticGeometry

end
