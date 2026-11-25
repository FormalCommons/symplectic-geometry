/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.IntervalContraction
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.TimeExtension
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
the boundaryless `P × ℝ`. For a boundaryless manifold `M`, a closed form `η` on `M × [a, b]` is
`pr^* ι_a^* η + d (K η)`, where `pr^* ι_a^*` is the pull-back along `(x, t) ↦ (x, a)`. When `η`
is a two-form, `K η` has no component along the interval, so it is the restriction to
`M × [a, b]` of its time extension to `M × ℝ` (`TauCeti.SmoothForm.timeExtendIcc`,
`SymplecticGeometry.mpullback_prodMap_subtypeVal_timeExtendIcc_prodIccHomotopyOperator`).
Replacing `K η` by its time extension gives a closed form on `M × ℝ`
(`SymplecticGeometry.prodIccExtension`, `SymplecticGeometry.isClosed_prodIccExtension`) that
commutes with pull-back along `f × id` (`SymplecticGeometry.mpullback_prodMap_prodIccExtension`)
and restricts to `η` on `M × [a, b]`
(`SymplecticGeometry.mpullback_prodMap_subtypeVal_prodIccExtension`). For coupling forms `ω₀`
and `ω₁` for the same family, the extension `ω̃₀` of `ω₀` and the time extension `σ̃` of
`σ = K (ω₁ - ω₀)` are invariant under the circle action
(`SymplecticGeometry.mpullback_smul_prodIccExtension`,
`SymplecticGeometry.IsCouplingForm.mpullback_smul_timeExtendIcc_prodIccHomotopyOperator_sub`).
The form `σ̃` restricts to `σ`, vanishes on the direction of `ℝ`
(`TauCeti.SmoothForm.timeExtendIcc_apply_eq_zero`) and on `(X, 0)`
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

/-! ### The extension of a closed form to `M × ℝ` -/

section Extension

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H} [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {k : ℕ}

/-- **The extension of a form on `M × [a, b]` to `M × ℝ`.** For a boundaryless manifold `M`, it
sends a `(k + 1)`-form `η` on `M × Icc a b` to `pr^* ι_a^* η + d (ext (K η))` on `M × ℝ`, where
`pr^* ι_a^*` is the pull-back along `(x, t) ↦ (x, a)`, `K` is
`SymplecticGeometry.prodIccHomotopyOperator` and `ext` is the time extension
`TauCeti.SmoothForm.timeExtendIcc`. When `η` is closed, this form is closed
(`SymplecticGeometry.isClosed_prodIccExtension`), and for a closed two-form `η` it restricts to
`η` on `M × [a, b]` (`SymplecticGeometry.mpullback_prodMap_subtypeVal_prodIccExtension`). -/
def prodIccExtension (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M] [BoundarylessManifold I M] (a b : ℝ) [Fact (a < b)]
    (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (k : ℕ) :
    SmoothForm (I.prod (𝓡∂ 1)) (M × Icc a b) F (k + 1) →ₗ[ℝ]
      SmoothForm (I.prod 𝓘(ℝ, ℝ)) (M × ℝ) F (k + 1) :=
  SmoothForm.mpullback (fun x : M × ℝ ↦ (x.1, (⊥ : Icc a b)))
      (contMDiff_fst.prodMk contMDiff_const) +
    mextDerivₗ (I.prod 𝓘(ℝ, ℝ)) k ∘ₗ SmoothForm.timeExtendIcc ∘ₗ
      prodIccHomotopyOperator I M a b F k

theorem prodIccExtension_apply (η : SmoothForm (I.prod (𝓡∂ 1)) (M × Icc a b) F (k + 1)) :
    prodIccExtension I M a b F k η =
      SmoothForm.mpullback (fun x : M × ℝ ↦ (x.1, (⊥ : Icc a b)))
          (contMDiff_fst.prodMk contMDiff_const) η +
        mextDerivₗ (I.prod 𝓘(ℝ, ℝ)) k
          (SmoothForm.timeExtendIcc (prodIccHomotopyOperator I M a b F k η)) :=
  (rfl)

/-- The extension of a closed form on `M × [a, b]` to `M × ℝ` is closed. -/
theorem isClosed_prodIccExtension {η : SmoothForm (I.prod (𝓡∂ 1)) (M × Icc a b) F (k + 1)}
    (hη : η.IsClosed) : (prodIccExtension I M a b F k η).IsClosed := by
  rw [prodIccExtension_apply]
  exact (hη.mpullback _ _).add (SmoothForm.isClosed_mextDerivₗ _)

/-- **Naturality of the extension to `M × ℝ`.** For a smooth map `f : N → M` of boundaryless
manifolds, pulling the extension of `η` back along `f × id` gives the extension of the pull-back
of `η` along `f × id`. -/
theorem mpullback_prodMap_prodIccExtension {E' H' N : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace N]
    [ChartedSpace H' N] [IsManifold I' ∞ N] [BoundarylessManifold I' N] {f : N → M}
    (hf : ContMDiff I' I ∞ f) (η : SmoothForm (I.prod (𝓡∂ 1)) (M × Icc a b) F (k + 1)) :
    SmoothForm.mpullback (Prod.map f id) (hf.prodMap contMDiff_id)
        (prodIccExtension I M a b F k η) =
      prodIccExtension I' N a b F k
        (SmoothForm.mpullback (Prod.map f id) (hf.prodMap contMDiff_id) η) := by
  rw [prodIccExtension_apply, prodIccExtension_apply, map_add, ← SmoothForm.mextDerivₗ_mpullback,
    ← SmoothForm.timeExtendIcc_mpullback_prodMap hf, mpullback_prodMap_prodIccHomotopyOperator hf]
  congr 1
  exact SmoothForm.mpullback_mpullback_of_comp_eq (hf.prodMap contMDiff_id)
    (contMDiff_fst.prodMk contMDiff_const) (contMDiff_fst.prodMk contMDiff_const)
    (hf.prodMap contMDiff_id) (funext fun _ ↦ rfl) η

/-- The extension of `K η` to `M × ℝ`, for a two-form `η` on `M × [a, b]`, restricts to `K η` on
`M × [a, b]`: `K η` has no component along the interval. -/
theorem mpullback_prodMap_subtypeVal_timeExtendIcc_prodIccHomotopyOperator
    (η : SmoothForm (I.prod (𝓡∂ 1)) (M × Icc a b) F 2) :
    SmoothForm.mpullback (Prod.map id Subtype.val) (contMDiff_id.prodMap contMDiff_subtypeVal_Icc)
        (SmoothForm.timeExtendIcc (prodIccHomotopyOperator I M a b F 1 η)) =
      prodIccHomotopyOperator I M a b F 1 η :=
  SmoothForm.mpullback_prodMap_subtypeVal_timeExtendIcc _
    (prodIccHomotopyOperator_apply_eq_zero η)

/-- **Restriction of the extension.** The extension to `M × ℝ` of a closed two-form `η` on
`M × [a, b]` restricts to `η` on `M × [a, b]`. -/
theorem mpullback_prodMap_subtypeVal_prodIccExtension
    {η : SmoothForm (I.prod (𝓡∂ 1)) (M × Icc a b) F 2} (hη : η.IsClosed) :
    SmoothForm.mpullback (Prod.map id Subtype.val) (contMDiff_id.prodMap contMDiff_subtypeVal_Icc)
        (prodIccExtension I M a b F 1 η) = η := by
  rw [prodIccExtension_apply, map_add, ← SmoothForm.mextDerivₗ_mpullback,
    mpullback_prodMap_subtypeVal_timeExtendIcc_prodIccHomotopyOperator,
    mextDerivₗ_prodIccHomotopyOperator ((SmoothForm.isClosed_iff_mextDerivₗ_eq_zero _).mp hη),
    SmoothForm.mpullback_mpullback,
    SmoothForm.mpullback_congr
      (f := (fun x : M × ℝ ↦ (x.1, (⊥ : Icc a b))) ∘ Prod.map id Subtype.val)
      (g := fun x : M × Icc a b ↦ (x.1, ⊥)) _ (contMDiff_fst.prodMk contMDiff_const)
      (funext fun _ ↦ rfl),
    add_sub_cancel]

end Extension

/-- **Invariance of the extended form.** If a two-form `η` on `P × [a, b]` is invariant under the
action of `z : Circle` on the total space, then so is its extension to `P × ℝ`
(`SymplecticGeometry.prodIccExtension`). This applies to coupling forms
(`SymplecticGeometry.IsCouplingForm.mpullback_smul`). -/
theorem mpullback_smul_prodIccExtension [IB.Boundaryless] (z : Circle)
    {η : SmoothTwoForm ((IB.prod (𝓡 1)).prod (𝓡∂ 1)) (ManifoldTotalSpace Circle P × Icc a b)}
    (hη : SmoothForm.mpullback
      (fun x : ManifoldTotalSpace Circle P × Icc a b ↦ (op z • x.1, x.2))
      (((contMDiff_const_smul (op z)).comp contMDiff_fst).prodMk contMDiff_snd) η = η) :
    SmoothForm.mpullback (fun x : ManifoldTotalSpace Circle P × ℝ ↦ (op z • x.1, x.2))
        (((contMDiff_const_smul (op z)).comp contMDiff_fst).prodMk contMDiff_snd)
        (prodIccExtension (IB.prod (𝓡 1)) (ManifoldTotalSpace Circle P) a b ℝ 1 η) =
      prodIccExtension (IB.prod (𝓡 1)) (ManifoldTotalSpace Circle P) a b ℝ 1 η := by
  -- `Prod.map f id` sends `x` to `(f x.1, x.2)`, by definition
  rw [SmoothForm.mpullback_congr
      (f := fun x : ManifoldTotalSpace Circle P × ℝ ↦ (op z • x.1, x.2))
      (g := Prod.map (op z • ·) id) _
      ((contMDiff_const_smul (op z)).prodMap contMDiff_id) (funext fun _ ↦ rfl),
    mpullback_prodMap_prodIccExtension (contMDiff_const_smul (op z)),
    SmoothForm.mpullback_congr (f := Prod.map (op z • ·) id)
      (g := fun x : ManifoldTotalSpace Circle P × Icc a b ↦ (op z • x.1, x.2)) _
      (((contMDiff_const_smul (op z)).comp contMDiff_fst).prodMk contMDiff_snd)
      (funext fun _ ↦ rfl), hη]

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
          (ω₁ - ω₀)) := by
  -- `Prod.map f id` sends `x` to `(f x.1, x.2)`, by definition
  rw [SmoothForm.mpullback_congr
      (f := fun x : ManifoldTotalSpace Circle P × ℝ ↦ (op z • x.1, x.2))
      (g := Prod.map (op z • ·) id) _
      ((contMDiff_const_smul (op z)).prodMap contMDiff_id) (funext fun _ ↦ rfl),
    ← SmoothForm.timeExtendIcc_mpullback_prodMap (contMDiff_const_smul (op z)),
    SmoothForm.mpullback_congr (f := Prod.map (op z • ·) id)
      (g := fun x : ManifoldTotalSpace Circle P × Icc a b ↦ (op z • x.1, x.2)) _
      (((contMDiff_const_smul (op z)).comp contMDiff_fst).prodMk contMDiff_snd)
      (funext fun _ ↦ rfl), mpullback_smul_prodIccHomotopyOperator_sub h₀ h₁]

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
