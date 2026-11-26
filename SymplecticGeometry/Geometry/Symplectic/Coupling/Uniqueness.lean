/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Moser.Field
public import SymplecticGeometry.Geometry.Symplectic.Coupling.Basic
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.IntervalContraction
import SymplecticGeometry.Geometry.Symplectic.Coupling.Primitive
import SymplecticGeometry.Geometry.Manifold.VectorField.Prod
import SymplecticGeometry.Geometry.Manifold.Diffeomorph.Prod.Basic
import SymplecticGeometry.Geometry.Manifold.Diffeomorph.Prod.Icc
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Pullback.LocalDiffeomorph
import SymplecticGeometry.Geometry.Symplectic.Manifold.Family
import SymplecticGeometry.Geometry.Symplectic.Moser.Equivariant
import TauCeti.Geometry.Manifold.PartitionOfUnity.Compact
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.ProdIcc
import SymplecticGeometry.Geometry.Manifold.FiberBundle.Principal.BasicForm
import SymplecticGeometry.Geometry.Manifold.Flow.TimeDependent

/-!
# Uniqueness of coupling forms

Two coupling forms `ω₀` and `ω₁` on `P × [a, b]` for the same family `τ` of nondegenerate forms
on the base are related by an equivariant diffeomorphism of `P × [a, b]` that preserves the
coordinate `t` of the interval (McDuff–Salamon, Proposition 5.1.9). The proof is Moser's
argument along the segment `ω₀ + s • (ω₁ - ω₀)`, with a primitive of `ω₁ - ω₀` that is invariant
under the circle action and makes the Moser field tangent to the levels `t = const`.

The primitive and its properties, and the invariance of the extensions to `P × ℝ`, are in
`Coupling/Primitive.lean`; this file builds the extended Moser flow on them.

The primitive is `K (ω₁ - ω₀)`, for the homotopy operator `K` of the
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
(`TauCeti.SmoothForm.isSemibasic_fst_timeExtendIcc`) and on `(X, 0)`
(`IsCouplingForm.timeExtendIcc_prodIccHomotopyOperator_sub_apply_prodVectorField`).

For a coupling form `ω₀`, `K ω₀` takes the value `t - a` on `(X, 0)`
(`SymplecticGeometry.IsCouplingForm.prodIccHomotopyOperator_apply_couplingField_eq_sub`): the
contraction moves the point of the interval from `a` to `t` and fixes `(X, 0)`, on which `ω₀`
is `-dt`. The time extension `A` of `K ω₀` is invariant, so Cartan's formula
(`TauCeti.PrincipalBundle.mextDeriv_apply_rightFundamentalVectorField_prod`) gives
`ι_{(X, 0)} dA = -d (A (X, 0)) = -de`, where `e` is the time extension of the height `t - a`
(`SymplecticGeometry.prodIccHeight`). The first summand of `ω̃₀` vanishes on `(X, 0)`, since the
projection to the bottom level fixes the point of `P` and kills the direction of the interval
(`SymplecticGeometry.IsCouplingForm.mpullback_bot_apply_prodVectorField_eq_zero`), so
`ι_{(X, 0)} ω̃₀ = -de` (`SymplecticGeometry.IsCouplingForm.prodIccExtension_apply_prodVectorField`),
and `de = dt` over `[a, b]` (`SymplecticGeometry.mextDerivₗ_timeExtendIcc_prodIccHeight_apply`).

The extended Moser segment is `ω̃₀ + s • dσ̃`. On `P × [a, b]` it restricts to
`ω₀ + s • (ω₁ - ω₀)`, for every real `s`
(`SymplecticGeometry.IsCouplingForm.mpullback_prodMap_subtypeVal_prodIccExtension_add_smul`).
That restriction is a coupling form, so nondegenerate over a family of nondegenerate forms, and
the differential of the inclusion `P × [a, b] → P × ℝ` is invertible, also at the two boundary
levels (`TauCeti.Manifold.isInvertible_mfderiv_prodMap_id_subtypeVal_Icc`). Hence the extended
segment is nondegenerate at every point of `P × ℝ` over `[a, b]`
(`SymplecticGeometry.IsCouplingForm.nondegenerate_bilinFormAt_prodIccExtension_add_smul`).
So every pair `(s, t)` with `t ∈ [a, b]` lies in the set of pairs at which the extended segment
is nondegenerate along all of `P × {t}`
(`IsCouplingForm.univ_prod_Icc_subset_setOfPred_nondegenerate_prodIccExtension_add_smul`);
for compact `B` that set is open
(`TauCeti.SmoothTwoForm.isOpen_setOfPred_forall_nondegenerate_bilinFormAt_add_smul`).
It contains the compact set `[0, 1] × [a, b]`, so Tau Ceti's smooth cutoff around a compact set
(`IsCompact.exists_contMDiff_one_nhds_tsupport_subset`) gives a smooth `ρ : ℝ × ℝ → ℝ`, equal to
`1` near `[0, 1] × [a, b]`, with compact support inside it, by
`IsCouplingForm.exists_contMDiff_tsupport_subset_setOfPred_nondegenerate_prodIccExtension_add_smul`.
The cutoff of the extended Moser field is `(s, (x, t)) ↦ ρ (s, t)`: it is smooth, invariant
under the circle action, compactly supported because `P` is compact, equal to `1` near
`[0, 1] × P × [a, b]`, and the extended segment is nondegenerate on its support
(`IsCouplingForm.exists_cutoff_prodIccExtension_add_smul`).

The cut-off Moser field `Y` on `P × ℝ` (`SymplecticGeometry.prodIccMoserField`) is
`SymplecticGeometry.moserField` for the family
`TauCeti.SmoothForm.lineMapFamily ω̃₀ (ω̃₀ + dσ̃) contDiff_id`, whose slice at `s` is
`ω̃₀ + s • dσ̃`, the one-form `σ̃` pulled back along `Prod.snd`, and a cutoff `ρ` on
`ℝ × (P × ℝ)`, such as the one of `IsCouplingForm.exists_cutoff_prodIccExtension_add_smul`. It is
jointly smooth when `ρ` is smooth and the slices are nondegenerate on its support
(`SymplecticGeometry.contMDiff_prodIccMoserField`, from
`SymplecticGeometry.contMDiff_moserField_lineMapFamily`), and for `ρ` with compact support it
vanishes outside a compact set
(`SymplecticGeometry.exists_isCompact_prodIccMoserField_eq_zero`, from
`SymplecticGeometry.exists_isCompact_moserField_eq_zero`). It is carried to itself by the
differential of `(x, t) ↦ (op z • x, t)` when `ρ` is invariant
(`IsCouplingForm.mfderiv_smul_prodIccMoserField`, from
`SymplecticGeometry.mfderiv_moserField`). Finally `de (Y_s) = 0` at every point: Cartan's
formula for the invariant `σ̃`, which vanishes on `(X, 0)`, gives `ι_{(X, 0)} dσ̃ = 0`
(`IsCouplingForm.mextDerivₗ_timeExtendIcc_prodIccHomotopyOperator_sub_apply_prodVectorField`),
so, where the flat map of the slice is invertible,
`-de (Y_s) = (ω̃₀ + s • dσ̃) ((X, 0), Y_s)` equals `ρ (s, p) σ̃ (X, 0) = 0`, and elsewhere `Y_s = 0`
(`IsCouplingForm.mextDerivₗ_timeExtendIcc_prodIccHeight_apply_prodIccMoserField`). As
`de = dt` over `[a, b]`, the field has no component along `ℝ` there
(`IsCouplingForm.prodIccMoserField_snd_eq_zero`).

For a cutoff with compact support and a jointly `C¹` field, the suspension of `Y` is complete
(`SymplecticGeometry.isCompleteVectorField_timeDependentSuspensionField_prodIccMoserField`, from
`TauCeti.isCompleteVectorField_timeDependentSuspensionField`), so the
time-one map `TauCeti.timeDependentFlowDiffeomorph … 0 1` is a diffeomorphism of `P × ℝ` whose
inverse is the flow from `1` to `0`. The flow of `Y` between any two times commutes with
`(x, t) ↦ (op z • x, t)` for an invariant cutoff, by naturality of flows
(`Diffeomorph.apply_timeDependentFlowOf`) and the invariance of `Y`
(`IsCouplingForm.timeDependentFlowOf_prodIccMoserField_smul`). It keeps each level
`P × {t}` with `t ∈ [a, b]` (`IsCouplingForm.timeDependentFlowOf_prodIccMoserField_snd`): `Y` has
no component along `ℝ` on such a level, so the flow of the field that `Y` induces on the level `P`,
kept at height `t`, solves the equation of `Y`, and by uniqueness of solutions it is the flow of
`Y` (`TauCeti.timeDependentFlowOf_snd_eq_of_forall_snd_eq_zero`).

Moser's equation then holds along the trajectory of every point `(x, t)` with `t ∈ [a, b]` up to
time `1`, for a smooth cutoff with compact support, equal to `1` near `[0, 1] × P × [a, b]` and
supported where the extended segment is nondegenerate. The trajectory stays on `P × {t}`, where
the cutoff is `1` and the segment nondegenerate, and the slices `ω̃₀ + s • dσ̃` are closed with
derivative `dσ̃` in `s`. So the time-one map pulls `ω̃₀ + dσ̃` back to `ω̃₀` at `(x, t)`
(`IsCouplingForm.mpullback_timeDependentFlowOf_prodIccMoserField_apply`,
from `TauCeti.SmoothTwoForm.mpullback_timeDependentFlowOf_moserField_lineMapFamily_apply` of
`Moser/Field.lean`).

The main theorem `SymplecticGeometry.IsCouplingForm.exists_diffeomorph` puts the steps together,
over a compact Hausdorff boundaryless base. With the cutoff of
`IsCouplingForm.exists_cutoff_prodIccExtension_add_smul`, the time-one map `Φ` of the cut-off
Moser flow and its inverse, the flow from `1` to `0`, keep every level over `[a, b]`, so `Φ`
restricts to a diffeomorphism `Ψ` of `P × [a, b]` (`Diffeomorph.restrictProdIcc`). It preserves
`t`, and it commutes with the circle action since `Φ` does. Restricting to `P × [a, b]` takes
`ω̃₀ + dσ̃` to `ω₁` and `ω̃₀` to `ω₀`, and restricting and then pulling back by `Ψ` is pulling
back by `Φ` and then restricting
(`Diffeomorph.mpullback_restrictProdIcc_mpullback_prodMap_subtypeVal`). Moser's equation at the
points over `[a, b]` then gives `Ψ^* ω₁ = ω₀`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Proposition 5.1.9 (uniqueness of coupling forms) and §3.2 (Moser's argument).
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

namespace IsCouplingForm

variable {η ω₀ ω₁ :
    SmoothTwoForm ((IB.prod (𝓡 1)).prod (𝓡∂ 1)) (ManifoldTotalSpace Circle P × Icc a b)}
  {τ : Icc a b → SmoothTwoForm IB B}

/-! ### The extended Moser data on `P × ℝ` -/

section Extension

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
  rw [prodVectorField_eq_couplingField, Subsingleton.elim w ![]]
  exact prodIccHomotopyOperator_sub_apply_couplingField h₀ h₁ q

/-- **The contraction of the extended form with `(X, 0)`.** For a coupling form `ω₀`, the
contraction of its extension `ω̃₀` to `P × ℝ` (`SymplecticGeometry.prodIccExtension`) with the
field `(X, 0)` is `-de`, where `e` is the time extension of the height `t - a`
(`SymplecticGeometry.prodIccHeight`). Over `[a, b]`, `de` is `dt`
(`SymplecticGeometry.mextDerivₗ_timeExtendIcc_prodIccHeight_apply`). -/
theorem prodIccExtension_apply_prodVectorField [IB.Boundaryless] (h : IsCouplingForm ω₀ τ)
    (p : ManifoldTotalSpace Circle P × ℝ) (w : TangentSpace ((IB.prod (𝓡 1)).prod 𝓘(ℝ, ℝ)) p) :
    (prodIccExtension (IB.prod (𝓡 1)) (ManifoldTotalSpace Circle P) a b ℝ 1 ω₀).val p
      ![Manifold.prodVectorField
        (rightFundamentalVectorField (IB.prod (𝓡 1)) circlePeriodOneGenerator) 0 p, w] =
      -(mextDerivₗ ((IB.prod (𝓡 1)).prod 𝓘(ℝ, ℝ)) 0 (SmoothForm.timeExtendIcc
        (prodIccHeight (IB.prod (𝓡 1)) (ManifoldTotalSpace Circle P) a b))).val p ![w] := by
  set A := SmoothForm.timeExtendIcc
    (prodIccHomotopyOperator (IB.prod (𝓡 1)) (ManifoldTotalSpace Circle P) a b ℝ 1 ω₀)
  have hA : ∀ z : Circle, SmoothForm.mpullback
      (fun x : ManifoldTotalSpace Circle P × ℝ ↦ (op z • x.1, x.2))
      (PrincipalBundle.contMDiff_op_smul_prod z) A = A := fun z ↦
    mpullback_smul_timeExtendIcc z (mpullback_smul_prodIccHomotopyOperator z (h.mpullback_smul z))
  -- the contraction of `A` with `(X, 0)` is the time extension of the height
  have hAX : (fun q : ManifoldTotalSpace Circle P × ℝ ↦
      A.val q ![(rightFundamentalVectorField (IB.prod (𝓡 1)) circlePeriodOneGenerator q.1,
        (0 : ℝ))]) = fun q ↦ (SmoothForm.timeExtendIcc
          (prodIccHeight (IB.prod (𝓡 1)) (ManifoldTotalSpace Circle P) a b)).val q 0 := by
    funext q
    refine Eq.trans ?_ (SmoothForm.timeExtendIcc_apply_cons_prodVectorField
      (rightFundamentalVectorField (IB.prod (𝓡 1)) circlePeriodOneGenerator)
      (η := prodIccHomotopyOperator (IB.prod (𝓡 1)) (ManifoldTotalSpace Circle P) a b ℝ 1 ω₀)
      (fun q' w' ↦ ?_) q 0)
    · congr 1
      funext i
      fin_cases i
      exact (Manifold.prodVectorField_apply
      (rightFundamentalVectorField (IB.prod (𝓡 1)) circlePeriodOneGenerator)
      (0 : Π t : ℝ, TangentSpace 𝓘(ℝ, ℝ) t) q).symm
    · rw [prodIccHeight_apply, Subsingleton.elim w' ![], prodVectorField_eq_couplingField]
      exact prodIccHomotopyOperator_apply_couplingField_eq_sub h q'
  have hY : Manifold.prodVectorField
      (rightFundamentalVectorField (IB.prod (𝓡 1)) circlePeriodOneGenerator) 0 p =
      ((rightFundamentalVectorField (IB.prod (𝓡 1)) circlePeriodOneGenerator p.1, (0 : ℝ)) :
        TangentSpace ((IB.prod (𝓡 1)).prod 𝓘(ℝ, ℝ)) p) :=
    Manifold.prodVectorField_apply
      (rightFundamentalVectorField (IB.prod (𝓡 1)) circlePeriodOneGenerator)
      (0 : Π t : ℝ, TangentSpace 𝓘(ℝ, ℝ) t) p
  -- `d A` contracted with `(X, 0)` is `-de`, by Cartan's formula for the invariant `A`
  have h₂ : (mextDerivₗ ((IB.prod (𝓡 1)).prod 𝓘(ℝ, ℝ)) 1 A).val p
      ![Manifold.prodVectorField
        (rightFundamentalVectorField (IB.prod (𝓡 1)) circlePeriodOneGenerator) 0 p, w] =
      -(mextDerivₗ ((IB.prod (𝓡 1)).prod 𝓘(ℝ, ℝ)) 0 (SmoothForm.timeExtendIcc
        (prodIccHeight (IB.prod (𝓡 1)) (ManifoldTotalSpace Circle P) a b))).val p ![w] := by
    rw [mextDerivₗ_apply, hY,
      PrincipalBundle.mextDeriv_apply_rightFundamentalVectorField_prod hA, hAX,
      mextDerivₗ_zero_apply]
  rw [prodIccExtension_apply, Submodule.coe_add, Pi.add_apply, ContinuousAlternatingMap.add_apply,
    mpullback_bot_apply_prodVectorField_eq_zero h, h₂, zero_add]

/-- **The extended Moser segment restricts to the segment.** For two coupling forms `ω₀` and `ω₁`
for the same family and every real `s`, the form `ω̃₀ + s • dσ̃` on `P × ℝ`, where `ω̃₀` is the
extension of `ω₀` (`SymplecticGeometry.prodIccExtension`) and `σ̃` the time extension of
`K (ω₁ - ω₀)`, pulls back along the inclusion `P × [a, b] → P × ℝ` to `ω₀ + s • (ω₁ - ω₀)`. -/
theorem mpullback_prodMap_subtypeVal_prodIccExtension_add_smul (h₀ : IsCouplingForm ω₀ τ)
    (h₁ : IsCouplingForm ω₁ τ) (s : ℝ) :
    SmoothForm.mpullback (Prod.map id Subtype.val) (contMDiff_id.prodMap contMDiff_subtypeVal_Icc)
        (prodIccExtension (IB.prod (𝓡 1)) (ManifoldTotalSpace Circle P) a b ℝ 1 ω₀ +
          s • mextDerivₗ ((IB.prod (𝓡 1)).prod 𝓘(ℝ, ℝ)) 1 (SmoothForm.timeExtendIcc
            (prodIccHomotopyOperator (IB.prod (𝓡 1)) (ManifoldTotalSpace Circle P) a b ℝ 1
              (ω₁ - ω₀)))) =
      ω₀ + s • (ω₁ - ω₀) := by
  rw [map_add, map_smul, mpullback_prodMap_subtypeVal_prodIccExtension h₀.isClosed,
    ← SmoothForm.mextDerivₗ_mpullback,
    mpullback_prodMap_subtypeVal_timeExtendIcc_prodIccHomotopyOperator,
    mextDerivₗ_prodIccHomotopyOperator_sub h₀ h₁]

/-- **The extended Moser segment is nondegenerate over `P × [a, b]`.** Let `ω₀` and `ω₁` be
coupling forms for the same family `τ` of nondegenerate forms. For every real `s`, the form
`ω̃₀ + s • dσ̃` on `P × ℝ` (as in
`SymplecticGeometry.IsCouplingForm.mpullback_prodMap_subtypeVal_prodIccExtension_add_smul`) is
nondegenerate at every point `(x, t)` with `t ∈ [a, b]`, the ends of the interval included. -/
theorem nondegenerate_bilinFormAt_prodIccExtension_add_smul (h₀ : IsCouplingForm ω₀ τ)
    (h₁ : IsCouplingForm ω₁ τ) (hτ : ∀ t, (τ t).IsNondegenerate) (s : ℝ)
    (x : ManifoldTotalSpace Circle P) {t : ℝ} (ht : t ∈ Icc a b) :
    ((prodIccExtension (IB.prod (𝓡 1)) (ManifoldTotalSpace Circle P) a b ℝ 1 ω₀ +
        s • mextDerivₗ ((IB.prod (𝓡 1)).prod 𝓘(ℝ, ℝ)) 1 (SmoothForm.timeExtendIcc
          (prodIccHomotopyOperator (IB.prod (𝓡 1)) (ManifoldTotalSpace Circle P) a b ℝ 1
            (ω₁ - ω₀)))).bilinFormAt (x, t)).Nondegenerate := by
  -- the inclusion sends `(x, ⟨t, ht⟩)` to `(x, t)`, by definition of `Prod.map`
  refine (SmoothTwoForm.nondegenerate_bilinFormAt_iff_of_isInvertible_mfderiv
    (Manifold.isInvertible_mfderiv_prodMap_id_subtypeVal_Icc (x, ⟨t, ht⟩))
    (congrFun (SmoothForm.coe_mpullback _ (contMDiff_id.prodMap contMDiff_subtypeVal_Icc) _)
      (x, ⟨t, ht⟩)).symm).mpr ?_
  rw [mpullback_prodMap_subtypeVal_prodIccExtension_add_smul h₀ h₁ s]
  exact ((h₀.lineMap h₁ s).isNondegenerate hτ).nondegenerate_bilinFormAt (x, ⟨t, ht⟩)

/-- **The parameters of nondegenerate slices contain `ℝ × [a, b]`.** Let `ω₀` and `ω₁` be
coupling forms for the same family `τ` of nondegenerate forms. Every pair `(s, t)` with
`t ∈ [a, b]` lies in the set of pairs such that `ω̃₀ + s • dσ̃` (as in
`SymplecticGeometry.IsCouplingForm.mpullback_prodMap_subtypeVal_prodIccExtension_add_smul`) is
nondegenerate at every point of `P × {t}`. For compact `B` and finite-dimensional `EB`, that set
is open (`TauCeti.SmoothTwoForm.isOpen_setOfPred_forall_nondegenerate_bilinFormAt_add_smul`). -/
theorem univ_prod_Icc_subset_setOfPred_nondegenerate_prodIccExtension_add_smul
    (h₀ : IsCouplingForm ω₀ τ) (h₁ : IsCouplingForm ω₁ τ) (hτ : ∀ t, (τ t).IsNondegenerate) :
    univ ×ˢ Icc a b ⊆ {p : ℝ × ℝ | ∀ x : ManifoldTotalSpace Circle P,
      ((prodIccExtension (IB.prod (𝓡 1)) (ManifoldTotalSpace Circle P) a b ℝ 1 ω₀ +
        p.1 • mextDerivₗ ((IB.prod (𝓡 1)).prod 𝓘(ℝ, ℝ)) 1 (SmoothForm.timeExtendIcc
          (prodIccHomotopyOperator (IB.prod (𝓡 1)) (ManifoldTotalSpace Circle P) a b ℝ 1
            (ω₁ - ω₀)))).bilinFormAt (x, p.2)).Nondegenerate} :=
  fun p hp x ↦ nondegenerate_bilinFormAt_prodIccExtension_add_smul h₀ h₁ hτ p.1 x hp.2

/-- **`dσ̃` vanishes on `(X, 0)`.** For two coupling forms `ω₀` and `ω₁` for the same family, the
exterior derivative of the extension `σ̃` to `P × ℝ` of the primitive `K (ω₁ - ω₀)` vanishes when
its first argument is the field `(X, 0)`, where `X` is the period-one fundamental vector field of
the circle action: `σ̃` is invariant and vanishes on `(X, 0)`, so Cartan's formula gives
`ι_{(X, 0)} dσ̃ = -d (σ̃ (X, 0)) = 0`. -/
theorem mextDerivₗ_timeExtendIcc_prodIccHomotopyOperator_sub_apply_prodVectorField
    [IB.Boundaryless] (h₀ : IsCouplingForm ω₀ τ) (h₁ : IsCouplingForm ω₁ τ)
    (p : ManifoldTotalSpace Circle P × ℝ)
    (w : TangentSpace ((IB.prod (𝓡 1)).prod 𝓘(ℝ, ℝ)) p) :
    (mextDerivₗ ((IB.prod (𝓡 1)).prod 𝓘(ℝ, ℝ)) 1 (SmoothForm.timeExtendIcc
        (prodIccHomotopyOperator (IB.prod (𝓡 1)) (ManifoldTotalSpace Circle P) a b ℝ 1
          (ω₁ - ω₀)))).val p
      ![Manifold.prodVectorField
        (rightFundamentalVectorField (IB.prod (𝓡 1)) circlePeriodOneGenerator) 0 p, w] = 0 := by
  have hY (q : ManifoldTotalSpace Circle P × ℝ) : Manifold.prodVectorField
      (rightFundamentalVectorField (IB.prod (𝓡 1)) circlePeriodOneGenerator) 0 q =
      ((rightFundamentalVectorField (IB.prod (𝓡 1)) circlePeriodOneGenerator q.1, (0 : ℝ)) :
        TangentSpace ((IB.prod (𝓡 1)).prod 𝓘(ℝ, ℝ)) q) :=
    Manifold.prodVectorField_apply
      (rightFundamentalVectorField (IB.prod (𝓡 1)) circlePeriodOneGenerator)
      (0 : Π t : ℝ, TangentSpace 𝓘(ℝ, ℝ) t) q
  -- the contraction of `σ̃` with `(X, 0)` is the zero function
  have hAX : (fun q : ManifoldTotalSpace Circle P × ℝ ↦
      (SmoothForm.timeExtendIcc
        (prodIccHomotopyOperator (IB.prod (𝓡 1)) (ManifoldTotalSpace Circle P) a b ℝ 1
          (ω₁ - ω₀))).val q
        ![(rightFundamentalVectorField (IB.prod (𝓡 1)) circlePeriodOneGenerator q.1,
          (0 : ℝ))]) = fun _ ↦ 0 := by
    funext q
    rw [← hY]
    exact timeExtendIcc_prodIccHomotopyOperator_sub_apply_prodVectorField h₀ h₁ q
  rw [mextDerivₗ_apply, hY,
    PrincipalBundle.mextDeriv_apply_rightFundamentalVectorField_prod
      (mpullback_smul_timeExtendIcc_prodIccHomotopyOperator_sub h₀ h₁), hAX]
  -- `erw`: the derivative is taken for the model of `P × ℝ` given by the product instances,
  -- which `mfderiv_const` does not unify with syntactically
  simp only [mvfderiv, neg_eq_zero]
  erw [mfderiv_const, zero_apply]

/-- The cut-off Moser field on `P × ℝ` of two-forms `ω₀` and `ω₁` on `P × [a, b]` and a
cutoff `ρ` on `ℝ × (P × ℝ)`: the field `SymplecticGeometry.moserField` of the family
`TauCeti.SmoothForm.lineMapFamily ω̃₀ (ω̃₀ + dσ̃) contDiff_id`, whose slice at `s` is
`ω̃₀ + s • dσ̃`, and of the pull-back of `σ̃` along `Prod.snd`. Here `ω̃₀` is the extension
`SymplecticGeometry.prodIccExtension` of `ω₀` to `P × ℝ`, and `σ̃` is the time extension
`TauCeti.SmoothForm.timeExtendIcc` of `K (ω₁ - ω₀)`, for the homotopy operator `K`
(`SymplecticGeometry.prodIccHomotopyOperator`). Its value at `(s, p)` is `ρ (s, p)` times the
vector `Y` with `ι_Y (ω̃₀ + s • dσ̃) = -σ̃` at `p` where the flat map of `ω̃₀ + s • dσ̃` at `p`
is invertible, and `0` where it is not. -/
def _root_.SymplecticGeometry.prodIccMoserField (ω₀ ω₁ :
      SmoothTwoForm ((IB.prod (𝓡 1)).prod (𝓡∂ 1)) (ManifoldTotalSpace Circle P × Icc a b))
    (ρ : ℝ × (ManifoldTotalSpace Circle P × ℝ) → ℝ) (s : ℝ) :
    Π p : ManifoldTotalSpace Circle P × ℝ, TangentSpace ((IB.prod (𝓡 1)).prod 𝓘(ℝ, ℝ)) p :=
  moserField
    (SmoothForm.lineMapFamily
      (prodIccExtension (IB.prod (𝓡 1)) (ManifoldTotalSpace Circle P) a b ℝ 1 ω₀)
      (prodIccExtension (IB.prod (𝓡 1)) (ManifoldTotalSpace Circle P) a b ℝ 1 ω₀ +
        mextDerivₗ ((IB.prod (𝓡 1)).prod 𝓘(ℝ, ℝ)) 1 (SmoothForm.timeExtendIcc
          (prodIccHomotopyOperator (IB.prod (𝓡 1)) (ManifoldTotalSpace Circle P) a b ℝ 1
            (ω₁ - ω₀)))) (contDiff_id (E := ℝ)))
    (SmoothForm.mpullback Prod.snd contMDiff_snd (SmoothForm.timeExtendIcc
      (prodIccHomotopyOperator (IB.prod (𝓡 1)) (ManifoldTotalSpace Circle P) a b ℝ 1
        (ω₁ - ω₀)))) ρ s

omit [∀ b, MulAction Circleᵐᵒᵖ (P b)] [PrincipalBundle Circle P] in
theorem _root_.SymplecticGeometry.prodIccMoserField_def (ω₀ ω₁ :
      SmoothTwoForm ((IB.prod (𝓡 1)).prod (𝓡∂ 1)) (ManifoldTotalSpace Circle P × Icc a b))
    (ρ : ℝ × (ManifoldTotalSpace Circle P × ℝ) → ℝ) :
    prodIccMoserField ω₀ ω₁ ρ =
      moserField
        (SmoothForm.lineMapFamily
          (prodIccExtension (IB.prod (𝓡 1)) (ManifoldTotalSpace Circle P) a b ℝ 1 ω₀)
          (prodIccExtension (IB.prod (𝓡 1)) (ManifoldTotalSpace Circle P) a b ℝ 1 ω₀ +
            mextDerivₗ ((IB.prod (𝓡 1)).prod 𝓘(ℝ, ℝ)) 1 (SmoothForm.timeExtendIcc
              (prodIccHomotopyOperator (IB.prod (𝓡 1)) (ManifoldTotalSpace Circle P) a b ℝ 1
                (ω₁ - ω₀)))) (contDiff_id (E := ℝ)))
        (SmoothForm.mpullback Prod.snd contMDiff_snd (SmoothForm.timeExtendIcc
          (prodIccHomotopyOperator (IB.prod (𝓡 1)) (ManifoldTotalSpace Circle P) a b ℝ 1
            (ω₁ - ω₀)))) ρ :=
  (rfl)

omit [∀ b, MulAction Circleᵐᵒᵖ (P b)] [PrincipalBundle Circle P] in
/-- For a cutoff `ρ` with compact support, the cut-off Moser field
`SymplecticGeometry.prodIccMoserField ω₀ ω₁ ρ` vanishes, at every time, outside a compact subset
of `P × ℝ`. -/
theorem _root_.SymplecticGeometry.exists_isCompact_prodIccMoserField_eq_zero (ω₀ ω₁ :
      SmoothTwoForm ((IB.prod (𝓡 1)).prod (𝓡∂ 1)) (ManifoldTotalSpace Circle P × Icc a b))
    {ρ : ℝ × (ManifoldTotalSpace Circle P × ℝ) → ℝ} (hρ : HasCompactSupport ρ) :
    ∃ K : Set (ManifoldTotalSpace Circle P × ℝ), IsCompact K ∧
      ∀ s, ∀ p ∉ K, prodIccMoserField ω₀ ω₁ ρ s p = 0 := by
  rw [prodIccMoserField_def]
  exact exists_isCompact_moserField_eq_zero hρ

omit [∀ b, MulAction Circleᵐᵒᵖ (P b)] [PrincipalBundle Circle P] in
/-- The cut-off Moser field `(s, p) ↦ Y_s(p)` (`SymplecticGeometry.prodIccMoserField ω₀ ω₁ ρ`)
is jointly smooth on `ℝ × (P × ℝ)` when `ρ` is smooth and the slice `ω̃₀ + s • dσ̃` is
nondegenerate at `p` for every point `(s, p)` of the support of `ρ`. -/
theorem _root_.SymplecticGeometry.contMDiff_prodIccMoserField [FiniteDimensional ℝ EB] (ω₀ ω₁ :
      SmoothTwoForm ((IB.prod (𝓡 1)).prod (𝓡∂ 1)) (ManifoldTotalSpace Circle P × Icc a b))
    {ρ : ℝ × (ManifoldTotalSpace Circle P × ℝ) → ℝ}
    (hρ : ContMDiff (𝓘(ℝ, ℝ).prod ((IB.prod (𝓡 1)).prod 𝓘(ℝ, ℝ))) 𝓘(ℝ) ∞ ρ)
    (hnd : ∀ p ∈ tsupport ρ,
      ((prodIccExtension (IB.prod (𝓡 1)) (ManifoldTotalSpace Circle P) a b ℝ 1 ω₀ +
        p.1 • mextDerivₗ ((IB.prod (𝓡 1)).prod 𝓘(ℝ, ℝ)) 1 (SmoothForm.timeExtendIcc
          (prodIccHomotopyOperator (IB.prod (𝓡 1)) (ManifoldTotalSpace Circle P) a b ℝ 1
            (ω₁ - ω₀)))).bilinFormAt p.2).Nondegenerate) :
    ContMDiff (𝓘(ℝ, ℝ).prod ((IB.prod (𝓡 1)).prod 𝓘(ℝ, ℝ)))
      ((IB.prod (𝓡 1)).prod 𝓘(ℝ, ℝ)).tangent ∞
      (fun p : ℝ × (ManifoldTotalSpace Circle P × ℝ) ↦
        (⟨p.2, prodIccMoserField ω₀ ω₁ ρ p.1 p.2⟩ :
          TangentBundle ((IB.prod (𝓡 1)).prod 𝓘(ℝ, ℝ)) (ManifoldTotalSpace Circle P × ℝ))) := by
  rw [prodIccMoserField_def]
  exact contMDiff_moserField_lineMapFamily _ _ _ hρ hnd

omit [∀ b, MulAction Circleᵐᵒᵖ (P b)] [PrincipalBundle Circle P] in
/-- **The suspension of the cut-off Moser field is complete.** For a cutoff `ρ` with compact
support, if the cut-off Moser field `SymplecticGeometry.prodIccMoserField ω₀ ω₁ ρ` is jointly
`C¹`, then its time-dependent flow is defined between any two times, as the field vanishes
outside a compact subset of `P × ℝ`. -/
theorem
    _root_.SymplecticGeometry.isCompleteVectorField_timeDependentSuspensionField_prodIccMoserField
    [IB.Boundaryless] [CompleteSpace EB] [T2Space B] (ω₀ ω₁ :
      SmoothTwoForm ((IB.prod (𝓡 1)).prod (𝓡∂ 1)) (ManifoldTotalSpace Circle P × Icc a b))
    {ρ : ℝ × (ManifoldTotalSpace Circle P × ℝ) → ℝ} (hρ : HasCompactSupport ρ)
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod ((IB.prod (𝓡 1)).prod 𝓘(ℝ, ℝ)))
      ((IB.prod (𝓡 1)).prod 𝓘(ℝ, ℝ)).tangent 1
      (fun p : ℝ × (ManifoldTotalSpace Circle P × ℝ) ↦
        (⟨p.2, prodIccMoserField ω₀ ω₁ ρ p.1 p.2⟩ :
          TangentBundle ((IB.prod (𝓡 1)).prod 𝓘(ℝ, ℝ)) (ManifoldTotalSpace Circle P × ℝ)))) :
    IsCompleteVectorField (timeDependentSuspensionField (prodIccMoserField ω₀ ω₁ ρ)) := by
  obtain ⟨K, hK, hXK⟩ := exists_isCompact_prodIccMoserField_eq_zero ω₀ ω₁ hρ
  exact isCompleteVectorField_timeDependentSuspensionField hX hK hXK

/-- **The cut-off Moser field preserves the extended height.** Let `ω₀` and `ω₁` be coupling
forms for the same family. For any cutoff `ρ`, the cut-off Moser field `Y_s`
(`SymplecticGeometry.prodIccMoserField`) is killed at every point by `de`, where `e` is the
time extension of the height `t - a` (`SymplecticGeometry.prodIccHeight`). -/
theorem mextDerivₗ_timeExtendIcc_prodIccHeight_apply_prodIccMoserField [IB.Boundaryless]
    (h₀ : IsCouplingForm ω₀ τ) (h₁ : IsCouplingForm ω₁ τ)
    (ρ : ℝ × (ManifoldTotalSpace Circle P × ℝ) → ℝ) (s : ℝ)
    (p : ManifoldTotalSpace Circle P × ℝ) :
    (mextDerivₗ ((IB.prod (𝓡 1)).prod 𝓘(ℝ, ℝ)) 0 (SmoothForm.timeExtendIcc
        (prodIccHeight (IB.prod (𝓡 1)) (ManifoldTotalSpace Circle P) a b))).val p
      ![prodIccMoserField ω₀ ω₁ ρ s p] = 0 := by
  rw [prodIccMoserField_def]
  set W := prodIccExtension (IB.prod (𝓡 1)) (ManifoldTotalSpace Circle P) a b ℝ 1 ω₀
  set S := SmoothForm.timeExtendIcc
    (prodIccHomotopyOperator (IB.prod (𝓡 1)) (ManifoldTotalSpace Circle P) a b ℝ 1 (ω₁ - ω₀))
  set X := Manifold.prodVectorField
    (rightFundamentalVectorField (IB.prod (𝓡 1)) circlePeriodOneGenerator)
    (0 : Π t : ℝ, TangentSpace 𝓘(ℝ, ℝ) t) p
  have hσ : SmoothForm.mpullback (Prod.mk s) (contMDiff_const.prodMk contMDiff_id)
      (SmoothForm.lineMapFamily W (W + mextDerivₗ ((IB.prod (𝓡 1)).prod 𝓘(ℝ, ℝ)) 1 S)
        (contDiff_id (E := ℝ))) = W + s • mextDerivₗ ((IB.prod (𝓡 1)).prod 𝓘(ℝ, ℝ)) 1 S := by
    rw [SmoothForm.mpullback_prodMk_lineMapFamily, add_sub_cancel_left, id]
  by_cases hinv : (SmoothTwoForm.flat (SmoothForm.mpullback (Prod.mk s)
      (contMDiff_const.prodMk contMDiff_id) (SmoothForm.lineMapFamily W
        (W + mextDerivₗ ((IB.prod (𝓡 1)).prod 𝓘(ℝ, ℝ)) 1 S) (contDiff_id (E := ℝ)))) p).IsInvertible
  · -- `ι_{Y_s} (ω̃₀ + s • dσ̃) = -ρ σ̃` at `p`, evaluated on `(X, 0)`, where `σ̃` vanishes
    have hY := congrArg (fun c ↦ c ![X])
      (interior_moserField _ (SmoothForm.mpullback Prod.snd contMDiff_snd S) ρ hinv)
    simp only [RoughForm.interior_apply, SmoothForm.mpullback_prodMk_mpullback_snd] at hY
    rw [hσ, ContinuousAlternatingMap.apply_vecCons_swap, Submodule.coe_add, Pi.add_apply,
      ContinuousAlternatingMap.add_apply, Submodule.coe_smul, Pi.smul_apply,
      ContinuousAlternatingMap.smul_apply, prodIccExtension_apply_prodVectorField h₀,
      mextDerivₗ_timeExtendIcc_prodIccHomotopyOperator_sub_apply_prodVectorField h₀ h₁,
      smul_zero, add_zero, ContinuousAlternatingMap.smul_apply,
      timeExtendIcc_prodIccHomotopyOperator_sub_apply_prodVectorField h₀ h₁, smul_zero,
      neg_neg] at hY
    exact hY
  · rw [moserField_def, ContinuousLinearMap.inverse_of_not_isInvertible hinv, zero_apply,
      smul_zero]
    exact ContinuousAlternatingMap.map_coord_zero _ 0 rfl

/-- **The cut-off Moser field is tangent to the levels over `[a, b]`.** Let `ω₀` and `ω₁` be
coupling forms for the same family. For any cutoff `ρ`, at every point `(x, t)` of `P × ℝ` with
`t ∈ [a, b]` the cut-off Moser field (`SymplecticGeometry.prodIccMoserField`) has no component
along `ℝ`. -/
theorem prodIccMoserField_snd_eq_zero [IB.Boundaryless] (h₀ : IsCouplingForm ω₀ τ)
    (h₁ : IsCouplingForm ω₁ τ) (ρ : ℝ × (ManifoldTotalSpace Circle P × ℝ) → ℝ) (s : ℝ)
    (x : ManifoldTotalSpace Circle P) (t : Icc a b) :
    (prodIccMoserField ω₀ ω₁ ρ s (x, t)).2 = 0 := by
  rw [← mextDerivₗ_timeExtendIcc_prodIccHeight_apply x t]
  exact mextDerivₗ_timeExtendIcc_prodIccHeight_apply_prodIccMoserField h₀ h₁ ρ s (x, t)

/-- **The cut-off Moser field is invariant.** Let `ω₀` and `ω₁` be coupling forms for the same
family and `z : Circle`. For a cutoff `ρ` invariant under `(x, t) ↦ (op z • x, t)` at every
time, the differential of `(x, t) ↦ (op z • x, t)` carries the cut-off Moser field `Y_s`
(`SymplecticGeometry.prodIccMoserField`) at `p` to `Y_s` at the image of `p`. -/
theorem mfderiv_smul_prodIccMoserField (h₀ : IsCouplingForm ω₀ τ)
    (h₁ : IsCouplingForm ω₁ τ) (z : Circle) {ρ : ℝ × (ManifoldTotalSpace Circle P × ℝ) → ℝ}
    (hρ : ∀ (s : ℝ) (p : ManifoldTotalSpace Circle P × ℝ), ρ (s, (op z • p.1, p.2)) = ρ (s, p))
    (s : ℝ) (p : ManifoldTotalSpace Circle P × ℝ) :
    mfderiv ((IB.prod (𝓡 1)).prod 𝓘(ℝ, ℝ)) ((IB.prod (𝓡 1)).prod 𝓘(ℝ, ℝ))
        (fun x : ManifoldTotalSpace Circle P × ℝ ↦ (op z • x.1, x.2)) p
        (prodIccMoserField ω₀ ω₁ ρ s p) =
      prodIccMoserField ω₀ ω₁ ρ s (op z • p.1, p.2) := by
  rw [prodIccMoserField_def]
  set W := prodIccExtension (IB.prod (𝓡 1)) (ManifoldTotalSpace Circle P) a b ℝ 1 ω₀
  set S := SmoothForm.timeExtendIcc
    (prodIccHomotopyOperator (IB.prod (𝓡 1)) (ManifoldTotalSpace Circle P) a b ℝ 1 (ω₁ - ω₀))
  set g := (Diffeomorph.constSmul (M := ManifoldTotalSpace Circle P) (IB.prod (𝓡 1)) ∞
    (op z)).prodCongr (Diffeomorph.refl 𝓘(ℝ, ℝ) ℝ ∞)
  have hg : ⇑g = fun x : ManifoldTotalSpace Circle P × ℝ ↦ (op z • x.1, x.2) := by
    funext x
    simp only [g, Diffeomorph.prodCongr_refl_right_apply, Diffeomorph.coe_constSmul]
  have hW : SmoothForm.mpullback g g.contMDiff W = W :=
    (SmoothForm.mpullback_congr _ _ hg W).trans
      (mpullback_smul_prodIccExtension z (h₀.mpullback_smul z))
  have hS : SmoothForm.mpullback g g.contMDiff S = S :=
    (SmoothForm.mpullback_congr _ _ hg S).trans
      (mpullback_smul_timeExtendIcc_prodIccHomotopyOperator_sub h₀ h₁ z)
  have h := mfderiv_moserField g (t := s) (ρ := ρ)
    (σ := SmoothForm.lineMapFamily W (W + mextDerivₗ ((IB.prod (𝓡 1)).prod 𝓘(ℝ, ℝ)) 1 S)
      (contDiff_id (E := ℝ)))
    (β := SmoothForm.mpullback Prod.snd contMDiff_snd S) ?_ ?_ (fun x ↦ by rw [hg]; exact hρ s x) p
  · rwa [hg] at h
  · rw [SmoothForm.mpullback_prodMk_lineMapFamily, add_sub_cancel_left, map_add, map_smul,
      ← SmoothForm.mextDerivₗ_mpullback, hW, hS, id]
  · rw [SmoothForm.mpullback_prodMk_mpullback_snd, hS]

/-- **The cut-off Moser flow is equivariant.** Let `ω₀` and `ω₁` be coupling forms for the same
family and `z : Circle`. For a cutoff `ρ` invariant under `(x, r) ↦ (op z • x, r)` at every
time, if the cut-off Moser field (`SymplecticGeometry.prodIccMoserField`) is jointly `C¹`, then
its time-dependent flow from `s` to `t` commutes with `(x, r) ↦ (op z • x, r)`. -/
theorem timeDependentFlowOf_prodIccMoserField_smul
    [IB.Boundaryless] [T2Space B] (h₀ : IsCouplingForm ω₀ τ)
    (h₁ : IsCouplingForm ω₁ τ) (z : Circle) {ρ : ℝ × (ManifoldTotalSpace Circle P × ℝ) → ℝ}
    (hρ : ∀ (s : ℝ) (p : ManifoldTotalSpace Circle P × ℝ), ρ (s, (op z • p.1, p.2)) = ρ (s, p))
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod ((IB.prod (𝓡 1)).prod 𝓘(ℝ, ℝ)))
      ((IB.prod (𝓡 1)).prod 𝓘(ℝ, ℝ)).tangent 1
      (fun p : ℝ × (ManifoldTotalSpace Circle P × ℝ) ↦
        (⟨p.2, prodIccMoserField ω₀ ω₁ ρ p.1 p.2⟩ :
          TangentBundle ((IB.prod (𝓡 1)).prod 𝓘(ℝ, ℝ)) (ManifoldTotalSpace Circle P × ℝ))))
    (s t : ℝ) (p : ManifoldTotalSpace Circle P × ℝ) :
    timeDependentFlowOf (prodIccMoserField ω₀ ω₁ ρ) s t (op z • p.1, p.2) =
      (op z • (timeDependentFlowOf (prodIccMoserField ω₀ ω₁ ρ) s t p).1,
        (timeDependentFlowOf (prodIccMoserField ω₀ ω₁ ρ) s t p).2) := by
  set g := (Diffeomorph.constSmul (M := ManifoldTotalSpace Circle P) (IB.prod (𝓡 1)) ∞
    (op z)).prodCongr (Diffeomorph.refl 𝓘(ℝ, ℝ) ℝ ∞)
  have hg : ⇑g = fun x : ManifoldTotalSpace Circle P × ℝ ↦ (op z • x.1, x.2) := by
    funext x
    simp only [g, Diffeomorph.prodCongr_refl_right_apply, Diffeomorph.coe_constSmul]
  have h := g.apply_timeDependentFlowOf (by simp) hX (fun u y ↦ by
    rw [hg]
    exact mfderiv_smul_prodIccMoserField h₀ h₁ z hρ u y) s t p
  rw [hg] at h
  exact h.symm

/-- **The cut-off Moser flow keeps the levels over `[a, b]`.** Let `ω₀` and `ω₁` be coupling forms
for the same family. For a cutoff `ρ` with compact support, if the cut-off Moser field
(`SymplecticGeometry.prodIccMoserField`) is jointly `C¹`, then its time-dependent flow between
any two times keeps each level `P × {t}` with `t ∈ [a, b]`. -/
theorem timeDependentFlowOf_prodIccMoserField_snd
    [IB.Boundaryless] [CompleteSpace EB] [T2Space B]
    (h₀ : IsCouplingForm ω₀ τ)
    (h₁ : IsCouplingForm ω₁ τ) {ρ : ℝ × (ManifoldTotalSpace Circle P × ℝ) → ℝ}
    (hρ : HasCompactSupport ρ)
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod ((IB.prod (𝓡 1)).prod 𝓘(ℝ, ℝ)))
      ((IB.prod (𝓡 1)).prod 𝓘(ℝ, ℝ)).tangent 1
      (fun p : ℝ × (ManifoldTotalSpace Circle P × ℝ) ↦
        (⟨p.2, prodIccMoserField ω₀ ω₁ ρ p.1 p.2⟩ :
          TangentBundle ((IB.prod (𝓡 1)).prod 𝓘(ℝ, ℝ)) (ManifoldTotalSpace Circle P × ℝ))))
    (s u : ℝ) (x : ManifoldTotalSpace Circle P) (t : Icc a b) :
    (timeDependentFlowOf (prodIccMoserField ω₀ ω₁ ρ) s u (x, t)).2 = t := by
  obtain ⟨K, hK, hXK⟩ := exists_isCompact_prodIccMoserField_eq_zero ω₀ ω₁ hρ
  exact timeDependentFlowOf_snd_eq_of_forall_snd_eq_zero hX hK hXK
    (fun v y ↦ prodIccMoserField_snd_eq_zero h₀ h₁ ρ v y t) s u x

/-- **Moser's equation for the cut-off Moser flow over `[a, b]`.** Let `ω₀` and `ω₁` be coupling
forms for the same family. Take the family `s ↦ ω̃₀ + s • dσ̃` on `P × ℝ` (as in
`SymplecticGeometry.IsCouplingForm.mpullback_prodMap_subtypeVal_prodIccExtension_add_smul`), the
one-form `σ̃` and a smooth cutoff `ρ` with compact support, equal to `1` on a neighbourhood of
`[0, 1] × P × [a, b]`, such that `ω̃₀ + s • dσ̃` is nondegenerate at `p` for every point `(s, p)`
of the topological support of `ρ`. Then the time-one map of the cut-off Moser field
(`SymplecticGeometry.prodIccMoserField`) pulls `ω̃₀ + dσ̃` back to `ω̃₀` at every point `(x, t)`
with `t ∈ [a, b]`. -/
theorem mpullback_timeDependentFlowOf_prodIccMoserField_apply
    [IB.Boundaryless] [FiniteDimensional ℝ EB] [T2Space B]
    (h₀ : IsCouplingForm ω₀ τ) (h₁ : IsCouplingForm ω₁ τ)
    {ρ : ℝ × (ManifoldTotalSpace Circle P × ℝ) → ℝ}
    (hρ : ContMDiff (𝓘(ℝ, ℝ).prod ((IB.prod (𝓡 1)).prod 𝓘(ℝ, ℝ))) 𝓘(ℝ) ∞ ρ)
    (hρc : HasCompactSupport ρ) (hρ1 : ∀ᶠ p in 𝓝ˢ (Icc 0 1 ×ˢ (univ ×ˢ Icc a b)), ρ p = 1)
    (hnd : ∀ p ∈ tsupport ρ,
      ((prodIccExtension (IB.prod (𝓡 1)) (ManifoldTotalSpace Circle P) a b ℝ 1 ω₀ +
        p.1 • mextDerivₗ ((IB.prod (𝓡 1)).prod 𝓘(ℝ, ℝ)) 1 (SmoothForm.timeExtendIcc
          (prodIccHomotopyOperator (IB.prod (𝓡 1)) (ManifoldTotalSpace Circle P) a b ℝ 1
            (ω₁ - ω₀)))).bilinFormAt p.2).Nondegenerate)
    (x : ManifoldTotalSpace Circle P) (t : Icc a b) :
    TauCeti.mpullback ((IB.prod (𝓡 1)).prod 𝓘(ℝ, ℝ)) ((IB.prod (𝓡 1)).prod 𝓘(ℝ, ℝ))
        (timeDependentFlowOf (prodIccMoserField ω₀ ω₁ ρ) 0 1)
        (prodIccExtension (IB.prod (𝓡 1)) (ManifoldTotalSpace Circle P) a b ℝ 1 ω₀ +
          mextDerivₗ ((IB.prod (𝓡 1)).prod 𝓘(ℝ, ℝ)) 1 (SmoothForm.timeExtendIcc
            (prodIccHomotopyOperator (IB.prod (𝓡 1)) (ManifoldTotalSpace Circle P) a b ℝ 1
              (ω₁ - ω₀)))).val (x, t) =
      (prodIccExtension (IB.prod (𝓡 1)) (ManifoldTotalSpace Circle P) a b ℝ 1 ω₀).val (x, t) := by
  set W := prodIccExtension (IB.prod (𝓡 1)) (ManifoldTotalSpace Circle P) a b ℝ 1 ω₀
  set D := mextDerivₗ ((IB.prod (𝓡 1)).prod 𝓘(ℝ, ℝ)) 1 (SmoothForm.timeExtendIcc
    (prodIccHomotopyOperator (IB.prod (𝓡 1)) (ManifoldTotalSpace Circle P) a b ℝ 1 (ω₁ - ω₀)))
  have hX := contMDiff_prodIccMoserField ω₀ ω₁ hρ hnd
  -- the trajectory of `(x, t)` stays on the level `P × {t}`, near which `ρ = 1`
  have hy (s : ℝ) := timeDependentFlowOf_prodIccMoserField_snd h₀ h₁ hρc
    (hX.of_le (by simp)) 0 s x t
  have hc := isCompleteVectorField_timeDependentSuspensionField_prodIccMoserField ω₀ ω₁ hρc
    (hX.of_le (by simp))
  rw [prodIccMoserField_def] at hX hy hc ⊢
  refine SmoothTwoForm.mpullback_timeDependentFlowOf_moserField_lineMapFamily_apply
    (isClosed_prodIccExtension h₀.isClosed) (add_sub_cancel_left W D) (hX.of_le (by simp)) hc
    fun s hs ↦ ?_
  refine ((Continuous.prodMk_right s).continuousAt.eventually
    (hρ1.filter_mono (nhds_le_nhdsSet ?_))).mono fun z hz ↦ ⟨hz, ?_⟩
  · exact ⟨hs, mem_univ _, by rw [hy s]; exact t.property⟩
  rw [add_sub_cancel_left]
  exact SmoothTwoForm.isInvertible_flat_iff.mpr
    (hnd (s, z) (subset_tsupport ρ (by rw [Function.mem_support, hz]; exact one_ne_zero)))

variable [CompactSpace B] [FiniteDimensional ℝ EB]

/-- **A cutoff in the parameters.** Let `ω₀` and `ω₁` be coupling forms for the same family `τ`
of nondegenerate forms, over a compact base modelled on a finite-dimensional space. There is a
smooth `ρ : ℝ × ℝ → ℝ` with values in `[0, 1]` and compact support, equal to `1` on a
neighbourhood of `[0, 1] × [a, b]`, whose topological support lies in the set of pairs `(s, t)`
such that `ω̃₀ + s • dσ̃` (as in
`SymplecticGeometry.IsCouplingForm.mpullback_prodMap_subtypeVal_prodIccExtension_add_smul`) is
nondegenerate at every point of `P × {t}`. -/
theorem exists_contMDiff_tsupport_subset_setOfPred_nondegenerate_prodIccExtension_add_smul
    (h₀ : IsCouplingForm ω₀ τ) (h₁ : IsCouplingForm ω₁ τ) (hτ : ∀ t, (τ t).IsNondegenerate) :
    ∃ ρ : ℝ × ℝ → ℝ, ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞ ρ ∧
      (∀ᶠ q in 𝓝ˢ (Icc 0 1 ×ˢ Icc a b), ρ q = 1) ∧ HasCompactSupport ρ ∧
      tsupport ρ ⊆ {p : ℝ × ℝ | ∀ x : ManifoldTotalSpace Circle P,
        ((prodIccExtension (IB.prod (𝓡 1)) (ManifoldTotalSpace Circle P) a b ℝ 1 ω₀ +
          p.1 • mextDerivₗ ((IB.prod (𝓡 1)).prod 𝓘(ℝ, ℝ)) 1 (SmoothForm.timeExtendIcc
            (prodIccHomotopyOperator (IB.prod (𝓡 1)) (ManifoldTotalSpace Circle P) a b ℝ 1
              (ω₁ - ω₀)))).bilinFormAt (x, p.2)).Nondegenerate} ∧
      ∀ q, ρ q ∈ Icc 0 1 :=
  (isCompact_Icc.prod isCompact_Icc).exists_contMDiff_one_nhds_tsupport_subset
    (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))
    (SmoothTwoForm.isOpen_setOfPred_forall_nondegenerate_bilinFormAt_add_smul _ _)
    ((prod_mono (subset_univ _) subset_rfl).trans
      (univ_prod_Icc_subset_setOfPred_nondegenerate_prodIccExtension_add_smul h₀ h₁ hτ))

/-- **The cutoff of the extended Moser field.** Let `ω₀` and `ω₁` be coupling forms for the same
family `τ` of nondegenerate forms, over a compact base modelled on a finite-dimensional space.
There is `ρ : ℝ × ℝ → ℝ` with values in `[0, 1]` such that the function
`ρ ∘ Prod.map id Prod.snd`, that is `(s, (x, t)) ↦ ρ (s, t)`, on `ℝ × (P × ℝ)` is smooth, has
compact support, equals `1` on a neighbourhood of `[0, 1] × P × [a, b]`, and at each point
`(s, p)` of its topological support the form `ω̃₀ + s • dσ̃` (as in
`SymplecticGeometry.IsCouplingForm.mpullback_prodMap_subtypeVal_prodIccExtension_add_smul`) is
nondegenerate at `p`. As it does not depend on the point of `P`, it is invariant under the
action of every `z : Circle` on `P`. -/
theorem exists_cutoff_prodIccExtension_add_smul (h₀ : IsCouplingForm ω₀ τ)
    (h₁ : IsCouplingForm ω₁ τ) (hτ : ∀ t, (τ t).IsNondegenerate) :
    ∃ ρ : ℝ × ℝ → ℝ,
      ContMDiff (𝓘(ℝ, ℝ).prod ((IB.prod (𝓡 1)).prod 𝓘(ℝ, ℝ))) 𝓘(ℝ) ∞
        (ρ ∘ Prod.map id (Prod.snd (α := ManifoldTotalSpace Circle P))) ∧
      HasCompactSupport (ρ ∘ Prod.map id (Prod.snd (α := ManifoldTotalSpace Circle P))) ∧
      (∀ᶠ p in 𝓝ˢ (Icc 0 1 ×ˢ (univ ×ˢ Icc a b)),
        ρ ((p : ℝ × (ManifoldTotalSpace Circle P × ℝ)).1, p.2.2) = 1) ∧
      (∀ p ∈ tsupport (ρ ∘ Prod.map id (Prod.snd (α := ManifoldTotalSpace Circle P))),
        ((prodIccExtension (IB.prod (𝓡 1)) (ManifoldTotalSpace Circle P) a b ℝ 1 ω₀ +
          p.1 • mextDerivₗ ((IB.prod (𝓡 1)).prod 𝓘(ℝ, ℝ)) 1 (SmoothForm.timeExtendIcc
            (prodIccHomotopyOperator (IB.prod (𝓡 1)) (ManifoldTotalSpace Circle P) a b ℝ 1
              (ω₁ - ω₀)))).bilinFormAt p.2).Nondegenerate) ∧
      (∀ (z : Circle) (s : ℝ) (x : ManifoldTotalSpace Circle P) (t : ℝ),
        (ρ ∘ Prod.map id Prod.snd) (s, (op z • x, t)) = (ρ ∘ Prod.map id Prod.snd) (s, (x, t))) ∧
      ∀ q, ρ q ∈ Icc 0 1 := by
  obtain ⟨ρ, hρ, h1, hc, hs, h01⟩ :=
    exists_contMDiff_tsupport_subset_setOfPred_nondegenerate_prodIccExtension_add_smul h₀ h₁ hτ
  have hΨ : Continuous (Prod.map id (Prod.snd (α := ManifoldTotalSpace Circle P)) :
      ℝ × (ManifoldTotalSpace Circle P × ℝ) → ℝ × ℝ) := by
    fun_prop
  -- `Prod.map id Prod.snd` is proper as `P` is compact, so the preimage of `tsupport ρ` is compact
  refine ⟨ρ, hρ.comp (contMDiff_fst.prodMk (contMDiff_snd.comp contMDiff_snd)),
    .intro' ((isProperMap_id.prodMap isProperMap_snd_of_compactSpace).isCompact_preimage
      hc.isCompact) ((isClosed_tsupport ρ).preimage hΨ)
      fun _ hz ↦ image_eq_zero_of_notMem_tsupport (f := ρ) hz,
    (hΨ.tendsto_nhdsSet (s := Icc 0 1 ×ˢ (univ ×ˢ Icc a b)) (t := Icc 0 1 ×ˢ Icc a b)
      fun _ hp ↦ ⟨hp.1, hp.2.2⟩).eventually h1,
    fun p hp ↦ hs (tsupport_comp_subset_preimage ρ hΨ hp) p.2.1, fun _ _ _ _ ↦ rfl, h01⟩

/-- **Uniqueness of coupling forms.** Let `P` be a smooth principal `Circle`-bundle over a compact
Hausdorff boundaryless manifold `B`, modelled on a finite-dimensional space, and let `ω₀` and
`ω₁` be coupling forms on `P × [a, b]` for the same family `τ` of nondegenerate two-forms on `B`.
Then there is a diffeomorphism `Ψ` of `P × [a, b]` that preserves the coordinate `t` of the
interval, commutes with the action `(x, t) ↦ (op z • x, t)` of every `z : Circle`, and pulls
`ω₁` back to `ω₀`. It need not cover the identity of `B`.

Milestone: *Minimal coupling*. -/
theorem exists_diffeomorph [IB.Boundaryless] [T2Space B] (h₀ : IsCouplingForm ω₀ τ)
    (h₁ : IsCouplingForm ω₁ τ) (hτ : ∀ t, (τ t).IsNondegenerate) :
    ∃ Ψ : (ManifoldTotalSpace Circle P × Icc a b) ≃ₘ⟮(IB.prod (𝓡 1)).prod (𝓡∂ 1),
        (IB.prod (𝓡 1)).prod (𝓡∂ 1)⟯ ManifoldTotalSpace Circle P × Icc a b,
      (∀ x, (Ψ x).2 = x.2) ∧
      (∀ (z : Circle) (x : ManifoldTotalSpace Circle P × Icc a b),
        Ψ (op z • x.1, x.2) = (op z • (Ψ x).1, x.2)) ∧
      SmoothForm.mpullback Ψ Ψ.contMDiff ω₁ = ω₀ := by
  obtain ⟨ρ, hρ, hρc, hρ1, hnd, hinv, -⟩ := exists_cutoff_prodIccExtension_add_smul h₀ h₁ hτ
  set W := prodIccExtension (IB.prod (𝓡 1)) (ManifoldTotalSpace Circle P) a b ℝ 1 ω₀
  set D := mextDerivₗ ((IB.prod (𝓡 1)).prod 𝓘(ℝ, ℝ)) 1 (SmoothForm.timeExtendIcc
    (prodIccHomotopyOperator (IB.prod (𝓡 1)) (ManifoldTotalSpace Circle P) a b ℝ 1 (ω₁ - ω₀)))
  have hX := contMDiff_prodIccMoserField ω₀ ω₁ hρ hnd
  have hX₁ := hX.of_le (m := 1) (by simp)
  have hc := isCompleteVectorField_timeDependentSuspensionField_prodIccMoserField ω₀ ω₁ hρc hX₁
  -- `Φ` is the time-one map of the cut-off Moser flow on `P × ℝ`; it and its inverse keep the
  -- levels over `[a, b]`
  set Φ := timeDependentFlowDiffeomorph hc le_top hX 0 1
  have hΦ (x : ManifoldTotalSpace Circle P) (t : ℝ) (ht : t ∈ Icc a b) : (Φ (x, t)).2 = t := by
    rw [timeDependentFlowDiffeomorph_apply]
    exact timeDependentFlowOf_prodIccMoserField_snd h₀ h₁ hρc hX₁ 0 1 x ⟨t, ht⟩
  have hΦ' (x : ManifoldTotalSpace Circle P) (t : ℝ) (ht : t ∈ Icc a b) :
      (Φ.symm (x, t)).2 = t := by
    rw [timeDependentFlowDiffeomorph_symm_apply]
    exact timeDependentFlowOf_prodIccMoserField_snd h₀ h₁ hρc hX₁ 1 0 x ⟨t, ht⟩
  refine ⟨Φ.restrictProdIcc hΦ hΦ', Φ.restrictProdIcc_apply_snd hΦ hΦ', fun z x ↦ ?_, ?_⟩
  · rw [Diffeomorph.restrictProdIcc_apply, Diffeomorph.restrictProdIcc_apply,
      timeDependentFlowDiffeomorph_apply, timeDependentFlowDiffeomorph_apply,
      timeDependentFlowOf_prodIccMoserField_smul h₀ h₁ z (fun s p ↦ hinv z s p.1 p.2) hX₁ 0 1
        (x.1, x.2)]
  -- `ω₁` and `ω₀` are the restrictions of `W + D` and `W`, and `Φ` pulls `W + D` back to `W`
  -- over `[a, b]`
  have hW₁ : SmoothForm.mpullback (Prod.map id Subtype.val)
      (contMDiff_id.prodMap contMDiff_subtypeVal_Icc) (W + D) = ω₁ := by
    have h := mpullback_prodMap_subtypeVal_prodIccExtension_add_smul h₀ h₁ 1
    rwa [one_smul, one_smul, add_sub_cancel] at h
  have hW₀ : SmoothForm.mpullback (Prod.map id Subtype.val)
      (contMDiff_id.prodMap contMDiff_subtypeVal_Icc) W = ω₀ := by
    have h := mpullback_prodMap_subtypeVal_prodIccExtension_add_smul h₀ h₁ 0
    rwa [zero_smul, zero_smul, add_zero, add_zero] at h
  rw [← hW₁, ← hW₀, Diffeomorph.mpullback_restrictProdIcc_mpullback_prodMap_subtypeVal]
  refine Subtype.ext (funext fun p ↦ ?_)
  rw [SmoothForm.coe_mpullback, SmoothForm.coe_mpullback, SmoothForm.coe_mpullback]
  refine TauCeti.mpullback_apply_congr ?_
  rw [show ⇑Φ = _ from funext (timeDependentFlowDiffeomorph_apply hc le_top hX 0 1)]
  exact mpullback_timeDependentFlowOf_prodIccMoserField_apply h₀ h₁ hρ hρc hρ1 hnd p.1 p.2

end Extension

end IsCouplingForm

end SymplecticGeometry

end
