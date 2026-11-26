/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Sphere
public import SymplecticGeometry.Geometry.Lie.Exponential.Circle
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.MapCoeff
public import SymplecticGeometry.Geometry.Manifold.FiberBundle.Basic
public import SymplecticGeometry.Geometry.Manifold.FiberBundle.Principal.Connection.Curvature
public import TauCeti.Geometry.Manifold.DeRham.Circle
public import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Submersion
public import TauCeti.Geometry.Manifold.FiberBundle.Principal.FundamentalVectorField
public import TauCeti.Geometry.Manifold.FiberBundle.Submersion
public import SymplecticGeometry.Topology.Algebra.Module.Alternating.Basic
import SymplecticGeometry.Geometry.Manifold.DeRham.Circle
import SymplecticGeometry.Geometry.Manifold.FiberBundle.Principal.BasicForm
import SymplecticGeometry.Geometry.Manifold.FiberBundle.Principal.Trivialization
import TauCeti.Geometry.Manifold.MFDeriv.Slice

/-!
# Connection forms on principal circle bundles

Let `P` be a smooth principal `Circle`-bundle over a manifold `B`, with charted total space
`TauCeti.ManifoldTotalSpace Circle P` and projection `π`. A connection form on `P` is written here
as a real `1`-form `α` on the total space, the connection form `i α` with values in `i ℝ` of
McDuff–Salamon: `α` is invariant under the action of `Circle` and takes the value `1` on the
fundamental vector field of `1 ∈ ℝ`, read in the Lie algebra of `Circle` through `Circle.exp`
(`SymplecticGeometry.circleLieGenerator`).

Writing `ξ₀ = circleLieGenerator`, the `𝔤`-valued form `α ξ₀` is a connection form in the sense of
`Principal/Connection/Basic.lean` exactly when `α` is a circle connection form, and its curvature
is `(d α) ξ₀`, since the bracket term vanishes on the line `𝔤`.

The exterior derivative `d α` is invariant and, as the curvature of a connection form, vanishes on
vertical vectors, so it is basic and descends along `π`: its curvature `hα.curvature` is the
unique `2`-form on `B` whose pull-back is `d α`. The connection forms form an affine space over
the `1`-forms on `B`: two of them differ by the pull-back `π^* a` of a unique `1`-form, and
adding `π^* a` adds `d a` to the curvature. Over the base set of an equivariant trivialization
with fibre coordinate `θ`, the pull-back `θ^* dθ` of the angular form of the circle satisfies
both conditions of a connection form, and in the trivialization of a local section `σ`, a
connection form is `θ^* dθ + π^* (σ^* α)`. The existence of connection forms,
`exists_isCircleConnectionForm`, is the case `G = Circle` of the general existence theorem, in
`Principal/Connection/Circle.lean`.

## Main definitions

* `SymplecticGeometry.IsCircleConnectionForm α`: `α` is a connection form.
* `SymplecticGeometry.IsCircleConnectionForm.curvature`: the curvature of a connection form.

## Main results

* `SymplecticGeometry.isConnectionForm_mapCoeff_iff`: `α ξ₀` is a connection form exactly when
  `α` is a circle connection form.
* `SymplecticGeometry.IsCircleConnectionForm.mpullback_curvature`,
  `SymplecticGeometry.IsCircleConnectionForm.curvature_eq_iff`: the curvature is the unique form on
  the base whose pull-back is `d α`.
* `SymplecticGeometry.IsCircleConnectionForm.add_mpullback`,
  `SymplecticGeometry.IsCircleConnectionForm.existsUnique_eq_add_mpullback`,
  `SymplecticGeometry.IsCircleConnectionForm.curvature_add_mpullback`: the affine structure.
* `SymplecticGeometry.mpullback_op_smul_mpullback_trivialization_snd`,
  `SymplecticGeometry.mpullback_trivialization_snd_apply_rightFundamentalVectorField`: over the
  base set of an equivariant trivialization with fibre coordinate `θ`, `θ^* dθ` is invariant and
  takes the value `1` on the fundamental vector field.
* `SymplecticGeometry.IsCircleConnectionForm.apply_eq_mpullback_add_mpullback`: the local form in
  the trivialization of a local section.
* `SymplecticGeometry.IsCircleConnectionForm.mpullback_apply_eq_mpullback_division_add`: a change
  of local section `τ = σ • g` adds `g^* dθ` to the pull-back of a connection form.
* `SymplecticGeometry.IsCircleConnectionForm.curvature_apply_eq_mextDeriv_mpullback`: near a
  point where a section `σ` is smooth, the curvature is `d (σ^* α)`.

## Implementation notes

That `d α` vanishes on vertical vectors is the case `G = Circle` of
`SymplecticGeometry.IsConnectionForm.isSemibasic_connectionCurvature`, applied to
`α ξ₀` through `SymplecticGeometry.isConnectionForm_mapCoeff_iff` and
`SymplecticGeometry.connectionCurvature_mapCoeff_toSpanSingleton`.

The two local lemmas over a trivialization are short rewrites with
`Bundle.Trivialization.mpullback_op_smul_mpullback_snd` and
`Bundle.Trivialization.mfderiv_snd_rightFundamentalVectorField`, which do not involve the angular
form.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.7
  (circle bundles, connection forms and their curvature).
* [R. Bott, L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982], §6 (the global
  angular form of a circle bundle).
* S. Kobayashi and K. Nomizu, *Foundations of Differential Geometry*, Vol. I, Interscience, 1963,
  Chapter II, §§1–5 (connection forms of principal bundles, their existence and curvature).
-/

public section

noncomputable section

open Bundle Manifold MulOpposite TauCeti TauCeti.Lie
open scoped Manifold ContDiff Topology GroupLieAlgebra

namespace SymplecticGeometry

variable {EB HB B : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  {IB : ModelWithCorners ℝ EB HB} [TopologicalSpace B] [ChartedSpace HB B] [IsManifold IB ∞ B]
  {P : B → Type*} [TopologicalSpace (TotalSpace Circle P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle Circle P] [∀ b, MulAction Circleᵐᵒᵖ (P b)] [PrincipalBundle Circle P]
  [ContMDiffFiberBundle ∞ Circle P IB (𝓡 1)]

omit [IsManifold IB ∞ B] in
/-- A vertical tangent vector of the total space of a principal `Circle`-bundle is a multiple of
the fundamental vector field of any nonzero element `ξ` of the Lie algebra of `Circle`. -/
theorem exists_eq_smul_rightFundamentalVectorField_of_mfderiv_proj_eq_zero {n : ℕ∞ω}
    {ξ : GroupLieAlgebra (𝓡 1) Circle} (hξ : ξ ≠ 0)
    {x : ManifoldTotalSpace Circle P} {v : TangentSpace (IB.prod (𝓡 1)) x}
    (hv : mfderiv (IB.prod (𝓡 1)) IB (ManifoldTotalSpace.projContMDiffMap n Circle P IB (𝓡 1)) x
      v = 0) :
    ∃ c : ℝ, v = c • rightFundamentalVectorField (IB.prod (𝓡 1)) ξ x := by
  have hv' : v ∈ LinearMap.range (PrincipalBundle.rightFundamentalLinearMap IB (𝓡 1) x) := by
    rw [PrincipalBundle.range_rightFundamentalLinearMap_eq_ker_mfderiv_proj]
    rw [ManifoldTotalSpace.coe_projContMDiffMap] at hv
    exact hv
  obtain ⟨η, rfl⟩ := hv'
  obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one finrank_groupLieAlgebra_circle hξ η
  refine ⟨c, ?_⟩
  rw [PrincipalBundle.rightFundamentalLinearMap_apply, ← hc]
  exact congrFun (rightFundamentalVectorField_smul c _) x

/-! ### Connection forms -/

variable (α : SmoothForm (IB.prod (𝓡 1)) (ManifoldTotalSpace Circle P) ℝ 1)

/-- A **connection form** on a smooth principal `Circle`-bundle `P`: a smooth real `1`-form `α` on
the total space that is invariant under the action of `Circle` and takes the value `1` on the
fundamental vector field of `1 ∈ ℝ` (`circleLieGenerator`). The connection form with values in
`i ℝ` of McDuff–Salamon is `i α`. -/
structure IsCircleConnectionForm : Prop where
  /-- A connection form is invariant under the action of `Circle`. -/
  mpullback_op_smul (z : Circle) :
    SmoothForm.mpullback (fun x : ManifoldTotalSpace Circle P ↦ op z • x)
      (contMDiff_const_smul (op z)) α = α
  /-- A connection form takes the value `1` on the fundamental vector field of `1`. -/
  apply_rightFundamentalVectorField (x : ManifoldTotalSpace Circle P) :
    α.val x ![rightFundamentalVectorField (IB.prod (𝓡 1)) circleLieGenerator x] = 1

variable {α}

/-! ### As Lie-algebra-valued connection forms -/

/-- **Circle connection forms are connection forms.** For a real one-form `α` on the total space
of a principal `Circle`-bundle, the `𝔤`-valued form `α ξ₀`, with `ξ₀ = circleLieGenerator`, is a
connection form exactly when `α` is a circle connection form. -/
theorem isConnectionForm_mapCoeff_iff :
    IsConnectionForm
        (SmoothForm.mapCoeff (ContinuousLinearMap.toSpanSingleton ℝ circleLieGenerator) α) ↔
      IsCircleConnectionForm α := by
  have hinj := SmoothForm.mapCoeff_injective (I := IB.prod (𝓡 1))
    (M := ManifoldTotalSpace Circle P) (k := 1)
    (L := ContinuousLinearMap.toSpanSingleton ℝ circleLieGenerator) fun a b h ↦
      smul_left_injective ℝ circleLieGenerator_ne_zero <| by
        simpa only [ContinuousLinearMap.toSpanSingleton_apply] using h
  have hpull (z : Circle) :
      (SmoothForm.mpullback (fun x : ManifoldTotalSpace Circle P ↦ op z • x)
        (contMDiff_const_smul (op z))
        (SmoothForm.mapCoeff (ContinuousLinearMap.toSpanSingleton ℝ circleLieGenerator) α) =
        SmoothForm.mapCoeff (adjointContinuousLinearMap z⁻¹)
          (SmoothForm.mapCoeff (ContinuousLinearMap.toSpanSingleton ℝ circleLieGenerator) α)) ↔
      SmoothForm.mpullback (fun x : ManifoldTotalSpace Circle P ↦ op z • x)
        (contMDiff_const_smul (op z)) α = α := by
    rw [SmoothForm.mpullback_mapCoeff, adjointContinuousLinearMap_eq_id, SmoothForm.mapCoeff_id,
      LinearMap.id_apply, hinj.eq_iff]
  have hval (x : ManifoldTotalSpace Circle P) (ξ : GroupLieAlgebra (𝓡 1) Circle) :
      (SmoothForm.mapCoeff (ContinuousLinearMap.toSpanSingleton ℝ circleLieGenerator) α).val x
        ![rightFundamentalVectorField (IB.prod (𝓡 1)) ξ x] =
        α.val x ![rightFundamentalVectorField (IB.prod (𝓡 1)) ξ x] • circleLieGenerator := by
    rw [SmoothForm.coe_mapCoeff, RoughForm.mapCoeff_apply,
      ContinuousLinearMap.toSpanSingleton_apply]
  refine ⟨fun hA ↦ ⟨fun z ↦ (hpull z).mp (hA.mpullback_op_smul z), fun x ↦ ?_⟩,
    fun hα ↦ ⟨fun g ↦ (hpull g).mpr (hα.mpullback_op_smul g), fun x ξ ↦ ?_⟩⟩
  · refine smul_left_injective ℝ circleLieGenerator_ne_zero ?_
    simp only [one_smul]
    rw [← hval, hA.apply_rightFundamentalVectorField]
  · obtain ⟨c, rfl⟩ :=
      exists_smul_eq_of_finrank_eq_one finrank_groupLieAlgebra_circle circleLieGenerator_ne_zero ξ
    rw [hval, rightFundamentalVectorField_smul, Pi.smul_apply,
      ContinuousAlternatingMap.vecCons_smul, hα.apply_rightFundamentalVectorField, smul_eq_mul,
      mul_one]

/-! ### The curvature -/

section Curvature

variable [IB.Boundaryless]

/-- The exterior derivative of a connection form is basic for the projection. -/
theorem IsCircleConnectionForm.isBasic_mextDerivₗ (hα : IsCircleConnectionForm α) {n : ℕ∞ω} :
    RoughForm.IsBasic (V := ℝ) IB (ManifoldTotalSpace.projContMDiffMap n Circle P IB (𝓡 1))
      (mextDerivₗ (IB.prod (𝓡 1)) 1 α).val :=
  PrincipalBundle.isBasic_of_mpullback_op_smul (β := mextDerivₗ (IB.prod (𝓡 1)) 1 α)
    (fun z ↦ by rw [← SmoothForm.mextDerivₗ_mpullback, hα.mpullback_op_smul])
    (SmoothForm.isSemibasic_iff.mpr fun x v j hv ↦ by
      have h := SmoothForm.isSemibasic_iff.mp
        (isConnectionForm_mapCoeff_iff.mpr hα).isSemibasic_connectionCurvature x v j hv
      rw [connectionCurvature_mapCoeff_toSpanSingleton, SmoothForm.coe_mapCoeff,
        RoughForm.mapCoeff_apply, ContinuousLinearMap.toSpanSingleton_apply, smul_eq_zero] at h
      exact h.resolve_right circleLieGenerator_ne_zero)

/-- The **curvature** of a connection form `α` on a principal `Circle`-bundle over `B`: the unique
smooth `2`-form on `B` whose pull-back along the projection is `d α`
(`IsCircleConnectionForm.curvature_eq_iff`). The curvature with values in `i ℝ` of McDuff–Salamon
is `i` times it. -/
def IsCircleConnectionForm.curvature (hα : IsCircleConnectionForm α) : SmoothForm IB B ℝ 2 :=
  SmoothForm.descendedForm (ManifoldTotalSpace.isSubmersion_projContMDiffMap ∞ Circle P IB (𝓡 1))
    (ManifoldTotalSpace.surjective_projContMDiffMap ∞ Circle P IB (𝓡 1))
    (mextDerivₗ (IB.prod (𝓡 1)) 1 α) hα.isBasic_mextDerivₗ

theorem IsCircleConnectionForm.curvature_def (hα : IsCircleConnectionForm α) :
    hα.curvature = SmoothForm.descendedForm
      (ManifoldTotalSpace.isSubmersion_projContMDiffMap ∞ Circle P IB (𝓡 1))
      (ManifoldTotalSpace.surjective_projContMDiffMap ∞ Circle P IB (𝓡 1))
      (mextDerivₗ (IB.prod (𝓡 1)) 1 α) hα.isBasic_mextDerivₗ :=
  (rfl)

/-- The pull-back of the curvature of a connection form `α` along the projection is `d α`. -/
theorem IsCircleConnectionForm.mpullback_curvature (hα : IsCircleConnectionForm α) :
    SmoothForm.mpullback (ManifoldTotalSpace.projContMDiffMap ∞ Circle P IB (𝓡 1))
      (ManifoldTotalSpace.projContMDiffMap ∞ Circle P IB (𝓡 1)).contMDiff hα.curvature =
      mextDerivₗ (IB.prod (𝓡 1)) 1 α :=
  SmoothForm.mpullback_descendedForm

/-- The curvature of a connection form `α` is the only `2`-form on the base whose pull-back along
the projection is `d α`. -/
theorem IsCircleConnectionForm.curvature_eq_iff (hα : IsCircleConnectionForm α)
    {β : SmoothForm IB B ℝ 2} :
    hα.curvature = β ↔
      SmoothForm.mpullback (ManifoldTotalSpace.projContMDiffMap ∞ Circle P IB (𝓡 1))
      (ManifoldTotalSpace.projContMDiffMap ∞ Circle P IB (𝓡 1)).contMDiff β =
      mextDerivₗ (IB.prod (𝓡 1)) 1 α :=
  eq_comm.trans SmoothForm.eq_descendedForm_iff

/-- The curvature of a connection form is closed. -/
theorem IsCircleConnectionForm.isClosed_curvature (hα : IsCircleConnectionForm α) :
    hα.curvature.IsClosed := by
  rw [curvature_def, SmoothForm.isClosed_descendedForm_iff]
  exact SmoothForm.isClosed_mextDerivₗ α

end Curvature

/-! ### The affine space of connection forms -/

/-- Adding the pull-back of a `1`-form on the base to a connection form gives a connection
form. -/
theorem IsCircleConnectionForm.add_mpullback (hα : IsCircleConnectionForm α)
    (a : SmoothForm IB B ℝ 1) :
    IsCircleConnectionForm (α + SmoothForm.mpullback
      (ManifoldTotalSpace.projContMDiffMap ∞ Circle P IB (𝓡 1))
      (ManifoldTotalSpace.projContMDiffMap ∞ Circle P IB (𝓡 1)).contMDiff a) where
  mpullback_op_smul z := by
    rw [map_add, hα.mpullback_op_smul, PrincipalBundle.mpullback_op_smul_mpullback_proj]
  apply_rightFundamentalVectorField x := by
    rw [Submodule.coe_add, Pi.add_apply, ContinuousAlternatingMap.add_apply,
      hα.apply_rightFundamentalVectorField, SmoothForm.mpullback_apply_one,
      -- Tau Ceti states the vanishing of `dπ` on fundamental fields with the projection written
      -- out.
      ManifoldTotalSpace.coe_projContMDiffMap,
      PrincipalBundle.mfderiv_proj_rightFundamentalVectorField,
      (a.val _).map_coord_zero (0 : Fin 1) rfl, add_zero]

variable [IB.Boundaryless]

/-- Two connection forms differ by the pull-back of a unique `1`-form on the base. The base is
assumed boundaryless, as for the curvature, because Tau Ceti's descent of basic forms along
submersions (`SmoothForm.descendedForm`) assumes it. -/
theorem IsCircleConnectionForm.existsUnique_eq_add_mpullback (hα : IsCircleConnectionForm α)
    {β : SmoothForm (IB.prod (𝓡 1)) (ManifoldTotalSpace Circle P) ℝ 1}
    (hβ : IsCircleConnectionForm β) :
    ∃! a : SmoothForm IB B ℝ 1, β = α + SmoothForm.mpullback
      (ManifoldTotalSpace.projContMDiffMap ∞ Circle P IB (𝓡 1))
      (ManifoldTotalSpace.projContMDiffMap ∞ Circle P IB (𝓡 1)).contMDiff a := by
  have hsurj := ManifoldTotalSpace.surjective_projContMDiffMap ∞ Circle P IB (𝓡 1)
  have hsub := ManifoldTotalSpace.isSubmersion_projContMDiffMap ∞ Circle P IB (𝓡 1)
  -- The difference `β - α` is invariant and vanishes on vertical vectors, so it is basic.
  have hbasic := PrincipalBundle.isBasic_of_mpullback_op_smul (n := ∞) (β := β - α)
    (fun z ↦ by rw [map_sub, hα.mpullback_op_smul, hβ.mpullback_op_smul])
    (RoughForm.isSemibasic_iff.mpr fun x v j hv ↦ by
      set ξ := rightFundamentalVectorField (IB.prod (𝓡 1)) circleLieGenerator x
      obtain rfl : j = 0 := Subsingleton.elim _ _
      obtain ⟨c, hc⟩ := exists_eq_smul_rightFundamentalVectorField_of_mfderiv_proj_eq_zero
        circleLieGenerator_ne_zero hv
      have hv0 : v = ![0 + c • ξ] := by
        funext i
        fin_cases i
        exact hc.trans (zero_add _).symm
      rw [hv0, ContinuousAlternatingMap.vecCons_add, ContinuousAlternatingMap.vecCons_smul,
        ((β - α).val x).map_coord_zero (0 : Fin 1) rfl,
        Submodule.coe_sub, Pi.sub_apply, ContinuousAlternatingMap.sub_apply,
        hα.apply_rightFundamentalVectorField, hβ.apply_rightFundamentalVectorField, sub_self,
        smul_zero, add_zero])
  refine ⟨SmoothForm.descendedForm hsub hsurj (β - α) hbasic, ?_,
    fun a' ha' ↦ SmoothForm.eq_descendedForm_iff.mpr ?_⟩
  · beta_reduce
    rw [SmoothForm.mpullback_descendedForm, add_sub_cancel]
  · rw [ha', add_sub_cancel_left]

/-- Adding the pull-back of a `1`-form `a` on the base to a connection form adds `d a` to its
curvature. -/
@[simp]
theorem IsCircleConnectionForm.curvature_add_mpullback (hα : IsCircleConnectionForm α)
    (a : SmoothForm IB B ℝ 1) :
    (hα.add_mpullback a).curvature = hα.curvature + mextDerivₗ IB 1 a := by
  rw [curvature_eq_iff, map_add, mpullback_curvature, map_add,
    SmoothForm.mextDerivₗ_mpullback]

omit [IB.Boundaryless]

/-! ### Local connection forms -/

section Local

variable {e : Trivialization Circle (π Circle P)} [e.IsEquivariant]

variable (hθ : ∀ x : ManifoldTotalSpace Circle P,
  ((ManifoldTotalSpace.homeomorph Circle P).symm x).proj ∈ e.baseSet →
    MDifferentiableAt (IB.prod (𝓡 1)) (𝓡 1) e.manifoldSnd x)
include hθ

omit [IsManifold IB ∞ B] [ContMDiffFiberBundle ∞ Circle P IB (𝓡 1)] in
/-- Let `e` be an equivariant trivialization whose fibre coordinate `θ` is differentiable over its
base set. Over the base set, `θ^* dθ`, the pull-back of the angular form of the circle along `θ`,
is invariant under the action of `Circle`. -/
theorem mpullback_op_smul_mpullback_trivialization_snd {x : ManifoldTotalSpace Circle P}
    (hx : ((ManifoldTotalSpace.homeomorph Circle P).symm x).proj ∈ e.baseSet) (z : Circle) :
    TauCeti.mpullback (IB.prod (𝓡 1)) (IB.prod (𝓡 1))
      (fun y : ManifoldTotalSpace Circle P ↦ op z • y)
      (TauCeti.mpullback (IB.prod (𝓡 1)) (𝓡 1) e.manifoldSnd circleAngularForm) x =
      TauCeti.mpullback (IB.prod (𝓡 1)) (𝓡 1) e.manifoldSnd circleAngularForm x := by
  rw [e.mpullback_op_smul_mpullback_snd hθ hx, mpullback_mul_right_circleAngularForm]

omit [IsManifold IB ∞ B] [ContMDiffFiberBundle ∞ Circle P IB (𝓡 1)] in
/-- Let `e` be an equivariant trivialization whose fibre coordinate `θ` is differentiable over its
base set. Over the base set, `θ^* dθ`, the pull-back of the angular form of the circle along `θ`,
takes the value `1` on the fundamental vector field of `1`. -/
theorem mpullback_trivialization_snd_apply_rightFundamentalVectorField
    {x : ManifoldTotalSpace Circle P}
    (hx : ((ManifoldTotalSpace.homeomorph Circle P).symm x).proj ∈ e.baseSet) :
    TauCeti.mpullback (IB.prod (𝓡 1)) (𝓡 1) e.manifoldSnd circleAngularForm x
      ![rightFundamentalVectorField (IB.prod (𝓡 1)) circleLieGenerator x] = 1 := by
  set θ := e.manifoldSnd
  have hL := DFunLike.congr_fun (congrFun (mpullback_mul_left_circleAngularForm (θ x)) 1)
    ![circleLieGenerator]
  rw [mpullback_apply_one, mul_one] at hL
  have hv : mfderiv (IB.prod (𝓡 1)) (𝓡 1) θ x
      (rightFundamentalVectorField (IB.prod (𝓡 1)) circleLieGenerator x) =
      mfderiv (𝓡 1) (𝓡 1) (fun g ↦ θ x * g) 1 circleLieGenerator :=
    (e.mfderiv_snd_rightFundamentalVectorField hx (hθ _ hx) _).trans
      (GroupLieAlgebra.mulInvariantVectorField_apply _ _)
  rw [mpullback_apply_one, hv]
  exact hL.trans circleAngularForm_one_circleLieGenerator

/-- Over the base set of an equivariant trivialization with fibre coordinate `θ`, the difference
of a connection form `α` and `θ^* dθ` takes the same value on two vectors at two points of one
fibre that have the same image under the derivative of the projection. -/
private theorem IsCircleConnectionForm.sub_apply_eq_of_mfderiv_proj_eq
    (hα : IsCircleConnectionForm α) {x y : ManifoldTotalSpace Circle P}
    (hy : ((ManifoldTotalSpace.homeomorph Circle P).symm y).proj ∈ e.baseSet)
    (hxy : ((ManifoldTotalSpace.homeomorph Circle P).symm x).proj =
      ((ManifoldTotalSpace.homeomorph Circle P).symm y).proj)
    (v : TangentSpace (IB.prod (𝓡 1)) x) (w : TangentSpace (IB.prod (𝓡 1)) y)
    {n : ℕ∞ω}
    (hvw : mfderiv (IB.prod (𝓡 1)) IB (ManifoldTotalSpace.projContMDiffMap n Circle P IB (𝓡 1)) x
        v =
      mfderiv (IB.prod (𝓡 1)) IB (ManifoldTotalSpace.projContMDiffMap n Circle P IB (𝓡 1)) y w) :
    α.val x ![v] - TauCeti.mpullback (IB.prod (𝓡 1)) (𝓡 1) e.manifoldSnd circleAngularForm x ![v] =
      α.val y ![w] -
        TauCeti.mpullback (IB.prod (𝓡 1)) (𝓡 1) e.manifoldSnd circleAngularForm y ![w] := by
  set ℓ := TauCeti.mpullback (IB.prod (𝓡 1)) (𝓡 1) e.manifoldSnd circleAngularForm
  -- `x = y • g` for some `g`.
  obtain ⟨g, rfl⟩ := PrincipalBundle.exists_op_smul_eq_of_proj_eq hxy
  have hgd : MDifferentiableAt (IB.prod (𝓡 1)) (IB.prod (𝓡 1))
      (fun z : ManifoldTotalSpace Circle P ↦ op g • z) y :=
    (contMDiff_const_smul (I := IB.prod (𝓡 1)) (n := 1) (op g) y).mdifferentiableAt one_ne_zero
  set u := mfderiv (IB.prod (𝓡 1)) (IB.prod (𝓡 1)) (fun z : ManifoldTotalSpace Circle P ↦
    op g • z) y w
  -- `v - u` is vertical, so it is a multiple of the fundamental vector field.
  have hvert : mfderiv (IB.prod (𝓡 1)) IB (ManifoldTotalSpace.projContMDiffMap n Circle P IB (𝓡 1))
      (op g • y) (v - u) = 0 := by
    have h := mfderiv_comp y
      (ManifoldTotalSpace.mdifferentiable_projContMDiffMap (n := n) (op g • y)) hgd
    rw [PrincipalBundle.proj_comp_op_smul] at h
    rw [map_sub, hvw, h]
    exact sub_eq_zero.mpr rfl
  obtain ⟨c, hc⟩ := exists_eq_smul_rightFundamentalVectorField_of_mfderiv_proj_eq_zero
    circleLieGenerator_ne_zero hvert
  have hvu : v = u + c • rightFundamentalVectorField (IB.prod (𝓡 1)) circleLieGenerator
      (op g • y) := by
    rw [← hc, add_sub_cancel]
  -- By invariance, `α` and `θ^* dθ` take the same values on `u` at `y • g` as on `w` at `y`.
  have hαu : α.val (op g • y) ![u] = α.val y ![w] := by
    have h := congrArg (fun β : SmoothForm (IB.prod (𝓡 1)) (ManifoldTotalSpace Circle P) ℝ 1 ↦
      β.val y ![w]) (hα.mpullback_op_smul g)
    simpa only [SmoothForm.mpullback_apply_one] using h
  have hℓu : ℓ (op g • y) ![u] = ℓ y ![w] := by
    have h := DFunLike.congr_fun (mpullback_op_smul_mpullback_trivialization_snd hθ hy g) ![w]
    rwa [mpullback_apply_one] at h
  rw [hvu, ContinuousAlternatingMap.vecCons_add, ContinuousAlternatingMap.vecCons_smul,
    ContinuousAlternatingMap.vecCons_add, ContinuousAlternatingMap.vecCons_smul, hαu, hℓu,
    hα.apply_rightFundamentalVectorField,
    mpullback_trivialization_snd_apply_rightFundamentalVectorField hθ (hxy ▸ hy)]
  ring

end Local

/-! ### The local form of a connection form -/

/-- **The local form of a connection form.** Let `σ` be a section of `P` that is smooth on an open
set `U` of the base, and let `θ` be the fibre coordinate of the trivialization that `σ` determines
(`TauCeti.PrincipalBundle.trivializationOfSection`). Over `U`, a connection form `α` is
`θ^* dθ + π^* (σ^* α)`, where `dθ` is the angular form of the circle and `σ` is read as a map into
the charted total space. -/
theorem IsCircleConnectionForm.apply_eq_mpullback_add_mpullback (hα : IsCircleConnectionForm α)
    {σ : ∀ b, P b} {U : Set B} (hU : IsOpen U)
    (hσ : ContinuousOn (fun b ↦ TotalSpace.mk' Circle b (σ b)) U)
    (hσ' : ContMDiffOn IB (IB.prod (𝓡 1)) ∞
      (fun b ↦ ManifoldTotalSpace.homeomorph Circle P ⟨b, σ b⟩) U)
    {x : ManifoldTotalSpace Circle P}
    (hx : ((ManifoldTotalSpace.homeomorph Circle P).symm x).proj ∈ U) :
    α.val x = TauCeti.mpullback (IB.prod (𝓡 1)) (𝓡 1)
        (PrincipalBundle.trivializationOfSection σ hU hσ).manifoldSnd circleAngularForm x +
      TauCeti.mpullback (IB.prod (𝓡 1)) IB (ManifoldTotalSpace.projContMDiffMap ∞ Circle P IB (𝓡 1))
        (TauCeti.mpullback IB (IB.prod (𝓡 1))
          (fun b ↦ ManifoldTotalSpace.homeomorph Circle P ⟨b, σ b⟩) α.val) x := by
  set e := PrincipalBundle.trivializationOfSection σ hU hσ
  set p := ⇑(ManifoldTotalSpace.projContMDiffMap ∞ Circle P IB (𝓡 1)) with hp
  have hpx (y : ManifoldTotalSpace Circle P) :
      p y = ((ManifoldTotalSpace.homeomorph Circle P).symm y).proj := by
    rw [hp, ManifoldTotalSpace.coe_projContMDiffMap]
  set θ := e.manifoldSnd with hθdef
  set s := fun b ↦ ManifoldTotalSpace.homeomorph Circle P ⟨b, σ b⟩ with hs
  have hθd (y : ManifoldTotalSpace Circle P)
      (hy : ((ManifoldTotalSpace.homeomorph Circle P).symm y).proj ∈ e.baseSet) :
      MDifferentiableAt (IB.prod (𝓡 1)) (𝓡 1) θ y := by
    exact (PrincipalBundle.contMDiffAt_snd_trivializationOfSection hσ'
      (by rwa [PrincipalBundle.baseSet_trivializationOfSection] at hy)).mdifferentiableAt
        (by simp)
  have hps (b : B) : p (s b) = b := by simp [hp, hs]
  -- The section `s` has fibre coordinate `1`.
  have hθs (b : B) : θ (s b) = 1 := by
    simp only [hθdef, hs, e, Trivialization.manifoldSnd_homeomorph,
      PrincipalBundle.trivializationOfSection_apply]
    exact PrincipalBundle.division_self _
  have hx' : p x ∈ U := by rwa [hpx]
  have hsd : MDifferentiableAt IB (IB.prod (𝓡 1)) s (p x) :=
    (hσ'.contMDiffAt (hU.mem_nhds hx')).mdifferentiableAt (by simp)
  have hxU : ((ManifoldTotalSpace.homeomorph Circle P).symm (s (p x))).proj ∈ e.baseSet := by
    rw [← hpx, hps, PrincipalBundle.baseSet_trivializationOfSection]
    exact hx'
  ext u
  set w := mfderiv IB (IB.prod (𝓡 1)) s (p x) (mfderiv (IB.prod (𝓡 1)) IB p x u)
  -- The derivative of `p ∘ s = id` is the identity, and that of `θ ∘ s = 1` vanishes.
  have hdps : mfderiv (IB.prod (𝓡 1)) IB p x u = mfderiv (IB.prod (𝓡 1)) IB p (s (p x)) w :=
    (ManifoldTotalSpace.mfderiv_proj_mfderiv_section_apply (n := ∞) hsd _).symm
  have hdθs : mfderiv (IB.prod (𝓡 1)) (𝓡 1) θ (s (p x)) w = 0 :=
    TauCeti.mfderiv_mfderiv_apply_eq_zero_of_comp_eventuallyEq_const
      (.of_eq (funext hθs : θ ∘ s = fun _ ↦ (1 : Circle))) _
  have hxy : ((ManifoldTotalSpace.homeomorph Circle P).symm x).proj =
      ((ManifoldTotalSpace.homeomorph Circle P).symm (s (p x))).proj := by
    rw [← hpx, ← hpx, hps]
  have hkey := hα.sub_apply_eq_of_mfderiv_proj_eq hθd hxU hxy u w hdps
  have hℓ : TauCeti.mpullback (IB.prod (𝓡 1)) (𝓡 1) θ circleAngularForm (s (p x)) ![w] = 0 := by
    rw [mpullback_apply_one]
    exact (circleAngularForm (θ (s (p x)))).map_coord_zero (0 : Fin 1) hdθs
  have hpull : TauCeti.mpullback (IB.prod (𝓡 1)) IB p
      (TauCeti.mpullback IB (IB.prod (𝓡 1)) s α.val) x ![u] = α.val (s (p x)) ![w] := by
    rw [mpullback_apply_one, mpullback_apply_one]
  rw [hℓ, sub_zero] at hkey
  rw [ContinuousAlternatingMap.add_apply, hpull, ← hkey]
  ring

/-- **Change of local section.** Let `σ` be a section of `P` that is smooth on an open set `U` of
the base, and `τ` a section differentiable at `x ∈ U`, both read as maps into the charted total
space. At `x`, the pull-back of a connection form `α` along `τ` is its pull-back along `σ` plus the
pull-back of the angular form `dθ` of the circle along the transition `g = σ⁻¹ τ`, the map with
`τ = σ • g` (`TauCeti.PrincipalBundle.division`): `τ^* α = σ^* α + g^* dθ`. -/
theorem IsCircleConnectionForm.mpullback_apply_eq_mpullback_division_add
    (hα : IsCircleConnectionForm α) {σ τ : ∀ b, P b} {U : Set B} (hU : IsOpen U)
    (hσ : ContMDiffOn IB (IB.prod (𝓡 1)) ∞
      (fun b ↦ ManifoldTotalSpace.homeomorph Circle P ⟨b, σ b⟩) U)
    {x : B} (hx : x ∈ U)
    (hτ : MDifferentiableAt IB (IB.prod (𝓡 1))
      (fun b ↦ ManifoldTotalSpace.homeomorph Circle P ⟨b, τ b⟩) x) :
    TauCeti.mpullback IB (IB.prod (𝓡 1))
        (fun b ↦ ManifoldTotalSpace.homeomorph Circle P ⟨b, τ b⟩) α.val x =
      TauCeti.mpullback IB (𝓡 1) (fun b ↦ PrincipalBundle.division Circle (σ b) (τ b))
          circleAngularForm x +
        TauCeti.mpullback IB (IB.prod (𝓡 1))
          (fun b ↦ ManifoldTotalSpace.homeomorph Circle P ⟨b, σ b⟩) α.val x := by
  have hσc : ContinuousOn (fun b ↦ TotalSpace.mk' Circle b (σ b)) U :=
    ManifoldTotalSpace.continuousOn_of_contMDiffOn_homeomorph hσ
  set t := fun b ↦ ManifoldTotalSpace.homeomorph Circle P ⟨b, τ b⟩
  set p := ⇑(ManifoldTotalSpace.projContMDiffMap ∞ Circle P IB (𝓡 1))
  set θ := (PrincipalBundle.trivializationOfSection σ hU hσc).manifoldSnd with hθdef
  -- Along `τ`, the fibre coordinate of the trivialization of `σ` is the transition `σ⁻¹ τ`.
  have hθt : θ ∘ t = fun b ↦ PrincipalBundle.division Circle (σ b) (τ b) :=
    funext fun b ↦ by
      simp only [hθdef, t, Function.comp_apply, Trivialization.manifoldSnd_homeomorph,
        PrincipalBundle.trivializationOfSection_apply]
  have hxt : ((ManifoldTotalSpace.homeomorph Circle P).symm (t x)).proj ∈ U := by
    simpa [t] using hx
  have hθd : MDifferentiableAt (IB.prod (𝓡 1)) (𝓡 1) θ (t x) := by
    exact (PrincipalBundle.contMDiffAt_snd_trivializationOfSection hσ hxt).mdifferentiableAt
      (by simp)
  have hloc := hα.apply_eq_mpullback_add_mpullback hU hσc hσ hxt
  have h : TauCeti.mpullback IB (IB.prod (𝓡 1)) t α.val x =
      TauCeti.mpullback IB (IB.prod (𝓡 1)) t
        (TauCeti.mpullback (IB.prod (𝓡 1)) (𝓡 1) θ circleAngularForm +
          TauCeti.mpullback (IB.prod (𝓡 1)) IB p (TauCeti.mpullback IB (IB.prod (𝓡 1))
            (fun b ↦ ManifoldTotalSpace.homeomorph Circle P ⟨b, σ b⟩) α.val)) x :=
    mpullback_apply_congr hloc
  rw [h, mpullback_add, Pi.add_apply, ← mpullback_comp_at hτ hθd, hθt]
  exact congrArg (_ + ·) (ManifoldTotalSpace.mpullback_mpullback_proj_apply (n := ∞) _ hτ)

/-- **The curvature in a local section.** At a point `x` near which a section `σ` of `P` is
smooth, read as a map into the charted total space, the curvature of a connection form `α` is the
exterior derivative of `σ^* α`. -/
theorem IsCircleConnectionForm.curvature_apply_eq_mextDeriv_mpullback [IB.Boundaryless]
    (hα : IsCircleConnectionForm α) {σ : ∀ b, P b} {x : B}
    (hσ : ContMDiffAt IB (IB.prod (𝓡 1)) ∞
      (fun b ↦ ManifoldTotalSpace.homeomorph Circle P ⟨b, σ b⟩) x) :
    hα.curvature.val x = mextDeriv (TauCeti.mpullback IB (IB.prod (𝓡 1))
      (fun b ↦ ManifoldTotalSpace.homeomorph Circle P ⟨b, σ b⟩) α.val) x := by
  rw [← mpullback_mextDeriv_at (hσ.of_le (by simp))
    ((α.isSmoothForm.contMDiff _).of_le (by simp))]
  have h := congrArg Subtype.val hα.mpullback_curvature
  rw [SmoothForm.coe_mpullback, mextDerivₗ_apply] at h
  rw [← h, ManifoldTotalSpace.mpullback_mpullback_proj_apply _ (hσ.mdifferentiableAt (by simp))]

end SymplecticGeometry
