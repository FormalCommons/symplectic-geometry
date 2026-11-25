/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Sphere
public import SymplecticGeometry.Geometry.Lie.Exponential.Circle
public import TauCeti.Geometry.Manifold.DeRham.Circle
public import TauCeti.Geometry.Manifold.DifferentialForm.LieDeriv
public import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Submersion
public import TauCeti.Geometry.Manifold.FiberBundle.Principal.FundamentalVectorField
public import TauCeti.Geometry.Manifold.FiberBundle.Submersion
public import SymplecticGeometry.Topology.Algebra.Module.Alternating.Basic
public import SymplecticGeometry.Topology.VectorBundle.Complex.RestrictScalars
import SymplecticGeometry.Geometry.Manifold.DeRham.Circle
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.PartitionOfUnity
import SymplecticGeometry.Geometry.Manifold.FiberBundle.Basic
import SymplecticGeometry.Geometry.Manifold.FiberBundle.Principal.BasicForm
import SymplecticGeometry.Geometry.Manifold.VectorBundle.Hermitian.CircleBundle

/-!
# Connection forms on principal circle bundles

Let `P` be a smooth principal `Circle`-bundle over a manifold `B`, with charted total space
`TauCeti.ManifoldTotalSpace Circle P` and projection `π`. A connection form on `P` is written here
as a real `1`-form `α` on the total space, the connection form `i α` with values in `i ℝ` of
McDuff–Salamon: `α` is invariant under the action of `Circle` and takes the value `1` on the
fundamental vector field of `1 ∈ ℝ`, read in the Lie algebra of `Circle` through `Circle.exp`
(`SymplecticGeometry.circleLieGenerator`).

The exterior derivative `d α` is invariant and, by Cartan's formula, vanishes on vertical vectors,
so it is basic and descends along `π`: its curvature `hα.curvature` is the unique `2`-form on `B`
whose pull-back is `d α`. The connection forms form an affine space over the `1`-forms on `B`: two
of them differ by the pull-back `π^* a` of a unique `1`-form, and adding `π^* a` adds `d a` to the
curvature. Every bundle over a Hausdorff, σ-compact, finite-dimensional base has a connection
form, glued with a partition of unity from the pull-backs `θ^* dθ` of the angular form of the
circle along the fibre coordinates of local trivializations. In the trivialization of a local
section `σ`, a connection form is `θ^* dθ + π^* (σ^* α)`.

## Main definitions

* `SymplecticGeometry.IsCircleConnectionForm α`: `α` is a connection form.
* `SymplecticGeometry.IsCircleConnectionForm.curvature`: the curvature of a connection form.

## Main results

* `SymplecticGeometry.mlieDerivForm_rightFundamentalVectorField_circleLieGenerator_eq_zero`: an
  invariant form has vanishing Lie derivative along the fundamental vector field of `1`, the
  case `G = Circle` of `TauCeti.PrincipalBundle.mlieDerivForm_rightFundamentalVectorField_eq_zero`.
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
* `SymplecticGeometry.exists_isCircleConnectionForm`: existence of connection forms.
* `SymplecticGeometry.IsCircleConnectionForm.apply_eq_mpullback_add_mpullback`: the local form in
  the trivialization of a local section.
* `SymplecticGeometry.IsCircleConnectionForm.mpullback_apply_eq_mpullback_division_add`: a change
  of local section `τ = σ • g` adds `g^* dθ` to the pull-back of a connection form.
* `SymplecticGeometry.IsCircleConnectionForm.curvature_apply_eq_mextDeriv_mpullback`: near a
  point where a section `σ` is smooth, the curvature is `d (σ^* α)`.

## Implementation notes

The invariance of `α` gives `L_ξ α = 0` along the fundamental vector field `ξ` of `1`
(`TauCeti.PrincipalBundle.mlieDerivForm_rightFundamentalVectorField_eq_zero`). Cartan's formula
then gives `ι_ξ d α = 0`.

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

open Bundle Manifold MulOpposite TauCeti
open scoped Manifold ContDiff Topology

namespace SymplecticGeometry

variable {EB HB B : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  {IB : ModelWithCorners ℝ EB HB} [TopologicalSpace B] [ChartedSpace HB B] [IsManifold IB ∞ B]
  {P : B → Type*} [TopologicalSpace (TotalSpace Circle P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle Circle P] [∀ b, MulAction Circleᵐᵒᵖ (P b)] [PrincipalBundle Circle P]
  [ContMDiffFiberBundle ∞ Circle P IB (𝓡 1)]

omit [IsManifold IB ∞ B] in
/-- A vertical tangent vector of the total space of a principal `Circle`-bundle is a multiple of
the fundamental vector field of any nonzero element `ξ` of the Lie algebra of `Circle`. -/
theorem exists_eq_smul_rightFundamentalVectorField_of_mfderiv_proj_eq_zero
    {ξ : GroupLieAlgebra (𝓡 1) Circle} (hξ : ξ ≠ 0)
    {x : ManifoldTotalSpace Circle P} {v : TangentSpace (IB.prod (𝓡 1)) x}
    (hv : mfderiv (IB.prod (𝓡 1)) IB (fun y : ManifoldTotalSpace Circle P ↦
      ((ManifoldTotalSpace.homeomorph Circle P).symm y).proj) x v = 0) :
    ∃ c : ℝ, v = c • rightFundamentalVectorField (IB.prod (𝓡 1)) ξ x := by
  have hv' : v ∈ LinearMap.range (PrincipalBundle.rightFundamentalLinearMap IB (𝓡 1) x) := by
    rw [PrincipalBundle.range_rightFundamentalLinearMap_eq_ker_mfderiv_proj]
    exact hv
  obtain ⟨η, rfl⟩ := hv'
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_ne_zero' _ hξ).mp
    (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 1)) η
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

/-! ### The curvature -/

section Curvature

variable [IB.Boundaryless]

/-- A form on the total space of a principal `Circle`-bundle that is invariant under the action
has vanishing Lie derivative along the fundamental vector field of `1`: the case of `Circle` and
`circleLieGenerator` of `TauCeti.PrincipalBundle.mlieDerivForm_rightFundamentalVectorField_eq_zero`.
-/
theorem mlieDerivForm_rightFundamentalVectorField_circleLieGenerator_eq_zero {k : ℕ}
    {β : SmoothForm (IB.prod (𝓡 1)) (ManifoldTotalSpace Circle P) ℝ k}
    (hβ : ∀ z : Circle, SmoothForm.mpullback (fun x : ManifoldTotalSpace Circle P ↦ op z • x)
      (contMDiff_const_smul (op z)) β = β) :
    mlieDerivForm (rightFundamentalVectorField (IB.prod (𝓡 1)) circleLieGenerator) β.val =
      0 :=
  PrincipalBundle.mlieDerivForm_rightFundamentalVectorField_eq_zero hβ circleLieGenerator

/-- **Cartan's formula for a connection form.** The exterior derivative of a connection form
vanishes when its first argument is the fundamental vector field of `1`. -/
private theorem IsCircleConnectionForm.mextDeriv_apply_rightFundamentalVectorField
    (hα : IsCircleConnectionForm α) (x : ManifoldTotalSpace Circle P)
    (v : TangentSpace (IB.prod (𝓡 1)) x) :
    mextDeriv α.val x ![rightFundamentalVectorField (IB.prod (𝓡 1)) circleLieGenerator x, v] =
      0 := by
  have hV := (PrincipalBundle.contMDiff_rightFundamentalVectorField (P := P) (IB := IB)
    (m := 1) (n := ∞) (by simp) circleLieGenerator x).mdifferentiableAt one_ne_zero
  have h := mlieDerivForm_apply_eq_mextDeriv_add (f := fun _ ↦ (1 : ℝ))
    hα.apply_rightFundamentalVectorField (α.mdifferentiable x) hV v
  rw [mlieDerivForm_rightFundamentalVectorField_circleLieGenerator_eq_zero hα.mpullback_op_smul,
    mvfderiv_const] at h
  simpa [eq_comm] using h

/-- The exterior derivative of a connection form vanishes as soon as one of its arguments is
vertical. -/
private theorem IsCircleConnectionForm.mextDeriv_apply_eq_zero_of_vertical
    (hα : IsCircleConnectionForm α) (x : ManifoldTotalSpace Circle P)
    (v : Fin 2 → TangentSpace (IB.prod (𝓡 1)) x) (j : Fin 2)
    (hv : mfderiv (IB.prod (𝓡 1)) IB (fun y : ManifoldTotalSpace Circle P ↦
      ((ManifoldTotalSpace.homeomorph Circle P).symm y).proj) x (v j) = 0) :
    mextDeriv α.val x v = 0 := by
  set ξ := rightFundamentalVectorField (IB.prod (𝓡 1)) circleLieGenerator x
  obtain ⟨c, hc⟩ := exists_eq_smul_rightFundamentalVectorField_of_mfderiv_proj_eq_zero
    circleLieGenerator_ne_zero hv
  have hv01 : v = ![v 0, v 1] := (FinVec.etaExpand_eq _).symm
  have hfirst (w : TangentSpace (IB.prod (𝓡 1)) x) : mextDeriv α.val x ![c • ξ, w] = 0 := by
    rw [ContinuousAlternatingMap.vecCons_smul, hα.mextDeriv_apply_rightFundamentalVectorField,
      smul_zero]
  obtain rfl | rfl : j = 0 ∨ j = 1 := by fin_cases j <;> simp
  · rw [hv01]
    exact hc ▸ hfirst (v 1)
  · have hswap : ![v 0, v 1] = ![v 1, v 0] ∘ Equiv.swap 0 1 := by
      funext i
      fin_cases i <;> rfl
    rw [hv01, hswap, ← ContinuousAlternatingMap.coe_toAlternatingMap,
      AlternatingMap.map_swap _ _ zero_ne_one, neg_eq_zero]
    exact hc ▸ hfirst (v 0)

/-- The exterior derivative of a connection form is basic for the projection. -/
theorem IsCircleConnectionForm.isBasic_mextDerivₗ (hα : IsCircleConnectionForm α) :
    RoughForm.IsBasic (V := ℝ) IB (fun y : ManifoldTotalSpace Circle P ↦
      ((ManifoldTotalSpace.homeomorph Circle P).symm y).proj)
      (mextDerivₗ (IB.prod (𝓡 1)) 1 α).val :=
  PrincipalBundle.isBasic_of_mpullback_op_smul
    (fun z ↦ by rw [← SmoothForm.mextDerivₗ_mpullback, hα.mpullback_op_smul])
    fun x v j hv ↦ by
      rw [mextDerivₗ_apply]
      exact hα.mextDeriv_apply_eq_zero_of_vertical x v j hv

/-- The **curvature** of a connection form `α` on a principal `Circle`-bundle over `B`: the unique
smooth `2`-form on `B` whose pull-back along the projection is `d α`
(`IsCircleConnectionForm.curvature_eq_iff`). The curvature with values in `i ℝ` of McDuff–Salamon
is `i` times it. -/
def IsCircleConnectionForm.curvature (hα : IsCircleConnectionForm α) : SmoothForm IB B ℝ 2 :=
  SmoothForm.descendedForm (ManifoldTotalSpace.isSubmersion_proj ∞ Circle P IB (𝓡 1))
    ((FiberBundle.surjective_proj Circle P).comp
      (ManifoldTotalSpace.homeomorph Circle P).symm.surjective)
    (mextDerivₗ (IB.prod (𝓡 1)) 1 α) hα.isBasic_mextDerivₗ

theorem IsCircleConnectionForm.curvature_def (hα : IsCircleConnectionForm α) :
    hα.curvature = SmoothForm.descendedForm
      (ManifoldTotalSpace.isSubmersion_proj ∞ Circle P IB (𝓡 1))
      ((FiberBundle.surjective_proj Circle P).comp
        (ManifoldTotalSpace.homeomorph Circle P).symm.surjective)
      (mextDerivₗ (IB.prod (𝓡 1)) 1 α) hα.isBasic_mextDerivₗ :=
  (rfl)

/-- The pull-back of the curvature of a connection form `α` along the projection is `d α`. -/
@[simp]
theorem IsCircleConnectionForm.mpullback_curvature (hα : IsCircleConnectionForm α) :
    SmoothForm.mpullback (fun y : ManifoldTotalSpace Circle P ↦
        ((ManifoldTotalSpace.homeomorph Circle P).symm y).proj)
      (ManifoldTotalSpace.contMDiff_proj ∞ Circle P IB (𝓡 1)) hα.curvature =
      mextDerivₗ (IB.prod (𝓡 1)) 1 α :=
  SmoothForm.mpullback_descendedForm

/-- The curvature of a connection form `α` is the only `2`-form on the base whose pull-back along
the projection is `d α`. -/
theorem IsCircleConnectionForm.curvature_eq_iff (hα : IsCircleConnectionForm α)
    {β : SmoothForm IB B ℝ 2} :
    hα.curvature = β ↔ SmoothForm.mpullback (fun y : ManifoldTotalSpace Circle P ↦
        ((ManifoldTotalSpace.homeomorph Circle P).symm y).proj)
      (ManifoldTotalSpace.contMDiff_proj ∞ Circle P IB (𝓡 1)) β =
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
    IsCircleConnectionForm (α + SmoothForm.mpullback (fun y : ManifoldTotalSpace Circle P ↦
      ((ManifoldTotalSpace.homeomorph Circle P).symm y).proj)
      (ManifoldTotalSpace.contMDiff_proj ∞ Circle P IB (𝓡 1)) a) where
  mpullback_op_smul z := by
    rw [map_add, hα.mpullback_op_smul, PrincipalBundle.mpullback_op_smul_mpullback_proj]
  apply_rightFundamentalVectorField x := by
    rw [Submodule.coe_add, Pi.add_apply, ContinuousAlternatingMap.add_apply,
      hα.apply_rightFundamentalVectorField, SmoothForm.mpullback_apply_one,
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
      (fun y : ManifoldTotalSpace Circle P ↦ ((ManifoldTotalSpace.homeomorph Circle P).symm y).proj)
      (ManifoldTotalSpace.contMDiff_proj ∞ Circle P IB (𝓡 1)) a := by
  have hsurj := (FiberBundle.surjective_proj Circle P).comp
    (ManifoldTotalSpace.homeomorph Circle P).symm.surjective
  have hsub := ManifoldTotalSpace.isSubmersion_proj ∞ Circle P IB (𝓡 1)
  -- The difference `β - α` is invariant and vanishes on vertical vectors, so it is basic.
  have hbasic := PrincipalBundle.isBasic_of_mpullback_op_smul (β := β - α)
    (fun z ↦ by rw [map_sub, hα.mpullback_op_smul, hβ.mpullback_op_smul]) fun x v j hv ↦ by
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
        smul_zero, add_zero]
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
    MDifferentiableAt (IB.prod (𝓡 1)) (𝓡 1) (fun x : ManifoldTotalSpace Circle P ↦
      (e ((ManifoldTotalSpace.homeomorph Circle P).symm x)).2) x)
include hθ

omit [IsManifold IB ∞ B] [ContMDiffFiberBundle ∞ Circle P IB (𝓡 1)] in
/-- Let `e` be an equivariant trivialization whose fibre coordinate `θ` is differentiable over its
base set. Over the base set, `θ^* dθ`, the pull-back of the angular form of the circle along `θ`,
is invariant under the action of `Circle`. -/
theorem mpullback_op_smul_mpullback_trivialization_snd {x : ManifoldTotalSpace Circle P}
    (hx : ((ManifoldTotalSpace.homeomorph Circle P).symm x).proj ∈ e.baseSet) (z : Circle) :
    TauCeti.mpullback (IB.prod (𝓡 1)) (IB.prod (𝓡 1))
      (fun y : ManifoldTotalSpace Circle P ↦ op z • y)
      (TauCeti.mpullback (IB.prod (𝓡 1)) (𝓡 1) (fun x : ManifoldTotalSpace Circle P ↦
        (e ((ManifoldTotalSpace.homeomorph Circle P).symm x)).2) circleAngularForm) x =
      TauCeti.mpullback (IB.prod (𝓡 1)) (𝓡 1) (fun x : ManifoldTotalSpace Circle P ↦
        (e ((ManifoldTotalSpace.homeomorph Circle P).symm x)).2) circleAngularForm x := by
  set θ := fun x : ManifoldTotalSpace Circle P ↦
    (e ((ManifoldTotalSpace.homeomorph Circle P).symm x)).2
  have hS := e.open_baseSet.preimage
    (ManifoldTotalSpace.contMDiff_proj ∞ Circle P IB (𝓡 1)).continuous
  have hzx : ((ManifoldTotalSpace.homeomorph Circle P).symm (op z • x)).proj ∈ e.baseSet := by
    simpa [ManifoldTotalSpace.homeomorph_symm_smul] using hx
  have hsmul : MDifferentiableAt (IB.prod (𝓡 1)) (IB.prod (𝓡 1))
      (fun y : ManifoldTotalSpace Circle P ↦ op z • y) x :=
    (contMDiff_const_smul (I := IB.prod (𝓡 1)) (n := 1) (op z) x).mdifferentiableAt one_ne_zero
  have hmul : MDifferentiableAt (𝓡 1) (𝓡 1) (fun w : Circle ↦ w * z) (θ x) :=
    (contMDiff_mul_right (I := 𝓡 1) (n := 1) (a := z) _).mdifferentiableAt one_ne_zero
  -- Near `x`, the fibre coordinate of `y • z` is that of `y` times `z`.
  have heq : θ ∘ (fun y ↦ op z • y) =ᶠ[𝓝 x] (fun w : Circle ↦ w * z) ∘ θ := by
    filter_upwards [hS.mem_nhds hx] with y hy
    simp only [Function.comp_apply, θ, ManifoldTotalSpace.homeomorph_symm_smul]
    exact e.snd_apply_smul hy _ z
  rw [← mpullback_comp_at hsmul (hθ _ hzx), heq.mpullback_eq,
    mpullback_comp_at (hθ _ hx) hmul,
    mpullback_mul_right_circleAngularForm]

omit [IsManifold IB ∞ B] [ContMDiffFiberBundle ∞ Circle P IB (𝓡 1)] in
/-- Let `e` be an equivariant trivialization whose fibre coordinate `θ` is differentiable over its
base set. Over the base set, `θ^* dθ`, the pull-back of the angular form of the circle along `θ`,
takes the value `1` on the fundamental vector field of `1`. -/
theorem mpullback_trivialization_snd_apply_rightFundamentalVectorField
    {x : ManifoldTotalSpace Circle P}
    (hx : ((ManifoldTotalSpace.homeomorph Circle P).symm x).proj ∈ e.baseSet) :
    TauCeti.mpullback (IB.prod (𝓡 1)) (𝓡 1) (fun x : ManifoldTotalSpace Circle P ↦
        (e ((ManifoldTotalSpace.homeomorph Circle P).symm x)).2) circleAngularForm x
      ![rightFundamentalVectorField (IB.prod (𝓡 1)) circleLieGenerator x] = 1 := by
  set θ := fun x : ManifoldTotalSpace Circle P ↦
    (e ((ManifoldTotalSpace.homeomorph Circle P).symm x)).2
  have horb := PrincipalBundle.mdifferentiableAt_orbit (IB := IB) (IG := 𝓡 1) (n := ∞)
    (by simp) x 1
  have hθx : MDifferentiableAt (IB.prod (𝓡 1)) (𝓡 1) θ (op (1 : Circle) • x) := by
    rw [op_one, one_smul]
    exact hθ _ hx
  -- Along the orbit of `x`, the fibre coordinate is left multiplication by `θ x`.
  have hcomp : θ ∘ (fun g : Circle ↦ op g • x) = fun g ↦ θ x * g :=
    funext fun g ↦ by
      simp only [Function.comp_apply, θ, ManifoldTotalSpace.homeomorph_symm_smul]
      exact e.snd_apply_smul hx _ g
  have hv : mfderiv (IB.prod (𝓡 1)) (𝓡 1) θ x
      (rightFundamentalVectorField (IB.prod (𝓡 1)) circleLieGenerator x) =
      mfderiv (𝓡 1) (𝓡 1) (fun g ↦ θ x * g) 1 circleLieGenerator := by
    rw [rightFundamentalVectorField_apply, ← hcomp, mfderiv_comp_of_eq hθx horb rfl, op_one,
      one_smul]
    rfl
  have hL := DFunLike.congr_fun (congrFun (mpullback_mul_left_circleAngularForm (θ x)) 1)
    ![circleLieGenerator]
  rw [mpullback_apply, mul_one] at hL
  have hvec : (fun i ↦ mfderiv (IB.prod (𝓡 1)) (𝓡 1) θ x
      (![rightFundamentalVectorField (IB.prod (𝓡 1)) circleLieGenerator x] i)) =
      fun i ↦ mfderiv (𝓡 1) (𝓡 1) (fun g ↦ θ x * g) 1 (![circleLieGenerator] i) := by
    funext i
    fin_cases i
    exact hv
  rw [mpullback_apply, hvec]
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
    (hvw : mfderiv (IB.prod (𝓡 1)) IB (fun y : ManifoldTotalSpace Circle P ↦
        ((ManifoldTotalSpace.homeomorph Circle P).symm y).proj) x v =
      mfderiv (IB.prod (𝓡 1)) IB (fun y : ManifoldTotalSpace Circle P ↦
        ((ManifoldTotalSpace.homeomorph Circle P).symm y).proj) y w) :
    α.val x ![v] - TauCeti.mpullback (IB.prod (𝓡 1)) (𝓡 1) (fun x : ManifoldTotalSpace Circle P ↦
        (e ((ManifoldTotalSpace.homeomorph Circle P).symm x)).2) circleAngularForm x ![v] =
      α.val y ![w] - TauCeti.mpullback (IB.prod (𝓡 1)) (𝓡 1) (fun x : ManifoldTotalSpace Circle P ↦
        (e ((ManifoldTotalSpace.homeomorph Circle P).symm x)).2) circleAngularForm y ![w] := by
  set p := fun x : ManifoldTotalSpace Circle P ↦
    ((ManifoldTotalSpace.homeomorph Circle P).symm x).proj
  set ℓ := TauCeti.mpullback (IB.prod (𝓡 1)) (𝓡 1) (fun x : ManifoldTotalSpace Circle P ↦
    (e ((ManifoldTotalSpace.homeomorph Circle P).symm x)).2) circleAngularForm
  -- `x = y • g` for some `g`.
  obtain ⟨g, rfl⟩ := PrincipalBundle.exists_op_smul_eq_of_proj_eq hxy
  have hgd : MDifferentiableAt (IB.prod (𝓡 1)) (IB.prod (𝓡 1))
      (fun z : ManifoldTotalSpace Circle P ↦ op g • z) y :=
    (contMDiff_const_smul (I := IB.prod (𝓡 1)) (n := 1) (op g) y).mdifferentiableAt one_ne_zero
  set u := mfderiv (IB.prod (𝓡 1)) (IB.prod (𝓡 1)) (fun z : ManifoldTotalSpace Circle P ↦
    op g • z) y w
  -- `v - u` is vertical, so it is a multiple of the fundamental vector field.
  have hvert : mfderiv (IB.prod (𝓡 1)) IB p (op g • y) (v - u) = 0 := by
    have h := mfderiv_comp y ((ManifoldTotalSpace.contMDiff_proj 1 Circle P IB (𝓡 1)
      (op g • y)).mdifferentiableAt one_ne_zero) hgd
    rw [show p ∘ (fun z ↦ op g • z) = p from PrincipalBundle.proj_comp_op_smul g] at h
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
    rw [mpullback_apply] at h
    refine Eq.trans ?_ h
    congr 1
    -- The outer `Eq.symm` makes Lean read the vector off the goal's right side.
    exact Eq.symm (FinVec.etaExpand_eq _).symm
  rw [hvu, ContinuousAlternatingMap.vecCons_add, ContinuousAlternatingMap.vecCons_smul,
    ContinuousAlternatingMap.vecCons_add, ContinuousAlternatingMap.vecCons_smul, hαu, hℓu,
    hα.apply_rightFundamentalVectorField,
    mpullback_trivialization_snd_apply_rightFundamentalVectorField hθ (hxy ▸ hy)]
  ring

end Local

/-! ### Existence -/

/-- **Existence of connection forms.** Every smooth principal `Circle`-bundle over a Hausdorff,
σ-compact, finite-dimensional base has a connection form. It is glued, with a smooth partition of
unity of the base, from the pull-backs of the angular form along the fibre coordinates of the
trivializations of the atlas. -/
theorem exists_isCircleConnectionForm [FiniteDimensional ℝ EB] [T2Space B]
    [SigmaCompactSpace B] :
    ∃ α : SmoothForm (IB.prod (𝓡 1)) (ManifoldTotalSpace Circle P) ℝ 1,
      IsCircleConnectionForm α := by
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate IB isClosed_univ
    (fun b : B ↦ (trivializationAt Circle P b).baseSet)
    (fun b ↦ (trivializationAt Circle P b).open_baseSet)
    (fun b _ ↦ Set.mem_iUnion.2 ⟨b, FiberBundle.mem_baseSet_trivializationAt' b⟩)
  set p := fun x : ManifoldTotalSpace Circle P ↦
    ((ManifoldTotalSpace.homeomorph Circle P).symm x).proj with hp
  have hpc : ContMDiff (IB.prod (𝓡 1)) IB ∞ p :=
    ManifoldTotalSpace.contMDiff_proj ∞ Circle P IB (𝓡 1)
  have hθ (b : B) : ContMDiffOn (IB.prod (𝓡 1)) (𝓡 1) ∞
      (fun x : ManifoldTotalSpace Circle P ↦
        (trivializationAt Circle P b ((ManifoldTotalSpace.homeomorph Circle P).symm x)).2)
      (p ⁻¹' (trivializationAt Circle P b).baseSet) :=
    ManifoldTotalSpace.contMDiffOn_trivialization_snd_comp _ (f := fun x ↦ x) contMDiffOn_id
      fun _ hx ↦ hx
  have hθd (b : B) (x : ManifoldTotalSpace Circle P)
      (hx : p x ∈ (trivializationAt Circle P b).baseSet) :
      ContMDiffAt (IB.prod (𝓡 1)) (𝓡 1) ∞ (fun x : ManifoldTotalSpace Circle P ↦
        (trivializationAt Circle P b ((ManifoldTotalSpace.homeomorph Circle P).symm x)).2) x :=
    (hθ b).contMDiffAt (((trivializationAt Circle P b).open_baseSet.preimage
      hpc.continuous).mem_nhds hx)
  -- The local connection forms `θ^* dθ`, glued with the partition of unity.
  set ℓ : B → RoughForm (IB.prod (𝓡 1)) (ManifoldTotalSpace Circle P) ℝ 1 := fun b ↦
    TauCeti.mpullback (IB.prod (𝓡 1)) (𝓡 1) (fun x : ManifoldTotalSpace Circle P ↦
      (trivializationAt Circle P b ((ManifoldTotalSpace.homeomorph Circle P).symm x)).2)
      circleAngularForm
  set t : B → RoughForm (IB.prod (𝓡 1)) (ManifoldTotalSpace Circle P) ℝ 1 :=
    fun b x ↦ ρ b (p x) • ℓ b x with ht
  have hsupp (b : B) (x : ManifoldTotalSpace Circle P) (hx : t b x ≠ 0) : ρ b (p x) ≠ 0 :=
    left_ne_zero_of_smul hx
  let α : SmoothForm (IB.prod (𝓡 1)) (ManifoldTotalSpace Circle P) ℝ 1 :=
    ⟨fun x ↦ ∑ᶠ b, t b x, IsSmoothForm.mem_smoothBundleForms <|
      hρ.isSmoothForm_finsum_smul_comp (fun b ↦ (trivializationAt Circle P b).open_baseSet) hpc
        fun b x hx ↦ ((isSmoothForm_circleAngularForm.contMDiff _).mpullback_form (hθd b x hx)
          (by simp)).contMDiffWithinAt⟩
  -- Over a point of the base, `α` is a finite sum.
  have hfin (x : ManifoldTotalSpace Circle P) : ∃ s : Finset B, (∀ b, ρ b (p x) ≠ 0 → b ∈ s) ∧
      ∀ y, p y = p x → α.val y = ∑ b ∈ s, t b y := by
    have h := ρ.locallyFinite.point_finite (p x)
    have hs (b : B) (hb : ρ b (p x) ≠ 0) : b ∈ h.toFinset := by simpa using hb
    exact ⟨h.toFinset, hs, fun y hy ↦ finsum_eq_sum_of_support_subset _ fun b hb ↦
      hs b (hy ▸ hsupp b y hb)⟩
  refine ⟨α, fun z ↦ ?_, fun x ↦ ?_⟩
  · refine Subtype.ext (funext fun x ↦ ?_)
    ext v
    obtain ⟨s, -, hs⟩ := hfin x
    have hpz : p (op z • x) = p x := by simp [hp, ManifoldTotalSpace.homeomorph_symm_smul]
    rw [SmoothForm.coe_mpullback, mpullback_apply, hs _ hpz, hs x rfl,
      ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.sum_apply]
    refine Finset.sum_congr rfl fun b _ ↦ ?_
    simp only [ht, hpz, ContinuousAlternatingMap.smul_apply]
    by_cases hb : ρ b (p x) = 0
    · simp [hb]
    · have hxb : p x ∈ (trivializationAt Circle P b).baseSet := hρ b (subset_tsupport _ hb)
      congr 1
      exact (mpullback_apply _ _ _ _).symm.trans (DFunLike.congr_fun
        (mpullback_op_smul_mpullback_trivialization_snd
          (fun x hx ↦ (hθd b x hx).mdifferentiableAt (by simp)) hxb z) ![v])
  · obtain ⟨s, hsmem, hs⟩ := hfin x
    have hterm (b : B) :
        t b x ![rightFundamentalVectorField (IB.prod (𝓡 1)) circleLieGenerator x] =
          ρ b (p x) := by
      simp only [ht, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
      by_cases hb : ρ b (p x) = 0
      · simp [hb]
      · rw [mpullback_trivialization_snd_apply_rightFundamentalVectorField
          (fun x hx ↦ (hθd b x hx).mdifferentiableAt (by simp)) (hρ b (subset_tsupport _ hb)),
          mul_one]
    rw [hs x rfl, ContinuousAlternatingMap.sum_apply, Finset.sum_congr rfl fun b _ ↦ hterm b,
      ← finsum_eq_sum_of_support_subset _ fun b hb ↦ hsmem b hb, ρ.sum_eq_one (Set.mem_univ _)]

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
    α.val x = TauCeti.mpullback (IB.prod (𝓡 1)) (𝓡 1) (fun y : ManifoldTotalSpace Circle P ↦
        (PrincipalBundle.trivializationOfSection σ hU hσ
          ((ManifoldTotalSpace.homeomorph Circle P).symm y)).2) circleAngularForm x +
      TauCeti.mpullback (IB.prod (𝓡 1)) IB (fun y : ManifoldTotalSpace Circle P ↦
          ((ManifoldTotalSpace.homeomorph Circle P).symm y).proj)
        (TauCeti.mpullback IB (IB.prod (𝓡 1))
          (fun b ↦ ManifoldTotalSpace.homeomorph Circle P ⟨b, σ b⟩) α.val) x := by
  set e := PrincipalBundle.trivializationOfSection σ hU hσ
  set p := fun x : ManifoldTotalSpace Circle P ↦
    ((ManifoldTotalSpace.homeomorph Circle P).symm x).proj with hp
  set θ := fun y : ManifoldTotalSpace Circle P ↦
    (e ((ManifoldTotalSpace.homeomorph Circle P).symm y)).2 with hθdef
  set s := fun b ↦ ManifoldTotalSpace.homeomorph Circle P ⟨b, σ b⟩ with hs
  have hθd (y : ManifoldTotalSpace Circle P) (hy : p y ∈ e.baseSet) :
      MDifferentiableAt (IB.prod (𝓡 1)) (𝓡 1) θ y :=
    (PrincipalBundle.contMDiffAt_snd_trivializationOfSection hσ'
      (by rwa [PrincipalBundle.baseSet_trivializationOfSection] at hy)).mdifferentiableAt
        (by simp)
  have hps (b : B) : p (s b) = b := by simp [hp, hs]
  -- The section `s` has fibre coordinate `1`.
  have hθs (b : B) : θ (s b) = 1 := by
    simp only [hθdef, hs, e, PrincipalBundle.trivializationOfSection_apply]
    rw [Homeomorph.symm_apply_apply]
    exact PrincipalBundle.division_self _
  have hsd : MDifferentiableAt IB (IB.prod (𝓡 1)) s (p x) :=
    (hσ'.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
  have hxU : p (s (p x)) ∈ e.baseSet := by
    rw [hps, PrincipalBundle.baseSet_trivializationOfSection]
    exact hx
  ext u
  set w := mfderiv IB (IB.prod (𝓡 1)) s (p x) (mfderiv (IB.prod (𝓡 1)) IB p x u)
  -- The derivative of `p ∘ s = id` is the identity, and that of `θ ∘ s = 1` vanishes.
  have hdps : mfderiv (IB.prod (𝓡 1)) IB p x u = mfderiv (IB.prod (𝓡 1)) IB p (s (p x)) w :=
    (ManifoldTotalSpace.mfderiv_proj_mfderiv_section_apply hsd _).symm
  have hdθs : mfderiv (IB.prod (𝓡 1)) (𝓡 1) θ (s (p x)) w = 0 := by
    have h := mfderiv_comp (p x) (hθd _ hxU) hsd
    rw [show θ ∘ s = fun _ ↦ (1 : Circle) from funext hθs, mfderiv_const] at h
    exact (DFunLike.congr_fun h _).symm
  have hkey := hα.sub_apply_eq_of_mfderiv_proj_eq hθd hxU (hps (p x)).symm u w hdps
  have hℓ : TauCeti.mpullback (IB.prod (𝓡 1)) (𝓡 1) θ circleAngularForm (s (p x)) ![w] = 0 := by
    rw [mpullback_apply]
    exact (circleAngularForm (θ (s (p x)))).map_coord_zero (0 : Fin 1) hdθs
  have hpull : TauCeti.mpullback (IB.prod (𝓡 1)) IB p
      (TauCeti.mpullback IB (IB.prod (𝓡 1)) s α.val) x ![u] = α.val (s (p x)) ![w] := by
    rw [mpullback_apply, mpullback_apply]
    congr 1
    exact (FinVec.etaExpand_eq _).symm
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
  set p := fun y : ManifoldTotalSpace Circle P ↦
    ((ManifoldTotalSpace.homeomorph Circle P).symm y).proj
  set θ := fun y : ManifoldTotalSpace Circle P ↦
    (PrincipalBundle.trivializationOfSection σ hU hσc
      ((ManifoldTotalSpace.homeomorph Circle P).symm y)).2
  -- Along `τ`, the fibre coordinate of the trivialization of `σ` is the transition `σ⁻¹ τ`.
  have hθt : θ ∘ t = fun b ↦ PrincipalBundle.division Circle (σ b) (τ b) :=
    funext fun b ↦ by
      simp only [θ, t, Function.comp_apply, PrincipalBundle.trivializationOfSection_apply]
      rw [Homeomorph.symm_apply_apply]
  have hxt : p (t x) ∈ U := by simpa [p, t] using hx
  have hθd : MDifferentiableAt (IB.prod (𝓡 1)) (𝓡 1) θ (t x) :=
    (PrincipalBundle.contMDiffAt_snd_trivializationOfSection hσ hxt).mdifferentiableAt (by simp)
  have hloc := hα.apply_eq_mpullback_add_mpullback hU hσc hσ hxt
  have h : TauCeti.mpullback IB (IB.prod (𝓡 1)) t α.val x =
      TauCeti.mpullback IB (IB.prod (𝓡 1)) t
        (TauCeti.mpullback (IB.prod (𝓡 1)) (𝓡 1) θ circleAngularForm +
          TauCeti.mpullback (IB.prod (𝓡 1)) IB p (TauCeti.mpullback IB (IB.prod (𝓡 1))
            (fun b ↦ ManifoldTotalSpace.homeomorph Circle P ⟨b, σ b⟩) α.val)) x :=
    mpullback_apply_congr hloc
  rw [h, mpullback_add, Pi.add_apply, ← mpullback_comp_at hτ hθd, hθt,
    ManifoldTotalSpace.mpullback_mpullback_proj_apply _ hτ]

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

/-! ### The circle bundle of a Hermitian line bundle -/

section CircleBundle

open Module TauCeti.OrthonormalFrameBundle

attribute [local instance] finrank_real_complex_fact'

variable {E' H' M F : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {I : ModelWithCorners ℝ E' H'} [TopologicalSpace M] [ChartedSpace H' M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  [Fact (finrank ℂ F = 1)]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)]
  [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℂ F V]

open scoped VectorBundle.ComplexToReal

/-- The unit circle bundle of a smooth Hermitian line bundle over a Hausdorff, σ-compact,
finite-dimensional manifold has a connection form. -/
example [ContMDiffVectorBundle ∞ F V I] (g : ContMDiffRiemannianMetric I ∞ F V)
    (hI : ∀ x (v w : V x), g.inner x (Complex.I • v) (Complex.I • w) = g.inner x v w) :
    letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
    letI : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
    letI : IsContinuousRiemannianBundle F V :=
      instIsContinuousRiemannianBundle g.toContinuousRiemannianMetric
    haveI : ContMDiffFiberBundle ∞ Circle (Fiber ℂ F V ℂ) I (𝓡 1) :=
      Bundle.contMDiffFiberBundle_circleFiber g hI
    ∃ α : SmoothForm (I.prod (𝓡 1)) (ManifoldTotalSpace Circle (Fiber ℂ F V ℂ)) ℝ 1,
      IsCircleConnectionForm α := by
  let : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
  let : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
  let : IsContinuousRiemannianBundle F V :=
    instIsContinuousRiemannianBundle g.toContinuousRiemannianMetric
  have : ContMDiffFiberBundle ∞ Circle (Fiber ℂ F V ℂ) I (𝓡 1) :=
    Bundle.contMDiffFiberBundle_circleFiber g hI
  exact exists_isCircleConnectionForm

end CircleBundle

end SymplecticGeometry
