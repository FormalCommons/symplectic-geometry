/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Lie.GroupLieAlgebra.Model
public import TauCeti.Geometry.Manifold.DifferentialForm.MapCoeff
public import TauCeti.Geometry.Manifold.FiberBundle.Principal.Connection
public import TauCeti.Geometry.Manifold.Submersion.EhresmannConnection.Basic
public import SymplecticGeometry.Geometry.Manifold.FiberBundle.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Descent
public import TauCeti.Geometry.Manifold.DifferentialForm.DegreeOne
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.MapCoeff
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Smooth
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Pullback.Descent
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Pullback.Smooth
import SymplecticGeometry.Geometry.Manifold.FiberBundle.Principal.BasicForm
import SymplecticGeometry.Geometry.Manifold.Distribution.OneFormKernel
import TauCeti.Geometry.Manifold.IsManifold.Basic

/-!
# Connection forms on principal bundles

Let `P` be a smooth principal `G`-bundle over `B`, with charted total space
`TauCeti.ManifoldTotalSpace G P`, projection `π` and Lie algebra `𝔤 = GroupLieAlgebra IG G`.
Write `R_g x = x • g` for the right action, `ξ^♯` for the fundamental vector field of `ξ ∈ 𝔤`
and `Ad` for Tau Ceti's adjoint action `TauCeti.Lie.adjointContinuousLinearMap`.

Connection forms are Tau Ceti's `TauCeti.PrincipalBundle.IsConnectionForm`: smooth `𝔤`-valued
one-forms `A` on the total space with `A(ξ^♯) = ξ` for every `ξ`, and equivariant at every point.
This file adds what the library needs on top of them: the equivariance as an identity of forms,
`R_g^* A = Ad(g⁻¹) ∘ A`, finite affine combinations, tensorial forms and the affine structure of
connection forms over them, and horizontal spaces.

A **tensorial** form of type `Ad` is a `𝔤`-valued `k`-form with the same equivariance that
vanishes as soon as one of its arguments is vertical. Tensorial forms stand for the forms on `B`
with values in the adjoint bundle `P ×_G 𝔤` (Tau Ceti's `TauCeti.AdjointBundle`, whose forms
would be Tau Ceti's `TauCeti.SmoothBundleForm`); working with them on `P` needs no vector bundle
structure on the adjoint bundle.

The **horizontal space** of a one-form `A` at `x` is the kernel of `A_x`. For a connection form it
is a complement of the vertical space `ker dπ_x`, and the action carries horizontal spaces to
horizontal spaces. When `B` and `G` are finite-dimensional, the horizontal spaces of a connection
form are a smooth Ehresmann connection on `π`.

## Main definitions

* `SymplecticGeometry.IsTensorialForm a`: `a` is a tensorial form of type `Ad`.
* `SymplecticGeometry.horizontal A x`: the kernel of `A` at `x`.

## Main results

* `TauCeti.PrincipalBundle.IsConnectionForm.mpullback_op_smul`,
  `TauCeti.PrincipalBundle.IsConnectionForm.of_mpullback_op_smul`: the equivariance of a
  connection form as an identity of forms, and the converse construction.
* `TauCeti.PrincipalBundle.isConnectionForm_sum_smul`: a combination of connection forms whose
  weights sum to one is a connection form.
* `SymplecticGeometry.IsTensorialForm.add`, `SymplecticGeometry.IsTensorialForm.smul`, … :
  tensorial forms are a vector space; `SymplecticGeometry.IsTensorialForm.apply_mfderiv_op_smul`:
  their equivariance at a point.
* `TauCeti.PrincipalBundle.IsConnectionForm.add_isTensorialForm`,
  `TauCeti.PrincipalBundle.IsConnectionForm.isTensorialForm_sub`,
  `TauCeti.PrincipalBundle.IsConnectionForm.existsUnique_eq_add`: the connection forms are an
  affine space over the tensorial one-forms.
* `SymplecticGeometry.isTensorialForm_iff_isBasic`: for a commutative structure group, the
  tensorial forms are the forms that are basic for the projection (`TauCeti.RoughForm.IsBasic`).
* `TauCeti.PrincipalBundle.IsConnectionForm.isCompl_horizontal`: the horizontal space of a
  connection form is a complement of the vertical space.
* `TauCeti.PrincipalBundle.IsConnectionForm.mfderiv_op_smul_mem_horizontal`: the action preserves
  the horizontal spaces.
* `TauCeti.PrincipalBundle.IsConnectionForm.isEhresmannConnection_horizontal`: for
  finite-dimensional `B` and `G`, the horizontal spaces of a connection form are a smooth
  Ehresmann connection (Tau Ceti's `TauCeti.IsEhresmannConnection`) on the projection; they are
  smooth because they are the kernels of `A`, which is onto `𝔤` at every point
  (`TauCeti.SmoothForm.isContMDiffDistribution_ker_degreeOneEquiv`).

## Implementation notes

The forms take their values in the model space `EG` of `G`, which is `𝔤` by definition and
carries the norm that `SmoothForm` needs, as Tau Ceti's connection forms do. The adjoint action
enters the form-level statements as Tau Ceti's `adjointContinuousLinearMap (I := IG) g`, read as
a map of `EG` by `SmoothForm.mapCoeff (F := EG) (G := EG)`. The statements
about connection forms are in Tau Ceti's namespace `TauCeti.PrincipalBundle.IsConnectionForm`, so
that dot notation finds them. The proof of `TauCeti.PrincipalBundle.isConnectionForm_sum_smul`
follows that of Tau Ceti's `TauCeti.PrincipalBundle.IsConnectionForm.smul_add_smul`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §6.3
  (connection forms on principal bundles).
* S. Kobayashi and K. Nomizu, *Foundations of Differential Geometry*, Vol. I, Interscience, 1963,
  Chapter II, §§1 and 5 (connections in principal bundles, their connection forms, and tensorial
  forms of type `ad`).
-/

public section

noncomputable section

open Bundle Manifold Module MulOpposite TauCeti TauCeti.Lie
open scoped Manifold ContDiff

variable {EB HB B : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  {IB : ModelWithCorners ℝ EB HB} [TopologicalSpace B] [ChartedSpace HB B] [IsManifold IB ∞ B]
  {EG HG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG] [TopologicalSpace HG]
  {IG : ModelWithCorners ℝ EG HG} [TopologicalSpace G] [ChartedSpace HG G] [Group G]
  [LieGroup IG ∞ G]
  {P : B → Type*} [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle G P] [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P]
  [ContMDiffFiberBundle ∞ G P IB IG]

namespace SymplecticGeometry

/-! ### Tensorial forms -/

/-- A **tensorial form** of type `Ad` on a smooth principal `G`-bundle `P`: a smooth `k`-form `a`
on the total space with values in the Lie algebra `𝔤` of `G` that is equivariant,
`R_g^* a = Ad(g⁻¹) ∘ a` for the right action `R_g` of every `g : G`, and vanishes as soon as one
of its arguments is vertical, that is, in the kernel of the derivative of the projection. These
forms stand for the `k`-forms on the base with values in the adjoint bundle
(`TauCeti.AdjointBundle`). -/
structure IsTensorialForm {k : ℕ}
    (a : SmoothForm (IB.prod IG) (ManifoldTotalSpace G P) EG k) : Prop where
  /-- A tensorial form is equivariant: its pull-back by the action of `g` is its image under
  `Ad(g⁻¹)`. -/
  mpullback_op_smul (g : G) :
    SmoothForm.mpullback (fun x : ManifoldTotalSpace G P ↦ op g • x)
      (contMDiff_const_smul (op g)) a =
        SmoothForm.mapCoeff (F := EG) (G := EG) (adjointContinuousLinearMap (I := IG) g⁻¹) a
  /-- A tensorial form is semibasic for the projection: it vanishes as soon as one of its
  arguments is vertical. -/
  isSemibasic : RoughForm.IsSemibasic (F := EG) IB
    (ManifoldTotalSpace.projContMDiffMap ∞ G P IB IG) a.val

namespace IsTensorialForm

variable {k : ℕ} {a b : SmoothForm (IB.prod IG) (ManifoldTotalSpace G P) EG k}

/-- The zero form is tensorial. -/
theorem zero :
    IsTensorialForm (0 : SmoothForm (IB.prod IG) (ManifoldTotalSpace G P) EG k) :=
  ⟨fun g ↦ by rw [map_zero, map_zero], by
    rw [ZeroMemClass.coe_zero]; exact RoughForm.isSemibasic_zero _ _⟩

/-- The sum of two tensorial forms is tensorial. -/
theorem add (ha : IsTensorialForm a) (hb : IsTensorialForm b) : IsTensorialForm (a + b) :=
  ⟨fun g ↦ by rw [map_add, map_add, ha.mpullback_op_smul, hb.mpullback_op_smul],
    SmoothForm.isSemibasic_add ha.isSemibasic hb.isSemibasic⟩

/-- A real multiple of a tensorial form is tensorial. -/
theorem smul (ha : IsTensorialForm a) (c : ℝ) : IsTensorialForm (c • a) :=
  ⟨fun g ↦ by rw [map_smul, map_smul, ha.mpullback_op_smul],
    SmoothForm.isSemibasic_smul ha.isSemibasic c⟩

/-- The negative of a tensorial form is tensorial. -/
theorem neg (ha : IsTensorialForm a) : IsTensorialForm (-a) := by
  rw [← neg_one_smul ℝ a]
  exact ha.smul (-1)

/-- The equivariance of a tensorial form at a point: its value at `x • g` on the images of
tangent vectors `v` under the derivative of the action of `g` is `Ad(g⁻¹)` applied to its value
at `x` on `v`. -/
theorem apply_mfderiv_op_smul (ha : IsTensorialForm a) (g : G) (x : ManifoldTotalSpace G P)
    (v : Fin k → TangentSpace (IB.prod IG) x) :
    a.val (op g • x) (fun i ↦ mfderiv (IB.prod IG) (IB.prod IG) (fun y ↦ op g • y) x (v i)) =
      adjointContinuousLinearMap (I := IG) g⁻¹ (a.val x v) :=
  (SmoothForm.mpullback_eq_mapCoeff_iff _).1 (ha.mpullback_op_smul g) x v

/-- The difference of two tensorial forms is tensorial. -/
theorem sub (ha : IsTensorialForm a) (hb : IsTensorialForm b) : IsTensorialForm (a - b) := by
  simpa [sub_eq_add_neg] using ha.add hb.neg

end IsTensorialForm

/-! ### Horizontal spaces -/

omit [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P] in
/-- The **horizontal space** of a `𝔤`-valued one-form `A` on the total space of a principal
bundle at `x`: the kernel of `A` at `x`. For a connection form it is a complement of the vertical
space (`IsConnectionForm.isCompl_horizontal`). -/
def horizontal
    (A : SmoothForm (IB.prod IG) (ManifoldTotalSpace G P) EG 1)
    (x : ManifoldTotalSpace G P) : Submodule ℝ (TangentSpace (IB.prod IG) x) :=
  (SmoothForm.degreeOneEquiv A x).ker

omit [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P] in
theorem horizontal_def
    (A : SmoothForm (IB.prod IG) (ManifoldTotalSpace G P) EG 1)
    (x : ManifoldTotalSpace G P) :
    horizontal A x = (SmoothForm.degreeOneEquiv A x).ker :=
  (rfl)

omit [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P] in
/-- A tangent vector is horizontal for `A` exactly when `A` vanishes on it. -/
@[simp]
theorem mem_horizontal_iff
    {A : SmoothForm (IB.prod IG) (ManifoldTotalSpace G P) EG 1}
    {x : ManifoldTotalSpace G P} {v : TangentSpace (IB.prod IG) x} :
    v ∈ horizontal A x ↔ A.val x ![v] = 0 := by
  rw [horizontal_def, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    SmoothForm.degreeOneEquiv_apply_apply_vec]

end SymplecticGeometry

/-! ### Connection forms -/

namespace TauCeti.PrincipalBundle

open SymplecticGeometry

omit [PrincipalBundle G P] in
/-- **Affine combinations of connection forms.** A combination `∑ i ∈ s, c i • A i` of
connection forms whose weights `c i` sum to `1` is a connection form. -/
theorem isConnectionForm_sum_smul {ι : Type*} (s : Finset ι)
    {A : ι → SmoothForm (IB.prod IG) (ManifoldTotalSpace G P) EG 1}
    (hA : ∀ i ∈ s, IsConnectionForm (A i)) {c : ι → ℝ} (hc : ∑ i ∈ s, c i = 1) :
    IsConnectionForm (∑ i ∈ s, c i • A i) where
  apply_rightFundamentalVectorField x ξ := by
    rw [SmoothBundleForm.sum_apply, ContinuousAlternatingMap.sum_apply,
      Finset.sum_congr rfl fun i hi ↦ by
        rw [SmoothBundleForm.smul_apply, ContinuousAlternatingMap.smul_apply,
          (hA i hi).apply_rightFundamentalVectorField]]
    -- The weights act on `ξ` as an element of the model space `EG`.
    have key (y : EG) : ∑ i ∈ s, c i • y = y := by rw [← Finset.sum_smul, hc, one_smul]
    exact key ξ
  apply_mfderiv_op_smul g x v := by
    rw [SmoothBundleForm.sum_apply, ContinuousAlternatingMap.sum_apply,
      SmoothBundleForm.sum_apply, ContinuousAlternatingMap.sum_apply]
    -- The adjoint action is read as a linear map of the model space, where the sum lives.
    refine (Finset.sum_congr rfl fun i hi ↦ ?_).trans
      (map_sum (adjointContinuousLinearMap (I := IG) g⁻¹ : EG →L[ℝ] EG) _ _).symm
    rw [SmoothBundleForm.smul_apply, ContinuousAlternatingMap.smul_apply,
      SmoothBundleForm.smul_apply, ContinuousAlternatingMap.smul_apply,
      (hA i hi).apply_mfderiv_op_smul]
    exact ((adjointContinuousLinearMap (I := IG) g⁻¹ : EG →L[ℝ] EG).map_smul _ _).symm

namespace IsConnectionForm

variable {A : SmoothForm (IB.prod IG) (ManifoldTotalSpace G P) EG 1}

/-- A one-form that takes the value `ξ` on the fundamental vector field of every `ξ` and whose
pull-back by the action of every `g` is its image under `Ad(g⁻¹)` is a connection form. -/
theorem of_mpullback_op_smul
    (h₁ : ∀ (x : ManifoldTotalSpace G P) (ξ : GroupLieAlgebra IG G),
      A.val x ![rightFundamentalVectorField (IB.prod IG) ξ x] = ξ)
    (h₂ : ∀ g : G, SmoothForm.mpullback (fun x : ManifoldTotalSpace G P ↦ op g • x)
      (contMDiff_const_smul (op g)) A =
        SmoothForm.mapCoeff (F := EG) (G := EG) (adjointContinuousLinearMap (I := IG) g⁻¹) A) :
    IsConnectionForm A where
  apply_rightFundamentalVectorField := h₁
  apply_mfderiv_op_smul g :=
    (SmoothForm.mpullback_eq_mapCoeff_iff_one (F := EG) (G := EG) _).1 (h₂ g)

/-- **The equivariance of a connection form, as forms.** The pull-back of a connection form `A`
by the action of `g` is its image `Ad(g⁻¹) ∘ A` under the adjoint action of `g⁻¹`. -/
theorem mpullback_op_smul (hA : IsConnectionForm A) (g : G) :
    SmoothForm.mpullback (fun x : ManifoldTotalSpace G P ↦ op g • x)
      (contMDiff_const_smul (op g)) A =
        SmoothForm.mapCoeff (F := EG) (G := EG) (adjointContinuousLinearMap (I := IG) g⁻¹) A :=
  (SmoothForm.mpullback_eq_mapCoeff_iff_one _).2 (hA.apply_mfderiv_op_smul g)

/-- The horizontal space of a connection form is a complement of the vertical space, the kernel
of the derivative of the projection. -/
theorem isCompl_horizontal {n : ℕ∞ω} (hA : IsConnectionForm A) (x : ManifoldTotalSpace G P) :
    IsCompl (horizontal A x)
      (mfderiv (IB.prod IG) IB (ManifoldTotalSpace.projContMDiffMap n G P IB IG) x).ker := by
  rw [ManifoldTotalSpace.coe_projContMDiffMap]
  set e : EG ≃ₗ[ℝ] _ := PrincipalBundle.verticalLinearEquiv IB IG (P := P) x
  set f : TangentSpace (IB.prod IG) x →ₗ[ℝ] EG :=
    (SmoothForm.degreeOneEquiv A x).toLinearMap
  have hf (ξ : GroupLieAlgebra IG G) : f (rightFundamentalVectorField (IB.prod IG) ξ x) = ξ := by
    rw [ContinuousLinearMap.coe_coe, SmoothForm.degreeOneEquiv_apply_apply_vec,
      hA.apply_rightFundamentalVectorField]
  have h := LinearMap.isCompl_of_proj (f := e.toLinearMap ∘ₗ f) fun v ↦ by
    rw [LinearMap.comp_apply, ← PrincipalBundle.rightFundamentalVectorField_verticalLinearEquiv_symm
      x v, hf]
    exact (PrincipalBundle.verticalLinearEquiv IB IG (P := P) x).apply_symm_apply v
  rw [LinearMap.ker_comp, LinearEquiv.ker, Submodule.comap_bot] at h
  rw [horizontal_def]
  exact h.symm

omit [PrincipalBundle G P] in
/-- The right action of `G` on the total space carries the horizontal spaces of a connection form
to horizontal spaces. -/
theorem mfderiv_op_smul_mem_horizontal (hA : IsConnectionForm A) (g : G)
    {x : ManifoldTotalSpace G P} {v : TangentSpace (IB.prod IG) x} (hv : v ∈ horizontal A x) :
    mfderiv (IB.prod IG) (IB.prod IG) (fun y : ManifoldTotalSpace G P ↦ op g • y) x v ∈
      horizontal A (op g • x) := by
  rw [mem_horizontal_iff, hA.apply_mfderiv_op_smul, mem_horizontal_iff.mp hv]
  -- The adjoint action is read as a linear map of the model space, where the form takes values.
  exact map_zero (adjointContinuousLinearMap (I := IG) g⁻¹ : EG →L[ℝ] EG)

/-- **The horizontal spaces of a connection form are a smooth Ehresmann connection** on the
projection of the principal bundle to its base: they are complements of the vertical spaces and
form a smooth distribution of rank `dim B`. -/
theorem isEhresmannConnection_horizontal [FiniteDimensional ℝ EB] [FiniteDimensional ℝ EG]
    (hA : IsConnectionForm A) :
    IsEhresmannConnection (IB.prod IG) IB ∞ (ManifoldTotalSpace.projContMDiffMap ∞ G P IB IG)
      (horizontal A) where
  mdifferentiable := ManifoldTotalSpace.mdifferentiable_projContMDiffMap
  isCompl_ker := hA.isCompl_horizontal
  surjective_mfderiv x :=
    (ManifoldTotalSpace.isSubmersion_projContMDiffMap ∞ G P IB IG).surjective_mfderiv (by simp) x
  isContMDiffDistribution := by
    have h := SmoothForm.isContMDiffDistribution_ker_degreeOneEquiv (n := ∞) A
      fun x (ξ : GroupLieAlgebra IG G) ↦
      ⟨rightFundamentalVectorField (IB.prod IG) ξ x, by
        rw [SmoothForm.degreeOneEquiv_apply_apply_vec, hA.apply_rightFundamentalVectorField]⟩
    rw [Module.finrank_prod, Nat.add_sub_cancel] at h
    rwa [show horizontal A = _ from funext (horizontal_def A)]

/-! ### The affine structure of connection forms -/

/-- Adding a tensorial one-form to a connection form gives a connection form. -/
theorem add_isTensorialForm (hA : IsConnectionForm A)
    {a : SmoothForm (IB.prod IG) (ManifoldTotalSpace G P) EG 1}
    (ha : IsTensorialForm a) : IsConnectionForm (A + a) :=
  of_mpullback_op_smul (fun x ξ ↦ by
    have ha0 : a.val x ![rightFundamentalVectorField (IB.prod IG) ξ x] = 0 :=
      ha.isSemibasic.apply_eq_zero x _ 0 (by
        rw [ManifoldTotalSpace.coe_projContMDiffMap]
        exact PrincipalBundle.mfderiv_proj_rightFundamentalVectorField x ξ)
    rw [SmoothBundleForm.add_apply, ContinuousAlternatingMap.add_apply,
      hA.apply_rightFundamentalVectorField, ha0]
    exact add_zero _) fun g ↦ by
    rw [map_add, map_add, hA.mpullback_op_smul, ha.mpullback_op_smul]

/-- The difference of two connection forms is a tensorial one-form. -/
theorem isTensorialForm_sub (hA : IsConnectionForm A)
    {A' : SmoothForm (IB.prod IG) (ManifoldTotalSpace G P) EG 1}
    (hA' : IsConnectionForm A') : IsTensorialForm (A - A') where
  mpullback_op_smul g := by
    rw [map_sub, map_sub, hA.mpullback_op_smul, hA'.mpullback_op_smul]
  isSemibasic := SmoothForm.isSemibasic_iff.mpr fun x v j hv ↦ by
    -- A vertical vector is the value of the fundamental vector field of some `ξ`.
    obtain rfl : j = 0 := Subsingleton.elim _ _
    rw [ManifoldTotalSpace.coe_projContMDiffMap] at hv
    set ξ := (PrincipalBundle.verticalLinearEquiv IB IG (P := P) x).symm ⟨v 0, hv⟩
    have hv : v = ![rightFundamentalVectorField (IB.prod IG) ξ x] := by
      funext i
      rw [Subsingleton.elim i 0, Matrix.cons_val_zero,
        PrincipalBundle.rightFundamentalVectorField_verticalLinearEquiv_symm]
    rw [hv]
    exact hA.sub_apply_rightFundamentalVectorField_eq_zero hA' x ξ

/-- **The connection forms are an affine space over the tensorial one-forms.** Any connection
form `A'` is the sum of a given connection form `A` and a unique tensorial one-form. -/
theorem existsUnique_eq_add (hA : IsConnectionForm A)
    {A' : SmoothForm (IB.prod IG) (ManifoldTotalSpace G P) EG 1}
    (hA' : IsConnectionForm A') : ∃! a, IsTensorialForm a ∧ A' = A + a :=
  ⟨A' - A, ⟨hA'.isTensorialForm_sub hA, (add_sub_cancel A A').symm⟩,
    fun a ⟨_, h⟩ ↦ by rw [h, add_sub_cancel_left]⟩

end IsConnectionForm

end TauCeti.PrincipalBundle

namespace SymplecticGeometry

/-! ### Tensorial forms for a commutative structure group -/

/-- **Tensorial forms for a commutative structure group are the basic forms.** When `G` is
commutative, its adjoint action is trivial, and a smooth `𝔤`-valued form on the total space is
tensorial exactly when it is basic for the projection. -/
theorem isTensorialForm_iff_isBasic [IsMulCommutative G] {n : ℕ∞ω} {k : ℕ}
    {a : SmoothForm (IB.prod IG) (ManifoldTotalSpace G P) EG k} :
    IsTensorialForm a ↔ RoughForm.IsBasic (V := EG) IB
      (ManifoldTotalSpace.projContMDiffMap n G P IB IG) a.val := by
  -- The adjoint action of a commutative group is trivial. Tau Ceti states it as the identity of
  -- `GroupLieAlgebra IG G`; the `show` reads it as the identity of the model space `EG`.
  have hAd (g : G) :
      SmoothForm.mapCoeff (F := EG) (G := EG) (adjointContinuousLinearMap (I := IG) g⁻¹) a = a := by
    rw [show (adjointContinuousLinearMap (I := IG) g⁻¹ : EG →L[ℝ] EG) = ContinuousLinearMap.id ℝ EG
      from adjointContinuousLinearMap_eq_id g⁻¹, SmoothForm.mapCoeff_id, LinearMap.id_apply]
  refine ⟨fun h ↦ PrincipalBundle.isBasic_of_mpullback_op_smul
      (fun g ↦ (h.mpullback_op_smul g).trans (hAd g))
      (ManifoldTotalSpace.isSemibasic_projContMDiffMap_iff.mp h.isSemibasic),
    fun h ↦ ⟨fun g ↦ ?_, ManifoldTotalSpace.isSemibasic_projContMDiffMap_iff.mp h.isSemibasic⟩⟩
  rw [hAd]
  rw [SmoothForm.mpullback_eq_iff]
  exact h.mpullback_eq ManifoldTotalSpace.mdifferentiable_projContMDiffMap
    ((contMDiff_const_smul (I := IB.prod IG) (n := ∞) (op g)).mdifferentiable (by simp))
    (PrincipalBundle.proj_comp_op_smul g)

end SymplecticGeometry

end
