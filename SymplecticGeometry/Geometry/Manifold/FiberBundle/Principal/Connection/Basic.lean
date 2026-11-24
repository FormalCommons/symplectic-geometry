/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Lie.GroupLieAlgebra.Normed
public import TauCeti.Geometry.Lie.Adjoint.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.MapCoeff
public import TauCeti.Geometry.Manifold.FiberBundle.Principal.FundamentalVectorField

/-!
# Connection forms on principal bundles

Let `P` be a smooth principal `G`-bundle over `B`, with charted total space
`TauCeti.ManifoldTotalSpace G P`, projection `π` and Lie algebra `𝔤 = GroupLieAlgebra IG G`.
Write `R_g x = x • g` for the right action, `ξ^♯` for the fundamental vector field of `ξ ∈ 𝔤`
and `Ad` for Tau Ceti's adjoint action `TauCeti.Lie.adjointContinuousLinearMap`.

A **connection form** is a smooth `𝔤`-valued one-form `A` on the total space with
`R_g^* A = Ad(g⁻¹) ∘ A` for every `g` and `A(ξ^♯) = ξ` for every `ξ`. A **tensorial** form of
type `Ad` is a `𝔤`-valued `k`-form with the same equivariance that vanishes as soon as one of its
arguments is vertical. Tensorial forms stand for the forms on `B` with values in the adjoint
bundle `P ×_G 𝔤` (Tau Ceti's `TauCeti.AdjointBundle`, whose forms would be Tau Ceti's
`TauCeti.SmoothBundleForm`); working with them on `P` needs no vector bundle structure on the
adjoint bundle.

The **horizontal space** of a one-form `A` at `x` is the kernel of `A_x`. For a connection form it
is a complement of the vertical space `ker dπ_x`, and the action carries horizontal spaces to
horizontal spaces.

## Main definitions

* `SymplecticGeometry.IsConnectionForm A`: `A` is a connection form.
* `SymplecticGeometry.IsTensorialForm a`: `a` is a tensorial form of type `Ad`.
* `SymplecticGeometry.horizontal A x`: the kernel of `A` at `x`.

## Main results

* `SymplecticGeometry.IsTensorialForm.add`, `SymplecticGeometry.IsTensorialForm.smul`, … :
  tensorial forms are a vector space.
* `SymplecticGeometry.isConnectionForm_sum_smul`: a combination of connection forms whose weights
  sum to one is a connection form.
* `SymplecticGeometry.IsConnectionForm.apply_mfderiv_op_smul`,
  `SymplecticGeometry.IsTensorialForm.apply_mfderiv_op_smul`: the equivariance at a point.
* `SymplecticGeometry.IsConnectionForm.isCompl_horizontal`: the horizontal space of a connection
  form is a complement of the vertical space.
* `SymplecticGeometry.IsConnectionForm.mfderiv_op_smul_mem_horizontal`: the action preserves the
  horizontal spaces.

## Implementation notes

The norm on `𝔤` that `SmoothForm` needs is the scoped one of
`SymplecticGeometry.Geometry.Lie.GroupLieAlgebra.Normed`; statements of this file need
`open scoped GroupLieAlgebra`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §6.3
  (connection forms on principal bundles).
* S. Kobayashi and K. Nomizu, *Foundations of Differential Geometry*, Vol. I, Interscience, 1963,
  Chapter II, §§1 and 5 (connections in principal bundles, their connection forms, and tensorial
  forms of type `ad`).
-/

public section

noncomputable section

open Bundle Manifold MulOpposite TauCeti TauCeti.Lie
open scoped Manifold ContDiff GroupLieAlgebra

namespace SymplecticGeometry

variable {EB HB B : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  {IB : ModelWithCorners ℝ EB HB} [TopologicalSpace B] [ChartedSpace HB B] [IsManifold IB ∞ B]
  {EG HG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG] [TopologicalSpace HG]
  {IG : ModelWithCorners ℝ EG HG} [TopologicalSpace G] [ChartedSpace HG G] [Group G]
  [LieGroup IG ∞ G]
  {P : B → Type*} [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle G P] [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P]
  [ContMDiffFiberBundle ∞ G P IB IG]

/-! ### Connection forms and tensorial forms -/

/-- A **connection form** on a smooth principal `G`-bundle `P`: a smooth one-form `A` on the total
space with values in the Lie algebra `𝔤` of `G` that is equivariant, `R_g^* A = Ad(g⁻¹) ∘ A` for
the right action `R_g` of every `g : G`, and takes the value `ξ` on the fundamental vector field
of every `ξ ∈ 𝔤`. -/
structure IsConnectionForm
    (A : SmoothForm (IB.prod IG) (ManifoldTotalSpace G P) (GroupLieAlgebra IG G) 1) : Prop where
  /-- A connection form is equivariant: its pull-back by the action of `g` is its image under
  `Ad(g⁻¹)`. -/
  mpullback_op_smul (g : G) :
    SmoothForm.mpullback (fun x : ManifoldTotalSpace G P ↦ op g • x)
      (contMDiff_const_smul (op g)) A = SmoothForm.mapCoeff (adjointContinuousLinearMap g⁻¹) A
  /-- A connection form takes the value `ξ` on the fundamental vector field of `ξ`. -/
  apply_rightFundamentalVectorField (x : ManifoldTotalSpace G P) (ξ : GroupLieAlgebra IG G) :
    A.val x ![rightFundamentalVectorField (IB.prod IG) ξ x] = ξ

/-- A **tensorial form** of type `Ad` on a smooth principal `G`-bundle `P`: a smooth `k`-form `a`
on the total space with values in the Lie algebra `𝔤` of `G` that is equivariant,
`R_g^* a = Ad(g⁻¹) ∘ a` for the right action `R_g` of every `g : G`, and vanishes as soon as one
of its arguments is vertical, that is, in the kernel of the derivative of the projection. These
forms stand for the `k`-forms on the base with values in the adjoint bundle
(`TauCeti.AdjointBundle`). -/
structure IsTensorialForm {k : ℕ}
    (a : SmoothForm (IB.prod IG) (ManifoldTotalSpace G P) (GroupLieAlgebra IG G) k) : Prop where
  /-- A tensorial form is equivariant: its pull-back by the action of `g` is its image under
  `Ad(g⁻¹)`. -/
  mpullback_op_smul (g : G) :
    SmoothForm.mpullback (fun x : ManifoldTotalSpace G P ↦ op g • x)
      (contMDiff_const_smul (op g)) a = SmoothForm.mapCoeff (adjointContinuousLinearMap g⁻¹) a
  /-- A tensorial form vanishes as soon as one of its arguments is vertical. -/
  apply_eq_zero_of_vertical (x : ManifoldTotalSpace G P) (v : Fin k → TangentSpace (IB.prod IG) x)
    (j : Fin k) (hv : mfderiv (IB.prod IG) IB (fun y : ManifoldTotalSpace G P ↦
      ((ManifoldTotalSpace.homeomorph G P).symm y).proj) x (v j) = 0) : a.val x v = 0

namespace IsTensorialForm

variable {k : ℕ} {a b : SmoothForm (IB.prod IG) (ManifoldTotalSpace G P) (GroupLieAlgebra IG G) k}

/-- The zero form is tensorial. -/
theorem zero :
    IsTensorialForm (0 : SmoothForm (IB.prod IG) (ManifoldTotalSpace G P)
      (GroupLieAlgebra IG G) k) :=
  ⟨fun g ↦ by rw [map_zero, map_zero], fun _ _ _ _ ↦ rfl⟩

/-- The sum of two tensorial forms is tensorial. -/
theorem add (ha : IsTensorialForm a) (hb : IsTensorialForm b) : IsTensorialForm (a + b) :=
  ⟨fun g ↦ by rw [map_add, map_add, ha.mpullback_op_smul, hb.mpullback_op_smul],
    fun x v j hv ↦ by
      rw [Submodule.coe_add, Pi.add_apply, ContinuousAlternatingMap.add_apply,
        ha.apply_eq_zero_of_vertical x v j hv, hb.apply_eq_zero_of_vertical x v j hv, add_zero]⟩

/-- A real multiple of a tensorial form is tensorial. -/
theorem smul (ha : IsTensorialForm a) (c : ℝ) : IsTensorialForm (c • a) :=
  ⟨fun g ↦ by rw [map_smul, map_smul, ha.mpullback_op_smul],
    fun x v j hv ↦ by
      rw [Submodule.coe_smul, Pi.smul_apply, ContinuousAlternatingMap.smul_apply,
        ha.apply_eq_zero_of_vertical x v j hv, smul_zero]⟩

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
      adjointContinuousLinearMap g⁻¹ (a.val x v) := by
  have h := DFunLike.congr_fun (congrFun (congrArg Subtype.val (ha.mpullback_op_smul g)) x) v
  simp only [SmoothForm.mpullback_apply, SmoothForm.coe_mapCoeff, RoughForm.mapCoeff_apply] at h
  exact h

/-- The difference of two tensorial forms is tensorial. -/
theorem sub (ha : IsTensorialForm a) (hb : IsTensorialForm b) : IsTensorialForm (a - b) := by
  simpa [sub_eq_add_neg] using ha.add hb.neg

end IsTensorialForm

/-- **Affine combinations of connection forms.** A combination `∑ i ∈ s, c i • A i` of
connection forms whose weights `c i` sum to `1` is a connection form. -/
theorem isConnectionForm_sum_smul {ι : Type*} (s : Finset ι)
    {A : ι → SmoothForm (IB.prod IG) (ManifoldTotalSpace G P) (GroupLieAlgebra IG G) 1}
    (hA : ∀ i ∈ s, IsConnectionForm (A i)) {c : ι → ℝ} (hc : ∑ i ∈ s, c i = 1) :
    IsConnectionForm (∑ i ∈ s, c i • A i) where
  mpullback_op_smul g := by
    simp only [map_sum, map_smul]
    exact Finset.sum_congr rfl fun i hi ↦ by rw [(hA i hi).mpullback_op_smul]
  apply_rightFundamentalVectorField x ξ := by
    rw [Submodule.coe_sum, Finset.sum_apply, ContinuousAlternatingMap.sum_apply,
      Finset.sum_congr rfl fun i hi ↦ by
        rw [Submodule.coe_smul, Pi.smul_apply, ContinuousAlternatingMap.smul_apply,
          (hA i hi).apply_rightFundamentalVectorField],
      ← Finset.sum_smul, hc, one_smul]

/-! ### Horizontal spaces -/

omit [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P] in
/-- The **horizontal space** of a `𝔤`-valued one-form `A` on the total space of a principal
bundle at `x`: the kernel of `A` at `x`. For a connection form it is a complement of the vertical
space (`IsConnectionForm.isCompl_horizontal`). -/
def horizontal
    (A : SmoothForm (IB.prod IG) (ManifoldTotalSpace G P) (GroupLieAlgebra IG G) 1)
    (x : ManifoldTotalSpace G P) : Submodule ℝ (TangentSpace (IB.prod IG) x) :=
  LinearMap.ker ((ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace (IB.prod IG) x)
    (GroupLieAlgebra IG G) (0 : Fin 1)).symm (A.val x) :
      TangentSpace (IB.prod IG) x →ₗ[ℝ] GroupLieAlgebra IG G)

omit [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P] in
theorem horizontal_def
    (A : SmoothForm (IB.prod IG) (ManifoldTotalSpace G P) (GroupLieAlgebra IG G) 1)
    (x : ManifoldTotalSpace G P) :
    horizontal A x =
      LinearMap.ker ((ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace (IB.prod IG) x)
        (GroupLieAlgebra IG G) (0 : Fin 1)).symm (A.val x) :
          TangentSpace (IB.prod IG) x →ₗ[ℝ] GroupLieAlgebra IG G) :=
  (rfl)

omit [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P] in
/-- A tangent vector is horizontal for `A` exactly when `A` vanishes on it. -/
@[simp]
theorem mem_horizontal_iff
    {A : SmoothForm (IB.prod IG) (ManifoldTotalSpace G P) (GroupLieAlgebra IG G) 1}
    {x : ManifoldTotalSpace G P} {v : TangentSpace (IB.prod IG) x} :
    v ∈ horizontal A x ↔ A.val x ![v] = 0 := by
  rw [horizontal_def, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    ContinuousAlternatingMap.ofSubsingleton_symm_apply_apply, Matrix.vec_single_eq_const]

namespace IsConnectionForm

variable {A : SmoothForm (IB.prod IG) (ManifoldTotalSpace G P) (GroupLieAlgebra IG G) 1}

/-- The equivariance of a connection form at a point: its value at `x • g` on the image of a
tangent vector `v` under the derivative of the action of `g` is `Ad(g⁻¹)` applied to its value at
`x` on `v`. -/
theorem apply_mfderiv_op_smul (hA : IsConnectionForm A) (g : G) (x : ManifoldTotalSpace G P)
    (v : TangentSpace (IB.prod IG) x) :
    A.val (op g • x) ![mfderiv (IB.prod IG) (IB.prod IG) (fun y ↦ op g • y) x v] =
      adjointContinuousLinearMap g⁻¹ (A.val x ![v]) := by
  have h := DFunLike.congr_fun (congrFun (congrArg Subtype.val (hA.mpullback_op_smul g)) x) ![v]
  simp only [SmoothForm.mpullback_apply_one, SmoothForm.coe_mapCoeff, RoughForm.mapCoeff_apply]
    at h
  exact h

/-- The horizontal space of a connection form is a complement of the vertical space, the kernel
of the derivative of the projection. -/
theorem isCompl_horizontal (hA : IsConnectionForm A) (x : ManifoldTotalSpace G P) :
    IsCompl (horizontal A x)
      (mfderiv (IB.prod IG) IB (fun y : ManifoldTotalSpace G P ↦
        ((ManifoldTotalSpace.homeomorph G P).symm y).proj) x).ker := by
  set e := PrincipalBundle.verticalLinearEquiv IB IG (P := P) x
  set f : TangentSpace (IB.prod IG) x →ₗ[ℝ] GroupLieAlgebra IG G :=
    ((ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace (IB.prod IG) x)
      (GroupLieAlgebra IG G) (0 : Fin 1)).symm (A.val x) :
        TangentSpace (IB.prod IG) x →ₗ[ℝ] GroupLieAlgebra IG G)
  have hf (ξ : GroupLieAlgebra IG G) : f (rightFundamentalVectorField (IB.prod IG) ξ x) = ξ := by
    rw [ContinuousLinearMap.coe_coe, ContinuousAlternatingMap.ofSubsingleton_symm_apply_apply,
      ← Matrix.vec_single_eq_const, hA.apply_rightFundamentalVectorField]
  have h := LinearMap.isCompl_of_proj (f := e.toLinearMap ∘ₗ f) fun v ↦ by
    rw [LinearMap.comp_apply, ← PrincipalBundle.rightFundamentalVectorField_verticalLinearEquiv_symm
      x v, hf, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  rw [LinearMap.ker_comp, LinearEquiv.ker, Submodule.comap_bot] at h
  rw [horizontal_def]
  exact h.symm

/-- The right action of `G` on the total space carries the horizontal spaces of a connection form
to horizontal spaces. -/
theorem mfderiv_op_smul_mem_horizontal (hA : IsConnectionForm A) (g : G)
    {x : ManifoldTotalSpace G P} {v : TangentSpace (IB.prod IG) x} (hv : v ∈ horizontal A x) :
    mfderiv (IB.prod IG) (IB.prod IG) (fun y : ManifoldTotalSpace G P ↦ op g • y) x v ∈
      horizontal A (op g • x) := by
  rw [mem_horizontal_iff, hA.apply_mfderiv_op_smul, mem_horizontal_iff.mp hv, map_zero]

end IsConnectionForm

end SymplecticGeometry

end
