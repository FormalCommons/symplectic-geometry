/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Wedge.Smooth.Comm
public import SymplecticGeometry.Geometry.Manifold.FiberBundle.Principal.Connection.Basic
public import TauCeti.Geometry.Lie.Adjoint.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.MapCoeff
public import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
public import TauCeti.Geometry.Manifold.DifferentialForm.VectorField
public import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
public import TauCeti.Topology.Algebra.Lie.Bracket

/-!
# The curvature of a connection form

For a Lie group `G`, write `𝔤 = GroupLieAlgebra IG G`. The **curvature** of a smooth
`𝔤`-valued one-form `A` on a manifold `M` is the `𝔤`-valued two-form
`F_A = d A + ½ [A ∧ A]`, where `[A ∧ A]` is the wedge of `A` with itself paired by the bracket
of `𝔤` (`TauCeti.lieL`). On a pair of tangent vectors it is
`F_A(v, w) = d A(v, w) + [A v, A w]`. The definition needs no principal bundle; on the total space
of a principal bundle, `A` is usually a connection form.

## Main definitions

* `SymplecticGeometry.connectionCurvature A`: the curvature `d A + ½ [A ∧ A]` of a `𝔤`-valued
  one-form `A`.

## Main results

* `SymplecticGeometry.connectionCurvature_apply`: `F_A(v, w) = d A(v, w) + [A v, A w]`.
* `SymplecticGeometry.mpullback_connectionCurvature`: the curvature commutes with pull-back by
  smooth maps.
* `SymplecticGeometry.connectionCurvature_mapCoeff`: the curvature commutes with linear maps of
  `𝔤` that preserve the bracket.
* `SymplecticGeometry.IsConnectionForm.mpullback_op_smul_connectionCurvature`: the curvature of a
  connection form is equivariant, `R_g^* F_A = Ad(g⁻¹) ∘ F_A`.
* `SymplecticGeometry.connectionCurvature_apply_horizontal`: the structure equation
  `F_A(X, Y) = -A([X, Y])` at a point near which the vector fields `X` and `Y` are horizontal,
  that is, near which `A` vanishes on them. The bracket `[X, Y]` is the usual one, Mathlib's
  `VectorField.mlieBracket`, as in Guillemin–Lerman–Sternberg. McDuff–Salamon's bracket of
  vector fields is its negative, so their structure equation has no minus sign; the formula
  `F_A = d A + ½ [A ∧ A]` is the same in both conventions.
* `SymplecticGeometry.connectionCurvature_add`: the curvature of `A + a` is
  `F_A + d a + [A ∧ a] + ½ [a ∧ a]`.

## Implementation notes

The norm on `𝔤` is the scoped one of `SymplecticGeometry.Geometry.Lie.GroupLieAlgebra.Normed`,
and the bracket of `𝔤` needs the local instance `LieGroup.minSmoothness_of_isRCLikeNormedField`;
statements of this file need `open scoped GroupLieAlgebra` and that instance.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §6.3
  (connection forms on principal bundles and their curvature).
* [V. Guillemin, E. Lerman, S. Sternberg, *Symplectic Fibrations and Multiplicity
  Diagrams*][GuilleminLermanSternberg1996], §1.3 (the sign of the bracket of vector fields).
* S. Kobayashi and K. Nomizu, *Foundations of Differential Geometry*, Vol. I, Interscience, 1963,
  Chapter II, §5 (the curvature form and the structure equation).
-/

public section

noncomputable section

open Bundle Manifold MulOpposite TauCeti TauCeti.Lie VectorField Filter
open scoped Manifold ContDiff GroupLieAlgebra Topology

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

namespace SymplecticGeometry

variable {EM HM M : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [TopologicalSpace HM]
  {IM : ModelWithCorners ℝ EM HM} [TopologicalSpace M] [ChartedSpace HM M] [IsManifold IM ∞ M]
  {EG HG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
  [TopologicalSpace HG] {IG : ModelWithCorners ℝ EG HG} [TopologicalSpace G] [ChartedSpace HG G]
  [Group G] [LieGroup IG ∞ G]

/-! ### The curvature of a Lie-algebra-valued one-form -/

/-- The **curvature** of a smooth one-form `A` on `M` with values in the Lie algebra `𝔤` of `G`:
the two-form `d A + ½ [A ∧ A]`, where `[A ∧ A]` is the wedge of `A` with itself paired by the
bracket of `𝔤`. Its value on `v, w` is `d A(v, w) + [A v, A w]` (`connectionCurvature_apply`). -/
def connectionCurvature (A : SmoothForm IM M (GroupLieAlgebra IG G) 1) :
    SmoothForm IM M (GroupLieAlgebra IG G) 2 :=
  mextDerivₗ IM 1 A +
    (1 / 2 : ℝ) •
      SmoothForm.wedgeWith (lieL ℝ (GroupLieAlgebra IG G) (GroupLieAlgebra IG G)) A A

theorem connectionCurvature_def (A : SmoothForm IM M (GroupLieAlgebra IG G) 1) :
    connectionCurvature A = mextDerivₗ IM 1 A +
      (1 / 2 : ℝ) •
        SmoothForm.wedgeWith (lieL ℝ (GroupLieAlgebra IG G) (GroupLieAlgebra IG G)) A A :=
  (rfl)

/-- The curvature on two tangent vectors: `F_A(v, w) = d A(v, w) + [A v, A w]`. -/
theorem connectionCurvature_apply (A : SmoothForm IM M (GroupLieAlgebra IG G) 1) (x : M)
    (v w : TangentSpace IM x) :
    (connectionCurvature A).val x ![v, w] =
      mextDeriv A.val x ![v, w] + ⁅A.val x ![v], A.val x ![w]⁆ := by
  rw [connectionCurvature_def, Submodule.coe_add, Pi.add_apply,
    ContinuousAlternatingMap.add_apply, mextDerivₗ_apply, Submodule.coe_smul, Pi.smul_apply,
    ContinuousAlternatingMap.smul_apply, SmoothForm.wedgeWith_apply_one_one, lieL_apply,
    lieL_apply, ← lie_skew (A.val x ![w]), sub_neg_eq_add, ← two_smul ℝ, smul_smul]
  norm_num

/-- The curvature commutes with pull-back by smooth maps: `f^* F_A = F_{f^* A}`. -/
theorem mpullback_connectionCurvature {EM' HM' M' : Type*} [NormedAddCommGroup EM']
    [NormedSpace ℝ EM'] [TopologicalSpace HM'] {IM' : ModelWithCorners ℝ EM' HM'}
    [TopologicalSpace M'] [ChartedSpace HM' M'] [IsManifold IM' ∞ M'] (f : M → M')
    (hf : ContMDiff IM IM' ∞ f) (A : SmoothForm IM' M' (GroupLieAlgebra IG G) 1) :
    SmoothForm.mpullback f hf (connectionCurvature A) =
      connectionCurvature (SmoothForm.mpullback f hf A) := by
  rw [connectionCurvature_def, connectionCurvature_def, map_add, map_smul,
    ← SmoothForm.mextDerivₗ_mpullback]
  congr 2
  exact SmoothForm.mpullback_wedgeWith _ f hf A A

/-- The curvature commutes with every linear map `L` of the Lie algebra that preserves the
bracket: `F_{L ∘ A} = L ∘ F_A`. -/
theorem connectionCurvature_mapCoeff (L : GroupLieAlgebra IG G →L[ℝ] GroupLieAlgebra IG G)
    (hL : ∀ a b, L ⁅a, b⁆ = ⁅L a, L b⁆) (A : SmoothForm IM M (GroupLieAlgebra IG G) 1) :
    connectionCurvature (SmoothForm.mapCoeff L A) =
      SmoothForm.mapCoeff L (connectionCurvature A) := by
  rw [connectionCurvature_def, connectionCurvature_def, map_add, map_smul,
    SmoothForm.mextDerivₗ_mapCoeff]
  congr 2
  exact (SmoothForm.mapCoeff_wedgeWith _ _ L L L (fun a b ↦ by simp [hL]) A A).symm

/-- **The curvature of a connection form is equivariant**: its pull-back by the action of `g` is
its image under `Ad(g⁻¹)`. -/
theorem IsConnectionForm.mpullback_op_smul_connectionCurvature {EB HB B : Type*}
    [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
    {IB : ModelWithCorners ℝ EB HB}
    [TopologicalSpace B] [ChartedSpace HB B] [IsManifold IB ∞ B]
    {P : B → Type*} [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
    [FiberBundle G P] [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P]
    [ContMDiffFiberBundle ∞ G P IB IG]
    {A : SmoothForm (IB.prod IG) (ManifoldTotalSpace G P) (GroupLieAlgebra IG G) 1}
    (hA : IsConnectionForm A) (g : G) :
    SmoothForm.mpullback (fun x : ManifoldTotalSpace G P ↦ op g • x)
        (contMDiff_const_smul (op g)) (connectionCurvature A) =
      SmoothForm.mapCoeff (adjointContinuousLinearMap g⁻¹) (connectionCurvature A) := by
  rw [mpullback_connectionCurvature, hA.mpullback_op_smul,
    connectionCurvature_mapCoeff _ (adjointContinuousLinearMap_lie g⁻¹)]

/-- **The structure equation.** If the vector fields `X` and `Y` are differentiable at `x` and
horizontal for `A` near `x`, that is, `A` vanishes on them near `x`, then the curvature of `A` on
them at `x` is `-A([X, Y](x))`. Here `[X, Y]` is the usual bracket, Mathlib's `mlieBracket`, as in
Guillemin–Lerman–Sternberg; McDuff–Salamon's bracket is its negative, so their structure equation
has no minus sign. -/
theorem connectionCurvature_apply_horizontal (A : SmoothForm IM M (GroupLieAlgebra IG G) 1)
    {X Y : (y : M) → TangentSpace IM y} {x : M}
    (hX : MDifferentiableAt IM IM.tangent (fun y ↦ (X y : TangentBundle IM M)) x)
    (hY : MDifferentiableAt IM IM.tangent (fun y ↦ (Y y : TangentBundle IM M)) x)
    (hXh : ∀ᶠ y in 𝓝 x, A.val y ![X y] = 0) (hYh : ∀ᶠ y in 𝓝 x, A.val y ![Y y] = 0) :
    (connectionCurvature A).val x ![X x, Y x] = -A.val x ![mlieBracket IM X Y x] := by
  rw [connectionCurvature_apply, SmoothForm.mextDeriv_apply_one hX hY, hXh.self_of_nhds,
    hYh.self_of_nhds, lie_self, add_zero,
    Filter.EventuallyEq.mvfderiv_eq (f := fun _ ↦ (0 : GroupLieAlgebra IG G)) hYh,
    Filter.EventuallyEq.mvfderiv_eq (f := fun _ ↦ (0 : GroupLieAlgebra IG G)) hXh,
    mvfderiv_const]
  simp

/-- **The curvature of `A + a`**: `F_{A + a} = F_A + d a + [A ∧ a] + ½ [a ∧ a]`, where the
wedges are paired by the bracket of the Lie algebra. -/
theorem connectionCurvature_add (A a : SmoothForm IM M (GroupLieAlgebra IG G) 1) :
    connectionCurvature (A + a) =
      connectionCurvature A + mextDerivₗ IM 1 a +
        SmoothForm.wedgeWith (lieL ℝ (GroupLieAlgebra IG G) (GroupLieAlgebra IG G)) A a +
        (1 / 2 : ℝ) •
          SmoothForm.wedgeWith (lieL ℝ (GroupLieAlgebra IG G) (GroupLieAlgebra IG G)) a a := by
  have hcomm := SmoothForm.wedgeWith_one_one_comm_of_anticomm
    (lieL ℝ (GroupLieAlgebra IG G) (GroupLieAlgebra IG G))
    (fun a b ↦ by rw [lieL_apply, lieL_apply, lie_skew]) a A
  rw [connectionCurvature_def, connectionCurvature_def, map_add, LinearMap.map_add₂, map_add,
    map_add, hcomm]
  module

end SymplecticGeometry

end
