/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.FiberBundle.Associated.PullbackPrincipal
public import SymplecticGeometry.Geometry.Manifold.FiberBundle.Principal.Connection.Basic
public import TauCeti.Geometry.Manifold.IsManifold.Basic
public import TauCeti.Geometry.Manifold.FiberBundle.Submersion

/-!
# The horizontal spaces induced by a connection form on an associated bundle

Let `P` be a smooth principal `G`-bundle over `B` with a connection form `A`, let `G` act smoothly
on the left on a manifold `F`, and let `M = P ×_G F` be the associated bundle, with charted total
space `TauCeti.ManifoldTotalSpace F (AssociatedBundle G P F)` and quotient map
`q (x, v) = [x, v]`.

At a point `y = [x, v]` of `M`, the connection induces the horizontal space
`dq_{(x, v)} (ker A_x × 0)`, that is, the image of the horizontal space `ker A_x` of `P` under the
derivative at `x` of the map `x' ↦ [x', v]`. It does not depend on the representative `(x, v)`:
two representatives differ by the diagonal action, `(x', v') = (x · g, g⁻¹ • v)`, the map
`x' ↦ [x', v]` is `x' ↦ [x' · g, g⁻¹ • v]`, and the action of `g` carries `ker A_x` to
`ker A_{x · g}`. The induced horizontal space is a complement of the vertical space of `M`, the
kernel of the derivative of its projection to `B`: the projection of `M` composed with
`x' ↦ [x', v]` is the projection of `P`, so the horizontal space of `M` at `[x, v]` is mapped
isomorphically onto the tangent space of the base, as that of `P` at `x` is.

## Main definitions

* `SymplecticGeometry.IsConnectionForm.associatedHorizontal`: the horizontal space at a point of
  the associated bundle induced by a connection form.

## Main results

* `SymplecticGeometry.IsConnectionForm.associatedHorizontal_eq`: the horizontal space at `[x, v]`
  is the image of `ker A_x` under the derivative of `x' ↦ [x', v]`, for every representative
  `(x, v)`.
* `SymplecticGeometry.IsConnectionForm.mem_associatedHorizontal_iff`: the membership criterion.
* `SymplecticGeometry.IsConnectionForm.isCompl_associatedHorizontal`: the induced horizontal space
  is a complement of the vertical space of the associated bundle.

## Implementation notes

The definition takes the representative `(x, v)` that
`TauCeti.AssociatedBundle.surjective_totalSpaceMk_mk` chooses for `y`. The image of `ker A_x` lies
in the tangent space at `[x, v]`, which is the tangent space at `y` only up to an equation, so the
definition transports it with Mathlib's `tangentSpaceCast`; `associatedHorizontal_eq` states it
without the cast. The derivative of `x' ↦ [x', v]` at `x` is the derivative of the quotient map at
`(x, v)` on the vectors `(w, 0)`, by the chain rule and `mfderiv_prod_left`. The definition uses
the former, since the tangent space of `P × F` is a product of tangent spaces only up to
unfolding `TangentSpace`. Complementarity needs neither the kernel nor the surjectivity of the
derivative of the quotient map: it only needs the derivative of the projection of `P` to be
surjective (`TauCeti.ManifoldTotalSpace.isRegularPoint_proj`).

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §6.3,
  Exercise 6.3.2 (the connection induced on an associated bundle).
-/

public section

noncomputable section

open Bundle Manifold MulOpposite TauCeti TauCeti.AssociatedBundle
open scoped Manifold ContDiff GroupLieAlgebra

namespace SymplecticGeometry

variable {EB HB B : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  {IB : ModelWithCorners ℝ EB HB} [TopologicalSpace B] [ChartedSpace HB B] [IsManifold IB ∞ B]
  {EG HG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG] [TopologicalSpace HG]
  {IG : ModelWithCorners ℝ EG HG} [TopologicalSpace G] [ChartedSpace HG G] [Group G]
  [LieGroup IG ∞ G]
  {EF HF F : Type*} [NormedAddCommGroup EF] [NormedSpace ℝ EF] [TopologicalSpace HF]
  {IF : ModelWithCorners ℝ EF HF} [TopologicalSpace F] [ChartedSpace HF F]
  [MulAction G F] [ContinuousSMul G F] [ContMDiffSMul IG IF ∞ G F]
  {P : B → Type*} [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle G P] [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P]
  [ContMDiffFiberBundle ∞ G P IB IG]
  {A : SmoothForm (IB.prod IG) (ManifoldTotalSpace G P) (GroupLieAlgebra IG G) 1}

/-- The class `[x, v]`, in the charted total space of `P ×_G F`, of a point `x` of the charted
total space of `P` and a point `v` of `F`. -/
local notation "⟪" x ", " v "⟫ₐ" =>
  ManifoldTotalSpace.homeomorph F (AssociatedBundle G P F)
    (TotalSpace.mk' F (TotalSpace.proj (Homeomorph.symm (ManifoldTotalSpace.homeomorph G P) x))
      (AssociatedBundle.mk G
        (TotalSpace.snd (Homeomorph.symm (ManifoldTotalSpace.homeomorph G P) x)) v))

namespace IsConnectionForm

omit [IsManifold IB ∞ B] [LieGroup IG ∞ G] [ContMDiffSMul IG IF ∞ G F]
  [ContMDiffFiberBundle ∞ G P IB IG] in
/-- The **horizontal space induced by a connection form** `A` on `P` at a point `y` of the
associated bundle `P ×_G F`: for a representative `(x, v)` of `y = [x, v]`, the image of the
horizontal space `ker A_x` under the derivative at `x` of `x' ↦ [x', v]`, which is
`dq_{(x, v)} (ker A_x × 0)` for the quotient map `q`. It does not depend on the representative
(`IsConnectionForm.associatedHorizontal_eq`). -/
@[nolint unusedArguments]
def associatedHorizontal (_hA : IsConnectionForm A)
    (y : ManifoldTotalSpace F (AssociatedBundle G P F)) :
    Submodule ℝ (TangentSpace (IB.prod IF) y) :=
  Submodule.map
    ((tangentSpaceCast (IB.prod IF) ⟪(surjective_totalSpaceMk_mk y).choose.1,
        (surjective_totalSpaceMk_mk y).choose.2⟫ₐ y).toContinuousLinearMap ∘L
      mfderiv (IB.prod IG) (IB.prod IF)
        (fun x' : ManifoldTotalSpace G P ↦ ⟪x', (surjective_totalSpaceMk_mk y).choose.2⟫ₐ)
        (surjective_totalSpaceMk_mk y).choose.1).toLinearMap
    (horizontal A (surjective_totalSpaceMk_mk y).choose.1)

/-- One step of the independence of the representative: for two representatives `(x, v)` and
`(x', v')` of `y`, the image of `ker A_x` under the derivative of `x'' ↦ [x'', v]` is contained
in the image of `ker A_{x'}` under that of `x'' ↦ [x'', v']`. -/
private theorem map_le_map_of_totalSpaceMk_mk_eq (hA : IsConnectionForm A)
    {x x' : ManifoldTotalSpace G P} {v v' : F} {y : ManifoldTotalSpace F (AssociatedBundle G P F)}
    (h : ⟪x, v⟫ₐ = y) (h' : ⟪x', v'⟫ₐ = y) :
    Submodule.map ((tangentSpaceCast (IB.prod IF) ⟪x, v⟫ₐ y).toContinuousLinearMap ∘L
        mfderiv (IB.prod IG) (IB.prod IF) (fun x'' : ManifoldTotalSpace G P ↦ ⟪x'', v⟫ₐ) x
          ).toLinearMap (horizontal A x) ≤
      Submodule.map ((tangentSpaceCast (IB.prod IF) ⟪x', v'⟫ₐ y).toContinuousLinearMap ∘L
        mfderiv (IB.prod IG) (IB.prod IF) (fun x'' : ManifoldTotalSpace G P ↦ ⟪x'', v'⟫ₐ) x'
          ).toLinearMap (horizontal A x') := by
  obtain ⟨g, hg⟩ := (totalSpaceMk_mk_eq_totalSpaceMk_mk_iff (x := (x, v)) (y := (x', v'))).1
    (h.trans h'.symm)
  simp only [Prod.mk.injEq] at hg
  obtain ⟨rfl, rfl⟩ := hg
  rintro _ ⟨w, hw, rfl⟩
  refine ⟨_, hA.mfderiv_op_smul_mem_horizontal g hw, ?_⟩
  -- The map `x'' ↦ [x'', v]` is `x'' ↦ [x'' · g, g⁻¹ • v]`.
  have hfun : (fun x'' : ManifoldTotalSpace G P ↦ ⟪x'', v⟫ₐ) =ᶠ[nhds x]
      (fun x'' : ManifoldTotalSpace G P ↦ ⟪x'', g⁻¹ • v⟫ₐ) ∘ fun x'' ↦ op g • x'' :=
    .of_forall fun x'' ↦ (totalSpaceMk_mk_op_smul_inv_smul g (x'', v)).symm
  have hq : ContMDiff (IB.prod IG) (IB.prod IF) ∞
      (fun x'' : ManifoldTotalSpace G P ↦ ⟪x'', g⁻¹ • v⟫ₐ) :=
    (contMDiff_totalSpaceMk_mk ∞ G F IB IG IF P).comp (contMDiff_id.prodMk contMDiff_const)
  have hxv : ⟪op g • x, g⁻¹ • v⟫ₐ = ⟪x, v⟫ₐ := totalSpaceMk_mk_op_smul_inv_smul g (x, v)
  simp only [hfun.mfderiv_eq, ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe]
  rw [mfderiv_comp_apply x (hq.mdifferentiableAt (by simp))
    ((contMDiff_const_smul (I := IB.prod IG) (n := ∞) (op g)).mdifferentiableAt (by simp))]
  simp only [Function.comp_apply]
  rw [tangentSpaceCast_trans hxv h]

/-- **The induced horizontal space does not depend on the representative.** At `[x, v]`, the
horizontal space induced by a connection form `A` is the image of `ker A_x` under the derivative
at `x` of `x' ↦ [x', v]`, for every representative `(x, v)`. -/
theorem associatedHorizontal_eq (hA : IsConnectionForm A) (x : ManifoldTotalSpace G P) (v : F) :
    hA.associatedHorizontal ⟪x, v⟫ₐ =
      Submodule.map (mfderiv (IB.prod IG) (IB.prod IF)
        (fun x' : ManifoldTotalSpace G P ↦ ⟪x', v⟫ₐ) x).toLinearMap (horizontal A x) := by
  have h := (surjective_totalSpaceMk_mk ⟪x, v⟫ₐ).choose_spec
  have hcast : ((tangentSpaceCast (IB.prod IF) ⟪x, v⟫ₐ ⟪x, v⟫ₐ).toContinuousLinearMap ∘L
      mfderiv (IB.prod IG) (IB.prod IF) (fun x' : ManifoldTotalSpace G P ↦ ⟪x', v⟫ₐ) x) =
      mfderiv (IB.prod IG) (IB.prod IF) (fun x' : ManifoldTotalSpace G P ↦ ⟪x', v⟫ₐ) x :=
    ContinuousLinearMap.ext fun w ↦ by simp
  rw [← hcast]
  exact le_antisymm (hA.map_le_map_of_totalSpaceMk_mk_eq h rfl)
    (hA.map_le_map_of_totalSpaceMk_mk_eq rfl h)

/-- A tangent vector to `P ×_G F` at `[x, v]` is horizontal for the connection induced by `A`
exactly when it is the image of a horizontal vector of `P` at `x` under the derivative of
`x' ↦ [x', v]`. -/
theorem mem_associatedHorizontal_iff (hA : IsConnectionForm A) {x : ManifoldTotalSpace G P}
    {v : F} {u : TangentSpace (IB.prod IF) ⟪x, v⟫ₐ} :
    u ∈ hA.associatedHorizontal ⟪x, v⟫ₐ ↔
      ∃ w ∈ horizontal A x, mfderiv (IB.prod IG) (IB.prod IF)
        (fun x' : ManifoldTotalSpace G P ↦ ⟪x', v⟫ₐ) x w = u := by
  rw [associatedHorizontal_eq, Submodule.mem_map, ContinuousLinearMap.coe_coe]

/-- **The induced horizontal space is a complement of the vertical space.** At every point of
the associated bundle `P ×_G F`, the horizontal space induced by a connection form is a complement
of the kernel of the derivative of the projection to the base. -/
theorem isCompl_associatedHorizontal (hA : IsConnectionForm A)
    (y : ManifoldTotalSpace F (AssociatedBundle G P F)) :
    IsCompl (hA.associatedHorizontal y)
      (mfderiv (IB.prod IF) IB (fun y' : ManifoldTotalSpace F (AssociatedBundle G P F) ↦
        ((ManifoldTotalSpace.homeomorph F (AssociatedBundle G P F)).symm y').proj) y).ker := by
  obtain ⟨⟨x, v⟩, rfl⟩ := surjective_totalSpaceMk_mk y
  dsimp only
  have : ContMDiffFiberBundle ∞ F (AssociatedBundle G P F) IB IF := contMDiffFiberBundle IG
  rw [associatedHorizontal_eq]
  -- The projection of `P ×_G F` composed with `x' ↦ [x', v]` is the projection of `P`.
  have hTL (w : TangentSpace (IB.prod IG) x) :
      mfderiv (IB.prod IG) IB (fun x' : ManifoldTotalSpace G P ↦
        ((ManifoldTotalSpace.homeomorph G P).symm x').proj) x w =
      tangentSpaceCast IB
        ((ManifoldTotalSpace.homeomorph F (AssociatedBundle G P F)).symm ⟪x, v⟫ₐ).proj
        ((ManifoldTotalSpace.homeomorph G P).symm x).proj
        (mfderiv (IB.prod IF) IB (fun y' : ManifoldTotalSpace F (AssociatedBundle G P F) ↦
          ((ManifoldTotalSpace.homeomorph F (AssociatedBundle G P F)).symm y').proj) ⟪x, v⟫ₐ
          (mfderiv (IB.prod IG) (IB.prod IF) (fun x' : ManifoldTotalSpace G P ↦ ⟪x', v⟫ₐ) x
            w)) := by
    have hfun : (fun x' : ManifoldTotalSpace G P ↦
        ((ManifoldTotalSpace.homeomorph G P).symm x').proj) =ᶠ[nhds x]
        (fun y' : ManifoldTotalSpace F (AssociatedBundle G P F) ↦
          ((ManifoldTotalSpace.homeomorph F (AssociatedBundle G P F)).symm y').proj) ∘
        (fun x' : ManifoldTotalSpace G P ↦ ⟪x', v⟫ₐ) :=
      .of_forall fun x' ↦ by simp
    have hq : ContMDiff (IB.prod IG) (IB.prod IF) ∞
        (fun x' : ManifoldTotalSpace G P ↦ ⟪x', v⟫ₐ) :=
      (contMDiff_totalSpaceMk_mk ∞ G F IB IG IF P).comp (contMDiff_id.prodMk contMDiff_const)
    rw [hfun.mfderiv_eq, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      mfderiv_comp_apply x
        ((ManifoldTotalSpace.contMDiff_proj ∞ F (AssociatedBundle G P F) IB IF).mdifferentiableAt
          (by simp)) (hq.mdifferentiableAt (by simp))]
    simp only [Function.comp_apply]
  set L := mfderiv (IB.prod IG) (IB.prod IF) (fun x' : ManifoldTotalSpace G P ↦ ⟪x', v⟫ₐ) x
  set T := mfderiv (IB.prod IF) IB (fun y' : ManifoldTotalSpace F (AssociatedBundle G P F) ↦
    ((ManifoldTotalSpace.homeomorph F (AssociatedBundle G P F)).symm y').proj) ⟪x, v⟫ₐ
  set S := mfderiv (IB.prod IG) IB (fun x' : ManifoldTotalSpace G P ↦
    ((ManifoldTotalSpace.homeomorph G P).symm x').proj) x
  set C := tangentSpaceCast IB
    ((ManifoldTotalSpace.homeomorph F (AssociatedBundle G P F)).symm ⟪x, v⟫ₐ).proj
    ((ManifoldTotalSpace.homeomorph G P).symm x).proj
  have hc := hA.isCompl_horizontal x
  constructor
  · rw [Submodule.disjoint_def]
    intro u hu hk
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.1 hu
    have hwk : w ∈ S.ker := by
      simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hk ⊢
      rw [hTL, hk, map_zero]
    rw [ContinuousLinearMap.coe_coe, Submodule.disjoint_def.1 hc.disjoint w hw hwk, map_zero]
  · rw [Submodule.codisjoint_iff_exists_add_eq]
    intro u
    -- Lift the image of `u` in the base to `P`, and take the horizontal part of the lift.
    obtain ⟨w', hw'⟩ := TauCeti.isRegularPoint_iff.1
      (ManifoldTotalSpace.isRegularPoint_proj IB IG (E := P) x) (C (T u))
    obtain ⟨w, k, hw, hk, rfl⟩ := Submodule.codisjoint_iff_exists_add_eq.1 hc.codisjoint w'
    simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hk
    refine ⟨L w, u - L w, Submodule.mem_map_of_mem hw, ?_, add_sub_cancel _ _⟩
    rw [map_add, hk, add_zero, hTL] at hw'
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, map_sub, C.injective hw', sub_self]

end IsConnectionForm

end SymplecticGeometry

end
