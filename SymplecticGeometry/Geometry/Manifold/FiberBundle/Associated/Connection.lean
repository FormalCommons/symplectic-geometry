/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.FiberBundle.Associated.PullbackPrincipal
public import SymplecticGeometry.Geometry.Manifold.FiberBundle.Principal.Connection.Basic
public import TauCeti.Geometry.Manifold.IsManifold.Basic
public import TauCeti.Geometry.Manifold.Submersion.EhresmannConnection.Hom
import SymplecticGeometry.Geometry.Manifold.IsManifold.Basic
import SymplecticGeometry.Geometry.Manifold.Distribution.Prod
import SymplecticGeometry.Geometry.Manifold.Distribution.Pushforward

/-!
# The horizontal spaces induced by a connection form on an associated bundle

Let `P` be a smooth principal `G`-bundle over `B` with a connection form `A`, let `G` act smoothly
on the left on a manifold `F`, and let `M = P ×_G F` be the associated bundle, with charted total
space `TauCeti.ManifoldTotalSpace F (AssociatedBundle G P F)` and quotient map
`q (x, v) = [x, v]`, which is `TauCeti.AssociatedBundle.chartedMk`.

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
* `SymplecticGeometry.IsConnectionForm.isEhresmannConnection_associatedHorizontal`: the induced
  horizontal spaces are a smooth Ehresmann connection (Tau Ceti's `TauCeti.IsEhresmannConnection`)
  on the projection of the associated bundle, for finite-dimensional base, group and fibre
  without boundary.
* `SymplecticGeometry.IsConnectionForm.isEhresmannConnectionHom_chartedMk`: the map
  `x' ↦ [x', v]`, over the identity of the base, is a morphism of Ehresmann connections
  (Tau Ceti's `TauCeti.IsEhresmannConnectionHom`) from `ker A` to the induced horizontal spaces.
* `SymplecticGeometry.IsConnectionForm.mfderiv_chartedMk_horizontalLift`: the horizontal lift of a
  tangent vector of the base at `[x, v]` is the image under the derivative of `x' ↦ [x', v]` of
  its horizontal lift at `x` for the connection on `P`.

## Implementation notes

The definition takes the representative `(x, v)` that
`TauCeti.AssociatedBundle.surjective_chartedMk` chooses for `y`. The image of `ker A_x` lies
in the tangent space at `[x, v]`, which is the tangent space at `y` only up to an equation, so the
definition transports it with Mathlib's `tangentSpaceCast`; `associatedHorizontal_eq` states it
without the cast. The derivative of `x' ↦ [x', v]` at `x` is the derivative of the quotient map at
`(x, v)` on the vectors `(w, 0)`, by the chain rule and `mfderiv_prod_left`. The definition uses
the former, since the tangent space of `P × F` is a product of tangent spaces only up to
unfolding `TangentSpace`. Complementarity needs neither the kernel nor the surjectivity of the
derivative of the quotient map: it only needs the derivative of the projection of `P` to be
surjective (`TauCeti.ManifoldTotalSpace.isSubmersion_projContMDiffMap`).

Smoothness comes from `P × F`: there the distribution `ker A_x × 0` is smooth of rank `dim B`
(`TauCeti.IsContMDiffDistribution.map_mfderiv_prod_left`, from
`IsConnectionForm.isEhresmannConnection_horizontal`), the quotient map is a surjective
submersion (`TauCeti.AssociatedBundle.isSubmersion_chartedMk`) whose derivative maps it onto
the induced horizontal spaces, injectively since its composite with the derivative of the
projection of `P ×_G F` is that of the projection of `P`. So the push-forward of
`TauCeti.IsContMDiffDistribution.map_mfderiv_of_isSubmersion` applies; it reads the
distribution through local sections of the quotient map. The statement takes the instance
`[ContMDiffFiberBundle ∞ F (AssociatedBundle G P F) IB IF]`, which Tau Ceti's
`TauCeti.AssociatedBundle.contMDiffFiberBundle` supplies, since `IsEhresmannConnection` needs a
manifold structure on the charted total space of `P ×_G F`.

The horizontal lift on `P ×_G F` is computed from that on `P` by Tau Ceti's
`TauCeti.IsEhresmannConnectionHom.mfderiv_horizontalLift`, applied to the morphism
`isEhresmannConnectionHom_chartedMk`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §6.3,
  Exercise 6.3.2 (the connection induced on an associated bundle).
-/

public section

noncomputable section

open Bundle Manifold MulOpposite TauCeti TauCeti.AssociatedBundle
open scoped Manifold ContDiff

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
  {A : SmoothForm (IB.prod IG) (ManifoldTotalSpace G P) EG 1}

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
    ((tangentSpaceCast (IB.prod IF) (chartedMk G F P (surjective_chartedMk y).choose)
        y).toContinuousLinearMap ∘L
      mfderiv (IB.prod IG) (IB.prod IF)
        (fun x' : ManifoldTotalSpace G P ↦
          chartedMk G F P (x', (surjective_chartedMk y).choose.2))
        (surjective_chartedMk y).choose.1).toLinearMap
    (horizontal A (surjective_chartedMk y).choose.1)

/-- One step of the independence of the representative: for two representatives `(x, v)` and
`(x', v')` of `y`, the image of `ker A_x` under the derivative of `x'' ↦ [x'', v]` is contained
in the image of `ker A_{x'}` under that of `x'' ↦ [x'', v']`. -/
private theorem map_le_map_of_chartedMk_eq (hA : IsConnectionForm A)
    {x x' : ManifoldTotalSpace G P} {v v' : F} {y : ManifoldTotalSpace F (AssociatedBundle G P F)}
    (h : chartedMk G F P (x, v) = y) (h' : chartedMk G F P (x', v') = y) :
    Submodule.map
        ((tangentSpaceCast (IB.prod IF) (chartedMk G F P (x, v)) y).toContinuousLinearMap ∘L
          mfderiv (IB.prod IG) (IB.prod IF)
            (fun x'' : ManifoldTotalSpace G P ↦ chartedMk G F P (x'', v)) x).toLinearMap
        (horizontal A x) ≤
      Submodule.map
        ((tangentSpaceCast (IB.prod IF) (chartedMk G F P (x', v')) y).toContinuousLinearMap ∘L
          mfderiv (IB.prod IG) (IB.prod IF)
            (fun x'' : ManifoldTotalSpace G P ↦ chartedMk G F P (x'', v')) x').toLinearMap
        (horizontal A x') := by
  obtain ⟨g, hg⟩ := (chartedMk_eq_chartedMk_iff (x := (x, v)) (y := (x', v'))).1
    (h.trans h'.symm)
  simp only [Prod.mk.injEq] at hg
  obtain ⟨rfl, rfl⟩ := hg
  rintro _ ⟨w, hw, rfl⟩
  refine ⟨_, hA.mfderiv_op_smul_mem_horizontal g hw, ?_⟩
  -- The map `x'' ↦ [x'', v]` is `x'' ↦ [x'' · g, g⁻¹ • v]`.
  have hfun : (fun x'' : ManifoldTotalSpace G P ↦ chartedMk G F P (x'', v)) =ᶠ[nhds x]
      (fun x'' : ManifoldTotalSpace G P ↦ chartedMk G F P (x'', g⁻¹ • v)) ∘ fun x'' ↦ op g • x'' :=
    .of_forall fun x'' ↦ (chartedMk_op_smul_inv_smul g (x'', v)).symm
  have hxv : chartedMk G F P (op g • x, g⁻¹ • v) = chartedMk G F P (x, v) :=
    chartedMk_op_smul_inv_smul g (x, v)
  simp only [hfun.mfderiv_eq, ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe]
  rw [mfderiv_comp_apply x
    ((contMDiff_chartedMk_left ∞ IB IF (g⁻¹ • v)).mdifferentiableAt (by simp))
    ((contMDiff_const_smul (I := IB.prod IG) (n := ∞) (op g)).mdifferentiableAt (by simp))]
  simp only [Function.comp_apply]
  rw [tangentSpaceCast_trans hxv h]

/-- **The induced horizontal space does not depend on the representative.** At `[x, v]`, the
horizontal space induced by a connection form `A` is the image of `ker A_x` under the derivative
at `x` of `x' ↦ [x', v]`, for every representative `(x, v)`. -/
theorem associatedHorizontal_eq (hA : IsConnectionForm A) (x : ManifoldTotalSpace G P) (v : F) :
    hA.associatedHorizontal (chartedMk G F P (x, v)) =
      Submodule.map (mfderiv (IB.prod IG) (IB.prod IF)
        (fun x' : ManifoldTotalSpace G P ↦ chartedMk G F P (x', v)) x).toLinearMap
        (horizontal A x) := by
  have h := (surjective_chartedMk (chartedMk G F P (x, v))).choose_spec
  have hcast : ((tangentSpaceCast (IB.prod IF) (chartedMk G F P (x, v))
      (chartedMk G F P (x, v))).toContinuousLinearMap ∘L
      mfderiv (IB.prod IG) (IB.prod IF)
        (fun x' : ManifoldTotalSpace G P ↦ chartedMk G F P (x', v)) x) =
      mfderiv (IB.prod IG) (IB.prod IF)
        (fun x' : ManifoldTotalSpace G P ↦ chartedMk G F P (x', v)) x :=
    ContinuousLinearMap.ext fun w ↦ by simp
  rw [← hcast]
  exact le_antisymm (hA.map_le_map_of_chartedMk_eq h rfl)
    (hA.map_le_map_of_chartedMk_eq rfl h)

/-- A tangent vector to `P ×_G F` at `[x, v]` is horizontal for the connection induced by `A`
exactly when it is the image of a horizontal vector of `P` at `x` under the derivative of
`x' ↦ [x', v]`. -/
theorem mem_associatedHorizontal_iff (hA : IsConnectionForm A) {x : ManifoldTotalSpace G P}
    {v : F} {u : TangentSpace (IB.prod IF) (chartedMk G F P (x, v))} :
    u ∈ hA.associatedHorizontal (chartedMk G F P (x, v)) ↔
      ∃ w ∈ horizontal A x, mfderiv (IB.prod IG) (IB.prod IF)
        (fun x' : ManifoldTotalSpace G P ↦ chartedMk G F P (x', v)) x w = u := by
  rw [associatedHorizontal_eq, Submodule.mem_map, ContinuousLinearMap.coe_coe]

/-- **The induced horizontal space is a complement of the vertical space.** At every point of
the associated bundle `P ×_G F`, the horizontal space induced by a connection form is a complement
of the kernel of the derivative of the projection to the base. -/
theorem isCompl_associatedHorizontal (hA : IsConnectionForm A)
    (y : ManifoldTotalSpace F (AssociatedBundle G P F)) :
    IsCompl (hA.associatedHorizontal y)
      (mfderiv (IB.prod IF) IB
        (ManifoldTotalSpace.projContMDiffMap ∞ F (AssociatedBundle G P F) IB IF) y).ker := by
  obtain ⟨⟨x, v⟩, rfl⟩ := surjective_chartedMk y
  rw [associatedHorizontal_eq]
  set L := mfderiv (IB.prod IG) (IB.prod IF)
    (fun x' : ManifoldTotalSpace G P ↦ chartedMk G F P (x', v)) x
  set T := mfderiv (IB.prod IF) IB
    (ManifoldTotalSpace.projContMDiffMap ∞ F (AssociatedBundle G P F) IB IF)
    (chartedMk G F P (x, v))
  set S := mfderiv (IB.prod IG) IB (ManifoldTotalSpace.projContMDiffMap ∞ G P IB IG) x
  set C := tangentSpaceCast IB
    (ManifoldTotalSpace.projContMDiffMap ∞ F (AssociatedBundle G P F) IB IF
      (chartedMk G F P (x, v)))
    (ManifoldTotalSpace.projContMDiffMap ∞ G P IB IG x)
  have hc := hA.isCompl_horizontal (n := ∞) x
  have hTL := mfderiv_proj_chartedMk_apply (IB := IB) (IG := IG) (IF := IF) (n := ∞)
    (by simp) x v
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
    obtain ⟨w', hw'⟩ := (ManifoldTotalSpace.isSubmersion_projContMDiffMap ∞ G P IB IG
      ).surjective_mfderiv (by simp) x (C (T u))
    obtain ⟨w, k, hw, hk, rfl⟩ := Submodule.codisjoint_iff_exists_add_eq.1 hc.codisjoint w'
    simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hk
    refine ⟨L w, u - L w, Submodule.mem_map_of_mem hw, ?_, add_sub_cancel _ _⟩
    rw [map_add, hk, add_zero, hTL] at hw'
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, map_sub, C.injective hw', sub_self]

omit [IsManifold IB ∞ B] [LieGroup IG ∞ G] [ContMDiffFiberBundle ∞ G P IB IG] in
/-- The derivative of `x' ↦ [x', v]` at `x` is that of the quotient map at `(x, v)` composed with
the derivative of `x' ↦ (x', v)`, by the chain rule. -/
private theorem mfderiv_chartedMk_comp_mfderiv_prod_left [IsManifold IF ∞ F]
    (x : ManifoldTotalSpace G P) (v : F) :
    (mfderiv ((IB.prod IG).prod IF) (IB.prod IF) (chartedMk G F P) (x, v)).comp
        (mfderiv (IB.prod IG) ((IB.prod IG).prod IF) (fun x' ↦ (x', v)) x) =
      mfderiv (IB.prod IG) (IB.prod IF)
        (fun x' : ManifoldTotalSpace G P ↦ chartedMk G F P (x', v)) x :=
  (mfderiv_comp x ((contMDiff_chartedMk ∞ IB IG IF).mdifferentiableAt (by simp))
    (mdifferentiableAt_id.prodMk mdifferentiableAt_const)).symm

/-- **The connection induced on an associated bundle is an Ehresmann connection.** For a
connection form `A` on a principal `G`-bundle `P` and a smooth action of `G` on `F`, with base,
group and fibre finite-dimensional and without boundary, the induced horizontal spaces are a
smooth Ehresmann connection on the projection of `P ×_G F` to the base: complements of the
vertical spaces that form a smooth distribution of rank `dim B`. -/
theorem isEhresmannConnection_associatedHorizontal [FiniteDimensional ℝ EB] [IB.Boundaryless]
    [FiniteDimensional ℝ EG] [IG.Boundaryless] [FiniteDimensional ℝ EF] [IF.Boundaryless]
    [IsManifold IF ∞ F] [ContMDiffFiberBundle ∞ F (AssociatedBundle G P F) IB IF]
    (hA : IsConnectionForm A) :
    IsEhresmannConnection (IB.prod IF) IB ∞
      (ManifoldTotalSpace.projContMDiffMap ∞ F (AssociatedBundle G P F) IB IF)
      hA.associatedHorizontal := by
  refine ⟨ManifoldTotalSpace.mdifferentiable_projContMDiffMap, fun y ↦ ?_, fun y ↦ ?_, ?_⟩
  · exact hA.isCompl_associatedHorizontal y
  · exact (ManifoldTotalSpace.isSubmersion_projContMDiffMap ∞ F (AssociatedBundle G P F) IB IF
      ).surjective_mfderiv (by simp) y
  refine (hA.isEhresmannConnection_horizontal.isContMDiffDistribution.map_mfderiv_prod_left
    (I' := IF) (M' := F)).map_mfderiv_of_isSubmersion
    (isSubmersion_chartedMk (n := ∞) ENat.LEInfty.out) surjective_chartedMk (by simp)
    (fun ⟨x, v⟩ ↦ ?_) (fun ⟨x, v⟩ ↦ ?_)
  · rw [← Submodule.map_comp, ← ContinuousLinearMap.toLinearMap_comp,
      mfderiv_chartedMk_comp_mfderiv_prod_left, associatedHorizontal_eq]
  · -- `dq` is injective on `ker A_x × 0`, since its composite with the derivative of the
    -- projection of `P ×_G F` is the derivative of the projection of `P`, injective on `ker A_x`.
    rintro _ ⟨w, hw, rfl⟩ _ ⟨w', hw', rfl⟩ h
    simp only [ContinuousLinearMap.coe_coe, ← ContinuousLinearMap.comp_apply,
      mfderiv_chartedMk_comp_mfderiv_prod_left] at h
    have hc := hA.isCompl_horizontal (n := ∞) x
    have hTL := mfderiv_proj_chartedMk_apply (IB := IB) (IG := IG) (IF := IF) (n := ∞)
      (by simp) x v
    rw [LinearMap.injOn_of_disjoint_ker le_rfl hc.disjoint hw hw'
      (by simp only [ContinuousLinearMap.coe_coe, hTL, h])]

/-- For a connection form `A` and `v : F`, the map `x' ↦ [x', v]` from `P` to `P ×_G F`, over the
identity of the base, is a morphism of Ehresmann connections from `ker A` to the induced
horizontal spaces: it is differentiable, covers the identity of `B`, and its derivative carries
`ker A_x` into the horizontal space at `[x, v]`. -/
theorem isEhresmannConnectionHom_chartedMk [IsManifold IF ∞ F]
    [ContMDiffFiberBundle ∞ F (AssociatedBundle G P F) IB IF] (hA : IsConnectionForm A) (v : F) :
    IsEhresmannConnectionHom (IB.prod IG) IB (IB.prod IF) IB
      (ManifoldTotalSpace.projContMDiffMap ∞ G P IB IG) (horizontal A)
      (ManifoldTotalSpace.projContMDiffMap ∞ F (AssociatedBundle G P F) IB IF)
      hA.associatedHorizontal (fun x' : ManifoldTotalSpace G P ↦ chartedMk G F P (x', v)) id :=
  ⟨(contMDiff_chartedMk_left ∞ IB IF v).mdifferentiable (by simp), mdifferentiable_id,
    funext fun x' ↦ by simp, fun x' _ hu ↦ hA.mem_associatedHorizontal_iff.2 ⟨_, hu, rfl⟩⟩

/-- **The horizontal lift on the associated bundle.** For the connection induced by a connection
form `A` on `P ×_G F`, the horizontal lift of a tangent vector `w` of the base at `[x, v]` is the
image under the derivative of `x' ↦ [x', v]` at `x` of the horizontal lift of `w` at `x` for the
connection `ker A` on `P`. The base points of `x` and `[x, v]` are equal, but not syntactically,
so `w` is transported between their tangent spaces by `tangentSpaceCast`. -/
theorem mfderiv_chartedMk_horizontalLift [FiniteDimensional ℝ EB] [IB.Boundaryless]
    [FiniteDimensional ℝ EG] [IG.Boundaryless] [FiniteDimensional ℝ EF] [IF.Boundaryless]
    [IsManifold IF ∞ F] [ContMDiffFiberBundle ∞ F (AssociatedBundle G P F) IB IF]
    (hA : IsConnectionForm A) (x : ManifoldTotalSpace G P) (v : F)
    (w : TangentSpace IB (ManifoldTotalSpace.projContMDiffMap ∞ G P IB IG x)) :
    mfderiv (IB.prod IG) (IB.prod IF)
        (fun x' : ManifoldTotalSpace G P ↦ chartedMk G F P (x', v)) x
        (hA.isEhresmannConnection_horizontal.horizontalLift x w) =
      hA.isEhresmannConnection_associatedHorizontal.horizontalLift (chartedMk G F P (x, v))
        (tangentSpaceCast IB (ManifoldTotalSpace.projContMDiffMap ∞ G P IB IG x)
          (ManifoldTotalSpace.projContMDiffMap ∞ F (AssociatedBundle G P F) IB IF
            (chartedMk G F P (x, v))) w) := by
  rw [(hA.isEhresmannConnectionHom_chartedMk v).mfderiv_horizontalLift
    hA.isEhresmannConnection_horizontal hA.isEhresmannConnection_associatedHorizontal x w,
    mfderiv_id, ContinuousLinearMap.id_apply, tangentSpaceCast_apply]

end IsConnectionForm

end SymplecticGeometry

end
