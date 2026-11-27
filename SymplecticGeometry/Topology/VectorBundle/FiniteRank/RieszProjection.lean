/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Basic
public import SymplecticGeometry.Analysis.Normed.Algebra.UnitDiscRieszProjection
import SymplecticGeometry.Topology.VectorBundle.Core.Basic

/-!
# The Riesz projection of an endomorphism of a finite-rank core

Let `T : E ⟶ E` be an endomorphism of a complex finite-rank core `E` over `X` such that the
spectrum of no fibre map `T.fiberMap x` meets the unit circle. Then the Riesz projections
`unitDiscRieszProjection (T.fiberMap x)` of the fibre maps, the circle integrals
`(2πi)⁻¹ ∮_{|z| = 1} (z - T.fiberMap x)⁻¹ dz`, are the fibre maps of an endomorphism
`TauCeti.FiniteRankBundleCore.unitDiscRieszProjection T h` of `E`.

To see that this family is a morphism, we build it with Tau Ceti's
`VectorBundleCore.CoordinateHom.ofContinuous`, which asks for continuity in every pair of charts
`i`, `j`. In the chart `i` on both sides, the chart expression of a fibre map is its conjugate
by a continuous linear automorphism of the model fibre
(`VectorBundleCore.exists_conjContinuousAlgEquiv_eq_inChartCoordinates`), and the Riesz
projection commutes with such a conjugation
(`SymplecticGeometry.unitDiscRieszProjection_conjContinuousAlgEquiv`); so there it is the Riesz
projection of the chart expression of `T`, which has the spectrum of `T` (`AlgEquiv.spectrum_eq`)
and is continuous, hence so is its projection (`ContinuousOn.unitDiscRieszProjection`). The chart
expression in the charts `i`, `j` is the one in `i`, `i` followed by that of the identity, which
is continuous too.

## Main results

* `TauCeti.FiniteRankBundleCore.unitDiscRieszProjection`: the endomorphism, and
  `TauCeti.FiniteRankBundleCore.fiberMap_unitDiscRieszProjection`: its fibre maps;
* `TauCeti.FiniteRankBundleCore.unitDiscRieszProjection_comp_self`: it is idempotent;
* `TauCeti.FiniteRankBundleCore.unitDiscRieszProjection_comp_comm`: it commutes with `T`;
* `TauCeti.FiniteRankBundleCore.disjoint_ker_sub_smul_ker_unitDiscRieszProjection` and
  `TauCeti.FiniteRankBundleCore.disjoint_ker_id_sub_smul_range_unitDiscRieszProjection`: for
  `‖w‖ ≤ 1`, the map `T - w` is injective on the kernel of the projection, and `1 - w T` on its
  range, on each fibre.

## References

* [A. Hatcher, *Vector Bundles and K-Theory*][Hatcher2017], §2.1 (the splitting of a linear
  clutching function).
-/

public section

noncomputable section

open Bundle CategoryTheory VectorBundleCore

namespace TauCeti

namespace FiniteRankBundleCore

variable {X : Type*} [TopologicalSpace X] {E : FiniteRankBundleCore ℂ X}

/-- A step of the definition of `unitDiscRieszProjection`: the Riesz projections of the fibre
maps of `T` form a continuous section of the Hom bundle. -/
private theorem continuous_unitDiscRieszProjection_fiberMap (T : E ⟶ E)
    (h : ∀ x, ∀ z ∈ spectrum ℂ (T.fiberMap x), ‖z‖ ≠ 1) :
    Continuous fun x ↦ TotalSpace.mk' ((Fin E.rank → ℂ) →L[ℂ] (Fin E.rank → ℂ))
      (E := fun y ↦ E.core.Fiber y →L[ℂ] E.core.Fiber y) x
      (SymplecticGeometry.unitDiscRieszProjection
        (A := (Fin E.rank → ℂ) →L[ℂ] (Fin E.rank → ℂ)) (T.fiberMap x)) := by
  -- In the chart `i` on both sides, the chart expression of a fibre map is its conjugate by an
  -- algebra isomorphism, under which the Riesz projection is natural and the spectrum invariant.
  have hconj {i x : X} (hx : x ∈ E.core.baseSet i) (M : (Fin E.rank → ℂ) →L[ℂ] _) :
      E.core.inChartCoordinates E.core i i x (SymplecticGeometry.unitDiscRieszProjection M) =
        SymplecticGeometry.unitDiscRieszProjection (E.core.inChartCoordinates E.core i i x M) := by
    obtain ⟨e, he⟩ := E.core.exists_conjContinuousAlgEquiv_eq_inChartCoordinates hx
    rw [← he, ← he, SymplecticGeometry.unitDiscRieszProjection_conjContinuousAlgEquiv]
  refine E.core.continuous_hom_bundle_iff_forall_continuousOn.2 fun i j ↦ ?_
  have hid := E.core.continuous_hom_bundle_iff_forall_continuousOn.1
    (CoordinateHom.id E.core).continuous_fiberMap i j
  have hT := E.core.continuous_hom_bundle_iff_forall_continuousOn.1 T.continuous_fiberMap i i
  simp only [CoordinateHom.fiberMap_id, Set.inter_self] at hid hT
  -- The Riesz projection of the chart expression of `T` in the chart `i` is continuous there,
  -- since that expression is conjugate to `T`, with the same spectrum.
  have hR : ContinuousOn (fun x ↦ SymplecticGeometry.unitDiscRieszProjection
      (E.core.inChartCoordinates E.core i i x (T.fiberMap x))) (E.core.baseSet i) := by
    refine hT.unitDiscRieszProjection fun x hx ↦ ?_
    obtain ⟨e, he⟩ := E.core.exists_conjContinuousAlgEquiv_eq_inChartCoordinates hx
    simpa only [← he, AlgEquiv.spectrum_eq] using h x
  -- In the charts `i`, `j`, it is the chart expression in `i`, `i` followed by that of the
  -- identity.
  refine (hid.clm_comp (hR.mono Set.inter_subset_left)).congr fun x hx ↦ ?_
  dsimp only
  rw [← hconj hx.1, ← E.core.inChartCoordinates_comp E.core E.core i j hx.1,
    ContinuousLinearMap.id_comp]

/-- The **Riesz projection** of an endomorphism `T` of a complex finite-rank core such that the
spectrum of no fibre map meets the unit circle: the endomorphism whose fibre map over `x` is the
Riesz projection `unitDiscRieszProjection (T.fiberMap x)` for the unit circle. -/
def unitDiscRieszProjection (T : E ⟶ E) (h : ∀ x, ∀ z ∈ spectrum ℂ (T.fiberMap x), ‖z‖ ≠ 1) :
    E ⟶ E :=
  CoordinateHom.ofContinuous _ (continuous_unitDiscRieszProjection_fiberMap T h)

/-- The fibre map over `x` of the Riesz projection of `T` is the Riesz projection of the fibre
map of `T` over `x`. -/
@[simp]
theorem fiberMap_unitDiscRieszProjection (T : E ⟶ E)
    (h : ∀ x, ∀ z ∈ spectrum ℂ (T.fiberMap x), ‖z‖ ≠ 1) (x : X) :
    (unitDiscRieszProjection T h).fiberMap x =
      SymplecticGeometry.unitDiscRieszProjection (T.fiberMap x) :=
  congrFun (CoordinateHom.fiberMap_ofContinuous _ _) x

variable (T : E ⟶ E) (h : ∀ x, ∀ z ∈ spectrum ℂ (T.fiberMap x), ‖z‖ ≠ 1)

/-- The Riesz projection of `T` is idempotent. -/
@[simp]
theorem unitDiscRieszProjection_comp_self :
    unitDiscRieszProjection T h ≫ unitDiscRieszProjection T h = unitDiscRieszProjection T h := by
  ext x : 1
  rw [fiberMap_comp, fiberMap_unitDiscRieszProjection, ← ContinuousLinearMap.mul_def]
  exact (SymplecticGeometry.isIdempotentElem_unitDiscRieszProjection _ (h x)).eq

/-- The Riesz projection of `T` commutes with `T`. -/
theorem unitDiscRieszProjection_comp_comm :
    unitDiscRieszProjection T h ≫ T = T ≫ unitDiscRieszProjection T h := by
  ext x : 1
  rw [fiberMap_comp, fiberMap_comp, fiberMap_unitDiscRieszProjection,
    ← ContinuousLinearMap.mul_def, ← ContinuousLinearMap.mul_def]
  exact (SymplecticGeometry.commute_unitDiscRieszProjection _).eq

/-- For `‖w‖ ≤ 1`, the map `T - w` is injective on the kernel of the Riesz projection of `T`, on
each fibre: the eigenvalues of `T` there lie outside the closed unit disc. -/
theorem disjoint_ker_sub_smul_ker_unitDiscRieszProjection (x : X) {w : ℂ} (hw : ‖w‖ ≤ 1) :
    Disjoint (LinearMap.ker
        ((T.fiberMap x - w • .id ℂ _ : _ →L[ℂ] _) : (Fin E.rank → ℂ) →ₗ[ℂ] (Fin E.rank → ℂ)))
      (LinearMap.ker
        ((unitDiscRieszProjection T h).fiberMap x : (Fin E.rank → ℂ) →ₗ[ℂ] (Fin E.rank → ℂ))) := by
  refine Submodule.disjoint_def.2 fun v hT hP ↦ ?_
  rw [LinearMap.mem_ker, fiberMap_unitDiscRieszProjection] at hP
  rw [LinearMap.mem_ker] at hT
  refine SymplecticGeometry.eq_zero_of_unitDiscRieszProjection_apply_eq_zero (h x) hP hw ?_
  simpa [sub_eq_zero] using hT

/-- For `‖w‖ ≤ 1`, the map `1 - w T` is injective on the range of the Riesz projection of `T`, on
each fibre: the eigenvalues of `T` there lie inside the open unit disc. -/
theorem disjoint_ker_id_sub_smul_range_unitDiscRieszProjection (x : X) {w : ℂ} (hw : ‖w‖ ≤ 1) :
    Disjoint (LinearMap.ker
        ((.id ℂ _ - w • T.fiberMap x : _ →L[ℂ] _) : (Fin E.rank → ℂ) →ₗ[ℂ] (Fin E.rank → ℂ)))
      (LinearMap.range
        ((unitDiscRieszProjection T h).fiberMap x : (Fin E.rank → ℂ) →ₗ[ℂ] (Fin E.rank → ℂ))) := by
  refine Submodule.disjoint_def.2 fun v hT hP ↦ ?_
  obtain ⟨u, rfl⟩ := hP
  rw [LinearMap.mem_ker] at hT
  refine SymplecticGeometry.eq_zero_of_unitDiscRieszProjection_apply_eq_self (h x) ?_ hw ?_
  · simp only [ContinuousLinearMap.coe_coe, fiberMap_unitDiscRieszProjection]
    rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.mul_def,
      (SymplecticGeometry.isIdempotentElem_unitDiscRieszProjection _ (h x)).eq]
  · rw [eq_comm]
    simpa [sub_eq_zero] using hT

end FiniteRankBundleCore

end TauCeti

end
