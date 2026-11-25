/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Topology.VectorBundle.FiniteRank.Biproduct
public import TauCeti.Topology.VectorBundle.FiniteRank.ExteriorPower
public import TauCeti.Topology.VectorBundle.FiniteRank.Tensor
public import TauCeti.Topology.VectorBundle.TensorProduct.Basic

/-!
# Tensor products of finite-rank cores

Tau Ceti's `TauCeti.FiniteRankBundleCore.tensor A D` is the tensor product of two finite-rank
cores, with coordinates `Fin (A.rank * D.rank) → 𝕜` and with the Kronecker products of the
transitions as transitions. This file compares it with Tau Ceti's tensor product of vector bundles
`fun x ↦ A.core.Fiber x ⊗[𝕜] D.core.Fiber x`
(`TauCeti.Topology.VectorBundle.TensorProduct.Basic`), and computes the determinant line of a
Whitney sum.

## Main definitions and results

* `TauCeti.FiniteRankBundleCore.toLinearMap_linearEquivAt_trivializationAt`: in the chart at
  `x₀`, the trivialization acts on the fibre over `x` by the transition `coordChange x x₀ x`;
* `TauCeti.FiniteRankBundleCore.tensorFiberEquiv`: the fibre of `tensor A D` over `x` is
  `A.core.Fiber x ⊗[𝕜] D.core.Fiber x`, by Tau Ceti's coordinates `TauCeti.piTensorEquiv`;
* `TauCeti.FiniteRankBundleCore.continuous_tensorFiberEquiv`: this identification is continuous
  from the total space of `tensor A D` to that of the tensor product bundle;
* `TauCeti.FiniteRankBundleCore.detWhitneySumIso`: the determinant line of a Whitney sum is the
  tensor product of the determinant lines, `Λ^top (A ⊕ D) ≅ Λ^top A ⊗ Λ^top D`, by a constant
  coordinate change. It uses `TauCeti.FiniteRankBundleCore.det_coordChange_whitneySum`, from
  `SymplecticGeometry.Topology.VectorBundle.FiniteRank.Biproduct`.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §3 (tensor products and exterior powers of vector bundles).
* M. F. Atiyah, *K-Theory*, Benjamin (1967), §1.2.
-/

public section

open Bundle CategoryTheory Module
open scoped TensorProduct

namespace TauCeti

namespace FiniteRankBundleCore

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {B : Type*} [TopologicalSpace B]

section Trivialization

/-- In the chart of a finite-rank core at `x₀`, the linear equivalence that the trivialization
gives on the fibre over a point `x` of its domain is the transition `A.core.coordChange x x₀ x`. -/
theorem toLinearMap_linearEquivAt_trivializationAt (A : FiniteRankBundleCore 𝕜 B) {x₀ x : B}
    (hx : x ∈ (trivializationAt (Fin A.rank → 𝕜) A.core.Fiber x₀).baseSet) :
    (Trivialization.linearEquivAt 𝕜 (trivializationAt (Fin A.rank → 𝕜) A.core.Fiber x₀) x
      hx).toLinearMap = (A.core.coordChange x x₀ x).toLinearMap := by
  have h := A.core.trivializationAt_continuousLinearMapAt (R := 𝕜) hx
  rw [A.indexAt_eq, A.indexAt_eq] at h
  rw [← h]
  ext v
  simp [Trivialization.continuousLinearMapAt_apply, Trivialization.linearMapAt_def_of_mem _ hx,
    Trivialization.linearEquivAt_apply]

end Trivialization

section TensorFiber

variable (A D : FiniteRankBundleCore 𝕜 B)
  [∀ x, TopologicalSpace (A.core.Fiber x ⊗[𝕜] D.core.Fiber x)]
  [∀ x, IsModuleTopology 𝕜 (A.core.Fiber x ⊗[𝕜] D.core.Fiber x)]

/-- The fibre of the tensor product core `tensor A D` over `x` is the tensor product
`A.core.Fiber x ⊗[𝕜] D.core.Fiber x` of the fibres: a coordinate vector goes to the tensor whose
coefficient on the tensor of the `i`th and `j`th standard basis vectors is its coordinate at
`finProdFinEquiv (i, j)` (the inverse of `TauCeti.piTensorEquiv`). -/
noncomputable def tensorFiberEquiv (x : B) :
    (tensor A D).core.Fiber x ≃L[𝕜] A.core.Fiber x ⊗[𝕜] D.core.Fiber x :=
  letI : IsModuleTopology 𝕜 ((tensor A D).core.Fiber x) :=
    inferInstanceAs (IsModuleTopology 𝕜 (Fin (A.rank * D.rank) → 𝕜))
  LinearEquiv.toContinuousLinearEquivOfIsModuleTopology (M := (tensor A D).core.Fiber x)
    (N := A.core.Fiber x ⊗[𝕜] D.core.Fiber x) (piTensorEquiv 𝕜 A.rank D.rank).symm

@[simp] theorem tensorFiberEquiv_apply (x : B) (v : (tensor A D).core.Fiber x) :
    tensorFiberEquiv A D x v = (piTensorEquiv 𝕜 A.rank D.rank).symm v := by
  let _ : IsModuleTopology 𝕜 ((tensor A D).core.Fiber x) :=
    inferInstanceAs (IsModuleTopology 𝕜 (Fin (A.rank * D.rank) → 𝕜))
  rw [tensorFiberEquiv]
  exact congrFun (LinearEquiv.coe_toContinuousLinearEquivOfIsModuleTopology _) v

@[simp] theorem tensorFiberEquiv_symm_apply (x : B) (t : A.core.Fiber x ⊗[𝕜] D.core.Fiber x) :
    (tensorFiberEquiv A D x).symm t = piTensorEquiv 𝕜 A.rank D.rank t := by
  -- The fibres of `A` and `D` are their coordinate spaces by definition, on which
  -- `piTensorEquiv` is stated; `exact` sees this, `rw` does not.
  exact (tensorFiberEquiv A D x).symm_apply_eq.2 <|
    ((tensorFiberEquiv_apply A D x _).trans (LinearEquiv.symm_apply_apply _ t)).symm

variable [CompleteSpace 𝕜]

/-- The identification `tensorFiberEquiv` of the fibres of `tensor A D` with the tensor products
of the fibres is continuous from the total space of `tensor A D` to that of Tau Ceti's tensor
product bundle `fun x ↦ A.core.Fiber x ⊗[𝕜] D.core.Fiber x`. -/
theorem continuous_tensorFiberEquiv :
    Continuous fun p : (tensor A D).core.TotalSpace ↦
      TotalSpace.mk' (ProjectiveTensor 𝕜 (Fin A.rank → 𝕜) (Fin D.rank → 𝕜))
        (E := fun x ↦ A.core.Fiber x ⊗[𝕜] D.core.Fiber x) p.proj
        (tensorFiberEquiv A D p.proj p.snd) := by
  refine continuous_iff_continuousAt.2 fun p₀ ↦ ?_
  rw [continuousAt_tensorProduct_bundle]
  refine ⟨(tensor A D).core.continuous_proj.continuousAt, ?_⟩
  set e := (tensor A D).core.localTriv p₀.proj
  have hp₀ : p₀ ∈ e.source := ((tensor A D).core.mem_localTriv_source p₀.proj p₀).2
    ((tensor A D).mem_baseSet_self p₀.proj)
  -- Near `p₀`, the coordinates of the image are a fixed linear map of the chart coordinates.
  let L : (Fin (A.rank * D.rank) → 𝕜) →ₗ[𝕜]
      ProjectiveTensor 𝕜 (Fin A.rank → 𝕜) (Fin D.rank → 𝕜) :=
    (ProjectiveTensor.linearEquiv 𝕜 _ _).symm.toLinearMap ∘ₗ
      (piTensorEquiv 𝕜 A.rank D.rank).symm.toLinearMap
  refine ((LinearMap.continuous_of_finiteDimensional L).continuousAt.comp
    (e.continuousOn.continuousAt (e.open_source.mem_nhds hp₀)).snd).congr_of_eventuallyEq ?_
  filter_upwards [e.open_source.mem_nhds hp₀] with p hp
  have hA : p.proj ∈ (trivializationAt (Fin A.rank → 𝕜) A.core.Fiber p₀.proj).baseSet := by
    rw [A.trivializationAt_core]; exact hp.1
  have hD : p.proj ∈ (trivializationAt (Fin D.rank → 𝕜) D.core.Fiber p₀.proj).baseSet := by
    rw [D.trivializationAt_core]; exact hp.2
  rw [TensorProduct.inCoordinates_eq hA hD]
  have hk (w : Fin (A.rank * D.rank) → 𝕜) : (piTensorEquiv 𝕜 A.rank D.rank).symm
      ((A.core.coordChange p.proj p₀.proj p.proj).kronecker
        (D.core.coordChange p.proj p₀.proj p.proj) w) =
      TensorProduct.map (A.core.coordChange p.proj p₀.proj p.proj).toLinearMap
        (D.core.coordChange p.proj p₀.proj p.proj).toLinearMap
        ((piTensorEquiv 𝕜 A.rank D.rank).symm w) := by
    rw [← ContinuousLinearMap.coe_coe, ContinuousLinearMap.toLinearMap_kronecker_eq]
    simp
  rw [A.toLinearMap_linearEquivAt_trivializationAt hA,
    D.toLinearMap_linearEquivAt_trivializationAt hD, tensorFiberEquiv_apply]
  simp only [L, e, VectorBundleCore.localTriv_apply, (tensor A D).indexAt_eq, coordChange_tensor]
  rw [← ProjectiveTensor.linearEquiv_symm_apply]
  -- `exact` evaluates the composite on the right, whose coordinate spaces
  -- `Fin (tensor A D).rank → 𝕜` and `Fin (A.rank * D.rank) → 𝕜` agree by definition.
  exact congrArg (ProjectiveTensor.linearEquiv 𝕜 _ _).symm (hk p.snd).symm

end TensorFiber

section DetWhitneySum

/-- The determinant line of a Whitney sum is the tensor product of the determinant lines,
`Λ^top (A ⊕ D) ≅ Λ^top A ⊗ Λ^top D`. Both are lines with the charts of `A ⊕ D`, whose
transitions are multiplication by the same scalars (`det_coordChange_whitneySum`), so the
identification of their coordinates `Fin 1 → 𝕜` is an isomorphism. -/
noncomputable def detWhitneySumIso (A D : FiniteRankBundleCore 𝕜 B) :
    (whitneySum A D).det ≅ tensor A.det D.det :=
  constIso
    -- Both chart domains are `A.core.baseSet i ∩ D.core.baseSet i`, by the definitions of the
    -- exterior powers, of the Whitney sum and of the tensor product.
    (fun i ↦ by rw [det_def, det_def, det_def]; rfl)
    (ContinuousLinearEquiv.piCongrLeft 𝕜 (fun _ ↦ 𝕜) (finCongr (by simp))) fun i j x _ _ ↦ by
      have key {m n : ℕ} (e : (Fin m → 𝕜) ≃L[𝕜] (Fin n → 𝕜)) (c : 𝕜) :
          e.toContinuousLinearMap.comp (c • ContinuousLinearMap.id 𝕜 _) =
            (c • ContinuousLinearMap.id 𝕜 _).comp e.toContinuousLinearMap := by
        ext; simp
      rw [coordChange_det, coordChange_tensor, coordChange_det, coordChange_det,
        ContinuousLinearMap.smul_kronecker, ContinuousLinearMap.kronecker_smul,
        ContinuousLinearMap.id_kronecker_id, det_coordChange_whitneySum, smul_smul]
      exact key _ _

@[simp] theorem fiberMap_detWhitneySumIso_hom (A D : FiniteRankBundleCore 𝕜 B) (x : B) :
    (detWhitneySumIso A D).hom.fiberMap x =
      (ContinuousLinearEquiv.piCongrLeft 𝕜 (fun _ ↦ 𝕜) (finCongr (by simp))).toContinuousLinearMap
        := by
  rw [detWhitneySumIso]; exact fiberMap_constIso_hom _ _ _ x

@[simp] theorem fiberMap_detWhitneySumIso_inv (A D : FiniteRankBundleCore 𝕜 B) (x : B) :
    (detWhitneySumIso A D).inv.fiberMap x =
      (ContinuousLinearEquiv.piCongrLeft 𝕜 (fun _ ↦ 𝕜)
        (finCongr (by simp))).symm.toContinuousLinearMap := by
  rw [detWhitneySumIso]; exact fiberMap_constIso_inv _ _ _ x

end DetWhitneySum

end FiniteRankBundleCore

end TauCeti

end
