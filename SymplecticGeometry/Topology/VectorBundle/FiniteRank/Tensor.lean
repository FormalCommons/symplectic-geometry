/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Topology.VectorBundle.FiniteRank.Basic
public import TauCeti.Topology.VectorBundle.FiniteRank.Monoidal
public import TauCeti.Topology.VectorBundle.TensorProduct.Basic

/-!
# Tensor products of finite-rank cores

Tau Ceti's `TauCeti.FiniteRankBundleCore.tensor A D` is the tensor product of two finite-rank
cores, with coordinates `Fin (A.rank * D.rank) → 𝕜` and with the Kronecker products of the
transitions as transitions. This file compares it with Tau Ceti's tensor product of vector bundles
`fun x ↦ A.core.Fiber x ⊗[𝕜] D.core.Fiber x`
(`TauCeti.Topology.VectorBundle.TensorProduct.Basic`).

## Main definitions and results

* `TauCeti.FiniteRankBundleCore.toLinearMap_linearEquivAt_trivializationAt`: in the chart at
  `x₀`, the trivialization acts on the fibre over `x` by the transition `coordChange x x₀ x`;
* `TauCeti.FiniteRankBundleCore.tensorFiberEquiv`: the fibre of `tensor A D` over `x` is
  `A.core.Fiber x ⊗[𝕜] D.core.Fiber x`, by Tau Ceti's coordinates `TauCeti.piTensorEquiv`;
* `TauCeti.FiniteRankBundleCore.continuous_tensorFiberEquiv`: this identification is continuous
  from the total space of `tensor A D` to that of the tensor product bundle;
* `TauCeti.FiniteRankBundleCore.tensorIsoPullback e₁ e₂`: the tensor product of isomorphisms
  between two pullbacks, read through Tau Ceti's `pullback_tensorObj` as an isomorphism between
  the pullbacks of the tensor products;
* `TauCeti.FiniteRankBundleCore.fiberMap_eqToHom_tensorHom_eqToHom`, with its forms
  `fiberMap_tensorIsoPullback_hom` and `fiberMap_tensorIsoPullback_inv` for isomorphisms: the
  tensor product of morphisms between two pullbacks, read through Tau Ceti's `pullback_tensorObj`
  as a morphism between the pullbacks of the tensor products, is the Kronecker product of their
  fibre maps in each fibre.

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

section Pullback

open MonoidalCategory

variable {X : Type*} [TopologicalSpace X] {A A' D D' : FiniteRankBundleCore 𝕜 B} (p : C(X, B))

/-- Read through `pullback_tensorObj`, the tensor product of morphisms `f` and `g` between
pullbacks along `p` acts on the fibres of the pullbacks of the tensor products by the Kronecker
product of their fibre maps. -/
theorem fiberMap_eqToHom_tensorHom_eqToHom (f : A.pullback p ⟶ A'.pullback p)
    (g : D.pullback p ⟶ D'.pullback p) (x : X) :
    (eqToHom (pullback_tensorObj A D p) ≫ (f ⊗ₘ g) ≫
      eqToHom (pullback_tensorObj A' D' p).symm).fiberMap x =
      (f.fiberMap x).kronecker (g.fiberMap x) := by
  ext v i
  simp only [fiberMap_comp, ContinuousLinearMap.comp_apply, fiberMap_eqToHom,
    Function.comp_apply]
  -- The casts are along `rank_pullback` and `rank_tensorObj`, which hold by `rfl`.
  exact congrFun (DFunLike.congr_fun (fiberMap_tensorHom_monoidal _ _ _) _) _

variable {p} in
/-- The tensor product of isomorphisms `e₁ : A|_p ≅ A'|_p` and `e₂ : D|_p ≅ D'|_p` between
pullbacks along `p`, read through `pullback_tensorObj` as an isomorphism between the pullbacks of
the tensor products, `(A ⊗ D)|_p ≅ (A' ⊗ D')|_p`. -/
def tensorIsoPullback (e₁ : A.pullback p ≅ A'.pullback p) (e₂ : D.pullback p ≅ D'.pullback p) :
    (A ⊗ D).pullback p ≅ (A' ⊗ D').pullback p :=
  eqToIso (pullback_tensorObj A D p) ≪≫ (e₁ ⊗ᵢ e₂) ≪≫ eqToIso (pullback_tensorObj A' D' p).symm

variable (e₁ : A.pullback p ≅ A'.pullback p) (e₂ : D.pullback p ≅ D'.pullback p)

theorem tensorIsoPullback_def :
    tensorIsoPullback e₁ e₂ = eqToIso (pullback_tensorObj A D p) ≪≫ (e₁ ⊗ᵢ e₂) ≪≫
      eqToIso (pullback_tensorObj A' D' p).symm :=
  (rfl)

theorem tensorIsoPullback_hom :
    (tensorIsoPullback e₁ e₂).hom = eqToHom (pullback_tensorObj A D p) ≫ (e₁.hom ⊗ₘ e₂.hom) ≫
      eqToHom (pullback_tensorObj A' D' p).symm := by
  rw [tensorIsoPullback_def, Iso.trans_hom, Iso.trans_hom, eqToIso.hom, eqToIso.hom,
    tensorIso_hom]

theorem tensorIsoPullback_inv :
    (tensorIsoPullback e₁ e₂).inv = eqToHom (pullback_tensorObj A' D' p) ≫ (e₁.inv ⊗ₘ e₂.inv) ≫
      eqToHom (pullback_tensorObj A D p).symm := by
  rw [tensorIsoPullback_def, Iso.trans_inv, Iso.trans_inv, eqToIso.inv, eqToIso.inv,
    tensorIso_inv, Category.assoc]

/-- The tensor product of isomorphisms `e₁` and `e₂` between pullbacks along `p`, read through
`pullback_tensorObj`, acts on the fibres of the pullbacks of the tensor products by the Kronecker
product of their fibre maps. -/
@[simp]
theorem fiberMap_tensorIsoPullback_hom (x : X) :
    (tensorIsoPullback e₁ e₂).hom.fiberMap x =
      (e₁.hom.fiberMap x).kronecker (e₂.hom.fiberMap x) := by
  rw [tensorIsoPullback_hom]
  exact fiberMap_eqToHom_tensorHom_eqToHom p _ _ x

/-- The inverse of the tensor product of isomorphisms `e₁` and `e₂` between pullbacks along `p`,
read through `pullback_tensorObj`, acts on the fibres of the pullbacks of the tensor products by
the Kronecker product of the fibre maps of `e₁⁻¹` and `e₂⁻¹`. -/
@[simp]
theorem fiberMap_tensorIsoPullback_inv (x : X) :
    (tensorIsoPullback e₁ e₂).inv.fiberMap x =
      (e₁.inv.fiberMap x).kronecker (e₂.inv.fiberMap x) := by
  rw [tensorIsoPullback_inv]
  exact fiberMap_eqToHom_tensorHom_eqToHom p _ _ x

end Pullback

end FiniteRankBundleCore

end TauCeti

end
