/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Basic

/-!
# The fibrewise equivalences of an isomorphism of finite-rank cores

Tau Ceti's `TauCeti.FiniteRankBundleCore.isoOfContinuousEquiv` builds an isomorphism of
finite-rank cores from a family of fibrewise continuous linear equivalences that is continuous on
total spaces. This file gives the converse construction.

* `TauCeti.FiniteRankBundleCore.isoFiberEquiv e x`: the continuous linear equivalence between the
  fibres over `x`, in coordinates, given by an isomorphism `e : A ≅ D` of finite-rank cores, with
  the fibre map of `e.hom` as the map and that of `e.inv` as its inverse;
* `TauCeti.FiniteRankBundleCore.continuous_isoFiberEquiv`: this family is continuous on total
  spaces, in the form that `isoOfContinuousEquiv` takes;
* `TauCeti.FiniteRankBundleCore.isoFiberEquiv_isoOfContinuousEquiv` and
  `TauCeti.FiniteRankBundleCore.isoOfContinuousEquiv_isoFiberEquiv`: the two constructions are
  inverse to each other.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §2 (isomorphisms of vector bundles).
-/

public section

open Bundle CategoryTheory

namespace TauCeti

namespace FiniteRankBundleCore

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {B : Type*} [TopologicalSpace B]
  {A D : FiniteRankBundleCore 𝕜 B}

/-- The continuous linear equivalence between the fibres over `x` of two finite-rank cores, in
their coordinates `Fin A.rank → 𝕜` and `Fin D.rank → 𝕜`, given by an isomorphism `e : A ≅ D`: the
fibre map of `e.hom`, with inverse the fibre map of `e.inv`. -/
def isoFiberEquiv (e : A ≅ D) (x : B) : (Fin A.rank → 𝕜) ≃L[𝕜] (Fin D.rank → 𝕜) :=
  ContinuousLinearEquiv.ofContinuousLinearMap (e.hom.fiberMap x) (e.inv.fiberMap x)
    (by rw [← fiberMap_comp, Iso.inv_hom_id, fiberMap_id])
    (by rw [← fiberMap_comp, Iso.hom_inv_id, fiberMap_id])

@[simp] theorem toContinuousLinearMap_isoFiberEquiv (e : A ≅ D) (x : B) :
    (isoFiberEquiv e x : (Fin A.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜)) = e.hom.fiberMap x := by
  rw [isoFiberEquiv, ContinuousLinearEquiv.toContinuousLinearMap_ofContinuousLinearMap]

@[simp] theorem isoFiberEquiv_apply (e : A ≅ D) (x : B) (v : Fin A.rank → 𝕜) :
    isoFiberEquiv e x v = e.hom.fiberMap x v := by
  rw [isoFiberEquiv, ContinuousLinearEquiv.coe_ofContinuousLinearMap]

@[simp] theorem isoFiberEquiv_symm (e : A ≅ D) (x : B) :
    (isoFiberEquiv e x).symm = isoFiberEquiv e.symm x := by
  apply ContinuousLinearEquiv.coe_injective
  rw [toContinuousLinearMap_isoFiberEquiv, Iso.symm_hom, isoFiberEquiv,
    ContinuousLinearEquiv.symm_ofContinuousLinearMap,
    ContinuousLinearEquiv.toContinuousLinearMap_ofContinuousLinearMap]

@[simp] theorem isoFiberEquiv_refl (A : FiniteRankBundleCore 𝕜 B) (x : B) :
    isoFiberEquiv (Iso.refl A) x = ContinuousLinearEquiv.refl 𝕜 (Fin A.rank → 𝕜) := by
  apply ContinuousLinearEquiv.coe_injective
  rw [toContinuousLinearMap_isoFiberEquiv, Iso.refl_hom, fiberMap_id,
    ContinuousLinearEquiv.coe_refl]

@[simp] theorem isoFiberEquiv_trans {C : FiniteRankBundleCore 𝕜 B} (e : A ≅ D) (f : D ≅ C)
    (x : B) : isoFiberEquiv (e ≪≫ f) x = (isoFiberEquiv e x).trans (isoFiberEquiv f x) := by
  apply ContinuousLinearEquiv.coe_injective
  rw [← ContinuousLinearEquiv.comp_coe, toContinuousLinearMap_isoFiberEquiv,
    toContinuousLinearMap_isoFiberEquiv, toContinuousLinearMap_isoFiberEquiv, Iso.trans_hom,
    fiberMap_comp]

/-- The fibrewise equivalences of an isomorphism of finite-rank cores are continuous on total
spaces. -/
theorem continuous_isoFiberEquiv (e : A ≅ D) :
    Continuous fun p : A.core.TotalSpace ↦
      TotalSpace.mk' (Fin D.rank → 𝕜) (E := D.core.Fiber) p.proj (isoFiberEquiv e p.proj p.snd) :=
  e.hom.continuous_totalSpaceMap.congr fun p ↦ by
    -- `exact` identifies the fibre `A.core.Fiber p.proj` with the coordinates `Fin A.rank → 𝕜`,
    -- which it is by definition.
    rw [VectorBundleCore.CoordinateHom.totalSpaceMap_def]
    exact congrArg (TotalSpace.mk' _ p.proj) (isoFiberEquiv_apply e p.proj p.snd).symm

/-- The fibrewise equivalences of the isomorphism built from a continuous family `ψ` of fibrewise
equivalences are those of `ψ`. -/
@[simp] theorem isoFiberEquiv_isoOfContinuousEquiv [CompleteSpace 𝕜]
    (ψ : B → (Fin A.rank → 𝕜) ≃L[𝕜] (Fin D.rank → 𝕜))
    (hψ : Continuous fun p : A.core.TotalSpace ↦
      TotalSpace.mk' (Fin D.rank → 𝕜) (E := D.core.Fiber) p.proj (ψ p.proj p.snd)) (x : B) :
    isoFiberEquiv (isoOfContinuousEquiv ψ hψ) x = ψ x := by
  apply ContinuousLinearEquiv.coe_injective
  rw [toContinuousLinearMap_isoFiberEquiv, fiberMap_isoOfContinuousEquiv_hom]

/-- The isomorphism built from the fibrewise equivalences of an isomorphism `e` of finite-rank
cores is `e`. -/
@[simp] theorem isoOfContinuousEquiv_isoFiberEquiv [CompleteSpace 𝕜] (e : A ≅ D) :
    isoOfContinuousEquiv (isoFiberEquiv e) (continuous_isoFiberEquiv e) = e := by
  ext x : 2
  simp

end FiniteRankBundleCore

end TauCeti

end
