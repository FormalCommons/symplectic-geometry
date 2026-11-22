/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Star
public import SymplecticGeometry.Topology.VectorBundle.FiniteRank.OfBundle
public import TauCeti.Topology.VectorBundle.Conjugate
public import TauCeti.Topology.VectorBundle.FiniteRank.Conjugate

/-!
# Conjugate finite-rank cores and conjugate bundles

Tau Ceti's conjugate core `(TauCeti.FiniteRankBundleCore.conjugate B).obj A` has the transitions
of `A` conjugated entrywise. This file relates it to `A` and to Tau Ceti's conjugate bundle
`TauCeti.ConjugateBundle`.

* `TauCeti.FiniteRankBundleCore.continuous_star_conjugate`: coordinatewise complex conjugation of
  fibre coordinates, a conjugate-linear map from the fibres of the conjugate core to those of `A`,
  is continuous on total spaces.
* `TauCeti.FiniteRankBundleCore.ofBundleOfFinrankEqConjugateIso`: the core of the conjugate
  bundle `ConjugateBundle E` (with model `Conjugate G`) is isomorphic to the conjugate of the core
  of `E`, by a constant coordinate isomorphism.

The proof of `continuous_star_conjugate` adapts that of Tau Ceti's
`TauCeti.FiniteRankBundleCore.continuous_pullbackLift`, and `ofBundleOfFinrankEqConjugateIso` is
built through `constIso` as Tau Ceti's `TauCeti.FiniteRankBundleCore.doubleConjugateIso` is.

## References

* M. F. Atiyah, *K-Theory*, §1.2, conjugate bundles.
-/

public section

open Bundle CategoryTheory Module WithConv TauCeti.Conjugate

namespace TauCeti

namespace FiniteRankBundleCore

variable {B : Type*} [TopologicalSpace B]

/-- Coordinatewise complex conjugation of fibre coordinates is continuous from the total space of
the conjugate core to that of `A`. -/
theorem continuous_star_conjugate (A : FiniteRankBundleCore ℂ B) :
    Continuous fun p : ((conjugate B).obj A).core.TotalSpace ↦
      TotalSpace.mk' (Fin A.rank → ℂ) (E := A.core.Fiber) p.proj
        ((starL ℂ : (Fin A.rank → ℂ) ≃L⋆[ℂ] (Fin A.rank → ℂ)) p.snd) := by
  refine continuous_iff_continuousAt.2 fun p ↦ ?_
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨((conjugate B).obj A).core.continuous_proj.continuousAt, ?_⟩
  have hp := ((conjugate B).obj A).core.mem_source_at p.proj p.snd
  have hc := ((((conjugate B).obj A).core.localTrivAt p.proj).continuousOn.continuousAt
    ((((conjugate B).obj A).core.localTrivAt p.proj).open_source.mem_nhds hp)).snd
  refine (continuous_star.continuousAt.comp hc).congr_of_eventuallyEq ?_
  filter_upwards with q
  simp only [VectorBundleCore.trivializationAt, VectorBundleCore.localTrivAt, indexAt_eq,
    VectorBundleCore.localTriv_apply, coordChange_conjugate_obj, Function.comp_apply]
  -- The intrinsic star of an operator evaluates as `v ↦ star (g (star v))`.
  exact (star_star _).symm

section OfBundle

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G]
  (E : B → Type*) [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)] [∀ x, TopologicalSpace (E x)]
  [TopologicalSpace (TotalSpace G E)] [FiberBundle G E] [VectorBundle ℂ G E]
  {n n' : ℕ} (h : finrank ℂ G = n) (h' : finrank ℂ (Conjugate G) = n')

/-- The complex-linear coordinate isomorphism between the cores of `ConjugateBundle E` and of `E`:
read a coordinate vector in `Conjugate G`, view it in `G`, and conjugate its coordinates. -/
noncomputable def conjugateModelEquiv : (Fin n' → ℂ) ≃L[ℂ] (Fin n → ℂ) :=
  ((ContinuousLinearEquiv.ofFinrankEq (h'.trans (finrank_fin_fun ℂ).symm)).symm.trans
    ((toConjL (V := G)).symm.trans
      (ContinuousLinearEquiv.ofFinrankEq (h.trans (finrank_fin_fun ℂ).symm)))).trans (starL ℂ)

@[simp] theorem conjugateModelEquiv_apply (v : Fin n' → ℂ) :
    conjugateModelEquiv h h' v =
      star (ContinuousLinearEquiv.ofFinrankEq (h.trans (finrank_fin_fun ℂ).symm)
        (ofConj ((ContinuousLinearEquiv.ofFinrankEq (h'.trans (finrank_fin_fun ℂ).symm)).symm
          v))) := by
  simp only [conjugateModelEquiv, ContinuousLinearEquiv.trans_apply, coe_toConjL_symm]
  rfl

/-- The core of the conjugate bundle `ConjugateBundle E` is isomorphic to the conjugate of the
core of `E`, by `conjugateModelEquiv` on every fibre. -/
noncomputable def ofBundleOfFinrankEqConjugateIso :
    ofBundleOfFinrankEq ℂ (Conjugate G) (ConjugateBundle E) h' ≅
      (conjugate B).obj (ofBundleOfFinrankEq ℂ G E h) :=
  constIso (fun i ↦ by
      rw [VectorBundleCore.baseSet_at, VectorBundleCore.baseSet_at,
        localTriv_baseSet_ofBundleOfFinrankEq, localTriv_baseSet_conjugate_obj,
        VectorBundleCore.baseSet_at, localTriv_baseSet_ofBundleOfFinrankEq]
      -- The trivializations of `ConjugateBundle E` are those of `E` (`trivializationAt_eq`).
      rfl)
    (conjugateModelEquiv h h') fun i j x hi hj ↦ by
      have hx : x ∈ (trivializationAt G E i).baseSet ∩ (trivializationAt G E j).baseSet := by
        rw [VectorBundleCore.baseSet_at, localTriv_baseSet_ofBundleOfFinrankEq] at hi hj
        -- The trivializations of `ConjugateBundle E` are those of `E` (`trivializationAt_eq`).
        exact ⟨hi, hj⟩
      have hc : (Trivialization.coordChangeL ℂ
          (trivializationAt (Conjugate G) (ConjugateBundle E) i)
          (trivializationAt (Conjugate G) (ConjugateBundle E) j) x :
            Conjugate G →L[ℂ] Conjugate G) =
          (Trivialization.coordChangeL ℂ (trivializationAt G E i) (trivializationAt G E j) x :
            G →L[ℂ] G).conjugate := by
        simp only [ConjugateBundle.trivializationAt_eq]
        exact Trivialization.coordChangeL_conjugate _ _ hx
      rw [coordChange_conjugate_obj, coordChange_ofBundleOfFinrankEq,
        coordChange_ofBundleOfFinrankEq, hc]
      -- State the identity on the standard coordinate spaces, to fix the fibre instances.
      let g : G →L[ℂ] G :=
        Trivialization.coordChangeL ℂ (trivializationAt G E i) (trivializationAt G E j) x
      let eG := ContinuousLinearEquiv.ofFinrankEq (h.trans (finrank_fin_fun ℂ).symm)
      let eC := ContinuousLinearEquiv.ofFinrankEq (h'.trans (finrank_fin_fun ℂ).symm)
      have key : (conjugateModelEquiv h h' : (Fin n' → ℂ) →L[ℂ] (Fin n → ℂ)).comp
          (eC.arrowCongr eC g.conjugate) =
          (star (toConv (eG.arrowCongr eG g))).ofConv.comp
            (conjugateModelEquiv h h' : (Fin n' → ℂ) →L[ℂ] (Fin n → ℂ)) := by
        refine ContinuousLinearMap.ext fun v ↦ ?_
        simp [conjugateModelEquiv_apply, g, eG, eC]
      exact key

@[simp] theorem fiberMap_ofBundleOfFinrankEqConjugateIso_hom (x : B) :
    (ofBundleOfFinrankEqConjugateIso E h h').hom.fiberMap x =
      (conjugateModelEquiv h h' : (Fin n' → ℂ) →L[ℂ] (Fin n → ℂ)) :=
  fiberMap_constIso_hom _ _ _ x

@[simp] theorem fiberMap_ofBundleOfFinrankEqConjugateIso_inv (x : B) :
    (ofBundleOfFinrankEqConjugateIso E h h').inv.fiberMap x =
      ((conjugateModelEquiv h h').symm : (Fin n → ℂ) →L[ℂ] (Fin n' → ℂ)) :=
  fiberMap_constIso_inv _ _ _ x

end OfBundle

end FiniteRankBundleCore

end TauCeti
