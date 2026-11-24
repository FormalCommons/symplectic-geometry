/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Analysis.Normed.Operator.ExteriorPowerCoords
public import TauCeti.Topology.VectorBundle.FiniteRank.Conjugate
public import TauCeti.Topology.VectorBundle.FiniteRank.ExteriorPower

/-!
# Exterior powers of conjugate bundles

The `k`th exterior power of the conjugate of a complex finite-rank core is the conjugate of its
`k`th exterior power. On transitions this says that the compound matrix of the entrywise
conjugate of a matrix is the entrywise conjugate of its compound matrix
(`ContinuousLinearMap.exteriorPowerCoords_intrinsicStar`): the minors of a matrix are
polynomials with integer coefficients in its entries.

## Main definitions

* `TauCeti.FiniteRankBundleCore.exteriorPowerConjugateIso k A`:
  `⋀^k (conj A) ≅ conj (⋀^k A)`, by the identity on every fibre;
* `TauCeti.FiniteRankBundleCore.exteriorPowerConjugateNatIso k`: the same, natural in `A`, as an
  isomorphism `conjugate B ⋙ exteriorPower ℂ B k ≅ exteriorPower ℂ B k ⋙ conjugate B`;
* `TauCeti.FiniteRankBundleCore.detConjugateIso A`: the determinant line of the conjugate is the
  conjugate of the determinant line.

The statements and proofs follow Tau Ceti's `doubleConjugateIso`, `doubleConjugateNatIso` and
`conjugatePullbackIso`.

## References

* M. F. Atiyah, *K-Theory*, §1.2 and §3.1.
-/

public section

open CategoryTheory WithConv

namespace TauCeti

namespace FiniteRankBundleCore

universe u

variable {B : Type u} [TopologicalSpace B]

/-- The `k`th exterior power of the conjugate of `A` is the conjugate of the `k`th exterior power
of `A`, by the identity on every fibre. -/
noncomputable def exteriorPowerConjugateIso (k : ℕ) (A : FiniteRankBundleCore ℂ B) :
    (exteriorPower ℂ B k).obj ((conjugate B).obj A) ≅
      (conjugate B).obj ((exteriorPower ℂ B k).obj A) :=
  constIso (fun _ => subset_rfl) (ContinuousLinearEquiv.refl ℂ _) fun i j x _ _ => by
    simp only [coordChange_exteriorPower_obj, coordChange_conjugate_obj]
    -- State the identity on standard coordinates to fix the inherited fibre instances.
    have h : (ContinuousLinearMap.id ℂ (Fin (A.rank.choose k) → ℂ)).comp
        ((star (toConv (A.core.coordChange i j x))).ofConv.exteriorPowerCoords k) =
        (star (toConv ((A.core.coordChange i j x).exteriorPowerCoords k))).ofConv.comp
          (ContinuousLinearMap.id ℂ (Fin (A.rank.choose k) → ℂ)) := by
      rw [ContinuousLinearMap.exteriorPowerCoords_intrinsicStar, ContinuousLinearMap.id_comp,
        ContinuousLinearMap.comp_id]
    exact h

@[simp] theorem fiberMap_exteriorPowerConjugateIso_hom (k : ℕ) (A : FiniteRankBundleCore ℂ B)
    (x : B) :
    (exteriorPowerConjugateIso k A).hom.fiberMap x =
      ContinuousLinearMap.id ℂ (Fin (A.rank.choose k) → ℂ) := by
  rw [exteriorPowerConjugateIso]
  exact fiberMap_constIso_hom _ _ _ x

@[simp] theorem fiberMap_exteriorPowerConjugateIso_inv (k : ℕ) (A : FiniteRankBundleCore ℂ B)
    (x : B) :
    (exteriorPowerConjugateIso k A).inv.fiberMap x =
      ContinuousLinearMap.id ℂ (Fin (A.rank.choose k) → ℂ) := by
  rw [exteriorPowerConjugateIso]
  exact fiberMap_constIso_inv _ _ _ x

/-- The comparison of exterior powers of conjugates is natural in bundle maps. -/
@[reassoc] theorem exteriorPowerConjugateIso_naturality (k : ℕ)
    {A D : FiniteRankBundleCore ℂ B} (f : A ⟶ D) :
    (exteriorPower ℂ B k).map ((conjugate B).map f) ≫ (exteriorPowerConjugateIso k D).hom =
      (exteriorPowerConjugateIso k A).hom ≫ (conjugate B).map ((exteriorPower ℂ B k).map f) := by
  apply hom_ext
  intro x
  simp only [fiberMap_comp, fiberMap_exteriorPower_map, fiberMap_conjugate_map,
    fiberMap_exteriorPowerConjugateIso_hom]
  -- State the identity on the common standard coordinate models.
  have h : (ContinuousLinearMap.id ℂ (Fin (D.rank.choose k) → ℂ)).comp
      ((star (toConv (f.fiberMap x))).ofConv.exteriorPowerCoords k) =
      (star (toConv ((f.fiberMap x).exteriorPowerCoords k))).ofConv.comp
        (ContinuousLinearMap.id ℂ (Fin (A.rank.choose k) → ℂ)) := by
    rw [ContinuousLinearMap.exteriorPowerCoords_intrinsicStar, ContinuousLinearMap.id_comp,
      ContinuousLinearMap.comp_id]
  exact h

variable (B) in
/-- Exterior powers commute with conjugation, as functors. -/
noncomputable def exteriorPowerConjugateNatIso (k : ℕ) :
    conjugate B ⋙ exteriorPower ℂ B k ≅ exteriorPower ℂ B k ⋙ conjugate B :=
  NatIso.ofComponents (exteriorPowerConjugateIso k) (exteriorPowerConjugateIso_naturality k)

@[simp] theorem exteriorPowerConjugateNatIso_app (k : ℕ) (A : FiniteRankBundleCore ℂ B) :
    (exteriorPowerConjugateNatIso B k).app A = exteriorPowerConjugateIso k A := (rfl)

/-- The determinant line of the conjugate of `A` is the conjugate of the determinant line of `A`.
Conjugation keeps the rank (`rank_conjugate_obj`), so both are exterior powers in the same degree,
and `exteriorPowerConjugateIso` compares them. -/
noncomputable def detConjugateIso (A : FiniteRankBundleCore ℂ B) :
    ((conjugate B).obj A).det ≅ (conjugate B).obj A.det :=
  eqToIso (det_def _) ≪≫ exteriorPowerConjugateIso A.rank A ≪≫
    eqToIso (congrArg (conjugate B).obj (det_def A).symm)

theorem detConjugateIso_def (A : FiniteRankBundleCore ℂ B) :
    detConjugateIso A = eqToIso (det_def _) ≪≫ exteriorPowerConjugateIso A.rank A ≪≫
      eqToIso (congrArg (conjugate B).obj (det_def A).symm) := (rfl)

end FiniteRankBundleCore

end TauCeti
