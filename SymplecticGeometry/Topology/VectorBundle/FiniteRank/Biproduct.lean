/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Determinant
public import TauCeti.Topology.VectorBundle.FiniteRank.Biproduct
public import TauCeti.Topology.VectorBundle.FiniteRank.Pullback
public import SymplecticGeometry.Topology.VectorBundle.FiniteRank.Basic
import SymplecticGeometry.Topology.Algebra.Module.Determinant

/-!
# Whitney sums of finite-rank cores in charts

Tau Ceti's `TauCeti.FiniteRankBundleCore.whitneySum A D` has the concatenated coordinates
`Fin (A.rank + D.rank) → 𝕜`, split into the two blocks by `TauCeti.splitCoords`. This file
computes chart expressions in charts of Whitney sums, and the determinants of the transitions of
a Whitney sum.

## Main results

* `TauCeti.FiniteRankBundleCore.inChartCoordinates_whitneySum_prodMap`: in charts of Whitney
  sums, the chart expression of a block-diagonal map is the block-diagonal map of the chart
  expressions of its blocks;
* `TauCeti.FiniteRankBundleCore.det_coordChange_whitneySum`: the transitions of a Whitney sum
  are block diagonal, so their determinants are the products of the determinants of the
  transitions of the summands;
* `TauCeti.FiniteRankBundleCore.fiberMap_eqToHom_whitneyMap_eqToHom`, with its forms
  `fiberMap_eqToIso_whitneyMapIso_hom` and `fiberMap_eqToIso_whitneyMapIso_inv` for
  automorphisms: the direct sum of morphisms between two pullbacks, read through Tau Ceti's
  `pullback_whitneySum` as a morphism between the pullbacks of the Whitney sums, is block
  diagonal in each fibre.

The proof of `inChartCoordinates_whitneySum_prodMap` follows Tau Ceti's
`TauCeti.FiniteRankBundleCore.inChartCoordinates_tensor_kronecker`, which computes the chart
expression of a Kronecker product in charts of tensor products.
-/

public section

noncomputable section

open CategoryTheory

namespace TauCeti.FiniteRankBundleCore

variable {𝕜 B : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B]

/-- Read in charts of Whitney sums, a block-diagonal map is block diagonal, with the chart
expressions of its blocks as blocks. -/
theorem inChartCoordinates_whitneySum_prodMap
    (A A' D D' : FiniteRankBundleCore 𝕜 B)
    (f : (Fin A.rank → 𝕜) →L[𝕜] (Fin A'.rank → 𝕜))
    (g : (Fin D.rank → 𝕜) →L[𝕜] (Fin D'.rank → 𝕜)) (i j x : B) :
    (whitneySum A D).core.inChartCoordinates (whitneySum A' D').core i j x
        ((splitCoords (𝕜 := 𝕜) A'.rank D'.rank).symm.toContinuousLinearMap.comp
          ((f.prodMap g).comp (splitCoords (𝕜 := 𝕜) A.rank D.rank).toContinuousLinearMap)) =
      (splitCoords (𝕜 := 𝕜) A'.rank D'.rank).symm.toContinuousLinearMap.comp
        (((A.core.inChartCoordinates A'.core i j x f).prodMap
            (D.core.inChartCoordinates D'.core i j x g)).comp
          (splitCoords (𝕜 := 𝕜) A.rank D.rank).toContinuousLinearMap) := by
  refine (inChartCoordinates_core _ _ i j x _).trans ?_
  rw [inChartCoordinates_core, inChartCoordinates_core]
  -- Unfold the transitions of the Whitney sums, whose fibre models are the concatenated
  -- coordinates.
  dsimp +instances only [whitneySum]
  ext v : 1
  simp

/-- The transition maps of a Whitney sum are block diagonal, so their determinants are the
products of the determinants of the transition maps of the two summands. -/
@[simp]
theorem det_coordChange_whitneySum (A D : FiniteRankBundleCore 𝕜 B) (i j x : B) :
    ((whitneySum A D).core.coordChange i j x).det =
      (A.core.coordChange i j x).det * (D.core.coordChange i j x).det :=
  ContinuousLinearMap.det_eq_det_mul_det_of_splitCoords _ _ _
    (coordChange_whitneySum_splitCoords_symm A D i j x)

section Pullback

variable {X : Type*} [TopologicalSpace X] {A A' D D' : FiniteRankBundleCore 𝕜 B} (p : C(X, B))

/-- Read through `pullback_whitneySum`, the direct sum of morphisms `f` and `g` between pullbacks
along `p` acts on the fibres of the pullbacks of the Whitney sums block-diagonally, with the fibre
maps of `f` and `g` as blocks. -/
theorem fiberMap_eqToHom_whitneyMap_eqToHom (f : A.pullback p ⟶ A'.pullback p)
    (g : D.pullback p ⟶ D'.pullback p) (x : X) :
    (eqToHom (pullback_whitneySum A D p) ≫ whitneyMap f g ≫
      eqToHom (pullback_whitneySum A' D' p).symm).fiberMap x =
      (splitCoords (𝕜 := 𝕜) A'.rank D'.rank).symm.toContinuousLinearMap.comp
        (((f.fiberMap x).prodMap (g.fiberMap x)).comp
          (splitCoords (𝕜 := 𝕜) A.rank D.rank).toContinuousLinearMap) := by
  ext v i
  simp only [fiberMap_comp, ContinuousLinearMap.comp_apply, fiberMap_eqToHom,
    Function.comp_apply]
  -- The casts are along `rank_pullback` and `rank_whitneySum`, which hold by `rfl`.
  exact congrFun (DFunLike.congr_fun (fiberMap_whitneyMap _ _ _) _) _

variable (e₁ : A.pullback p ≅ A.pullback p) (e₂ : D.pullback p ≅ D.pullback p)

/-- Read through `pullback_whitneySum`, the direct sum of automorphisms `e₁` and `e₂` of the
pullbacks of `A` and `D` along `p` acts on the fibre of the pullback of `A ⊕ D` block-diagonally,
with the fibre maps of `e₁` and `e₂` as blocks. -/
theorem fiberMap_eqToIso_whitneyMapIso_hom (x : X) :
    (eqToIso (pullback_whitneySum A D p) ≪≫ whitneyMapIso e₁ e₂ ≪≫
      eqToIso (pullback_whitneySum A D p).symm).hom.fiberMap x =
      (splitCoords (𝕜 := 𝕜) A.rank D.rank).symm.toContinuousLinearMap.comp
        (((e₁.hom.fiberMap x).prodMap (e₂.hom.fiberMap x)).comp
          (splitCoords (𝕜 := 𝕜) A.rank D.rank).toContinuousLinearMap) := by
  simp only [Iso.trans_hom, eqToIso.hom, whitneyMapIso_hom]
  exact fiberMap_eqToHom_whitneyMap_eqToHom p _ _ x

/-- Read through `pullback_whitneySum`, the inverse of the direct sum of automorphisms `e₁` and
`e₂` of the pullbacks of `A` and `D` along `p` acts on the fibre of the pullback of `A ⊕ D`
block-diagonally, with the fibre maps of `e₁⁻¹` and `e₂⁻¹` as blocks. -/
theorem fiberMap_eqToIso_whitneyMapIso_inv (x : X) :
    (eqToIso (pullback_whitneySum A D p) ≪≫ whitneyMapIso e₁ e₂ ≪≫
      eqToIso (pullback_whitneySum A D p).symm).inv.fiberMap x =
      (splitCoords (𝕜 := 𝕜) A.rank D.rank).symm.toContinuousLinearMap.comp
        (((e₁.inv.fiberMap x).prodMap (e₂.inv.fiberMap x)).comp
          (splitCoords (𝕜 := 𝕜) A.rank D.rank).toContinuousLinearMap) := by
  simp only [Iso.trans_inv, eqToIso.inv, whitneyMapIso_inv, Category.assoc]
  exact fiberMap_eqToHom_whitneyMap_eqToHom p _ _ x

end Pullback

end TauCeti.FiniteRankBundleCore

end
