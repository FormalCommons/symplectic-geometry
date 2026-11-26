/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Determinant
public import TauCeti.CategoryTheory.GrothendieckGroup.Split
public import TauCeti.Topology.VectorBundle.FiniteRank.Biproduct
public import SymplecticGeometry.Topology.VectorBundle.FiniteRank.SMul
import SymplecticGeometry.Topology.Algebra.Module.Determinant

/-!
# Whitney sums of finite-rank cores: charts, rotations and classes

Tau Ceti's `TauCeti.FiniteRankBundleCore.whitneySum A D` has the concatenated coordinates
`Fin (A.rank + D.rank) → 𝕜`, split into the two blocks by `TauCeti.splitCoords`. This file
computes chart expressions in charts of Whitney sums, and the determinants of the transitions of
a Whitney sum. It also builds the rotations of a sum `A ⊕ A` of a core with itself, as
automorphisms whose angle varies continuously along the base, from the quarter turn
`(v, w) ↦ (-w, v)` and the multiplication of morphisms by scalar functions
(`TauCeti.FiniteRankBundleCore.instModuleContinuousMapHom`), and records that the class of a
Whitney sum in the split Grothendieck group is the sum of the classes.

## Main results

* `TauCeti.FiniteRankBundleCore.inChartCoordinates_whitneySum_prodMap`: in charts of Whitney
  sums, the chart expression of a block-diagonal map is the block-diagonal map of the chart
  expressions of its blocks;
* `TauCeti.FiniteRankBundleCore.det_coordChange_whitneySum`: the transitions of a Whitney sum
  are block diagonal, so their determinants are the products of the determinants of the
  transitions of the summands;
* `TauCeti.FiniteRankBundleCore.whitneyQuarterTurn A`: the endomorphism `(v, w) ↦ (-w, v)` of
  `A ⊕ A`, whose square is `-𝟙`;
* `TauCeti.FiniteRankBundleCore.whitneyRotation A c s h`: for continuous scalar functions `c`, `s`
  with `c ^ 2 + s ^ 2 = 1`, the automorphism `c • 𝟙 + s • whitneyQuarterTurn A` of `A ⊕ A`, the
  rotation by the angle whose cosine and sine are `c` and `s`;
* `TauCeti.SplitK0.of_whitneySum`: in the split Grothendieck group of cores, the class of a
  Whitney sum is the sum of the classes.

The proof of `inChartCoordinates_whitneySum_prodMap` follows Tau Ceti's
`TauCeti.FiniteRankBundleCore.inChartCoordinates_tensor_kronecker`, which computes the chart
expression of a Kronecker product in charts of tensor products.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

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

/-! ### Rotations of `A ⊕ A` -/

/-- The quarter turn of the Whitney sum `A ⊕ A`, with fibre map `(v, w) ↦ (-w, v)`. -/
def whitneyQuarterTurn (A : FiniteRankBundleCore 𝕜 B) : whitneySum A A ⟶ whitneySum A A :=
  whitneyLift (-whitneySnd A A) (whitneyFst A A)

theorem whitneyQuarterTurn_def (A : FiniteRankBundleCore 𝕜 B) :
    whitneyQuarterTurn A = whitneyLift (-whitneySnd A A) (whitneyFst A A) :=
  (rfl)

@[reassoc (attr := simp)]
theorem whitneyQuarterTurn_fst (A : FiniteRankBundleCore 𝕜 B) :
    whitneyQuarterTurn A ≫ whitneyFst A A = -whitneySnd A A :=
  whitneyLift_fst _ _

@[reassoc (attr := simp)]
theorem whitneyQuarterTurn_snd (A : FiniteRankBundleCore 𝕜 B) :
    whitneyQuarterTurn A ≫ whitneySnd A A = whitneyFst A A :=
  whitneyLift_snd _ _

/-- The square of the quarter turn is `-𝟙`. -/
@[simp]
theorem whitneyQuarterTurn_comp_self (A : FiniteRankBundleCore 𝕜 B) :
    whitneyQuarterTurn A ≫ whitneyQuarterTurn A = -𝟙 _ :=
  whitneySum_hom_ext (by simp) (by simp)

theorem fiberMap_whitneyQuarterTurn_fiberMap_whitneyQuarterTurn (A : FiniteRankBundleCore 𝕜 B)
    (x : B) (v : Fin (whitneySum A A).rank → 𝕜) :
    (whitneyQuarterTurn A).fiberMap x ((whitneyQuarterTurn A).fiberMap x v) = -v := by
  have h := DFunLike.congr_fun (congrArg (fun f ↦ VectorBundleCore.CoordinateHom.fiberMap f x)
    (whitneyQuarterTurn_comp_self A)) v
  simp only [fiberMap_comp, fiberMap_neg, fiberMap_id] at h
  exact h

/-- Conjugating a block-diagonal map by the quarter turn swaps its blocks. -/
theorem whitneyQuarterTurn_comp_whitneyMap_comp_neg {A D : FiniteRankBundleCore 𝕜 B}
    (f g : A ⟶ D) :
    whitneyQuarterTurn A ≫ whitneyMap f g ≫ (-whitneyQuarterTurn D) = whitneyMap g f :=
  whitneySum_hom_ext (by simp) (by simp)

/-- The rotation of the Whitney sum `A ⊕ A` by the angle, varying along the base, whose cosine
and sine are the continuous functions `c` and `s`: the automorphism `c • 𝟙 + s • J`, with `J` the
quarter turn `(v, w) ↦ (-w, v)`, and inverse `c • 𝟙 - s • J`. -/
def whitneyRotation (A : FiniteRankBundleCore 𝕜 B) (c s : C(B, 𝕜)) (h : c ^ 2 + s ^ 2 = 1) :
    whitneySum A A ≅ whitneySum A A where
  hom := c • 𝟙 _ + s • whitneyQuarterTurn A
  inv := c • 𝟙 _ - s • whitneyQuarterTurn A
  hom_inv_id := by
    have hx (x : B) : c x ^ 2 + s x ^ 2 = 1 := by simpa using congr($h x)
    refine hom_ext fun x ↦ ContinuousLinearMap.ext fun v ↦ ?_
    simp only [sub_eq_add_neg, ← neg_smul, fiberMap_comp, fiberMap_add, fiberMap_smul,
      fiberMap_id, ContinuousMap.neg_apply, ContinuousLinearMap.comp_apply, add_apply, smul_apply,
      ContinuousLinearMap.id_apply, map_add, map_smul,
      fiberMap_whitneyQuarterTurn_fiberMap_whitneyQuarterTurn]
    linear_combination (norm := module) hx x • v
  inv_hom_id := by
    have hx (x : B) : c x ^ 2 + s x ^ 2 = 1 := by simpa using congr($h x)
    refine hom_ext fun x ↦ ContinuousLinearMap.ext fun v ↦ ?_
    simp only [sub_eq_add_neg, ← neg_smul, fiberMap_comp, fiberMap_add, fiberMap_smul,
      fiberMap_id, ContinuousMap.neg_apply, ContinuousLinearMap.comp_apply, add_apply, smul_apply,
      ContinuousLinearMap.id_apply, map_add, map_smul,
      fiberMap_whitneyQuarterTurn_fiberMap_whitneyQuarterTurn]
    linear_combination (norm := module) hx x • v

@[simp]
theorem whitneyRotation_hom (A : FiniteRankBundleCore 𝕜 B) (c s : C(B, 𝕜))
    (h : c ^ 2 + s ^ 2 = 1) :
    (whitneyRotation A c s h).hom = c • 𝟙 _ + s • whitneyQuarterTurn A :=
  (rfl)

@[simp]
theorem whitneyRotation_inv (A : FiniteRankBundleCore 𝕜 B) (c s : C(B, 𝕜))
    (h : c ^ 2 + s ^ 2 = 1) :
    (whitneyRotation A c s h).inv = c • 𝟙 _ - s • whitneyQuarterTurn A :=
  (rfl)

theorem fiberMap_whitneyRotation_hom (A : FiniteRankBundleCore 𝕜 B) (c s : C(B, 𝕜))
    (h : c ^ 2 + s ^ 2 = 1) (x : B) :
    (whitneyRotation A c s h).hom.fiberMap x =
      c x • .id 𝕜 _ + s x • (whitneyQuarterTurn A).fiberMap x := by
  rw [whitneyRotation_hom, fiberMap_add, fiberMap_smul, fiberMap_smul, fiberMap_id]

theorem fiberMap_whitneyRotation_inv (A : FiniteRankBundleCore 𝕜 B) (c s : C(B, 𝕜))
    (h : c ^ 2 + s ^ 2 = 1) (x : B) :
    (whitneyRotation A c s h).inv.fiberMap x =
      c x • .id 𝕜 _ - s x • (whitneyQuarterTurn A).fiberMap x := by
  rw [whitneyRotation_inv, sub_eq_add_neg, ← neg_smul, fiberMap_add, fiberMap_smul, fiberMap_smul,
    fiberMap_id, ContinuousMap.neg_apply, neg_smul, ← sub_eq_add_neg]

end TauCeti.FiniteRankBundleCore

/-! ### The class of a Whitney sum -/

namespace TauCeti.SplitK0

/-- **The class of a Whitney sum is the sum of the classes.** In the split Grothendieck group of
finite-rank cores over `B`, `[A ⊕ D] = [A] + [D]`. -/
@[simp]
theorem of_whitneySum {𝕜 B : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B]
    (A D : FiniteRankBundleCore 𝕜 B) :
    (of (FiniteRankBundleCore.whitneySum A D) : SplitK0 (FiniteRankBundleCore 𝕜 B)) = of A + of D :=
  (of_congr (biprod.uniqueUpToIso A D (FiniteRankBundleCore.whitneyBiconeIsBilimit A D))).trans
    (of_biprod A D)

end TauCeti.SplitK0

end
