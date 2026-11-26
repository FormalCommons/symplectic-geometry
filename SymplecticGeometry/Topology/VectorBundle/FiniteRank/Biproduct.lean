/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.CategoryTheory.GrothendieckGroup.Split
public import TauCeti.Topology.VectorBundle.FiniteRank.Biproduct
public import TauCeti.Topology.VectorBundle.FiniteRank.Pullback
public import SymplecticGeometry.Topology.VectorBundle.FiniteRank.SMul
import SymplecticGeometry.Topology.VectorBundle.FiniteRank.Basic

/-!
# Whitney sums of finite-rank cores: charts, rotations and classes

Tau Ceti's `TauCeti.FiniteRankBundleCore.whitneySum A D` has the concatenated coordinates
`Fin (A.rank + D.rank) → 𝕜`, split into the two blocks by `TauCeti.splitCoords`. This file
computes chart expressions in charts of Whitney sums. It also builds the rotations of a sum
`A ⊕ A` of a core with itself, as automorphisms whose angle varies continuously along the base,
from the quarter turn `(v, w) ↦ (-w, v)` and the multiplication of morphisms by scalar functions
(`TauCeti.FiniteRankBundleCore.instModuleContinuousMapHom`), defines the iterated Whitney sum
`F ⊕ E ⊕ ⋯ ⊕ E`, and records that the class of a Whitney sum in the split Grothendieck group is
the sum of the classes.

## Main results

* `TauCeti.FiniteRankBundleCore.inChartCoordinates_whitneySum_prodMap`: in charts of Whitney
  sums, the chart expression of a block-diagonal map is the block-diagonal map of the chart
  expressions of its blocks;
* `TauCeti.FiniteRankBundleCore.whitneyQuarterTurn A`: the endomorphism `(v, w) ↦ (-w, v)` of
  `A ⊕ A`, whose square is `-𝟙`;
* `TauCeti.FiniteRankBundleCore.whitneyRotation A c s h`: for continuous scalar functions `c`, `s`
  with `c ^ 2 + s ^ 2 = 1`, the automorphism `c • 𝟙 + s • whitneyQuarterTurn A` of `A ⊕ A`, the
  rotation by the angle whose cosine and sine are `c` and `s`;
* `TauCeti.FiniteRankBundleCore.whitneySumIter E n F`: the Whitney sum `F ⊕ E ⊕ ⋯ ⊕ E` of `F`
  with `n` copies of `E`;
* `TauCeti.SplitK0.of_whitneySum`: in the split Grothendieck group of cores, the class of a
  Whitney sum is the sum of the classes;
* `TauCeti.FiniteRankBundleCore.whitneyMapIsoPullback e₁ e₂`: the direct sum of isomorphisms
  between two pullbacks, read through Tau Ceti's `pullback_whitneySum` as an isomorphism between
  the pullbacks of the Whitney sums;
* `TauCeti.FiniteRankBundleCore.fiberMap_eqToHom_whitneyMap_eqToHom`, with its forms
  `fiberMap_whitneyMapIsoPullback_hom` and `fiberMap_whitneyMapIsoPullback_inv` for
  isomorphisms: the direct sum of morphisms between two pullbacks, read through Tau Ceti's
  `pullback_whitneySum` as a morphism between the pullbacks of the Whitney sums, is block
  diagonal in each fibre.

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
    simp only [Preadditive.add_comp, Preadditive.comp_sub, Linear.smul_comp, Linear.comp_smul,
      Category.id_comp, Category.comp_id, whitneyQuarterTurn_comp_self]
    linear_combination (norm := module) h • 𝟙 (whitneySum A A)
  inv_hom_id := by
    simp only [Preadditive.sub_comp, Preadditive.comp_add, Linear.smul_comp, Linear.comp_smul,
      Category.id_comp, Category.comp_id, whitneyQuarterTurn_comp_self]
    linear_combination (norm := module) h • 𝟙 (whitneySum A A)

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

/-! ### Iterated Whitney sums -/

section WhitneySumIter

/-- The Whitney sum `F ⊕ E ⊕ ⋯ ⊕ E` of `F` with `n` copies of `E`, the sums taken from the
left: `whitneySumIter E (n + 1) F` is `whitneySumIter E n (F ⊕ E)`. -/
@[expose]
def whitneySumIter (E : FiniteRankBundleCore 𝕜 B) :
    ℕ → FiniteRankBundleCore 𝕜 B → FiniteRankBundleCore 𝕜 B
  | 0, F => F
  | n + 1, F => whitneySumIter E n (whitneySum F E)

variable (E F : FiniteRankBundleCore 𝕜 B)

@[simp]
theorem whitneySumIter_zero : whitneySumIter E 0 F = F :=
  (rfl)

theorem whitneySumIter_succ (n : ℕ) :
    whitneySumIter E (n + 1) F = whitneySumIter E n (whitneySum F E) :=
  (rfl)

@[simp]
theorem rank_whitneySumIter (n : ℕ) :
    (whitneySumIter E n F).rank = F.rank + n * E.rank := by
  induction n generalizing F with
  | zero => simp
  | succ n ih => rw [whitneySumIter_succ, ih, rank_whitneySum]; ring

/-- An isomorphism `F ≅ F'` gives an isomorphism of `F ⊕ E ⊕ ⋯ ⊕ E` with `F' ⊕ E ⊕ ⋯ ⊕ E`, the
sum of it with the identities of the copies of `E`. -/
def whitneySumIterMapIso : (n : ℕ) → {F F' : FiniteRankBundleCore 𝕜 B} → (F ≅ F') →
    (whitneySumIter E n F ≅ whitneySumIter E n F')
  | 0, _, _, e => e
  | n + 1, _, _, e => whitneySumIterMapIso n (whitneyMapIso e (Iso.refl E))

@[simp]
theorem whitneySumIterMapIso_zero {F F' : FiniteRankBundleCore 𝕜 B} (e : F ≅ F') :
    whitneySumIterMapIso E 0 e = e :=
  (rfl)

theorem whitneySumIterMapIso_succ (n : ℕ) {F F' : FiniteRankBundleCore 𝕜 B} (e : F ≅ F') :
    whitneySumIterMapIso E (n + 1) e =
      whitneySumIterMapIso E n (whitneyMapIso e (Iso.refl E)) :=
  (rfl)

end WhitneySumIter

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

omit p in
/-- The direct sum of `eqToHom`s is the `eqToHom` of the equality of the Whitney sums. -/
@[simp]
theorem whitneyMap_eqToHom (h : A = A') (h' : D = D') :
    whitneyMap (eqToHom h) (eqToHom h') = eqToHom (congrArg₂ whitneySum h h') := by
  subst h h'
  simp only [eqToHom_refl, whitneyMap_id]

variable {p} in
/-- The direct sum of isomorphisms `e₁ : A|_p ≅ A'|_p` and `e₂ : D|_p ≅ D'|_p` between pullbacks
along `p`, read through `pullback_whitneySum` as an isomorphism between the pullbacks of the
Whitney sums, `(A ⊕ D)|_p ≅ (A' ⊕ D')|_p`. -/
def whitneyMapIsoPullback (e₁ : A.pullback p ≅ A'.pullback p)
    (e₂ : D.pullback p ≅ D'.pullback p) :
    (whitneySum A D).pullback p ≅ (whitneySum A' D').pullback p :=
  eqToIso (pullback_whitneySum A D p) ≪≫ whitneyMapIso e₁ e₂ ≪≫
    eqToIso (pullback_whitneySum A' D' p).symm

variable (e₁ : A.pullback p ≅ A'.pullback p) (e₂ : D.pullback p ≅ D'.pullback p)

theorem whitneyMapIsoPullback_def :
    whitneyMapIsoPullback e₁ e₂ = eqToIso (pullback_whitneySum A D p) ≪≫ whitneyMapIso e₁ e₂ ≪≫
      eqToIso (pullback_whitneySum A' D' p).symm :=
  (rfl)

theorem whitneyMapIsoPullback_hom :
    (whitneyMapIsoPullback e₁ e₂).hom = eqToHom (pullback_whitneySum A D p) ≫
      whitneyMap e₁.hom e₂.hom ≫ eqToHom (pullback_whitneySum A' D' p).symm := by
  rw [whitneyMapIsoPullback_def, Iso.trans_hom, Iso.trans_hom, eqToIso.hom, eqToIso.hom,
    whitneyMapIso_hom]

theorem whitneyMapIsoPullback_inv :
    (whitneyMapIsoPullback e₁ e₂).inv = eqToHom (pullback_whitneySum A' D' p) ≫
      whitneyMap e₁.inv e₂.inv ≫ eqToHom (pullback_whitneySum A D p).symm := by
  rw [whitneyMapIsoPullback_def, Iso.trans_inv, Iso.trans_inv, eqToIso.inv, eqToIso.inv,
    whitneyMapIso_inv, Category.assoc]

/-- The direct sum of isomorphisms `e₁` and `e₂` between pullbacks along `p`, read through
`pullback_whitneySum`, acts on the fibres of the pullbacks of the Whitney sums
block-diagonally, with the fibre maps of `e₁` and `e₂` as blocks. -/
@[simp]
theorem fiberMap_whitneyMapIsoPullback_hom (x : X) :
    (whitneyMapIsoPullback e₁ e₂).hom.fiberMap x =
      (splitCoords (𝕜 := 𝕜) A'.rank D'.rank).symm.toContinuousLinearMap.comp
        (((e₁.hom.fiberMap x).prodMap (e₂.hom.fiberMap x)).comp
          (splitCoords (𝕜 := 𝕜) A.rank D.rank).toContinuousLinearMap) := by
  rw [whitneyMapIsoPullback_hom]
  exact fiberMap_eqToHom_whitneyMap_eqToHom p _ _ x

/-- The inverse of the direct sum of isomorphisms `e₁` and `e₂` between pullbacks along `p`, read
through `pullback_whitneySum`, acts on the fibres of the pullbacks of the Whitney sums
block-diagonally, with the fibre maps of `e₁⁻¹` and `e₂⁻¹` as blocks. -/
@[simp]
theorem fiberMap_whitneyMapIsoPullback_inv (x : X) :
    (whitneyMapIsoPullback e₁ e₂).inv.fiberMap x =
      (splitCoords (𝕜 := 𝕜) A.rank D.rank).symm.toContinuousLinearMap.comp
        (((e₁.inv.fiberMap x).prodMap (e₂.inv.fiberMap x)).comp
          (splitCoords (𝕜 := 𝕜) A'.rank D'.rank).toContinuousLinearMap) := by
  rw [whitneyMapIsoPullback_inv]
  exact fiberMap_eqToHom_whitneyMap_eqToHom p _ _ x

end Pullback

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
