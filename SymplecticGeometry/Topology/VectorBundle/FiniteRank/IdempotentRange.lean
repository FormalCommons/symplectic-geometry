/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.CategoryTheory.Idempotents.Basic
public import SymplecticGeometry.Topology.VectorBundle.Core.Basic
public import SymplecticGeometry.Topology.VectorBundle.FiniteRank.Range
public import TauCeti.Analysis.Normed.Operator.IdempotentRange
public import TauCeti.Topology.VectorBundle.FiniteRank.Biproduct

/-!
# Idempotent bundle endomorphisms: their rank, and the splitting along them

For a coordinate endomorphism `P` of a vector-bundle core (`VectorBundleCore.CoordinateHom Z Z`)
whose fibre maps are idempotent, over a complete model fibre, the rank of the range of
`P.fiberMap x` is a locally constant function of the base point. We apply this to an endomorphism
`P` of one of Tau Ceti's finite-rank cores (`TauCeti.FiniteRankBundleCore`) with `P ≫ P = P`:
its rank is locally constant, and constant over a preconnected base. This constant rank is what
one needs to make the range of `P` into a finite-rank core of its own, since such a core has the
same rank at every point. Over a disconnected base the rank of `P` may differ from one component
to another.

The proof applies Tau Ceti's `TauCeti.isLocallyConstant_finrank_range`, for a continuous family of
projections on a fixed space, to the chart operator of `P` in the chart of `Z` at a point `x₀`.
On that chart's base set this operator is continuous and idempotent, and it is conjugate to the
fibre map of `P` by transition maps, so it has the same rank
(`VectorBundleCore.finrank_range_inChartCoordinates`). Tau Ceti's
`TauCeti.Topology.VectorBundle.ConstantRank` compares ranks through charts in the same way
(`ContinuousLinearMap.finrank_range_inCoordinates`).

Suppose next that `P` has constant rank `r` and `𝟙 E - P` constant rank `s` (the latter is
idempotent too, by Mathlib's `CategoryTheory.Idempotents.idem_of_id_sub_idem`). Then `E` is the
Whitney sum of the range cores `range P hr` and `range (𝟙 E - P) hs` of `FiniteRank/Range.lean`,
as in [Hatcher2017, §2.1]. The isomorphism `rangeWhitneySumIso` pairs the two corestrictions by
`whitneyLift`; its inverse is the `whitneyDesc` of the two inclusions. It carries `P` to
`whitneyMap (𝟙 _) 0`. An endomorphism `T` that commutes with `P` restricts to each range core
(`restrictRange`), and the isomorphism carries `T` to the `whitneyMap` of the two restrictions.
All of this follows from the identities `rangeRestrict_rangeInclusion` and
`rangeInclusion_rangeRestrict_of_comp_self` and from Tau Ceti's biproduct API
(`TauCeti/Topology/VectorBundle/FiniteRank/Biproduct.lean`).

## Main results

* `VectorBundleCore.CoordinateHom.finrank_range_operator`: a chart operator of a coordinate
  morphism has the rank of the fibre map.
* `VectorBundleCore.CoordinateHom.isLocallyConstant_finrank_range_fiberMap`: the rank of a
  coordinate endomorphism with idempotent fibre maps is locally constant on the base.
* `TauCeti.FiniteRankBundleCore.isIdempotentElem_fiberMap`: the fibre maps of an idempotent
  endomorphism of a finite-rank core are idempotent.
* `TauCeti.FiniteRankBundleCore.isLocallyConstant_finrank_range_fiberMap`: the rank of an
  idempotent endomorphism of a finite-rank core is locally constant on the base.
* `TauCeti.FiniteRankBundleCore.finrank_range_fiberMap_eq`: over a preconnected base it is
  constant.
* `TauCeti.FiniteRankBundleCore.finrank_range_one_sub_fiberMap`: at each point, the rank of
  `𝟙 E - P` is that of `E` minus that of `P`.
* `TauCeti.FiniteRankBundleCore.rangeWhitneySumIso`: the isomorphism of `E` with
  `whitneySum (range P hr) (range (𝟙 E - P) hs)`, and
  `rangeWhitneySumIso_inv_comp_self_comp_hom`: it carries `P` to `whitneyMap (𝟙 _) 0`.
* `TauCeti.FiniteRankBundleCore.restrictRange`: the restriction of an endomorphism to the range
  core of `P`, with `restrictRange_rangeInclusion`, `restrictRange_id` and `restrictRange_comp`.
* `TauCeti.FiniteRankBundleCore.rangeWhitneySumIso_inv_comp_comp_hom`: an endomorphism that
  commutes with `P` is block diagonal.

## References

* T. Kato, *Perturbation Theory for Linear Operators*, Springer, Chapter I, §4.6.
* [A. Hatcher, *Vector Bundles and K-Theory*][Hatcher2017]
-/

public section

open CategoryTheory Filter

namespace VectorBundleCore.CoordinateHom

variable {𝕜 B F G ι κ : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {Z : VectorBundleCore 𝕜 B F ι} {W : VectorBundleCore 𝕜 B G κ}

/-- At a point `y` of the source chart `i` and the target chart `j`, the chart operator of a
coordinate morphism has the rank of its fibre map at `y`. -/
theorem finrank_range_operator (f : CoordinateHom Z W) (i : ι) (j : κ)
    (y : ↥(Z.baseSet i ∩ W.baseSet j)) :
    Module.finrank 𝕜 (f.operator i j y).range = Module.finrank 𝕜 (f.fiberMap y.val).range := by
  rw [operator_eq, Z.finrank_range_inChartCoordinates y.property.1 y.property.2]

/-- Over a complete model fibre, the rank of a coordinate endomorphism `P` whose fibre maps are
idempotent, that is the dimension of the range of `P.fiberMap x`, is a locally constant function
of `x`. -/
theorem isLocallyConstant_finrank_range_fiberMap [CompleteSpace F] (P : CoordinateHom Z Z)
    (hP : ∀ x, IsIdempotentElem (P.fiberMap x)) :
    IsLocallyConstant fun x ↦ Module.finrank 𝕜 (P.fiberMap x).range := by
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun x₀ ↦ ?_
  have hU : IsOpen (Z.baseSet (Z.indexAt x₀) ∩ Z.baseSet (Z.indexAt x₀)) :=
    (Z.isOpen_baseSet _).inter (Z.isOpen_baseSet _)
  have hx₀ : x₀ ∈ Z.baseSet (Z.indexAt x₀) ∩ Z.baseSet (Z.indexAt x₀) :=
    ⟨Z.mem_baseSet_at x₀, Z.mem_baseSet_at x₀⟩
  have hPP : P.comp P = P := fiberMap_injective <| funext fun x ↦ by
    rw [fiberMap_comp, ← ContinuousLinearMap.mul_def, (hP x).eq]
  have hidem (y) : IsIdempotentElem (P.operator (Z.indexAt x₀) (Z.indexAt x₀) y) :=
    (operator_comp P P _ _ _ y.property.1 y.property.1 y.property.2).symm.trans
      (congrArg (fun f ↦ f.operator (Z.indexAt x₀) (Z.indexAt x₀) y) hPP)
  have h := (IsLocallyConstant.iff_eventually_eq _).1
    (TauCeti.isLocallyConstant_finrank_range (P.operator _ _).continuous hidem) ⟨x₀, hx₀⟩
  rw [← hU.isOpenEmbedding_subtypeVal.map_nhds_eq ⟨x₀, hx₀⟩, eventually_map]
  filter_upwards [h] with y hy
  rw [← finrank_range_operator, hy, finrank_range_operator]

end VectorBundleCore.CoordinateHom

namespace TauCeti.FiniteRankBundleCore

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {X : Type*} [TopologicalSpace X]
  {E : FiniteRankBundleCore 𝕜 X} {P : E ⟶ E}

/-- The fibre maps of an idempotent endomorphism of a finite-rank core are idempotent. -/
theorem isIdempotentElem_fiberMap (hP : P ≫ P = P) (x : X) :
    IsIdempotentElem (P.fiberMap x) := by
  rw [IsIdempotentElem, ContinuousLinearMap.mul_def, ← fiberMap_comp, hP]

/-- At each point, the rank of `𝟙 E - P` for an idempotent endomorphism `P` of a finite-rank core
is the rank of the core minus the rank of `P`. -/
theorem finrank_range_one_sub_fiberMap (hP : P ≫ P = P) (x : X) :
    Module.finrank 𝕜 ((𝟙 E - P).fiberMap x).range =
      E.rank - Module.finrank 𝕜 (P.fiberMap x).range := by
  have hrk := LinearMap.finrank_range_add_finrank_ker (P.fiberMap x).toLinearMap
  rw [Module.finrank_fin_fun, LinearMap.IsIdempotentElem.ker_eq_range_one_sub
    (ContinuousLinearMap.IsIdempotentElem.toLinearMap (isIdempotentElem_fiberMap hP x))] at hrk
  have h1 : ((𝟙 E - P).fiberMap x).toLinearMap = 1 - (P.fiberMap x).toLinearMap := by
    ext v; simp [sub_eq_add_neg]
  rw [h1]
  omega

variable [CompleteSpace 𝕜]

/-- The rank of an idempotent endomorphism `P` of a finite-rank core, that is the dimension of the
range of `P.fiberMap x`, is a locally constant function of `x`. -/
theorem isLocallyConstant_finrank_range_fiberMap (hP : P ≫ P = P) :
    IsLocallyConstant fun x ↦ Module.finrank 𝕜 (P.fiberMap x).range :=
  VectorBundleCore.CoordinateHom.isLocallyConstant_finrank_range_fiberMap P
    (isIdempotentElem_fiberMap hP)

/-- Over a preconnected base, an idempotent endomorphism `P` of a finite-rank core has the same
rank at every point. Without preconnectedness this fails: over a disconnected base `P` can be the
identity over one component and zero over another. -/
theorem finrank_range_fiberMap_eq [PreconnectedSpace X] (hP : P ≫ P = P) (x y : X) :
    Module.finrank 𝕜 (P.fiberMap x).range = Module.finrank 𝕜 (P.fiberMap y).range :=
  (isLocallyConstant_finrank_range_fiberMap hP).apply_eq_of_preconnectedSpace x y

section Splitting

variable [IsRCLikeNormedField 𝕜] {r s : ℕ}
  (hr : ∀ x, Module.finrank 𝕜 (P.fiberMap x).range = r)
  (hs : ∀ x, Module.finrank 𝕜 ((𝟙 E - P).fiberMap x).range = s)

/-- An idempotent `P` followed by its corestriction to its range core is that corestriction. -/
@[reassoc (attr := simp)]
theorem comp_rangeRestrict_of_comp_self (hP : P ≫ P = P) :
    P ≫ rangeRestrict P hr = rangeRestrict P hr := by
  calc P ≫ rangeRestrict P hr
      = (rangeRestrict P hr ≫ rangeInclusion P hr) ≫ rangeRestrict P hr := by
        rw [rangeRestrict_rangeInclusion]
    _ = rangeRestrict P hr := by
        rw [Category.assoc, rangeInclusion_rangeRestrict_of_comp_self hr hP, Category.comp_id]

/-- For an idempotent `P`, the inclusion of the range core of `P` followed by the corestriction to
the range core of `𝟙 E - P` is zero. -/
@[reassoc (attr := simp)]
theorem rangeInclusion_rangeRestrict_one_sub (hP : P ≫ P = P) :
    rangeInclusion P hr ≫ rangeRestrict (𝟙 E - P) hs = 0 := by
  rw [← comp_rangeRestrict_of_comp_self hs (Idempotents.idem_of_id_sub_idem P hP),
    ← Category.assoc, Preadditive.comp_sub, Category.comp_id,
    rangeInclusion_comp_of_comp_self hr hP, sub_self, Limits.zero_comp]

/-- An idempotent `P` vanishes on the range core of `𝟙 E - P`. -/
@[reassoc (attr := simp)]
theorem rangeInclusion_one_sub_comp_of_comp_self (hP : P ≫ P = P) :
    rangeInclusion (𝟙 E - P) hs ≫ P = 0 := by
  have := rangeInclusion_comp_of_comp_self hs (Idempotents.idem_of_id_sub_idem P hP)
  rwa [Preadditive.comp_sub, Category.comp_id, sub_eq_self] at this

/-- For an idempotent `P`, the inclusion of the range core of `𝟙 E - P` followed by the
corestriction to the range core of `P` is zero. -/
@[reassoc (attr := simp)]
theorem rangeInclusion_one_sub_rangeRestrict (hP : P ≫ P = P) :
    rangeInclusion (𝟙 E - P) hs ≫ rangeRestrict P hr = 0 := by
  rw [← comp_rangeRestrict_of_comp_self hr hP, rangeInclusion_one_sub_comp_of_comp_self_assoc hs hP,
    Limits.zero_comp]

/-- An idempotent endomorphism `P` of `E`, of constant rank `r`, with `𝟙 E - P` of constant
rank `s`, splits `E` as the Whitney sum of the range cores of `P` and of `𝟙 E - P`. The
isomorphism pairs the two corestrictions, and its inverse is the copairing of the two
inclusions. -/
noncomputable def rangeWhitneySumIso (hP : P ≫ P = P) :
    E ≅ whitneySum (range P hr) (range (𝟙 E - P) hs) where
  hom := whitneyLift (rangeRestrict P hr) (rangeRestrict (𝟙 E - P) hs)
  inv := whitneyDesc (rangeInclusion P hr) (rangeInclusion (𝟙 E - P) hs)
  hom_inv_id := by
    rw [whitneyLift_desc, rangeRestrict_rangeInclusion, rangeRestrict_rangeInclusion,
      add_sub_cancel]
  inv_hom_id := by
    refine whitneySum_hom_ext' ?_ ?_ <;> refine whitneySum_hom_ext ?_ ?_ <;> simp [hP]

@[simp]
theorem rangeWhitneySumIso_hom (hP : P ≫ P = P) :
    (rangeWhitneySumIso hr hs hP).hom =
      whitneyLift (rangeRestrict P hr) (rangeRestrict (𝟙 E - P) hs) := (rfl)

@[simp]
theorem rangeWhitneySumIso_inv (hP : P ≫ P = P) :
    (rangeWhitneySumIso hr hs hP).inv =
      whitneyDesc (rangeInclusion P hr) (rangeInclusion (𝟙 E - P) hs) := (rfl)

/-- The compression of an endomorphism `T` of `E` to the range core of `P`: the inclusion, then
`T`, then the corestriction. When `T` commutes with an idempotent `P`, it is the restriction of `T`
to the range of `P` (`restrictRange_rangeInclusion`). -/
noncomputable def restrictRange (T : E ⟶ E) : range P hr ⟶ range P hr :=
  rangeInclusion P hr ≫ T ≫ rangeRestrict P hr

theorem restrictRange_def (T : E ⟶ E) :
    restrictRange hr T = rangeInclusion P hr ≫ T ≫ rangeRestrict P hr := (rfl)

/-- An endomorphism `T` that commutes with an idempotent `P` maps the range core of `P` to itself,
by `restrictRange hr T`. -/
@[reassoc]
theorem restrictRange_rangeInclusion (hP : P ≫ P = P) {T : E ⟶ E} (hT : T ≫ P = P ≫ T) :
    restrictRange hr T ≫ rangeInclusion P hr = rangeInclusion P hr ≫ T := by
  rw [restrictRange_def, Category.assoc, Category.assoc, rangeRestrict_rangeInclusion, hT,
    rangeInclusion_comp_of_comp_self_assoc hr hP]

/-- For an endomorphism `T` that commutes with an idempotent `P`, the corestriction to the range
core of `P` takes `T` to `restrictRange hr T`. -/
@[reassoc]
theorem rangeRestrict_restrictRange (hP : P ≫ P = P) {T : E ⟶ E} (hT : T ≫ P = P ≫ T) :
    rangeRestrict P hr ≫ restrictRange hr T = T ≫ rangeRestrict P hr := by
  rw [restrictRange_def, rangeRestrict_rangeInclusion_assoc, ← Category.assoc, ← hT,
    Category.assoc, comp_rangeRestrict_of_comp_self hr hP]

/-- The identity restricts to the identity of the range core of an idempotent. -/
@[simp]
theorem restrictRange_id (hP : P ≫ P = P) : restrictRange hr (𝟙 E) = 𝟙 _ := by
  rw [restrictRange_def, Category.id_comp, rangeInclusion_rangeRestrict_of_comp_self hr hP]

/-- Restriction to the range core of an idempotent `P` takes `T ≫ S` to the composite of the
restrictions of `T` and `S`, when `T` commutes with `P`. -/
theorem restrictRange_comp (hP : P ≫ P = P) {T : E ⟶ E} (hT : T ≫ P = P ≫ T) (S : E ⟶ E) :
    restrictRange hr (T ≫ S) = restrictRange hr T ≫ restrictRange hr S := by
  rw [restrictRange_def hr (T ≫ S), restrictRange_def hr S,
    ← Category.assoc (restrictRange hr T), restrictRange_rangeInclusion hr hP hT, Category.assoc,
    Category.assoc]

/-- An idempotent `P` restricts to the identity of its range core. -/
@[simp]
theorem restrictRange_self (hP : P ≫ P = P) : restrictRange hr P = 𝟙 _ := by
  rw [restrictRange_def, rangeInclusion_comp_of_comp_self_assoc hr hP,
    rangeInclusion_rangeRestrict_of_comp_self hr hP]

/-- An idempotent `P` restricts to zero on the range core of `𝟙 E - P`. -/
@[simp]
theorem restrictRange_one_sub (hP : P ≫ P = P) : restrictRange hs P = 0 := by
  rw [restrictRange_def, rangeInclusion_one_sub_comp_of_comp_self_assoc hs hP, Limits.zero_comp]

/-- The splitting `rangeWhitneySumIso` takes an endomorphism `T` that commutes with an idempotent
`P` to the `whitneyMap` of its restrictions to the range cores of `P` and of `𝟙 E - P`. -/
@[reassoc]
theorem rangeWhitneySumIso_hom_comp_whitneyMap (hP : P ≫ P = P) {T : E ⟶ E}
    (hT : T ≫ P = P ≫ T) :
    (rangeWhitneySumIso hr hs hP).hom ≫ whitneyMap (restrictRange hr T) (restrictRange hs T) =
      T ≫ (rangeWhitneySumIso hr hs hP).hom := by
  have hT' : T ≫ (𝟙 E - P) = (𝟙 E - P) ≫ T := by
    rw [Preadditive.comp_sub, Preadditive.sub_comp, hT, Category.comp_id, Category.id_comp]
  rw [rangeWhitneySumIso_hom, whitneyMap_def, comp_whitneyLift, comp_whitneyLift,
    whitneyLift_fst_assoc, whitneyLift_snd_assoc, rangeRestrict_restrictRange hr hP hT,
    rangeRestrict_restrictRange hs (Idempotents.idem_of_id_sub_idem P hP) hT']

/-- Through the splitting `rangeWhitneySumIso`, an endomorphism `T` that commutes with an
idempotent `P` is the block-diagonal map `whitneyMap` of its restrictions to the range cores of
`P` and of `𝟙 E - P`. -/
theorem rangeWhitneySumIso_inv_comp_comp_hom (hP : P ≫ P = P) {T : E ⟶ E}
    (hT : T ≫ P = P ≫ T) :
    (rangeWhitneySumIso hr hs hP).inv ≫ T ≫ (rangeWhitneySumIso hr hs hP).hom =
      whitneyMap (restrictRange hr T) (restrictRange hs T) := by
  rw [Iso.inv_comp_eq, rangeWhitneySumIso_hom_comp_whitneyMap hr hs hP hT]

/-- Through the splitting `rangeWhitneySumIso`, the idempotent `P` is the identity on the range
core of `P` and zero on that of `𝟙 E - P`. -/
theorem rangeWhitneySumIso_inv_comp_self_comp_hom (hP : P ≫ P = P) :
    (rangeWhitneySumIso hr hs hP).inv ≫ P ≫ (rangeWhitneySumIso hr hs hP).hom =
      whitneyMap (𝟙 _) 0 := by
  rw [rangeWhitneySumIso_inv_comp_comp_hom hr hs hP rfl, restrictRange_self hr hP,
    restrictRange_one_sub hs hP]

end Splitting

end TauCeti.FiniteRankBundleCore

end
