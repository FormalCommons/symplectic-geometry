/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.HomotopyInvariance
public import TauCeti.Topology.Category.TopPair.ContinuousLinearEquiv
public import TauCeti.Topology.Homotopy.Contractible
public import TauCeti.Topology.VectorBundle.EulerClass
public import TauCeti.Topology.VectorBundle.Trivialization
import SymplecticGeometry.Topology.Category.TopPair

/-!
# Maps into a Thom pair over a contractible trivializing set

Let `E → B` be a real vector bundle with model fibre `F`, `e` a linear trivialization of it, and
`φ : Q ⟶ (E, E₀)` a map of topological pairs into the Thom pair whose base points lie in the base
set of `e`. Reading `φ` in `e` and carrying its fibre coordinate back into a fixed fibre `E_b`
gives a map of pairs `Q ⟶ (E_b, E_b ∖ {0})`,
`Bundle.Trivialization.fiberCoordPairMap`, `q ↦ e.symm b (e (φ q)).2`.

When the base points of `φ` lie in a contractible subset `U` of the base set which contains `b`,
a contraction of `U` onto `b` moves the base point of `φ q` to `b` while keeping its coordinate
in `e` fixed. This is a homotopy of maps of pairs from `φ` to the fibre coordinate followed by the
inclusion `TauCeti.fiberThomPairMap F E b` of the fibre, so `φ` pulls classes of the Thom pair
back through the fibre over `b`. Carrying that fibre to the model pair `(F, F ∖ {0})` along `e`
at `b`, the pullback along `φ` becomes the pullback along the map of pairs `q ↦ (e (φ q)).2`.

## Main results

* `Bundle.Trivialization.fiberCoordPairMap`: the fibre coordinate of a map into the Thom pair,
  read in a linear trivialization and carried into the fibre over `b`.
* `Bundle.Trivialization.coordPairMap`: the coordinate `q ↦ (e (φ q)).2` of `φ` in the model
  fibre, a map of pairs `Q ⟶ (F, F ∖ {0})`.
* `Bundle.Trivialization.fiberCoordPairMap_comp_complZeroPairIso_hom`: carried back to the model
  fibre `F`, the fibre coordinate is `Bundle.Trivialization.coordPairMap`.
* `Bundle.Trivialization.homotopic_fiberCoordPairMap_comp_fiberThomPairMap`: over a
  contractible subset of the base set, `φ` is homotopic, as a map of pairs, to its fibre
  coordinate followed by the inclusion of the fibre.
* `TauCeti.singularCohomologyMap_eq_singularCohomologyMap_fiberCoordPairMap`: hence `φ` pulls
  every class of the Thom pair back as its restriction to the fibre over `b`, pulled back along
  the fibre coordinate.
* `TauCeti.singularCohomologyMap_eq_singularCohomologyMap_complZeroPairIso_inv`: carried to the
  model pair `(F, F ∖ {0})` along `e` at `b`, that pullback is the pullback along the map of pairs
  `q ↦ (e (φ q)).2`.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10 (the Thom pair of a vector bundle and its restriction to the fibres).
* A. Hatcher, *Algebraic Topology*, Cambridge University Press (2002), §3.1 (homotopy invariance
  of relative cohomology).
-/

public section

noncomputable section

open Bundle CategoryTheory Set

universe w

namespace Bundle.Trivialization

open TauCeti

section

variable {B : Type w} [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type w} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
  (e : Trivialization F (π F E)) [e.IsLinear ℝ] {b : B} (hb : b ∈ e.baseSet)
  {Q : TopPair.{w}} (φ : Q ⟶ thomPair F E)
  (hφ : ∀ q, (TopPair.Hom.fst φ q).proj ∈ e.baseSet)

/-- The fibre coordinate of a map of pairs `φ : Q ⟶ (E, E₀)` whose base points lie in the base
set of a linear trivialization `e`, read in `e` and carried into the fibre over a point `b` of the
base set: the map of pairs `Q ⟶ (E_b, E_b ∖ {0})`, `q ↦ e.symm b (e (φ q)).2`. -/
def fiberCoordPairMap : Q ⟶ TopPair.ofSubset (X := TopCat.of (E b)) ({0}ᶜ : Set (E b)) :=
  (TopPair.isoOfSubsetRange Q).hom ≫ TopPair.ofSubsetMap
    (TopCat.ofHom ⟨fun q ↦ e.symm b (e (TopPair.Hom.fst φ q)).2,
      (e.continuousLinearEquivAt ℝ b hb).symm.continuous.comp
        (e.continuousOn.comp_continuous (TopPair.Hom.fst φ).hom.continuous
          fun q ↦ e.mem_source.2 (hφ q)).snd⟩)
    fun q hq ↦ (e.symm_apply_ne_zero_iff ℝ hb).2 <| (e.snd_apply_ne_zero_iff ℝ (hφ q)).2 <|
      mem_zeroSectionCompl.1 (TopPair.mapsTo_range_map_of_hom φ hq)

theorem fiberCoordPairMap_def :
    e.fiberCoordPairMap hb φ hφ = (TopPair.isoOfSubsetRange Q).hom ≫ TopPair.ofSubsetMap
      (TopCat.ofHom ⟨fun q ↦ e.symm b (e (TopPair.Hom.fst φ q)).2,
        (e.continuousLinearEquivAt ℝ b hb).symm.continuous.comp
          (e.continuousOn.comp_continuous (TopPair.Hom.fst φ).hom.continuous
            fun q ↦ e.mem_source.2 (hφ q)).snd⟩)
      fun q hq ↦ (e.symm_apply_ne_zero_iff ℝ hb).2 <| (e.snd_apply_ne_zero_iff ℝ (hφ q)).2 <|
        mem_zeroSectionCompl.1 (TopPair.mapsTo_range_map_of_hom φ hq) :=
  (rfl)

@[simp]
theorem fiberCoordPairMap_fst_apply (q : Q.fst) :
    TopPair.Hom.fst (e.fiberCoordPairMap hb φ hφ) q = e.symm b (e (TopPair.Hom.fst φ q)).2 := by
  rw [fiberCoordPairMap_def, TopPair.Hom.fst_comp, TopCat.comp_app,
    TopPair.isoOfSubsetRange_hom_fst_apply]
  exact TopPair.ofSubsetMap_fst_apply _ _ _

/-- Over a contractible subset `U` of the base set of a linear trivialization `e` and a point
`b ∈ U`, a map of pairs `φ : Q ⟶ (E, E₀)` whose base points lie in `U` is homotopic, as a map of
pairs, to its fibre coordinate `q ↦ e.symm b (e (φ q)).2` followed by the inclusion
`(E_b, E_b ∖ {0}) ⟶ (E, E₀)` of the fibre over `b`. -/
theorem homotopic_fiberCoordPairMap_comp_fiberThomPairMap {U : Set B} [ContractibleSpace U]
    (hU : U ⊆ e.baseSet) (hbU : b ∈ U) (hφU : ∀ q, (TopPair.Hom.fst φ q).proj ∈ U) :
    TopPair.Homotopic φ
      (e.fiberCoordPairMap (hU hbU) φ (fun q ↦ hU (hφU q)) ≫ fiberThomPairMap F E b) := by
  set f := (TopPair.Hom.fst φ).hom
  let p : C(Q.fst, U) := ⟨fun q ↦ ⟨(f q).proj, hφU q⟩,
    ((FiberBundle.continuous_proj F E).comp f.continuous).subtype_mk _⟩
  let G := Classical.choice (ContinuousMap.homotopic_of_contractibleSpace p
    (ContinuousMap.const _ ⟨b, hbU⟩))
  have hG (x : unitInterval × Q.fst) : (G x : B) ∈ e.baseSet := hU (G x).property
  have hcont : Continuous fun x : unitInterval × Q.fst ↦ (e (f x.2)).2 :=
    (e.continuousOn.comp_continuous (f.continuous.comp continuous_snd)
      fun x ↦ e.mem_source.2 (hU (hφU x.2))).snd
  refine TopPair.homotopic_of_homotopy_fst
    { toFun x := TotalSpace.mk' F (G x : B) (e.symm (G x) (e (f x.2)).2)
      continuous_toFun := e.continuousOn_symm.comp_continuous
        ((continuous_subtypeVal.comp G.continuous).prodMk hcont) fun x ↦ ⟨hG x, trivial⟩
      map_zero_left q := ?_
      map_one_left q := ?_ } ?_
  · rw [G.apply_zero q]
    exact (congrArg (TotalSpace.mk' F (f q).proj) (e.symm_proj_apply (f q) (hU (hφU q)))).trans
      (TotalSpace.eta _)
  · rw [G.apply_one q, TopPair.Hom.fst_comp, TopCat.comp_app]
    exact ((fiberThomPairMap_fst_apply F E b _).trans
      (congrArg (TotalSpace.mk b) (e.fiberCoordPairMap_fst_apply _ φ _ q))).symm
  · intro t x hx
    exact mem_zeroSectionCompl.2 <| (e.symm_apply_ne_zero_iff ℝ (hG _)).2 <|
      (e.snd_apply_ne_zero_iff ℝ (hU (hφU x))).2 <|
        mem_zeroSectionCompl.1 (TopPair.mapsTo_range_map_of_hom φ hx)

end

section

variable {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type w} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
  (e : Trivialization F (π F E)) [e.IsLinear ℝ] {b : B} (hb : b ∈ e.baseSet)
  {Q : TopPair.{w}} (φ : Q ⟶ thomPair F E)
  (hφ : ∀ q, (TopPair.Hom.fst φ q).proj ∈ e.baseSet)

/-- The coordinate in the model fibre of a map of pairs `φ : Q ⟶ (E, E₀)` whose base points lie
in the base set of a linear trivialization `e`: the map of pairs `Q ⟶ (F, F ∖ {0})`,
`q ↦ (e (φ q)).2`. -/
def coordPairMap : Q ⟶ TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F) :=
  (TopPair.isoOfSubsetRange Q).hom ≫ TopPair.ofSubsetMap
    (TopCat.ofHom ⟨fun q ↦ (e (TopPair.Hom.fst φ q)).2,
      (e.continuousOn.comp_continuous (TopPair.Hom.fst φ).hom.continuous
        fun q ↦ e.mem_source.2 (hφ q)).snd⟩)
    fun q hq ↦ (e.snd_apply_ne_zero_iff ℝ (hφ q)).2 <|
      mem_zeroSectionCompl.1 (TopPair.mapsTo_range_map_of_hom φ hq)

omit [∀ b, TopologicalSpace (E b)] [FiberBundle F E] in
theorem coordPairMap_def :
    e.coordPairMap φ hφ = (TopPair.isoOfSubsetRange Q).hom ≫ TopPair.ofSubsetMap
      (TopCat.ofHom ⟨fun q ↦ (e (TopPair.Hom.fst φ q)).2,
        (e.continuousOn.comp_continuous (TopPair.Hom.fst φ).hom.continuous
          fun q ↦ e.mem_source.2 (hφ q)).snd⟩)
      fun q hq ↦ (e.snd_apply_ne_zero_iff ℝ (hφ q)).2 <|
        mem_zeroSectionCompl.1 (TopPair.mapsTo_range_map_of_hom φ hq) :=
  (rfl)

omit [∀ b, TopologicalSpace (E b)] [FiberBundle F E] in
@[simp]
theorem coordPairMap_fst_apply (q : Q.fst) :
    TopPair.Hom.fst (e.coordPairMap φ hφ) q = (e (TopPair.Hom.fst φ q)).2 := by
  rw [coordPairMap_def, TopPair.Hom.fst_comp, TopCat.comp_app,
    TopPair.isoOfSubsetRange_hom_fst_apply]
  exact TopPair.ofSubsetMap_fst_apply _ _ _

/-- Read back in `F` through the isomorphism `E_b ≃L[ℝ] F` of `e` at `b`, the fibre coordinate of
`φ` is its coordinate `q ↦ (e (φ q)).2` in the model fibre. -/
theorem fiberCoordPairMap_comp_complZeroPairIso_hom :
    e.fiberCoordPairMap hb φ hφ ≫ (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.hom =
      e.coordPairMap φ hφ := by
  rw [fiberCoordPairMap_def, coordPairMap_def, Category.assoc,
    ContinuousLinearEquiv.complZeroPairIso_hom]
  exact congrArg _ (TopPair.ofSubsetMap_comp_ofSubsetMap_of_comp_eq _ _ _
    (ConcreteCategory.hom_ext _ _ fun _ ↦ (e.continuousLinearEquivAt ℝ b hb).apply_symm_apply _))

end

end Bundle.Trivialization

namespace TauCeti

open Bundle

variable {C : Type*} [Category C] [Limits.HasCoproducts.{w} C] [Abelian C] {R : C}
  {k : Type*} [Ring k] [Linear k C] {M : C}

section

variable {B : Type w} [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type w} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]

/-- Let `e` be a linear trivialization of a real vector bundle `E → B`, `U` a contractible subset
of its base set and `b ∈ U`. A map of pairs `φ : Q ⟶ (E, E₀)` whose base points lie in `U` pulls
every class `u` of the Thom pair back as the restriction of `u` to the fibre over `b`, pulled back
along the fibre coordinate `q ↦ e.symm b (e (φ q)).2` of `φ`. -/
theorem singularCohomologyMap_eq_singularCohomologyMap_fiberCoordPairMap
    (e : Trivialization F (π F E)) [e.IsLinear ℝ] {U : Set B} [ContractibleSpace U]
    (hU : U ⊆ e.baseSet) {b : B} (hbU : b ∈ U) {Q : TopPair.{w}} (φ : Q ⟶ thomPair F E)
    (hφU : ∀ q, (TopPair.Hom.fst φ q).proj ∈ U) {n : ℕ}
    (u : (thomPair F E).singularCohomology R k M n) :
    TopPair.singularCohomologyMap φ n u =
      TopPair.singularCohomologyMap (e.fiberCoordPairMap (hU hbU) φ fun q ↦ hU (hφU q)) n
        (TopPair.singularCohomologyMap (fiberThomPairMap F E b) n u) := by
  rw [← TopPair.singularCohomologyMap_comp_apply,
    (e.homotopic_fiberCoordPairMap_comp_fiberThomPairMap φ hU hbU
      hφU).some.congr_singularCohomologyMap]

end

section

variable {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type w} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]

/-- Let `e` be a linear trivialization of a real vector bundle `E → B` with model fibre `F`, `U` a
contractible subset of its base set and `b ∈ U`, and write `ℓ : E_b ≃L[ℝ] F` for `e` at `b`. A
map of pairs `φ : Q ⟶ (E, E₀)` whose base points lie in `U` pulls every class `u` of the Thom
pair back as the restriction of `u` to the fibre over `b`, carried to the model pair
`(F, F ∖ {0})` along `ℓ`, and pulled back along the map of pairs `q ↦ (e (φ q)).2`. -/
theorem singularCohomologyMap_eq_singularCohomologyMap_complZeroPairIso_inv
    (e : Trivialization F (π F E)) [e.IsLinear ℝ] {U : Set B} [ContractibleSpace U]
    (hU : U ⊆ e.baseSet) {b : B} (hbU : b ∈ U) {Q : TopPair.{w}} (φ : Q ⟶ thomPair F E)
    (hφU : ∀ q, (TopPair.Hom.fst φ q).proj ∈ U) {n : ℕ}
    (u : (thomPair F E).singularCohomology R k M n) :
    TopPair.singularCohomologyMap φ n u =
      TopPair.singularCohomologyMap (e.coordPairMap φ fun q ↦ hU (hφU q)) n
        (TopPair.singularCohomologyMap
          (e.continuousLinearEquivAt ℝ b (hU hbU)).complZeroPairIso.inv n
          (TopPair.singularCohomologyMap (fiberThomPairMap F E b) n u)) := by
  rw [singularCohomologyMap_eq_singularCohomologyMap_fiberCoordPairMap e hU hbU φ hφU,
    ← e.fiberCoordPairMap_comp_complZeroPairIso_hom, TopPair.singularCohomologyMap_comp_apply,
    ← TopPair.singularCohomologyMap_comp_apply _ (Iso.inv _), Iso.hom_inv_id,
    TopPair.singularCohomologyMap_id, ConcreteCategory.id_apply]

end

end TauCeti

end
