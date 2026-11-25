/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Analysis.Complex.RadialProjection
public import SymplecticGeometry.Topology.VectorBundle.FiniteRank.Glue
public import SymplecticGeometry.Topology.VectorBundle.FiniteRank.OfBundle
public import SymplecticGeometry.Topology.VectorBundle.ProjectiveBundle.Tautological
public import TauCeti.Topology.Algebra.Projectivization

/-!
# The clutching construction over `X × ℂP¹`

The projective line `ℙ ℂ (Fin 2 → ℂ)` is covered by two open discs: the inner disc
`ProjectiveLine.innerDisc`, the points `[z : 1]` with `|z| < 2`, and the outer disc
`ProjectiveLine.outerDisc`, the points `[1 : w]` with `|w| < 2`, that is `|z| > 1/2` together with
`∞ = [1 : 0]`. They meet in the annulus `1/2 < |z| < 2`, which `ProjectiveLine.annulusToCircle`
retracts radially onto the unit circle, `[z : 1] ↦ z / |z|`.

For a finite-rank core `E` over `X` and an automorphism `f` of the pullback of `E` to `X × Circle`
along the projection, `E.clutching f` is the core over `X × ℙ ℂ (Fin 2 → ℂ)` obtained by gluing
the pullback of `E` along `Prod.fst` to itself over the product of `X` with the annulus by `f`
composed with the radial retraction (`clutchingMap`): a vector `v` over `(x, [z : 1])` in the
copy over the outer disc is the vector `f_{(x, z / |z|)} v` in the copy over the inner disc. This
is the clutching construction of [Hatcher2017, §2.1]. It uses no K-theory, and the fibres may be
over any nontrivially normed field.

## Main definitions and results

* `SymplecticGeometry.ProjectiveLine.innerDisc`, `SymplecticGeometry.ProjectiveLine.outerDisc`:
  the two open discs, open (`isOpen_innerDisc`, `isOpen_outerDisc`) and covering the projective
  line (`innerDisc_union_outerDisc`).
* `SymplecticGeometry.ProjectiveLine.annulusCoord`: the affine coordinate `z` of the points
  `[z : 1]` of their intersection, the annulus, as a nonzero complex number.
* `SymplecticGeometry.ProjectiveLine.annulusToCircle`: the radial retraction of the annulus onto
  `Circle`, `[z : 1] ↦ z / |z|` (`coe_annulusToCircle_apply`).
* `TauCeti.FiniteRankBundleCore.clutchingMap`: the map from the product of `X` with the annulus to
  `X × Circle`, and `TauCeti.FiniteRankBundleCore.clutchingAut E f`, the pullback of `f` along it.
* `TauCeti.FiniteRankBundleCore.clutching`: the clutched core, of rank `E.rank`
  (`rank_clutching`).
* `TauCeti.FiniteRankBundleCore.coordChange_clutching`: its transitions, through the gluing cocycle.
* `TauCeti.FiniteRankBundleCore.clutchingRestrictIso`: over `X × innerDisc` (`true`) and over
  `X × outerDisc` (`false`), the clutched core is isomorphic to the pullback of `E`.
* `TauCeti.FiniteRankBundleCore.coordChange_clutching_of_notMem_of_mem` and
  `coordChange_clutching_of_mem_of_notMem`: over the annulus, the transitions of the clutched
  core between a chart over the outer disc and one over the inner disc are the fibre maps of `f`
  and of its inverse at the radial retraction of the point.
* `TauCeti.FiniteRankBundleCore.clutchingOneIso` and `clutching_one`: the clutching by the
  identity is isomorphic to the pullback of `E` along `Prod.fst`.
* `TauCeti.FiniteRankBundleCore.circleZPowIso X n`: the automorphism of the trivial line over
  `X × Circle` that multiplies the fibre over `(x, u)` by `u ^ n`.
* `Projectivization.tautologicalCore 𝕜 V`: the tautological line `Projectivization.Tautological`
  as a finite-rank core of rank one, through
  `TauCeti.FiniteRankBundleCore.ofBundleOfFinrankEq`.
* `SymplecticGeometry.ProjectiveLine.innerSection` and `outerSection`: nowhere vanishing vectors
  `(z, 1) / max 1 |z|` and `(1, w) / max 1 |w|` of the lines `[z : 1]` and `[1 : w]`; on the
  annulus the first is the second times `z / |z|` (`innerSection_eq_smul_outerSection`).
* `TauCeti.FiniteRankBundleCore.clutchingZIso` and `clutching_z`: the pullback of the tautological
  line of `ℙ ℂ (Fin 2 → ℂ)` to `X × ℙ ℂ (Fin 2 → ℂ)` is the clutching of the trivial line by
  `circleZPowIso X (-1)`, that is by `u ↦ u⁻¹`.

The clutched core is `TauCeti.FiniteRankBundleCore.glue`, applied to the cover of
`X × ℙ ℂ (Fin 2 → ℂ)` by the preimages of the two discs. The clutching by the identity glues by
the identity (`clutchingAut_refl`), so it is the gluing by the identity (`clutching_refl`), and
`clutchingOneIso` is this equality followed by `TauCeti.FiniteRankBundleCore.glueReflIso`.

For `clutchingZIso`, a coordinate `a` of the clutched line over a point of `X × innerDisc` goes to
`a • innerSection`, and over the rest to `a • outerSection`. These agree with the gluing because
the inner section is the outer one times `z / |z|` on the annulus; the sections are normalized by
`max 1 |z|` and `max 1 |w|` so that this ratio is exactly the radial retraction. Continuity on
total spaces is checked in the charts of the clutched line, where the map is a coordinate times
one of the two sections, and in the subspace topology of the tautological line
(`Projectivization.continuous_totalSpace_tautological_iff`); the isomorphism of cores is then
`TauCeti.FiniteRankBundleCore.isoOfContinuousEquiv`.

## References

* [A. Hatcher, *Vector Bundles and K-Theory*][Hatcher2017], §2.1 (clutching functions over
  `X × S²`).
-/

public section

noncomputable section

open Set CategoryTheory Projectivization Bundle Module Topology

open scoped LinearAlgebra.Projectivization

namespace SymplecticGeometry.ProjectiveLine

/-! ### The two discs of the projective line and their annulus -/

/-- The inner disc of the projective line: the points `[z : 1]` with `|z| < 2`. -/
def innerDisc : Set (ℙ ℂ (Fin 2 → ℂ)) :=
  affineOpen 1 ∩ affineChart 1 ⁻¹' {z | ‖z 0‖ < 2}

/-- The outer disc of the projective line: the points `[1 : w]` with `|w| < 2`, that is the points
`[z : 1]` with `|z| > 1/2` together with `∞ = [1 : 0]`. -/
def outerDisc : Set (ℙ ℂ (Fin 2 → ℂ)) :=
  affineOpen 0 ∩ affineChart 0 ⁻¹' {z | ‖z 0‖ < 2}

theorem innerDisc_def : innerDisc = affineOpen 1 ∩ affineChart 1 ⁻¹' {z | ‖z 0‖ < 2} :=
  (rfl)

theorem outerDisc_def : outerDisc = affineOpen 0 ∩ affineChart 0 ⁻¹' {z | ‖z 0‖ < 2} :=
  (rfl)

theorem mem_innerDisc_iff {p : ℙ ℂ (Fin 2 → ℂ)} :
    p ∈ innerDisc ↔ p ∈ affineOpen 1 ∧ ‖affineChart 1 p 0‖ < 2 :=
  Iff.rfl

theorem mem_outerDisc_iff {p : ℙ ℂ (Fin 2 → ℂ)} :
    p ∈ outerDisc ↔ p ∈ affineOpen 0 ∧ ‖affineChart 0 p 0‖ < 2 :=
  Iff.rfl

@[simp]
theorem mk_mem_innerDisc_iff (v : Fin 2 → ℂ) (hv : v ≠ 0) :
    mk ℂ v hv ∈ innerDisc ↔ v 1 ≠ 0 ∧ ‖v 0 / v 1‖ < 2 := by
  simp [mem_innerDisc_iff]

@[simp]
theorem mk_mem_outerDisc_iff (v : Fin 2 → ℂ) (hv : v ≠ 0) :
    mk ℂ v hv ∈ outerDisc ↔ v 0 ≠ 0 ∧ ‖v 1 / v 0‖ < 2 := by
  simp [mem_outerDisc_iff]

theorem isOpen_innerDisc : IsOpen innerDisc := by
  rw [innerDisc_def]
  simpa using (affineOpenPartialHomeomorph (K := ℂ) (n := 1) 1).isOpen_inter_preimage
    (isOpen_lt (continuous_norm.comp (continuous_apply 0)) continuous_const)

theorem isOpen_outerDisc : IsOpen outerDisc := by
  rw [outerDisc_def]
  simpa using (affineOpenPartialHomeomorph (K := ℂ) (n := 1) 0).isOpen_inter_preimage
    (isOpen_lt (continuous_norm.comp (continuous_apply 0)) continuous_const)

/-- The inner and outer discs cover the projective line. -/
theorem innerDisc_union_outerDisc : innerDisc ∪ outerDisc = univ := by
  refine eq_univ_of_forall fun p ↦ ?_
  induction p using Projectivization.ind with | h v hv =>
  simp only [mem_union, mk_mem_innerDisc_iff, mk_mem_outerDisc_iff]
  by_cases h1 : v 1 = 0
  · have h0 : v 0 ≠ 0 := fun h0 ↦ hv (funext fun i ↦ by fin_cases i <;> assumption)
    exact Or.inr ⟨h0, by simp [h1]⟩
  by_cases h : ‖v 0 / v 1‖ < 2
  · exact Or.inl ⟨h1, h⟩
  have h0 : v 0 ≠ 0 := fun h0 ↦ h (by simp [h0])
  refine Or.inr ⟨h0, ?_⟩
  rw [not_lt] at h
  have h' : ‖v 0 / v 1‖⁻¹ ≤ 2⁻¹ := inv_anti₀ (by norm_num) h
  rw [← inv_div, norm_inv]
  linarith

/-- On the annulus, the affine coordinate `z` of a point `[z : 1]` is nonzero. -/
theorem affineChart_one_ne_zero_of_mem {p : ℙ ℂ (Fin 2 → ℂ)} (hp : p ∈ innerDisc ∩ outerDisc) :
    affineChart 1 p 0 ≠ 0 := by
  induction p using Projectivization.ind with | h v hv =>
  simp only [mem_inter_iff, mk_mem_innerDisc_iff, mk_mem_outerDisc_iff] at hp
  simpa using div_ne_zero hp.2.1 hp.1.1

/-- The affine coordinate `z` of the points `[z : 1]` of the annulus `innerDisc ∩ outerDisc`, as a
nonzero complex number. -/
def annulusCoord : C(↥(innerDisc ∩ outerDisc), ({0}ᶜ : Set ℂ)) :=
  ⟨fun p ↦ ⟨affineChart 1 p.val 0, affineChart_one_ne_zero_of_mem p.property⟩,
    (continuousOn_iff_continuous_domRestrict.1 ((continuous_apply 0).comp_continuousOn
      ((continuousOn_affineChart (K := ℂ) 1).mono
        fun _ (hp : _ ∈ innerDisc ∩ outerDisc) ↦ hp.1.1))).subtype_mk _⟩

@[simp]
theorem coe_annulusCoord_apply (p : ↥(innerDisc ∩ outerDisc)) :
    (annulusCoord p : ℂ) = affineChart 1 p.val 0 :=
  (rfl)

/-- The radial retraction of the annulus `innerDisc ∩ outerDisc` onto the unit circle,
`[z : 1] ↦ z / |z|`. -/
def annulusToCircle : C(↥(innerDisc ∩ outerDisc), Circle) :=
  Circle.radialProjection.comp annulusCoord

theorem annulusToCircle_def : annulusToCircle = Circle.radialProjection.comp annulusCoord :=
  (rfl)

/-- The radial retraction of the annulus sends `[z : 1]` to `z / |z|`. -/
@[simp]
theorem coe_annulusToCircle_apply (p : ↥(innerDisc ∩ outerDisc)) :
    (annulusToCircle p : ℂ) = ‖affineChart 1 p.val 0‖⁻¹ • affineChart 1 p.val 0 := by
  simp [annulusToCircle_def]

end SymplecticGeometry.ProjectiveLine

/-! ### The clutched core -/

namespace TauCeti.FiniteRankBundleCore

open SymplecticGeometry.ProjectiveLine

variable {𝕜 X : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace X]

variable (X) in
/-- The map from the product of `X` with the annulus of the projective line to `X × Circle`:
the identity on `X`, and the radial retraction `annulusToCircle` on the annulus. -/
def clutchingMap :
    C(↥(Prod.snd ⁻¹' innerDisc ∩ Prod.snd ⁻¹' outerDisc : Set (X × ℙ ℂ (Fin 2 → ℂ))),
      X × Circle) :=
  ⟨fun w ↦ (w.val.1, annulusToCircle ⟨w.val.2, w.property⟩),
    (continuous_fst.comp continuous_subtypeVal).prodMk
      (annulusToCircle.continuous.comp
        ((continuous_snd.comp continuous_subtypeVal).subtype_mk _))⟩

@[simp]
theorem clutchingMap_apply
    (w : ↥(Prod.snd ⁻¹' innerDisc ∩ Prod.snd ⁻¹' outerDisc : Set (X × ℙ ℂ (Fin 2 → ℂ)))) :
    clutchingMap X w = (w.val.1, annulusToCircle ⟨w.val.2, w.property⟩) :=
  (rfl)

/-- The automorphism of the pullback of `E` to the product of `X` with the annulus by which the
clutching by `f` glues: the pullback of `f` along `clutchingMap`. -/
def clutchingAut (E : FiniteRankBundleCore 𝕜 X)
    (f : E.pullback (ContinuousMap.fst : C(X × Circle, X)) ≅
      E.pullback (ContinuousMap.fst : C(X × Circle, X))) :
    (E.pullback (ContinuousMap.fst : C(X × ℙ ℂ (Fin 2 → ℂ), X))).pullback
        (ContinuousMap.subtypeVal (Prod.snd ⁻¹' innerDisc ∩ Prod.snd ⁻¹' outerDisc)) ≅
      (E.pullback (ContinuousMap.fst : C(X × ℙ ℂ (Fin 2 → ℂ), X))).pullback
        (ContinuousMap.subtypeVal (Prod.snd ⁻¹' innerDisc ∩ Prod.snd ⁻¹' outerDisc)) :=
  -- Both iterated pullbacks are the pullback of `E` along `w ↦ w.val.1`.
  (pullbackFunctor (clutchingMap X)).mapIso f

@[simp]
theorem fiberMap_clutchingAut_hom (E : FiniteRankBundleCore 𝕜 X)
    (f : E.pullback (ContinuousMap.fst : C(X × Circle, X)) ≅
      E.pullback (ContinuousMap.fst : C(X × Circle, X)))
    (w : ↥(Prod.snd ⁻¹' innerDisc ∩ Prod.snd ⁻¹' outerDisc : Set (X × ℙ ℂ (Fin 2 → ℂ)))) :
    (clutchingAut E f).hom.fiberMap w = f.hom.fiberMap (clutchingMap X w) :=
  fiberMap_pullbackMap f.hom (clutchingMap X) w

@[simp]
theorem fiberMap_clutchingAut_inv (E : FiniteRankBundleCore 𝕜 X)
    (f : E.pullback (ContinuousMap.fst : C(X × Circle, X)) ≅
      E.pullback (ContinuousMap.fst : C(X × Circle, X)))
    (w : ↥(Prod.snd ⁻¹' innerDisc ∩ Prod.snd ⁻¹' outerDisc : Set (X × ℙ ℂ (Fin 2 → ℂ)))) :
    (clutchingAut E f).inv.fiberMap w = f.inv.fiberMap (clutchingMap X w) :=
  fiberMap_pullbackMap f.inv (clutchingMap X) w

/-- **The clutching construction.** For a core `E` over `X` and an automorphism `f` of its pullback
to `X × Circle`, the core over `X × ℙ ℂ (Fin 2 → ℂ)` that is the pullback of `E` along `Prod.fst`
over `X × innerDisc` and over `X × outerDisc`, a vector `v` over a point `(x, [z : 1])` of the
product of `X` with the annulus in the copy over the outer disc being the vector
`f_{(x, z / |z|)} v` in the copy over the inner disc. -/
-- Expose the rank so that the fibre model of the clutched core reduces to that of `E`.
@[expose, implicit_reducible]
def clutching (E : FiniteRankBundleCore 𝕜 X)
    (f : E.pullback (ContinuousMap.fst : C(X × Circle, X)) ≅
      E.pullback (ContinuousMap.fst : C(X × Circle, X))) :
    FiniteRankBundleCore 𝕜 (X × ℙ ℂ (Fin 2 → ℂ)) :=
  (E.pullback ContinuousMap.fst).glue (isOpen_innerDisc.preimage continuous_snd)
    (isOpen_outerDisc.preimage continuous_snd)
    (by rw [← preimage_union, innerDisc_union_outerDisc, preimage_univ]) (clutchingAut E f)

variable (E : FiniteRankBundleCore 𝕜 X)
  (f : E.pullback (ContinuousMap.fst : C(X × Circle, X)) ≅
    E.pullback (ContinuousMap.fst : C(X × Circle, X)))

theorem clutching_def :
    E.clutching f = (E.pullback ContinuousMap.fst).glue
      (isOpen_innerDisc.preimage continuous_snd) (isOpen_outerDisc.preimage continuous_snd)
      (by rw [← preimage_union, innerDisc_union_outerDisc, preimage_univ]) (clutchingAut E f) :=
  (rfl)

@[simp]
theorem rank_clutching : (E.clutching f).rank = E.rank :=
  (rfl)

theorem baseSet_clutching (x : X × ℙ ℂ (Fin 2 → ℂ)) :
    (E.clutching f).core.baseSet x = (E.pullback ContinuousMap.fst).core.baseSet x ∩
      glueSide (Prod.snd ⁻¹' innerDisc) (Prod.snd ⁻¹' outerDisc)
        (glueIndex (Prod.snd ⁻¹' innerDisc) x) :=
  baseSet_glue _ _ _ _ _ x

/-- The transitions of the clutched core: the chart expressions, in the charts of the pullback of
`E`, of the gluing cocycle of `clutchingAut E f` from the side of one chart to that of the other.
-/
theorem coordChange_clutching (x y b : X × ℙ ℂ (Fin 2 → ℂ)) :
    (E.clutching f).core.coordChange x y b =
      (E.pullback ContinuousMap.fst).core.inChartCoordinates (E.pullback ContinuousMap.fst).core
        x y b (glueCocycle (clutchingAut E f) (glueIndex (Prod.snd ⁻¹' innerDisc) x)
          (glueIndex (Prod.snd ⁻¹' innerDisc) y) b) :=
  coordChange_glue _ _ _ _ _ x y b

/-- **The clutched core over each disc.** The restriction of `E.clutching f` to `X × innerDisc`
(for `s = true`) or to `X × outerDisc` (for `s = false`) is isomorphic to that of the pullback of
`E` along `Prod.fst`; over the inner disc the isomorphism is the identity in coordinates, and over
the outer disc it is the fibre map of `f⁻¹` at the radial retraction on the annulus. -/
def clutchingRestrictIso (s : Bool) :
    (E.clutching f).pullback (ContinuousMap.subtypeVal
        (glueSide (Prod.snd ⁻¹' innerDisc) (Prod.snd ⁻¹' outerDisc) s)) ≅
      (E.pullback ContinuousMap.fst).pullback (ContinuousMap.subtypeVal
        (glueSide (Prod.snd ⁻¹' innerDisc) (Prod.snd ⁻¹' outerDisc) s)) :=
  glueRestrictIso _ _ _ _ _ s

/-- Over the inner disc, the isomorphism of the clutched core with the pullback of `E` is the
identity in coordinates. -/
@[simp]
theorem fiberMap_clutchingRestrictIso_true_hom
    (x : ↥(Prod.snd ⁻¹' innerDisc : Set (X × ℙ ℂ (Fin 2 → ℂ)))) :
    (E.clutchingRestrictIso f true).hom.fiberMap x = .id 𝕜 _ :=
  fiberMap_glueRestrictIso_true_hom _ _ _ _ _ x

/-- Over the outer disc, at a point of the annulus, the isomorphism of the clutched core with the
pullback of `E` is the fibre map of `f⁻¹` at the radial retraction of the point. -/
theorem fiberMap_clutchingRestrictIso_false_hom
    {x : ↥(Prod.snd ⁻¹' outerDisc : Set (X × ℙ ℂ (Fin 2 → ℂ)))} (hx : (x.val.2 : _) ∈ innerDisc) :
    (E.clutchingRestrictIso f false).hom.fiberMap x =
      f.inv.fiberMap (clutchingMap X ⟨x, hx, x.property⟩) :=
  (fiberMap_glueRestrictIso_false_hom _ _ _ _ _ hx).trans (fiberMap_clutchingAut_inv E f _)

/-- Over the outer disc, at a point outside the inner disc, the isomorphism of the clutched core
with the pullback of `E` is the identity in coordinates. -/
theorem fiberMap_clutchingRestrictIso_false_hom_of_notMem
    {x : ↥(Prod.snd ⁻¹' outerDisc : Set (X × ℙ ℂ (Fin 2 → ℂ)))} (hx : (x.val.2 : _) ∉ innerDisc) :
    (E.clutchingRestrictIso f false).hom.fiberMap x = .id 𝕜 _ :=
  fiberMap_glueRestrictIso_false_hom_of_notMem _ _ _ _ _ hx

@[simp]
theorem fiberMap_clutchingRestrictIso_true_inv
    (x : ↥(Prod.snd ⁻¹' innerDisc : Set (X × ℙ ℂ (Fin 2 → ℂ)))) :
    (E.clutchingRestrictIso f true).inv.fiberMap x = .id 𝕜 _ :=
  fiberMap_glueRestrictIso_true_inv _ _ _ _ _ x

/-- Over the outer disc, at a point of the annulus, the inverse isomorphism, from the pullback of
`E` to the clutched core, is the fibre map of `f` at the radial retraction of the point. -/
theorem fiberMap_clutchingRestrictIso_false_inv
    {x : ↥(Prod.snd ⁻¹' outerDisc : Set (X × ℙ ℂ (Fin 2 → ℂ)))} (hx : (x.val.2 : _) ∈ innerDisc) :
    (E.clutchingRestrictIso f false).inv.fiberMap x =
      f.hom.fiberMap (clutchingMap X ⟨x, hx, x.property⟩) :=
  (fiberMap_glueRestrictIso_false_inv _ _ _ _ _ hx).trans (fiberMap_clutchingAut_hom E f _)

/-- Over the outer disc, at a point outside the inner disc, the inverse isomorphism, from the
pullback of `E` to the clutched core, is the identity in coordinates. -/
theorem fiberMap_clutchingRestrictIso_false_inv_of_notMem
    {x : ↥(Prod.snd ⁻¹' outerDisc : Set (X × ℙ ℂ (Fin 2 → ℂ)))} (hx : (x.val.2 : _) ∉ innerDisc) :
    (E.clutchingRestrictIso f false).inv.fiberMap x = .id 𝕜 _ :=
  fiberMap_glueRestrictIso_false_inv_of_notMem _ _ _ _ _ hx

/-- From a chart over the outer disc to a chart over the inner disc, at a point `b` of the product
of `X` with the annulus, the transition of the clutched core is the fibre map of `f` at the radial
retraction of `b`, read in the two charts of `E`. -/
theorem coordChange_clutching_of_notMem_of_mem {x y : X × ℙ ℂ (Fin 2 → ℂ)}
    (hx : x.2 ∉ innerDisc) (hy : y.2 ∈ innerDisc)
    {b : X × ℙ ℂ (Fin 2 → ℂ)} (hb : b.2 ∈ innerDisc ∩ outerDisc) :
    (E.clutching f).core.coordChange x y b =
      (E.core.coordChange b.1 y.1 b.1).comp
        ((f.hom.fiberMap (clutchingMap X ⟨b, hb⟩)).comp (E.core.coordChange x.1 b.1 b.1)) := by
  refine (coordChange_glue_of_notMem_of_mem (U := Prod.snd ⁻¹' innerDisc)
    (V := Prod.snd ⁻¹' outerDisc)
    (E.pullback ContinuousMap.fst) _ _ _ (clutchingAut E f) hx hy hb).trans ?_
  simp only [fiberMap_clutchingAut_hom, coordChange_pullback, ContinuousMap.fst_apply]

/-- From a chart over the inner disc to a chart over the outer disc, at a point `b` of the product
of `X` with the annulus, the transition of the clutched core is the fibre map of `f⁻¹` at the
radial retraction of `b`, read in the two charts of `E`. -/
theorem coordChange_clutching_of_mem_of_notMem {x y : X × ℙ ℂ (Fin 2 → ℂ)}
    (hx : x.2 ∈ innerDisc) (hy : y.2 ∉ innerDisc)
    {b : X × ℙ ℂ (Fin 2 → ℂ)} (hb : b.2 ∈ innerDisc ∩ outerDisc) :
    (E.clutching f).core.coordChange x y b =
      (E.core.coordChange b.1 y.1 b.1).comp
        ((f.inv.fiberMap (clutchingMap X ⟨b, hb⟩)).comp (E.core.coordChange x.1 b.1 b.1)) := by
  refine (coordChange_glue_of_mem_of_notMem (U := Prod.snd ⁻¹' innerDisc)
    (V := Prod.snd ⁻¹' outerDisc)
    (E.pullback ContinuousMap.fst) _ _ _ (clutchingAut E f) hx hy hb).trans ?_
  simp only [fiberMap_clutchingAut_inv, coordChange_pullback, ContinuousMap.fst_apply]

/-! ### Clutching by the identity -/

/-- The clutching by the identity glues by the identity. -/
@[simp]
theorem clutchingAut_refl : clutchingAut E (Iso.refl _) = Iso.refl _ :=
  Functor.mapIso_refl _ _

/-- The clutching by the identity is the gluing by the identity. -/
theorem clutching_refl : E.clutching (Iso.refl _) =
    (E.pullback ContinuousMap.fst).glue (isOpen_innerDisc.preimage continuous_snd)
      (isOpen_outerDisc.preimage continuous_snd)
      (by rw [← preimage_union, innerDisc_union_outerDisc, preimage_univ]) (Iso.refl _) := by
  rw [clutching_def, clutchingAut_refl]

/-- **Clutching by the identity.** The clutching of `E` by the identity of its pullback to
`X × Circle` is the pullback of `E` along `Prod.fst`, by the identity in coordinates. -/
def clutchingOneIso : E.clutching (Iso.refl _) ≅ E.pullback ContinuousMap.fst :=
  eqToIso (clutching_refl E) ≪≫ glueReflIso _ _ _ _

@[simp]
theorem fiberMap_clutchingOneIso_hom (x : X × ℙ ℂ (Fin 2 → ℂ)) :
    (E.clutchingOneIso).hom.fiberMap x = .id 𝕜 _ := by
  ext v i
  simp [clutchingOneIso]

@[simp]
theorem fiberMap_clutchingOneIso_inv (x : X × ℙ ℂ (Fin 2 → ℂ)) :
    (E.clutchingOneIso).inv.fiberMap x = .id 𝕜 _ := by
  ext v i
  simp [clutchingOneIso]

/-- **Clutching by the identity.** The clutching of `E` by the identity is isomorphic to the
pullback of `E` along `Prod.fst`. -/
theorem clutching_one : Nonempty (E.clutching (Iso.refl _) ≅ E.pullback ContinuousMap.fst) :=
  ⟨E.clutchingOneIso⟩

/-! ### Clutching by a power of the coordinate -/

variable (X) in
/-- The automorphism of the trivial line over `X × Circle` that multiplies the fibre over `(x, u)`
by `u ^ n`. -/
def circleZPowIso (n : ℤ) :
    (trivial ℂ X 1).pullback (ContinuousMap.fst : C(X × Circle, X)) ≅
      (trivial ℂ X 1).pullback (ContinuousMap.fst : C(X × Circle, X)) :=
  isoOfContinuousEquiv (A := trivial ℂ (X × Circle) 1) (D := trivial ℂ (X × Circle) 1)
    (fun b ↦ (LinearEquiv.smulOfUnit (Circle.toUnits (b.2 ^ n))).toContinuousLinearEquiv)
    (continuous_trivial_iff.2 ⟨FiberBundle.continuous_proj _ _, by
      have hproj : Continuous fun p : (trivial ℂ (X × Circle) 1).core.TotalSpace ↦ p.proj.2 :=
        continuous_snd.comp (FiberBundle.continuous_proj _ _)
      have hsnd := continuous_trivial_snd (𝕜 := ℂ) (B := X × Circle) (n := 1)
      -- Multiplication by a unit is multiplication by its value.
      exact ((continuous_subtypeVal.comp (hproj.zpow n)).smul hsnd).congr fun _ ↦ (rfl)⟩)

@[simp]
theorem fiberMap_circleZPowIso_hom_apply (n : ℤ) (b : X × Circle) (v : Fin 1 → ℂ) :
    (circleZPowIso X n).hom.fiberMap b v = ((b.2 ^ n : Circle) : ℂ) • v :=
  (DFunLike.congr_fun (fiberMap_isoOfContinuousEquiv_hom (A := trivial ℂ (X × Circle) 1)
    (D := trivial ℂ (X × Circle) 1) _ _ b) v).trans
    -- Multiplication by a unit is multiplication by its value.
    (rfl)

@[simp]
theorem fiberMap_circleZPowIso_inv_apply (n : ℤ) (b : X × Circle) (v : Fin 1 → ℂ) :
    (circleZPowIso X n).inv.fiberMap b v = ((b.2 ^ (-n) : Circle) : ℂ) • v :=
  (DFunLike.congr_fun (fiberMap_isoOfContinuousEquiv_inv (A := trivial ℂ (X × Circle) 1)
    (D := trivial ℂ (X × Circle) 1) _ _ b) v).trans
    -- Multiplication by a unit is multiplication by its value.
    (by rw [zpow_neg]; rfl)

end TauCeti.FiniteRankBundleCore

/-! ### The tautological line as a core -/

namespace Projectivization

variable (𝕜 V : Type*) [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [NormedAddCommGroup V]
  [NormedSpace 𝕜 V] [SeparatingDual 𝕜 V]

/-- The tautological line of `ℙ 𝕜 V`, whose fibre over a point is the line itself, as a
finite-rank core of rank one. -/
-- Expose the rank so that the fibre model reduces to `Fin 1 → 𝕜`.
@[expose, implicit_reducible]
def tautologicalCore : TauCeti.FiniteRankBundleCore 𝕜 (ℙ 𝕜 V) :=
  TauCeti.FiniteRankBundleCore.ofBundleOfFinrankEq 𝕜 𝕜 (Tautological 𝕜 V) (finrank_self 𝕜)

theorem tautologicalCore_def : tautologicalCore 𝕜 V =
    TauCeti.FiniteRankBundleCore.ofBundleOfFinrankEq 𝕜 𝕜 (Tautological 𝕜 V) (finrank_self 𝕜) :=
  (rfl)

@[simp]
theorem rank_tautologicalCore : (tautologicalCore 𝕜 V).rank = 1 :=
  (rfl)

end Projectivization

/-! ### Two nonvanishing sections of the tautological line of `ℂP¹` -/

namespace SymplecticGeometry.ProjectiveLine

/-- On the affine open `[z : 1]`, the vector `(z, 1) / max 1 |z|` of the line. -/
def innerSection (p : ℙ ℂ (Fin 2 → ℂ)) : Fin 2 → ℂ :=
  (((max 1 ‖affineChart 1 p 0‖)⁻¹ : ℝ) : ℂ) • ![affineChart 1 p 0, 1]

/-- On the affine open `[1 : w]`, the vector `(1, w) / max 1 |w|` of the line. -/
def outerSection (p : ℙ ℂ (Fin 2 → ℂ)) : Fin 2 → ℂ :=
  (((max 1 ‖affineChart 0 p 0‖)⁻¹ : ℝ) : ℂ) • ![1, affineChart 0 p 0]

theorem innerSection_def (p : ℙ ℂ (Fin 2 → ℂ)) :
    innerSection p = (((max 1 ‖affineChart 1 p 0‖)⁻¹ : ℝ) : ℂ) • ![affineChart 1 p 0, 1] :=
  (rfl)

theorem outerSection_def (p : ℙ ℂ (Fin 2 → ℂ)) :
    outerSection p = (((max 1 ‖affineChart 0 p 0‖)⁻¹ : ℝ) : ℂ) • ![1, affineChart 0 p 0] :=
  (rfl)

theorem innerSection_ne_zero (p : ℙ ℂ (Fin 2 → ℂ)) : innerSection p ≠ 0 := fun h ↦
  (lt_max_of_lt_left one_pos : (0 : ℝ) < max 1 ‖affineChart 1 p 0‖).ne'
    (by simpa [innerSection_def] using congrFun h 1)

theorem outerSection_ne_zero (p : ℙ ℂ (Fin 2 → ℂ)) : outerSection p ≠ 0 := fun h ↦
  (lt_max_of_lt_left one_pos : (0 : ℝ) < max 1 ‖affineChart 0 p 0‖).ne'
    (by simpa [outerSection_def] using congrFun h 0)

theorem innerSection_mem_submodule {p : ℙ ℂ (Fin 2 → ℂ)} (hp : p ∈ affineOpen 1) :
    innerSection p ∈ p.submodule := by
  induction p using Projectivization.ind with | h v hv =>
  rw [mk_mem_affineOpen_iff] at hp
  rw [submodule_mk, innerSection_def]
  refine Submodule.smul_mem _ _ ?_
  have h : ![affineChart 1 (mk ℂ v hv) 0, 1] = (v 1)⁻¹ • v := by
    ext i
    fin_cases i <;> simp [div_eq_inv_mul, hp]
  rw [h]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)

theorem outerSection_mem_submodule {p : ℙ ℂ (Fin 2 → ℂ)} (hp : p ∈ affineOpen 0) :
    outerSection p ∈ p.submodule := by
  induction p using Projectivization.ind with | h v hv =>
  rw [mk_mem_affineOpen_iff] at hp
  rw [submodule_mk, outerSection_def]
  refine Submodule.smul_mem _ _ ?_
  have h : ![1, affineChart 0 (mk ℂ v hv) 0] = (v 0)⁻¹ • v := by
    ext i
    fin_cases i <;> simp [div_eq_inv_mul, hp]
  rw [h]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)

private theorem continuousOn_section {i : Fin 2} {g : ℂ → Fin 2 → ℂ} (hg : Continuous g) :
    ContinuousOn (fun p : ℙ ℂ (Fin 2 → ℂ) ↦
      (((max 1 ‖affineChart i p 0‖)⁻¹ : ℝ) : ℂ) • g (affineChart i p 0)) (affineOpen i) := by
  have hz : ContinuousOn (fun p : ℙ ℂ (Fin 2 → ℂ) ↦ affineChart i p 0) (affineOpen i) :=
    (continuous_apply 0).comp_continuousOn (continuousOn_affineChart i)
  refine ContinuousOn.smul (Complex.continuous_ofReal.comp_continuousOn
    (((continuous_const.max continuous_id).comp_continuousOn hz.norm).inv₀
      fun _ _ ↦ (lt_max_of_lt_left one_pos).ne')) ?_
  exact hg.comp_continuousOn hz

theorem continuousOn_innerSection : ContinuousOn innerSection (affineOpen 1) :=
  continuousOn_section (g := fun z ↦ ![z, 1]) (by fun_prop)

theorem continuousOn_outerSection : ContinuousOn outerSection (affineOpen 0) :=
  continuousOn_section (g := fun w ↦ ![1, w]) (by fun_prop)

/-- On the annulus, the inner section is the outer one times the radial retraction `z / |z|`. -/
theorem innerSection_eq_smul_outerSection (p : ↥(innerDisc ∩ outerDisc)) :
    innerSection p = (annulusToCircle p : ℂ) • outerSection p := by
  obtain ⟨p, hp⟩ := p
  induction p using Projectivization.ind with | h v hv =>
  simp only [mem_inter_iff, mk_mem_innerDisc_iff, mk_mem_outerDisc_iff] at hp
  have h0 := hp.2.1
  have h1 := hp.1.1
  have hz : v 0 / v 1 ≠ 0 := div_ne_zero h0 h1
  have hr : ‖v 0 / v 1‖ ≠ 0 := norm_ne_zero_iff.2 hz
  -- The coordinate `w` of the outer chart is `z⁻¹`, and `|z| * max 1 |z⁻¹| = max 1 |z|`.
  have hw : v 1 / v 0 = (v 0 / v 1)⁻¹ := (inv_div _ _).symm
  simp only [innerSection_def, outerSection_def, coe_annulusToCircle_apply, affineChart_mk,
    show Fin.succAbove (1 : Fin 2) 0 = 0 from rfl, show Fin.succAbove (0 : Fin 2) 0 = 1 from rfl,
    hw]
  generalize v 0 / v 1 = z at *
  ext i
  have hkey : (‖z‖ : ℂ) * ((max 1 (1 / ‖z‖) : ℝ) : ℂ) = ((max 1 ‖z‖ : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, mul_max_of_nonneg _ _ (norm_nonneg _), mul_one,
      mul_one_div_cancel hr, max_comm]
  fin_cases i <;> simp [Complex.real_smul] <;> field_simp <;> rw [hkey]

end SymplecticGeometry.ProjectiveLine

/-! ### The tautological line of `ℂP¹` as a clutching -/

namespace TauCeti.FiniteRankBundleCore

open SymplecticGeometry.ProjectiveLine

variable {X : Type*} [TopologicalSpace X]

/-- The section of the tautological line on the disc of the side `s` (`true` for the inner
disc). -/
private def discSection (s : Bool) : ℙ ℂ (Fin 2 → ℂ) → Fin 2 → ℂ :=
  bif s then innerSection else outerSection

private theorem discSection_mem_submodule {s : Bool} {p : ℙ ℂ (Fin 2 → ℂ)}
    (hp : p ∈ bif s then innerDisc else outerDisc) : discSection s p ∈ p.submodule := by
  cases s
  · exact outerSection_mem_submodule hp.1
  · exact innerSection_mem_submodule hp.1

private theorem discSection_ne_zero (s : Bool) (p : ℙ ℂ (Fin 2 → ℂ)) : discSection s p ≠ 0 := by
  cases s
  · exact outerSection_ne_zero p
  · exact innerSection_ne_zero p

private theorem continuousAt_discSection {s : Bool} {p : ℙ ℂ (Fin 2 → ℂ)}
    (hp : p ∈ bif s then innerDisc else outerDisc) : ContinuousAt (discSection s) p := by
  cases s
  · exact continuousOn_outerSection.continuousAt
      ((isOpen_affineOpen 0).mem_nhds hp.1)
  · exact continuousOn_innerSection.continuousAt
      ((isOpen_affineOpen 1).mem_nhds hp.1)

variable (X)

/-- The side of the gluing of `X × ℙ ℂ (Fin 2 → ℂ)` on which the chart at `b` lies. -/
private abbrev side (b : X × ℙ ℂ (Fin 2 → ℂ)) : Bool :=
  glueIndex (Prod.snd ⁻¹' innerDisc) b

omit [TopologicalSpace X] in
private theorem mem_disc_side (b : X × ℙ ℂ (Fin 2 → ℂ)) :
    b.2 ∈ bif side X b then innerDisc else outerDisc := by
  have := mem_glueSide_glueIndex (U := Prod.snd ⁻¹' innerDisc) (V := Prod.snd ⁻¹' outerDisc)
    (by rw [← preimage_union, innerDisc_union_outerDisc, preimage_univ]) b
  cases h : side X b <;> simp_all [glueSide]

/-- The identification of the fibre of the clutched line at `b` with the line `b.2`: a coordinate
`a` goes to `a` times the section of the tautological line on the side of `b`. -/
private def lineEquiv (b : X × ℙ ℂ (Fin 2 → ℂ)) :
    (Fin 1 → ℂ) ≃L[ℂ] Tautological ℂ (Fin 2 → ℂ) b.2 :=
  (LinearMap.linearEquivOfInjective
    { toFun := fun a ↦ ⟨a 0 • discSection (side X b) b.2,
        Submodule.smul_mem _ _ (discSection_mem_submodule (mem_disc_side X b))⟩
      map_add' := fun a a' ↦ Subtype.ext (add_smul _ _ _)
      map_smul' := fun c a ↦ Subtype.ext (mul_smul _ _ _) }
    (fun a a' h ↦ by
      have h' := congrArg Subtype.val h
      simp only [LinearMap.coe_mk, AddHom.coe_mk] at h'
      have := smul_left_injective ℂ (discSection_ne_zero (side X b) b.2) h'
      ext i
      rwa [Subsingleton.elim i 0])
    (by rw [finrank_fin_fun, finrank_submodule])).toContinuousLinearEquiv

omit [TopologicalSpace X] in
private theorem coe_lineEquiv_apply (b : X × ℙ ℂ (Fin 2 → ℂ)) (a : Fin 1 → ℂ) :
    (lineEquiv X b a : Fin 2 → ℂ) = a 0 • discSection (side X b) b.2 :=
  (rfl)

/-- The gluing cocycle of the clutching by `u⁻¹` matches the sections of the two sides. -/
private theorem glueCocycle_smul_discSection (s t : Bool) (b : X × ℙ ℂ (Fin 2 → ℂ))
    (hs : b.2 ∈ bif s then innerDisc else outerDisc)
    (ht : b.2 ∈ bif t then innerDisc else outerDisc) (a : Fin 1 → ℂ) :
    glueCocycle (clutchingAut (trivial ℂ X 1) (circleZPowIso X (-1))) s t b a (0 : Fin 1) •
        discSection t b.2 = a 0 • discSection s b.2 := by
  cases s <;> cases t
  · rw [glueCocycle_self]; rfl
  · have hb : b.2 ∈ innerDisc ∩ outerDisc := ⟨ht, hs⟩
    rw [glueCocycle_false_true _ (show b ∈ Prod.snd ⁻¹' innerDisc ∩ Prod.snd ⁻¹' outerDisc
      from hb)]
    -- `erw`: the fibres are `Fin 1 → ℂ` here, and `Fin r → ℂ` for ranks `r` equal to `1` there.
    erw [fiberMap_clutchingAut_hom, fiberMap_circleZPowIso_hom_apply, clutchingMap_apply]
    simp only [discSection, Bool.cond_true, Bool.cond_false, Pi.smul_apply, smul_eq_mul]
    rw [innerSection_eq_smul_outerSection ⟨b.2, hb⟩, smul_smul, zpow_neg_one, Circle.coe_inv]
    have hu := Circle.coe_ne_zero (annulusToCircle ⟨b.2, hb⟩)
    congr 1
    field_simp
  · have hb : b.2 ∈ innerDisc ∩ outerDisc := ⟨hs, ht⟩
    rw [glueCocycle_true_false _ (show b ∈ Prod.snd ⁻¹' innerDisc ∩ Prod.snd ⁻¹' outerDisc
      from hb)]
    -- `erw`: the fibres are `Fin 1 → ℂ` here, and `Fin r → ℂ` for ranks `r` equal to `1` there.
    erw [fiberMap_clutchingAut_inv, fiberMap_circleZPowIso_inv_apply, clutchingMap_apply]
    simp only [discSection, Bool.cond_true, Bool.cond_false, Pi.smul_apply, smul_eq_mul, neg_neg,
      zpow_one]
    rw [innerSection_eq_smul_outerSection ⟨b.2, hb⟩, smul_smul, mul_comm]
  · rw [glueCocycle_self]; rfl

/-- The clutching of the trivial line by `u ↦ u⁻¹`. -/
private abbrev clutchedLine : FiniteRankBundleCore ℂ (X × ℙ ℂ (Fin 2 → ℂ)) :=
  (trivial ℂ X 1).clutching (circleZPowIso X (-1))

/-- The total space of the clutching of the trivial line by `u ↦ u⁻¹`. -/
private abbrev CT : Type _ :=
  (clutchedLine X).core.TotalSpace

/-- The vector of the tautological line given by a point of the total space of the clutched
line is continuous. -/
private theorem continuous_lineEquiv :
    Continuous fun p : CT X ↦ (lineEquiv X p.proj p.snd : Fin 2 → ℂ) := by
  refine continuous_iff_continuousAt.2 fun p₀ ↦ ?_
  set y := p₀.proj
  have hsrc : ((clutchedLine X).core.localTriv y).source ∈ 𝓝 p₀ :=
    ((clutchedLine X).core.localTriv y).open_source.mem_nhds
      (by simpa using (clutchedLine X).mem_baseSet_self y)
  have hdisc : {p : CT X | p.proj.2 ∈ bif side X y then innerDisc else outerDisc}
      ∈ 𝓝 p₀ := by
    refine (IsOpen.preimage (continuous_snd.comp (FiberBundle.continuous_proj _ _)) ?_).mem_nhds
      (mem_disc_side X y)
    cases side X y
    · exact isOpen_outerDisc
    · exact isOpen_innerDisc
  -- Near `p₀`, read the vector in the chart at `y`, on whose side the section is continuous.
  refine ContinuousAt.congr (f := fun p ↦ ((clutchedLine X).core.localTriv y p).2 (0 : Fin 1) •
      discSection (side X y) p.proj.2) ?_ ?_
  · refine ((continuous_apply (0 : Fin 1)).continuousAt.comp (continuous_snd.continuousAt.comp
      (((clutchedLine X).core.localTriv y).continuousAt (mem_of_mem_nhds hsrc)))).smul ?_
    exact ContinuousAt.comp (g := discSection (side X y)) (f := fun p : CT X ↦ p.proj.2)
      (x := p₀) (continuousAt_discSection (mem_disc_side X y))
      (continuous_snd.comp (FiberBundle.continuous_proj _ _)).continuousAt
  · filter_upwards [hdisc] with p hp
    refine Eq.trans ?_ (coe_lineEquiv_apply X p.proj p.snd).symm
    rw [VectorBundleCore.localTriv_apply, indexAt_eq, coordChange_clutching]
    dsimp only
    -- `erw`: the fibre of the clutched core is `Fin 1 → ℂ` only up to unfolding its rank.
    erw [inChartCoordinates_core_apply]
    -- The transitions of the pullback of the trivial line are the identity by definition.
    exact glueCocycle_smul_discSection X _ _ p.proj (mem_disc_side X p.proj) hp p.snd

private theorem continuous_totalSpaceMk_lineEquiv :
    Continuous fun p : CT X ↦ TotalSpace.mk' ℂ
      (E := (⇑(ContinuousMap.snd : C(X × ℙ ℂ (Fin 2 → ℂ), _))) *ᵖ (Tautological ℂ (Fin 2 → ℂ)))
      p.proj (lineEquiv X p.proj p.snd) := by
  refine (inducing_pullbackTotalSpaceEmbedding (F := ℂ) (Tautological ℂ (Fin 2 → ℂ))
    (⇑(ContinuousMap.snd : C(X × ℙ ℂ (Fin 2 → ℂ), _)))).continuous_iff.2
    ((FiberBundle.continuous_proj _ _).prodMk ?_)
  exact continuous_totalSpace_tautological_iff.2
    ⟨continuous_snd.comp (FiberBundle.continuous_proj _ _), continuous_lineEquiv X⟩

/-- **The tautological line as a clutching.** The pullback of the tautological line of
`ℙ ℂ (Fin 2 → ℂ)` to `X × ℙ ℂ (Fin 2 → ℂ)` is isomorphic to the clutching of the trivial line by
`u ↦ u⁻¹`. -/
def clutchingZIso :
    (trivial ℂ X 1).clutching (circleZPowIso X (-1)) ≅
      (Projectivization.tautologicalCore ℂ (Fin 2 → ℂ)).pullback ContinuousMap.snd :=
  isoOfContinuousEquiv (D := ofBundleOfFinrankEq ℂ ℂ
      ((⇑(ContinuousMap.snd : C(X × ℙ ℂ (Fin 2 → ℂ), _))) *ᵖ (Tautological ℂ (Fin 2 → ℂ)))
      (finrank_self ℂ))
    (fun b ↦ (lineEquiv X b).trans (ofBundleOfFinrankEqFiberEquiv ℂ ℂ
      ((⇑(ContinuousMap.snd : C(X × ℙ ℂ (Fin 2 → ℂ), _))) *ᵖ (Tautological ℂ (Fin 2 → ℂ)))
      (finrank_self ℂ) b).symm)
    (((ofBundleOfFinrankEqHomeomorph ℂ ℂ _ _).symm.continuous.comp
      (continuous_totalSpaceMk_lineEquiv X)).congr fun p ↦ by
      rw [Function.comp_apply, ofBundleOfFinrankEqHomeomorph_symm_apply]
      -- Both sides are `⟨p.proj, ψ p.proj p.snd⟩`, the fibre of the pullback unfolded.
      rfl) ≪≫
    eqToIso (Projectivization.tautologicalCore_def ℂ (Fin 2 → ℂ) ▸
      pullback_ofBundleOfFinrankEq _ _ _).symm

/-- **The tautological line as a clutching.** The pullback of the tautological line of
`ℙ ℂ (Fin 2 → ℂ)` to `X × ℙ ℂ (Fin 2 → ℂ)` is isomorphic to the clutching of the trivial line by
`u ↦ u⁻¹`. -/
theorem clutching_z :
    Nonempty ((Projectivization.tautologicalCore ℂ (Fin 2 → ℂ)).pullback ContinuousMap.snd ≅
      (trivial ℂ X 1).clutching (circleZPowIso X (-1))) :=
  ⟨(clutchingZIso X).symm⟩

end TauCeti.FiniteRankBundleCore

end
