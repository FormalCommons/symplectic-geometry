/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Analysis.Complex.RadialProjection
public import SymplecticGeometry.Topology.VectorBundle.FiniteRank.Glue
public import SymplecticGeometry.Topology.VectorBundle.FiniteRank.HomotopyInvariance
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
* `TauCeti.FiniteRankBundleCore.pullbackClutchingIso`: for an automorphism `H` over
  `(X × T) × Circle`, the pullback of the clutching by `H` along `(x, p) ↦ ((x, t), p)` is the
  clutching by any automorphism over `X × Circle` with the fibre maps of `H` at time `t`.
* `TauCeti.FiniteRankBundleCore.nonempty_iso_clutching_of_homotopic`: over a paracompact R₁
  space, clutchings by automorphisms joined by a family over `X × I` are isomorphic.

The clutched core is `TauCeti.FiniteRankBundleCore.glue`, applied to the cover of
`X × ℙ ℂ (Fin 2 → ℂ)` by the preimages of the two discs. The clutching by the identity glues by
the identity (`clutchingAut_refl`), so it is the gluing by the identity (`clutching_refl`), and
`clutchingOneIso` is this equality followed by `TauCeti.FiniteRankBundleCore.glueReflIso`.

For clutchings by homotopic families, the family over `X × I` clutches a core over
`(X × I) × ℙ ℂ (Fin 2 → ℂ)`, whose pullbacks along the inclusions at times `0` and `1` are the
two clutchings (`pullbackClutchingIso`, by `TauCeti.FiniteRankBundleCore.constIso`). These
inclusions are homotopic, so the pullbacks are isomorphic by homotopy invariance
(`TauCeti.FiniteRankBundleCore.nonempty_pullback_iso_of_homotopic`, from Tau Ceti's
`ContinuousMap.Homotopic.exists_continuousLinearEquiv_pullback`), as in [Hatcher2017, §2.1].

## References

* [A. Hatcher, *Vector Bundles and K-Theory*][Hatcher2017], §2.1 (clutching functions over
  `X × S²`).
-/

public section

noncomputable section

open Set CategoryTheory Projectivization

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

/-! ### Clutching by homotopic families -/

section Homotopic

variable {T : Type*} [TopologicalSpace T]
  (H : (E.pullback (ContinuousMap.fst : C(X × T, X))).pullback
      (ContinuousMap.fst : C((X × T) × Circle, X × T)) ≅
    (E.pullback (ContinuousMap.fst : C(X × T, X))).pullback
      (ContinuousMap.fst : C((X × T) × Circle, X × T)))
  (t : T)

/-- The side of the chart at `((x, t), p)` of a clutching over `X × T` is that of the chart at
`(x, p)` of a clutching over `X`. -/
private theorem glueIndex_sliceAt (x : X × ℙ ℂ (Fin 2 → ℂ)) :
    glueIndex (Prod.snd ⁻¹' innerDisc)
        ((((ContinuousMap.id X).prodMk (.const X t)).prodMap (.id _)) x) =
      glueIndex (Prod.snd ⁻¹' innerDisc) x := by
  simp [glueIndex_def]

/-- The chart at `i` of the pullback of a clutching over `X × T` along `(x, p) ↦ ((x, t), p)` lies
in the chart at `i` of a clutching over `X`. -/
private theorem baseSet_pullback_clutching_subset (i : X × ℙ ℂ (Fin 2 → ℂ)) :
    (((E.pullback ContinuousMap.fst).clutching H).pullback
        (((ContinuousMap.id X).prodMk (.const X t)).prodMap (.id _))).core.baseSet i ⊆
      (E.clutching f).core.baseSet i := by
  intro b hb
  rw [VectorBundleCore.baseSet_at, localTriv_baseSet_pullback, ← VectorBundleCore.baseSet_at,
    Set.mem_preimage] at hb
  rw [baseSet_clutching, glueIndex_sliceAt] at hb
  rw [baseSet_clutching]
  generalize glueIndex (Prod.snd ⁻¹' innerDisc) i = s at hb ⊢
  cases s <;> exact ⟨hb.1, hb.2⟩

variable {H t}

/-- If the fibre maps of `H` at `((x, t), z)` are those of `f` at `(x, z)`, so are the fibre maps
of their inverses. -/
private theorem fiberMap_inv_sliceAt
    (hf : ∀ w : X × Circle, H.hom.fiberMap ((w.1, t), w.2) = f.hom.fiberMap w) (w : X × Circle) :
    H.inv.fiberMap ((w.1, t), w.2) = f.inv.fiberMap w := by
  have h₁ : (f.inv.fiberMap w).comp (f.hom.fiberMap w) = .id 𝕜 _ := by
    rw [← fiberMap_comp, f.hom_inv_id, fiberMap_id]
  have h₂ : (H.hom.fiberMap ((w.1, t), w.2)).comp (H.inv.fiberMap ((w.1, t), w.2)) =
      .id 𝕜 _ := by
    rw [← fiberMap_comp, H.inv_hom_id, fiberMap_id]
  calc H.inv.fiberMap ((w.1, t), w.2)
      = ((f.inv.fiberMap w).comp (f.hom.fiberMap w)).comp (H.inv.fiberMap ((w.1, t), w.2)) := by
        rw [h₁, ContinuousLinearMap.id_comp]
    _ = f.inv.fiberMap w := by
        rw [ContinuousLinearMap.comp_assoc, ← hf, h₂, ContinuousLinearMap.comp_id]

/-- The transitions of the pullback of a clutching over `X × T` along `(x, p) ↦ ((x, t), p)` are
those of the clutching by the slice of `H` at `t`. -/
private theorem coordChange_pullback_clutching
    (hf : ∀ w : X × Circle, H.hom.fiberMap ((w.1, t), w.2) = f.hom.fiberMap w)
    (i k b : X × ℙ ℂ (Fin 2 → ℂ))
    (hi : b ∈ (((E.pullback ContinuousMap.fst).clutching H).pullback
      (((ContinuousMap.id X).prodMk (.const X t)).prodMap (.id _))).core.baseSet i)
    (hk : b ∈ (((E.pullback ContinuousMap.fst).clutching H).pullback
      (((ContinuousMap.id X).prodMk (.const X t)).prodMap (.id _))).core.baseSet k) :
    ((((E.pullback ContinuousMap.fst).clutching H).pullback
        (((ContinuousMap.id X).prodMk (.const X t)).prodMap (.id _))).core.coordChange i k b) =
      (E.clutching f).core.coordChange i k b := by
  have hs := ((baseSet_clutching E f i).le (baseSet_pullback_clutching_subset E f H t i hi)).2
  have hr := ((baseSet_clutching E f k).le (baseSet_pullback_clutching_subset E f H t k hk)).2
  simp only [coordChange_pullback, coordChange_clutching, glueIndex_sliceAt,
    inChartCoordinates_pullback]
  congr 1
  generalize glueIndex (Prod.snd ⁻¹' innerDisc) i = s at hs ⊢
  generalize glueIndex (Prod.snd ⁻¹' innerDisc) k = r at hr ⊢
  cases s <;> cases r
  · -- Both sides are the identity of `Fin E.rank → 𝕜`: the rank of a pullback is that of the core.
    simp only [glueCocycle_self]
    rfl
  · have hb : b ∈ Prod.snd ⁻¹' innerDisc ∩ Prod.snd ⁻¹' outerDisc := ⟨hr, hs⟩
    have hb' : (((ContinuousMap.id X).prodMk (.const X t)).prodMap (.id _)) b ∈
        (Prod.snd ⁻¹' innerDisc ∩ Prod.snd ⁻¹' outerDisc : Set ((X × T) × ℙ ℂ (Fin 2 → ℂ))) :=
      hb
    rw [glueCocycle_false_true _ hb', glueCocycle_false_true _ hb, fiberMap_clutchingAut_hom,
      fiberMap_clutchingAut_hom]
    exact hf (clutchingMap X ⟨b, hb⟩)
  · have hb : b ∈ Prod.snd ⁻¹' innerDisc ∩ Prod.snd ⁻¹' outerDisc := ⟨hs, hr⟩
    have hb' : (((ContinuousMap.id X).prodMk (.const X t)).prodMap (.id _)) b ∈
        (Prod.snd ⁻¹' innerDisc ∩ Prod.snd ⁻¹' outerDisc : Set ((X × T) × ℙ ℂ (Fin 2 → ℂ))) :=
      hb
    rw [glueCocycle_true_false _ hb', glueCocycle_true_false _ hb, fiberMap_clutchingAut_inv,
      fiberMap_clutchingAut_inv]
    exact fiberMap_inv_sliceAt E f hf (clutchingMap X ⟨b, hb⟩)
  · -- Both sides are the identity of `Fin E.rank → 𝕜`: the rank of a pullback is that of the core.
    simp only [glueCocycle_self]
    rfl

variable (H t)

/-- **Restricting the parameter of a clutching.** Let `H` be an automorphism of the pullback of
`E` to `(X × T) × Circle`, and `f` one of the pullback of `E` to `X × Circle` whose fibre map at
`(x, z)` is that of `H` at `((x, t), z)`. Then the pullback of the clutching of the pullback of `E`
to `X × T` by `H`, along `(x, p) ↦ ((x, t), p)`, is isomorphic to the clutching of `E` by `f`, by
the identity in coordinates. -/
def pullbackClutchingIso
    (hf : ∀ w : X × Circle, H.hom.fiberMap ((w.1, t), w.2) = f.hom.fiberMap w) :
    ((E.pullback ContinuousMap.fst).clutching H).pullback
        (((ContinuousMap.id X).prodMk (.const X t)).prodMap (.id _)) ≅ E.clutching f :=
  constIso (baseSet_pullback_clutching_subset E f H t) (.refl 𝕜 _) fun i k b hi hk ↦ by
    rw [ContinuousLinearEquiv.coe_refl, ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id]
    exact coordChange_pullback_clutching E f hf i k b hi hk

/-- The isomorphism `pullbackClutchingIso` is the identity in coordinates. -/
@[simp]
theorem fiberMap_pullbackClutchingIso_hom
    (hf : ∀ w : X × Circle, H.hom.fiberMap ((w.1, t), w.2) = f.hom.fiberMap w)
    (x : X × ℙ ℂ (Fin 2 → ℂ)) :
    (E.pullbackClutchingIso f H t hf).hom.fiberMap x = .id 𝕜 _ := by
  rw [pullbackClutchingIso, fiberMap_constIso_hom]
  -- The two sides differ only in the rank they name, both `E.rank` by definition.
  exact ContinuousLinearEquiv.coe_refl

/-- The inverse of `pullbackClutchingIso` is the identity in coordinates. -/
@[simp]
theorem fiberMap_pullbackClutchingIso_inv
    (hf : ∀ w : X × Circle, H.hom.fiberMap ((w.1, t), w.2) = f.hom.fiberMap w)
    (x : X × ℙ ℂ (Fin 2 → ℂ)) :
    (E.pullbackClutchingIso f H t hf).inv.fiberMap x = .id 𝕜 _ := by
  rw [pullbackClutchingIso, fiberMap_constIso_inv, ContinuousLinearEquiv.refl_symm]
  -- The two sides differ only in the rank they name, both `E.rank` by definition.
  exact ContinuousLinearEquiv.coe_refl

end Homotopic

open scoped unitInterval in
/-- **Clutchings by homotopic families are isomorphic.** Let `X` be paracompact and R₁, for
instance compact Hausdorff, and let `f₀` and `f₁` be automorphisms of the pullback of `E` to
`X × Circle`. If an automorphism `H` of the pullback of `E` to `(X × I) × Circle` has the fibre
maps of `f₀` at time `0` and those of `f₁` at time `1`, then the clutchings of `E` by `f₀` and by
`f₁` are isomorphic. -/
theorem nonempty_iso_clutching_of_homotopic [NormedAlgebra ℝ 𝕜] [CompleteSpace 𝕜]
    [ParacompactSpace X] [R1Space X] {f₀ f₁ : E.pullback (ContinuousMap.fst : C(X × Circle, X)) ≅
      E.pullback (ContinuousMap.fst : C(X × Circle, X))}
    (H : (E.pullback (ContinuousMap.fst : C(X × I, X))).pullback
        (ContinuousMap.fst : C((X × I) × Circle, X × I)) ≅
      (E.pullback (ContinuousMap.fst : C(X × I, X))).pullback
        (ContinuousMap.fst : C((X × I) × Circle, X × I)))
    (h₀ : ∀ w : X × Circle, H.hom.fiberMap ((w.1, 0), w.2) = f₀.hom.fiberMap w)
    (h₁ : ∀ w : X × Circle, H.hom.fiberMap ((w.1, 1), w.2) = f₁.hom.fiberMap w) :
    Nonempty (E.clutching f₀ ≅ E.clutching f₁) := by
  -- The two ends of the clutching over `X × I` are pullbacks along homotopic maps; the homotopy
  -- `(s, (x, p)) ↦ ((x, s), p)` is at its ends the two maps, as they are evaluated.
  have hJ : (((ContinuousMap.id X).prodMk (.const X (0 : I))).prodMap
      (.id (ℙ ℂ (Fin 2 → ℂ)))).Homotopic
        (((ContinuousMap.id X).prodMk (.const X (1 : I))).prodMap (.id _)) :=
    ⟨⟨⟨fun p ↦ ((p.2.1, p.1), p.2.2), by fun_prop⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩⟩
  obtain ⟨e⟩ :=
    ((E.pullback ContinuousMap.fst).clutching H).nonempty_pullback_iso_of_homotopic hJ
  exact ⟨(E.pullbackClutchingIso f₀ H 0 h₀).symm ≪≫ e ≪≫ E.pullbackClutchingIso f₁ H 1 h₁⟩

end TauCeti.FiniteRankBundleCore

end
