/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Analysis.Complex.RadialProjection
public import SymplecticGeometry.Topology.VectorBundle.FiniteRank.Glue
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
* `TauCeti.FiniteRankBundleCore.clutchingWhitneySumIso` and `clutching_whitneySum`: the
  clutching of `E₁ ⊕ E₂` by the block-diagonal family `whitneyMapIso f₁ f₂` is the Whitney sum of
  the clutchings of `E₁` by `f₁` and of `E₂` by `f₂`.
* `TauCeti.FiniteRankBundleCore.clutchingTensorIso` and `clutching_tensor`: the clutching of
  `E₁ ⊗ E₂` by the tensor product `f₁ ⊗ᵢ f₂` of the families is the tensor product of the
  clutchings, for instance the twist of a clutching by a line bundle with its clutching function.

The clutched core is `TauCeti.FiniteRankBundleCore.glue`, applied to the cover of
`X × ℙ ℂ (Fin 2 → ℂ)` by the preimages of the two discs. The clutching by the identity glues by
the identity (`clutchingAut_refl`), so it is the gluing by the identity (`clutching_refl`), and
`clutchingOneIso` is this equality followed by `TauCeti.FiniteRankBundleCore.glueReflIso`.
The clutching by a direct sum or tensor product of families glues by the direct sum or tensor
product of the gluing automorphisms (`clutchingAut_whitneyMapIso`, `clutchingAut_tensorIso`), so
its transitions are those of the Whitney sum or tensor product of the clutchings
(`TauCeti.FiniteRankBundleCore.coordChange_glue_whitneyMapIso`, `coordChange_glue_tensorIso`), and
the identity of coordinates is an isomorphism (`TauCeti.FiniteRankBundleCore.constIso`).

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

/-! ### Clutching Whitney sums and tensor products -/

section Operations

open MonoidalCategory

variable {E₁ E₂ : FiniteRankBundleCore 𝕜 X}
  (f₁ : E₁.pullback (ContinuousMap.fst : C(X × Circle, X)) ≅
    E₁.pullback (ContinuousMap.fst : C(X × Circle, X)))
  (f₂ : E₂.pullback (ContinuousMap.fst : C(X × Circle, X)) ≅
    E₂.pullback (ContinuousMap.fst : C(X × Circle, X)))

/-- The clutching by the direct sum of two families glues by the direct sum of the automorphisms
by which the clutchings by the two families glue. -/
theorem clutchingAut_whitneyMapIso :
    clutchingAut (whitneySum E₁ E₂) (whitneyMapIso f₁ f₂) =
      whitneyMapIso (clutchingAut E₁ f₁) (clutchingAut E₂ f₂) :=
  Iso.ext <| by
    rw [whitneyMapIso_hom]
    -- The gluing automorphism `clutchingAut` is by definition the pullback along `clutchingMap`.
    exact (congrArg (pullbackMap · (clutchingMap X)) (whitneyMapIso_hom f₁ f₂)).trans
      (pullbackMap_whitneyMap f₁.hom f₂.hom (clutchingMap X))

/-- The clutching by the tensor product of two families glues by the tensor product of the
automorphisms by which the clutchings by the two families glue. -/
theorem clutchingAut_tensorIso :
    clutchingAut (tensor E₁ E₂) (f₁ ⊗ᵢ f₂) = clutchingAut E₁ f₁ ⊗ᵢ clutchingAut E₂ f₂ :=
  Iso.ext (pullbackMap_tensorHom f₁.hom f₂.hom (clutchingMap X))

/-- The transitions of the clutching of `E₁ ⊕ E₂` by the block-diagonal family of `f₁` and `f₂`
are those of the Whitney sum of the clutching of `E₁` by `f₁` and that of `E₂` by `f₂`. -/
theorem coordChange_clutching_whitneyMapIso (x y b : X × ℙ ℂ (Fin 2 → ℂ)) :
    ((whitneySum E₁ E₂).clutching (whitneyMapIso f₁ f₂)).core.coordChange x y b =
      (whitneySum (E₁.clutching f₁) (E₂.clutching f₂)).core.coordChange x y b := by
  have h := coordChange_glue_whitneyMapIso (A := E₁.pullback ContinuousMap.fst)
    (D := E₂.pullback ContinuousMap.fst) (isOpen_innerDisc.preimage continuous_snd)
    (isOpen_outerDisc.preimage continuous_snd)
    (by rw [← preimage_union, innerDisc_union_outerDisc, preimage_univ])
    (clutchingAut E₁ f₁) (clutchingAut E₂ f₂) x y b
  rw [← clutchingAut_whitneyMapIso] at h
  -- The clutched core is by definition this gluing (`clutching_def`).
  exact h

/-- The transitions of the clutching of `E₁ ⊗ E₂` by the tensor product of `f₁` and `f₂` are those
of the tensor product of the clutching of `E₁` by `f₁` and that of `E₂` by `f₂`. -/
theorem coordChange_clutching_tensorIso (x y b : X × ℙ ℂ (Fin 2 → ℂ)) :
    ((tensor E₁ E₂).clutching (f₁ ⊗ᵢ f₂)).core.coordChange x y b =
      (tensor (E₁.clutching f₁) (E₂.clutching f₂)).core.coordChange x y b := by
  have h := coordChange_glue_tensorIso (A := E₁.pullback ContinuousMap.fst)
    (D := E₂.pullback ContinuousMap.fst) (isOpen_innerDisc.preimage continuous_snd)
    (isOpen_outerDisc.preimage continuous_snd)
    (by rw [← preimage_union, innerDisc_union_outerDisc, preimage_univ])
    (clutchingAut E₁ f₁) (clutchingAut E₂ f₂) x y b
  rw [← clutchingAut_tensorIso] at h
  -- The clutched core is by definition this gluing (`clutching_def`).
  exact h

/-- **Clutching a Whitney sum.** The clutching of `E₁ ⊕ E₂` by the block-diagonal family of `f₁`
and `f₂` is isomorphic to the Whitney sum of the clutching of `E₁` by `f₁` and that of `E₂` by
`f₂`, by the identity in coordinates. -/
def clutchingWhitneySumIso :
    (whitneySum E₁ E₂).clutching (whitneyMapIso f₁ f₂) ≅
      whitneySum (E₁.clutching f₁) (E₂.clutching f₂) :=
  constIso (fun _ _ hb ↦ ⟨⟨hb.1.1, hb.2⟩, hb.1.2, hb.2⟩) (ContinuousLinearEquiv.refl 𝕜 _)
    fun x y b _ _ ↦ by
      rw [coordChange_clutching_whitneyMapIso]
      -- Composition with the identity, once the ranks of the fibre models are unfolded.
      rfl

@[simp]
theorem fiberMap_clutchingWhitneySumIso_hom (x : X × ℙ ℂ (Fin 2 → ℂ)) :
    (clutchingWhitneySumIso f₁ f₂).hom.fiberMap x = .id 𝕜 _ := by
  rw [clutchingWhitneySumIso]
  exact fiberMap_constIso_hom _ _ _ x

@[simp]
theorem fiberMap_clutchingWhitneySumIso_inv (x : X × ℙ ℂ (Fin 2 → ℂ)) :
    (clutchingWhitneySumIso f₁ f₂).inv.fiberMap x = .id 𝕜 _ := by
  rw [clutchingWhitneySumIso]
  exact fiberMap_constIso_inv _ _ _ x

/-- **Clutching a Whitney sum.** The clutching of `E₁ ⊕ E₂` by the block-diagonal family of `f₁`
and `f₂` is isomorphic to the Whitney sum of the clutching of `E₁` by `f₁` and that of `E₂` by
`f₂`. -/
theorem clutching_whitneySum :
    Nonempty ((whitneySum E₁ E₂).clutching (whitneyMapIso f₁ f₂) ≅
      whitneySum (E₁.clutching f₁) (E₂.clutching f₂)) :=
  ⟨clutchingWhitneySumIso f₁ f₂⟩

/-- **Clutching a tensor product.** The clutching of `E₁ ⊗ E₂` by the tensor product of the
families `f₁` and `f₂` is isomorphic to the tensor product of the clutching of `E₁` by `f₁` and
that of `E₂` by `f₂`, by the identity in coordinates. -/
def clutchingTensorIso :
    (tensor E₁ E₂).clutching (f₁ ⊗ᵢ f₂) ≅ tensor (E₁.clutching f₁) (E₂.clutching f₂) :=
  constIso (fun _ _ hb ↦ ⟨⟨hb.1.1, hb.2⟩, hb.1.2, hb.2⟩) (ContinuousLinearEquiv.refl 𝕜 _)
    fun x y b _ _ ↦ by
      rw [coordChange_clutching_tensorIso]
      -- Composition with the identity, once the ranks of the fibre models are unfolded.
      rfl

@[simp]
theorem fiberMap_clutchingTensorIso_hom (x : X × ℙ ℂ (Fin 2 → ℂ)) :
    (clutchingTensorIso f₁ f₂).hom.fiberMap x = .id 𝕜 _ := by
  rw [clutchingTensorIso]
  exact fiberMap_constIso_hom _ _ _ x

@[simp]
theorem fiberMap_clutchingTensorIso_inv (x : X × ℙ ℂ (Fin 2 → ℂ)) :
    (clutchingTensorIso f₁ f₂).inv.fiberMap x = .id 𝕜 _ := by
  rw [clutchingTensorIso]
  exact fiberMap_constIso_inv _ _ _ x

/-- **Clutching a tensor product.** The clutching of `E₁ ⊗ E₂` by the tensor product of the
families `f₁` and `f₂` is isomorphic to the tensor product of the clutching of `E₁` by `f₁` and
that of `E₂` by `f₂`. For a line bundle `E₂` with a clutching family `f₂`, this twists a
clutching by the clutching of a line bundle. -/
theorem clutching_tensor :
    Nonempty ((tensor E₁ E₂).clutching (f₁ ⊗ᵢ f₂) ≅
      tensor (E₁.clutching f₁) (E₂.clutching f₂)) :=
  ⟨clutchingTensorIso f₁ f₂⟩

end Operations

end TauCeti.FiniteRankBundleCore

end
