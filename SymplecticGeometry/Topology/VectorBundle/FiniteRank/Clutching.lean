/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Topology.ComplexProjectiveSpace.ProjectiveLine
public import SymplecticGeometry.Topology.VectorBundle.FiniteRank.Glue
public import SymplecticGeometry.Topology.VectorBundle.FiniteRank.SMul
public import SymplecticGeometry.Topology.VectorBundle.ProjectiveBundle.Tautological

/-!
# The clutching construction over `X × ℂP¹`

The projective line `ℙ ℂ (Fin 2 → ℂ)` is covered by two open discs, the inner disc
`ProjectiveLine.innerDisc` and the outer disc `ProjectiveLine.outerDisc`, which meet in an annulus
that `ProjectiveLine.annulusToCircle` retracts radially onto the unit circle,
`[z : 1] ↦ z / |z|` (see `SymplecticGeometry.Topology.ComplexProjectiveSpace.ProjectiveLine`).

For a finite-rank core `E` over `X` and an automorphism `f` of the pullback of `E` to `X × Circle`
along the projection, `E.clutching f` is the core over `X × ℙ ℂ (Fin 2 → ℂ)` obtained by gluing
the pullback of `E` along `Prod.fst` to itself over the product of `X` with the annulus by `f`
composed with the radial retraction (`ProjectiveLine.clutchingMap`): a vector `v` over
`(x, [z : 1])` in the copy over the outer disc is the vector `f_{(x, z / |z|)} v` in the copy over
the inner disc. This is the clutching construction of [Hatcher2017, §2.1]. It uses no K-theory,
and the fibres may be over any nontrivially normed field.

## Main definitions and results

* `TauCeti.FiniteRankBundleCore.clutchingAut E f`: the pullback of `f` along
  `SymplecticGeometry.ProjectiveLine.clutchingMap`.
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
  clutching of `E₁ ⊕ E₂` by the block-diagonal family `whitneyMapIsoPullback f₁ f₂`, which is
  `whitneyMapIso f₁ f₂` read through `pullback_whitneySum`, is the Whitney sum of the clutchings
  of `E₁` by `f₁` and of `E₂` by `f₂`.
* `TauCeti.FiniteRankBundleCore.clutchingTensorIso` and `clutching_tensor`: the clutching of
  `E₁ ⊗ E₂` by the tensor product `tensorIsoPullback f₁ f₂` of the families, which is `f₁ ⊗ᵢ f₂`
  read through `pullback_tensorObj`, is the tensor product of the clutchings, for instance the
  twist of a clutching by a line bundle with its clutching function.
* `TauCeti.FiniteRankBundleCore.nonempty_iso_clutching_of_homotopic`: over a paracompact R₁
  space, clutchings by automorphisms joined by a family over `X × I` are isomorphic.
* `TauCeti.FiniteRankBundleCore.nonempty_iso_clutching_of_fiberMap_comp_eq`: isomorphisms
  `Φ Ψ : E ≅ E'` with `Φ_x ∘ f_{(x, u)} = f'_{(x, u)} ∘ Ψ_x` give an isomorphism of the
  clutchings, through `Φ` over the inner disc and `Ψ` over the outer disc.
* `TauCeti.FiniteRankBundleCore.nonempty_iso_clutching_pullback_trans` and
  `nonempty_iso_clutching_trans_pullback`: composing `f`, on either side, with the pullback to
  `X × Circle` of an automorphism of `E` gives an isomorphic clutching; in particular the
  clutching by such a pullback is the pullback of `E` along `Prod.fst`
  (`nonempty_iso_clutching_pullback`). The pullback extends over the whole product, so this is
  `nonempty_iso_clutching_of_fiberMap_comp_eq` with the identity on one side, with no homotopy.
* `TauCeti.FiniteRankBundleCore.circleZPowSMul m f`: for complex `E`, the family `u ^ m • f`
  whose fibre map at `(x, u)` is `u ^ m` times that of `f`.
* `TauCeti.FiniteRankBundleCore.circleZPowIso X n`: the automorphism of the trivial line over
  `X × Circle` that multiplies the fibre over `(x, u)` by `u ^ n`, that is `u ^ n` times the
  identity (`circleZPowIso_def`); for `n = 0` it is the identity (`circleZPowIso_zero`).
* `SymplecticGeometry.ProjectiveLine.innerSection` and `outerSection`: the vectors
  `(z, 1) / max 1 |z|` and `(1, w) / max 1 |w|` of the lines `[z : 1]` and `[1 : w]`, multiples
  of `Projectivization.normalizedRep` and nonzero on the affine opens; on the
  annulus the first is the second times `z / |z|` (`innerSection_eq_smul_outerSection`).
* `TauCeti.FiniteRankBundleCore.clutchingZIso` and `clutching_z`: the pullback of the tautological
  line of `ℙ ℂ (Fin 2 → ℂ)` to `X × ℙ ℂ (Fin 2 → ℂ)` is the clutching of the trivial line by
  `circleZPowIso X (-1)`, that is by `u ↦ u⁻¹`.

The clutched core is `TauCeti.FiniteRankBundleCore.glue`, applied to the cover of
`X × ℙ ℂ (Fin 2 → ℂ)` by the preimages of the two discs. The clutching by the identity glues by
the identity (`clutchingAut_refl`), so it is the gluing by the identity (`clutching_refl`), and
`clutchingOneIso` is this equality followed by `TauCeti.FiniteRankBundleCore.glueReflIso`.
The clutching by a direct sum or tensor product of families glues by the direct sum or tensor
product of the gluing automorphisms (`clutchingAut_whitneyMapIsoPullback`,
`clutchingAut_tensorIsoPullback`), so its transitions are those of the Whitney sum or tensor
product of the clutchings (`TauCeti.FiniteRankBundleCore.coordChange_glue_whitneyMapIsoPullback`,
`coordChange_glue_tensorIsoPullback`), and
the identity of coordinates is an isomorphism (`TauCeti.FiniteRankBundleCore.constIso`). A family
over `E₁ ⊕ E₂` or `E₁ ⊗ E₂` built from families over `E₁` and `E₂` is an automorphism of the Whitney
sum or tensor product of their pullbacks, so it is read through Tau Ceti's `pullback_whitneySum`
or `pullback_tensorObj` by `eqToIso`, as `TauCeti.FiniteRankBundleCore.whitneyMapIsoPullback` and
`TauCeti.FiniteRankBundleCore.tensorIsoPullback` do; `glue_eqToIso_trans_trans_eqToIso` moves the
gluing between the two ways of writing the pullback.

Clutchings by homotopic families are gluings by homotopic automorphisms: the family `H` over
`(X × I) × Circle`, pulled back along `((x, p), s) ↦ ((x, s), p / |p|)`, is an automorphism over
the product of the annulus part of `X × ℙ ℂ (Fin 2 → ℂ)` with `I`, whose slices at `0` and `1`
are the gluing automorphisms of the two clutchings. So
`nonempty_iso_clutching_of_homotopic` follows from
`TauCeti.FiniteRankBundleCore.nonempty_iso_glue_of_homotopic`, which rests on homotopy invariance
of pullbacks, as in [Hatcher2017, §2.1].

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

/-! ### The clutched core -/

namespace TauCeti.FiniteRankBundleCore

open SymplecticGeometry.ProjectiveLine

variable {𝕜 X : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace X]

/-- The pullback of `E` to the product of `X` with the annulus is its pullback to `X × Circle`
pulled back along `clutchingMap`: both are the pullback of `E` along `w ↦ w.val.1`. -/
theorem pullback_fst_pullback_subtypeVal_eq_pullback_clutchingMap
    (E : FiniteRankBundleCore 𝕜 X) :
    (E.pullback (ContinuousMap.fst : C(X × ℙ ℂ (Fin 2 → ℂ), X))).pullback
        (ContinuousMap.subtypeVal (Prod.snd ⁻¹' innerDisc ∩ Prod.snd ⁻¹' outerDisc)) =
      (E.pullback (ContinuousMap.fst : C(X × Circle, X))).pullback (clutchingMap X) := by
  rw [pullback_comp, pullback_comp, fst_comp_clutchingMap]

/-- The automorphism of the pullback of `E` to the product of `X` with the annulus by which the
clutching by `f` glues: the pullback of `f` along `clutchingMap`. -/
def clutchingAut (E : FiniteRankBundleCore 𝕜 X)
    (f : E.pullback (ContinuousMap.fst : C(X × Circle, X)) ≅
      E.pullback (ContinuousMap.fst : C(X × Circle, X))) :
    (E.pullback (ContinuousMap.fst : C(X × ℙ ℂ (Fin 2 → ℂ), X))).pullback
        (ContinuousMap.subtypeVal (Prod.snd ⁻¹' innerDisc ∩ Prod.snd ⁻¹' outerDisc)) ≅
      (E.pullback (ContinuousMap.fst : C(X × ℙ ℂ (Fin 2 → ℂ), X))).pullback
        (ContinuousMap.subtypeVal (Prod.snd ⁻¹' innerDisc ∩ Prod.snd ⁻¹' outerDisc)) :=
  eqToIso (pullback_fst_pullback_subtypeVal_eq_pullback_clutchingMap E) ≪≫
    (pullbackFunctor (clutchingMap X)).mapIso f ≪≫
    eqToIso (pullback_fst_pullback_subtypeVal_eq_pullback_clutchingMap E).symm

@[simp]
theorem fiberMap_clutchingAut_hom (E : FiniteRankBundleCore 𝕜 X)
    (f : E.pullback (ContinuousMap.fst : C(X × Circle, X)) ≅
      E.pullback (ContinuousMap.fst : C(X × Circle, X)))
    (w : ↥(Prod.snd ⁻¹' innerDisc ∩ Prod.snd ⁻¹' outerDisc : Set (X × ℙ ℂ (Fin 2 → ℂ)))) :
    (clutchingAut E f).hom.fiberMap w = f.hom.fiberMap (clutchingMap X w) := by
  ext v i
  simp [clutchingAut]

@[simp]
theorem fiberMap_clutchingAut_inv (E : FiniteRankBundleCore 𝕜 X)
    (f : E.pullback (ContinuousMap.fst : C(X × Circle, X)) ≅
      E.pullback (ContinuousMap.fst : C(X × Circle, X)))
    (w : ↥(Prod.snd ⁻¹' innerDisc ∩ Prod.snd ⁻¹' outerDisc : Set (X × ℙ ℂ (Fin 2 → ℂ)))) :
    (clutchingAut E f).inv.fiberMap w = f.inv.fiberMap (clutchingMap X w) := by
  ext v i
  simp [clutchingAut]

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
theorem clutchingAut_refl : clutchingAut E (Iso.refl _) = Iso.refl _ := by
  simp [clutchingAut]

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

/-- The clutching by the direct sum of two families, read through `pullback_whitneySum`, glues by
the direct sum of the automorphisms by which the clutchings by the two families glue, read
through `pullback_whitneySum`. -/
theorem clutchingAut_whitneyMapIsoPullback :
    clutchingAut (whitneySum E₁ E₂) (whitneyMapIsoPullback f₁ f₂) =
      eqToIso ((congrArg (pullback · _) (pullback_whitneySum E₁ E₂ _)).trans
          (pullback_whitneySum _ _ _)) ≪≫
        whitneyMapIso (clutchingAut E₁ f₁) (clutchingAut E₂ f₂) ≪≫
        eqToIso ((congrArg (pullback · _) (pullback_whitneySum E₁ E₂ _)).trans
          (pullback_whitneySum _ _ _)).symm := by
  ext1
  simp only [clutchingAut, Iso.trans_hom, eqToIso.hom, Functor.mapIso_hom, whitneyMapIso_hom,
    whitneyMapIsoPullback_hom, pullbackMap_comp, whitneyMap_comp, whitneyMap_eqToHom]
  rw [← pullbackFunctor_map (eqToHom _), eqToHom_map, ← pullbackFunctor_map (eqToHom _),
    eqToHom_map]
  simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
  rw [pullbackMap_whitneyMap]
  -- The `eqToHom`s of the two sides are along equalities of cores whose ends agree by
  -- `pullback_whitneySum`, which Tau Ceti proves by `rfl`.
  rfl

/-- The clutching by the tensor product of two families, read through `pullback_tensorObj`, glues
by the tensor product of the automorphisms by which the clutchings by the two families glue, read
through `pullback_tensorObj`. -/
theorem clutchingAut_tensorIsoPullback :
    clutchingAut (E₁ ⊗ E₂) (tensorIsoPullback f₁ f₂) =
      eqToIso ((congrArg (pullback · _) (pullback_tensorObj E₁ E₂ _)).trans
          (pullback_tensorObj _ _ _)) ≪≫
        (clutchingAut E₁ f₁ ⊗ᵢ clutchingAut E₂ f₂) ≪≫
        eqToIso ((congrArg (pullback · _) (pullback_tensorObj E₁ E₂ _)).trans
          (pullback_tensorObj _ _ _)).symm := by
  ext1
  simp only [clutchingAut, Iso.trans_hom, eqToIso.hom, Functor.mapIso_hom, tensorIso_hom,
    tensorIsoPullback_hom, pullbackMap_comp]
  rw [← pullbackFunctor_map (eqToHom _), eqToHom_map, ← pullbackFunctor_map (eqToHom _),
    eqToHom_map, ← MonoidalCategory.tensorHom_comp_tensorHom,
    ← MonoidalCategory.tensorHom_comp_tensorHom, MonoidalCategory.tensorHom_def (eqToHom _),
    MonoidalCategory.tensorHom_def (eqToHom _)]
  simp only [eqToHom_whiskerRight, whiskerLeft_eqToHom, Category.assoc, eqToHom_trans,
    eqToHom_trans_assoc]
  rw [pullbackMap_tensorHom_monoidal]
  -- The `eqToHom`s of the two sides are along equalities of cores whose ends agree by
  -- `pullback_tensorObj`, which Tau Ceti proves by `rfl`.
  rfl

/-- The transitions of the clutching of `E₁ ⊕ E₂` by the block-diagonal family of `f₁` and `f₂`
are those of the Whitney sum of the clutching of `E₁` by `f₁` and that of `E₂` by `f₂`. -/
theorem coordChange_clutching_whitneyMapIsoPullback (x y b : X × ℙ ℂ (Fin 2 → ℂ)) :
    ((whitneySum E₁ E₂).clutching (whitneyMapIsoPullback f₁ f₂)).core.coordChange x y b =
      (whitneySum (E₁.clutching f₁) (E₂.clutching f₂)).core.coordChange x y b := by
  have hc := clutching_def (whitneySum E₁ E₂) (whitneyMapIsoPullback f₁ f₂)
  rw [clutchingAut_whitneyMapIsoPullback, glue_eqToIso_trans_trans_eqToIso _ _ _
    (pullback_whitneySum E₁ E₂ _) _ (pullback_whitneySum _ _ _), ← whitneyMapIsoPullback_def] at hc
  refine eq_of_heq ((congr_arg_heq (fun A ↦ A.core.coordChange x y b) hc).trans
    (heq_of_eq (coordChange_glue_whitneyMapIsoPullback _ _ _ _ _ x y b) |>.trans ?_))
  exact congr_arg_heq (fun A ↦ A.core.coordChange x y b)
    (congrArg₂ whitneySum (clutching_def E₁ f₁) (clutching_def E₂ f₂)).symm

/-- The transitions of the clutching of `E₁ ⊗ E₂` by the tensor product of `f₁` and `f₂` are those
of the tensor product of the clutching of `E₁` by `f₁` and that of `E₂` by `f₂`. -/
theorem coordChange_clutching_tensorIsoPullback (x y b : X × ℙ ℂ (Fin 2 → ℂ)) :
    ((E₁ ⊗ E₂).clutching (tensorIsoPullback f₁ f₂)).core.coordChange x y b =
      (E₁.clutching f₁ ⊗ E₂.clutching f₂).core.coordChange x y b := by
  have hc := clutching_def (E₁ ⊗ E₂) (tensorIsoPullback f₁ f₂)
  rw [clutchingAut_tensorIsoPullback, glue_eqToIso_trans_trans_eqToIso _ _ _
    (pullback_tensorObj E₁ E₂ _) _ (pullback_tensorObj _ _ _), ← tensorIsoPullback_def] at hc
  refine eq_of_heq ((congr_arg_heq (fun A ↦ A.core.coordChange x y b) hc).trans
    (heq_of_eq (coordChange_glue_tensorIsoPullback _ _ _ _ _ x y b) |>.trans ?_))
  exact congr_arg_heq (fun A ↦ A.core.coordChange x y b)
    (congrArg₂ (· ⊗ ·) (clutching_def E₁ f₁) (clutching_def E₂ f₂)).symm

/-- **Clutching a Whitney sum.** The clutching of `E₁ ⊕ E₂` by the block-diagonal family of `f₁`
and `f₂` is isomorphic to the Whitney sum of the clutching of `E₁` by `f₁` and that of `E₂` by
`f₂`, by the identity in coordinates. -/
def clutchingWhitneySumIso :
    (whitneySum E₁ E₂).clutching (whitneyMapIsoPullback f₁ f₂) ≅
      whitneySum (E₁.clutching f₁) (E₂.clutching f₂) :=
  constIso (fun _ _ hb ↦ ⟨⟨hb.1.1, hb.2⟩, hb.1.2, hb.2⟩) (ContinuousLinearEquiv.refl 𝕜 _)
    fun x y b _ _ ↦ by
      rw [coordChange_clutching_whitneyMapIsoPullback]
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
    Nonempty ((whitneySum E₁ E₂).clutching (whitneyMapIsoPullback f₁ f₂) ≅
      whitneySum (E₁.clutching f₁) (E₂.clutching f₂)) :=
  ⟨clutchingWhitneySumIso f₁ f₂⟩

/-- **Clutching a tensor product.** The clutching of `E₁ ⊗ E₂` by the tensor product of the
families `f₁` and `f₂` is isomorphic to the tensor product of the clutching of `E₁` by `f₁` and
that of `E₂` by `f₂`, by the identity in coordinates. -/
def clutchingTensorIso :
    (E₁ ⊗ E₂).clutching (tensorIsoPullback f₁ f₂) ≅ E₁.clutching f₁ ⊗ E₂.clutching f₂ :=
  constIso (fun _ _ hb ↦ ⟨⟨hb.1.1, hb.2⟩, hb.1.2, hb.2⟩) (ContinuousLinearEquiv.refl 𝕜 _)
    fun x y b _ _ ↦ by
      rw [coordChange_clutching_tensorIsoPullback]
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
    Nonempty ((E₁ ⊗ E₂).clutching (tensorIsoPullback f₁ f₂) ≅ E₁.clutching f₁ ⊗ E₂.clutching f₂) :=
  ⟨clutchingTensorIso f₁ f₂⟩

end Operations

/-! ### Clutching by homotopic families -/

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
  -- The clutching by `H` glues by its pullback along `((x, p), s) ↦ ((x, s), p / |p|)`, a map
  -- from the product of the annulus part of `X × ℙ ℂ (Fin 2 → ℂ)` with `I`.
  let m : C(↥(Prod.fst ⁻¹' (Prod.snd ⁻¹' innerDisc) ∩ Prod.fst ⁻¹' (Prod.snd ⁻¹' outerDisc) :
      Set ((X × ℙ ℂ (Fin 2 → ℂ)) × I)), (X × I) × Circle) :=
    ⟨fun w ↦ ((w.val.1.1, w.val.2), annulusToCircle ⟨w.val.1.2, w.property⟩), by fun_prop⟩
  refine nonempty_iso_glue_of_homotopic (E.pullback ContinuousMap.fst) _ _ _
    ((pullbackFunctor m).mapIso H) (fun w ↦ ?_) (fun w ↦ ?_)
  · rw [fiberMap_clutchingAut_hom, clutchingMap_apply, ← h₀]
    exact fiberMap_pullbackMap H.hom m _
  · rw [fiberMap_clutchingAut_hom, clutchingMap_apply, ← h₁]
    exact fiberMap_pullbackMap H.hom m _

/-! ### Clutchings by conjugate families -/

/-- **Clutchings by conjugate families are isomorphic.** If isomorphisms `Φ Ψ : E ≅ E'` relate
the automorphism `f` of the pullback of `E` to `X × Circle` to the automorphism `f'` of that of
`E'` fibre by fibre, `Φ_x ∘ f_{(x, u)} = f'_{(x, u)} ∘ Ψ_x`, then the clutching of `E` by `f` is
isomorphic to that of `E'` by `f'`. -/
theorem nonempty_iso_clutching_of_fiberMap_comp_eq {E E' : FiniteRankBundleCore 𝕜 X}
    (Φ Ψ : E ≅ E') {f : E.pullback (ContinuousMap.fst : C(X × Circle, X)) ≅
      E.pullback (ContinuousMap.fst : C(X × Circle, X))}
    {f' : E'.pullback (ContinuousMap.fst : C(X × Circle, X)) ≅
      E'.pullback (ContinuousMap.fst : C(X × Circle, X))}
    (h : ∀ w : X × Circle, (Φ.hom.fiberMap w.1).comp (f.hom.fiberMap w) =
      (f'.hom.fiberMap w).comp (Ψ.hom.fiberMap w.1)) :
    Nonempty (E.clutching f ≅ E'.clutching f') := by
  -- The pullbacks of `Φ` over the inner disc and of `Ψ` over the outer disc.
  rw [clutching_def, clutching_def]
  refine nonempty_iso_glue_of_fiberMap_comp_eq_comp _ _ _
    ((pullbackFunctor (ContinuousMap.subtypeVal _)).mapIso
      ((pullbackFunctor ContinuousMap.fst).mapIso Φ))
    ((pullbackFunctor (ContinuousMap.subtypeVal _)).mapIso
      ((pullbackFunctor ContinuousMap.fst).mapIso Ψ)) fun b ↦ ?_
  simp only [Functor.mapIso_hom, fiberMap_pullbackMap, fiberMap_clutchingAut_hom,
    ContinuousMap.fst_apply, ContinuousMap.subtypeVal_apply]
  have hb := h (clutchingMap X b)
  rw [clutchingMap_apply] at hb ⊢
  exact hb

/-! ### Composing with the pullback of an automorphism of `E` -/

/-- **Composing with the pullback of an automorphism of `E` does not change the clutching.** For
an automorphism `φ` of `E`, the clutching of `E` by `f` after the pullback of `φ` to `X × Circle`,
the family `(x, u) ↦ f_{(x, u)} ∘ φ_x`, is isomorphic to the clutching of `E` by `f`. -/
theorem nonempty_iso_clutching_pullback_trans (φ : E ≅ E) :
    Nonempty (E.clutching ((pullbackFunctor ContinuousMap.fst).mapIso φ ≪≫ f) ≅
      E.clutching f) :=
  nonempty_iso_clutching_of_fiberMap_comp_eq (Iso.refl _) φ fun w ↦ by
    simp only [Iso.refl_hom, fiberMap_id, Iso.trans_hom, fiberMap_comp, Functor.mapIso_hom,
      fiberMap_pullbackMap, ContinuousMap.fst_apply]
    exact ContinuousLinearMap.id_comp _

/-- **Composing with the pullback of an automorphism of `E` does not change the clutching.** For
an automorphism `φ` of `E`, the clutching of `E` by the pullback of `φ` to `X × Circle` after `f`,
the family `(x, u) ↦ φ_x ∘ f_{(x, u)}`, is isomorphic to the clutching of `E` by `f`. -/
theorem nonempty_iso_clutching_trans_pullback (φ : E ≅ E) :
    Nonempty (E.clutching (f ≪≫ (pullbackFunctor ContinuousMap.fst).mapIso φ) ≅
      E.clutching f) :=
  (nonempty_iso_clutching_of_fiberMap_comp_eq φ (Iso.refl _) fun w ↦ by
    simp only [Iso.refl_hom, fiberMap_id, Iso.trans_hom, fiberMap_comp, Functor.mapIso_hom,
      fiberMap_pullbackMap, ContinuousMap.fst_apply]
    exact (ContinuousLinearMap.comp_id _).symm).map Iso.symm

/-- **Clutching by the pullback of an automorphism of `E`.** For an automorphism `φ` of `E`, the
clutching of `E` by its pullback to `X × Circle`, the constant family `(x, u) ↦ φ_x`, is
isomorphic to the pullback of `E` along `Prod.fst`. -/
theorem nonempty_iso_clutching_pullback (φ : E ≅ E) :
    Nonempty (E.clutching ((pullbackFunctor ContinuousMap.fst).mapIso φ) ≅
      E.pullback ContinuousMap.fst) := by
  obtain ⟨i⟩ := nonempty_iso_clutching_trans_pullback E (Iso.refl _) φ
  rw [Iso.refl_trans] at i
  exact ⟨i ≪≫ E.clutchingOneIso⟩

end TauCeti.FiniteRankBundleCore

/-! ### Multiplying a clutching function by a power of the coordinate -/

namespace TauCeti.FiniteRankBundleCore

variable {X : Type*} [TopologicalSpace X]

section CircleZPowSMul

variable {E : FiniteRankBundleCore ℂ X}

/-- The family `u ^ m • f` for an automorphism `f` of the pullback of `E` to `X × Circle` and
`m : ℤ`: the automorphism whose fibre map at `(x, u)` is `u ^ m • f_{(x, u)}`. -/
def circleZPowSMul (m : ℤ)
    (f : E.pullback (ContinuousMap.fst : C(X × Circle, X)) ≅
      E.pullback (ContinuousMap.fst : C(X × Circle, X))) :
    E.pullback (ContinuousMap.fst : C(X × Circle, X)) ≅
      E.pullback (ContinuousMap.fst : C(X × Circle, X)) where
  hom := (⟨fun w ↦ ((w.2 ^ m : Circle) : ℂ), by fun_prop⟩ : C(X × Circle, ℂ)) • f.hom
  inv := (⟨fun w ↦ ((w.2 ^ (-m) : Circle) : ℂ), by fun_prop⟩ : C(X × Circle, ℂ)) • f.inv
  hom_inv_id := hom_ext fun w ↦ by
    simp only [fiberMap_comp, fiberMap_smul, ContinuousMap.coe_mk, Circle.coe_zpow,
      ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp, fiberMap_hom_inv_id, smul_smul,
      fiberMap_id, ← zpow_add₀ (Circle.coe_ne_zero w.2), add_neg_cancel, zpow_zero, one_smul]
  inv_hom_id := hom_ext fun w ↦ by
    simp only [fiberMap_comp, fiberMap_smul, ContinuousMap.coe_mk, Circle.coe_zpow,
      ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp, fiberMap_inv_hom_id, smul_smul,
      fiberMap_id, ← zpow_add₀ (Circle.coe_ne_zero w.2), neg_add_cancel, zpow_zero, one_smul]

@[simp]
theorem fiberMap_circleZPowSMul_hom (m : ℤ)
    (f : E.pullback (ContinuousMap.fst : C(X × Circle, X)) ≅
      E.pullback (ContinuousMap.fst : C(X × Circle, X))) (w : X × Circle) :
    (circleZPowSMul m f).hom.fiberMap w = (w.2 : ℂ) ^ m • f.hom.fiberMap w := by
  simp [circleZPowSMul]

@[simp]
theorem fiberMap_circleZPowSMul_inv (m : ℤ)
    (f : E.pullback (ContinuousMap.fst : C(X × Circle, X)) ≅
      E.pullback (ContinuousMap.fst : C(X × Circle, X))) (w : X × Circle) :
    (circleZPowSMul m f).inv.fiberMap w = ((w.2 : ℂ) ^ m)⁻¹ • f.inv.fiberMap w := by
  simp [circleZPowSMul]

@[simp]
theorem circleZPowSMul_zero
    (f : E.pullback (ContinuousMap.fst : C(X × Circle, X)) ≅
      E.pullback (ContinuousMap.fst : C(X × Circle, X))) :
    circleZPowSMul 0 f = f :=
  Iso.ext <| hom_ext fun w ↦ by simp

@[simp]
theorem circleZPowSMul_circleZPowSMul (m n : ℤ)
    (f : E.pullback (ContinuousMap.fst : C(X × Circle, X)) ≅
      E.pullback (ContinuousMap.fst : C(X × Circle, X))) :
    circleZPowSMul m (circleZPowSMul n f) = circleZPowSMul (m + n) f :=
  Iso.ext <| hom_ext fun w ↦ by
    simp [smul_smul, zpow_add₀ (Circle.coe_ne_zero w.2)]

end CircleZPowSMul

variable (X) in
/-- The automorphism of the trivial line over `X × Circle` that multiplies the fibre over `(x, u)`
by `u ^ n`: the family `u ^ n` times the identity. -/
def circleZPowIso (n : ℤ) :
    (trivial ℂ X 1).pullback (ContinuousMap.fst : C(X × Circle, X)) ≅
      (trivial ℂ X 1).pullback (ContinuousMap.fst : C(X × Circle, X)) :=
  circleZPowSMul n (Iso.refl _)

theorem circleZPowIso_def (n : ℤ) : circleZPowIso X n = circleZPowSMul n (Iso.refl _) :=
  (rfl)

@[simp]
theorem fiberMap_circleZPowIso_hom (n : ℤ) (b : X × Circle) :
    (circleZPowIso X n).hom.fiberMap b = (b.2 : ℂ) ^ n • ContinuousLinearMap.id ℂ _ := by
  rw [circleZPowIso_def, fiberMap_circleZPowSMul_hom, Iso.refl_hom, fiberMap_id]

@[simp]
theorem fiberMap_circleZPowIso_inv (n : ℤ) (b : X × Circle) :
    (circleZPowIso X n).inv.fiberMap b = ((b.2 : ℂ) ^ n)⁻¹ • ContinuousLinearMap.id ℂ _ := by
  rw [circleZPowIso_def, fiberMap_circleZPowSMul_inv, Iso.refl_inv, fiberMap_id]

/-- Multiplication by `u ^ 0` is the identity: `circleZPowIso X 0` is the identity automorphism. -/
theorem circleZPowIso_zero : circleZPowIso X 0 = Iso.refl _ :=
  circleZPowSMul_zero _

end TauCeti.FiniteRankBundleCore

/-! ### Two nonvanishing sections of the tautological line of `ℂP¹` -/

namespace SymplecticGeometry.ProjectiveLine

/-- The vector `(z, 1) / max 1 |z|` of the line `[z : 1]`: the representative normalized by the
second coordinate, divided by `max 1 |z|`. It is `0` off the affine open `affineOpen 1`. -/
def innerSection (p : ℙ ℂ (Fin 2 → ℂ)) : Fin 2 → ℂ :=
  (((max 1 ‖affineChart 1 p 0‖)⁻¹ : ℝ) : ℂ) • normalizedRep (LinearMap.proj 1) p

/-- The vector `(1, w) / max 1 |w|` of the line `[1 : w]`: the representative normalized by the
first coordinate, divided by `max 1 |w|`. It is `0` off the affine open `affineOpen 0`. -/
def outerSection (p : ℙ ℂ (Fin 2 → ℂ)) : Fin 2 → ℂ :=
  (((max 1 ‖affineChart 0 p 0‖)⁻¹ : ℝ) : ℂ) • normalizedRep (LinearMap.proj 0) p

theorem innerSection_def (p : ℙ ℂ (Fin 2 → ℂ)) :
    innerSection p =
      (((max 1 ‖affineChart 1 p 0‖)⁻¹ : ℝ) : ℂ) • normalizedRep (LinearMap.proj 1) p :=
  (rfl)

theorem outerSection_def (p : ℙ ℂ (Fin 2 → ℂ)) :
    outerSection p =
      (((max 1 ‖affineChart 0 p 0‖)⁻¹ : ℝ) : ℂ) • normalizedRep (LinearMap.proj 0) p :=
  (rfl)

theorem innerSection_mem_submodule (p : ℙ ℂ (Fin 2 → ℂ)) : innerSection p ∈ p.submodule :=
  Submodule.smul_mem _ _ (normalizedRep_mem_submodule _ _)

theorem outerSection_mem_submodule (p : ℙ ℂ (Fin 2 → ℂ)) : outerSection p ∈ p.submodule :=
  Submodule.smul_mem _ _ (normalizedRep_mem_submodule _ _)

private theorem smul_normalizedRep_ne_zero {i : Fin 2} {p : ℙ ℂ (Fin 2 → ℂ)}
    (hp : p ∈ affineOpen i) :
    (((max 1 ‖affineChart i p 0‖)⁻¹ : ℝ) : ℂ) • normalizedRep (LinearMap.proj i) p ≠ 0 :=
  smul_ne_zero (by simpa using (lt_max_of_lt_left one_pos).ne')
    (normalizedRep_ne_zero ((affineOpen_eq_linearProjectionDomain (K := ℂ) i) ▸ hp))

theorem innerSection_ne_zero {p : ℙ ℂ (Fin 2 → ℂ)} (hp : p ∈ affineOpen 1) :
    innerSection p ≠ 0 :=
  smul_normalizedRep_ne_zero hp

theorem outerSection_ne_zero {p : ℙ ℂ (Fin 2 → ℂ)} (hp : p ∈ affineOpen 0) :
    outerSection p ≠ 0 :=
  smul_normalizedRep_ne_zero hp

private theorem continuousOn_smul_normalizedRep (i : Fin 2) :
    ContinuousOn (fun p : ℙ ℂ (Fin 2 → ℂ) ↦
      (((max 1 ‖affineChart i p 0‖)⁻¹ : ℝ) : ℂ) • normalizedRep (LinearMap.proj i) p)
      (affineOpen i) := by
  have hz : ContinuousOn (fun p : ℙ ℂ (Fin 2 → ℂ) ↦ affineChart i p 0) (affineOpen i) :=
    (continuous_apply 0).comp_continuousOn (continuousOn_affineChart i)
  refine ContinuousOn.smul (Complex.continuous_ofReal.comp_continuousOn
    (((continuous_const.max continuous_id).comp_continuousOn hz.norm).inv₀
      fun _ _ ↦ (lt_max_of_lt_left one_pos).ne')) ?_
  rw [affineOpen_eq_linearProjectionDomain]
  exact continuousOn_normalizedRep (continuous_apply i)

theorem continuousOn_innerSection : ContinuousOn innerSection (affineOpen 1) :=
  continuousOn_smul_normalizedRep 1

theorem continuousOn_outerSection : ContinuousOn outerSection (affineOpen 0) :=
  continuousOn_smul_normalizedRep 0

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
  -- The normalized representatives are `(z, 1)` and `(1, w)`.
  have e1 : (v 1)⁻¹ • v = ![v 0 / v 1, 1] := by
    ext i
    fin_cases i <;> simp [div_eq_inv_mul, h1]
  have e0 : (v 0)⁻¹ • v = ![1, v 1 / v 0] := by
    ext i
    fin_cases i <;> simp [div_eq_inv_mul, h0]
  simp only [innerSection_def, outerSection_def, normalizedRep_mk, LinearMap.proj_apply, e1, e0]
  simp only [coe_annulusToCircle_apply, affineChart_mk,
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

private theorem discSection_mem_submodule (s : Bool) (p : ℙ ℂ (Fin 2 → ℂ)) :
    discSection s p ∈ p.submodule := by
  cases s
  · exact outerSection_mem_submodule p
  · exact innerSection_mem_submodule p

private theorem discSection_ne_zero {s : Bool} {p : ℙ ℂ (Fin 2 → ℂ)}
    (hp : p ∈ bif s then innerDisc else outerDisc) : discSection s p ≠ 0 := by
  cases s
  · exact outerSection_ne_zero (outerDisc_subset_affineOpen hp)
  · exact innerSection_ne_zero (innerDisc_subset_affineOpen hp)

private theorem continuousAt_discSection {s : Bool} {p : ℙ ℂ (Fin 2 → ℂ)}
    (hp : p ∈ bif s then innerDisc else outerDisc) : ContinuousAt (discSection s) p := by
  cases s
  · exact continuousOn_outerSection.continuousAt
      ((isOpen_affineOpen 0).mem_nhds (outerDisc_subset_affineOpen hp))
  · exact continuousOn_innerSection.continuousAt
      ((isOpen_affineOpen 1).mem_nhds (innerDisc_subset_affineOpen hp))

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
        Submodule.smul_mem _ _ (discSection_mem_submodule _ _)⟩
      map_add' := fun a a' ↦ Subtype.ext (add_smul _ _ _)
      map_smul' := fun c a ↦ Subtype.ext (mul_smul _ _ _) }
    (fun a a' h ↦ by
      have h' := congrArg Subtype.val h
      simp only [LinearMap.coe_mk, AddHom.coe_mk] at h'
      have := smul_left_injective ℂ (discSection_ne_zero (mem_disc_side X b)) h'
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
    rw [fiberMap_clutchingAut_hom, fiberMap_circleZPowIso_hom, clutchingMap_apply]
    -- `erw`: the scalar acts on the fibre of the pullback to `X × Circle`, whose rank is the rank
    -- of the pullback to `X × ℙ ℂ (Fin 2 → ℂ)` only up to unfolding.
    erw [smul_apply, ContinuousLinearMap.id_apply a, Pi.smul_apply]
    simp only [discSection, Bool.cond_true, Bool.cond_false, smul_eq_mul, zpow_neg_one]
    rw [innerSection_eq_smul_outerSection ⟨b.2, hb⟩, smul_smul]
    have hu := Circle.coe_ne_zero (annulusToCircle ⟨b.2, hb⟩)
    congr 1
    field_simp
  · have hb : b.2 ∈ innerDisc ∩ outerDisc := ⟨hs, ht⟩
    rw [glueCocycle_true_false _ (show b ∈ Prod.snd ⁻¹' innerDisc ∩ Prod.snd ⁻¹' outerDisc
      from hb)]
    rw [fiberMap_clutchingAut_inv, fiberMap_circleZPowIso_inv, clutchingMap_apply]
    -- `erw`: the scalar acts on the fibre of the pullback to `X × Circle`, whose rank is the rank
    -- of the pullback to `X × ℙ ℂ (Fin 2 → ℂ)` only up to unfolding.
    erw [smul_apply, ContinuousLinearMap.id_apply a, Pi.smul_apply]
    simp only [discSection, Bool.cond_true, Bool.cond_false, smul_eq_mul, zpow_neg_one, inv_inv]
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
