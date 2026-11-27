/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Diffeomorph.Basic
public import TauCeti.Geometry.Manifold.Gluing.PartialDiffeomorph
public import TauCeti.Geometry.Manifold.Gluing.GlueData
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Pullback.LocalDiffeomorph
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.Basic
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Opens
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Injective
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Pullback.Smooth
import SymplecticGeometry.Geometry.Symplectic.Manifold.TwoForm

/-!
# Gluing two spaces along open subsets

Let `M₁` and `M₂` be topological spaces, let `U₁` and `U₂` be open subsets of them, and let
`φ : U₁ ≃ₜ U₂` be a homeomorphism. The glued space `SymplecticGeometry.GluedAlong φ` is
`M₁ ⊔ M₂` with each `x ∈ U₁` identified with `φ x ∈ U₂`. It is the glued space of Tau Ceti's star
gluing `TauCeti.starGlueData` of the pieces `M₂` (index `true`) and `M₁` (index `false`)
about the centre `M₂`, the piece `M₂` attached by the identity and `M₁` by `φ`: the
construction of Tau Ceti's `OpenPartialHomeomorph.glueData`, with `φ` in place of an open
partial homeomorphism `M₁ ⇀ M₂`. Such a partial homeomorphism need not exist, since it needs
maps between the whole spaces: for `M₁` a point, `M₂` empty and `U₁ = U₂ = ∅` there is none.
The glued space comes with the canonical open embeddings `GluedAlong.inl : M₁ → GluedAlong φ` and
`GluedAlong.inr : M₂ → GluedAlong φ`, whose ranges
cover it. A point `x` of `M₁` and a point `y` of `M₂` have the same image exactly when `x ∈ U₁`
and `φ x = y` (`GluedAlong.inl_eq_inr_iff`). The glued space need not be Hausdorff even when
`M₁` and `M₂` are; it is when, moreover, the graph of `φ` is closed in `M₁ × M₂`. When `M₁` and
`M₂` are charted spaces over one model, so is the glued space.

Let now `M₁` and `M₂` be charted spaces over one model `I`, and `φ : U₁ ≃ₘ^n⟮I, I⟯ U₂` a `C^n`
diffeomorphism, along whose homeomorphism `φ.toHomeomorph` the two are glued. Both
maps out of an overlap are local diffeomorphisms: the inclusions of `U₁` and `U₂`, and `φ`
and its inverse. So the gluing is compatible in the sense of Tau Ceti's
`TopCat.GlueData.IsCompatible`, and `TopCat.GlueData.chartedSpace` and
`TopCat.GlueData.IsCompatible.isManifold` make `GluedAlong φ.toHomeomorph` a charted space over
the model of `M₁` and `M₂`, and a `C^n` manifold when they are, for which `inl` and `inr` are
`C^n` local diffeomorphisms. The compatibility holds as well for a homeomorphism that is `C^n`
with a `C^n` inverse (`GluedAlong.isCompatible_glueData_of_contMDiff`), and for any compatible
gluing `inl` and `inr` are `C^n` local diffeomorphisms and a map out of the glued space is `C^m`
exactly when its compositions with them are (`GluedAlong.contMDiff_iff_of_isCompatible`), and a
local diffeomorphism exactly when they are (`GluedAlong.isLocalDiffeomorph_iff_of_isCompatible`).
So `C^m` maps on `M₁` and `M₂` that agree on the overlap give a `C^m` map on the glued manifold
(`GluedAlong.descContMDiffMap`), whose continuous map is `desc`. When the two maps are injective
local diffeomorphisms into a manifold `X` whose ranges cover it, and their values meet only at
points coming from the overlap, this map is a bijective local diffeomorphism, so by Mathlib's
`IsLocalDiffeomorph.diffeomorphOfBijective` a diffeomorphism onto `X`
(`GluedAlong.descDiffeomorph`): a manifold covered by two open subsets is their gluing.

Over `ℝ`, for a smooth `φ`, smooth forms glue. Let `σ₁` and `σ₂` be smooth forms on `M₁` and
`M₂` that correspond on the overlap: `φ^*(σ₂|U₂) = σ₁|U₁`, where restricting to an open subset
is pulling back along `Subtype.val`. The form `GluedAlong.gluedForm φ σ₁ σ₂ hσ` is, at a point
`inl x`, the value `σ₁ x` read through the inverse of the differential of `inl` at `x`, and at
the other points, which are of the form `inr y`, the value `σ₂ y` read through the inverse of
the differential of `inr`: the library's two-piece gluing `TauCeti.RoughForm.glue` of `σ₁` and
`σ₂` along `inl` and `inr` (`mpullback_inl_glue`, `mpullback_inr_glue`). It pulls back to
`σ₁` by `inl` and to `σ₂` by `inr`; for `inr` at a point of `U₂`, by the chain rule along
`inr ∘ φ = inl` on `U₁`. It is smooth because `inl` and `inr` are local diffeomorphisms
(`TauCeti.RoughForm.isSmoothForm_glue`). Since the ranges of `inl` and
`inr` cover the glued space and the differentials are invertible, a form on it is determined by
its two pull-backs, and it is closed, nondegenerate or symplectic exactly when both pull-backs
are. The form of the completion of a Liouville domain, in the library's
`Geometry/Symplectic/Liouville/Completion.lean`, is glued by the same construction. Pulling a
form on `X` back by `descContMDiffMap` or `descDiffeomorph` gives the form glued from its
pull-backs by the two maps (`mpullback_descContMDiffMap`, `mpullback_descDiffeomorph`).

## Main definitions

* `SymplecticGeometry.GluedAlong φ`: the space glued from `M₁` and `M₂` along `φ`.
* `SymplecticGeometry.GluedAlong.inl`, `SymplecticGeometry.GluedAlong.inr`: the canonical maps
  from `M₁` and `M₂`, and `SymplecticGeometry.GluedAlong.inlContinuousMap`, `inl` as a continuous
  map.
* `SymplecticGeometry.GluedAlong.desc`: the continuous map on the glued space given by continuous
  maps on `M₁` and `M₂` that agree on the overlap.
* `SymplecticGeometry.GluedAlong.descContMDiffMap`: its smooth version, for a gluing along a
  diffeomorphism.
* `SymplecticGeometry.GluedAlong.descDiffeomorph`: the diffeomorphism onto a manifold that two
  injective local diffeomorphisms from `M₁` and `M₂` cover, meeting only along the overlap.
* `SymplecticGeometry.GluedAlong.rangeInl`: the range of `inl`, as an open set, and
  `SymplecticGeometry.GluedAlong.rangeInlDiffeomorph`: for a compatible gluing, the
  diffeomorphism from it onto `M₁` inverse to `inl`; `rangeInr` and `rangeInrDiffeomorph`, the
  same for `inr` and `M₂`.
* `SymplecticGeometry.GluedAlong.gluedForm`: the form glued from forms on `M₁` and `M₂` that
  agree on the overlap.

## Main results

* `SymplecticGeometry.GluedAlong.isOpenEmbedding_inl`, `isOpenEmbedding_inr`,
  `range_inl_union_range_inr`, `exists_inl_or_exists_inr`, `inl_eq_inr_iff`,
  `inl_mem_range_inr_iff`, `inr_mem_range_inl_iff`, `range_inl_eq_compl_image_inr`,
  `range_inr_eq_compl_image_inl`, `range_inl_inter_range_inr`, `isClosed_image_inl`: the topology
  of the glued space.
* `SymplecticGeometry.GluedAlong.isCompatible_glueData_of_contMDiff`: the gluing along a
  homeomorphism that is `C^n` both ways is compatible.
* `SymplecticGeometry.GluedAlong.isLocalDiffeomorph_inl`, `isLocalDiffeomorph_inr`: the
  canonical maps are `C^n` local diffeomorphisms for the glued atlas.
* `SymplecticGeometry.GluedAlong.inl_eq_inr_diffeomorph_iff`, `inl_toHomeomorph_symm_apply`: the
  points identified by the gluing along a diffeomorphism, and along the inverse of one.
* `SymplecticGeometry.GluedAlong.contMDiff_iff_of_isCompatible`: for a compatible gluing, a map
  out of the glued space is `C^m` exactly when its compositions with `inl` and `inr` are;
  `isLocalDiffeomorph_iff_of_isCompatible`, the same for local diffeomorphisms.
* `SymplecticGeometry.GluedAlong.descContMDiffMap_inl`, `descContMDiffMap_inr`,
  `descDiffeomorph_inl`, `descDiffeomorph_inr`, `descDiffeomorph_symm_apply_left`,
  `descDiffeomorph_symm_apply_right`: the values of the smooth maps out of the glued manifold.
* `SymplecticGeometry.GluedAlong.desc_inl`, `desc_inr`, `continuousMap_ext`: continuous maps on `M₁`
  and `M₂` that agree on the overlap give one on the glued space, and a continuous map on the
  glued space is determined by its restrictions to `M₁` and `M₂`.
* `SymplecticGeometry.GluedAlong.t2Space_iff_isClosed_graph`, `t2Space_iff`: when the glued
  space is Hausdorff.
* `SymplecticGeometry.GluedAlong.t2Space_of_isClosed_graph`: the glued space is Hausdorff when
  `M₁` and `M₂` are and the graph of `φ` is closed in `M₁ × M₂`.
* The instance `SecondCountableTopology (GluedAlong φ)`: the glued space of two second
  countable spaces is second countable.
* `SymplecticGeometry.GluedAlong.compactSpace_of_isCompact`: the glued space is compact when the
  images of a compact subset of each piece cover it.
* `SymplecticGeometry.GluedAlong.mpullback_inl_gluedForm`, `mpullback_inr_gluedForm`,
  `eq_gluedForm_iff`: the glued form is the unique form with the given pull-backs.
* `SymplecticGeometry.GluedAlong.mpullback_rangeInlDiffeomorph_symm`,
  `mpullback_rangeInlDiffeomorph_symm_gluedForm`: the inverse of `rangeInlDiffeomorph` pulls the
  restriction of a form to the range of `inl` back to its pull-back by `inl`, and that of the
  glued form back to the form on `M₁`; `mpullback_rangeInrDiffeomorph_symm` and
  `mpullback_rangeInrDiffeomorph_symm_gluedForm`, the same for `inr` and `M₂`.
* `SymplecticGeometry.GluedAlong.isClosed_gluedForm_iff`, `isNondegenerate_gluedForm_iff`,
  `isSymplectic_gluedForm_iff`: the glued form is closed, nondegenerate or symplectic exactly
  when both forms are.
* `SymplecticGeometry.GluedAlong.mpullback_descContMDiffMap`, `mpullback_descDiffeomorph`: the
  pull-back of a form on `X` is the form glued from its pull-backs to `M₁` and `M₂`.

The compatibility of the gluing is Tau Ceti's `TauCeti.isCompatible_starGlueData`. The proof of
`t2Space_iff_isClosed_graph` follows that of Tau Ceti's
`OpenPartialHomeomorph.t2Space_glueData_iff`, and the proof of `inl_eq_inr_iff` that of
`OpenPartialHomeomorph.glueInl_eq_glueInr_iff`. The smooth map
`descContMDiffMap` has the shape of Tau Ceti's `TopCat.GlueData.IsCompatible.descContMDiffMap`,
for a target in any universe. The proofs that `descDiffeomorph` is a local diffeomorphism and
that `desc` is bijective (`bijective_desc`) follow the steps of Tau Ceti's
`TopCat.GlueData.IsCompatible.gluedDiffeomorph`, for a target that is not itself a gluing.
The cover argument of `compactSpace_of_isCompact` is that of Tau Ceti's
`TauCeti.ConnectedSum.compactSpace`, for any gluing of two pieces.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, Chapter 1 (the smooth manifold chart lemma) and
  Chapter 2, Corollary 2.8 (the gluing lemma for smooth maps).
-/

public section

open Set Topology TopologicalSpace CategoryTheory
open scoped Manifold ContDiff

noncomputable section

namespace SymplecticGeometry

universe u

section Space

variable {H : Type*} [TopologicalSpace H] {M₁ M₂ : Type u} [TopologicalSpace M₁]
  [TopologicalSpace M₂] {U₁ : Opens M₁} {U₂ : Opens M₂}
  (φ : U₁ ≃ₜ U₂)

namespace GluedAlong

open TauCeti

variable (M₂ U₁) in
/-- The attaching sets of the two pieces of the gluing: all of `M₂` (index `true`) and `U₁`
(index `false`). -/
@[expose] def glueSource : ∀ i, Opens (partialHomeomorphGluePiece M₂ M₁ i)
  | ⟨true⟩ => ⊤
  | ⟨false⟩ => U₁

variable (U₂) in
/-- The images in `M₂` of the attaching sets of the two pieces: all of `M₂` and `U₂`. -/
@[expose] def glueTarget : ULift.{u} Bool → Opens M₂
  | ⟨true⟩ => ⊤
  | ⟨false⟩ => U₂

/-- The attaching maps of the two pieces to `M₂`: the identity of `M₂`, and `φ`. -/
@[expose] def glueMap : ∀ i, glueSource M₂ U₁ i ≃ₜ glueTarget U₂ i
  | ⟨true⟩ => Homeomorph.refl _
  | ⟨false⟩ => φ

/-- The piece `M₂` is attached to the centre `M₂` by the identity. -/
@[simp] theorem coe_glueMap_true_apply (y : glueSource M₂ U₁ ⟨true⟩) :
    (glueMap φ ⟨true⟩ y : M₂) = (y : partialHomeomorphGluePiece M₂ M₁ ⟨true⟩) := (rfl)

/-- The piece `M₁` is attached to the centre `M₂` by `φ`. -/
@[simp] theorem coe_glueMap_false_apply (x : U₁) :
    (glueMap φ ⟨false⟩ x : M₂) = (φ x : M₂) := (rfl)

/-- The gluing data of `GluedAlong φ`: the star gluing of `M₂` (index `true`) and `M₁` (index
`false`) about the centre `M₂`, the piece `M₂` attached by the identity and `M₁` by `φ`. -/
abbrev glueData : TopCat.GlueData.{u} := starGlueData (glueMap φ)

end GluedAlong

/-- The space glued from `M₁` and `M₂` by identifying each point `x` of the open subset `U₁`
with the point `φ x` of `U₂`. -/
@[expose] def GluedAlong : Type u := (GluedAlong.glueData φ).toGlueData.glued

namespace GluedAlong

open TauCeti

instance : TopologicalSpace (GluedAlong φ) :=
  inferInstanceAs (TopologicalSpace (glueData φ).toGlueData.glued)

/-- The glued space of two second countable spaces is second countable. -/
instance [SecondCountableTopology M₁] [SecondCountableTopology M₂] :
    SecondCountableTopology (GluedAlong φ) :=
  -- Tau Ceti's `TopCat.GlueData.secondCountableTopology`, once each piece is second countable.
  have : ∀ i : (glueData φ).J, SecondCountableTopology ((glueData φ).U i)
    | ⟨false⟩ => inferInstanceAs (SecondCountableTopology M₁)
    | ⟨true⟩ => inferInstanceAs (SecondCountableTopology M₂)
  have : Countable (glueData φ).J := by
    rw [glueData, starGlueData_J]
    infer_instance
  TopCat.GlueData.secondCountableTopology (glueData φ)

/-- The atlas of `GluedAlong φ`, transported from the atlases of `M₁` and `M₂` along the
canonical maps. -/
instance [ChartedSpace H M₁] [ChartedSpace H M₂] : ChartedSpace H (GluedAlong φ) :=
  (glueData φ).chartedSpace H

/-- The canonical map from `M₁` to the glued space. -/
def inl : M₁ → GluedAlong φ := fun x ↦ (glueData φ).toGlueData.ι ⟨false⟩ x

/-- The canonical map from `M₂` to the glued space. -/
def inr : M₂ → GluedAlong φ := fun y ↦ (glueData φ).toGlueData.ι ⟨true⟩ y

theorem inl_def (x : M₁) : inl φ x = (glueData φ).toGlueData.ι ⟨false⟩ x := (rfl)

theorem inr_def (y : M₂) : inr φ y = (glueData φ).toGlueData.ι ⟨true⟩ y := (rfl)

theorem isOpenEmbedding_inl : IsOpenEmbedding (inl φ) :=
  (glueData φ).ι_isOpenEmbedding ⟨false⟩

theorem isOpenEmbedding_inr : IsOpenEmbedding (inr φ) :=
  (glueData φ).ι_isOpenEmbedding ⟨true⟩

theorem inl_injective : Function.Injective (inl φ) := (isOpenEmbedding_inl φ).injective

theorem inr_injective : Function.Injective (inr φ) := (isOpenEmbedding_inr φ).injective

@[simp]
theorem inl_inj {x x' : M₁} : inl φ x = inl φ x' ↔ x = x' := (inl_injective φ).eq_iff

@[simp]
theorem inr_inj {y y' : M₂} : inr φ y = inr φ y' ↔ y = y' := (inr_injective φ).eq_iff

@[fun_prop]
theorem continuous_inl : Continuous (inl φ) := (isOpenEmbedding_inl φ).continuous

@[fun_prop]
theorem continuous_inr : Continuous (inr φ) := (isOpenEmbedding_inr φ).continuous

theorem isOpen_range_inl : IsOpen (range (inl φ)) := (isOpenEmbedding_inl φ).isOpen_range

theorem isOpen_range_inr : IsOpen (range (inr φ)) := (isOpenEmbedding_inr φ).isOpen_range

/-- Every point of the glued space is `inl x` for a point `x` of `M₁` or `inr y` for a point `y`
of `M₂`. -/
theorem exists_inl_or_exists_inr (z : GluedAlong φ) : (∃ x, inl φ x = z) ∨ ∃ y, inr φ y = z := by
  obtain ⟨⟨_ | _⟩, w, rfl⟩ := (glueData φ).ι_jointly_surjective z
  exacts [Or.inl ⟨w, rfl⟩, Or.inr ⟨w, rfl⟩]

/-- Every point of the glued space comes from `M₁` or from `M₂`. -/
theorem range_inl_union_range_inr : range (inl φ) ∪ range (inr φ) = univ :=
  eq_univ_of_forall (exists_inl_or_exists_inr φ)

/-- A point `x` of `M₁` and a point `y` of `M₂` have the same image in the glued space exactly
when `x ∈ U₁` and `φ x = y`. -/
@[simp, grind =]
theorem inl_eq_inr_iff {x : M₁} {y : M₂} :
    inl φ x = inr φ y ↔ ∃ h : x ∈ U₁, (φ ⟨x, h⟩ : M₂) = y :=
  -- In the star gluing, `M₁` is attached to the centre `M₂` by `φ` and `M₂` by the identity.
  (starGlueData_ι_eq_iff_of_ne (ψ := glueMap φ) (i := ⟨false⟩) (j := ⟨true⟩) (by simp)
    (x := x) (y := y)).trans
    ⟨fun ⟨hx, _, h⟩ ↦ ⟨hx, h⟩, fun ⟨hx, h⟩ ↦ ⟨hx, trivial, h⟩⟩

/-- A point `y` of `M₂` and a point `x` of `M₁` have the same image in the glued space exactly
when `x ∈ U₁` and `φ x = y`. -/
@[simp, grind =]
theorem inr_eq_inl_iff {y : M₂} {x : M₁} :
    inr φ y = inl φ x ↔ ∃ h : x ∈ U₁, (φ ⟨x, h⟩ : M₂) = y :=
  eq_comm.trans (inl_eq_inr_iff φ)

/-- The image in the glued space of a closed subset of `M₁` that does not meet the overlap `U₁`
is closed. -/
theorem isClosed_image_inl {S : Set M₁} (hS : IsClosed S) (hSU : Disjoint S U₁) :
    IsClosed (inl φ '' S) := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro z hz
  rcases exists_inl_or_exists_inr φ z with ⟨x, rfl⟩ | ⟨y, rfl⟩
  · -- Near `inl x`, for `x ∉ S`: the open set `inl '' Sᶜ`.
    refine ⟨inl φ '' Sᶜ, ?_, (isOpenEmbedding_inl φ).isOpenMap _ hS.isOpen_compl,
      ⟨x, fun hx ↦ hz ⟨x, hx, rfl⟩, rfl⟩⟩
    rintro _ ⟨x', hx', rfl⟩ ⟨x'', hx'', h⟩
    exact hx' (inl_injective φ h ▸ hx'')
  · -- Near `inr y`: the range of `inr`, which meets `inl '' S` only in the image of `U₁`.
    refine ⟨range (inr φ), ?_, isOpen_range_inr φ, mem_range_self y⟩
    rintro _ ⟨y', rfl⟩ ⟨x, hx, h⟩
    obtain ⟨hxU, -⟩ := (inl_eq_inr_iff φ).1 h
    exact hSU.notMem_of_mem_left hx hxU

/-- A point of `U₁` and its image under `φ` have the same image in the glued space. -/
@[simp]
theorem inr_apply (x : U₁) : inr φ (φ x : M₂) = inl φ (x : M₁) :=
  ((inl_eq_inr_iff φ).2 ⟨x.property, rfl⟩).symm

/-- A point of `U₂` and its image under the inverse of `φ` have the same image in the glued
space. -/
@[simp]
theorem inl_symm_apply (y : U₂) : inl φ (φ.symm y : M₁) = inr φ (y : M₂) := by
  rw [← inr_apply, Homeomorph.apply_symm_apply]

/-- The image of a point `x` of `M₁` lies in the image of `M₂` exactly when `x ∈ U₁`. -/
@[grind =]
theorem inl_mem_range_inr_iff {x : M₁} : inl φ x ∈ range (inr φ) ↔ x ∈ U₁ :=
  ⟨fun ⟨_, hy⟩ ↦ ((inr_eq_inl_iff φ).1 hy).1, fun hx ↦ ⟨_, inr_apply φ ⟨x, hx⟩⟩⟩

/-- The image of a point `y` of `M₂` lies in the image of `M₁` exactly when `y ∈ U₂`. -/
@[grind =]
theorem inr_mem_range_inl_iff {y : M₂} : inr φ y ∈ range (inl φ) ↔ y ∈ U₂ := by
  refine ⟨fun ⟨x, hx⟩ ↦ ?_, fun hy ↦ ⟨_, inl_symm_apply φ ⟨y, hy⟩⟩⟩
  obtain ⟨h, rfl⟩ := (inl_eq_inr_iff φ).1 hx
  exact (φ ⟨x, h⟩).property

/-- The image of `M₁` in the glued space is the complement of the image of `M₂ \ U₂`. -/
theorem range_inl_eq_compl_image_inr : range (inl φ) = (inr φ '' (U₂ : Set M₂)ᶜ)ᶜ := by
  ext z
  rcases exists_inl_or_exists_inr φ z with ⟨x, rfl⟩ | ⟨y, rfl⟩
  · refine iff_of_true (mem_range_self x) fun ⟨y, hy, h⟩ ↦ hy ?_
    exact (inr_mem_range_inl_iff φ).1 ⟨x, h.symm⟩
  · rw [inr_mem_range_inl_iff, mem_compl_iff, (inr_injective φ).mem_set_image, mem_compl_iff,
      not_not, SetLike.mem_coe]

/-- The image of `M₂` in the glued space is the complement of the image of `M₁ \ U₁`. -/
theorem range_inr_eq_compl_image_inl : range (inr φ) = (inl φ '' (U₁ : Set M₁)ᶜ)ᶜ := by
  ext z
  rcases exists_inl_or_exists_inr φ z with ⟨x, rfl⟩ | ⟨y, rfl⟩
  · rw [inl_mem_range_inr_iff, mem_compl_iff, (inl_injective φ).mem_set_image, mem_compl_iff,
      not_not, SetLike.mem_coe]
  · refine iff_of_true (mem_range_self y) fun ⟨x, hx, h⟩ ↦ hx ?_
    exact (inl_mem_range_inr_iff φ).1 ⟨y, h.symm⟩

/-- The ranges of `inl` and `inr` meet in the image of `U₁`. -/
theorem range_inl_inter_range_inr : range (inl φ) ∩ range (inr φ) = inl φ '' U₁ := by
  ext z
  constructor
  · rintro ⟨⟨x, rfl⟩, hz⟩
    exact ⟨x, inl_mem_range_inr_iff φ |>.1 hz, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨mem_range_self x, inl_mem_range_inr_iff φ |>.2 hx⟩

/-- The glued space is compact when the images of compact sets `K₁ ⊆ M₁` and `K₂ ⊆ M₂` cover
it: each point of `M₁` outside `K₁` is glued to a point of `K₂`, and `K₂` contains every point
of `M₂` outside `U₂`. A point `y` of `U₂` outside `K₂` is then glued to the point `φ⁻¹ y`, which
lies in `K₁`, since otherwise `y` would be glued to a point of `K₂`. -/
theorem compactSpace_of_isCompact {K₁ : Set M₁} {K₂ : Set M₂} (hK₁ : IsCompact K₁)
    (hK₂ : IsCompact K₂) (h₁ : ∀ x ∉ K₁, ∃ y ∈ K₂, inr φ y = inl φ x)
    (h₂ : (U₂ : Set M₂)ᶜ ⊆ K₂) : CompactSpace (GluedAlong φ) := by
  have hcover : inl φ '' K₁ ∪ inr φ '' K₂ = univ := by
    refine eq_univ_of_forall fun z ↦ ?_
    rcases exists_inl_or_exists_inr φ z with ⟨x, rfl⟩ | ⟨y, rfl⟩
    · by_cases hx : x ∈ K₁
      · exact Or.inl (mem_image_of_mem _ hx)
      · exact Or.inr (h₁ x hx)
    · by_cases hy : y ∈ K₂
      · exact Or.inr (mem_image_of_mem _ hy)
      have hyU : y ∈ U₂ := not_not.1 fun h ↦ hy (h₂ h)
      refine Or.inl ⟨φ.symm ⟨y, hyU⟩, by_contra fun hx ↦ hy ?_, inl_symm_apply φ ⟨y, hyU⟩⟩
      obtain ⟨y', hy', h⟩ := h₁ _ hx
      rw [inl_symm_apply, inr_inj] at h
      rwa [h] at hy'
  exact ⟨hcover ▸ (hK₁.image (continuous_inl φ)).union (hK₂.image (continuous_inr φ))⟩

/-- The canonical map from `M₁` to the glued space, as a continuous map. -/
@[expose] def inlContinuousMap : C(M₁, GluedAlong φ) := ⟨inl φ, continuous_inl φ⟩

@[simp]
theorem coe_inlContinuousMap : ⇑(inlContinuousMap φ) = inl φ := (rfl)

/-- The range of `inl`, an open subset of the glued space: the points that come from `M₁`. -/
def rangeInl : Opens (GluedAlong φ) := ⟨range (inl φ), isOpen_range_inl φ⟩

@[simp]
theorem coe_rangeInl : (rangeInl φ : Set (GluedAlong φ)) = range (inl φ) := (rfl)

/-- A point of the glued space lies in `rangeInl φ` exactly when it is `inl x` for some `x`. -/
@[simp]
theorem mem_rangeInl {z : GluedAlong φ} : z ∈ rangeInl φ ↔ ∃ x, inl φ x = z := Iff.rfl

/-- Every point `inl x` of the glued space lies in `rangeInl φ`. -/
theorem inl_mem_rangeInl (x : M₁) : inl φ x ∈ rangeInl φ :=
  (mem_rangeInl φ).2 ⟨x, rfl⟩

/-- The range of `inr`, an open subset of the glued space: the points that come from `M₂`. -/
def rangeInr : Opens (GluedAlong φ) := ⟨range (inr φ), isOpen_range_inr φ⟩

@[simp]
theorem coe_rangeInr : (rangeInr φ : Set (GluedAlong φ)) = range (inr φ) := (rfl)

/-- A point of the glued space lies in `rangeInr φ` exactly when it is `inr y` for some `y`. -/
@[simp]
theorem mem_rangeInr {z : GluedAlong φ} : z ∈ rangeInr φ ↔ ∃ y, inr φ y = z := Iff.rfl

/-- Every point `inr y` of the glued space lies in `rangeInr φ`. -/
theorem inr_mem_rangeInr (y : M₂) : inr φ y ∈ rangeInr φ :=
  (mem_rangeInr φ).2 ⟨y, rfl⟩

section Desc

variable {X : Type*} [TopologicalSpace X]

/-- The map on the disjoint union of the pieces of the gluing that is `f₁` on `M₁` and `f₂` on
`M₂`. -/
private def sigmaDesc (f₁ : C(M₁, X)) (f₂ : C(M₂, X)) : C((Σ i, (glueData φ).U i), X) :=
  ContinuousMap.sigma fun
    | ⟨false⟩ => f₁
    | ⟨true⟩ => f₂

/-- The quotient map from the disjoint union of the pieces of the gluing onto the glued
space. -/
private def sigmaι : C((Σ i, (glueData φ).U i), GluedAlong φ) :=
  ⟨_, (glueData φ).isOpenQuotientMap_sigma_ι.continuous⟩

/-- The glued space is the quotient of the disjoint union of the pieces by `sigmaι φ`. -/
private theorem isQuotientMap_sigmaι : IsQuotientMap (sigmaι φ) :=
  (glueData φ).isOpenQuotientMap_sigma_ι.isQuotientMap

/-- `sigmaDesc φ f₁ f₂` is constant on the fibres of the quotient map `sigmaι φ`. -/
private theorem factorsThrough_sigmaDesc {f₁ : C(M₁, X)} {f₂ : C(M₂, X)}
    (h : ∀ x : U₁, f₂ (φ x) = f₁ x) : Function.FactorsThrough (sigmaDesc φ f₁ f₂) (sigmaι φ) := by
  -- On the points of `M₁` and `M₂`, `sigmaι φ` is `inl φ` and `inr φ` (`inl_def`, `inr_def`).
  rintro ⟨⟨_ | _⟩, x⟩ ⟨⟨_ | _⟩, y⟩ hxy
  · exact congrArg f₁ (inl_injective φ hxy)
  · obtain ⟨hx, rfl⟩ := (inl_eq_inr_iff φ).1 hxy
    exact (h ⟨x, hx⟩).symm
  · obtain ⟨hy, rfl⟩ := (inr_eq_inl_iff φ).1 hxy
    exact h ⟨y, hy⟩
  · exact congrArg f₂ (inr_injective φ hxy)

/-- **Maps out of the glued space.** Continuous maps `f₁ : M₁ → X` and `f₂ : M₂ → X` that agree
on the overlap, `f₂ (φ x) = f₁ x` for `x ∈ U₁`, define the continuous map on `GluedAlong φ` that
is `f₁` on `M₁` and `f₂` on `M₂` (`desc_inl`, `desc_inr`). -/
def desc (f₁ : C(M₁, X)) (f₂ : C(M₂, X)) (h : ∀ x : U₁, f₂ (φ x) = f₁ x) :
    C(GluedAlong φ, X) :=
  -- The glued space is the quotient of the disjoint union of `M₁` and `M₂` by `sigmaι`.
  (isQuotientMap_sigmaι φ).lift (sigmaDesc φ f₁ f₂) (factorsThrough_sigmaDesc φ h)

/-- The map out of the glued space is `f₁` on `M₁`. -/
@[simp]
theorem desc_inl {f₁ : C(M₁, X)} {f₂ : C(M₂, X)} (h : ∀ x : U₁, f₂ (φ x) = f₁ x) (x : M₁) :
    desc φ f₁ f₂ h (inl φ x) = f₁ x :=
  DFunLike.congr_fun ((isQuotientMap_sigmaι φ).lift_comp _ (factorsThrough_sigmaDesc φ h))
    ⟨⟨false⟩, x⟩

/-- The map out of the glued space is `f₂` on `M₂`. -/
@[simp]
theorem desc_inr {f₁ : C(M₁, X)} {f₂ : C(M₂, X)} (h : ∀ x : U₁, f₂ (φ x) = f₁ x) (y : M₂) :
    desc φ f₁ f₂ h (inr φ y) = f₂ y :=
  DFunLike.congr_fun ((isQuotientMap_sigmaι φ).lift_comp _ (factorsThrough_sigmaDesc φ h))
    ⟨⟨true⟩, y⟩

/-- Two continuous maps out of the glued space that agree on the images of `M₁` and of `M₂`
are equal. -/
theorem continuousMap_ext {f g : C(GluedAlong φ, X)} (h₁ : ∀ x, f (inl φ x) = g (inl φ x))
    (h₂ : ∀ y, f (inr φ y) = g (inr φ y)) : f = g := by
  ext z
  rcases exists_inl_or_exists_inr φ z with ⟨x, rfl⟩ | ⟨y, rfl⟩
  exacts [h₁ x, h₂ y]

/-- The map out of the glued space given by injective maps `f₁` and `f₂` whose ranges cover `X`,
and such that `f₁ x = f₂ y` only for `x ∈ U₁`, is bijective. -/
theorem bijective_desc {f₁ : C(M₁, X)} {f₂ : C(M₂, X)} (h : ∀ x : U₁, f₂ (φ x) = f₁ x)
    (hinj₁ : Function.Injective f₁) (hinj₂ : Function.Injective f₂)
    (hcover : range f₁ ∪ range f₂ = univ) (hU₁ : ∀ x y, f₁ x = f₂ y → x ∈ U₁) :
    Function.Bijective (desc φ f₁ f₂ h) := by
  -- If `f₁ x = f₂ y`, then `x ∈ U₁`, and `f₂ (φ x) = f₁ x = f₂ y` gives `φ x = y`.
  have key (x : M₁) (y : M₂) (hxy : f₁ x = f₂ y) : inl φ x = inr φ y :=
    (inl_eq_inr_iff φ).2 ⟨hU₁ x y hxy, hinj₂ ((h ⟨x, hU₁ x y hxy⟩).trans hxy)⟩
  refine ⟨fun z w hzw ↦ ?_, fun p ↦ ?_⟩
  · rcases exists_inl_or_exists_inr φ z with ⟨x, rfl⟩ | ⟨y, rfl⟩ <;>
      rcases exists_inl_or_exists_inr φ w with ⟨x', rfl⟩ | ⟨y', rfl⟩ <;>
      simp only [desc_inl, desc_inr] at hzw
    · rw [hinj₁ hzw]
    · exact key x y' hzw
    · exact (key x' y hzw.symm).symm
    · rw [hinj₂ hzw]
  · rcases (mem_union _ _ _).1 (hcover ▸ mem_univ p) with ⟨x, rfl⟩ | ⟨y, rfl⟩
    exacts [⟨_, desc_inl φ h x⟩, ⟨_, desc_inr φ h y⟩]

end Desc

/-- The relation between the pieces `M₁` and `M₂` of the gluing is the graph of `φ`. -/
private theorem chartRel_false_true :
    (glueData φ).chartRel ⟨false⟩ ⟨true⟩ =
      {p : M₁ × M₂ | ∃ u : U₁, (u : M₁) = p.1 ∧ (φ u : M₂) = p.2} :=
  Set.ext fun p ↦ (glueData φ).mem_chartRel_iff.trans <| (inl_eq_inr_iff φ).trans <| by
    obtain ⟨x, y⟩ := p
    refine ⟨fun ⟨h, hy⟩ ↦ ⟨⟨x, h⟩, rfl, hy⟩, ?_⟩
    rintro ⟨u, hu, hy⟩
    simp only at hu hy
    subst hu hy
    exact ⟨u.property, rfl⟩

/-- The relation between the pieces `M₂` and `M₁` of the gluing is the graph of `φ`, read with
its two factors exchanged. -/
private theorem chartRel_true_false :
    (glueData φ).chartRel ⟨true⟩ ⟨false⟩ =
      Prod.swap ⁻¹' {p : M₁ × M₂ | ∃ u : U₁, (u : M₁) = p.1 ∧ (φ u : M₂) = p.2} :=
  Set.ext fun p ↦
    (glueData φ).swap_mem_chartRel_iff.symm.trans (Set.ext_iff.1 (chartRel_false_true φ) p.swap)

/-- **Hausdorff criterion for the glued space.** The glued space is Hausdorff exactly when `M₁`
and `M₂` are and the graph of `φ` is closed in `M₁ × M₂`. -/
theorem t2Space_iff_isClosed_graph : T2Space (GluedAlong φ) ↔ T2Space M₁ ∧ T2Space M₂ ∧
    IsClosed {p : M₁ × M₂ | ∃ u : U₁, (u : M₁) = p.1 ∧ (φ u : M₂) = p.2} := by
  -- `t2Space_iff_isClosed_chartRel` is stated for the glued space of `glueData φ`, which is
  -- `GluedAlong φ`, with its topology, by definition.
  rw [show T2Space (GluedAlong φ) ↔ T2Space (glueData φ).toGlueData.glued from Iff.rfl,
    (glueData φ).t2Space_iff_isClosed_chartRel]
  refine ⟨fun h ↦ ⟨?_, ?_, chartRel_false_true φ ▸ h ⟨false⟩ ⟨true⟩⟩, fun ⟨h₁, h₂, hg⟩ ↦ ?_⟩
  · exact t2_iff_isClosed_diagonal.2 ((glueData φ).chartRel_self ⟨false⟩ ▸ h ⟨false⟩ ⟨false⟩)
  · exact t2_iff_isClosed_diagonal.2 ((glueData φ).chartRel_self ⟨true⟩ ▸ h ⟨true⟩ ⟨true⟩)
  rintro ⟨_ | _⟩ ⟨_ | _⟩
  · exact (glueData φ).chartRel_self ⟨false⟩ ▸ t2_iff_isClosed_diagonal.1 h₁
  · exact chartRel_false_true φ ▸ hg
  · rw [chartRel_true_false]
    exact hg.preimage continuous_swap
  · exact (glueData φ).chartRel_self ⟨true⟩ ▸ t2_iff_isClosed_diagonal.1 h₂

/-- **Hausdorff criterion for the glued space.** If `M₁` and `M₂` are Hausdorff and the graph
of `φ`, as a subset of `M₁ × M₂`, is closed, then the glued space is Hausdorff. -/
theorem t2Space_of_isClosed_graph [T2Space M₁] [T2Space M₂]
    (hφ : IsClosed {p : M₁ × M₂ | ∃ u : U₁, (u : M₁) = p.1 ∧ (φ u : M₂) = p.2}) :
    T2Space (GluedAlong φ) :=
  (t2Space_iff_isClosed_graph φ).2 ⟨‹_›, ‹_›, hφ⟩

/-- **Hausdorff criterion for the glued space.** The glued space is Hausdorff exactly when `M₁`
and `M₂` are and any point `x` of `M₁` outside `U₁` and point `y` of `M₂` outside `U₂` have
neighbourhoods `A` and `B` such that `φ` maps no point of `U₁ ∩ A` into `B`. -/
theorem t2Space_iff : T2Space (GluedAlong φ) ↔ T2Space M₁ ∧ T2Space M₂ ∧
    ∀ x ∉ U₁, ∀ y ∉ U₂, ∃ A ∈ 𝓝 x, ∃ B ∈ 𝓝 y, ∀ z : U₁, (z : M₁) ∈ A → (φ z : M₂) ∉ B := by
  rw [t2Space_iff_isClosed_graph]
  refine and_congr_right fun h₁ ↦ and_congr_right fun h₂ ↦ ?_
  -- The pieces of `glueData φ` are `M₁` and `M₂` by definition (`starGlueData_U`).
  have : T2Space ((glueData φ).U ⟨false⟩) := h₁
  have : T2Space ((glueData φ).U ⟨true⟩) := h₂
  rw [← chartRel_false_true φ]
  refine ((glueData φ).isClosed_chartRel_iff (i := ⟨false⟩) (j := ⟨true⟩)).trans ?_
  have hne : (⟨false⟩ : ULift.{u} Bool) ≠ ⟨true⟩ := by simp
  -- The overlaps of the two pieces are `U₁` and `U₂`, and the transition between them is `φ`.
  have hU₁ (x : M₁) : x ∈ range ((glueData φ).f ⟨false⟩ ⟨true⟩) ↔ x ∈ U₁ :=
    (Set.ext_iff.1 ((glueData φ).preimage_range ⟨true⟩ ⟨false⟩) x).symm.trans
      (inl_mem_range_inr_iff φ)
  have hU₂ (y : M₂) : y ∈ range ((glueData φ).f ⟨true⟩ ⟨false⟩) ↔ y ∈ U₂ :=
    (Set.ext_iff.1 ((glueData φ).preimage_range ⟨false⟩ ⟨true⟩) y).symm.trans
      (inr_mem_range_inl_iff φ)
  have ht (z : starOverlap (glueMap φ) ⟨false⟩ ⟨true⟩)
      (hz : (z : partialHomeomorphGluePiece M₂ M₁ ⟨false⟩) ∈ glueSource M₂ U₁ ⟨false⟩) :
      (starTransition (glueMap φ) ⟨false⟩ ⟨true⟩ z : partialHomeomorphGluePiece M₂ M₁ ⟨true⟩) =
        (φ ⟨(z : partialHomeomorphGluePiece M₂ M₁ ⟨false⟩), hz⟩ : M₂) :=
    coe_starTransition_apply_of_ne hne z hz trivial
  refine forall_congr' fun x ↦ imp_congr (not_congr (hU₁ x)) <| forall_congr' fun y ↦
    imp_congr (not_congr (hU₂ y)) <| exists_congr fun A ↦ and_congr_right fun _ ↦
      exists_congr fun B ↦ and_congr_right fun _ ↦ ⟨fun h z hA hB ↦ ?_, fun h z hA hB ↦ ?_⟩
  · have hz : ((z : M₁) : partialHomeomorphGluePiece M₂ M₁ ⟨false⟩) ∈
        starOverlap (glueMap φ) ⟨false⟩ ⟨true⟩ := mem_starOverlap.2 (.inr ⟨z.property, trivial⟩)
    exact h ⟨_, hz⟩ hA ((ht ⟨_, hz⟩ z.property).symm.subst (motive := (· ∈ B)) hB)
  · have hz := starOverlap_le hne z.property
    exact h ⟨z.val, hz⟩ hA (ht z hz ▸ hB)

end GluedAlong

end Space

/-! ### Gluing along a diffeomorphism -/

section Smooth

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω}
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace H M₁] [TopologicalSpace M₂]
  [ChartedSpace H M₂] {U₁ : Opens M₁} {U₂ : Opens M₂}

namespace GluedAlong

section Homeomorph

variable (φ : U₁ ≃ₜ U₂)

/-- **The gluing along a `C^n` homeomorphism is compatible.** If `φ` and its inverse are
`C^n`, both attaching maps of the star gluing, the identity of `M₂` and `φ`, are `C^n` local
diffeomorphisms. -/
theorem isCompatible_glueData_of_contMDiff (hφ : ContMDiff I I n φ)
    (hφ' : ContMDiff I I n φ.symm) : (glueData φ).IsCompatible I n :=
  TauCeti.isCompatible_starGlueData fun
    | ⟨true⟩ => (Diffeomorph.refl I (⊤ : Opens M₂) n).isLocalDiffeomorph
    | ⟨false⟩ =>
      ({ φ.toEquiv with contMDiff_toFun := hφ, contMDiff_invFun := hφ' } :
        U₁ ≃ₘ^n⟮I, I⟯ U₂).isLocalDiffeomorph

variable {φ}

/-- For a `C^n` compatible gluing, the canonical map from `M₁` is a `C^n` local
diffeomorphism for the glued atlas. -/
theorem isLocalDiffeomorph_inl_of_isCompatible [IsManifold I n M₁] [IsManifold I n M₂]
    (h : (glueData φ).IsCompatible I n) : IsLocalDiffeomorph I I n (inl φ) :=
  h.isLocalDiffeomorph_ι ⟨false⟩

/-- For a `C^n` compatible gluing, the canonical map from `M₂` is a `C^n` local
diffeomorphism for the glued atlas. -/
theorem isLocalDiffeomorph_inr_of_isCompatible [IsManifold I n M₁] [IsManifold I n M₂]
    (h : (glueData φ).IsCompatible I n) : IsLocalDiffeomorph I I n (inr φ) :=
  h.isLocalDiffeomorph_ι ⟨true⟩

/-- For a `C^n` compatible gluing, the `C^n` diffeomorphism from the range of `inl` onto `M₁`,
the inverse of `inl`. -/
def rangeInlDiffeomorph [IsManifold I n M₁] [IsManifold I n M₂]
    (h : (glueData φ).IsCompatible I n) : rangeInl φ ≃ₘ^n⟮I, I⟯ M₁ :=
  -- `rangeInl φ` is by definition the open set `IsLocalDiffeomorph.image` of `inl φ`.
  ((isLocalDiffeomorph_inl_of_isCompatible h).diffeomorphOfInjective (inl_injective φ)).symm

section RangeInl

variable [IsManifold I n M₁] [IsManifold I n M₂] (h : (glueData φ).IsCompatible I n)

/-- The inverse of `rangeInlDiffeomorph h` is `inl`. -/
@[simp]
theorem coe_rangeInlDiffeomorph_symm_apply (x : M₁) :
    ((rangeInlDiffeomorph h).symm x : GluedAlong φ) = inl φ x :=
  IsLocalDiffeomorph.coe_diffeomorphOfInjective_apply _ _ x

/-- `inl` undoes `rangeInlDiffeomorph h`. -/
@[simp]
theorem inl_rangeInlDiffeomorph_apply (z : rangeInl φ) : inl φ (rangeInlDiffeomorph h z) = z :=
  IsLocalDiffeomorph.apply_diffeomorphOfInjective_symm (isLocalDiffeomorph_inl_of_isCompatible h)
    _ z

/-- `rangeInlDiffeomorph h` sends the point `inl x` to `x`. -/
@[simp]
theorem rangeInlDiffeomorph_mk_inl (x : M₁) :
    rangeInlDiffeomorph h ⟨inl φ x, inl_mem_rangeInl φ x⟩ = x :=
  inl_injective φ (inl_rangeInlDiffeomorph_apply h _)

end RangeInl

/-- For a `C^n` compatible gluing, the `C^n` diffeomorphism from the range of `inr` onto `M₂`,
the inverse of `inr`. -/
def rangeInrDiffeomorph [IsManifold I n M₁] [IsManifold I n M₂]
    (h : (glueData φ).IsCompatible I n) : rangeInr φ ≃ₘ^n⟮I, I⟯ M₂ :=
  -- `rangeInr φ` is by definition the open set `IsLocalDiffeomorph.image` of `inr φ`.
  ((isLocalDiffeomorph_inr_of_isCompatible h).diffeomorphOfInjective (inr_injective φ)).symm

section RangeInr

variable [IsManifold I n M₁] [IsManifold I n M₂] (h : (glueData φ).IsCompatible I n)

/-- The inverse of `rangeInrDiffeomorph h` is `inr`. -/
@[simp]
theorem coe_rangeInrDiffeomorph_symm_apply (y : M₂) :
    ((rangeInrDiffeomorph h).symm y : GluedAlong φ) = inr φ y :=
  IsLocalDiffeomorph.coe_diffeomorphOfInjective_apply _ _ y

/-- `inr` undoes `rangeInrDiffeomorph h`. -/
@[simp]
theorem inr_rangeInrDiffeomorph_apply (z : rangeInr φ) : inr φ (rangeInrDiffeomorph h z) = z :=
  IsLocalDiffeomorph.apply_diffeomorphOfInjective_symm (isLocalDiffeomorph_inr_of_isCompatible h)
    _ z

/-- `rangeInrDiffeomorph h` sends the point `inr y` to `y`. -/
@[simp]
theorem rangeInrDiffeomorph_mk_inr (y : M₂) :
    rangeInrDiffeomorph h ⟨inr φ y, inr_mem_rangeInr φ y⟩ = y :=
  inr_injective φ (inr_rangeInrDiffeomorph_apply h _)

end RangeInr

/-- For a `C^n` compatible gluing, a map out of the glued space is `C^m`, for `m ≤ n`, exactly
when its compositions with `inl` and `inr` are. -/
theorem contMDiff_iff_of_isCompatible [IsManifold I n M₁] [IsManifold I n M₂]
    (h : (glueData φ).IsCompatible I n) {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'} {N : Type*}
    [TopologicalSpace N] [ChartedSpace H' N] {m : ℕ∞ω} (hm : m ≤ n) {g : GluedAlong φ → N} :
    ContMDiff I I' m g ↔ ContMDiff I I' m (g ∘ inl φ) ∧ ContMDiff I I' m (g ∘ inr φ) := by
  -- The canonical maps of the pieces `false` and `true` are `inl φ` and `inr φ` by definition.
  refine (h.contMDiff_iff hm).trans ⟨fun hg ↦ ⟨hg ⟨false⟩, hg ⟨true⟩⟩, fun hg ↦ ?_⟩
  rintro ⟨_ | _⟩
  exacts [hg.1, hg.2]

/-- For a `C^n` compatible gluing, a map out of the glued space is a `C^n` local diffeomorphism
exactly when its compositions with `inl` and `inr` are. -/
theorem isLocalDiffeomorph_iff_of_isCompatible [IsManifold I n M₁] [IsManifold I n M₂]
    (h : (glueData φ).IsCompatible I n) {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'} {N : Type*}
    [TopologicalSpace N] [ChartedSpace H' N] {g : GluedAlong φ → N} :
    IsLocalDiffeomorph I I' n g ↔
      IsLocalDiffeomorph I I' n (g ∘ inl φ) ∧ IsLocalDiffeomorph I I' n (g ∘ inr φ) := by
  -- The canonical maps of the pieces `false` and `true` are `inl φ` and `inr φ` by definition.
  refine h.isLocalDiffeomorph_iff.trans ⟨fun hg ↦ ⟨hg ⟨false⟩, hg ⟨true⟩⟩, fun hg ↦ ?_⟩
  rintro ⟨_ | _⟩
  exacts [hg.1, hg.2]

end Homeomorph

variable (φ : U₁ ≃ₘ^n⟮I, I⟯ U₂)

/-- **The gluing along a diffeomorphism is compatible.** -/
theorem isCompatible_glueData : (glueData φ.toHomeomorph).IsCompatible I n :=
  isCompatible_glueData_of_contMDiff _ (by simpa using φ.contMDiff)
    (by simpa using φ.symm.contMDiff)

/-- The space glued from two `C^n` manifolds along a `C^n` diffeomorphism of open subsets is a
`C^n` manifold. -/
instance [IsManifold I n M₁] [IsManifold I n M₂] : IsManifold I n (GluedAlong φ.toHomeomorph) :=
  (isCompatible_glueData φ).isManifold

/-- The canonical map from `M₁` is a `C^n` local diffeomorphism for the glued atlas. -/
theorem isLocalDiffeomorph_inl [IsManifold I n M₁] [IsManifold I n M₂] :
    IsLocalDiffeomorph I I n (inl φ.toHomeomorph) :=
  isLocalDiffeomorph_inl_of_isCompatible (isCompatible_glueData φ)

/-- The canonical map from `M₂` is a `C^n` local diffeomorphism for the glued atlas. -/
theorem isLocalDiffeomorph_inr [IsManifold I n M₁] [IsManifold I n M₂] :
    IsLocalDiffeomorph I I n (inr φ.toHomeomorph) :=
  isLocalDiffeomorph_inr_of_isCompatible (isCompatible_glueData φ)

/-- A point of `U₁` and its image under the diffeomorphism `φ` have the same image in the glued
space. -/
@[simp]
theorem inr_diffeomorph_apply (x : U₁) :
    inr φ.toHomeomorph (φ x : M₂) = inl φ.toHomeomorph (x : M₁) := by
  rw [← Diffeomorph.coe_toHomeomorph, inr_apply]

/-- A point of `U₂` and its image under the inverse of the diffeomorphism `φ` have the same
image in the glued space. -/
@[simp]
theorem inl_diffeomorph_symm_apply (y : U₂) :
    inl φ.toHomeomorph (φ.symm y : M₁) = inr φ.toHomeomorph (y : M₂) := by
  rw [← Diffeomorph.coe_toHomeomorph_symm, inl_symm_apply]

/-- A point `x` of `M₁` and a point `y` of `M₂` have the same image in the space glued along the
diffeomorphism `φ` exactly when `x ∈ U₁` and `φ x = y`. -/
theorem inl_eq_inr_diffeomorph_iff {x : M₁} {y : M₂} :
    inl φ.toHomeomorph x = inr φ.toHomeomorph y ↔ ∃ h : x ∈ U₁, (φ ⟨x, h⟩ : M₂) = y := by
  rw [inl_eq_inr_iff, Diffeomorph.coe_toHomeomorph]

/-- A point `y` of `M₂` and a point `x` of `M₁` have the same image in the space glued along the
diffeomorphism `φ` exactly when `x ∈ U₁` and `φ x = y`. -/
theorem inr_eq_inl_diffeomorph_iff {y : M₂} {x : M₁} :
    inr φ.toHomeomorph y = inl φ.toHomeomorph x ↔ ∃ h : x ∈ U₁, (φ ⟨x, h⟩ : M₂) = y :=
  eq_comm.trans (inl_eq_inr_diffeomorph_iff φ)

/-- In the space glued along the inverse of a diffeomorphism `ψ : U₂ ≃ₘ U₁`, a point `p` of `U₂`
and its image `ψ p` have the same image. -/
@[simp]
theorem inl_toHomeomorph_symm_apply (ψ : U₂ ≃ₘ^n⟮I, I⟯ U₁) (p : U₂) :
    inl ψ.toHomeomorph.symm (ψ p : M₁) = inr ψ.toHomeomorph.symm (p : M₂) := by
  rw [← inl_symm_apply ψ.toHomeomorph.symm p, Homeomorph.symm_symm, Diffeomorph.coe_toHomeomorph]

section Desc

variable [IsManifold I n M₁] [IsManifold I n M₂] {E' : Type*} [NormedAddCommGroup E']
  [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H' X] {m : ℕ∞ω}

/-- **Smooth maps out of the glued manifold.** For `m ≤ n`, `C^m` maps `g₁ : M₁ → X` and
`g₂ : M₂ → X` that agree on the overlap, `g₂ (φ x) = g₁ x` for `x ∈ U₁`, define the `C^m` map on
`GluedAlong φ.toHomeomorph` that is `g₁` on `M₁` and `g₂` on `M₂` (`descContMDiffMap_inl`,
`descContMDiffMap_inr`). Its underlying continuous map is `desc`. -/
def descContMDiffMap (hm : m ≤ n) (g₁ : C^m⟮I, M₁; I', X⟯) (g₂ : C^m⟮I, M₂; I', X⟯)
    (h : ∀ x : U₁, g₂ (φ x) = g₁ x) : C^m⟮I, GluedAlong φ.toHomeomorph; I', X⟯ :=
  ⟨desc φ.toHomeomorph ⟨g₁, g₁.contMDiff.continuous⟩ ⟨g₂, g₂.contMDiff.continuous⟩ h,
    (contMDiff_iff_of_isCompatible (isCompatible_glueData φ) hm).2
      ⟨by
        convert g₁.contMDiff using 1
        exact funext (desc_inl φ.toHomeomorph h), by
        convert g₂.contMDiff using 1
        exact funext (desc_inr φ.toHomeomorph h)⟩⟩

variable {φ}

/-- The underlying map of the smooth map out of the glued manifold is that of `desc`. -/
theorem coe_descContMDiffMap (hm : m ≤ n) (g₁ : C^m⟮I, M₁; I', X⟯) (g₂ : C^m⟮I, M₂; I', X⟯)
    (h : ∀ x : U₁, g₂ (φ x) = g₁ x) :
    ⇑(descContMDiffMap φ hm g₁ g₂ h) =
      desc φ.toHomeomorph ⟨g₁, g₁.contMDiff.continuous⟩ ⟨g₂, g₂.contMDiff.continuous⟩ h :=
  (rfl)

/-- The smooth map out of the glued manifold is `g₁` on `M₁`. -/
@[simp]
theorem descContMDiffMap_inl (hm : m ≤ n) {g₁ : C^m⟮I, M₁; I', X⟯} {g₂ : C^m⟮I, M₂; I', X⟯}
    (h : ∀ x : U₁, g₂ (φ x) = g₁ x) (x : M₁) :
    descContMDiffMap φ hm g₁ g₂ h (inl φ.toHomeomorph x) = g₁ x :=
  desc_inl φ.toHomeomorph h x

/-- The smooth map out of the glued manifold is `g₂` on `M₂`. -/
@[simp]
theorem descContMDiffMap_inr (hm : m ≤ n) {g₁ : C^m⟮I, M₁; I', X⟯} {g₂ : C^m⟮I, M₂; I', X⟯}
    (h : ∀ x : U₁, g₂ (φ x) = g₁ x) (y : M₂) :
    descContMDiffMap φ hm g₁ g₂ h (inr φ.toHomeomorph y) = g₂ y :=
  desc_inr φ.toHomeomorph h y

variable {g₁ : M₁ → X} {g₂ : M₂ → X} (hg₁ : IsLocalDiffeomorph I I' n g₁)
  (hg₂ : IsLocalDiffeomorph I I' n g₂) (h : ∀ x : U₁, g₂ (φ x) = g₁ x)
  (hinj₁ : Function.Injective g₁) (hinj₂ : Function.Injective g₂)
  (hcover : range g₁ ∪ range g₂ = univ) (hU₁ : ∀ x y, g₁ x = g₂ y → x ∈ U₁)

/-- The smooth map out of the glued manifold given by two `C^n` local diffeomorphisms is a `C^n`
local diffeomorphism. -/
theorem isLocalDiffeomorph_descContMDiffMap :
    IsLocalDiffeomorph I I' n
      (descContMDiffMap φ le_rfl ⟨g₁, hg₁.contMDiff⟩ ⟨g₂, hg₂.contMDiff⟩ h) := by
  refine (isLocalDiffeomorph_iff_of_isCompatible (isCompatible_glueData φ)).2 ⟨?_, ?_⟩
  · convert hg₁ using 1
    exact funext (descContMDiffMap_inl le_rfl h)
  · convert hg₂ using 1
    exact funext (descContMDiffMap_inr le_rfl h)

/-- **Two open pieces covering a manifold.** Let `g₁ : M₁ → X` and `g₂ : M₂ → X` be injective
`C^n` local diffeomorphisms, that is `C^n` diffeomorphisms onto open subsets of `X`, whose ranges
cover `X`, that agree on the overlap, `g₂ (φ x) = g₁ x` for `x ∈ U₁`, and such that `g₁ x = g₂ y`
only for `x ∈ U₁`. Then the map that is `g₁` on `M₁` and `g₂` on `M₂` is a `C^n` diffeomorphism
from `GluedAlong φ.toHomeomorph` onto `X` (`descDiffeomorph_inl`, `descDiffeomorph_inr`). -/
def descDiffeomorph : GluedAlong φ.toHomeomorph ≃ₘ^n⟮I, I'⟯ X :=
  (isLocalDiffeomorph_descContMDiffMap hg₁ hg₂ h).diffeomorphOfBijective
    (coe_descContMDiffMap (φ := φ) le_rfl ⟨g₁, hg₁.contMDiff⟩ ⟨g₂, hg₂.contMDiff⟩ h ▸
      bijective_desc φ.toHomeomorph h hinj₁ hinj₂ hcover hU₁)

/-- The diffeomorphism onto `X` is the smooth map out of the glued manifold given by `g₁` and
`g₂`. -/
theorem coe_descDiffeomorph :
    ⇑(descDiffeomorph hg₁ hg₂ h hinj₁ hinj₂ hcover hU₁) =
      descContMDiffMap φ le_rfl ⟨g₁, hg₁.contMDiff⟩ ⟨g₂, hg₂.contMDiff⟩ h :=
  IsLocalDiffeomorph.coe_diffeomorphOfBijective _ _

/-- The diffeomorphism onto `X` is `g₁` on `M₁`. -/
@[simp]
theorem descDiffeomorph_inl (x : M₁) :
    descDiffeomorph hg₁ hg₂ h hinj₁ hinj₂ hcover hU₁ (inl φ.toHomeomorph x) = g₁ x :=
  (congrFun (coe_descDiffeomorph hg₁ hg₂ h hinj₁ hinj₂ hcover hU₁) _).trans
    (descContMDiffMap_inl le_rfl h x)

/-- The diffeomorphism onto `X` is `g₂` on `M₂`. -/
@[simp]
theorem descDiffeomorph_inr (y : M₂) :
    descDiffeomorph hg₁ hg₂ h hinj₁ hinj₂ hcover hU₁ (inr φ.toHomeomorph y) = g₂ y :=
  (congrFun (coe_descDiffeomorph hg₁ hg₂ h hinj₁ hinj₂ hcover hU₁) _).trans
    (descContMDiffMap_inr le_rfl h y)

/-- The inverse of the diffeomorphism onto `X` sends `g₁ x` to `inl x`. -/
@[simp]
theorem descDiffeomorph_symm_apply_left (x : M₁) :
    (descDiffeomorph hg₁ hg₂ h hinj₁ hinj₂ hcover hU₁).symm (g₁ x) = inl φ.toHomeomorph x := by
  rw [← descDiffeomorph_inl hg₁ hg₂ h hinj₁ hinj₂ hcover hU₁ x, Diffeomorph.symm_apply_apply]

/-- The inverse of the diffeomorphism onto `X` sends `g₂ y` to `inr y`. -/
@[simp]
theorem descDiffeomorph_symm_apply_right (y : M₂) :
    (descDiffeomorph hg₁ hg₂ h hinj₁ hinj₂ hcover hU₁).symm (g₂ y) = inr φ.toHomeomorph y := by
  rw [← descDiffeomorph_inr hg₁ hg₂ h hinj₁ hinj₂ hcover hU₁ y, Diffeomorph.symm_apply_apply]

end Desc

end GluedAlong

end Smooth

/-! ### Gluing differential forms -/

namespace GluedAlong

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace H M₁]
  [TopologicalSpace M₂] [ChartedSpace H M₂] [IsManifold I ∞ M₁] [IsManifold I ∞ M₂]
  {U₁ : Opens M₁} {U₂ : Opens M₂} (φ : U₁ ≃ₘ^∞⟮I, I⟯ U₂)
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

/-- Two forms on the glued space with the same pull-backs by `inl` and by `inr` are equal. -/
theorem roughForm_ext {α β : RoughForm I (GluedAlong φ.toHomeomorph) F k}
    (h₁ : mpullback I I (inl φ.toHomeomorph) α = mpullback I I (inl φ.toHomeomorph) β)
    (h₂ : mpullback I I (inr φ.toHomeomorph) α = mpullback I I (inr φ.toHomeomorph) β) :
    α = β := by
  funext z
  rcases exists_inl_or_exists_inr φ.toHomeomorph z with ⟨x, rfl⟩ | ⟨y, rfl⟩
  · exact (mpullback_apply_eq_mpullback_apply_iff
      ((isLocalDiffeomorph_inl φ x).isInvertible_mfderiv (by simp)).surjective).1 (congrFun h₁ x)
  · exact (mpullback_apply_eq_mpullback_apply_iff
      ((isLocalDiffeomorph_inr φ y).isInvertible_mfderiv (by simp)).surjective).1 (congrFun h₂ y)

/-- Two smooth forms on the glued space with the same pull-backs by `inl` and by `inr` are
equal. -/
theorem smoothForm_ext {α β : SmoothForm I (GluedAlong φ.toHomeomorph) F k}
    (h₁ : SmoothForm.mpullback (inl φ.toHomeomorph) (isLocalDiffeomorph_inl φ).contMDiff α =
      SmoothForm.mpullback (inl φ.toHomeomorph) (isLocalDiffeomorph_inl φ).contMDiff β)
    (h₂ : SmoothForm.mpullback (inr φ.toHomeomorph) (isLocalDiffeomorph_inr φ).contMDiff α =
      SmoothForm.mpullback (inr φ.toHomeomorph) (isLocalDiffeomorph_inr φ).contMDiff β) :
    α = β := by
  refine Subtype.ext (roughForm_ext φ ?_ ?_)
  · exact (SmoothForm.mpullback_eq_mpullback_iff _ _).1 h₁
  · exact (SmoothForm.mpullback_eq_mpullback_iff _ _).1 h₂

variable {φ}

/-- The form glued from `σ₁` and `σ₂` along `inl` and `inr` pulls back by `inl` to `σ₁`. -/
theorem mpullback_inl_glue (σ₁ : RoughForm I M₁ F k) (σ₂ : RoughForm I M₂ F k) :
    mpullback I I (inl φ.toHomeomorph)
      (RoughForm.glue I (inl φ.toHomeomorph) univ (inr φ.toHomeomorph) σ₁ σ₂) = σ₁ :=
  funext fun x ↦ RoughForm.mpullback_glue_apply_of_mem (inl_injective φ.toHomeomorph).injOn
    (mem_univ x) ((isLocalDiffeomorph_inl φ x).isInvertible_mfderiv (by simp))

/-- If `σ₁` and `σ₂` correspond on the overlap, `φ^*(σ₂|U₂) = σ₁|U₁`, the form glued from them
along `inl` and `inr` pulls back by `inr` to `σ₂`. -/
theorem mpullback_inr_glue {σ₁ : RoughForm I M₁ F k} {σ₂ : RoughForm I M₂ F k}
    (hσ : mpullback I I φ (mpullback I I Subtype.val σ₂) = mpullback I I Subtype.val σ₁) :
    mpullback I I (inr φ.toHomeomorph)
      (RoughForm.glue I (inl φ.toHomeomorph) univ (inr φ.toHomeomorph) σ₁ σ₂) = σ₂ := by
  funext y
  by_cases hz : ∃ x, inl φ.toHomeomorph x = inr φ.toHomeomorph y
  · obtain ⟨x, hx⟩ := hz
    obtain ⟨hxU, hy⟩ := (inl_eq_inr_diffeomorph_iff φ).1 hx
    subst hy
    set u : U₁ := ⟨x, hxU⟩
    have hd₁ : MDifferentiable I I (Subtype.val : U₂ → M₂) :=
      (contMDiff_subtypeVal (n := ∞)).mdifferentiable (by simp)
    have hd₂ : MDifferentiable I I (Subtype.val : U₁ → M₁) :=
      (contMDiff_subtypeVal (n := ∞)).mdifferentiable (by simp)
    have hφd : MDifferentiable I I φ := φ.contMDiff.mdifferentiable (by simp)
    rw [← mpullback_subtype_val_apply
        (mpullback I I (inr φ.toHomeomorph)
          (RoughForm.glue I (inl φ.toHomeomorph) univ (inr φ.toHomeomorph) σ₁ σ₂)) (φ u),
      ← mpullback_subtype_val_apply σ₂ (φ u)]
    refine (mpullback_apply_eq_mpullback_apply_iff (f := φ) (x := u)
      (φ.isInvertible_mfderiv (x := u) (by simp)).surjective).1 ?_
    rw [congrFun hσ u, ← mpullback_comp hd₁ ((isLocalDiffeomorph_inr φ).mdifferentiable
      (by simp)), ← mpullback_comp hφd (((isLocalDiffeomorph_inr φ).mdifferentiable
      (by simp)).comp hd₁)]
    have hcomp : (inr φ.toHomeomorph ∘ Subtype.val) ∘ φ = inl φ.toHomeomorph ∘ Subtype.val := by
      funext v; exact inr_diffeomorph_apply φ v
    rw [hcomp, mpullback_comp hd₂ ((isLocalDiffeomorph_inl φ).mdifferentiable (by simp)),
      mpullback_inl_glue]
  · exact RoughForm.mpullback_glue_apply_of_notMem (inr_injective φ.toHomeomorph)
      (fun ⟨x, _, hx⟩ ↦ hz ⟨x, hx⟩)
      ((isLocalDiffeomorph_inr φ y).isInvertible_mfderiv (by simp))

variable (φ) in
/-- **Gluing forms.** Smooth forms `σ₁` on `M₁` and `σ₂` on `M₂` whose restrictions to the
overlaps correspond under `φ`, `φ^*(σ₂|U₂) = σ₁|U₁`, glue to the smooth form on
`GluedAlong φ.toHomeomorph` whose pull-backs by `inl` and `inr` are `σ₁` and `σ₂`
(`mpullback_inl_gluedForm`, `mpullback_inr_gluedForm`). It is the only such form
(`eq_gluedForm_iff`). -/
def gluedForm (σ₁ : SmoothForm I M₁ F k) (σ₂ : SmoothForm I M₂ F k)
    (hσ : SmoothForm.mpullback φ φ.contMDiff
        (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal σ₂) =
      SmoothForm.mpullback Subtype.val contMDiff_subtypeVal σ₁) :
    SmoothForm I (GluedAlong φ.toHomeomorph) F k :=
  ⟨RoughForm.glue I (inl φ.toHomeomorph) univ (inr φ.toHomeomorph) σ₁.val σ₂.val,
    IsSmoothForm.mem_smoothBundleForms <|
      RoughForm.isSmoothForm_glue (by simp) isOpen_univ (inl_injective φ.toHomeomorph).injOn
        (fun x ↦ isLocalDiffeomorph_inl φ x) σ₁.isSmoothForm σ₂.isSmoothForm
        fun z hz ↦ by
          obtain ⟨y, rfl⟩ := (exists_inl_or_exists_inr φ.toHomeomorph z).resolve_left
            fun ⟨x, hx⟩ ↦ hz ⟨x, mem_univ x, hx⟩
          refine ⟨y, rfl, isLocalDiffeomorph_inr φ y, Filter.Eventually.of_forall fun r ↦ ?_⟩
          rw [mpullback_inr_glue (by
            simpa only [SmoothForm.coe_mpullback] using congrArg Subtype.val hσ)]⟩

variable {σ₁ : SmoothForm I M₁ F k} {σ₂ : SmoothForm I M₂ F k}
  {hσ : SmoothForm.mpullback φ φ.contMDiff
      (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal σ₂) =
    SmoothForm.mpullback Subtype.val contMDiff_subtypeVal σ₁}

/-- The glued form pulls back by `inl` to the form on `M₁`. -/
@[simp]
theorem mpullback_inl_gluedForm :
    SmoothForm.mpullback (inl φ.toHomeomorph) (isLocalDiffeomorph_inl φ).contMDiff
      (gluedForm φ σ₁ σ₂ hσ) = σ₁ :=
  (SmoothForm.mpullback_eq_iff _).2 (mpullback_inl_glue _ _)

/-- The glued form pulls back by `inr` to the form on `M₂`. -/
@[simp]
theorem mpullback_inr_gluedForm :
    SmoothForm.mpullback (inr φ.toHomeomorph) (isLocalDiffeomorph_inr φ).contMDiff
      (gluedForm φ σ₁ σ₂ hσ) = σ₂ :=
  (SmoothForm.mpullback_eq_iff _).2 <| mpullback_inr_glue <| by
    simpa only [SmoothForm.coe_mpullback] using congrArg Subtype.val hσ

/-- The glued form is the only form on `GluedAlong φ.toHomeomorph` whose pull-backs by `inl` and
`inr` are the forms on `M₁` and `M₂`. -/
theorem eq_gluedForm_iff {α : SmoothForm I (GluedAlong φ.toHomeomorph) F k} :
    α = gluedForm φ σ₁ σ₂ hσ ↔
      SmoothForm.mpullback (inl φ.toHomeomorph) (isLocalDiffeomorph_inl φ).contMDiff α = σ₁ ∧
        SmoothForm.mpullback (inr φ.toHomeomorph) (isLocalDiffeomorph_inr φ).contMDiff α =
          σ₂ := by
  refine ⟨?_, fun ⟨h₁, h₂⟩ ↦ smoothForm_ext φ ?_ ?_⟩
  · rintro rfl
    exact ⟨mpullback_inl_gluedForm, mpullback_inr_gluedForm⟩
  · rw [h₁, mpullback_inl_gluedForm]
  · rw [h₂, mpullback_inr_gluedForm]

/-- Pulling the restriction of a form `α` on the glued space to the range of `inl` back by the
inverse of `rangeInlDiffeomorph h`, which is `inl`, is pulling `α` back by `inl`. -/
@[simp]
theorem mpullback_rangeInlDiffeomorph_symm (h : (glueData φ.toHomeomorph).IsCompatible I ∞)
    (α : SmoothForm I (GluedAlong φ.toHomeomorph) F k) :
    SmoothForm.mpullback (rangeInlDiffeomorph h).symm (rangeInlDiffeomorph h).symm.contMDiff
        (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal α) =
      SmoothForm.mpullback (inl φ.toHomeomorph) (isLocalDiffeomorph_inl φ).contMDiff α :=
  SmoothForm.mpullback_diffeomorphOfInjective_mpullback_subtype_val
    (isLocalDiffeomorph_inl_of_isCompatible h) (inl_injective _) α

/-- The inverse of `rangeInlDiffeomorph h` pulls the restriction of the glued form to the range
of `inl` back to the form on `M₁`. -/
theorem mpullback_rangeInlDiffeomorph_symm_gluedForm
    (h : (glueData φ.toHomeomorph).IsCompatible I ∞) :
    SmoothForm.mpullback (rangeInlDiffeomorph h).symm (rangeInlDiffeomorph h).symm.contMDiff
        (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal (gluedForm φ σ₁ σ₂ hσ)) = σ₁ := by
  rw [mpullback_rangeInlDiffeomorph_symm, mpullback_inl_gluedForm]

/-- Pulling the restriction of a form `α` on the glued space to the range of `inr` back by the
inverse of `rangeInrDiffeomorph h`, which is `inr`, is pulling `α` back by `inr`. -/
@[simp]
theorem mpullback_rangeInrDiffeomorph_symm (h : (glueData φ.toHomeomorph).IsCompatible I ∞)
    (α : SmoothForm I (GluedAlong φ.toHomeomorph) F k) :
    SmoothForm.mpullback (rangeInrDiffeomorph h).symm (rangeInrDiffeomorph h).symm.contMDiff
        (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal α) =
      SmoothForm.mpullback (inr φ.toHomeomorph) (isLocalDiffeomorph_inr φ).contMDiff α :=
  SmoothForm.mpullback_diffeomorphOfInjective_mpullback_subtype_val
    (isLocalDiffeomorph_inr_of_isCompatible h) (inr_injective _) α

/-- The inverse of `rangeInrDiffeomorph h` pulls the restriction of the glued form to the range
of `inr` back to the form on `M₂`. -/
theorem mpullback_rangeInrDiffeomorph_symm_gluedForm
    (h : (glueData φ.toHomeomorph).IsCompatible I ∞) :
    SmoothForm.mpullback (rangeInrDiffeomorph h).symm (rangeInrDiffeomorph h).symm.contMDiff
        (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal (gluedForm φ σ₁ σ₂ hσ)) = σ₂ := by
  rw [mpullback_rangeInrDiffeomorph_symm, mpullback_inr_gluedForm]

variable (φ) in
/-- A smooth form on the glued space is closed exactly when its pull-backs by `inl` and `inr`
are. -/
theorem isClosed_iff_isClosed_mpullback {α : SmoothForm I (GluedAlong φ.toHomeomorph) F k} :
    α.IsClosed ↔
      (SmoothForm.mpullback (inl φ.toHomeomorph) (isLocalDiffeomorph_inl φ).contMDiff
          α).IsClosed ∧
        (SmoothForm.mpullback (inr φ.toHomeomorph) (isLocalDiffeomorph_inr φ).contMDiff
          α).IsClosed := by
  refine ⟨fun h ↦ ⟨h.mpullback _ _, h.mpullback _ _⟩, fun ⟨h₁, h₂⟩ ↦ ?_⟩
  rw [SmoothForm.isClosed_def, ← mextDerivₗ_apply, SmoothForm.mextDerivₗ_mpullback,
    SmoothForm.coe_mpullback] at h₁ h₂
  rw [SmoothForm.isClosed_def, ← mextDerivₗ_apply]
  refine roughForm_ext φ ?_ ?_
  · rw [h₁, mpullback_zero]
  · rw [h₂, mpullback_zero]

/-- The glued form is closed exactly when the forms on `M₁` and `M₂` are. -/
@[simp]
theorem isClosed_gluedForm_iff :
    (gluedForm φ σ₁ σ₂ hσ).IsClosed ↔ σ₁.IsClosed ∧ σ₂.IsClosed := by
  rw [isClosed_iff_isClosed_mpullback, mpullback_inl_gluedForm, mpullback_inr_gluedForm]

section TwoForm

variable (φ) in
/-- A two-form on the glued space is nondegenerate exactly when its pull-backs by `inl` and `inr`
are. -/
theorem isNondegenerate_iff_isNondegenerate_mpullback
    {α : SmoothTwoForm I (GluedAlong φ.toHomeomorph)} :
    α.IsNondegenerate ↔
      SmoothTwoForm.IsNondegenerate
          (SmoothForm.mpullback (inl φ.toHomeomorph) (isLocalDiffeomorph_inl φ).contMDiff α) ∧
        SmoothTwoForm.IsNondegenerate
          (SmoothForm.mpullback (inr φ.toHomeomorph) (isLocalDiffeomorph_inr φ).contMDiff α) := by
  refine ⟨fun h ↦ ⟨h.isNondegenerate_mpullback_of_isLocalDiffeomorph (isLocalDiffeomorph_inl φ),
    h.isNondegenerate_mpullback_of_isLocalDiffeomorph (isLocalDiffeomorph_inr φ)⟩,
    fun ⟨h₁, h₂⟩ ↦ SmoothTwoForm.isNondegenerate_def.2 fun z ↦ ?_⟩
  rcases exists_inl_or_exists_inr φ.toHomeomorph z with ⟨x, rfl⟩ | ⟨y, rfl⟩
  · exact (SmoothTwoForm.nondegenerate_bilinFormAt_iff_of_isInvertible_mfderiv
      ((isLocalDiffeomorph_inl φ x).isInvertible_mfderiv (by simp))
      (congrFun (SmoothForm.coe_mpullback _ _ _) x).symm).2
      (h₁.nondegenerate_bilinFormAt x)
  · exact (SmoothTwoForm.nondegenerate_bilinFormAt_iff_of_isInvertible_mfderiv
      ((isLocalDiffeomorph_inr φ y).isInvertible_mfderiv (by simp))
      (congrFun (SmoothForm.coe_mpullback _ _ _) y).symm).2
      (h₂.nondegenerate_bilinFormAt y)

variable (φ) in
/-- A two-form on the glued space is symplectic exactly when its pull-backs by `inl` and `inr`
are. -/
theorem isSymplectic_iff_isSymplectic_mpullback
    {α : SmoothTwoForm I (GluedAlong φ.toHomeomorph)} :
    α.IsSymplectic ↔
      SmoothTwoForm.IsSymplectic
          (SmoothForm.mpullback (inl φ.toHomeomorph) (isLocalDiffeomorph_inl φ).contMDiff α) ∧
        SmoothTwoForm.IsSymplectic
          (SmoothForm.mpullback (inr φ.toHomeomorph) (isLocalDiffeomorph_inr φ).contMDiff α) := by
  refine ⟨fun h ↦ ?_, fun ⟨h₁, h₂⟩ ↦
    ⟨(isClosed_iff_isClosed_mpullback φ).2 ⟨h₁.isClosed, h₂.isClosed⟩,
      (isNondegenerate_iff_isNondegenerate_mpullback φ).2
        ⟨h₁.isNondegenerate, h₂.isNondegenerate⟩⟩⟩
  obtain ⟨hc₁, hc₂⟩ := (isClosed_iff_isClosed_mpullback φ).1 h.isClosed
  obtain ⟨hn₁, hn₂⟩ := (isNondegenerate_iff_isNondegenerate_mpullback φ).1 h.isNondegenerate
  exact ⟨⟨hc₁, hn₁⟩, ⟨hc₂, hn₂⟩⟩

variable {σ₁ : SmoothTwoForm I M₁} {σ₂ : SmoothTwoForm I M₂}
  {hσ : SmoothForm.mpullback φ φ.contMDiff
      (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal σ₂) =
    SmoothForm.mpullback Subtype.val contMDiff_subtypeVal σ₁}

/-- The glued two-form is nondegenerate exactly when the two-forms on `M₁` and `M₂` are. -/
@[simp]
theorem isNondegenerate_gluedForm_iff :
    SmoothTwoForm.IsNondegenerate (gluedForm φ σ₁ σ₂ hσ) ↔
      σ₁.IsNondegenerate ∧ σ₂.IsNondegenerate := by
  rw [isNondegenerate_iff_isNondegenerate_mpullback, mpullback_inl_gluedForm,
    mpullback_inr_gluedForm]

/-- The glued two-form is symplectic exactly when the two-forms on `M₁` and `M₂` are. -/
@[simp]
theorem isSymplectic_gluedForm_iff :
    SmoothTwoForm.IsSymplectic (gluedForm φ σ₁ σ₂ hσ) ↔ σ₁.IsSymplectic ∧ σ₂.IsSymplectic := by
  rw [isSymplectic_iff_isSymplectic_mpullback, mpullback_inl_gluedForm,
    mpullback_inr_gluedForm]

end TwoForm

section Desc

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] {H' : Type*}
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} {X : Type*} [TopologicalSpace X]
  [ChartedSpace H' X] [IsManifold I' ∞ X]

variable (φ) in
/-- The pull-backs of a form `σ` on `X` by smooth maps `g₁ : M₁ → X` and `g₂ : M₂ → X` that agree
on the overlap, `g₂ (φ x) = g₁ x` for `x ∈ U₁`, correspond on the overlap:
`φ^*((g₂^* σ)|U₂) = (g₁^* σ)|U₁`. So they glue (`gluedForm`). -/
theorem mpullback_overlap_mpullback {g₁ : M₁ → X} {g₂ : M₂ → X} (hg₁ : ContMDiff I I' ∞ g₁)
    (hg₂ : ContMDiff I I' ∞ g₂) (h : ∀ x : U₁, g₂ (φ x) = g₁ x) (σ : SmoothForm I' X F k) :
    SmoothForm.mpullback φ φ.contMDiff
        (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal (SmoothForm.mpullback g₂ hg₂ σ)) =
      SmoothForm.mpullback Subtype.val contMDiff_subtypeVal (SmoothForm.mpullback g₁ hg₁ σ) := by
  simp only [SmoothForm.mpullback_mpullback]
  exact SmoothForm.mpullback_congr _ _ (funext h) σ

/-- The pull-back of a form `σ` on `X` by the smooth map out of the glued manifold given by `g₁`
and `g₂` is the form glued from `g₁^* σ` and `g₂^* σ`. -/
theorem mpullback_descContMDiffMap {g₁ : C^∞⟮I, M₁; I', X⟯} {g₂ : C^∞⟮I, M₂; I', X⟯}
    (h : ∀ x : U₁, g₂ (φ x) = g₁ x) (σ : SmoothForm I' X F k) :
    SmoothForm.mpullback (descContMDiffMap φ le_rfl g₁ g₂ h)
        (descContMDiffMap φ le_rfl g₁ g₂ h).contMDiff σ =
      gluedForm φ (SmoothForm.mpullback g₁ g₁.contMDiff σ)
        (SmoothForm.mpullback g₂ g₂.contMDiff σ)
        (mpullback_overlap_mpullback φ g₁.contMDiff g₂.contMDiff h σ) := by
  rw [eq_gluedForm_iff, SmoothForm.mpullback_mpullback, SmoothForm.mpullback_mpullback]
  exact ⟨SmoothForm.mpullback_congr _ _ (funext (descContMDiffMap_inl le_rfl h)) σ,
    SmoothForm.mpullback_congr _ _ (funext (descContMDiffMap_inr le_rfl h)) σ⟩

/-- The pull-back of a form `σ` on `X` by the diffeomorphism `descDiffeomorph` onto `X` is the
form glued from `g₁^* σ` and `g₂^* σ`. In particular, it carries a symplectic form on `X` to a
glued symplectic form (`isSymplectic_gluedForm_iff`). -/
theorem mpullback_descDiffeomorph {g₁ : M₁ → X} {g₂ : M₂ → X}
    (hg₁ : IsLocalDiffeomorph I I' ∞ g₁) (hg₂ : IsLocalDiffeomorph I I' ∞ g₂)
    (h : ∀ x : U₁, g₂ (φ x) = g₁ x) (hinj₁ : Function.Injective g₁)
    (hinj₂ : Function.Injective g₂) (hcover : range g₁ ∪ range g₂ = univ)
    (hU₁ : ∀ x y, g₁ x = g₂ y → x ∈ U₁) (σ : SmoothForm I' X F k) :
    SmoothForm.mpullback (descDiffeomorph hg₁ hg₂ h hinj₁ hinj₂ hcover hU₁)
        (descDiffeomorph hg₁ hg₂ h hinj₁ hinj₂ hcover hU₁).contMDiff σ =
      gluedForm φ (SmoothForm.mpullback g₁ hg₁.contMDiff σ)
        (SmoothForm.mpullback g₂ hg₂.contMDiff σ)
        (mpullback_overlap_mpullback φ hg₁.contMDiff hg₂.contMDiff h σ) :=
  (SmoothForm.mpullback_congr _ _ (coe_descDiffeomorph hg₁ hg₂ h hinj₁ hinj₂ hcover hU₁) σ).trans
    (mpullback_descContMDiffMap (g₁ := ⟨g₁, hg₁.contMDiff⟩) (g₂ := ⟨g₂, hg₂.contMDiff⟩) h σ)

end Desc

end GluedAlong

end SymplecticGeometry
