/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Topology.Category.TopCat.GlueData.Pair
public import TauCeti.Geometry.Manifold.Gluing.GlueData
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.Basic

/-!
# Gluing two manifolds along open subsets

Let `M₁` and `M₂` be charted spaces over one model `I`, let `U₁` and `U₂` be open subsets of
them, and let `φ : U₁ ≃ₘ^n⟮I, I⟯ U₂` be a `C^n` diffeomorphism. The glued space
`SymplecticGeometry.GluedAlong φ` is `M₁ ⊔ M₂` with each `x ∈ U₁` identified with `φ x ∈ U₂`. It
is the glued space of the two-piece gluing data `TopCat.GlueData.ofHomeomorph` along the
homeomorphism underlying `φ`, and it comes with the canonical open embeddings
`GluedAlong.inl : M₁ → GluedAlong φ` and `GluedAlong.inr : M₂ → GluedAlong φ`, whose ranges
cover it. A point `x` of `M₁` and a point `y` of `M₂` have the same image exactly when `x ∈ U₁`
and `φ x = y` (`GluedAlong.inl_eq_inr_iff`).

Both maps out of an overlap are local diffeomorphisms: the inclusions of `U₁` and `U₂`, and `φ`
and its inverse. So the gluing is compatible in the sense of Tau Ceti's
`TopCat.GlueData.IsCompatible`, and `TopCat.GlueData.chartedSpace` and
`TopCat.GlueData.IsCompatible.isManifold` make `GluedAlong φ` a charted space over the model of
`M₁` and `M₂`, and a `C^n` manifold when they are, for which `inl` and `inr` are `C^n` local
diffeomorphisms. The glued space need not be Hausdorff even when `M₁` and `M₂` are; it is when,
moreover, the graph of `φ` is closed in `M₁ × M₂`.

## Main definitions

* `SymplecticGeometry.GluedAlong φ`: the space glued from `M₁` and `M₂` along `φ`.
* `SymplecticGeometry.GluedAlong.inl`, `SymplecticGeometry.GluedAlong.inr`: the canonical maps
  from `M₁` and `M₂`.

## Main results

* `SymplecticGeometry.GluedAlong.isOpenEmbedding_inl`, `isOpenEmbedding_inr`,
  `range_inl_union_range_inr`, `inl_eq_inr_iff`: the topology of the glued space.
* `SymplecticGeometry.GluedAlong.isLocalDiffeomorph_inl`, `isLocalDiffeomorph_inr`: the
  canonical maps are `C^n` local diffeomorphisms for the glued atlas.
* `SymplecticGeometry.GluedAlong.t2Space_of_isClosed_graph`: the glued space is Hausdorff when
  `M₁` and `M₂` are and the graph of `φ` is closed in `M₁ × M₂`.

The compatibility proof follows Tau Ceti's `TauCeti.isCompatible_doubleGlueData`, which treats
the gluing of two copies of one space along an open subset by the identity.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, Chapter 1 (the smooth manifold chart lemma).
-/

public section

open Set Topology TopologicalSpace CategoryTheory
open scoped Manifold ContDiff

noncomputable section

namespace SymplecticGeometry

universe u

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω}
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace H M₁] [TopologicalSpace M₂]
  [ChartedSpace H M₂] {U₁ : Opens M₁} {U₂ : Opens M₂} (φ : U₁ ≃ₘ^n⟮I, I⟯ U₂)

namespace GluedAlong

/-- The gluing data of `GluedAlong φ`: the pieces `M₁` and `M₂`, glued along the homeomorphism
underlying `φ`. -/
@[expose] def glueData : TopCat.GlueData.{u} := TopCat.GlueData.ofHomeomorph φ.toHomeomorph

/-- Each piece of the gluing carries its own atlas: `M₁` for `false` and `M₂` for `true`. -/
instance instChartedSpaceGlueDataU : ∀ i : (glueData φ).J, ChartedSpace H ((glueData φ).U i)
  | ⟨false⟩ => inferInstanceAs (ChartedSpace H M₁)
  | ⟨true⟩ => inferInstanceAs (ChartedSpace H M₂)

/-- Each piece of the gluing of two `C^n` manifolds is a `C^n` manifold. -/
instance instIsManifoldGlueDataU [IsManifold I n M₁] [IsManifold I n M₂] :
    ∀ i : (glueData φ).J, IsManifold I n ((glueData φ).U i)
  | ⟨false⟩ => inferInstanceAs (IsManifold I n M₁)
  | ⟨true⟩ => inferInstanceAs (IsManifold I n M₂)

/-- Each overlap of the gluing carries its atlas as an open subset of its piece. -/
instance instChartedSpaceGlueDataV (p : (glueData φ).J × (glueData φ).J) :
    ChartedSpace H ((glueData φ).V p) :=
  -- `show` gives the overlap the type `Opens ((glueData φ).U p.1)`, so that the atlas
  -- `instChartedSpaceGlueDataU` of the piece applies.
  Opens.instChartedSpace (show Opens ((glueData φ).U p.1) from
    TopCat.GlueData.ofHomeomorphOverlap U₁ U₂ p.1 p.2)

/-- **The gluing along a diffeomorphism is compatible.** The maps out of an overlap are the
inclusion of an open subset, and `φ` or its inverse, so they are `C^n` local diffeomorphisms. -/
theorem isCompatible_glueData : (glueData φ).IsCompatible I n := by
  -- By definition (`TopCat.GlueData.ofHomeomorph_f`), each map `f i j` is the inclusion of an
  -- open subset, and the transitions are the identity, `φ` and `φ.symm`.
  refine .of_isLocalDiffeomorph_t (fun i j ↦ TauCeti.isLocalDiffeomorph_subtype_val) ?_
  rintro ⟨_ | _⟩ ⟨_ | _⟩
  · exact isLocalDiffeomorph_id
  · exact φ.isLocalDiffeomorph
  · exact φ.symm.isLocalDiffeomorph
  · exact isLocalDiffeomorph_id

end GluedAlong

/-- The space glued from `M₁` and `M₂` by identifying each point `x` of the open subset `U₁`
with the point `φ x` of `U₂`. -/
@[expose] def GluedAlong : Type u := (GluedAlong.glueData φ).toGlueData.glued

namespace GluedAlong

instance : TopologicalSpace (GluedAlong φ) :=
  inferInstanceAs (TopologicalSpace (glueData φ).toGlueData.glued)

/-- The atlas of `GluedAlong φ`, transported from the atlases of `M₁` and `M₂` along the
canonical maps. -/
instance : ChartedSpace H (GluedAlong φ) := (glueData φ).chartedSpace H

/-- The space glued from two `C^n` manifolds along a `C^n` diffeomorphism of open subsets is a
`C^n` manifold. -/
instance [IsManifold I n M₁] [IsManifold I n M₂] : IsManifold I n (GluedAlong φ) :=
  (isCompatible_glueData φ).isManifold

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

/-- Every point of the glued space comes from `M₁` or from `M₂`. -/
theorem range_inl_union_range_inr : range (inl φ) ∪ range (inr φ) = univ :=
  eq_univ_of_forall fun z ↦
    (TopCat.GlueData.ofHomeomorph_ι_jointly_surjective φ.toHomeomorph z).imp id id

/-- A point `x` of `M₁` and a point `y` of `M₂` have the same image in the glued space exactly
when `x ∈ U₁` and `φ x = y`. -/
@[simp, grind =]
theorem inl_eq_inr_iff {x : M₁} {y : M₂} :
    inl φ x = inr φ y ↔ ∃ h : x ∈ U₁, (φ ⟨x, h⟩ : M₂) = y :=
  TopCat.GlueData.ofHomeomorph_ι_false_eq_ι_true_iff φ.toHomeomorph

/-- A point `y` of `M₂` and a point `x` of `M₁` have the same image in the glued space exactly
when `x ∈ U₁` and `φ x = y`. -/
@[simp, grind =]
theorem inr_eq_inl_iff {y : M₂} {x : M₁} :
    inr φ y = inl φ x ↔ ∃ h : x ∈ U₁, (φ ⟨x, h⟩ : M₂) = y :=
  eq_comm.trans (inl_eq_inr_iff φ)

/-- A point of `U₁` and its image under `φ` have the same image in the glued space. -/
@[simp]
theorem inr_apply (x : U₁) : inr φ (φ x : M₂) = inl φ (x : M₁) :=
  ((inl_eq_inr_iff φ).2 ⟨x.property, rfl⟩).symm

/-- A point of `U₂` and its image under `φ.symm` have the same image in the glued space. -/
@[simp]
theorem inl_symm_apply (y : U₂) : inl φ (φ.symm y : M₁) = inr φ (y : M₂) := by
  rw [← inr_apply, Diffeomorph.apply_symm_apply]

/-- **Hausdorff criterion for the glued space.** If `M₁` and `M₂` are Hausdorff and the graph
of `φ`, as a subset of `M₁ × M₂`, is closed, then the glued space is Hausdorff. -/
theorem t2Space_of_isClosed_graph [T2Space M₁] [T2Space M₂]
    (hφ : IsClosed {p : M₁ × M₂ | ∃ u : U₁, (u : M₁) = p.1 ∧ (φ u : M₂) = p.2}) :
    T2Space (GluedAlong φ) := by
  -- `GluedAlong φ` is by definition the glued space of `glueData φ`.
  refine TopCat.GlueData.ofHomeomorph_t2Space_of_isClosed_range φ.toHomeomorph ?_
  convert hφ using 1
  ext ⟨x, y⟩
  simp [Prod.ext_iff]

/-- The canonical map from `M₁` is a `C^n` local diffeomorphism for the glued atlas. -/
theorem isLocalDiffeomorph_inl [IsManifold I n M₁] [IsManifold I n M₂] :
    IsLocalDiffeomorph I I n (inl φ) :=
  (isCompatible_glueData φ).isLocalDiffeomorph_ι ⟨false⟩

/-- The canonical map from `M₂` is a `C^n` local diffeomorphism for the glued atlas. -/
theorem isLocalDiffeomorph_inr [IsManifold I n M₁] [IsManifold I n M₂] :
    IsLocalDiffeomorph I I n (inr φ) :=
  (isCompatible_glueData φ).isLocalDiffeomorph_ι ⟨true⟩

end GluedAlong

end SymplecticGeometry
