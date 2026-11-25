/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Topology.Category.TopCat.GlueData.Pair
public import TauCeti.Geometry.Manifold.Gluing.GlueData
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Pullback.LocalDiffeomorph
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.DifferentialForm.Opens

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
`Geometry/Symplectic/Liouville/Completion.lean`, is glued by the same construction.

## Main definitions

* `SymplecticGeometry.GluedAlong φ`: the space glued from `M₁` and `M₂` along `φ`.
* `SymplecticGeometry.GluedAlong.inl`, `SymplecticGeometry.GluedAlong.inr`: the canonical maps
  from `M₁` and `M₂`.
* `SymplecticGeometry.GluedAlong.desc`: the continuous map on the glued space given by continuous
  maps on `M₁` and `M₂` that agree on the overlap.
* `SymplecticGeometry.GluedAlong.gluedForm`: the form glued from forms on `M₁` and `M₂` that
  agree on the overlap.

## Main results

* `SymplecticGeometry.GluedAlong.isOpenEmbedding_inl`, `isOpenEmbedding_inr`,
  `range_inl_union_range_inr`, `exists_inl_or_exists_inr`, `inl_eq_inr_iff`: the topology of
  the glued space.
* `SymplecticGeometry.GluedAlong.isLocalDiffeomorph_inl`, `isLocalDiffeomorph_inr`: the
  canonical maps are `C^n` local diffeomorphisms for the glued atlas.
* `SymplecticGeometry.GluedAlong.t2Space_iff`: when the glued space is Hausdorff.
* `SymplecticGeometry.GluedAlong.t2Space_of_isClosed_graph`: the glued space is Hausdorff when
  `M₁` and `M₂` are and the graph of `φ` is closed in `M₁ × M₂`.
* `SymplecticGeometry.GluedAlong.mpullback_inl_gluedForm`, `mpullback_inr_gluedForm`,
  `eq_gluedForm_iff`: the glued form is the unique form with the given pull-backs.
* `SymplecticGeometry.GluedAlong.isClosed_gluedForm_iff`, `isNondegenerate_gluedForm_iff`,
  `isSymplectic_gluedForm_iff`: the glued form is closed, nondegenerate or symplectic exactly
  when both forms are.

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

section Space

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

/-- Every point of the glued space is `inl x` for a point `x` of `M₁` or `inr y` for a point `y`
of `M₂`. -/
theorem exists_inl_or_exists_inr (z : GluedAlong φ) : (∃ x, inl φ x = z) ∨ ∃ y, inr φ y = z :=
  (range_inl_union_range_inr φ).ge (mem_univ z)

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

section Desc

variable {X : Type*} {f₁ : M₁ → X} {f₂ : M₂ → X}

open Classical in
/-- The function on the glued space that is `f₁` on `M₁` and `f₂` on `M₂`. -/
private def descFun (f₁ : M₁ → X) (f₂ : M₂ → X) (z : GluedAlong φ) : X :=
  if hz : ∃ x, inl φ x = z then f₁ hz.choose
  else f₂ ((exists_inl_or_exists_inr φ z).resolve_left hz).choose

private theorem descFun_inl (x : M₁) : descFun φ f₁ f₂ (inl φ x) = f₁ x := by
  have hx : ∃ x', inl φ x' = inl φ x := ⟨x, rfl⟩
  rw [descFun, dite_eq_left_of_eq_true (eq_true hx), inl_injective φ hx.choose_spec]

private theorem descFun_inr (h : ∀ x : U₁, f₂ (φ x) = f₁ x) (y : M₂) :
    descFun φ f₁ f₂ (inr φ y) = f₂ y := by
  rw [descFun]
  split_ifs with hz
  · obtain ⟨hx, hy⟩ := (inl_eq_inr_iff φ).1 hz.choose_spec
    exact (h ⟨_, hx⟩).symm.trans (congrArg f₂ hy)
  · rw [inr_injective φ ((exists_inl_or_exists_inr φ _).resolve_left hz).choose_spec]

variable [TopologicalSpace X]

/-- **Maps out of the glued space.** Continuous maps `f₁ : M₁ → X` and `f₂ : M₂ → X` that agree
on the overlap, `f₂ (φ x) = f₁ x` for `x ∈ U₁`, define the continuous map on `GluedAlong φ` that
is `f₁` on `M₁` and `f₂` on `M₂` (`desc_inl`, `desc_inr`). -/
def desc (f₁ : C(M₁, X)) (f₂ : C(M₂, X)) (h : ∀ x : U₁, f₂ (φ x) = f₁ x) :
    C(GluedAlong φ, X) where
  toFun := descFun φ f₁ f₂
  continuous_toFun := by
    refine continuous_iff_continuousAt.2 fun z ↦ ?_
    rcases exists_inl_or_exists_inr φ z with ⟨x, rfl⟩ | ⟨y, rfl⟩
    · refine (isOpenEmbedding_inl φ).continuousAt_iff.1 ?_
      simpa only [Function.comp_def, descFun_inl] using f₁.continuous.continuousAt
    · refine (isOpenEmbedding_inr φ).continuousAt_iff.1 ?_
      simpa only [Function.comp_def, descFun_inr φ h] using f₂.continuous.continuousAt

/-- The map out of the glued space is `f₁` on `M₁`. -/
@[simp]
theorem desc_inl {f₁ : C(M₁, X)} {f₂ : C(M₂, X)} (h : ∀ x : U₁, f₂ (φ x) = f₁ x) (x : M₁) :
    desc φ f₁ f₂ h (inl φ x) = f₁ x :=
  descFun_inl φ x

/-- The map out of the glued space is `f₂` on `M₂`. -/
@[simp]
theorem desc_inr {f₁ : C(M₁, X)} {f₂ : C(M₂, X)} (h : ∀ x : U₁, f₂ (φ x) = f₁ x) (y : M₂) :
    desc φ f₁ f₂ h (inr φ y) = f₂ y :=
  descFun_inr φ h y

end Desc

/-- **Hausdorff criterion for the glued space.** The glued space is Hausdorff exactly when `M₁`
and `M₂` are and any point `x` of `M₁` outside `U₁` and point `y` of `M₂` outside `U₂` have
neighbourhoods `A` and `B` such that `φ` maps no point of `U₁ ∩ A` into `B`. -/
theorem t2Space_iff : T2Space (GluedAlong φ) ↔ T2Space M₁ ∧ T2Space M₂ ∧
    ∀ x ∉ U₁, ∀ y ∉ U₂, ∃ A ∈ 𝓝 x, ∃ B ∈ 𝓝 y, ∀ z : U₁, (z : M₁) ∈ A → (φ z : M₂) ∉ B :=
  TopCat.GlueData.ofHomeomorph_t2Space_iff φ.toHomeomorph

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

end Space

/-! ### Gluing differential forms -/

namespace GluedAlong

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace H M₁]
  [TopologicalSpace M₂] [ChartedSpace H M₂] [IsManifold I ∞ M₁] [IsManifold I ∞ M₂]
  {U₁ : Opens M₁} {U₂ : Opens M₂} (φ : U₁ ≃ₘ^∞⟮I, I⟯ U₂)
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

/-- Two forms on the glued space with the same pull-backs by `inl` and by `inr` are equal. -/
theorem roughForm_ext {α β : RoughForm I (GluedAlong φ) F k}
    (h₁ : mpullback I I (inl φ) α = mpullback I I (inl φ) β)
    (h₂ : mpullback I I (inr φ) α = mpullback I I (inr φ) β) : α = β := by
  funext z
  rcases (range_inl_union_range_inr φ).symm ▸ mem_univ z with ⟨x, rfl⟩ | ⟨y, rfl⟩
  · exact (mpullback_apply_eq_mpullback_apply_iff
      ((isLocalDiffeomorph_inl φ x).isInvertible_mfderiv (by simp)).surjective).1 (congrFun h₁ x)
  · exact (mpullback_apply_eq_mpullback_apply_iff
      ((isLocalDiffeomorph_inr φ y).isInvertible_mfderiv (by simp)).surjective).1 (congrFun h₂ y)

/-- Two smooth forms on the glued space with the same pull-backs by `inl` and by `inr` are
equal. -/
theorem smoothForm_ext {α β : SmoothForm I (GluedAlong φ) F k}
    (h₁ : SmoothForm.mpullback (inl φ) (isLocalDiffeomorph_inl φ).contMDiff α =
      SmoothForm.mpullback (inl φ) (isLocalDiffeomorph_inl φ).contMDiff β)
    (h₂ : SmoothForm.mpullback (inr φ) (isLocalDiffeomorph_inr φ).contMDiff α =
      SmoothForm.mpullback (inr φ) (isLocalDiffeomorph_inr φ).contMDiff β) : α = β := by
  refine Subtype.ext (roughForm_ext φ ?_ ?_)
  · simpa only [SmoothForm.coe_mpullback] using congrArg Subtype.val h₁
  · simpa only [SmoothForm.coe_mpullback] using congrArg Subtype.val h₂

variable {φ}

/-- The form glued from `σ₁` and `σ₂` along `inl` and `inr` pulls back by `inl` to `σ₁`. -/
theorem mpullback_inl_glue (σ₁ : RoughForm I M₁ F k) (σ₂ : RoughForm I M₂ F k) :
    mpullback I I (inl φ) (RoughForm.glue I (inl φ) univ (inr φ) σ₁ σ₂) = σ₁ :=
  funext fun x ↦ RoughForm.mpullback_glue_apply_of_mem (inl_injective φ).injOn (mem_univ x)
    ((isLocalDiffeomorph_inl φ x).isInvertible_mfderiv (by simp))

/-- If `σ₁` and `σ₂` correspond on the overlap, `φ^*(σ₂|U₂) = σ₁|U₁`, the form glued from them
along `inl` and `inr` pulls back by `inr` to `σ₂`. -/
theorem mpullback_inr_glue {σ₁ : RoughForm I M₁ F k} {σ₂ : RoughForm I M₂ F k}
    (hσ : mpullback I I φ (mpullback I I Subtype.val σ₂) = mpullback I I Subtype.val σ₁) :
    mpullback I I (inr φ) (RoughForm.glue I (inl φ) univ (inr φ) σ₁ σ₂) = σ₂ := by
  funext y
  by_cases hz : ∃ x, inl φ x = inr φ y
  · obtain ⟨x, hx⟩ := hz
    obtain ⟨hxU, rfl⟩ := (inl_eq_inr_iff φ).1 hx
    set u : U₁ := ⟨x, hxU⟩
    have hd₁ : MDifferentiable I I (Subtype.val : U₂ → M₂) :=
      (contMDiff_subtypeVal (n := ∞)).mdifferentiable (by simp)
    have hd₂ : MDifferentiable I I (Subtype.val : U₁ → M₁) :=
      (contMDiff_subtypeVal (n := ∞)).mdifferentiable (by simp)
    have hφd : MDifferentiable I I φ := φ.contMDiff.mdifferentiable (by simp)
    rw [← mpullback_subtype_val_apply
        (mpullback I I (inr φ) (RoughForm.glue I (inl φ) univ (inr φ) σ₁ σ₂)) (φ u),
      ← mpullback_subtype_val_apply σ₂ (φ u)]
    refine (mpullback_apply_eq_mpullback_apply_iff (f := φ) (x := u)
      (φ.isInvertible_mfderiv (x := u) (by simp)).surjective).1 ?_
    rw [congrFun hσ u, ← mpullback_comp hd₁ ((isLocalDiffeomorph_inr φ).mdifferentiable
      (by simp)), ← mpullback_comp hφd (((isLocalDiffeomorph_inr φ).mdifferentiable
      (by simp)).comp hd₁)]
    have hcomp : (inr φ ∘ Subtype.val) ∘ φ = inl φ ∘ Subtype.val := by
      funext v; exact inr_apply φ v
    rw [hcomp, mpullback_comp hd₂ ((isLocalDiffeomorph_inl φ).mdifferentiable (by simp)),
      mpullback_inl_glue]
  · exact RoughForm.mpullback_glue_apply_of_notMem (inr_injective φ)
      (fun ⟨x, _, hx⟩ ↦ hz ⟨x, hx⟩)
      ((isLocalDiffeomorph_inr φ y).isInvertible_mfderiv (by simp))

variable (φ) in
/-- **Gluing forms.** Smooth forms `σ₁` on `M₁` and `σ₂` on `M₂` whose restrictions to the
overlaps correspond under `φ`, `φ^*(σ₂|U₂) = σ₁|U₁`, glue to the smooth form on `GluedAlong φ`
whose pull-backs by `inl` and `inr` are `σ₁` and `σ₂` (`mpullback_inl_gluedForm`,
`mpullback_inr_gluedForm`). It is the only such form (`eq_gluedForm_iff`). -/
def gluedForm (σ₁ : SmoothForm I M₁ F k) (σ₂ : SmoothForm I M₂ F k)
    (hσ : SmoothForm.mpullback φ φ.contMDiff
        (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal σ₂) =
      SmoothForm.mpullback Subtype.val contMDiff_subtypeVal σ₁) :
    SmoothForm I (GluedAlong φ) F k :=
  ⟨RoughForm.glue I (inl φ) univ (inr φ) σ₁.val σ₂.val,
    IsSmoothForm.mem_smoothBundleForms <|
      RoughForm.isSmoothForm_glue (by simp) isOpen_univ (inl_injective φ).injOn
        (fun x ↦ isLocalDiffeomorph_inl φ x) σ₁.isSmoothForm σ₂.isSmoothForm
        fun z hz ↦ by
          obtain ⟨y, rfl⟩ := ((range_inl_union_range_inr φ).symm ▸ mem_univ z).resolve_left
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
    SmoothForm.mpullback (inl φ) (isLocalDiffeomorph_inl φ).contMDiff (gluedForm φ σ₁ σ₂ hσ) =
      σ₁ :=
  Subtype.ext <| (SmoothForm.coe_mpullback _ _ _).trans (mpullback_inl_glue _ _)

/-- The glued form pulls back by `inr` to the form on `M₂`. -/
@[simp]
theorem mpullback_inr_gluedForm :
    SmoothForm.mpullback (inr φ) (isLocalDiffeomorph_inr φ).contMDiff (gluedForm φ σ₁ σ₂ hσ) =
      σ₂ :=
  Subtype.ext <| (SmoothForm.coe_mpullback _ _ _).trans <| mpullback_inr_glue <| by
    simpa only [SmoothForm.coe_mpullback] using congrArg Subtype.val hσ

/-- The glued form is the only form on `GluedAlong φ` whose pull-backs by `inl` and `inr` are the
forms on `M₁` and `M₂`. -/
theorem eq_gluedForm_iff {α : SmoothForm I (GluedAlong φ) F k} :
    α = gluedForm φ σ₁ σ₂ hσ ↔
      SmoothForm.mpullback (inl φ) (isLocalDiffeomorph_inl φ).contMDiff α = σ₁ ∧
        SmoothForm.mpullback (inr φ) (isLocalDiffeomorph_inr φ).contMDiff α = σ₂ := by
  refine ⟨?_, fun ⟨h₁, h₂⟩ ↦ smoothForm_ext φ ?_ ?_⟩
  · rintro rfl
    exact ⟨mpullback_inl_gluedForm, mpullback_inr_gluedForm⟩
  · rw [h₁, mpullback_inl_gluedForm]
  · rw [h₂, mpullback_inr_gluedForm]

variable (φ) in
/-- A smooth form on the glued space is closed exactly when its pull-backs by `inl` and `inr`
are. -/
theorem isClosed_iff_isClosed_mpullback {α : SmoothForm I (GluedAlong φ) F k} :
    α.IsClosed ↔
      (SmoothForm.mpullback (inl φ) (isLocalDiffeomorph_inl φ).contMDiff α).IsClosed ∧
        (SmoothForm.mpullback (inr φ) (isLocalDiffeomorph_inr φ).contMDiff α).IsClosed := by
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
theorem isNondegenerate_iff_isNondegenerate_mpullback {α : SmoothTwoForm I (GluedAlong φ)} :
    α.IsNondegenerate ↔
      SmoothTwoForm.IsNondegenerate
          (SmoothForm.mpullback (inl φ) (isLocalDiffeomorph_inl φ).contMDiff α) ∧
        SmoothTwoForm.IsNondegenerate
          (SmoothForm.mpullback (inr φ) (isLocalDiffeomorph_inr φ).contMDiff α) := by
  refine ⟨fun h ↦ ⟨h.isNondegenerate_mpullback_of_isLocalDiffeomorph (isLocalDiffeomorph_inl φ),
    h.isNondegenerate_mpullback_of_isLocalDiffeomorph (isLocalDiffeomorph_inr φ)⟩,
    fun ⟨h₁, h₂⟩ ↦ SmoothTwoForm.isNondegenerate_iff_forall_ker_bilinFormAt_eq_bot.2 fun z ↦ ?_⟩
  suffices hz : (α.bilinFormAt z).Nondegenerate from LinearMap.separatingLeft_iff_ker_eq_bot.1 hz.1
  rcases (range_inl_union_range_inr φ).symm ▸ mem_univ z with ⟨x, rfl⟩ | ⟨y, rfl⟩
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
theorem isSymplectic_iff_isSymplectic_mpullback {α : SmoothTwoForm I (GluedAlong φ)} :
    α.IsSymplectic ↔
      SmoothTwoForm.IsSymplectic
          (SmoothForm.mpullback (inl φ) (isLocalDiffeomorph_inl φ).contMDiff α) ∧
        SmoothTwoForm.IsSymplectic
          (SmoothForm.mpullback (inr φ) (isLocalDiffeomorph_inr φ).contMDiff α) := by
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

end GluedAlong

end SymplecticGeometry
