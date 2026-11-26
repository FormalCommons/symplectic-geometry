/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Complex.Blowup.Model
public import SymplecticGeometry.Topology.Category.TopCat.GlueData.Pair
public import TauCeti.Geometry.Manifold.Gluing.GlueData

/-!
# The blowup of a manifold at a point: the glued space

Let `M` be a topological space charted on `E = ℂⁿ⁺¹`, let `p₀ : M`, and let `c` be a chart of
`M` around `p₀` with `c p₀ = 0` (a `SymplecticGeometry.BlowupChart M p₀`). The blowup
`SymplecticGeometry.Blowup c` of `M` at `p₀` along `c` is glued from two open pieces: the
punctured space `M \ {p₀}`, and the part `π⁻¹(c.target)` of the model blowup
`SymplecticGeometry.BlowupModel n` lying over the target of `c`, where `π` is the blowdown. A
point `x ≠ p₀` of the source of `c` is identified with the unique point of the model over
`c x ≠ 0`, that is, with `π⁻¹(c x)`; this is the homeomorphism
`SymplecticGeometry.Blowup.gluingHomeomorph c`, made of `c` and the model's
`BlowupModel.blowdownDiffeomorph n`. The gluing is the library's two-piece gluing
`TopCat.GlueData.ofHomeomorph`.

This file builds the glued space with its topology and the atlas of Tau Ceti's
`TopCat.GlueData.chartedSpace`, without any smooth structure. The exceptional divisor
`SymplecticGeometry.Blowup.exceptionalDivisor c` is the image of the zero section of the model;
its point `Blowup.ofDirection c ℓ` corresponds to the line `ℓ` of `E`, which through the
differential of `c` at `p₀` is a line of the tangent space at `p₀`. Off the divisor the blowup
is the punctured space (`Blowup.range_inl`), and the divisor is closed with dense complement.

## Main definitions

* `SymplecticGeometry.BlowupChart M p₀`: a chart of `M` whose source contains `p₀` and which
  sends `p₀` to `0`.
* `SymplecticGeometry.Blowup.glueData c`, `SymplecticGeometry.Blowup c`: the gluing data and the
  glued space.
* `SymplecticGeometry.Blowup.inl c`, `SymplecticGeometry.Blowup.inr c`: the canonical open
  embeddings of the two pieces.
* `SymplecticGeometry.Blowup.ofDirection c ℓ` and `SymplecticGeometry.Blowup.exceptionalDivisor c`:
  the point of the exceptional divisor over the line `ℓ`, and the divisor.
* `SymplecticGeometry.Blowup.lift c`: the map `φ̃` to the model blowup, the inverse of `inr c`
  on its range.

## Main results

* `SymplecticGeometry.Blowup.inl_eq_inr_iff`: when points of the two pieces are identified.
* `SymplecticGeometry.Blowup.range_inl`, `SymplecticGeometry.Blowup.range_inr`: the images of the
  two pieces.
* `SymplecticGeometry.Blowup.isClosed_exceptionalDivisor`,
  `SymplecticGeometry.Blowup.dense_exceptionalDivisor_compl`: the divisor is closed, and its
  complement is dense.
* The instances `ChartedSpace E (Blowup c)`, `T2Space (Blowup c)` when `M` is Hausdorff, and
  `SecondCountableTopology (Blowup c)` when `M` is second countable.

The Hausdorff property follows from the criterion `TopCat.GlueData.ofHomeomorph_t2Space_iff`:
a point `x ≠ p₀` and a point of the divisor are separated by the preimages of disjoint
neighbourhoods of `x` and of `p₀`, the second taken in the model through `c.symm ∘ π`. The
construction of the glued space and its canonical maps follows the library's
`SymplecticGeometry.GluedAlong` (`Geometry/Manifold/Gluing/Pair.lean`).

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §7.1 (the complex blowup).
* [P. Griffiths, J. Harris, *Principles of Algebraic Geometry*][GriffithsHarris1978], Chapter 1,
  §4 (blowing up a point of a complex manifold).
-/

public section

open Set Function Topology TopologicalSpace CategoryTheory Projectivization
open scoped LinearAlgebra.Projectivization

noncomputable section

namespace SymplecticGeometry

variable {n : ℕ}

/-- A chart for blowing up `M` at `p₀`: a partial homeomorphism of `M` to `ℂⁿ⁺¹` whose source
contains `p₀` and which sends `p₀` to `0`. Instance search does not find the dimension `n` from
`M`, so it is given by name, as in `BlowupChart (n := n) M p₀`. -/
@[ext]
structure BlowupChart (M : Type) [TopologicalSpace M] [ChartedSpace (Fin (n + 1) → ℂ) M] (p₀ : M)
    extends OpenPartialHomeomorph M (Fin (n + 1) → ℂ) where
  /-- The centre `p₀` is in the source of the chart. -/
  mem_source : p₀ ∈ toOpenPartialHomeomorph.source
  /-- The chart sends the centre `p₀` to `0`. -/
  map_center : toOpenPartialHomeomorph p₀ = 0

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Fin (n + 1) → ℂ) M] {p₀ : M}

namespace BlowupChart

instance : CoeOut (BlowupChart (n := n) M p₀) (OpenPartialHomeomorph M (Fin (n + 1) → ℂ)) :=
  ⟨toOpenPartialHomeomorph⟩

instance : CoeFun (BlowupChart (n := n) M p₀) fun _ ↦ M → Fin (n + 1) → ℂ :=
  ⟨fun c ↦ c.toOpenPartialHomeomorph⟩

variable (c : BlowupChart (n := n) M p₀)

/-- The origin is in the target of the chart. -/
theorem zero_mem_target : 0 ∈ c.target := c.map_center ▸ c.map_source c.mem_source

/-- The inverse of the chart sends `0` to the centre. -/
@[simp]
theorem symm_zero : c.symm 0 = p₀ := by
  rw [← c.map_center, c.left_inv c.mem_source]

/-- The chart sends no point of its source other than the centre to `0`. -/
theorem apply_ne_zero {x : M} (hx : x ∈ c.source) (hne : x ≠ p₀) : c x ≠ 0 := fun h ↦
  hne (c.injOn hx c.mem_source (h.trans c.map_center.symm))

/-- The inverse of the chart sends no nonzero point of its target to the centre. -/
theorem symm_apply_ne {z : Fin (n + 1) → ℂ} (hz : z ∈ c.target) (hne : z ≠ 0) :
    c.symm z ≠ p₀ := fun h ↦ hne (by rw [← c.right_inv hz, h, c.map_center])

end BlowupChart

namespace Blowup

open BlowupModel

variable (c : BlowupChart (n := n) M p₀)

/-- The first piece of the blowup: the open set `M \ {p₀}`, open since a space charted on
`ℂⁿ⁺¹` is T1. It does not depend on `c`, which only fixes the dimension. -/
def puncturedOpens (_c : BlowupChart (n := n) M p₀) : Opens M :=
  haveI := ChartedSpace.t1Space (Fin (n + 1) → ℂ) M
  ⟨{p₀}ᶜ, isOpen_compl_singleton⟩

@[simp]
theorem mem_puncturedOpens {x : M} : x ∈ puncturedOpens c ↔ x ≠ p₀ := Iff.rfl

/-- The second piece of the blowup: the open set of points of the model blowup whose blowdown
lies in the target of `c`. -/
def modelOpens : Opens (BlowupModel n) :=
  ⟨blowdown ⁻¹' c.target, c.open_target.preimage continuous_blowdown⟩

@[simp]
theorem mem_modelOpens {y : BlowupModel n} : y ∈ modelOpens c ↔ y.blowdown ∈ c.target := Iff.rfl

/-- The overlap in the first piece: the punctured source of `c`. -/
def puncturedSourceOpens : Opens (puncturedOpens c) :=
  ⟨Subtype.val ⁻¹' c.source, c.open_source.preimage continuous_subtypeVal⟩

@[simp]
theorem mem_puncturedSourceOpens {x : puncturedOpens c} :
    x ∈ puncturedSourceOpens c ↔ (x : M) ∈ c.source := Iff.rfl

/-- The overlap in the second piece: its points off the exceptional divisor of the model. -/
def modelOffDivisorOpens : Opens (modelOpens c) :=
  ⟨{y | (y : BlowupModel n).blowdown ≠ 0},
    isOpen_ne.preimage (continuous_blowdown.comp continuous_subtypeVal)⟩

@[simp]
theorem mem_modelOffDivisorOpens {y : modelOpens c} :
    y ∈ modelOffDivisorOpens c ↔ (y : BlowupModel n).blowdown ≠ 0 := Iff.rfl

/-- The point of the model blowup over the image under `c` of a point of the overlap in the
first piece: `(mk (c x), c x)`, through the inverse of `blowdownDiffeomorph`. -/
private def toModel (x : puncturedSourceOpens c) : BlowupModel n :=
  (blowdownDiffeomorph n).symm ⟨c x, c.apply_ne_zero x.property x.val.property⟩

private theorem blowdown_toModel (x : puncturedSourceOpens c) :
    (toModel c x).blowdown = c x := by
  simp [toModel, blowdown_mk]

private theorem continuous_toModel : Continuous (toModel c) :=
  continuous_subtypeVal.comp <| (blowdownDiffeomorph n).symm.continuous.comp <|
    (c.continuousOn.comp_continuous (continuous_subtypeVal.comp continuous_subtypeVal)
      fun x ↦ x.property).subtype_mk _

/-- The homeomorphism along which the blowup is glued: a point `x ≠ p₀` of the source of `c`
goes to the point of the model over `c x`, and a point `y` of the model off the divisor goes to
`c.symm (π y)`. -/
def gluingHomeomorph : puncturedSourceOpens c ≃ₜ modelOffDivisorOpens c where
  toFun x := ⟨⟨toModel c x, by
      rw [mem_modelOpens, blowdown_toModel]; exact c.map_source x.property⟩, by
    rw [mem_modelOffDivisorOpens, blowdown_toModel]
    exact c.apply_ne_zero x.property x.val.property⟩
  invFun y := ⟨⟨c.symm (y : BlowupModel n).blowdown,
    c.symm_apply_ne y.val.property y.property⟩, c.map_target y.val.property⟩
  left_inv x := by
    ext
    simp [blowdown_toModel, c.left_inv x.property]
  right_inv y := by
    refine Subtype.ext (Subtype.ext (eq_of_blowdown_eq ?_ ?_).symm)
    · exact y.property
    · simp [blowdown_toModel, c.right_inv y.val.property]
  continuous_toFun := continuous_induced_rng.2 (continuous_induced_rng.2 (continuous_toModel c))
  continuous_invFun := by
    refine continuous_induced_rng.2 (continuous_induced_rng.2 ?_)
    exact c.continuousOn_symm.comp_continuous
      (continuous_blowdown.comp (continuous_subtypeVal.comp continuous_subtypeVal))
      fun y ↦ y.val.property

/-- The point glued to `x` lies over `c x`. -/
@[simp]
theorem blowdown_gluingHomeomorph (x : puncturedSourceOpens c) :
    ((gluingHomeomorph c x : modelOpens c) : BlowupModel n).blowdown = c x :=
  blowdown_toModel c x

/-- The point glued to `x` is `(mk (c x), c x)`, the inverse of the blowdown applied to `c x`. -/
theorem coe_gluingHomeomorph (x : puncturedSourceOpens c) :
    ((gluingHomeomorph c x : modelOpens c) : BlowupModel n) =
      (blowdownDiffeomorph n).symm
        ⟨c x, c.apply_ne_zero ((mem_puncturedSourceOpens c).1 x.property)
          ((mem_puncturedOpens c).1 x.val.property)⟩ :=
  (rfl)

/-- The point glued to `y` is `c.symm (π y)`. -/
@[simp]
theorem coe_gluingHomeomorph_symm (y : modelOffDivisorOpens c) :
    ((gluingHomeomorph c).symm y : M) = c.symm (y : BlowupModel n).blowdown :=
  (rfl)

/-- The gluing data of the blowup: the pieces `M \ {p₀}` (index `false`) and the part of the
model over the target of `c` (index `true`), glued along `gluingHomeomorph c`. -/
@[expose] def glueData : TopCat.GlueData := TopCat.GlueData.ofHomeomorph (gluingHomeomorph c)

/-- The gluing data of the blowup is the two-piece gluing along `gluingHomeomorph c`; its
pieces, overlaps and transitions are given by the lemmas about `TopCat.GlueData.ofHomeomorph`. -/
theorem glueData_def :
    glueData c = TopCat.GlueData.ofHomeomorph (gluingHomeomorph c) := (rfl)

end Blowup

/-- The blowup of `M` at `p₀` along the chart `c`: the space glued from `M \ {p₀}` and the part
of the model blowup over the target of `c`. -/
@[expose] def Blowup (c : BlowupChart (n := n) M p₀) : Type :=
  (Blowup.glueData c).toGlueData.glued

namespace Blowup

open BlowupModel

variable (c : BlowupChart (n := n) M p₀)

instance : TopologicalSpace (Blowup c) :=
  inferInstanceAs (TopologicalSpace (glueData c).toGlueData.glued)

/-- Each piece of the gluing carries its atlas as an open subset of `M` or of the model. -/
instance instChartedSpaceGlueDataU :
    ∀ i : (glueData c).J, ChartedSpace (Fin (n + 1) → ℂ) ((glueData c).U i)
  | ⟨false⟩ => inferInstanceAs (ChartedSpace (Fin (n + 1) → ℂ) (puncturedOpens c))
  | ⟨true⟩ => inferInstanceAs (ChartedSpace (Fin (n + 1) → ℂ) (modelOpens c))

/-- The atlas of the blowup, transported from those of the two pieces along the canonical
maps (Tau Ceti's `TopCat.GlueData.chartedSpace`). -/
instance : ChartedSpace (Fin (n + 1) → ℂ) (Blowup c) :=
  (glueData c).chartedSpace (Fin (n + 1) → ℂ)

/-- The canonical map from the punctured space `M \ {p₀}` to the blowup. -/
def inl (x : puncturedOpens c) : Blowup c := (glueData c).toGlueData.ι ⟨false⟩ x

/-- The canonical map from the part of the model blowup over the target of `c` to the blowup. -/
def inr (y : modelOpens c) : Blowup c := (glueData c).toGlueData.ι ⟨true⟩ y

theorem inl_def (x : puncturedOpens c) : inl c x = (glueData c).toGlueData.ι ⟨false⟩ x := (rfl)

theorem inr_def (y : modelOpens c) : inr c y = (glueData c).toGlueData.ι ⟨true⟩ y := (rfl)

theorem isOpenEmbedding_inl : IsOpenEmbedding (inl c) := (glueData c).ι_isOpenEmbedding ⟨false⟩

theorem isOpenEmbedding_inr : IsOpenEmbedding (inr c) := (glueData c).ι_isOpenEmbedding ⟨true⟩

theorem inl_injective : Injective (inl c) := (isOpenEmbedding_inl c).injective

theorem inr_injective : Injective (inr c) := (isOpenEmbedding_inr c).injective

@[simp]
theorem inl_inj {x x' : puncturedOpens c} : inl c x = inl c x' ↔ x = x' :=
  (inl_injective c).eq_iff

@[simp]
theorem inr_inj {y y' : modelOpens c} : inr c y = inr c y' ↔ y = y' := (inr_injective c).eq_iff

@[fun_prop]
theorem continuous_inl : Continuous (inl c) := (isOpenEmbedding_inl c).continuous

@[fun_prop]
theorem continuous_inr : Continuous (inr c) := (isOpenEmbedding_inr c).continuous

theorem isOpen_range_inl : IsOpen (range (inl c)) := (isOpenEmbedding_inl c).isOpen_range

theorem isOpen_range_inr : IsOpen (range (inr c)) := (isOpenEmbedding_inr c).isOpen_range

/-- Every point of the blowup comes from one of the two pieces. -/
theorem range_inl_union_range_inr : range (inl c) ∪ range (inr c) = univ :=
  eq_univ_of_forall fun z ↦
    (TopCat.GlueData.ofHomeomorph_ι_jointly_surjective (gluingHomeomorph c) z).imp id id

/-- A point `x ≠ p₀` of `M` and a point `y` of the model are identified in the blowup exactly
when `x` is in the source of `c` and `y` lies over `c x`. -/
@[simp, grind =]
theorem inl_eq_inr_iff {x : puncturedOpens c} {y : modelOpens c} :
    inl c x = inr c y ↔ (x : M) ∈ c.source ∧ c x = (y : BlowupModel n).blowdown := by
  refine (TopCat.GlueData.ofHomeomorph_ι_false_eq_ι_true_iff (gluingHomeomorph c)).trans
    ⟨?_, ?_⟩
  · rintro ⟨hx, rfl⟩
    exact ⟨hx, (blowdown_gluingHomeomorph c ⟨x, hx⟩).symm⟩
  · rintro ⟨hx, hxy⟩
    refine ⟨hx, Subtype.ext (eq_of_blowdown_eq ?_ ?_)⟩
    · simpa using c.apply_ne_zero hx x.property
    · simpa using hxy

/-- A point `y` of the model and a point `x ≠ p₀` of `M` are identified in the blowup exactly
when `x` is in the source of `c` and `y` lies over `c x`. -/
@[simp, grind =]
theorem inr_eq_inl_iff {y : modelOpens c} {x : puncturedOpens c} :
    inr c y = inl c x ↔ (x : M) ∈ c.source ∧ c x = (y : BlowupModel n).blowdown :=
  eq_comm.trans (inl_eq_inr_iff c)

/-- A point of the punctured source of `c` and the point of the model glued to it have the same
image in the blowup. -/
@[simp]
theorem inr_gluingHomeomorph (x : puncturedSourceOpens c) :
    inr c (gluingHomeomorph c x : modelOpens c) = inl c (x : puncturedOpens c) :=
  ((inl_eq_inr_iff c).2 ⟨x.property, (blowdown_gluingHomeomorph c x).symm⟩).symm

/-- A point of the model off the divisor and the point of `M` glued to it have the same image in
the blowup. -/
@[simp]
theorem inl_gluingHomeomorph_symm (y : modelOffDivisorOpens c) :
    inl c ((gluingHomeomorph c).symm y : puncturedOpens c) = inr c (y : modelOpens c) := by
  rw [← inr_gluingHomeomorph, Homeomorph.apply_symm_apply]

/-- A point of the model lies in the image of the punctured space exactly when it is off the
exceptional divisor of the model. -/
theorem inr_mem_range_inl_iff {y : modelOpens c} :
    inr c y ∈ range (inl c) ↔ (y : BlowupModel n).blowdown ≠ 0 := by
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨hxs, hxy⟩ := (inl_eq_inr_iff c).1 hx
    exact hxy ▸ c.apply_ne_zero hxs x.property
  · intro hy
    refine ⟨⟨c.symm (y : BlowupModel n).blowdown, c.symm_apply_ne y.property hy⟩,
      (inl_eq_inr_iff c).2 ⟨c.map_target y.property, c.right_inv y.property⟩⟩

/-- A point of the punctured space lies in the image of the model exactly when it is in the
source of `c`. -/
theorem inl_mem_range_inr_iff {x : puncturedOpens c} :
    inl c x ∈ range (inr c) ↔ (x : M) ∈ c.source := by
  constructor
  · rintro ⟨y, hy⟩
    exact ((inl_eq_inr_iff c).1 hy.symm).1
  · exact fun hx ↦ ⟨_, inr_gluingHomeomorph c ⟨x, hx⟩⟩

/-! ### The exceptional divisor -/

/-- The point of the model's zero section over the line `ℓ`, as a point of the second piece. -/
private def zeroSectionPiece (ℓ : ℙ ℂ (Fin (n + 1) → ℂ)) : modelOpens c :=
  ⟨zeroSection ℓ, by simpa using c.zero_mem_target⟩

/-- The point of the exceptional divisor of the blowup over the line `ℓ` of `ℂⁿ⁺¹`: the image of
the point `(ℓ, 0)` of the model. -/
def ofDirection (ℓ : ℙ ℂ (Fin (n + 1) → ℂ)) : Blowup c := inr c (zeroSectionPiece c ℓ)

/-- `ofDirection c ℓ` is the image of the point `(ℓ, 0)` of the model. -/
theorem ofDirection_def (ℓ : ℙ ℂ (Fin (n + 1) → ℂ)) :
    ofDirection c ℓ = inr c ⟨zeroSection ℓ, by simpa using c.zero_mem_target⟩ := (rfl)

theorem ofDirection_injective : Injective (ofDirection c) := fun _ _ h ↦
  zeroSection_injective (congrArg Subtype.val (inr_injective c h))

/-- The exceptional divisor of the blowup: the image of the zero section of the model, a copy
of `ℙ ℂ (Fin (n + 1) → ℂ)`. -/
def exceptionalDivisor : Set (Blowup c) := range (ofDirection c)

/-- The exceptional divisor is the set of the points `ofDirection c ℓ`. -/
theorem exceptionalDivisor_def : exceptionalDivisor c = range (ofDirection c) := (rfl)

/-- The point over each line `ℓ` is on the exceptional divisor. -/
@[simp]
theorem ofDirection_mem_exceptionalDivisor (ℓ : ℙ ℂ (Fin (n + 1) → ℂ)) :
    ofDirection c ℓ ∈ exceptionalDivisor c := by
  rw [exceptionalDivisor_def]
  exact mem_range_self ℓ

/-- A point of the blowup is on the exceptional divisor exactly when it is the image of a point
of the model over `0`. -/
theorem mem_exceptionalDivisor_iff {z : Blowup c} :
    z ∈ exceptionalDivisor c ↔ ∃ y : modelOpens c, (y : BlowupModel n).blowdown = 0 ∧
      inr c y = z := by
  constructor
  · rw [exceptionalDivisor_def]
    rintro ⟨ℓ, rfl⟩
    exact ⟨zeroSectionPiece c ℓ, blowdown_zeroSection ℓ, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    rw [exceptionalDivisor_def]
    exact ⟨(y : BlowupModel n).pr, congrArg (inr c) (Subtype.ext (eq_zeroSection_pr hy).symm)⟩

/-- A point of the model is on the exceptional divisor exactly when it lies over `0`. -/
@[simp]
theorem inr_mem_exceptionalDivisor_iff {y : modelOpens c} :
    inr c y ∈ exceptionalDivisor c ↔ (y : BlowupModel n).blowdown = 0 := by
  rw [mem_exceptionalDivisor_iff]
  constructor
  · rintro ⟨y', hy', h⟩
    rwa [← inr_injective c h]
  · exact fun hy ↦ ⟨y, hy, rfl⟩

/-- Off the exceptional divisor, the blowup is the punctured space. -/
theorem range_inl : range (inl c) = (exceptionalDivisor c)ᶜ := by
  ext z
  rcases (range_inl_union_range_inr c).ge (mem_univ z) with ⟨x, rfl⟩ | ⟨y, rfl⟩
  · simp only [mem_range_self, mem_compl_iff, true_iff, mem_exceptionalDivisor_iff, not_exists,
      not_and]
    intro y hy hxy
    exact c.apply_ne_zero ((inl_eq_inr_iff c).1 hxy.symm).1 x.property
      (((inl_eq_inr_iff c).1 hxy.symm).2.trans hy)
  · rw [inr_mem_range_inl_iff, mem_compl_iff, inr_mem_exceptionalDivisor_iff]

/-- No point of the punctured space is on the exceptional divisor. -/
@[simp]
theorem inl_notMem_exceptionalDivisor (x : puncturedOpens c) :
    inl c x ∉ exceptionalDivisor c := by
  rw [← mem_compl_iff, ← range_inl]
  exact mem_range_self x

/-- The image of the model in the blowup is the exceptional divisor together with the image of
the punctured source of `c`. -/
theorem range_inr :
    range (inr c) = exceptionalDivisor c ∪ inl c '' {x | (x : M) ∈ c.source} := by
  ext z
  rcases (range_inl_union_range_inr c).ge (mem_univ z) with ⟨x, rfl⟩ | ⟨y, rfl⟩
  · refine (inl_mem_range_inr_iff c).trans ⟨fun hx ↦ .inr ⟨x, hx, rfl⟩, ?_⟩
    rintro (h | ⟨x', hx', h⟩)
    · exact (inl_notMem_exceptionalDivisor c x h).elim
    · rwa [← inl_injective c h]
  · simp only [mem_range_self, true_iff, mem_union, inr_mem_exceptionalDivisor_iff]
    by_cases hy : (y : BlowupModel n).blowdown = 0
    · exact .inl hy
    · obtain ⟨x, hx⟩ := (inr_mem_range_inl_iff c).2 hy
      exact .inr ⟨x, (inl_mem_range_inr_iff c).1 ⟨y, hx.symm⟩, hx⟩

theorem isClosed_exceptionalDivisor : IsClosed (exceptionalDivisor c) := by
  rw [← isOpen_compl_iff, ← range_inl]
  exact isOpen_range_inl c

/-- The complement of the exceptional divisor is dense in the blowup. -/
theorem dense_exceptionalDivisor_compl : Dense (exceptionalDivisor c)ᶜ := by
  rw [← range_inl, dense_iff_closure_eq, eq_univ_iff_forall]
  intro z
  rcases (range_inl_union_range_inr c).ge (mem_univ z) with ⟨x, rfl⟩ | ⟨y, rfl⟩
  · exact subset_closure (mem_range_self x)
  -- Off the divisor the model is dense, and the second piece is open in it.
  have hD : Dense (Subtype.val ⁻¹' (BlowupModel.exceptionalDivisor n)ᶜ : Set (modelOpens c)) :=
    BlowupModel.dense_exceptionalDivisor_compl.preimage (modelOpens c).isOpen.isOpenMap_subtypeVal
  refine closure_mono ?_ (mem_closure_image (continuous_inr c).continuousAt (hD y))
  rintro _ ⟨y', hy', rfl⟩
  exact (inr_mem_range_inl_iff c).2 (by simpa using hy')

/-! ### The map to the model -/

instance : Nonempty (modelOpens c) := ⟨zeroSectionPiece c (Classical.arbitrary _)⟩

/-- The map `φ̃` from the blowup to the model blowup: the inverse of the open embedding `inr c`
on its range, followed by the inclusion. Off the range of `inr c` its values are not
meaningful. -/
def lift (z : Blowup c) : BlowupModel n :=
  (((isOpenEmbedding_inr c).toOpenPartialHomeomorph (inr c)).symm z : modelOpens c)

theorem lift_def (z : Blowup c) :
    lift c z = (((isOpenEmbedding_inr c).toOpenPartialHomeomorph (inr c)).symm z :
      modelOpens c) := (rfl)

@[simp]
theorem lift_inr (y : modelOpens c) : lift c (inr c y) = y := by
  rw [lift_def, IsOpenEmbedding.toOpenPartialHomeomorph_left_inv]

/-- On the punctured source of `c`, the map to the model is the inverse of the blowdown applied
to `c x`, which is `(mk (c x), c x)`. -/
theorem lift_inl {x : puncturedOpens c} (hx : (x : M) ∈ c.source) :
    lift c (inl c x) =
      (blowdownDiffeomorph n).symm
        ⟨c x, c.apply_ne_zero hx ((mem_puncturedOpens c).1 x.property)⟩ := by
  rw [← inr_gluingHomeomorph c ⟨x, hx⟩, lift_inr, coe_gluingHomeomorph]

/-- On the range of `inr c`, the map to the model lands over the target of `c`. -/
theorem lift_mem_modelOpens {z : Blowup c} (hz : z ∈ range (inr c)) :
    lift c z ∈ modelOpens c := by
  obtain ⟨y, rfl⟩ := hz
  rw [lift_inr]
  exact y.property

/-- On the range of `inr c`, the map to the model is the inverse of `inr c`. -/
theorem inr_lift {z : Blowup c} (hz : z ∈ range (inr c)) :
    inr c ⟨lift c z, lift_mem_modelOpens c hz⟩ = z := by
  obtain ⟨y, rfl⟩ := hz
  simp only [lift_inr]

/-! ### Separation and countability -/

/-- The blowup of a Hausdorff space is Hausdorff. -/
instance [T2Space M] : T2Space (Blowup c) := by
  refine (TopCat.GlueData.ofHomeomorph_t2Space_iff (gluingHomeomorph c)).2
    ⟨inferInstanceAs (T2Space (puncturedOpens c)), inferInstanceAs (T2Space (modelOpens c)),
      fun x _ y hy ↦ ?_⟩
  have hy0 : (y : BlowupModel n).blowdown = 0 := of_not_not hy
  -- Separate `x` from `p₀` in `M`, and pull the neighbourhood of `p₀` back to the model.
  obtain ⟨A, B, hA, hB, hxA, hpB, hAB⟩ := t2_separation ((mem_puncturedOpens c).1 x.property)
  have hg : Continuous fun y : modelOpens c ↦ c.symm (y : BlowupModel n).blowdown :=
    c.continuousOn_symm.comp_continuous (continuous_blowdown.comp continuous_subtypeVal)
      fun y ↦ y.property
  refine ⟨Subtype.val ⁻¹' A, (hA.preimage continuous_subtypeVal).mem_nhds hxA,
    _, (hB.preimage hg).mem_nhds (by simpa [hy0] using hpB), fun z hzA hzB ↦ ?_⟩
  have hzB' : ((z : puncturedOpens c) : M) ∈ B := by
    simpa [c.left_inv z.property] using hzB
  exact hAB.ne_of_mem hzA hzB' rfl

/-- The blowup of a second countable space is second countable. -/
instance [SecondCountableTopology M] : SecondCountableTopology (Blowup c) :=
  have : ∀ i : (glueData c).J, SecondCountableTopology ((glueData c).U i)
    | ⟨false⟩ => inferInstanceAs (SecondCountableTopology (puncturedOpens c))
    | ⟨true⟩ => inferInstanceAs (SecondCountableTopology (modelOpens c))
  have : Countable (glueData c).J := by
    rw [glueData, TopCat.GlueData.ofHomeomorph_J]
    infer_instance
  TopCat.GlueData.secondCountableTopology (glueData c)

end Blowup

end SymplecticGeometry

end
