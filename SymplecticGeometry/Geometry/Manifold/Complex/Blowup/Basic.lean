/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Gluing.Pair
public import SymplecticGeometry.Geometry.Manifold.Complex.Blowup.Model
public import Mathlib.Analysis.CStarAlgebra.Classes
import SymplecticGeometry.Geometry.Manifold.Complex.Blowup.Tautological
import SymplecticGeometry.Geometry.Manifold.ContMDiff.RestrictScalars
import TauCeti.Geometry.Manifold.ContMDiff.Subtype
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Injective
import TauCeti.Geometry.Manifold.SmoothEmbedding.LocalDiffeomorph

/-!
# The blowup of a manifold at a point

Let `M` be a topological space charted on `E = ℂⁿ⁺¹`, let `p₀ : M`, and let `c` be a chart of
`M` around `p₀` with `c p₀ = 0` (a `SymplecticGeometry.BlowupChart M p₀`). The blowup
`SymplecticGeometry.Blowup c` of `M` at `p₀` along `c` is glued from two open pieces: the
punctured space `M \ {p₀}`, and the part `π⁻¹(c.target)` of the model blowup
`SymplecticGeometry.BlowupModel n` lying over the target of `c`, where `π` is the blowdown. A
point `x ≠ p₀` of the source of `c` is identified with the unique point of the model over
`c x ≠ 0`, that is, with `π⁻¹(c x)`; this is the homeomorphism
`SymplecticGeometry.Blowup.gluingHomeomorph c`, made of `c` and the model's
`BlowupModel.blowdownDiffeomorph n`. The blowup is the library's
`SymplecticGeometry.GluedAlong (Blowup.gluingHomeomorph c)`, the gluing of two spaces along a
homeomorphism of open subsets, and it takes from it its topology, its atlas (that of Tau Ceti's
`TopCat.GlueData.chartedSpace`), its second countability when `M` is second countable, and
the canonical open embeddings `GluedAlong.inl` and `GluedAlong.inr` of the two pieces with their
API.

This file builds the glued space, and then its manifold structures. The exceptional divisor
`SymplecticGeometry.Blowup.exceptionalDivisor c` is the image of the zero section of the model;
its point `Blowup.ofDirection c ℓ` corresponds to the line `ℓ` of `E`, which through the
differential of `c` at `p₀` is a line of the tangent space at `p₀`. Off the divisor the blowup
is the punctured space (`Blowup.range_inl`), and the divisor is closed with dense complement.

When `c` is a holomorphic chart of a complex manifold `M`, the gluing map is a biholomorphism,
as `c` and the model's `BlowupModel.blowdownDiffeomorph n` are; so the gluing is compatible in
the sense of Tau Ceti's `TopCat.GlueData.IsCompatible` (`Blowup.isCompatible_complex`), and
`Blowup c` is a complex manifold for which `GluedAlong.inl` and `GluedAlong.inr` are local
biholomorphisms. The same holds for a smooth chart of a real manifold modelled on `E`
(`Blowup.isCompatible_real`). The chart enters as a `Fact` hypothesis, so that both structures
are instances. The blowdown
`Blowup.blowdown c : Blowup c → M` is the inclusion on `M \ {p₀}` and `c.symm ∘ π` on the
model; it is holomorphic (resp. smooth), sends exactly the divisor to `p₀`, and restricts to a
biholomorphism (resp. diffeomorphism) from the complement of the divisor onto `M \ {p₀}`. The
divisor is the image of the holomorphic (resp. smooth) embedding `Blowup.divisorEmbedding c`
(resp. `Blowup.divisorRealEmbedding c`) of `ℙ ℂ E`.

## Main definitions

* `SymplecticGeometry.BlowupChart M p₀`: a chart of `M` whose source contains `p₀` and which
  sends `p₀` to `0`.
* `SymplecticGeometry.Blowup.gluingHomeomorph c`, `SymplecticGeometry.Blowup c`: the
  homeomorphism along which the pieces are glued, and the glued space.
* `SymplecticGeometry.Blowup.ofDirection c ℓ` and `SymplecticGeometry.Blowup.exceptionalDivisor c`:
  the point of the exceptional divisor over the line `ℓ`, and the divisor.
* `SymplecticGeometry.Blowup.lift c`: the map `φ̃` to the model blowup, the inverse of
  `GluedAlong.inr (Blowup.gluingHomeomorph c)` on its range.
* `SymplecticGeometry.Blowup.blowdown c`: the blowdown `π_M : Blowup c → M`.
* `SymplecticGeometry.Blowup.offDivisorOpens c`: the complement of the exceptional divisor, as an
  open set.
* `SymplecticGeometry.Blowup.blowdownDiffeomorph c`,
  `SymplecticGeometry.Blowup.blowdownRealDiffeomorph c`: the blowdown off the divisor, as a
  biholomorphism and as a diffeomorphism onto `M \ {p₀}`.
* `SymplecticGeometry.Blowup.divisorEmbedding c`,
  `SymplecticGeometry.Blowup.divisorRealEmbedding c`:
  the exceptional divisor as the image of a holomorphic, resp. smooth, embedding of `ℙ ℂ E`.

## Main results

* `SymplecticGeometry.Blowup.inl_eq_inr_iff`: when points of the two pieces are identified, in
  terms of the blowdown.
* `SymplecticGeometry.Blowup.range_inl`, `SymplecticGeometry.Blowup.range_inr`: the images of the
  two pieces.
* `SymplecticGeometry.Blowup.isClosed_exceptionalDivisor`,
  `SymplecticGeometry.Blowup.dense_exceptionalDivisor_compl`: the divisor is closed, and its
  complement is dense.
* The instance `T2Space (Blowup c)` when `M` is Hausdorff.
* `SymplecticGeometry.Blowup.isCompatible_complex`, `SymplecticGeometry.Blowup.isCompatible_real`:
  the gluing is holomorphically, resp. smoothly, compatible, and the instances
  `IsManifold 𝓘(ℂ, E) ω (Blowup c)` and `IsManifold 𝓘(ℝ, E) ∞ (Blowup c)`.
* `SymplecticGeometry.Blowup.isLocalDiffeomorph_inl`,
  `SymplecticGeometry.Blowup.isLocalDiffeomorph_inr`
  and their real forms: the canonical maps are local biholomorphisms, resp. diffeomorphisms.
* `SymplecticGeometry.Blowup.contMDiff_blowdown`,
  `SymplecticGeometry.Blowup.blowdown_eq_center_iff`:
  the blowdown is holomorphic, and the preimage of `p₀` is the exceptional divisor.

The Hausdorff property follows from the criterion `SymplecticGeometry.GluedAlong.t2Space_iff`:
a point `x ≠ p₀` and a point of the divisor are separated by the preimages of disjoint
neighbourhoods of `x` and of `p₀`, the second taken in the model through `c.symm ∘ π`. The
compatibility of the gluing is `SymplecticGeometry.GluedAlong.isCompatible_glueData_of_contMDiff`,
and the blowdown is a `SymplecticGeometry.GluedAlong.desc`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §7.1 (the complex blowup).
* [P. Griffiths, J. Harris, *Principles of Algebraic Geometry*][GriffithsHarris1978], Chapter 1,
  §4 (blowing up a point of a complex manifold).
-/

public section

open Set Function Topology TopologicalSpace CategoryTheory Projectivization
open scoped LinearAlgebra.Projectivization Manifold ContDiff

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
  simp [toModel]

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

/-- A point `x` of the overlap in the first piece is glued to the point `y` of the model exactly
when `y` lies over `c x`. -/
@[simp]
theorem coe_gluingHomeomorph_eq_iff {x : puncturedSourceOpens c} {y : modelOpens c} :
    (gluingHomeomorph c x : modelOpens c) = y ↔ c x = (y : BlowupModel n).blowdown := by
  refine ⟨?_, fun hxy ↦ Subtype.ext (eq_of_blowdown_eq ?_ ?_)⟩
  · rintro rfl
    exact (blowdown_gluingHomeomorph c x).symm
  · simpa using c.apply_ne_zero x.property x.val.property
  · simpa using hxy

end Blowup

/-- The blowup of `M` at `p₀` along the chart `c`: the space glued from `M \ {p₀}` and the part
of the model blowup over the target of `c` along `Blowup.gluingHomeomorph c`. Its topology,
atlas and second countability, and its canonical maps `GluedAlong.inl` and `GluedAlong.inr`
from the two pieces, are those of `SymplecticGeometry.GluedAlong`. -/
abbrev Blowup (c : BlowupChart (n := n) M p₀) : Type :=
  GluedAlong (Blowup.gluingHomeomorph c)

namespace Blowup

open BlowupModel

open GluedAlong (glueData inl inr)

variable (c : BlowupChart (n := n) M p₀)

/-- A point `x ≠ p₀` of `M` and a point `y` of the model are identified in the blowup exactly
when `x` is in the source of `c` and `y` lies over `c x`. -/
theorem inl_eq_inr_iff {x : puncturedOpens c} {y : modelOpens c} :
    inl (gluingHomeomorph c) x = inr (gluingHomeomorph c) y ↔
      (x : M) ∈ c.source ∧ c x = (y : BlowupModel n).blowdown := by
  simp

/-- A point `y` of the model and a point `x ≠ p₀` of `M` are identified in the blowup exactly
when `x` is in the source of `c` and `y` lies over `c x`. -/
theorem inr_eq_inl_iff {y : modelOpens c} {x : puncturedOpens c} :
    inr (gluingHomeomorph c) y = inl (gluingHomeomorph c) x ↔
      (x : M) ∈ c.source ∧ c x = (y : BlowupModel n).blowdown :=
  eq_comm.trans (inl_eq_inr_iff c)

/-! ### The exceptional divisor -/

/-- The point of the model's zero section over the line `ℓ`, as a point of the second piece. -/
private def zeroSectionPiece (ℓ : ℙ ℂ (Fin (n + 1) → ℂ)) : modelOpens c :=
  ⟨zeroSection ℓ, by simpa using c.zero_mem_target⟩

/-- The point of the exceptional divisor of the blowup over the line `ℓ` of `ℂⁿ⁺¹`: the image of
the point `(ℓ, 0)` of the model. -/
def ofDirection (ℓ : ℙ ℂ (Fin (n + 1) → ℂ)) : Blowup c :=
  inr (gluingHomeomorph c) (zeroSectionPiece c ℓ)

/-- `ofDirection c ℓ` is the image of the point `(ℓ, 0)` of the model. -/
theorem ofDirection_def (ℓ : ℙ ℂ (Fin (n + 1) → ℂ)) :
    ofDirection c ℓ = inr (gluingHomeomorph c) ⟨zeroSection ℓ, by simpa using c.zero_mem_target⟩ :=
  (rfl)

theorem ofDirection_injective : Injective (ofDirection c) := fun _ _ h ↦
  zeroSection_injective (congrArg Subtype.val (GluedAlong.inr_injective (gluingHomeomorph c) h))

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
      inr (gluingHomeomorph c) y = z := by
  constructor
  · rw [exceptionalDivisor_def]
    rintro ⟨ℓ, rfl⟩
    exact ⟨zeroSectionPiece c ℓ, blowdown_zeroSection ℓ, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    rw [exceptionalDivisor_def]
    exact ⟨(y : BlowupModel n).pr,
      congrArg (inr (gluingHomeomorph c)) (Subtype.ext (eq_zeroSection_pr hy).symm)⟩

/-- A point of the model is on the exceptional divisor exactly when it lies over `0`. -/
@[simp]
theorem inr_mem_exceptionalDivisor_iff {y : modelOpens c} :
    inr (gluingHomeomorph c) y ∈ exceptionalDivisor c ↔ (y : BlowupModel n).blowdown = 0 := by
  rw [mem_exceptionalDivisor_iff]
  constructor
  · rintro ⟨y', hy', h⟩
    rwa [← GluedAlong.inr_injective (gluingHomeomorph c) h]
  · exact fun hy ↦ ⟨y, hy, rfl⟩

/-- Off the exceptional divisor, the blowup is the punctured space. -/
theorem range_inl : range (inl (gluingHomeomorph c)) = (exceptionalDivisor c)ᶜ := by
  ext z
  rcases GluedAlong.exists_inl_or_exists_inr _ z with ⟨x, rfl⟩ | ⟨y, rfl⟩
  · simp only [mem_range_self, mem_compl_iff, true_iff, mem_exceptionalDivisor_iff, not_exists,
      not_and]
    intro y hy hxy
    exact c.apply_ne_zero ((inl_eq_inr_iff c).1 hxy.symm).1 x.property
      (((inl_eq_inr_iff c).1 hxy.symm).2.trans hy)
  · rw [GluedAlong.inr_mem_range_inl_iff, mem_modelOffDivisorOpens, mem_compl_iff,
      inr_mem_exceptionalDivisor_iff]

/-- No point of the punctured space is on the exceptional divisor. -/
@[simp]
theorem inl_notMem_exceptionalDivisor (x : puncturedOpens c) :
    inl (gluingHomeomorph c) x ∉ exceptionalDivisor c := by
  rw [← mem_compl_iff, ← range_inl]
  exact mem_range_self x

/-- The complement of the exceptional divisor, the range of `inl (gluingHomeomorph c)`, as an
open set. -/
def offDivisorOpens : Opens (Blowup c) :=
  ⟨range (inl (gluingHomeomorph c)), GluedAlong.isOpen_range_inl (gluingHomeomorph c)⟩

theorem offDivisorOpens_def : offDivisorOpens c =
    ⟨range (inl (gluingHomeomorph c)), GluedAlong.isOpen_range_inl (gluingHomeomorph c)⟩ :=
  (rfl)

@[simp]
theorem coe_offDivisorOpens : (offDivisorOpens c : Set (Blowup c)) = (exceptionalDivisor c)ᶜ := by
  rw [offDivisorOpens_def, Opens.coe_mk, range_inl]

@[simp]
theorem mem_offDivisorOpens {z : Blowup c} : z ∈ offDivisorOpens c ↔ z ∉ exceptionalDivisor c := by
  rw [← SetLike.mem_coe, coe_offDivisorOpens, mem_compl_iff]

/-- The image of the model in the blowup is the exceptional divisor together with the image of
the punctured source of `c`. -/
theorem range_inr :
    range (inr (gluingHomeomorph c)) =
      exceptionalDivisor c ∪ inl (gluingHomeomorph c) '' {x | (x : M) ∈ c.source} := by
  ext z
  rcases GluedAlong.exists_inl_or_exists_inr _ z with ⟨x, rfl⟩ | ⟨y, rfl⟩
  · rw [GluedAlong.inl_mem_range_inr_iff, mem_puncturedSourceOpens]
    refine ⟨fun hx ↦ .inr ⟨x, hx, rfl⟩, ?_⟩
    rintro (h | ⟨x', hx', h⟩)
    · exact (inl_notMem_exceptionalDivisor c x h).elim
    · rwa [← GluedAlong.inl_injective (gluingHomeomorph c) h]
  · simp only [mem_range_self, true_iff, mem_union, inr_mem_exceptionalDivisor_iff]
    by_cases hy : (y : BlowupModel n).blowdown = 0
    · exact .inl hy
    · have hy' : y ∈ modelOffDivisorOpens c := (mem_modelOffDivisorOpens c).2 hy
      obtain ⟨x, hx⟩ := (GluedAlong.inr_mem_range_inl_iff (gluingHomeomorph c)).2 hy'
      exact .inr ⟨x, (mem_puncturedSourceOpens c).1 ((GluedAlong.inl_mem_range_inr_iff _).1
        ⟨y, hx.symm⟩), hx⟩

theorem isClosed_exceptionalDivisor : IsClosed (exceptionalDivisor c) := by
  rw [← isOpen_compl_iff, ← range_inl]
  exact GluedAlong.isOpen_range_inl (gluingHomeomorph c)

/-- The complement of the exceptional divisor is dense in the blowup. -/
theorem dense_exceptionalDivisor_compl : Dense (exceptionalDivisor c)ᶜ := by
  rw [← range_inl, dense_iff_closure_eq, eq_univ_iff_forall]
  intro z
  rcases GluedAlong.exists_inl_or_exists_inr _ z with ⟨x, rfl⟩ | ⟨y, rfl⟩
  · exact subset_closure (mem_range_self x)
  -- Off the divisor the model is dense, and the second piece is open in it.
  have hD : Dense (Subtype.val ⁻¹' (BlowupModel.exceptionalDivisor n)ᶜ : Set (modelOpens c)) :=
    BlowupModel.dense_exceptionalDivisor_compl.preimage (modelOpens c).isOpen.isOpenMap_subtypeVal
  refine closure_mono ?_ (mem_closure_image (GluedAlong.continuous_inr _).continuousAt (hD y))
  rintro _ ⟨y', hy', rfl⟩
  exact (GluedAlong.inr_mem_range_inl_iff (gluingHomeomorph c)).2 (by simpa using hy')

/-! ### The map to the model -/

instance : Nonempty (modelOpens c) := ⟨zeroSectionPiece c (Classical.arbitrary _)⟩

/-- The map `φ̃` from the blowup to the model blowup: the inverse of the open embedding
`inr (gluingHomeomorph c)` on its range, followed by the inclusion. Off that range its values
are not meaningful. -/
def lift (z : Blowup c) : BlowupModel n :=
  (((GluedAlong.isOpenEmbedding_inr (gluingHomeomorph c)).toOpenPartialHomeomorph
    (inr (gluingHomeomorph c))).symm z : modelOpens c)

theorem lift_def (z : Blowup c) :
    lift c z = (((GluedAlong.isOpenEmbedding_inr (gluingHomeomorph c)).toOpenPartialHomeomorph
      (inr (gluingHomeomorph c))).symm z :
      modelOpens c) := (rfl)

@[simp]
theorem lift_inr (y : modelOpens c) : lift c (inr (gluingHomeomorph c) y) = y := by
  rw [lift_def, IsOpenEmbedding.toOpenPartialHomeomorph_left_inv]

/-- On the punctured source of `c`, the map to the model is the inverse of the blowdown applied
to `c x`, which is `(mk (c x), c x)`. -/
theorem lift_inl {x : puncturedOpens c} (hx : (x : M) ∈ c.source) :
    lift c (inl (gluingHomeomorph c) x) =
      (blowdownDiffeomorph n).symm
        ⟨c x, c.apply_ne_zero hx ((mem_puncturedOpens c).1 x.property)⟩ := by
  rw [← GluedAlong.inr_apply (gluingHomeomorph c) ⟨x, hx⟩, lift_inr, coe_gluingHomeomorph]

/-- On the range of `inr`, the map to the model lands over the target of `c`. -/
theorem lift_mem_modelOpens {z : Blowup c} (hz : z ∈ range (inr (gluingHomeomorph c))) :
    lift c z ∈ modelOpens c := by
  obtain ⟨y, rfl⟩ := hz
  rw [lift_inr]
  exact y.property

/-- On the range of `inr`, the map to the model is the inverse of `inr`. -/
theorem inr_lift {z : Blowup c} (hz : z ∈ range (inr (gluingHomeomorph c))) :
    inr (gluingHomeomorph c) ⟨lift c z, lift_mem_modelOpens c hz⟩ = z := by
  obtain ⟨y, rfl⟩ := hz
  simp only [lift_inr]

/-! ### Separation -/

/-- The blowup of a Hausdorff space is Hausdorff. -/
instance [T2Space M] : T2Space (Blowup c) := by
  refine (GluedAlong.t2Space_iff (gluingHomeomorph c)).2
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

/-! ### The manifold structures -/

section Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 (Fin (n + 1) → ℂ)] {r : ℕ∞ω}

/-- The gluing map is `C^r` when `c` is `C^r` on its source and the inverse of the model's
blowdown off the divisor is `C^r`. -/
theorem contMDiff_gluingHomeomorph
    (hc : ContMDiffOn 𝓘(𝕜, Fin (n + 1) → ℂ) 𝓘(𝕜, Fin (n + 1) → ℂ) r c c.source)
    (hb : ContMDiff 𝓘(𝕜, Fin (n + 1) → ℂ) 𝓘(𝕜, Fin (n + 1) → ℂ) r (blowdownDiffeomorph n).symm) :
    ContMDiff 𝓘(𝕜, Fin (n + 1) → ℂ) 𝓘(𝕜, Fin (n + 1) → ℂ) r (gluingHomeomorph c) := by
  have hc' : ContMDiff 𝓘(𝕜, Fin (n + 1) → ℂ) 𝓘(𝕜, Fin (n + 1) → ℂ) r
      fun x : puncturedSourceOpens c ↦ (⟨c x, c.apply_ne_zero x.property x.val.property⟩ :
        (⟨{z | z ≠ 0}, isOpen_ne⟩ : Opens (Fin (n + 1) → ℂ))) :=
    (TauCeti.ContMDiff.subtypeVal_comp_iff _ _).1 <|
      hc.comp_contMDiff (contMDiff_subtypeVal.comp contMDiff_subtypeVal) fun x ↦ x.property
  refine (TauCeti.ContMDiff.subtypeVal_comp_iff _ _).1 ?_
  refine (TauCeti.ContMDiff.subtypeVal_comp_iff _ (Subtype.val ∘ gluingHomeomorph c)).1 ?_
  convert contMDiff_subtypeVal.comp (hb.comp hc') using 1
  exact funext (coe_gluingHomeomorph c)

/-- The inverse of the gluing map is `C^r` when `c.symm` is `C^r` on the target of `c` and the
model's blowdown is `C^r`. -/
theorem contMDiff_gluingHomeomorph_symm
    (hc : ContMDiffOn 𝓘(𝕜, Fin (n + 1) → ℂ) 𝓘(𝕜, Fin (n + 1) → ℂ) r c.symm c.target)
    (hb : ContMDiff 𝓘(𝕜, Fin (n + 1) → ℂ) 𝓘(𝕜, Fin (n + 1) → ℂ) r
      (blowdown : BlowupModel n → Fin (n + 1) → ℂ)) :
    ContMDiff 𝓘(𝕜, Fin (n + 1) → ℂ) 𝓘(𝕜, Fin (n + 1) → ℂ) r (gluingHomeomorph c).symm := by
  refine (TauCeti.ContMDiff.subtypeVal_comp_iff _ _).1 <|
    (TauCeti.ContMDiff.subtypeVal_comp_iff _ _).1 ?_
  exact hc.comp_contMDiff (hb.comp (contMDiff_subtypeVal.comp contMDiff_subtypeVal))
    fun y ↦ y.val.property

/-- The gluing is compatible as soon as `c`, its inverse, the model's blowdown and its inverse
off the divisor are `C^r`. -/
theorem isCompatible_of_contMDiff
    (hc : ContMDiffOn 𝓘(𝕜, Fin (n + 1) → ℂ) 𝓘(𝕜, Fin (n + 1) → ℂ) r c c.source)
    (hcs : ContMDiffOn 𝓘(𝕜, Fin (n + 1) → ℂ) 𝓘(𝕜, Fin (n + 1) → ℂ) r c.symm c.target)
    (hb : ContMDiff 𝓘(𝕜, Fin (n + 1) → ℂ) 𝓘(𝕜, Fin (n + 1) → ℂ) r
      (blowdown : BlowupModel n → Fin (n + 1) → ℂ))
    (hbs : ContMDiff 𝓘(𝕜, Fin (n + 1) → ℂ) 𝓘(𝕜, Fin (n + 1) → ℂ) r
      (blowdownDiffeomorph n).symm) :
    (glueData (gluingHomeomorph c)).IsCompatible 𝓘(𝕜, Fin (n + 1) → ℂ) r :=
  GluedAlong.isCompatible_glueData_of_contMDiff _ (contMDiff_gluingHomeomorph c hc hbs)
    (contMDiff_gluingHomeomorph_symm c hcs hb)

/-- **The holomorphic gluing.** For a holomorphic chart `c`, the gluing of the punctured
manifold and the part of the model blowup over the target of `c` is holomorphically
compatible. -/
theorem isCompatible_complex [IsManifold 𝓘(ℂ, Fin (n + 1) → ℂ) ω M]
    (hc : c.toOpenPartialHomeomorph ∈ IsManifold.maximalAtlas 𝓘(ℂ, Fin (n + 1) → ℂ) ω M) :
    (glueData (gluingHomeomorph c)).IsCompatible 𝓘(ℂ, Fin (n + 1) → ℂ) ω :=
  isCompatible_of_contMDiff c (contMDiffOn_of_mem_maximalAtlas hc)
    (contMDiffOn_symm_of_mem_maximalAtlas hc) (contMDiff_blowdown ω)
    (blowdownDiffeomorph n).symm.contMDiff

open scoped TauCeti.ComplexManifold in
/-- **The smooth gluing.** For a smooth chart `c` of a real manifold modelled on `ℂⁿ⁺¹`, the
gluing of the punctured manifold and the part of the model blowup over the target of `c` is
smoothly compatible. -/
theorem isCompatible_real [IsManifold 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ M]
    (hc : c.toOpenPartialHomeomorph ∈ IsManifold.maximalAtlas 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ M) :
    (glueData (gluingHomeomorph c)).IsCompatible 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ :=
  isCompatible_of_contMDiff c (contMDiffOn_of_mem_maximalAtlas hc)
    (contMDiffOn_symm_of_mem_maximalAtlas hc)
    (((contMDiff_blowdown ω).restrictScalars' ℝ).of_le le_top)
    (((blowdownDiffeomorph n).symm.contMDiff.restrictScalars' ℝ).of_le le_top)

/-- The blowup along a holomorphic chart is a complex manifold. -/
instance instIsManifoldComplex [IsManifold 𝓘(ℂ, Fin (n + 1) → ℂ) ω M]
    [hc : Fact (c.toOpenPartialHomeomorph ∈ IsManifold.maximalAtlas 𝓘(ℂ, Fin (n + 1) → ℂ) ω M)] :
    IsManifold 𝓘(ℂ, Fin (n + 1) → ℂ) ω (Blowup c) :=
  (isCompatible_complex c hc.out).isManifold

open scoped TauCeti.ComplexManifold in
/-- The blowup along a smooth chart is a smooth manifold. -/
instance instIsManifoldReal [IsManifold 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ M]
    [hc : Fact (c.toOpenPartialHomeomorph ∈ IsManifold.maximalAtlas 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ M)] :
    IsManifold 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ (Blowup c) :=
  (isCompatible_real c hc.out).isManifold

/-- The canonical map from the punctured space is a local biholomorphism. -/
theorem isLocalDiffeomorph_inl [IsManifold 𝓘(ℂ, Fin (n + 1) → ℂ) ω M]
    [hc : Fact (c.toOpenPartialHomeomorph ∈ IsManifold.maximalAtlas 𝓘(ℂ, Fin (n + 1) → ℂ) ω M)] :
    IsLocalDiffeomorph 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) ω (inl (gluingHomeomorph c)) :=
  GluedAlong.isLocalDiffeomorph_inl_of_isCompatible (isCompatible_complex c hc.out)

/-- The canonical map from the model is a local biholomorphism. -/
theorem isLocalDiffeomorph_inr [IsManifold 𝓘(ℂ, Fin (n + 1) → ℂ) ω M]
    [hc : Fact (c.toOpenPartialHomeomorph ∈ IsManifold.maximalAtlas 𝓘(ℂ, Fin (n + 1) → ℂ) ω M)] :
    IsLocalDiffeomorph 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) ω (inr (gluingHomeomorph c)) :=
  GluedAlong.isLocalDiffeomorph_inr_of_isCompatible (isCompatible_complex c hc.out)

open scoped TauCeti.ComplexManifold in
/-- The canonical map from the punctured space is a local diffeomorphism of real manifolds. -/
theorem isLocalDiffeomorph_inl_real [IsManifold 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ M]
    [hc : Fact (c.toOpenPartialHomeomorph ∈ IsManifold.maximalAtlas 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ M)] :
    IsLocalDiffeomorph 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ (inl (gluingHomeomorph c)) :=
  GluedAlong.isLocalDiffeomorph_inl_of_isCompatible (isCompatible_real c hc.out)

open scoped TauCeti.ComplexManifold in
/-- The canonical map from the model is a local diffeomorphism of real manifolds. -/
theorem isLocalDiffeomorph_inr_real [IsManifold 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ M]
    [hc : Fact (c.toOpenPartialHomeomorph ∈ IsManifold.maximalAtlas 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ M)] :
    IsLocalDiffeomorph 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ (inr (gluingHomeomorph c)) :=
  GluedAlong.isLocalDiffeomorph_inr_of_isCompatible (isCompatible_real c hc.out)

end Manifold

/-! ### The blowdown -/

/-- The blowdown `π_M : Blowup c → M`: the identity off the exceptional divisor, through `inl`,
and `c.symm ∘ π` on the part of the model over the target of `c`, through `inr`. It sends the
exceptional divisor to `p₀`. -/
def blowdown : C(Blowup c, M) :=
  GluedAlong.desc (gluingHomeomorph c) ⟨Subtype.val, continuous_subtypeVal⟩
    ⟨fun y : modelOpens c ↦ c.symm (y : BlowupModel n).blowdown,
      c.continuousOn_symm.comp_continuous (continuous_blowdown.comp continuous_subtypeVal)
        fun y ↦ y.property⟩
    fun x ↦ by
      rw [ContinuousMap.coe_mk, ContinuousMap.coe_mk, blowdown_gluingHomeomorph]
      exact c.left_inv x.property

/-- Off the exceptional divisor, the blowdown is the identity of `M \ {p₀}`. -/
@[simp]
theorem blowdown_inl (x : puncturedOpens c) : blowdown c (inl (gluingHomeomorph c) x) = x :=
  GluedAlong.desc_inl _ _ x

/-- On the part of the model over the target of `c`, the blowdown is `c.symm ∘ π`. -/
@[simp]
theorem blowdown_inr (y : modelOpens c) :
    blowdown c (inr (gluingHomeomorph c) y) = c.symm (y : BlowupModel n).blowdown :=
  GluedAlong.desc_inr _ _ y

/-- The blowdown sends each point of the exceptional divisor to the centre. -/
@[simp]
theorem blowdown_ofDirection (ℓ : ℙ ℂ (Fin (n + 1) → ℂ)) : blowdown c (ofDirection c ℓ) = p₀ := by
  rw [ofDirection_def, blowdown_inr, blowdown_zeroSection, c.symm_zero]

section Smooth

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 (Fin (n + 1) → ℂ)] {r : ℕ∞ω}

/-- The blowdown is `C^r` for a `C^r` compatible gluing, when `c.symm` and the model's
blowdown are `C^r`. -/
theorem contMDiff_blowdown_of_isCompatible [IsManifold 𝓘(𝕜, Fin (n + 1) → ℂ) r M]
    [IsManifold 𝓘(𝕜, Fin (n + 1) → ℂ) r (BlowupModel n)]
    (h : (glueData (gluingHomeomorph c)).IsCompatible 𝓘(𝕜, Fin (n + 1) → ℂ) r)
    (hc : ContMDiffOn 𝓘(𝕜, Fin (n + 1) → ℂ) 𝓘(𝕜, Fin (n + 1) → ℂ) r c.symm c.target)
    (hb : ContMDiff 𝓘(𝕜, Fin (n + 1) → ℂ) 𝓘(𝕜, Fin (n + 1) → ℂ) r
      (BlowupModel.blowdown : BlowupModel n → Fin (n + 1) → ℂ)) :
    ContMDiff 𝓘(𝕜, Fin (n + 1) → ℂ) 𝓘(𝕜, Fin (n + 1) → ℂ) r (blowdown c) := by
  refine (GluedAlong.contMDiff_iff_of_isCompatible h le_rfl).2 ⟨?_, ?_⟩
  · exact contMDiff_subtypeVal.congr fun x ↦ by rw [Function.comp_apply, blowdown_inl]
  · exact (hc.comp_contMDiff (hb.comp contMDiff_subtypeVal) fun y ↦ y.property).congr fun y ↦ by
      simp only [Function.comp_apply, blowdown_inr]

end Smooth

/-- The blowdown is holomorphic. -/
theorem contMDiff_blowdown [IsManifold 𝓘(ℂ, Fin (n + 1) → ℂ) ω M]
    [hc : Fact (c.toOpenPartialHomeomorph ∈ IsManifold.maximalAtlas 𝓘(ℂ, Fin (n + 1) → ℂ) ω M)] :
    ContMDiff 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) ω (blowdown c) :=
  contMDiff_blowdown_of_isCompatible c (isCompatible_complex c hc.out)
    (contMDiffOn_symm_of_mem_maximalAtlas hc.out) (BlowupModel.contMDiff_blowdown ω)

open scoped TauCeti.ComplexManifold in
/-- The blowdown is smooth for the real structures. -/
theorem contMDiff_blowdown_real [IsManifold 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ M]
    [hc : Fact (c.toOpenPartialHomeomorph ∈ IsManifold.maximalAtlas 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ M)] :
    ContMDiff 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ (blowdown c) :=
  contMDiff_blowdown_of_isCompatible c (isCompatible_real c hc.out)
    (contMDiffOn_symm_of_mem_maximalAtlas hc.out)
    (((BlowupModel.contMDiff_blowdown ω).restrictScalars' ℝ).of_le le_top)

/-- The blowdown sends a point to the centre exactly when it is on the exceptional divisor. -/
theorem blowdown_eq_center_iff {z : Blowup c} : blowdown c z = p₀ ↔ z ∈ exceptionalDivisor c := by
  rcases GluedAlong.exists_inl_or_exists_inr _ z with ⟨x, rfl⟩ | ⟨y, rfl⟩
  · rw [blowdown_inl, iff_false_intro (inl_notMem_exceptionalDivisor c x), iff_false]
    exact x.property
  · rw [blowdown_inr, inr_mem_exceptionalDivisor_iff]
    refine ⟨fun h ↦ of_not_not fun h0 ↦ c.symm_apply_ne y.property h0 h, fun h ↦ ?_⟩
    rw [h, c.symm_zero]

/-- The blowdown sends the complement of the exceptional divisor into `M \ {p₀}`. -/
theorem blowdown_mem_puncturedOpens {z : Blowup c} (hz : z ∈ offDivisorOpens c) :
    blowdown c z ∈ puncturedOpens c := by
  rw [mem_puncturedOpens, Ne, blowdown_eq_center_iff]
  exact (mem_offDivisorOpens c).1 hz

/-- **The blowdown off the exceptional divisor.** The blowdown is a biholomorphism from the
complement of the exceptional divisor onto `M \ {p₀}`, with inverse `inl (gluingHomeomorph c)`. -/
def blowdownDiffeomorph [IsManifold 𝓘(ℂ, Fin (n + 1) → ℂ) ω M]
    [Fact (c.toOpenPartialHomeomorph ∈ IsManifold.maximalAtlas 𝓘(ℂ, Fin (n + 1) → ℂ) ω M)] :
    offDivisorOpens c ≃ₘ^ω⟮𝓘(ℂ, Fin (n + 1) → ℂ), 𝓘(ℂ, Fin (n + 1) → ℂ)⟯ puncturedOpens c :=
  -- `offDivisorOpens c` is by definition the open set `IsLocalDiffeomorph.image` of
  -- `inl (gluingHomeomorph c)`.
  ((isLocalDiffeomorph_inl c).diffeomorphOfInjective
    (GluedAlong.inl_injective (gluingHomeomorph c))).symm

section Complex

variable [IsManifold 𝓘(ℂ, Fin (n + 1) → ℂ) ω M]
  [Fact (c.toOpenPartialHomeomorph ∈ IsManifold.maximalAtlas 𝓘(ℂ, Fin (n + 1) → ℂ) ω M)]

/-- The inverse of `blowdownDiffeomorph c` is `inl (gluingHomeomorph c)`. -/
@[simp]
theorem coe_blowdownDiffeomorph_symm_apply (x : puncturedOpens c) :
    ((blowdownDiffeomorph c).symm x : Blowup c) = inl (gluingHomeomorph c) x :=
  IsLocalDiffeomorph.coe_diffeomorphOfInjective_apply _ _ x

/-- The biholomorphism `blowdownDiffeomorph c` is the blowdown. -/
@[simp]
theorem coe_blowdownDiffeomorph_apply (z : offDivisorOpens c) :
    (blowdownDiffeomorph c z : M) = blowdown c z := by
  conv_rhs => rw [← (blowdownDiffeomorph c).symm_apply_apply z]
  rw [coe_blowdownDiffeomorph_symm_apply, blowdown_inl]

end Complex

open scoped TauCeti.ComplexManifold in
/-- **The blowdown off the exceptional divisor, for the real structures.** The blowdown is a
diffeomorphism from the complement of the exceptional divisor onto `M \ {p₀}`, with inverse
`inl (gluingHomeomorph c)`. -/
def blowdownRealDiffeomorph [IsManifold 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ M]
    [Fact (c.toOpenPartialHomeomorph ∈ IsManifold.maximalAtlas 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ M)] :
    offDivisorOpens c ≃ₘ^∞⟮𝓘(ℝ, Fin (n + 1) → ℂ), 𝓘(ℝ, Fin (n + 1) → ℂ)⟯ puncturedOpens c :=
  -- `offDivisorOpens c` is by definition the open set `IsLocalDiffeomorph.image` of
  -- `inl (gluingHomeomorph c)`.
  ((isLocalDiffeomorph_inl_real c).diffeomorphOfInjective
    (GluedAlong.inl_injective (gluingHomeomorph c))).symm

section Real

variable [IsManifold 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ M]
  [Fact (c.toOpenPartialHomeomorph ∈ IsManifold.maximalAtlas 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ M)]

/-- The inverse of `blowdownRealDiffeomorph c` is `inl (gluingHomeomorph c)`. -/
@[simp]
theorem coe_blowdownRealDiffeomorph_symm_apply (x : puncturedOpens c) :
    ((blowdownRealDiffeomorph c).symm x : Blowup c) = inl (gluingHomeomorph c) x :=
  IsLocalDiffeomorph.coe_diffeomorphOfInjective_apply _ _ x

/-- The diffeomorphism `blowdownRealDiffeomorph c` is the blowdown. -/
@[simp]
theorem coe_blowdownRealDiffeomorph_apply (z : offDivisorOpens c) :
    (blowdownRealDiffeomorph c z : M) = blowdown c z := by
  conv_rhs => rw [← (blowdownRealDiffeomorph c).symm_apply_apply z]
  rw [coe_blowdownRealDiffeomorph_symm_apply, blowdown_inl]

end Real

/-! ### The exceptional divisor as a submanifold -/

/-- **The exceptional divisor as a complex submanifold.** The map `ℓ ↦ ofDirection c ℓ` from
`ℙ ℂ (Fin (n + 1) → ℂ)` to the blowup, as a holomorphic embedding:
`inr (gluingHomeomorph c)` after the model's zero section `BlowupModel.zeroSectionEmbedding n`.
Its image is the exceptional divisor. -/
def divisorEmbedding [IsManifold 𝓘(ℂ, Fin (n + 1) → ℂ) ω M]
    [Fact (c.toOpenPartialHomeomorph ∈ IsManifold.maximalAtlas 𝓘(ℂ, Fin (n + 1) → ℂ) ω M)] :
    TauCeti.SmoothEmbedding 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) ω (ℙ ℂ (Fin (n + 1) → ℂ))
      (Blowup c) :=
  ((zeroSectionEmbedding n).codRestrict (modelOpens c) fun ℓ ↦ by
      simpa using c.zero_mem_target).transLocalDiffeomorph (inr (gluingHomeomorph c)) (s := univ)
    (fun y _ ↦ isLocalDiffeomorph_iff.1 (isLocalDiffeomorph_inr c) y)
    (by
      rw [domRestrict_def]
      exact (GluedAlong.isOpenEmbedding_inr (gluingHomeomorph c)).isEmbedding.comp .subtypeVal)
    (subset_univ _)

/-- The holomorphic embedding of the exceptional divisor is `ofDirection c`. -/
@[simp]
theorem coe_divisorEmbedding [IsManifold 𝓘(ℂ, Fin (n + 1) → ℂ) ω M]
    [Fact (c.toOpenPartialHomeomorph ∈ IsManifold.maximalAtlas 𝓘(ℂ, Fin (n + 1) → ℂ) ω M)] :
    ⇑(divisorEmbedding c) = ofDirection c := by
  ext ℓ
  rw [divisorEmbedding, TauCeti.SmoothEmbedding.transLocalDiffeomorph_apply, ofDirection_def]
  exact congrArg (inr (gluingHomeomorph c)) (Subtype.ext (by
    rw [TauCeti.SmoothEmbedding.val_codRestrict_apply, coe_zeroSectionEmbedding]))

/-- The image of the holomorphic embedding of the divisor is the exceptional divisor. -/
theorem range_divisorEmbedding [IsManifold 𝓘(ℂ, Fin (n + 1) → ℂ) ω M]
    [Fact (c.toOpenPartialHomeomorph ∈ IsManifold.maximalAtlas 𝓘(ℂ, Fin (n + 1) → ℂ) ω M)] :
    range (divisorEmbedding c) = exceptionalDivisor c := by
  rw [coe_divisorEmbedding, exceptionalDivisor_def]

open scoped TauCeti.ComplexManifold in
/-- **The exceptional divisor as a real submanifold.** The map `ℓ ↦ ofDirection c ℓ` as a smooth
embedding of the underlying real manifolds: `inr (gluingHomeomorph c)` after the model's
`BlowupModel.zeroSectionRealEmbedding n`. Its image is the exceptional divisor. -/
def divisorRealEmbedding [IsManifold 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ M]
    [Fact (c.toOpenPartialHomeomorph ∈ IsManifold.maximalAtlas 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ M)] :
    TauCeti.SmoothEmbedding 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ (ℙ ℂ (Fin (n + 1) → ℂ))
      (Blowup c) :=
  ((zeroSectionRealEmbedding n).codRestrict (modelOpens c) fun ℓ ↦ by
      simpa using c.zero_mem_target).transLocalDiffeomorph (inr (gluingHomeomorph c)) (s := univ)
    (fun y _ ↦ isLocalDiffeomorph_iff.1 (isLocalDiffeomorph_inr_real c) y)
    (by
      rw [domRestrict_def]
      exact (GluedAlong.isOpenEmbedding_inr (gluingHomeomorph c)).isEmbedding.comp .subtypeVal)
    (subset_univ _)

open scoped TauCeti.ComplexManifold in
/-- The real embedding of the exceptional divisor is `ofDirection c`. -/
@[simp]
theorem coe_divisorRealEmbedding [IsManifold 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ M]
    [Fact (c.toOpenPartialHomeomorph ∈ IsManifold.maximalAtlas 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ M)] :
    ⇑(divisorRealEmbedding c) = ofDirection c := by
  ext ℓ
  rw [divisorRealEmbedding, TauCeti.SmoothEmbedding.transLocalDiffeomorph_apply, ofDirection_def]
  exact congrArg (inr (gluingHomeomorph c)) (Subtype.ext (by
    rw [TauCeti.SmoothEmbedding.val_codRestrict_apply, coe_zeroSectionRealEmbedding]))

open scoped TauCeti.ComplexManifold in
/-- The image of the real embedding of the divisor is the exceptional divisor. -/
theorem range_divisorRealEmbedding [IsManifold 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ M]
    [Fact (c.toOpenPartialHomeomorph ∈ IsManifold.maximalAtlas 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ M)] :
    range (divisorRealEmbedding c) = exceptionalDivisor c := by
  rw [coe_divisorRealEmbedding, exceptionalDivisor_def]

end Blowup

end SymplecticGeometry

end
