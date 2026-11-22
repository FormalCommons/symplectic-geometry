/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.Normed.Module.Normalize
public import TauCeti.AlgebraicTopology.Sphere.Equator
public import TauCeti.Analysis.Normed.Group.BallSphere
public import TauCeti.Topology.Homotopy.FiberHomotopyEquiv.Basic
public import TauCeti.Topology.Homotopy.PuncturedStarConvex

/-!
# Radial projection over the sphere, and the complement of a line

Let `V` be a subset of a real normed space, star-convex about `p` and containing `sphere p r`.
Tau Ceti's straight-line homotopy `StarConvex.radialHomotopy` from radial projection to the
identity of `V ∖ {p}` moves each point along its ray from `p`, so it keeps the radial projection
fixed. Hence radial projection `V ∖ {p} ⟶ sphere p r` is a fibre homotopy equivalence over the
sphere (`StarConvex.radialProjectionFiberHomotopyEquiv`), and restricting it to preimages shows
that the punctured cone `ρ⁻¹ W` over any subset `W` of the unit sphere is homotopy equivalent to
`W` (`TauCeti.complZeroPreimageHomotopyEquiv`).

For a point `p` of the unit sphere, `E ∖ {0}` is covered by `TauCeti.complRay p` and
`TauCeti.complRay (-p)`, the points off the open rays `{t • p | t > 0}` and `{t • p | t < 0}`.
Each is contractible, as a subset of `E` star-convex about the opposite point
(`TauCeti.contractibleSpace_complRay`).
Their intersection is the complement of the line `ℝ ∙ p`
(`TauCeti.mem_complRay_inter_complRay_neg_iff`), the punctured cone over the sphere minus `±p`.
In an inner product space it is therefore homotopy equivalent to the unit sphere of `(ℝ ∙ p)ᗮ`
(`TauCeti.complRayInterHomotopyEquiv`), by radial projection followed by
`TauCeti.equatorHomotopyEquiv p`, and it contains `(ℝ ∙ p)ᗮ ∖ {0}`, on which this homotopy
equivalence is radial projection in `(ℝ ∙ p)ᗮ`.

## Main definitions

* `StarConvex.radialProjectionFiberHomotopyEquiv`: radial projection as a fibre homotopy
  equivalence over the sphere.
* `TauCeti.complZeroPreimageHomotopyEquiv W`: the punctured cone over `W` is homotopy equivalent
  to `W`.
* `TauCeti.complRay p`: the points of `E ∖ {0}` off the open ray through `p`.
* `TauCeti.complZeroOrthogonalInclusion p`: the inclusion of `(ℝ ∙ p)ᗮ ∖ {0}` into
  `complRay p ∩ complRay (-p)`.
* `TauCeti.complRayInterHomotopyEquiv p`: the complement of the line through `p` is homotopy
  equivalent to the unit sphere of `(ℝ ∙ p)ᗮ`.

## Implementation notes

The homotopy of `StarConvex.radialProjectionFiberHomotopyEquiv` is Tau Ceti's
`StarConvex.radialHomotopy`, and the equivalence is that of Tau Ceti's
`StarConvex.sphereHomotopyEquiv`, read over the sphere; the restriction to preimages is Tau Ceti's
`TauCeti.FiberHomotopyEquiv.restrictPreimage`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Chapter 0 (the radial deformation retraction of `ℝⁿ ∖ {0}` onto the sphere) and Section 2.2
  (Example 2.46).
-/

public section

noncomputable section

open Metric Set
open scoped ContinuousMap unitInterval

namespace TauCeti

section StarConvex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {V : Set E} {p : E} {r : ℝ}

/-- Radial projection fixes the points of the sphere. -/
@[simp]
theorem radialProjectionToSphere_comp_sphereInclusionDiffSingleton (hr : 0 < r)
    (hS : sphere p r ⊆ V) :
    (radialProjectionToSphere (V := V) hr).comp (sphereInclusionDiffSingleton hr.ne' hS) =
      ContinuousMap.id (sphere p r) := by
  ext x
  have hx : ‖(x : E) - p‖ = r := by simpa [dist_eq_norm] using x.property
  simp [hx, hr.ne']

/-- The straight-line homotopy from radial projection to the identity keeps the radial
projection of each point fixed: it moves the point along its ray from `p`. -/
@[simp]
theorem radialProjectionToSphere_radialHomotopy_apply (hV : StarConvex ℝ p V) (hr : 0 < r)
    (hS : sphere p r ⊆ V) (t : I) (z : ↥(V \ {p})) :
    radialProjectionToSphere hr (hV.radialHomotopy hr hS (t, z)) =
      radialProjectionToSphere hr z := by
  set c := (1 - (t : ℝ)) * (r / ‖(z : E) - p‖) + t
  have hH : ((hV.radialHomotopy hr hS (t, z) : ↥(V \ {p})) : E) - p = c • ((z : E) - p) := by
    rw [StarConvex.coe_radialHomotopy_apply, add_sub_cancel_left]
  have hc₀ : 0 ≤ c := add_nonneg (mul_nonneg (unitInterval.one_sub_nonneg t)
    (div_nonneg hr.le (norm_nonneg _))) t.property.1
  have hc : c ≠ 0 := by
    rintro h
    exact (hV.radialHomotopy hr hS (t, z)).property.2 (sub_eq_zero.1 (by rw [hH, h, zero_smul]))
  ext1
  rw [coe_radialProjectionToSphere_apply, coe_radialProjectionToSphere_apply, hH, norm_smul,
    Real.norm_of_nonneg hc₀, smul_smul]
  congr 2
  field_simp

/-- **Radial projection is a fibre homotopy equivalence over the sphere.** If `V` is star-convex
about `p` and contains `sphere p r` with `r > 0`, then radial projection `V ∖ {p} ⟶ sphere p r`,
with the inclusion of the sphere as homotopy inverse, is a homotopy equivalence over the sphere:
the homotopy from the composite to the identity of `V ∖ {p}` keeps the radial projection fixed. -/
def _root_.StarConvex.radialProjectionFiberHomotopyEquiv (hV : StarConvex ℝ p V) (hr : 0 < r)
    (hS : sphere p r ⊆ V) :
    FiberHomotopyEquiv (radialProjectionToSphere (V := V) hr) (ContinuousMap.id (sphere p r)) where
  toFun := radialProjectionToSphere hr
  invFun := sphereInclusionDiffSingleton hr.ne' hS
  comp_toFun := ContinuousMap.id_comp _
  comp_invFun := radialProjectionToSphere_comp_sphereInclusionDiffSingleton hr hS
  left_inv := ⟨{ toHomotopy := hV.radialHomotopy hr hS
                 prop' := fun t ↦ ContinuousMap.ext fun z ↦
                   radialProjectionToSphere_radialHomotopy_apply hV hr hS t z }⟩
  right_inv := by
    rw [radialProjectionToSphere_comp_sphereInclusionDiffSingleton]
    exact ContinuousMap.HomotopicWith.refl _ (ContinuousMap.id_comp _)

@[simp]
theorem _root_.StarConvex.radialProjectionFiberHomotopyEquiv_toFun (hV : StarConvex ℝ p V)
    (hr : 0 < r) (hS : sphere p r ⊆ V) :
    (hV.radialProjectionFiberHomotopyEquiv hr hS).toFun = radialProjectionToSphere hr :=
  (rfl)

@[simp]
theorem _root_.StarConvex.radialProjectionFiberHomotopyEquiv_invFun (hV : StarConvex ℝ p V)
    (hr : 0 < r) (hS : sphere p r ⊆ V) :
    (hV.radialProjectionFiberHomotopyEquiv hr hS).invFun =
      sphereInclusionDiffSingleton hr.ne' hS :=
  (rfl)

end StarConvex

section Radial

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Radial projection sends a point `x ≠ 0` to the point `p` of the unit sphere exactly when `x`
lies on the open ray through `p`. -/
theorem complSingletonHomotopyEquivSphere_zero_apply_eq_iff (x : ({0}ᶜ : Set E))
    (p : sphere (0 : E) 1) :
    complSingletonHomotopyEquivSphere (0 : E) x = p ↔ ∃ t : ℝ, 0 < t ∧ t • (p : E) = x := by
  have hx : 0 < ‖(x : E)‖ := norm_pos_iff.2 x.property
  rw [Subtype.ext_iff, coe_complSingletonHomotopyEquivSphere_apply, sub_zero]
  constructor
  · intro h
    refine ⟨‖(x : E)‖, hx, ?_⟩
    rw [← h, smul_smul, mul_inv_cancel₀ hx.ne', one_smul]
  · rintro ⟨t, ht, h⟩
    rw [← h, norm_smul, norm_eq_of_mem_sphere p, mul_one, Real.norm_of_nonneg ht.le, smul_smul,
      inv_mul_cancel₀ ht.ne', one_smul]

/-- Radial projection about `0` is `TauCeti.complSingletonHomotopyEquivSphere 0`, read on
`univ ∖ {0}`. -/
theorem radialProjectionToSphere_setCongr_compl_eq_univ_sdiff (x : ({0}ᶜ : Set E)) :
    radialProjectionToSphere (V := univ) (p := (0 : E)) one_pos
        (Homeomorph.setCongr (compl_eq_univ_sdiff {0}) x) =
      complSingletonHomotopyEquivSphere (0 : E) x := by
  ext1
  rw [coe_radialProjectionToSphere_apply, coe_complSingletonHomotopyEquivSphere_apply]
  -- `Homeomorph.setCongr` has no evaluation lemma; it does not move points.
  simp only [zero_add, sub_zero, one_div]
  rfl

variable (W : Set (sphere (0 : E) 1))

/-- The punctured cone over a subset `W` of the unit sphere, the points `x ≠ 0` whose radial
projection lies in `W`, is homotopy equivalent to `W`: radial projection is a homotopy
equivalence, with the inclusion of `W` as homotopy inverse. -/
def complZeroPreimageHomotopyEquiv :
    ↥(complSingletonHomotopyEquivSphere (0 : E) ⁻¹' W) ≃ₕ ↥W :=
  (((Homeomorph.setCongr (compl_eq_univ_sdiff {(0 : E)})).subtype
      (p := (· ∈ complSingletonHomotopyEquivSphere (0 : E) ⁻¹' W))
      (q := (· ∈ radialProjectionToSphere (V := univ) (p := (0 : E)) one_pos ⁻¹' W)) fun x ↦ by
        rw [Set.mem_preimage, Set.mem_preimage,
          radialProjectionToSphere_setCongr_compl_eq_univ_sdiff]).toHomotopyEquiv.trans
    (((starConvex_univ (0 : E)).radialProjectionFiberHomotopyEquiv one_pos
      (subset_univ _)).restrictPreimage W).toHomotopyEquiv).trans
    (Homeomorph.setCongr (by rw [ContinuousMap.coe_id, preimage_id])).toHomotopyEquiv

/-- The homotopy equivalence `TauCeti.complZeroPreimageHomotopyEquiv` is radial projection. -/
@[simp]
theorem coe_complZeroPreimageHomotopyEquiv_apply
    (x : ↥(complSingletonHomotopyEquivSphere (0 : E) ⁻¹' W)) :
    (complZeroPreimageHomotopyEquiv W x : sphere (0 : E) 1) =
      complSingletonHomotopyEquivSphere (0 : E) x := by
  rw [complZeroPreimageHomotopyEquiv, ContinuousMap.HomotopyEquiv.trans_apply,
    ContinuousMap.HomotopyEquiv.trans_apply, Homeomorph.coe_toHomotopyEquiv,
    FiberHomotopyEquiv.toHomotopyEquiv_apply]
  -- `Homeomorph.setCongr` and `Homeomorph.subtype` have no evaluation lemmas; they do not move
  -- points.
  exact (FiberHomotopyEquiv.coe_restrictPreimage_toFun_apply _ W _).trans
    (radialProjectionToSphere_setCongr_compl_eq_univ_sdiff _)

/-- The homotopy inverse of `TauCeti.complZeroPreimageHomotopyEquiv` is the inclusion of `W`. -/
@[simp]
theorem coe_complZeroPreimageHomotopyEquiv_symm_apply (y : W) :
    (((complZeroPreimageHomotopyEquiv W).symm y : ({0}ᶜ : Set E)) : E) = y := by
  rw [complZeroPreimageHomotopyEquiv, ContinuousMap.HomotopyEquiv.symm_trans,
    ContinuousMap.HomotopyEquiv.symm_trans, ContinuousMap.HomotopyEquiv.trans_apply,
    ContinuousMap.HomotopyEquiv.trans_apply, FiberHomotopyEquiv.toHomotopyEquiv_symm_apply]
  -- `Homeomorph.setCongr` and `Homeomorph.subtype` have no evaluation lemmas; they do not move
  -- points.
  exact (congrArg Subtype.val (FiberHomotopyEquiv.coe_restrictPreimage_invFun_apply
    ((starConvex_univ (0 : E)).radialProjectionFiberHomotopyEquiv one_pos (subset_univ _))
      W _)).trans
    (coe_sphereInclusionDiffSingleton_apply _ _ _)

end Radial

section ComplRay

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A real vector space has unique division by nonzero natural numbers; this lets Tau Ceti's
cover of a sphere by the complements of two antipodal points apply. -/
local instance : HasUniqueDiv E := HasUniqueDiv.of_isTorsionFree ℝ E

/-- The points of `E ∖ {0}` off the open ray `{t • p | t > 0}` through a point `p` of the unit
sphere: those whose radial projection is not `p` (`TauCeti.mem_complRay_iff`). -/
def complRay (p : sphere (0 : E) 1) : Set ({0}ᶜ : Set E) :=
  complSingletonHomotopyEquivSphere (0 : E) ⁻¹' {p}ᶜ

theorem complRay_def (p : sphere (0 : E) 1) :
    complRay p = complSingletonHomotopyEquivSphere (0 : E) ⁻¹' {p}ᶜ :=
  (rfl)

/-- A point lies in `TauCeti.complRay p` exactly when it is not a positive multiple of `p`. -/
theorem mem_complRay_iff {p : sphere (0 : E) 1} {x : ({0}ᶜ : Set E)} :
    x ∈ complRay p ↔ ∀ t : ℝ, 0 < t → t • (p : E) ≠ x := by
  rw [complRay_def, Set.mem_preimage, Set.mem_compl_singleton_iff, Ne,
    complSingletonHomotopyEquivSphere_zero_apply_eq_iff]
  push Not
  rfl

theorem isOpen_complRay (p : sphere (0 : E) 1) : IsOpen (complRay p) :=
  isOpen_compl_singleton.preimage (map_continuous _)

/-- Radial projection carries `TauCeti.complRay p` into the complement of `p` in the sphere. -/
theorem mapsTo_complRay (p : sphere (0 : E) 1) :
    Set.MapsTo (complSingletonHomotopyEquivSphere (0 : E)) (complRay p) {p}ᶜ :=
  Set.mapsTo_preimage _ _

/-- The complements of the two rays through `p` and `-p` cover `E ∖ {0}`. -/
theorem complRay_union_complRay_neg (p : sphere (0 : E) 1) :
    complRay p ∪ complRay (-p) = Set.univ := by
  rw [complRay_def, complRay_def, ← Set.preimage_union,
    compl_singleton_union_compl_singleton_neg one_ne_zero p, Set.preimage_univ]

/-- The intersection of `TauCeti.complRay p` and `TauCeti.complRay (-p)` is the complement of the
line through `p`. -/
theorem mem_complRay_inter_complRay_neg_iff {p : sphere (0 : E) 1} {x : ({0}ᶜ : Set E)} :
    x ∈ complRay p ∩ complRay (-p) ↔ (x : E) ∉ ℝ ∙ (p : E) := by
  have hx : ‖(x : E)‖⁻¹ ≠ 0 := inv_ne_zero (norm_ne_zero_iff.2 x.property)
  rw [complRay_def, complRay_def, ← Set.preimage_inter, Set.mem_preimage,
    compl_singleton_inter_compl_singleton_neg_eq, Set.mem_ofPred_eq,
    coe_complSingletonHomotopyEquivSphere_apply, sub_zero, Submodule.smul_mem_iff _ hx]

/-- `TauCeti.complRay p` is contractible: as a subset of `E` it is the complement of the closed
ray `{t • p | t ≥ 0}`, which is star-convex about `-p`. -/
instance contractibleSpace_complRay (p : sphere (0 : E) 1) : ContractibleSpace (complRay p) := by
  set S : Set E := {y | ∀ t : ℝ, 0 ≤ t → t • (p : E) ≠ y}
  have hp : (p : E) ≠ 0 := ne_zero_of_mem_unit_sphere p
  have hS : StarConvex ℝ (-(p : E)) S := by
    intro y hy a b ha hb hab t ht h
    have hby : b • y = (t + a) • (p : E) := by
      rw [add_smul, h, smul_neg]; abel
    rcases hb.eq_or_lt with rfl | hb
    · rw [zero_smul] at hby
      exact hp ((smul_eq_zero.1 hby.symm).resolve_left (by linarith))
    · refine hy ((t + a) / b) (div_nonneg (by linarith) hb.le) ?_
      rw [div_eq_inv_mul, mul_smul, ← hby, smul_smul, inv_mul_cancel₀ hb.ne', one_smul]
  have hemb : Topology.IsEmbedding fun x : complRay p ↦ ((x : ({0}ᶜ : Set E)) : E) :=
    Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal
  have hrange : Set.range (fun x : complRay p ↦ ((x : ({0}ᶜ : Set E)) : E)) = S := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩ t ht h
      rcases ht.eq_or_lt with rfl | ht
      · exact (x : ({0}ᶜ : Set E)).property (by simpa using h.symm)
      · exact mem_complRay_iff.1 x.property t ht h
    · intro hy
      have hy0 : y ≠ 0 := fun h ↦ hy 0 le_rfl (by simp [h])
      exact ⟨⟨⟨y, hy0⟩, mem_complRay_iff.2 fun t ht ↦ hy t ht.le⟩, rfl⟩
  have : ContractibleSpace S := hS.contractibleSpace ⟨-(p : E), fun t ht h ↦ hp (by
    have h' : (t + 1) • (p : E) = 0 := by rw [add_smul, one_smul, h, neg_add_cancel]
    exact (smul_eq_zero.1 h').resolve_left (by linarith))⟩
  exact (hemb.toHomeomorph.trans (Homeomorph.setCongr hrange)).contractibleSpace

end ComplRay

section InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The points `x ≠ 0` of the orthogonal complement of a unit vector `p` lie off the line through
`p`: they are in both `TauCeti.complRay p` and `TauCeti.complRay (-p)`. -/
theorem mem_complRay_inter_complRay_neg_of_mem_orthogonal (p : sphere (0 : E) 1)
    (x : ({0}ᶜ : Set (ℝ ∙ (p : E))ᗮ)) :
    (⟨(x : (ℝ ∙ (p : E))ᗮ), fun h ↦ x.property (Subtype.ext h)⟩ : ({0}ᶜ : Set E)) ∈
      complRay p ∩ complRay (-p) :=
  mem_complRay_inter_complRay_neg_iff.2 fun h ↦ x.property <| Subtype.ext <|
    Submodule.disjoint_def.1 (Submodule.orthogonal_disjoint _) _ h (x : (ℝ ∙ (p : E))ᗮ).property

/-- The inclusion of the punctured orthogonal complement `(ℝ ∙ p)ᗮ ∖ {0}` of a unit vector `p`
into the complement in `E ∖ {0}` of the line through `p`, the intersection of
`TauCeti.complRay p` and `TauCeti.complRay (-p)`. -/
def complZeroOrthogonalInclusion (p : sphere (0 : E) 1) :
    C(↥({0}ᶜ : Set (ℝ ∙ (p : E))ᗮ), ↥(complRay p ∩ complRay (-p))) where
  toFun x := ⟨_, mem_complRay_inter_complRay_neg_of_mem_orthogonal p x⟩
  continuous_toFun := by fun_prop

@[simp]
theorem coe_complZeroOrthogonalInclusion_apply (p : sphere (0 : E) 1)
    (x : ({0}ᶜ : Set (ℝ ∙ (p : E))ᗮ)) :
    ((complZeroOrthogonalInclusion p x : ({0}ᶜ : Set E)) : E) = (x : (ℝ ∙ (p : E))ᗮ) :=
  (rfl)

/-- **The complement of a line is homotopy equivalent to the equator.** For a point `p` of the
unit sphere, the points of `E ∖ {0}` off the line through `p`, the intersection of
`TauCeti.complRay p` and `TauCeti.complRay (-p)`, form a space homotopy equivalent to the unit
sphere of `(ℝ ∙ p)ᗮ`: radial projection onto the sphere minus `±p`, followed by
`TauCeti.equatorHomotopyEquiv p`. -/
def complRayInterHomotopyEquiv (p : sphere (0 : E) 1) :
    ↥(complRay p ∩ complRay (-p)) ≃ₕ sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 :=
  (complZeroPreimageHomotopyEquiv ({p}ᶜ ∩ {-p}ᶜ)).trans (equatorHomotopyEquiv p)

/-- `TauCeti.complRayInterHomotopyEquiv p` is radial projection onto the sphere minus `±p`,
followed by `TauCeti.equatorHomotopyEquiv p`. -/
@[simp]
theorem complRayInterHomotopyEquiv_apply (p : sphere (0 : E) 1)
    (x : ↥(complRay p ∩ complRay (-p))) :
    complRayInterHomotopyEquiv p x =
      equatorHomotopyEquiv p ⟨complSingletonHomotopyEquivSphere (0 : E) x,
        (mapsTo_complRay p).inter_inter (mapsTo_complRay (-p)) x.property⟩ :=
  congrArg (equatorHomotopyEquiv p)
    (Subtype.ext (coe_complZeroPreimageHomotopyEquiv_apply ({p}ᶜ ∩ {-p}ᶜ) x))

/-- The homotopy inverse of `TauCeti.complRayInterHomotopyEquiv p` is the inclusion of the unit
sphere of `(ℝ ∙ p)ᗮ`. -/
@[simp]
theorem coe_complRayInterHomotopyEquiv_symm_apply (p : sphere (0 : E) 1)
    (y : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1) :
    (((complRayInterHomotopyEquiv p).symm y : ({0}ᶜ : Set E)) : E) = ((y : (ℝ ∙ (p : E))ᗮ) : E) :=
  (coe_complZeroPreimageHomotopyEquiv_symm_apply _ _).trans
    (coe_equatorHomotopyEquiv_symm_apply p y)

/-- `TauCeti.complRayInterHomotopyEquiv p`, as a continuous map, is the restriction of radial
projection, followed by `TauCeti.equatorHomotopyEquiv p`. -/
theorem complRayInterHomotopyEquiv_toFun (p : sphere (0 : E) 1) :
    (complRayInterHomotopyEquiv p).toFun = (equatorHomotopyEquiv p).toFun.comp
      ⟨((mapsTo_complRay p).inter_inter (mapsTo_complRay (-p))).restrict,
        (map_continuous _).restrict _⟩ :=
  ContinuousMap.ext (complRayInterHomotopyEquiv_apply p)

/-- On the punctured orthogonal complement `(ℝ ∙ p)ᗮ ∖ {0}`, the homotopy equivalence
`TauCeti.complRayInterHomotopyEquiv p` is radial projection in `(ℝ ∙ p)ᗮ`. -/
theorem complRayInterHomotopyEquiv_toFun_comp_complZeroOrthogonalInclusion
    (p : sphere (0 : E) 1) :
    (complRayInterHomotopyEquiv p).toFun.comp (complZeroOrthogonalInclusion p) =
      (complSingletonHomotopyEquivSphere (0 : (ℝ ∙ (p : E))ᗮ)).toFun := by
  ext x
  have hpos : 0 < ‖(x : (ℝ ∙ (p : E))ᗮ)‖ := norm_pos_iff.2 x.property
  rw [ContinuousMap.comp_apply, complRayInterHomotopyEquiv_apply,
    coe_equatorHomotopyEquiv_apply, coe_complSingletonHomotopyEquivSphere_apply,
    coe_complSingletonHomotopyEquivSphere_apply, coe_complZeroOrthogonalInclusion_apply]
  simp only [sub_zero, Submodule.coe_smul, Submodule.norm_coe]
  rw [Submodule.starProjection_eq_self_iff.2 (Submodule.smul_mem _ _ (x : (ℝ ∙ (p : E))ᗮ).property),
    NormedSpace.normalize_smul_of_pos (inv_pos.2 hpos), NormedSpace.normalize, Submodule.norm_coe]

end InnerProductSpace

end TauCeti
