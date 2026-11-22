/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.ModelTransport.InteriorModel
public import TauCeti.Geometry.Manifold.Boundary.Collar.Smooth
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.OpenSubset

/-!
# Collar coordinates on the interior

Let `W` be a manifold with boundary, modelled on the half-space `EuclideanHalfSpace (n + 1)`, and
`c : ∂W × [0, 1) → W` a smooth collar of its boundary. A collar point `c (x, t)` is an interior
point of `W` exactly when its depth `t` is positive. This file gives the inverse of the collar on
the interior of `W`, re-modelled on `ℝⁿ⁺¹` as `SymplecticGeometry.InteriorModel`: on the open
subset `c.interiorModelRange` of the points covered by the collar, the collar coordinates
`c.interiorModelCoord` form a smooth local diffeomorphism into `∂W × [0, 1)` that takes values
of positive depth. Gluings of other manifolds to the interior of `W` along the collar, such as
attaching an end (`Boundary/Collar/End.lean`) or capping boundary circles with discs
(`Gluing/CapDiscs/Basic.lean`), are built on these coordinates.

## Main definitions

* `TauCeti.SmoothCollar.interiorModelRange`: the part of the interior of `W`, re-modelled on
  `ℝⁿ⁺¹`, covered by the collar.
* `TauCeti.SmoothCollar.interiorModelCoord`: the collar coordinates of a point of it.

## Main results

* `TauCeti.SmoothCollar.apply_mem_interior_iff`, `apply_mem_interior_iff_pos`: a collar point is
  interior exactly when its depth is not zero, or positive.
* `TauCeti.SmoothCollar.apply_interiorModelCoord`: the collar sends the collar coordinates of a
  point back to the point.
* `TauCeti.SmoothCollar.isLocalDiffeomorph_interiorModelCoord`: the collar coordinates are a
  smooth local diffeomorphism.

## References

* M. W. Hirsch, *Differential Topology*, Springer GTM 33, 1976, Chapter 4, §6 (collars).
-/

public section

open Set Function TopologicalSpace SymplecticGeometry
open scoped Manifold ContDiff

noncomputable section

namespace TauCeti.SmoothCollar
open _root_.TauCeti.EuclideanHalfSpace

variable {n : ℕ} {W : Type*} [TopologicalSpace W] [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
  (c : SmoothCollar n ∞ W)

/-- A collar point lies in the interior exactly when its depth is not zero. -/
theorem apply_mem_interior_iff (p : ↥((𝓡∂ (n + 1)).boundary W) × normalIioOpens 1) :
    c p ∈ (𝓡∂ (n + 1)).interior W ↔ p.2 ≠ normalIioOpensZero one_pos := by
  rw [← ModelWithCorners.compl_boundary, mem_compl_iff, apply_mem_boundary_iff]

/-- A collar point lies in the interior exactly when its depth is positive. -/
theorem apply_mem_interior_iff_pos (p : ↥((𝓡∂ (n + 1)).boundary W) × normalIioOpens 1) :
    c p ∈ (𝓡∂ (n + 1)).interior W ↔ 0 < (p.2 : EuclideanHalfSpace 1).val 0 := by
  rw [apply_mem_interior_iff, ((p.2 : EuclideanHalfSpace 1).property).lt_iff_ne', Ne, Ne,
    ← Subtype.coe_inj, coe_normalIioOpensZero, EuclideanHalfSpace.eq_zero_iff]

/-- The collar undoes the inverse of its diffeomorphism onto its image. -/
@[simp] theorem apply_diffeomorphOpensRange_symm (w : c.opensRange) :
    c (c.diffeomorphOpensRange.symm w) = w := by
  rw [← coe_diffeomorphOpensRange_apply, Diffeomorph.apply_symm_apply]

variable [IsManifold (𝓡∂ (n + 1)) ∞ W]

/-- The part of the interior of `W`, re-modelled on `ℝⁿ⁺¹` as `InteriorModel`, covered by the
collar: the points `c (x, t)` with `t > 0`. -/
def interiorModelRange :
    Opens (InteriorModel (𝓡∂ (n + 1)) ((𝓡∂ (n + 1)).interiorOpens W)) :=
  ⟨InteriorModel.val ⁻¹' range c, c.isOpen_range.preimage InteriorModel.continuous_val⟩

theorem mem_interiorModelRange
    {q : InteriorModel (𝓡∂ (n + 1)) ((𝓡∂ (n + 1)).interiorOpens W)} :
    q ∈ c.interiorModelRange ↔ q.val ∈ range c := Iff.rfl

/-- A point of `c.interiorModelRange` lies in the image of the collar. -/
theorem val_mem_opensRange (q : c.interiorModelRange) : q.val.val ∈ c.opensRange :=
  c.mem_opensRange.2 (c.mem_interiorModelRange.1 q.property)

/-- The collar coordinates `(x, t)` of a point `c (x, t)` of the interior covered by the
collar. -/
def interiorModelCoord (q : c.interiorModelRange) :
    ↥((𝓡∂ (n + 1)).boundary W) × normalIioOpens 1 :=
  c.diffeomorphOpensRange.symm ⟨q.val.val, c.val_mem_opensRange q⟩

theorem interiorModelCoord_def (q : c.interiorModelRange) :
    c.interiorModelCoord q = c.diffeomorphOpensRange.symm ⟨q.val.val, c.val_mem_opensRange q⟩ :=
  (rfl)

@[simp] theorem apply_interiorModelCoord (q : c.interiorModelRange) :
    c (c.interiorModelCoord q) = q.val.val :=
  c.apply_diffeomorphOpensRange_symm _

/-- The collar coordinates of a point are the unique preimage of the point under the collar. -/
theorem interiorModelCoord_eq_iff {q : c.interiorModelRange}
    {p : ↥((𝓡∂ (n + 1)).boundary W) × normalIioOpens 1} :
    c.interiorModelCoord q = p ↔ c p = q.val.val :=
  ⟨fun h ↦ h ▸ c.apply_interiorModelCoord q,
    fun h ↦ c.injective (by rw [apply_interiorModelCoord, h])⟩

theorem continuous_interiorModelCoord : Continuous c.interiorModelCoord :=
  c.diffeomorphOpensRange.symm.continuous.comp
    (Continuous.subtype_mk (InteriorModel.continuous_val.comp continuous_subtypeVal) _)

/-- The collar coordinates of a point of the interior have positive depth. -/
theorem interiorModelCoord_snd_pos (q : c.interiorModelRange) :
    0 < ((c.interiorModelCoord q).2 : EuclideanHalfSpace 1).val 0 := by
  rw [← apply_mem_interior_iff_pos, apply_interiorModelCoord]
  exact q.val.val_mem_interior

/-- The collar coordinates are a smooth local diffeomorphism from the interior, modelled on
`ℝⁿ⁺¹`, to `∂W × [0, 1)`. -/
theorem isLocalDiffeomorph_interiorModelCoord :
    IsLocalDiffeomorph (𝓡 (n + 1)) ((𝓡 n).prod (𝓡∂ 1)) ∞ c.interiorModelCoord := by
  intro q
  have hg : IsLocalDiffeomorphAt (𝓡 (n + 1)) (𝓡∂ (n + 1)) ∞
      (fun q : c.interiorModelRange ↦ (⟨q.val.val, c.val_mem_opensRange q⟩ : c.opensRange)) q := by
    refine isLocalDiffeomorphAt_subtypeVal_comp_iff.1 ?_
    exact (isLocalDiffeomorph_subtype_val q).comp (hg := InteriorModel.isLocalDiffeomorph_val _)
  exact hg.comp (hg := c.diffeomorphOpensRange.symm.isLocalDiffeomorph _)

end TauCeti.SmoothCollar

end
