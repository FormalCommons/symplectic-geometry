/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Collar.Smooth
public import TauCeti.Geometry.Manifold.Boundary.Interior
import SymplecticGeometry.Geometry.Manifold.Boundary.Interior
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.OpenSubset

/-!
# Collar coordinates on the interior

Let `W` be a manifold with boundary, modelled on the half-space `EuclideanHalfSpace (n + 1)`, and
`c : ∂W × [0, 1) → W` a `C^k` collar of its boundary. A collar point `c (x, t)` is an interior
point of `W` exactly when its depth `t` is positive. This file gives the inverse of the collar on
the interior of `W`, as Tau Ceti's charted interior `(𝓡∂ (n + 1)).interior W` over `ℝⁿ⁺¹`: on
the open subset `c.interiorRange` of the points covered by the collar, the collar
coordinates `c.interiorCoord` form a `C^k` local diffeomorphism into `∂W × [0, 1)` that
takes values of positive depth. Gluings of other manifolds to the interior of `W` along the
collar, such as attaching an end (`Boundary/Collar/End.lean`) or capping boundary circles with
discs (`Gluing/CapDiscs/Basic.lean`), are built on these coordinates.

## Main definitions

* `TauCeti.SmoothCollar.interiorRange`: the part of the charted interior of `W`, over
  `ℝⁿ⁺¹`, covered by the collar.
* `TauCeti.SmoothCollar.interiorCoord`: the collar coordinates of a point of it.

## Main results

* `TauCeti.SmoothCollar.apply_mem_interior_iff`, `apply_mem_interior_iff_pos`: a collar point is
  interior exactly when its depth is not zero, or positive.
* `TauCeti.SmoothCollar.apply_interiorCoord`: the collar sends the collar coordinates of a
  point back to the point.
* `TauCeti.SmoothCollar.isLocalDiffeomorph_interiorCoord`: the collar coordinates are a
  smooth local diffeomorphism.

## References

* M. W. Hirsch, *Differential Topology*, Springer GTM 33, 1976, Chapter 4, §6 (collars).
-/

public section

open Set Function TopologicalSpace
open scoped Manifold ContDiff

noncomputable section

namespace TauCeti.SmoothCollar
open _root_.TauCeti.EuclideanHalfSpace

variable {n : ℕ} {W : Type*} [TopologicalSpace W] [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
  {k : WithTop ℕ∞} (c : SmoothCollar n k W)

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

/-- The part of the charted interior of `W`, modelled on `ℝⁿ⁺¹`, covered by the
collar: the points `c (x, t)` with `t > 0`. -/
def interiorRange : Opens ((𝓡∂ (n + 1)).interior W) :=
  ⟨Subtype.val ⁻¹' range c, c.isOpen_range.preimage continuous_subtypeVal⟩

theorem mem_interiorRange {q : (𝓡∂ (n + 1)).interior W} :
    q ∈ c.interiorRange ↔ q.val ∈ range c := Iff.rfl

/-- A point of `c.interiorRange` lies in the image of the collar. -/
theorem val_mem_opensRange (q : c.interiorRange) : q.val.val ∈ c.opensRange :=
  c.mem_opensRange.2 (c.mem_interiorRange.1 q.property)

/-- The collar coordinates `(x, t)` of a point `c (x, t)` of the interior covered by the
collar. -/
def interiorCoord (q : c.interiorRange) :
    ↥((𝓡∂ (n + 1)).boundary W) × normalIioOpens 1 :=
  c.diffeomorphOpensRange.symm ⟨q.val.val, c.val_mem_opensRange q⟩

theorem interiorCoord_def (q : c.interiorRange) :
    c.interiorCoord q = c.diffeomorphOpensRange.symm ⟨q.val.val, c.val_mem_opensRange q⟩ :=
  (rfl)

@[simp] theorem apply_interiorCoord (q : c.interiorRange) :
    c (c.interiorCoord q) = q.val.val :=
  c.apply_diffeomorphOpensRange_symm _

/-- The collar coordinates of a point are the unique preimage of the point under the collar. -/
theorem interiorCoord_eq_iff {q : c.interiorRange}
    {p : ↥((𝓡∂ (n + 1)).boundary W) × normalIioOpens 1} :
    c.interiorCoord q = p ↔ c p = q.val.val :=
  ⟨fun h ↦ h ▸ c.apply_interiorCoord q,
    fun h ↦ c.injective (by rw [apply_interiorCoord, h])⟩

theorem continuous_interiorCoord : Continuous c.interiorCoord :=
  c.diffeomorphOpensRange.symm.continuous.comp
    (Continuous.subtype_mk (continuous_subtypeVal.comp continuous_subtypeVal) _)

/-- The collar coordinates of a point of the interior have positive depth. -/
theorem interiorCoord_snd_pos (q : c.interiorRange) :
    0 < ((c.interiorCoord q).2 : EuclideanHalfSpace 1).val 0 := by
  rw [← apply_mem_interior_iff_pos, apply_interiorCoord]
  exact q.val.property

/-- The collar coordinates are a `C^k` local diffeomorphism from the interior, modelled on
`ℝⁿ⁺¹`, to `∂W × [0, 1)`. -/
theorem isLocalDiffeomorph_interiorCoord [IsManifold (𝓡∂ (n + 1)) 1 W] :
    IsLocalDiffeomorph (𝓡 (n + 1)) ((𝓡 n).prod (𝓡∂ 1)) k c.interiorCoord := by
  intro q
  have hg : IsLocalDiffeomorphAt (𝓡 (n + 1)) (𝓡∂ (n + 1)) k
      (fun q : c.interiorRange ↦ (⟨q.val.val, c.val_mem_opensRange q⟩ : c.opensRange)) q := by
    refine isLocalDiffeomorphAt_subtypeVal_comp_iff.1 ?_
    exact (isLocalDiffeomorph_subtype_val q).comp
      (hg := (𝓡∂ (n + 1)).isLocalDiffeomorph_subtypeVal_interior _)
  exact hg.comp (hg := c.diffeomorphOpensRange.symm.isLocalDiffeomorph _)

end TauCeti.SmoothCollar

end
