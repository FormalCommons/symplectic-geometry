/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Boundary.Collar.Push
public import TauCeti.Topology.Homotopy.Extension.NDRPair

/-!
# A collared subset is a closed cofibration

Let `c : N × [0, 1) → X` be a collar of `f : N → X` (`TauCeti.IsCollar`), with `N` compact and
`X` Hausdorff. Then the image `f(N)` has the homotopy extension property in `X`
(`TauCeti.IsCollar.hasHomotopyExtensionProperty_range`).

The proof builds NDR data for `f(N)` with `TauCeti.NDRPair.ofHomotopyRel`. The neighbourhood is
the whole collar `c(N × [0, 1))`, deformed onto `f(N)` relative to `f(N)` by scaling the depth
(`TauCeti.IsCollar.collarDeformation`). The control function is twice the depth, clipped to
`[0, 1]`, on the collar, and `1` off it: it is less than `1` exactly on `c(N × [0, 1/2))`. It is
continuous because, `N` being compact, `c(N × [0, 1/2])` is compact and so closed in `X`, and the
function is `1` off that set (`TauCeti.IsCollar.isCompact_image_setOf_le`).

## Main results

* `TauCeti.IsCollar.hasHomotopyExtensionProperty_range`: the image of a map with a collar, from a
  compact space into a Hausdorff space, has the homotopy extension property.
* `TauCeti.IsCollared.hasHomotopyExtensionProperty_range`: the same for a collared map.

## References

* N. E. Steenrod, *A convenient category of topological spaces*, Michigan Math. J. 14 (1967),
  133–152, Section 6, for NDR pairs.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.3, proof of
  Theorem 3.43, for the deformation of a collar onto the boundary.
-/

public section

noncomputable section

namespace TauCeti

open Set Topology unitInterval

variable {X N : Type*} [TopologicalSpace X] [TopologicalSpace N] {f : N → X}
  {c : N × Ico (0 : ℝ) 1 → X}

namespace IsCollar

variable (hc : IsCollar f c)
include hc

open Classical in
/-- Twice the depth of a collar point, clipped to `[0, 1]`, and `1` off the collar. -/
private def depthControlFun (x : X) : I :=
  if h : x ∈ collarPart c 1 then
    projIcc (0 : ℝ) 1 zero_le_one (2 * ((hc.collarCoord 1 ⟨x, h⟩).2 : ℝ))
  else 1

private lemma depthControlFun_of_mem {x : X} (h : x ∈ collarPart c 1) :
    hc.depthControlFun x =
      projIcc (0 : ℝ) 1 zero_le_one (2 * ((hc.collarCoord 1 ⟨x, h⟩).2 : ℝ)) := by
  simp [depthControlFun, h]

private lemma depthControlFun_of_notMem {x : X} (h : x ∉ collarPart c 1) :
    hc.depthControlFun x = 1 := by
  simp [depthControlFun, h]

/-- The control function is `1` at every point outside `c(N × [0, 1/2))`. -/
private lemma depthControlFun_eq_one {x : X} (hx : x ∉ collarPart c (1 / 2)) :
    hc.depthControlFun x = 1 := by
  by_cases h : x ∈ collarPart c 1
  · rw [hc.depthControlFun_of_mem h, projIcc_eq_one]
    by_contra hlt
    exact hx (mem_collarPart_iff.2 ⟨hc.collarCoord 1 ⟨x, h⟩, by linarith, hc.apply_collarCoord _⟩)
  · exact hc.depthControlFun_of_notMem h

private lemma continuous_depthControlFun [CompactSpace N] [T2Space X] :
    Continuous hc.depthControlFun := by
  refine continuous_iff_continuousAt.2 fun x ↦ ?_
  by_cases h : x ∈ collarPart c 1
  · refine ContinuousOn.continuousAt ?_ ((hc.isOpen_collarPart 1).mem_nhds h)
    rw [continuousOn_iff_continuous_domRestrict]
    refine Continuous.congr (f := fun y : collarPart c 1 ↦ projIcc (0 : ℝ) 1 zero_le_one
      (2 * ((hc.collarCoord 1 y).2 : ℝ))) (by fun_prop) fun y ↦ ?_
    exact (hc.depthControlFun_of_mem y.property).symm
  · -- Off the collar, `x` lies outside the closed set `c(N × [0, 1/2])`, where the function is
    -- `1`.
    have hK := (hc.isCompact_image_setOf_le (t := 1 / 2) (by norm_num)).isClosed
    have hxK : x ∉ c '' {p | (p.2 : ℝ) ≤ 1 / 2} := by
      rintro ⟨p, hp, rfl⟩
      have hp : (p.2 : ℝ) ≤ 1 / 2 := hp
      exact h (mem_collarPart_iff.2 ⟨p, by linarith, rfl⟩)
    refine continuousAt_const.congr (Filter.eventuallyEq_of_mem (hK.isOpen_compl.mem_nhds hxK)
      fun y hy ↦ (hc.depthControlFun_eq_one fun hy' ↦ hy ?_).symm)
    obtain ⟨p, hp, rfl⟩ := mem_collarPart_iff.1 hy'
    exact ⟨p, show (p.2 : ℝ) ≤ 1 / 2 from hp.le, rfl⟩

/-- The control function vanishes exactly on the boundary `f(N)`. -/
private lemma depthControlFun_eq_zero_iff (x : X) :
    hc.depthControlFun x = 0 ↔ x ∈ range f := by
  by_cases h : x ∈ collarPart c 1
  · rw [hc.depthControlFun_of_mem h, projIcc_eq_zero]
    have hx := hc.apply_collarCoord ⟨x, h⟩
    set p := hc.collarCoord 1 ⟨x, h⟩
    refine ⟨fun hp ↦ ⟨p.1, ?_⟩, fun ⟨y, hy⟩ ↦ ?_⟩
    · rw [← hc.apply_zero]
      refine Eq.trans ?_ hx
      exact congrArg c (Prod.ext rfl (Subtype.ext (by linarith [p.2.property.1])))
    · have hp : p = (y, ⟨0, by norm_num⟩) :=
        hc.collarCoord_apply _ _ ((hc.apply_zero y).trans hy)
      rw [hp]
      simp
  · rw [hc.depthControlFun_of_notMem h]
    exact ⟨fun h1 ↦ absurd h1 one_ne_zero,
      fun hx ↦ absurd (hc.range_subset_collarPart one_pos hx) h⟩

/-- **A collared subset is a closed cofibration.** If `c` is a collar of `f : N → X`, with `N`
compact and `X` Hausdorff, then the image of `f` has the homotopy extension property in `X`. -/
theorem hasHomotopyExtensionProperty_range [CompactSpace N] [T2Space X] :
    HasHomotopyExtensionProperty (range f) :=
  (NDRPair.ofHomotopyRel (hc.range_subset_collarPart one_pos)
    (hc.collarDeformation one_pos).symm ⟨hc.depthControlFun, hc.continuous_depthControlFun⟩
    hc.depthControlFun_eq_zero_iff fun x hx ↦ by
      by_contra h
      exact (lt_irrefl _ ((hc.depthControlFun_of_notMem h) ▸ hx))).hasHomotopyExtensionProperty

end IsCollar

/-- **A collared subset is a closed cofibration.** If `f : N → X` admits a collar, with `N`
compact and `X` Hausdorff, then the image of `f` has the homotopy extension property in `X`. -/
theorem IsCollared.hasHomotopyExtensionProperty_range [CompactSpace N] [T2Space X]
    (h : IsCollared f) : HasHomotopyExtensionProperty (range f) := by
  obtain ⟨_, hc⟩ := isCollared_iff.1 h
  exact hc.hasHomotopyExtensionProperty_range

end TauCeti

end
