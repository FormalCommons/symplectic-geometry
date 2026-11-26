/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.DiscComplement.Basic
import SymplecticGeometry.Geometry.Manifold.RegularValue.ChartBall

/-!
# Regular sublevel sets around a coordinate disc and its complement

Let `e` be a chart of the smooth maximal atlas of a Hausdorff smooth surface `M`, and
`CoordinateDisc.ofChart e hr hc he` the coordinate disc it gives. This file gives two smooth
functions on `M` with regular value `0`: one whose strict sublevel set contains the closed disc,
and one whose strict sublevel set contains the complement `discComplement` of the open disc. In
both cases the sublevel set is connected (for the second, when `M` is) and the level set is
nonempty, so Tau Ceti's `TauCeti.isManifold_scalarRegularSublevel` and
`TauCeti.boundary_scalarRegularSublevel` make the sublevel set a connected surface with nonempty
boundary. The first sublevel set is moreover compact, whether or not `M` is.

The sublevel sets are the images under `e.symm` of a closed ball of radius `3r/4` and the
complement of that of an open ball of radius `r/4`, from
`OpenPartialHomeomorph.exists_isRegularValue_image_closedBall` and
`OpenPartialHomeomorph.exists_isRegularValue_compl_image_ball`.

## Main results

* `SymplecticGeometry.CoordinateDisc.exists_isRegularValue_disc_subset_ofChart`
* `SymplecticGeometry.CoordinateDisc.exists_isRegularValue_discComplement_subset_ofChart`

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Proposition 5.47 (regular sublevel sets are manifolds with boundary).
-/

public section

open Metric Set TauCeti
open scoped Manifold ContDiff

namespace SymplecticGeometry.CoordinateDisc

variable {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
  [IsManifold (𝓡 2) ∞ M]
  {o : Manifold.Orientation (𝓡 2) M (Fin 2)}
  {e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))}
  {c : EuclideanSpace ℝ (Fin 2)} {r : ℝ}

/-- **A regular sublevel set around a coordinate disc.** Let `e` be a chart of the smooth
maximal atlas of a Hausdorff smooth surface `M`, and `CoordinateDisc.ofChart e hr hc he` the
coordinate disc it gives. There is a smooth function `f : M → ℝ` with regular value `0` such
that the closed disc lies in `{f < 0}`, the sublevel set `{f ≤ 0}` is compact and connected, and
the level set `{f = 0}` is nonempty. -/
theorem exists_isRegularValue_disc_subset_ofChart
    (hea : e ∈ IsManifold.maximalAtlas (𝓡 2) ∞ M) (hr : 0 < r)
    (hc : Metric.ball c r ⊆ e.target)
    (he : ∀ x ∈ e.source,
      o.IsOrientationPreservingAt (Manifold.Orientation.euclideanSpace 2) e x) :
    ∃ f : M → ℝ, ContMDiff (𝓡 2) 𝓘(ℝ) ∞ f ∧ IsRegularValue (𝓡 2) 𝓘(ℝ) f 0 ∧
      (ofChart e hr hc he).disc ⊆ {x | f x < 0} ∧ IsCompact {x | f x ≤ 0} ∧
      IsConnected {x | f x ≤ 0} ∧ {x | f x = 0}.Nonempty := by
  have hρ : 0 < 3 * r / 4 := by positivity
  have hball : closedBall c (3 * r / 4) ⊆ e.target :=
    (closedBall_subset_ball (by linarith)).trans hc
  obtain ⟨f, hf, ha, hle, hlt, heq⟩ := e.exists_isRegularValue_image_closedBall hea hball hρ
  refine ⟨f, hf, ha, ?_, ?_, ?_, ?_⟩
  · rw [disc_ofChart, hlt]
    exact image_mono (closedBall_subset_ball (by linarith))
  · rw [hle]
    exact (isCompact_closedBall c _).image_of_continuousOn (e.continuousOn_symm.mono hball)
  · rw [hle]
    exact (isConnected_closedBall hρ.le).image _ (e.continuousOn_symm.mono hball)
  · rw [heq]
    exact (NormedSpace.sphere_nonempty.2 hρ.le).image _

/-- **A regular sublevel set around the complement of a coordinate disc.** Let `e` be a chart of
the smooth maximal atlas of a connected Hausdorff smooth surface `M`, and
`CoordinateDisc.ofChart e hr hc he` the coordinate disc it gives. There is a smooth function
`g : M → ℝ` with regular value `0` such that the complement `discComplement` of the open disc
lies in `{g < 0}`, the sublevel set `{g ≤ 0}` is connected and the level set `{g = 0}` is
nonempty. -/
theorem exists_isRegularValue_discComplement_subset_ofChart [ConnectedSpace M]
    (hea : e ∈ IsManifold.maximalAtlas (𝓡 2) ∞ M) (hr : 0 < r)
    (hc : Metric.ball c r ⊆ e.target)
    (he : ∀ x ∈ e.source,
      o.IsOrientationPreservingAt (Manifold.Orientation.euclideanSpace 2) e x) :
    ∃ g : M → ℝ, ContMDiff (𝓡 2) 𝓘(ℝ) ∞ g ∧ IsRegularValue (𝓡 2) 𝓘(ℝ) g 0 ∧
      discComplement (fun _ : Unit ↦ ofChart e hr hc he) ⊆ {x | g x < 0} ∧
      IsConnected {x | g x ≤ 0} ∧ {x | g x = 0}.Nonempty := by
  have hρ : 0 < r / 4 := by positivity
  have hball : closedBall c (r / 4) ⊆ e.target := (closedBall_subset_ball (by linarith)).trans hc
  obtain ⟨g, hg, hb, hle, hlt, heq⟩ := e.exists_isRegularValue_compl_image_ball hea hball hρ
  have hne : {x | g x = 0}.Nonempty := by
    rw [heq]
    exact (NormedSpace.sphere_nonempty.2 hρ.le).image _
  refine ⟨g, hg, hb, ?_, ⟨hne.mono fun x hx ↦ le_of_eq hx, ?_⟩, hne⟩
  · rw [discComplement_def, iUnion_const, openDisc_ofChart, hlt]
    exact compl_subset_compl.2 (image_mono (closedBall_subset_ball (by linarith)))
  · rw [hle]
    exact e.isPreconnected_compl_symm_image_ball (by
      rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]; norm_num) hρ.ne' hball

end SymplecticGeometry.CoordinateDisc

end
