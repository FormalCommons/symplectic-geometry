/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.DiscComplement.Basic
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Symplectic.Basic
import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.DiscComplement.RegularSublevel
import SymplecticGeometry.Geometry.Manifold.VectorBundle.Symplectic.Sublevel

/-!
# Symplectic frames over a coordinate disc and over its complement

Let `ω` be a nondegenerate smooth two-form on a smooth real vector bundle `V` of rank `2 |κ|`
over a Hausdorff smooth surface `M`, and let `φ = CoordinateDisc.ofChart e hr hc he`
be the coordinate disc given by a chart `e` of the smooth maximal atlas. This file gives smooth
symplectic frames of `ω` for `stdForm κ` over an open neighbourhood of the closed disc of `φ`,
and, when `M` is closed and connected, over an open neighbourhood of the complement
`discComplement` of its open disc. These are the two frames whose transition loop the clutching
description of the first Chern number compares.

## Main results

* `ContMDiffTwoForm.IsNondegenerate.exists_isSymplecticFrameOn_disc_ofChart`: a frame over an
  open neighbourhood of the closed disc.
* `ContMDiffTwoForm.IsNondegenerate.exists_isSymplecticFrameOn_discComplement_ofChart`: a frame
  over an open neighbourhood of the complement of the open disc.

## Implementation notes

Each set lies in the strict sublevel set `{f < 0}` of a smooth function with regular value `0`
whose sublevel set `{f ≤ 0}` is connected and whose level set `{f = 0}` is nonempty
(`CoordinateDisc.exists_isRegularValue_disc_subset_ofChart`,
`CoordinateDisc.exists_isRegularValue_discComplement_subset_ofChart`). The sublevel set is
compact: around the disc, the first of these lemmas says so, on any surface; around the
complement, it is closed in the compact surface `M`. Then
`ContMDiffTwoForm.IsNondegenerate.exists_isSymplecticFrameOn_setOfPred_lt` gives a frame over
`{f < 0}`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Theorem 2.1.3 and Proposition 2.6.7
-/

public section

open _root_.Bundle Module Set TauCeti
open scoped Manifold

namespace SymplecticGeometry.Bundle.ContMDiffTwoForm

open StdSpace

variable {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
  [IsManifold (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) M] [T2Space M]
  {o : Manifold.Orientation (𝓡 2) M (Fin 2)}
  {e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))} {c : EuclideanSpace ℝ (Fin 2)} {r : ℝ}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ((⊤ : ℕ∞) : WithTop ℕ∞) F V (𝓡 2)]
  {ω : ContMDiffTwoForm (𝓡 2) ⊤ F V} {κ : Type*} [Fintype κ]

/-- **Symplectic frames near a coordinate disc.** Let `ω` be a nondegenerate smooth two-form on a
smooth real vector bundle `V` of rank `2 |κ|` over a Hausdorff smooth surface `M`, and
let `CoordinateDisc.ofChart e hr hc he` be the coordinate disc of a chart `e` of the smooth
maximal atlas. Then `ω` has a smooth symplectic frame for `stdForm κ` over an open set that
contains the closed disc. -/
theorem IsNondegenerate.exists_isSymplecticFrameOn_disc_ofChart
    (hω : ω.IsNondegenerate)
    (hea : e ∈ IsManifold.maximalAtlas (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) M) (hr : 0 < r)
    (hc : Metric.ball c r ⊆ e.target)
    (he : ∀ x ∈ e.source,
      o.IsOrientationPreservingAt (Manifold.Orientation.euclideanSpace 2) e x)
    (hκ : finrank ℝ F = 2 * Fintype.card κ) :
    ∃ U : Set M, IsOpen U ∧ (CoordinateDisc.ofChart e hr hc he).disc ⊆ U ∧
      ∃ Φ : ∀ x, StdSpace κ ≃L[ℝ] V x, ω.IsSymplecticFrameOn (stdForm κ) U Φ := by
  obtain ⟨f, hf, hreg, hD, hcpt, hconn, hne⟩ :=
    CoordinateDisc.exists_isRegularValue_disc_subset_ofChart hea hr hc he
  exact ⟨_, isOpen_lt hf.continuous continuous_const, hD,
    hω.exists_isSymplecticFrameOn_setOfPred_lt finrank_euclideanSpace_fin hf hreg hcpt hconn hne hκ⟩

/-- **Symplectic frames near the complement of a coordinate disc.** Let `ω` be a nondegenerate
smooth two-form on a smooth real vector bundle `V` of rank `2 |κ|` over a closed connected smooth
surface `M`, and let `CoordinateDisc.ofChart e hr hc he` be the coordinate disc of a chart `e`
of the smooth maximal atlas. Then `ω` has a smooth symplectic frame for `stdForm κ` over an open
set that contains the complement `discComplement` of the open disc. -/
theorem IsNondegenerate.exists_isSymplecticFrameOn_discComplement_ofChart [CompactSpace M]
    [ConnectedSpace M]
    (hω : ω.IsNondegenerate)
    (hea : e ∈ IsManifold.maximalAtlas (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) M) (hr : 0 < r)
    (hc : Metric.ball c r ⊆ e.target)
    (he : ∀ x ∈ e.source,
      o.IsOrientationPreservingAt (Manifold.Orientation.euclideanSpace 2) e x)
    (hκ : finrank ℝ F = 2 * Fintype.card κ) :
    ∃ U : Set M, IsOpen U ∧
      discComplement (fun _ : Unit ↦ CoordinateDisc.ofChart e hr hc he) ⊆ U ∧
      ∃ Φ : ∀ x, StdSpace κ ≃L[ℝ] V x, ω.IsSymplecticFrameOn (stdForm κ) U Φ := by
  obtain ⟨g, hg, hreg, hD, hconn, hne⟩ :=
    CoordinateDisc.exists_isRegularValue_discComplement_subset_ofChart hea hr hc he
  exact ⟨_, isOpen_lt hg.continuous continuous_const, hD,
    hω.exists_isSymplecticFrameOn_setOfPred_lt finrank_euclideanSpace_fin hg hreg
      (isClosed_le hg.continuous continuous_const).isCompact hconn hne hκ⟩

end SymplecticGeometry.Bundle.ContMDiffTwoForm

end
