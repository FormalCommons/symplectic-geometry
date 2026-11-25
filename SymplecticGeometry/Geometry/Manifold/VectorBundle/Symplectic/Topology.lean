/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Symplectic.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Topology

/-!
# Two-forms in the frame topology

Tau Ceti's frame topology on the sections of a vector bundle (`ContMDiffSection.frameTopology`)
is a topology on the `C^n` two-forms of a bundle `V`, since these are the sections of the bundle
of alternating maps on `V`. This file proves that nondegeneracy over a compact subset of the base
is an open condition in it.

## Main results

* `Bundle.ContMDiffTwoForm.isOpen_setOf_forall_mem_nondegenerate`: for a covering frame system,
  a locally compact model of the base, a bundle of finite rank and a compact `K ⊆ M`, the
  two-forms that are nondegenerate on every fibre over `K` form an open set.

## Implementation notes

The proof adapts Tau Ceti's
`IsCompact.isOpen_setOf_forall_mem_forall_bilinear_apply_self_pos`
(`TauCeti/Topology/VectorBundle/Bilinear.lean`), with nondegeneracy in place of positivity: the
nondegenerate alternating maps are open in the total space of the bundle of alternating maps
(`isOpen_setOf_nondegenerate`), evaluation is jointly continuous in the section and the point
(`ContMDiffSection.continuous_totalSpace_eval`), and the tube lemma over `K` concludes.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.6
  (symplectic vector bundles).
-/

public section

open Bundle TopologicalSpace
open scoped Manifold

namespace SymplecticGeometry

namespace Bundle.ContMDiffTwoForm

variable {EB HB M : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [TopologicalSpace HB] {I : ModelWithCorners ℝ EB HB}
  [TopologicalSpace M] [ChartedSpace HB M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V] {n : ℕ∞}
  [IsManifold I n M] [ContMDiffVectorBundle n F V I]
  {ι : Type*}
  (e : ι → Trivialization (F [⋀^Fin 2]→L[ℝ] ℝ)
    (π (F [⋀^Fin 2]→L[ℝ] ℝ) (fun x ↦ V x [⋀^Fin 2]→L[ℝ] Trivial M ℝ x)))
  [∀ i, MemTrivializationAtlas (e i)]
  (U : ι → Opens M) (hU : ∀ i, (U i : Set M) ⊆ (e i).baseSet)

/-- For a covering frame system, a locally compact model of the base and a bundle of finite
rank, the two-forms whose bilinear form is nondegenerate on the fibre over every point of a
compact set `K` form an open set in the frame topology. -/
theorem isOpen_setOf_forall_mem_nondegenerate [LocallyCompactSpace EB] [FiniteDimensional ℝ F]
    (hcover : ∀ x, ∃ i, x ∈ U i) {K : Set M} (hK : IsCompact K) :
    let _ := ContMDiffSection.frameTopology (I := I) (n := n) e U hU
    IsOpen {ω : ContMDiffTwoForm I n F V | ∀ x ∈ K, (ω.bilinFormAt x).Nondegenerate} := by
  let _ := ContMDiffSection.frameTopology (I := I) (n := n) e U hU
  have hS := (isOpen_setOf_nondegenerate (F := F) (V := V)).preimage
    (ContMDiffSection.continuous_totalSpace_eval (I := I) (n := n) e U hU hcover)
  simp_rw [isOpen_iff_mem_nhds, bilinFormAt_def]
  exact fun ω hω ↦ hK.eventually_forall_of_forall_eventually fun x hx ↦ hS.mem_nhds (hω x hx)

end Bundle.ContMDiffTwoForm

end SymplecticGeometry

end
