/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.CWComplex.Classical.Basic
public import Mathlib.Topology.Homotopy.Equiv
public import TauCeti.Topology.Homotopy.HomotopyGroup.ConnectedMap.Basic
import TauCeti.AlgebraicTopology.Homotopy.Relative.Skeleton
import TauCeti.Topology.CWComplex.Classical.Skeleton.Basic
import TauCeti.Topology.Homotopy.HomotopyGroup.WeakHomotopyEquivalence

/-!
# Connectivity of a map from a relative CW model

Let `C` be a relative CW complex with base `D` in a Hausdorff space, with no cells of dimension
at most `n`, and let `j : B → Y` be weakly equivalent to the inclusion `D ↪ C`, through weak
homotopy equivalences `f : D → B` and `g : C → Y` with `g ∘ (D ↪ C) = j ∘ f`. Then `j` is
`n`-connected (`ContinuousMap.IsNConnected.of_isEmpty_cell_of_comp_eq`). The base is the
`n`-skeleton (`TauCeti.skeletonLT_eq_base_of_isEmpty_cell`), so its inclusion is `n`-connected
(`TauCeti.isNConnected_inclusion_skeletonLT`, Hatcher, Corollary 4.12), and the square carries
this to `j` (`ContinuousMap.IsWeakHomotopyEquivalence.isNConnected_iff_of_comp_eq`).

This puts together, as one `ContinuousMap.IsNConnected` statement, what Tau Ceti's file
`TauCeti/AlgebraicTopology/Homotopy/Relative/CellDimension.lean` proves degree by degree in
`TauCeti.exists_joined_of_isEmpty_cell_of_comp_eq`,
`TauCeti.surjective_homotopyGroupMap_of_isEmpty_cell_of_comp_eq` and
`TauCeti.injective_homotopyGroupMap_of_isEmpty_cell_of_comp_eq`, and its proof follows theirs.

The special case for relative CW models: if `X` is a Hausdorff space with a relative CW
structure over the image of an embedding `j : Z → X`, with no cells of dimension at most `n`,
and `h : X ≃ₕ M` is a homotopy equivalence with `h ∘ j = f`, then `f : Z → M` is `n`-connected
(`ContinuousMap.IsNConnected.of_relCWComplex_homotopyEquiv`). The models of Tau Ceti's
`TauCeti.IsMorse.exists_relCWComplex_homotopyEquiv_sublevel` have this form.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.1, Corollary 4.12.
-/

public section

open Set Topology Topology.RelCWComplex

namespace ContinuousMap.IsNConnected

section Transport

variable {X : Type*} [TopologicalSpace X] [T2Space X] {C D : Set X} [RelCWComplex C D]
  {Y B : Type*} [TopologicalSpace Y] [TopologicalSpace B] {f : C(D, B)} {g : C(C, Y)}
  {j : C(B, Y)} {n : ℕ}

/-- Let `C` be a relative CW complex with base `D` in a Hausdorff space, with no cells of
dimension at most `n`. If `j : B → Y` is weakly equivalent to the inclusion `D ↪ C`, through weak
homotopy equivalences `f : D → B` and `g : C → Y` with `g ∘ (D ↪ C) = j ∘ f`, then `j` is
`n`-connected. -/
theorem of_isEmpty_cell_of_comp_eq (hcell : ∀ m < n + 1, IsEmpty (cell C m))
    (hf : f.IsWeakHomotopyEquivalence) (hg : g.IsWeakHomotopyEquivalence)
    (hgf : g.comp (ContinuousMap.inclusion base_subset_complex) = j.comp f) :
    j.IsNConnected n := by
  have hD : (skeletonLT C (n + 1) : Set X) = D := by
    exact_mod_cast TauCeti.skeletonLT_eq_base_of_isEmpty_cell C (n + 1) hcell
  rw [hf.isNConnected_iff_of_comp_eq hg hgf]
  exact TauCeti.isNConnected_inclusion_skeletonLT hD base_subset_complex

end Transport

variable {Z X M : Type*} [TopologicalSpace Z] [TopologicalSpace X] [TopologicalSpace M]

/-- Let `X` be a Hausdorff relative CW complex over the image of an embedding `j : Z → X`,
with no cells of dimension at most `n`. If `h : X ≃ₕ M` is a homotopy equivalence with
`h (j z) = f z` for all `z`, then `f` is `n`-connected. -/
theorem of_relCWComplex_homotopyEquiv [T2Space X] {j : C(Z, X)}
    [RelCWComplex (univ : Set X) (range j)] {f : C(Z, M)} {n : ℕ} (h : X ≃ₕ M)
    (hj : IsEmbedding j) (hh : ∀ z, h (j z) = f z)
    (hcell : ∀ m < n + 1, IsEmpty (RelCWComplex.cell (univ : Set X) m)) :
    f.IsNConnected n := by
  -- The square `h ∘ (range j ↪ univ) = f ∘ (range j ≃ Z)`, with `h` read on `univ`.
  set e := hj.toHomeomorph
  set g := (Homeomorph.Set.univ X).toHomotopyEquiv.trans h
  have hsq : g.toFun.comp (ContinuousMap.inclusion (subset_univ _)) =
      f.comp (e.symm : C(range j, Z)) := by
    ext x
    obtain ⟨z, rfl⟩ := e.surjective x
    simpa [e, g] using hh z
  exact of_isEmpty_cell_of_comp_eq hcell e.symm.toHomotopyEquiv.isWeakHomotopyEquivalence
    g.isWeakHomotopyEquivalence hsq

end ContinuousMap.IsNConnected

end
