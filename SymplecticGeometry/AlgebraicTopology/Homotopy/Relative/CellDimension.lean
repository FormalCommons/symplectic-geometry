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

Let `X` be a Hausdorff space with a relative CW structure over the image of an embedding
`j : Z → X`, with no cells of dimension at most `n`, and let `h : X ≃ₕ M` be a homotopy
equivalence with `h ∘ j = f`. Then `f : Z → M` is `n`-connected
(`ContinuousMap.IsNConnected.of_relCWComplex_homotopyEquiv`).

This is the form in which a relative CW model gives connectivity, for instance the models of
Tau Ceti's `TauCeti.IsMorse.exists_relCWComplex_homotopyEquiv_sublevel`. Here the base is the
`n`-skeleton (`TauCeti.skeletonLT_eq_base_of_isEmpty_cell`), so its inclusion is `n`-connected
(`TauCeti.isNConnected_inclusion_skeletonLT`, Hatcher, Corollary 4.12), and the square with the
weak homotopy equivalences `Z ≃ range j` and `h` carries this to `f`
(`ContinuousMap.IsWeakHomotopyEquivalence.isNConnected_iff_of_comp_eq`).

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.1, Corollary 4.12.
-/

public section

open Set Topology Topology.RelCWComplex

namespace ContinuousMap.IsNConnected

variable {Z X M : Type*} [TopologicalSpace Z] [TopologicalSpace X] [TopologicalSpace M]

/-- Let `X` be a Hausdorff relative CW complex over the image of an embedding `j : Z → X`,
with no cells of dimension at most `n`. If `h : X ≃ₕ M` is a homotopy equivalence with
`h (j z) = f z` for all `z`, then `f` is `n`-connected. -/
theorem of_relCWComplex_homotopyEquiv [T2Space X] {j : C(Z, X)}
    [RelCWComplex (univ : Set X) (range j)] {f : C(Z, M)} {n : ℕ} (h : X ≃ₕ M)
    (hj : IsEmbedding j) (hh : ∀ z, h (j z) = f z)
    (hcell : ∀ m < n + 1, IsEmpty (RelCWComplex.cell (univ : Set X) m)) :
    f.IsNConnected n := by
  have hA : (skeletonLT (univ : Set X) (n + 1) : Set X) = range j := by
    exact_mod_cast TauCeti.skeletonLT_eq_base_of_isEmpty_cell _ (n + 1) hcell
  -- The square `h ∘ (range j ↪ univ) = f ∘ (range j ≃ Z)`, with `h` read on `univ`.
  set e := hj.toHomeomorph
  set g := (Homeomorph.Set.univ X).toHomotopyEquiv.trans h
  have hsq : g.toFun.comp (ContinuousMap.inclusion (subset_univ _)) =
      f.comp (e.symm : C(range j, Z)) := by
    ext x
    obtain ⟨z, rfl⟩ := e.surjective x
    simpa [e, g] using hh z
  rw [e.symm.toHomotopyEquiv.isWeakHomotopyEquivalence.isNConnected_iff_of_comp_eq
    g.isWeakHomotopyEquivalence hsq]
  exact TauCeti.isNConnected_inclusion_skeletonLT hA (subset_univ _)

end ContinuousMap.IsNConnected

end
