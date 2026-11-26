/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.CWModel
public import TauCeti.Geometry.Manifold.Morse.Generic.Basic
public import TauCeti.Geometry.Manifold.Morse.Index

/-!
# Finite CW models of compact manifolds with cells of dimension at most `dim M`

A compact boundaryless smooth manifold `M` modelled on `E` is homotopy equivalent to a finite CW
complex with no cell of dimension greater than `dim E`
(`SymplecticGeometry.exists_finite_cwComplex_homotopyEquiv_of_isManifold`).

## Proof

For nonempty `M`, the space `E` is finite-dimensional and `M` carries a Morse function
(`TauCeti.exists_isMorse`). Its CW model (`TauCeti.IsMorse.exists_finite_cwComplex_homotopyEquiv`)
has one `m`-cell for each critical point of index `m`, and every Morse index is at most `dim E`
(`TauCeti.manifoldMorseIndex_le_finrank`). For empty `M` the empty space, with its discrete CW
structure, is a model. The case split follows Tau Ceti's `TauCeti.FiniteCWType.of_isManifold`.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorem 3.5 (the CW model of a manifold from a Morse function).
-/

public section

open Module Set TauCeti Topology Topology.RelCWComplex
open scoped Manifold ContDiff ContinuousMap

universe u

namespace SymplecticGeometry

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  (M : Type u) (I : ModelWithCorners ℝ E H) [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [CompactSpace M]

include I in
/-- **Finite CW models of compact manifolds with cells of dimension at most `dim M`.** A compact
boundaryless smooth manifold `M` modelled on `E` is homotopy equivalent to a finite CW complex
`W` with no cells of dimension greater than `dim E`. -/
theorem exists_finite_cwComplex_homotopyEquiv_of_isManifold :
    ∃ (W : Type u) (_ : TopologicalSpace W) (_ : T2Space W) (_ : CWComplex (univ : Set W)),
      RelCWComplex.Finite (univ : Set W) ∧ Nonempty (W ≃ₕ M) ∧
      ∀ m, finrank ℝ E < m → IsEmpty (cell (univ : Set W) m) := by
  rcases isEmpty_or_nonempty M with _ | _
  · -- The empty space, whose discrete CW structure has no cells of positive dimension.
    refine ⟨PEmpty.{u + 1}, _, inferInstance, inferInstance, inferInstance,
      ⟨Homeomorph.empty.toHomotopyEquiv⟩, fun m hm ↦ ?_⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hm
    infer_instance
  · have := FiniteDimensional.of_locallyCompact_manifold M I
    obtain ⟨φ, hφ⟩ := exists_isMorse (I := I) (M := M)
    obtain ⟨W, _, _, _, hfin, e, hcell⟩ := hφ.exists_finite_cwComplex_homotopyEquiv
    -- The `m`-cells of `W` are critical points of index `m ≤ dim E`.
    refine ⟨W, _, ‹_›, ‹_›, hfin, e, fun m hm ↦ ⟨fun c ↦ ?_⟩⟩
    obtain ⟨σ⟩ := hcell m
    have h := (σ c).property.2
    have := manifoldMorseIndex_le_finrank (I := I) (f := φ) (x := (σ c : M))
    omega

end SymplecticGeometry

end
