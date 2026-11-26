/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Topology.VectorBundle.Orientation.Complex.Basic
import SymplecticGeometry.Topology.VectorBundle.Complex.RestrictScalars

/-!
# The canonical orientation of a complex vector bundle in a complex-linear trivialization

Tau Ceti orients a complex vector bundle `V` with model fibre `G` as a real bundle by
`TauCeti.VectorBundleOrientation.complex G V`, the complex orientation of each fibre. Its
`TauCeti.VectorBundleOrientation.mapOrientation_complex` says that a trivialization of the
bundle atlas reads this orientation as the complex orientation of `G`.

Here `TauCeti.VectorBundleOrientation.mapOrientation_complex_of_isLinear` says the same of any
complex-linear trivialization, whether or not it lies in the atlas; it follows from
`Bundle.Trivialization.mapOrientation_complexOrientation`.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §14 (the canonical orientation of a complex vector bundle).
-/

public section

open Bundle Module

namespace TauCeti.VectorBundleOrientation

variable {B : Type*} [TopologicalSpace B]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedSpace ℂ G] [IsScalarTower ℝ ℂ G]
  [FiniteDimensional ℂ G]
  {V : B → Type*} [TopologicalSpace (TotalSpace G V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)] [∀ x, IsScalarTower ℝ ℂ (V x)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle G V] [VectorBundle ℂ G V]

open scoped VectorBundle.ComplexToReal

/-- A complex-linear trivialization reads the canonical orientation of every fibre over its base
set as the canonical orientation of the model fibre. -/
@[simp]
theorem mapOrientation_complex_of_isLinear (e : Trivialization G (π G V)) [e.IsLinear ℂ]
    [e.IsLinear ℝ] {b : B} (hb : b ∈ e.baseSet) :
    e.mapOrientation _ hb (complex G V b) = complexOrientation G := by
  have := VectorBundle.finiteDimensional ℂ G V b
  rw [complex_apply, Trivialization.mapOrientation_complexOrientation _ _ _ rfl, finCongr_refl,
    Orientation.reindex_refl, Equiv.refl_apply]

end TauCeti.VectorBundleOrientation

end
