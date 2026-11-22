/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Topology.VectorBundle.Frame
public import TauCeti.Topology.VectorBundle.Complex.Clutching

/-!
# Clutching functions as transitions of frames

Tau Ceti's clutching function `TauCeti.clutchingFunction f ψ e` of a frame `ψ` of a complex
vector bundle along a map `f`, in a trivialization `e`, is, over the base set of `e`, the inverse
of the normalized determinant of the transition `Bundle.Trivialization.frameTransition e ψ` of
the frame in `e` (`Bundle.Trivialization.normalizedDet_frameTransition_inv`).

## References

* J. W. Milnor and J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §14 (Chern classes of complex vector bundles, and clutching).
-/

public section

open Bundle TauCeti

namespace Bundle.Trivialization

/-- At a point over the base set, the inverse of the normalized determinant of the transition of a
frame in a trivialization is Tau Ceti's clutching function of the frame. -/
theorem normalizedDet_frameTransition_inv {B X : Type*} [TopologicalSpace X]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {E : X → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)] [∀ x, TopologicalSpace (E x)]
    [TopologicalSpace (TotalSpace F E)] [FiberBundle F E]
    {f : B → X} {e : Trivialization F (π F E)} [e.IsLinear ℂ] {ψ : ∀ y, F ≃L[ℂ] E (f y)} {y : B}
    (h : f y ∈ e.baseSet) :
    (e.frameTransition ψ y).normalizedDet⁻¹ = clutchingFunction f ψ e y := by
  rw [frameTransition_of_mem h, clutchingFunction_of_mem h]

end Bundle.Trivialization
