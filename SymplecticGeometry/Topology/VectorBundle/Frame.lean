/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.VectorBundle.Basic
public import TauCeti.Analysis.Normed.Module.ContinuousInverse

/-!
# A frame along a map read in a trivialization

Let `E` be a vector bundle over `X` with model fibre `F`, let `f : B → X` be a map and let
`ψ y : F ≃L[R] E (f y)` be a frame of `E` along `f`. Given a linear trivialization `e` of `E`,
`Bundle.Trivialization.frameTransition e ψ y : F ≃L[R] F` is the frame `ψ y` followed by the
fibre equivalence of `e` at `f y`, at the points where `f y` lies in the base set of `e`, and
the identity elsewhere.

When the frame is continuous, as a map `B × F → TotalSpace F E`, and `F` is finite-dimensional,
the transition and its inverse are continuous on the preimage of the base set
(`Bundle.Trivialization.continuousOn_frameTransition`,
`Bundle.Trivialization.continuousOn_frameTransition_symm`). The continuity proof follows Tau
Ceti's proof of `TauCeti.continuousOn_clutchingFunction`, whose clutching function is the
inverse of the normalized determinant of this transition.

## References

* J. W. Milnor and J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §2 (local trivializations and frames of vector bundles).
-/

public section

noncomputable section

open Bundle

namespace Bundle.Trivialization

variable {R : Type*} [NontriviallyNormedField R] {B X : Type*} [TopologicalSpace X]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace R F]
  {E : X → Type*} [∀ x, AddCommMonoid (E x)] [∀ x, Module R (E x)] [∀ x, TopologicalSpace (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E]
  {f : B → X} (e : Trivialization F (π F E)) [e.IsLinear R]

open Classical in
/-- A frame `ψ y : F ≃ E (f y)` of `E` along a map `f`, read in the trivialization `e`: at a
point `y` with `f y` in the base set of `e`, the automorphism `e ∘ ψ y` of the model fibre `F`;
at the other points, the identity. -/
def frameTransition (ψ : ∀ y, F ≃L[R] E (f y)) (y : B) : F ≃L[R] F :=
  if h : f y ∈ e.baseSet then (ψ y).trans (e.continuousLinearEquivAt R (f y) h)
  else ContinuousLinearEquiv.refl R F

variable {e} {ψ : ∀ y, F ≃L[R] E (f y)}

theorem frameTransition_of_mem {y : B} (h : f y ∈ e.baseSet) :
    e.frameTransition ψ y = (ψ y).trans (e.continuousLinearEquivAt R (f y) h) :=
  dite_eq_left h

theorem frameTransition_of_notMem {y : B} (h : f y ∉ e.baseSet) :
    e.frameTransition ψ y = ContinuousLinearEquiv.refl R F :=
  dite_eq_right h

/-- At a point over the base set, the transition sends `v` to the coordinate in `e` of the
vector `ψ y v`. -/
theorem frameTransition_apply_of_mem {y : B} (h : f y ∈ e.baseSet) (v : F) :
    e.frameTransition ψ y v = (e ⟨f y, ψ y v⟩).2 := by
  simp [frameTransition_of_mem h]

variable [CompleteSpace R] [TopologicalSpace B] [FiniteDimensional R F]
  (hψ : Continuous fun q : B × F ↦ TotalSpace.mk' F (f q.1) (ψ q.1 q.2))

include hψ in
/-- The transition of a continuous frame in a trivialization is continuous on the preimage of
the base set. -/
theorem continuousOn_frameTransition (e : Trivialization F (π F E)) [e.IsLinear R] :
    ContinuousOn (fun y ↦ (e.frameTransition ψ y : F →L[R] F)) (f ⁻¹' e.baseSet) := by
  refine continuousOn_clm_apply.2 fun v ↦ ?_
  have hc : ContinuousOn (fun y ↦ (e (TotalSpace.mk' F (f y) (ψ y v))).2) (f ⁻¹' e.baseSet) :=
    continuous_snd.comp_continuousOn (e.continuousOn.comp
      (hψ.comp (Continuous.prodMk_left v)).continuousOn fun y hy ↦ e.mem_source.2 hy)
  exact hc.congr fun y (hy : f y ∈ e.baseSet) ↦ frameTransition_apply_of_mem hy v

include hψ in
/-- The inverse of the transition of a continuous frame in a trivialization is continuous on the
preimage of the base set. -/
theorem continuousOn_frameTransition_symm (e : Trivialization F (π F E)) [e.IsLinear R] :
    ContinuousOn (fun y ↦ ((e.frameTransition ψ y).symm : F →L[R] F)) (f ⁻¹' e.baseSet) :=
  fun y hy ↦ (continuousOn_frameTransition hψ e y hy).continuousLinearEquiv_symm

end Bundle.Trivialization
