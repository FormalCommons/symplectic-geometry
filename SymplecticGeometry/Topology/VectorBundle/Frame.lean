/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.VectorBundle.Constructions
public import TauCeti.Analysis.Normed.Module.ContinuousInverse
public import TauCeti.Topology.VectorBundle.Contractible
import TauCeti.Topology.VectorBundle.Hom

/-!
# Transition maps of frames of a vector bundle

For two frames `Φ Φ' : ∀ x, W ≃L[R] V x` of a bundle `V` with model fibre `W`, over any semiring
`R`, `SymplecticGeometry.Bundle.frameTransition Φ Φ' x : W ≃L[R] W` is the transition map
`(Φ' x)⁻¹ ∘ Φ x`, in the order of Mathlib's `Bundle.Trivialization.coordChangeL`. It is the
identity from a frame to itself, transition maps compose, and inverting one swaps the two frames.
Pulling two frames back along a map `f` gives, at `y`, their transition map at `f y`
(`SymplecticGeometry.Bundle.frameTransition_pullback`).

Let `E` be a vector bundle over `X` with model fibre `F`, let `f : B → X` be a map and let
`ψ y : F ≃L[R] E (f y)` be a frame of `E` along `f`. Given a linear trivialization `e` of `E`,
`Bundle.Trivialization.frameTransition e ψ y : F ≃L[R] F` is the frame `ψ y` followed by the
fibre equivalence of `e` at `f y`, at the points where `f y` lies in the base set of `e`, and
the identity elsewhere. Over the base set it is the transition map from `ψ` to any frame whose
value at `y` is the inverse of the fibre equivalence of `e`
(`Bundle.Trivialization.frameTransition_eq_frameTransition`).

When the frame is continuous, as a map `B × F → TotalSpace F E`, and `F` is finite-dimensional,
the transition and its inverse are continuous on the preimage of the base set
(`Bundle.Trivialization.continuousOn_frameTransition`,
`Bundle.Trivialization.continuousOn_frameTransition_symm`), for fibres that are groups. Over the
base set the transition is the frame read in `e`, which is continuous there by Tau Ceti's
`TauCeti.continuousOn_continuousLinearMapAt_comp`. More generally, a family of linear maps
`L y : G → E (f y)` from a finite-dimensional space that is continuous into the total space is,
read in `e`, continuous on the preimage of the base set
(`Bundle.Trivialization.continuousOn_continuousLinearMapAt_comp`). It is the case of Tau Ceti's
`TauCeti.continuousOn_continuousLinearMapAt_comp_symmL` whose source is the trivial bundle with
fibre `G`. Composing the inverse of a frame with such a family gives a continuous family of
maps `G → F` (`SymplecticGeometry.Bundle.continuous_frame_symm_comp`); the proof follows that
of Tau Ceti's `TauCeti.continuous_trans_symm_of_continuous_frame_aux`.

## References

* J. W. Milnor and J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §2 (local trivializations and frames of vector bundles).
-/

public section

noncomputable section

open Bundle

namespace SymplecticGeometry.Bundle

/-! ### Transition maps between two frames -/

section FrameTransition

variable {R : Type*} [Semiring R] {M W : Type*} [AddCommMonoid W] [Module R W] [TopologicalSpace W]
  {V : M → Type*} [∀ x, AddCommMonoid (V x)] [∀ x, Module R (V x)] [∀ x, TopologicalSpace (V x)]
  (Φ Φ' Φ'' : ∀ x, W ≃L[R] V x) (x : M)

/-- The transition map `Φ'ₓ⁻¹ ∘ Φₓ` at the point `x` from a frame `Φ` of a bundle with model fibre
`W` to a frame `Φ'`. As a map it is in the order of Mathlib's `Trivialization.coordChangeL`. -/
def frameTransition : W ≃L[R] W :=
  (Φ x).trans (Φ' x).symm

/-- The transition map is the composite of `Φ x` with the inverse of `Φ' x`. -/
theorem frameTransition_def : frameTransition Φ Φ' x = (Φ x).trans (Φ' x).symm :=
  (rfl)

/-- The transition map sends `v` to `Φ'ₓ⁻¹ (Φₓ v)`. -/
@[simp]
theorem frameTransition_apply (v : W) : frameTransition Φ Φ' x v = (Φ' x).symm (Φ x v) :=
  (rfl)

/-- The transition map from a frame to itself is the identity. -/
@[simp]
theorem frameTransition_self : frameTransition Φ Φ x = ContinuousLinearEquiv.refl R W := by
  ext v
  simp

/-- Transition maps compose: going from `Φ` to `Φ'` and then to `Φ''` is going from `Φ` to
`Φ''`. -/
@[simp]
theorem frameTransition_trans :
    (frameTransition Φ Φ' x).trans (frameTransition Φ' Φ'' x) = frameTransition Φ Φ'' x := by
  ext v
  simp

/-- The inverse of the transition map from `Φ` to `Φ'` is the transition map from `Φ'` to `Φ`. -/
@[simp]
theorem frameTransition_symm : (frameTransition Φ Φ' x).symm = frameTransition Φ' Φ x := by
  ext v
  simp [frameTransition_def, ContinuousLinearEquiv.symm_trans_apply]

/-- The transition map between the pull-backs `y ↦ Φ (f y)` and `y ↦ Φ' (f y)` of two frames along
a map `f : N → M` is the transition map between `Φ` and `Φ'` at `f y`. -/
@[simp]
theorem frameTransition_pullback {N : Type*} (f : N → M) (y : N) :
    frameTransition (V := f *ᵖ V) (fun y ↦ Φ (f y)) (fun y ↦ Φ' (f y)) y =
      frameTransition Φ Φ' (f y) :=
  (rfl)

end FrameTransition

end SymplecticGeometry.Bundle

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

/-- Over the base set, the transition of the frame `ψ` in `e` is the transition map from `ψ` to
any frame `Φ'` along `f` whose value at `y` is the inverse of the fibre equivalence of `e` at
`f y`. -/
theorem frameTransition_eq_frameTransition {y : B} (h : f y ∈ e.baseSet)
    {Φ' : ∀ y, F ≃L[R] E (f y)} (hΦ' : Φ' y = (e.continuousLinearEquivAt R (f y) h).symm) :
    e.frameTransition ψ y = SymplecticGeometry.Bundle.frameTransition ψ Φ' y := by
  rw [frameTransition_of_mem h, SymplecticGeometry.Bundle.frameTransition_def, hΦ',
    ContinuousLinearEquiv.symm_symm]

end Bundle.Trivialization

namespace Bundle.Trivialization

variable {R : Type*} [NontriviallyNormedField R] [CompleteSpace R] {B X : Type*}
  [TopologicalSpace B] [TopologicalSpace X] {F : Type*} [NormedAddCommGroup F] [NormedSpace R F]
  [FiniteDimensional R F] {E : X → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module R (E x)]
  [∀ x, TopologicalSpace (E x)] [TopologicalSpace (TotalSpace F E)] [FiberBundle F E]
  {f : B → X} {ψ : ∀ y, F ≃L[R] E (f y)}
  (hψ : Continuous fun q : B × F ↦ TotalSpace.mk' F (f q.1) (ψ q.1 q.2))

include hψ in
/-- The transition of a continuous frame in a trivialization is continuous on the preimage of
the base set. -/
theorem continuousOn_frameTransition (e : Trivialization F (π F E)) [e.IsLinear R] :
    ContinuousOn (fun y ↦ (e.frameTransition ψ y : F →L[R] F)) (f ⁻¹' e.baseSet) := by
  refine (TauCeti.continuousOn_continuousLinearMapAt_comp hψ e).congr
    fun y (hy : f y ∈ e.baseSet) ↦ ?_
  ext v
  simp [frameTransition_apply_of_mem hy, e.coe_linearMapAt_of_mem hy]

include hψ in
/-- The inverse of the transition of a continuous frame in a trivialization is continuous on the
preimage of the base set. -/
theorem continuousOn_frameTransition_symm (e : Trivialization F (π F E)) [e.IsLinear R] :
    ContinuousOn (fun y ↦ ((e.frameTransition ψ y).symm : F →L[R] F)) (f ⁻¹' e.baseSet) :=
  fun y hy ↦ (continuousOn_frameTransition hψ e y hy).continuousLinearEquiv_symm

end Bundle.Trivialization

namespace Bundle.Trivialization

variable {R : Type*} [NontriviallyNormedField R] [CompleteSpace R] {B X : Type*}
  [TopologicalSpace B] [TopologicalSpace X] {F : Type*} [NormedAddCommGroup F] [NormedSpace R F]
  {E : X → Type*} [∀ x, AddCommMonoid (E x)] [∀ x, Module R (E x)] [∀ x, TopologicalSpace (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] {f : B → X}

/-- Let `L y : G → E (f y)` be linear maps from a finite-dimensional space `G`, continuous as a
map `B × G → TotalSpace F E`. Read in a linear trivialization `e`, they form a family of maps
`G → F` that is continuous on the preimage of the base set of `e`. -/
theorem continuousOn_continuousLinearMapAt_comp {G : Type*} [NormedAddCommGroup G]
    [NormedSpace R G] [FiniteDimensional R G] {L : ∀ y, G →L[R] E (f y)}
    (hL : Continuous fun q : B × G ↦ TotalSpace.mk' F (f q.1) (L q.1 q.2))
    (e : Trivialization F (π F E)) [e.IsLinear R] :
    ContinuousOn (fun y ↦ (e.continuousLinearMapAt R (f y)).comp (L y)) (f ⁻¹' e.baseSet) := by
  simpa using TauCeti.continuousOn_continuousLinearMapAt_comp_symmL (E' := Bundle.Trivial B G)
    (g := f) (φ := L) (hL.comp (Bundle.Trivial.homeomorphProd B G).continuous) e
    (Bundle.Trivial.trivialization B G)

end Bundle.Trivialization

namespace SymplecticGeometry.Bundle

variable {R : Type*} [NontriviallyNormedField R] [CompleteSpace R] {B X : Type*}
  [TopologicalSpace B] [TopologicalSpace X] {F : Type*} [NormedAddCommGroup F] [NormedSpace R F]
  [FiniteDimensional R F] {E : X → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module R (E x)]
  [∀ x, TopologicalSpace (E x)] [TopologicalSpace (TotalSpace F E)] [FiberBundle F E]
  [VectorBundle R F E] {f : B → X}

/-- Let `φ y : F ≃ E (f y)` be a continuous frame of a finite-rank vector bundle `E` along `f`,
with the model fibre as its source, and let `L y : G → E (f y)` be linear maps from a
finite-dimensional space `G`, continuous as a map `B × G → TotalSpace F E`. Then the maps
`(φ y)⁻¹ ∘ L y : G → F` depend continuously on `y`. -/
theorem continuous_frame_symm_comp {G : Type*} [NormedAddCommGroup G] [NormedSpace R G]
    [FiniteDimensional R G] {φ : ∀ y, F ≃L[R] E (f y)}
    (hφ : Continuous fun q : B × F ↦ TotalSpace.mk' F (f q.1) (φ q.1 q.2))
    {L : ∀ y, G →L[R] E (f y)}
    (hL : Continuous fun q : B × G ↦ TotalSpace.mk' F (f q.1) (L q.1 q.2)) :
    Continuous fun y ↦ ((φ y).symm : E (f y) →L[R] F).comp (L y) := by
  refine continuous_iff_continuousAt.2 fun y₀ ↦ ?_
  let e := trivializationAt F E (f y₀)
  have hU : f ⁻¹' e.baseSet ∈ nhds y₀ :=
    (TauCeti.continuous_of_continuous_frame hφ).continuousAt.preimage_mem_nhds
      (e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' (f y₀)))
  refine ((Bundle.Trivialization.continuousOn_frameTransition_symm hφ e).clm_comp
    (e.continuousOn_continuousLinearMapAt_comp hL)).continuousAt hU |>.congr_of_eventuallyEq ?_
  filter_upwards [hU] with y (hy : f y ∈ e.baseSet)
  ext v
  simp [Bundle.Trivialization.frameTransition_of_mem hy, e.coe_linearMapAt_of_mem hy,
    e.symm_apply_apply_mk hy]

end SymplecticGeometry.Bundle
