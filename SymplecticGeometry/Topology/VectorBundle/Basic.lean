/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import TauCeti.Topology.FiberBundle.Trivialization
public import TauCeti.Topology.VectorBundle.Trivialization

/-!
# Linear trivializations and scaling in the fibre

Facts about the linear trivializations of a vector bundle, complementing Mathlib's
`Mathlib/Topology/VectorBundle/Basic.lean` and Tau Ceti's
`TauCeti/Topology/VectorBundle/Trivialization.lean`.

## Main results

* `Bundle.Trivialization.symm_smul_snd`: for a linear trivialization `e` and a point `y` over its
  base set, `e.symm y.proj (c • (e y).2) = c • y.snd`.
* `Bundle.Trivialization.isLinear_restrOpen`: the restriction of a linear trivialization to an
  open set (Mathlib's `Bundle.Trivialization.restrOpen`) is linear.
* `Bundle.Trivialization.continuousOn_coordChangeL`: the coordinate change between two linear
  trivializations with finite-dimensional model fibre over a complete field is continuous in the
  operator topology.
* `ContinuousAt.eventually_mem_baseSet_trivializationAt`: a map into the base of a fibre bundle,
  continuous at `x₀`, takes the points near `x₀` into the base set of the preferred trivialization
  at its value at `x₀`; Tau Ceti's `Bundle.TotalSpace.eventually_proj_mem_baseSet_trivializationAt`
  is the case of the projection.
-/

public section

namespace Bundle.Trivialization

section Semiring

variable {R B F : Type*} {E : B → Type*} [Semiring R] [TopologicalSpace F] [TopologicalSpace B]
  [AddCommMonoid F] [Module R F] [∀ b, AddCommMonoid (E b)] [∀ b, Module R (E b)]
  [TopologicalSpace (TotalSpace F E)]

/-- For a linear trivialization `e` and a point `y` over its base set, the point of the fibre of
`y` with fibre coordinate `c` times that of `y` is `c • y`. -/
theorem symm_smul_snd (e : Trivialization F (π F E)) [e.IsLinear R] {y : TotalSpace F E}
    (hy : y.proj ∈ e.baseSet) (c : R) : e.symm y.proj (c • (e y).2) = c • y.snd := by
  rw [e.symm_apply_smul hy, e.symm_proj_apply y hy]

/-- The restriction of an `R`-linear trivialization to an open set is `R`-linear. -/
instance isLinear_restrOpen (e : Trivialization F (π F E)) [e.IsLinear R] (s : Set B)
    (hs : IsOpen s) : (e.restrOpen s hs).IsLinear R where
  linear _ hb := e.linear R hb.1

end Semiring

/-- The coordinate change between two linear trivializations of a bundle whose model fibre is
finite-dimensional over a complete field is continuous, in the operator topology, on the overlap
of their base sets. -/
theorem continuousOn_coordChangeL {𝕜 B F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    [TopologicalSpace B] [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    {E : B → Type*} [TopologicalSpace (TotalSpace F E)] [∀ x, AddCommMonoid (E x)]
    [∀ x, Module 𝕜 (E x)]
    (e e' : Trivialization F (π F E)) [e.IsLinear 𝕜] [e'.IsLinear 𝕜] :
    ContinuousOn (fun b ↦ (e.coordChangeL 𝕜 e' b : F →L[𝕜] F)) (e.baseSet ∩ e'.baseSet) := by
  refine continuousOn_clm_apply.2 fun v ↦ ((e.continuousOn_coordChange e').comp
    (continuous_id.prodMk continuous_const).continuousOn fun b hb ↦ ⟨hb, Set.mem_univ v⟩).congr
    fun b hb ↦ ?_
  simp [coordChangeL_apply' _ _ hb, coordChange]

end Bundle.Trivialization

open Bundle Filter Topology in
/-- A map `f` into the base of a fibre bundle that is continuous at `x₀` takes every point near
`x₀` into the base set of the preferred trivialization at `f x₀`. -/
theorem ContinuousAt.eventually_mem_baseSet_trivializationAt {X B : Type*} (F : Type*)
    (E : B → Type*) [TopologicalSpace X] [TopologicalSpace B] [TopologicalSpace F]
    [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
    {f : X → B} {x₀ : X} (hf : ContinuousAt f x₀) :
    ∀ᶠ x in 𝓝 x₀, f x ∈ (trivializationAt F E (f x₀)).baseSet :=
  hf.eventually_mem ((trivializationAt F E (f x₀)).open_baseSet.mem_nhds
    (FiberBundle.mem_baseSet_trivializationAt' (f x₀)))

end
