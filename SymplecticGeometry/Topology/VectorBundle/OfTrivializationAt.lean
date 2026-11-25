/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.VectorBundle.Basic
public import TauCeti.Topology.FiberBundle.Trivialization

/-!
# Choosing the preferred trivializations of a bundle

A fibre bundle structure on `E` fixes a trivialization `trivializationAt F E x` at each point
`x` of the base. Given any family `e x` of trivializations of `E` with `x ∈ (e x).baseSet`, the
same total space, with the same topology, is a fibre bundle whose preferred trivialization at
`x` is `e x` and whose atlas is the range of `e`. If the model fibre is finite-dimensional over
a complete field and every `e x` is linear, this structure is a vector bundle: the coordinate
changes between the `e x` are continuous in the operator topology, since they are jointly
continuous (Tau Ceti's `Bundle.Trivialization.continuousOn_coordChange`) and a family of linear
maps on a finite-dimensional space is continuous as soon as its values at each vector are
(`continuousOn_clm_apply`).

Constructions on vector bundles that are built from the preferred trivializations, such as
finite-rank cores, then see the trivializations `e x`.

## Main definitions and results

* `FiberBundle.ofTrivializationAt e he`: the fibre bundle structure with preferred
  trivializations `e x`.
* `Bundle.Trivialization.continuousOn_coordChangeL`: the coordinate change between two linear
  trivializations with finite-dimensional model fibre is continuous in the operator topology.
* `VectorBundle.ofTrivializationAt`: it is a vector bundle when the `e x` are linear and the model
  fibre is finite-dimensional.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton University Press, 1974, §2.
-/

public section

open Bundle Set

namespace FiberBundle

variable {B F : Type*} [TopologicalSpace B] [TopologicalSpace F] {E : B → Type*}
  [TopologicalSpace (TotalSpace F E)] [∀ x, TopologicalSpace (E x)] [FiberBundle F E]
  (e : B → Trivialization F (π F E)) (he : ∀ x, x ∈ (e x).baseSet)

/-- The fibre bundle structure on `E`, with the topologies of the given one, whose preferred
trivialization at `x` is `e x` and whose atlas is the range of `e`. This is a definition, not an
instance, since `e` is data. -/
@[implicit_reducible]
def ofTrivializationAt : FiberBundle F E where
  totalSpaceMk_isInducing' := totalSpaceMk_isInducing F E
  trivializationAtlas' := range e
  trivializationAt' := e
  mem_baseSet_trivializationAt' := he
  trivialization_mem_atlas' := mem_range_self

/-- The preferred trivialization at `x` of `FiberBundle.ofTrivializationAt e he` is `e x`. -/
@[simp]
theorem trivializationAt_ofTrivializationAt (x : B) :
    letI := ofTrivializationAt e he
    trivializationAt F E x = e x :=
  (rfl)

/-- The atlas of `FiberBundle.ofTrivializationAt e he` is the range of `e`. -/
@[simp]
theorem trivializationAtlas_ofTrivializationAt :
    letI := ofTrivializationAt e he
    trivializationAtlas F E = range e :=
  (rfl)

end FiberBundle

/-- The coordinate change between two linear trivializations of a bundle whose model fibre is
finite-dimensional over a complete field is continuous, in the operator topology, on the overlap
of their base sets. -/
theorem Bundle.Trivialization.continuousOn_coordChangeL {𝕜 B F : Type*}
    [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [TopologicalSpace B] [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F] {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
    [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)] (e e' : Trivialization F (π F E))
    [e.IsLinear 𝕜] [e'.IsLinear 𝕜] :
    ContinuousOn (fun b ↦ (e.coordChangeL 𝕜 e' b : F →L[𝕜] F)) (e.baseSet ∩ e'.baseSet) := by
  refine continuousOn_clm_apply.2 fun v ↦ ((e.continuousOn_coordChange e').comp
    (continuous_id.prodMk continuous_const).continuousOn fun b hb ↦ ⟨hb, mem_univ v⟩).congr
    fun b hb ↦ ?_
  simp [coordChangeL_apply' _ _ hb, coordChange]

/-- If every trivialization `e x` is linear and the model fibre is finite-dimensional over a
complete field, then `FiberBundle.ofTrivializationAt e he` is a vector bundle. -/
theorem VectorBundle.ofTrivializationAt {𝕜 B F : Type*} [NontriviallyNormedField 𝕜]
    [CompleteSpace 𝕜] [TopologicalSpace B] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [FiniteDimensional 𝕜 F] {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
    [∀ x, TopologicalSpace (E x)] [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)]
    [FiberBundle F E] (e : B → Trivialization F (π F E)) (he : ∀ x, x ∈ (e x).baseSet)
    [∀ x, (e x).IsLinear 𝕜] :
    letI := FiberBundle.ofTrivializationAt e he
    VectorBundle 𝕜 F E := by
  let := FiberBundle.ofTrivializationAt e he
  refine ⟨?_, ?_⟩
  · rintro _ ⟨⟨x, rfl⟩⟩
    infer_instance
  · rintro _ _ ⟨⟨x, rfl⟩⟩ ⟨⟨y, rfl⟩⟩
    exact (e x).continuousOn_coordChangeL (e y)

end
