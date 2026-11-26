/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Topology.FiberBundle.MapFiber
public import Mathlib.Topology.VectorBundle.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import SymplecticGeometry.Topology.FiberBundle.Basic
import SymplecticGeometry.Topology.VectorBundle.Basic

/-!
# Choosing the preferred trivializations of a vector bundle

A fibre bundle structure on `E` fixes a trivialization `trivializationAt F E x` at each point
`x` of the base. Given any family `e x` of trivializations of `E` with `x ∈ (e x).baseSet`, Tau
Ceti's `TauCeti.MapFiber.Atlas.fiberBundleOfHomeomorph`, applied to the atlas `⟨e, he⟩` and the
identity homeomorphism of the total space, is a fibre bundle structure on the same total space,
with the same topology, whose preferred trivialization at `x` is `e x` transported along the
identity, that is `e x` itself
(`TauCeti.MapFiber.Atlas.trivializationAt_fiberBundleOfHomeomorph_refl`). If the
model fibre is finite-dimensional over a complete field and every `e x` is linear, this structure
is a vector bundle: its coordinate changes are continuous in the operator topology by
`Bundle.Trivialization.continuousOn_coordChangeL`.

Constructions on vector bundles that are built from the preferred trivializations, such as
finite-rank cores, then see the trivializations `e x`.

## Main results

* `VectorBundle.ofTrivializationAt`: the fibre bundle structure with preferred trivializations
  `e x` is a vector bundle when the `e x` are linear and the model fibre is finite-dimensional.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton University Press, 1974, §2.
-/

public section

open Bundle

/-- If every trivialization `e x` is linear and the model fibre is finite-dimensional over a
complete field, then the fibre bundle structure on `E` whose preferred trivialization at `x` is
`e x` (Tau Ceti's `TauCeti.MapFiber.Atlas.fiberBundleOfHomeomorph` for the atlas `⟨e, he⟩` and the
identity of the total space) is a vector bundle. -/
theorem VectorBundle.ofTrivializationAt {𝕜 B F : Type*} [NontriviallyNormedField 𝕜]
    [CompleteSpace 𝕜] [TopologicalSpace B] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [FiniteDimensional 𝕜 F] {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
    [∀ x, TopologicalSpace (E x)] [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)]
    [FiberBundle F E] (e : B → Trivialization F (π F E)) (he : ∀ x, x ∈ (e x).baseSet)
    [∀ x, (e x).IsLinear 𝕜] :
    letI := (⟨e, he⟩ : TauCeti.MapFiber.Atlas F (π F E)).fiberBundleOfHomeomorph
      (Homeomorph.refl _) (fun _ ↦ rfl) (FiberBundle.totalSpaceMk_isInducing F E)
    VectorBundle 𝕜 F E := by
  let A : TauCeti.MapFiber.Atlas F (π F E) := ⟨e, he⟩
  let := A.fiberBundleOfHomeomorph (Homeomorph.refl _) (fun _ ↦ rfl)
    (FiberBundle.totalSpaceMk_isInducing F E)
  have mem {e'} (h : MemTrivializationAtlas e') : ∃ x, e x = e' := by
    exact (A.mem_trivializationAtlas_fiberBundleOfHomeomorph_refl_iff _ e').1 h.out
  refine ⟨fun e' h ↦ ?_, fun e' e'' h h' ↦ ?_⟩
  · obtain ⟨x, rfl⟩ := mem h
    infer_instance
  · obtain ⟨x, rfl⟩ := mem h
    obtain ⟨y, rfl⟩ := mem h'
    exact (e x).continuousOn_coordChangeL (e y)

end
