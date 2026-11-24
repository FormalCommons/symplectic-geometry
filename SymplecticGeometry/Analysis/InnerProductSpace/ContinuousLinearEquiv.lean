/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Subspace
public import Mathlib.Analysis.Normed.Operator.Banach

/-!
# Banach spaces isomorphic to Hilbert spaces

A Banach space need not carry an inner product inducing its norm, yet be continuously linearly
equivalent to a Hilbert space. This file gives two ways to see that it is: by an injective
continuous linear map with closed range into a Hilbert space, or into a space already equivalent to
one, and by being a closed subspace of a space equivalent to a Hilbert space. The open mapping
theorem, through `ContinuousLinearMap.equivRange`, identifies the domain of such a map with its
range, a closed and hence complete subspace of a Hilbert space.

## Main results

* `ContinuousLinearMap.exists_continuousLinearEquiv_innerProductSpace`: the domain of an injective
  continuous linear map with closed range from a Banach space into a Hilbert space is equivalent to
  a Hilbert space.
* `ContinuousLinearMap.exists_continuousLinearEquiv_innerProductSpace_of_continuousLinearEquiv`:
  the same when the target is only equivalent to a Hilbert space.
* `Submodule.exists_continuousLinearEquiv_innerProductSpace_of_isClosed`: a closed subspace of a
  space equivalent to a Hilbert space is equivalent to a Hilbert space.
-/

public section

universe u w

namespace ContinuousLinearMap

variable {𝕜 : Type*} [RCLike 𝕜]
  {X : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
  {H : Type w} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- A Banach space that a continuous linear map embeds injectively, with closed range, into a
Hilbert space is continuously linearly equivalent to a Hilbert space, namely the range. -/
theorem exists_continuousLinearEquiv_innerProductSpace (f : X →L[𝕜] H)
    (hinj : Function.Injective f) (hclo : IsClosed (Set.range f)) :
    ∃ (K : Type w) (_ : NormedAddCommGroup K) (_ : InnerProductSpace 𝕜 K) (_ : CompleteSpace K),
      Nonempty (X ≃L[𝕜] K) :=
  have : CompleteSpace (LinearMap.range (f : X →ₗ[𝕜] H)) := hclo.completeSpace_coe
  ⟨LinearMap.range (f : X →ₗ[𝕜] H), _, _, this, ⟨f.equivRange hinj hclo⟩⟩

/-- A Banach space that a continuous linear map embeds injectively, with closed range, into a
space continuously linearly equivalent to a Hilbert space is itself continuously linearly
equivalent to a Hilbert space. -/
theorem exists_continuousLinearEquiv_innerProductSpace_of_continuousLinearEquiv
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] (f : X →L[𝕜] Y) (e : Y ≃L[𝕜] H)
    (hinj : Function.Injective f) (hclo : IsClosed (Set.range f)) :
    ∃ (K : Type w) (_ : NormedAddCommGroup K) (_ : InnerProductSpace 𝕜 K) (_ : CompleteSpace K),
      Nonempty (X ≃L[𝕜] K) := by
  refine exists_continuousLinearEquiv_innerProductSpace ((e : Y →L[𝕜] H).comp f)
    (e.injective.comp hinj) ?_
  rw [coe_comp, Set.range_comp]
  exact e.toHomeomorph.isClosedMap _ hclo

end ContinuousLinearMap

namespace Submodule

variable {𝕜 : Type*} [RCLike 𝕜] {X : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  {H : Type w} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- A closed subspace of a normed space that is continuously linearly equivalent to a Hilbert
space is itself continuously linearly equivalent to a Hilbert space. -/
theorem exists_continuousLinearEquiv_innerProductSpace_of_isClosed {p : Submodule 𝕜 X}
    (hp : IsClosed (p : Set X)) (e : X ≃L[𝕜] H) :
    ∃ (K : Type w) (_ : NormedAddCommGroup K) (_ : InnerProductSpace 𝕜 K) (_ : CompleteSpace K),
      Nonempty (p ≃L[𝕜] K) :=
  have : CompleteSpace X :=
    (completeSpace_congr (e := e.toLinearEquiv.toEquiv) e.isUniformEmbedding).2 inferInstance
  have : CompleteSpace p := hp.completeSpace_coe
  ContinuousLinearMap.exists_continuousLinearEquiv_innerProductSpace_of_continuousLinearEquiv
    p.subtypeL e Subtype.val_injective (by
      rwa [coe_subtypeL, coe_subtype, Subtype.range_coe])

end Submodule

end
