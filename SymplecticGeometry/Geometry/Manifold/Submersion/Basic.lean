/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Submersion.Basic
import TauCeti.Analysis.Normed.Module.FiniteDimension

/-!
# Submersions from a finite-dimensional source

Mathlib's `Manifold.IsSubmersion` asks for one complement shared by all points. This file shows
that for a source modelled on a finite-dimensional space over a complete field, this is no more
than being a submersion at every point (`Manifold.isSubmersion_iff_forall_isSubmersionAt`): the
pointwise complements are all complements of the target model in the source model, hence
isomorphic.

The proof adapts Tau Ceti's `TauCeti.isImmersion_iff_forall_isImmersionAt` from immersions to
submersions, using Tau Ceti's
`TauCeti.nonempty_continuousLinearEquiv_of_prod_continuousLinearEquiv`.
-/

public section

open scoped ContDiff

namespace Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type*} [TopologicalSpace G]
  {J : ModelWithCorners 𝕜 F G} {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {n : ℕ∞ω} {f : M → N}

/-- For a source modelled on a finite-dimensional space over a complete field, a map is a `C^n`
submersion exactly when it is a `C^n` submersion at every point. -/
theorem isSubmersion_iff_forall_isSubmersionAt :
    IsSubmersion I J n f ↔ ∀ x, IsSubmersionAt I J n f x := by
  refine ⟨fun h x ↦ h.isSubmersionAt x, fun h ↦ ?_⟩
  rcases isEmpty_or_nonempty M with hM | ⟨⟨x₀⟩⟩
  · exact IsSubmersionOfComplement.isSubmersion (F := E)
      (isSubmersionOfComplement_iff.2 fun x ↦ isEmptyElim x)
  refine IsSubmersionOfComplement.isSubmersion (F := (h x₀).complement)
    (isSubmersionOfComplement_iff.2 fun x ↦ ?_)
  obtain ⟨e⟩ := TauCeti.nonempty_continuousLinearEquiv_of_prod_continuousLinearEquiv
    (h x).isSubmersionAtOfComplement_complement.equiv.symm
    (h x₀).isSubmersionAtOfComplement_complement.equiv.symm
  exact (h x).isSubmersionAtOfComplement_complement.trans_F e

end Manifold

end
