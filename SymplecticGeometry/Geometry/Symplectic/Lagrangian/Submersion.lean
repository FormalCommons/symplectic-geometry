/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.Lagrangian.Manifold

/-!
# Isotropic maps through maps with surjective derivatives

This file adds to Tau Ceti's `TauCeti/Geometry/Symplectic/Lagrangian/Submersion.lean`, which
shows that the Lagrangian condition passes to and from the quotient by a surjective submersion
(`TauCeti.SmoothTwoForm.IsNondegenerate.isLagrangianMap_comp_submersion_iff`).

* `TauCeti.SmoothTwoForm.IsNondegenerate.isIsotropicMap_of_comp`: a differentiable map `f` is
  isotropic when `f ∘ q` is, for a surjective differentiable map `q` whose derivatives are all
  surjective. Every tangent vector of the source of `f` is then the image of one under the
  derivative of `q`, so the chain rule moves the vanishing of the form from `f ∘ q` to `f`. No
  smoothness of `q` beyond differentiability and no condition on boundaries is needed.
-/

public section

open Function Manifold
open scoped Manifold ContDiff

namespace TauCeti.SmoothTwoForm.IsNondegenerate

variable {E H M F H' N G H'' P : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H']
  {J : ModelWithCorners ℝ F H'} [TopologicalSpace N] [ChartedSpace H' N]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H'']
  {K : ModelWithCorners ℝ G H''} [TopologicalSpace P] [ChartedSpace H'' P]
  {σ : SmoothTwoForm I M} {hσ : σ.IsNondegenerate} {f : N → M} {q : P → N}

/-- A differentiable map `f` is isotropic when `f ∘ q` is, for a surjective differentiable map `q`
whose derivatives are all surjective: every tangent vector of the source of `f` is then the image
of one under the derivative of `q`. -/
theorem isIsotropicMap_of_comp (hq : Surjective q) (hdq : ∀ x, Surjective (mfderiv K J q x))
    (hf : MDifferentiable J I f) (hq' : MDifferentiable K J q)
    (h : hσ.IsIsotropicMap K (f ∘ q)) : hσ.IsIsotropicMap J f := by
  rw [isIsotropicMap_iff] at h ⊢
  intro y v w
  obtain ⟨x, rfl⟩ := hq y
  obtain ⟨v, rfl⟩ := hdq x v
  obtain ⟨w, rfl⟩ := hdq x w
  have h' := h x v w
  rwa [mfderiv_comp x (hf _) (hq' x)] at h'

end TauCeti.SmoothTwoForm.IsNondegenerate

end
