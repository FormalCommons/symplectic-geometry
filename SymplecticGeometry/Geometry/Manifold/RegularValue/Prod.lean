/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.RegularValue
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-!
# Regular points of a product of maps

The product `Prod.map f g` of two maps is regular at `(x, y)` when `f` is regular at `x` and `g`
is regular at `y`, since its differential is the product of theirs.

## Main results

* `TauCeti.IsRegularPoint.prodMap`: a product of regular points is a regular point.
-/

public section

open scoped Manifold

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners 𝕜 F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  {G' : Type*} [TopologicalSpace G'] {J' : ModelWithCorners 𝕜 F' G'}
  {N' : Type*} [TopologicalSpace N'] [ChartedSpace G' N']

/-- If `f` is differentiable and regular at `x` and `g` is differentiable and regular at `y`,
then `Prod.map f g` is regular at `(x, y)`. -/
theorem IsRegularPoint.prodMap {f : M → N} {g : M' → N'} {x : M} {y : M'}
    (hf : IsRegularPoint I J f x) (hg : IsRegularPoint I' J' g y)
    (hfd : MDifferentiableAt I J f x) (hgd : MDifferentiableAt I' J' g y) :
    IsRegularPoint (I.prod I') (J.prod J') (Prod.map f g) (x, y) := by
  rw [isRegularPoint_iff, mfderiv_prodMap (p := (x, y)) hfd hgd]
  rintro ⟨v, w⟩
  obtain ⟨v', rfl⟩ := isRegularPoint_iff.1 hf v
  obtain ⟨w', rfl⟩ := isRegularPoint_iff.1 hg w
  exact ⟨(v', w'), rfl⟩

end TauCeti

end
