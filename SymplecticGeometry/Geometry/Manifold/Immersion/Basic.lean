/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Immersion

/-!
# Immersions from an empty manifold

Every map out of an empty manifold is a `C^n` immersion, for any `n`, since the condition at each
point of the source holds vacuously. The complement in the definition of
`Manifold.IsImmersion` may be taken to be the model space of the target, as in the empty case of
Tau Ceti's `TauCeti.isImmersion_iff_forall_isImmersionAt`.

## Main results

* `Manifold.IsImmersion.of_isEmpty`: a map from an empty manifold is an immersion.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Springer GTM 218 (2013),
  Chapter 4.
-/

public section

namespace Manifold.IsImmersion

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E H M : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M] [ChartedSpace H M]
  {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [TopologicalSpace H']
  {J : ModelWithCorners 𝕜 E' H'} [TopologicalSpace N] [ChartedSpace H' N]

variable (I J) in
/-- Every map from an empty manifold `M` is a `C^n` immersion, for every `n`. -/
theorem of_isEmpty [IsEmpty M] (n : WithTop ℕ∞) (f : M → N) : IsImmersion I J n f :=
  IsImmersionOfComplement.isImmersion (F := E') isEmptyElim

end Manifold.IsImmersion

end
