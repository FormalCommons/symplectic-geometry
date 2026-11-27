/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Immersion
public import TauCeti.Geometry.Manifold.RegularValue
import TauCeti.Geometry.Manifold.MFDeriv.IsInvertible

/-!
# Immersions from an empty manifold, and between manifolds of equal dimension

Every map out of an empty manifold is a `C^n` immersion, for any `n`, since the condition at each
point of the source holds vacuously. The complement in the definition of
`Manifold.IsImmersion` may be taken to be the model space of the target, as in the empty case of
Tau Ceti's `TauCeti.isImmersion_iff_forall_isImmersionAt`.

A `C^n` immersion at a point, `n ≠ 0`, into a manifold whose model has finite dimension equal to
that of the source's model has onto differential there, so the point is regular: an injective
linear map between spaces of the same finite dimension is onto (Tau Ceti's
`TauCeti.isInvertible_mfderiv_iff_injective`). Unlike Tau Ceti's
`TauCeti.isRegularPoint_iff_injective_mfderiv`, only the target's model need be
finite-dimensional.

## Main results

* `Manifold.IsImmersion.of_isEmpty`: a map from an empty manifold is an immersion.
* `Manifold.IsImmersionAt.isRegularPoint_of_finrank_eq`: an immersion at a point between
  manifolds of equal finite dimension is regular there.

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

namespace Manifold.IsImmersionAt

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]
  {n : WithTop ℕ∞} {g : N → M} {z : N}

/-- A `C^n` immersion `g` at `z`, `n ≠ 0`, into a manifold whose model is finite-dimensional, of
the same `finrank` as the source's model, has onto differential at `z`: `z` is a regular point
of `g`. -/
theorem isRegularPoint_of_finrank_eq (h : IsImmersionAt J I n g z) (hn : n ≠ 0)
    (hdim : Module.finrank ℝ E' = Module.finrank ℝ E) : TauCeti.IsRegularPoint J I g z :=
  TauCeti.isRegularPoint_iff.2 ((TauCeti.isInvertible_mfderiv_iff_injective hdim).2
    (h.mfderiv_injective hn)).surjective

end Manifold.IsImmersionAt

end
