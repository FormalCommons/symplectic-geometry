/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.Countable
public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.FiniteCWType
public import TauCeti.Geometry.Manifold.Morse.CWModel
public import TauCeti.Geometry.Manifold.SmoothSingular.Period

/-!
# Periods of closed forms on compact manifolds

This file adds to Tau Ceti's `TauCeti.closedFormHomologyPeriod`, the periods
`H_p(M; ℤ) →+ ℝ` of a closed smooth real `p`-form `φ`, a statement about their size.

## Main results

* `TauCeti.countable_range_closedFormHomologyPeriod`: on a compact boundaryless manifold, the
  periods of a closed form form a countable subset of `ℝ`.

The manifold has the homotopy type of a finite CW complex (`TauCeti.FiniteCWType.of_isManifold`),
so `H_p(M; ℤ)` is a finitely generated abelian group
(`TauCeti.finite_singularHomology_of_finiteCWType`), hence countable, and so is the image of the
additive map `closedFormHomologyPeriod φ`. The passage from the finiteness of the singular
homology module to the homology of `singularChains ℤ` follows the proof of the instance
`FiniteDimensional ℝ (deRhamCohomology I M 1)` in Tau Ceti's
`Geometry/Manifold/DeRham/FiniteDimensional.lean`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017]
-/

public section

open CategoryTheory
open scoped Manifold ContDiff

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type} [TopologicalSpace M] [ChartedSpace H M]
  [FiniteDimensional ℝ E] [T2Space M] [IsManifold I ∞ M] [I.Boundaryless] [CompactSpace M]
  {p : ℕ}

/-- On a compact boundaryless manifold, the periods of a closed smooth real form on integral
singular homology `H_p(M; ℤ)` form a countable set. -/
theorem countable_range_closedFormHomologyPeriod (φ : closedForms I M p) :
    (Set.range (closedFormHomologyPeriod φ)).Countable := by
  have := FiniteCWType.of_isManifold (I := I) M
  have h := finite_singularHomology_of_finiteCWType (k := ℤ) M (ModuleCat.of ℤ ℤ) p
  rw [singularHomologyFunctor_obj_obj] at h
  -- `h` uses the `ℤ`-module structure of `ModuleCat ℤ`; the two `ℤ`-module structures agree.
  have : Module.Finite ℤ (((singularChains ℤ).obj (TopCat.of M)).homology p) := by
    convert h
  have := Countable.of_moduleFinite (R := ℤ)
    (M := ((singularChains ℤ).obj (TopCat.of M)).homology p)
  exact Set.countable_range _

end TauCeti

end
