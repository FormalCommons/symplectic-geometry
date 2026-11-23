/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.FundamentalClass
public import TauCeti.AlgebraicTopology.Cohomology.IntegralCup
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Smooth
public import SymplecticGeometry.Geometry.Manifold.Complex.Orientation
public import SymplecticGeometry.LinearAlgebra.Complex.Finrank

/-!
# The homological orientation and fundamental class of a complex manifold

A complex manifold `M` modelled on `𝓘(ℂ, E)`, of complex dimension `finrank ℂ E = r + 1`, is
oriented by its complex structure: Tau Ceti's `TauCeti.complexManifoldOrientation E M`, indexed
by `Fin (2 * finrank ℂ E)`. This file names, once for every such `E` and `M`, the two steps that
turn it into a pairing with the fundamental class:

* `SymplecticGeometry.complexManifoldHomologicalOrientation`: that orientation, reindexed to
  `Fin (2 r + 2)` (`SymplecticGeometry.complexManifoldOrientationOfFinrank`), as a homological
  orientation of `M` in degree `2 r + 2`, with
  `SymplecticGeometry.complexManifoldHomologicalOrientation_def`;
* `SymplecticGeometry.complexManifoldEvalFundamentalClass`: for `M` compact, the `ℤ`-linear map
  `H^{2r+2}(M; ℤ) → ℤ`, `c ↦ ⟨c, [M]⟩`, for that orientation, with
  `SymplecticGeometry.complexManifoldEvalFundamentalClass_def`.

Tau Ceti's `TauCeti.complexHomologicalOrientation` (in
`TauCeti/Geometry/Manifold/Complex/FundamentalClass.lean`) is the same construction for the model
`ℂ`, reindexed to `Fin 2`; the definitions here follow it.

## References

* [R. Bott, L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982], §3 (orienting a
  manifold by an atlas whose transition maps have positive Jacobian determinant).
* A. Hatcher, *Algebraic Topology*, Cambridge University Press (2002), §3.3 (homological
  orientations and fundamental classes).
-/

public section

open Module TauCeti
open scoped Manifold TauCeti.ComplexManifold

namespace SymplecticGeometry

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  (M : Type) [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) 1 M]
  {r : ℕ}

/-- **The homological orientation of a complex manifold.** A complex manifold `M` modelled on
`𝓘(ℂ, E)`, with `finrank ℂ E = r + 1`, is oriented by its complex structure: Tau Ceti's
`complexManifoldOrientation E M`, reindexed along `2 * finrank ℂ E = 2 r + 2`
(`complexManifoldOrientationOfFinrank E M hE`), as a homological orientation of `M` in degree
`2 r + 2`. -/
noncomputable def complexManifoldHomologicalOrientation (hE : finrank ℂ E = r + 1) :
    HomologicalOrientation M E (2 * r + 1 + 1) :=
  (complexManifoldOrientationOfFinrank E M hE).toHomologicalOrientation (n := 2 * r + 1)
    (finrank_real_of_finrank_complex_eq_add_one hE)

theorem complexManifoldHomologicalOrientation_def (hE : finrank ℂ E = r + 1) :
    complexManifoldHomologicalOrientation E M hE =
      (complexManifoldOrientationOfFinrank E M hE).toHomologicalOrientation (n := 2 * r + 1)
        (finrank_real_of_finrank_complex_eq_add_one hE) :=
  (rfl)

/-- **The evaluation on the fundamental class of a complex manifold**, `c ↦ ⟨c, [M]⟩`. For a
compact complex manifold `M` modelled on `𝓘(ℂ, E)`, with `finrank ℂ E = r + 1`, the `ℤ`-linear
map `H^{2r+2}(M; ℤ) → ℤ` that pairs a class with the fundamental class of `M` for its complex
orientation `complexManifoldHomologicalOrientation E M hE`. -/
noncomputable def complexManifoldEvalFundamentalClass [CompactSpace M]
    (hE : finrank ℂ E = r + 1) :
    (TopCat.of M).integralCohomology (2 * (r + 1)) →ₗ[ℤ] ℤ :=
  (complexManifoldHomologicalOrientation E M hE).evalFundamentalClass
    (finrank_real_of_finrank_complex_eq_add_one hE) (ModuleCat.of ℤ ℤ) (ContinuousMap.id M)

theorem complexManifoldEvalFundamentalClass_def [CompactSpace M] (hE : finrank ℂ E = r + 1) :
    complexManifoldEvalFundamentalClass E M hE =
      (complexManifoldHomologicalOrientation E M hE).evalFundamentalClass
        (finrank_real_of_finrank_complex_eq_add_one hE) (ModuleCat.of ℤ ℤ) (ContinuousMap.id M) :=
  (rfl)

end SymplecticGeometry

end
