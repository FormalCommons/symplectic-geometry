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
public import SymplecticGeometry.AlgebraicTopology.Cohomology.IntegralCohomologyULift
public import SymplecticGeometry.Topology.VectorBundle.Complex.RestrictScalars
public import TauCeti.Topology.VectorBundle.Orientation.Complex.EulerClass
public import TauCeti.Topology.VectorBundle.Orientation.SectionIndex

import SymplecticGeometry.AlgebraicTopology.Cohomology.FundamentalClass

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

For a complex vector bundle `V → M` of complex rank `r + 1` with a continuous section `s` that has
finitely many zeros,
`SymplecticGeometry.complexManifoldEvalFundamentalClass_complexEulerClass_eq_sum_sectionIndex`
computes the pairing of its Euler class `TauCeti.complexEulerClass` with `[M]` as the sum of the
local indices of `s` at its zeros, by Tau Ceti's
`TauCeti.VectorBundleOrientation.evalFundamentalClass_eulerClass_eq_sum_sectionIndex`.

Tau Ceti's `TauCeti.complexHomologicalOrientation` (in
`TauCeti/Geometry/Manifold/Complex/FundamentalClass.lean`) is the same construction for the model
`ℂ`, reindexed to `Fin 2`; the definitions here follow it.

## References

* [R. Bott, L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982], §3 (orienting a
  manifold by an atlas whose transition maps have positive Jacobian determinant).
* A. Hatcher, *Algebraic Topology*, Cambridge University Press (2002), §3.3 (homological
  orientations and fundamental classes).
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §11 (the Euler class as a sum of indices of a section) and §14 (the canonical
  orientation of a complex vector bundle).
-/

public section

open Bundle Module TauCeti
open scoped Manifold TauCeti.ComplexManifold VectorBundle.ComplexToReal

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

variable {E M}

/-- **The Euler number of a complex vector bundle as a sum of local indices.** Let `M` be a compact
complex manifold modelled on `𝓘(ℂ, E)`, of complex dimension `finrank ℂ E = r + 1`, and `V → M` a
complex vector bundle with model fibre `G` of the same complex rank `r + 1`. For a continuous
section `s` of `V` with finitely many zeros, the Euler class `complexEulerClass G V hG`, read in
integral cohomology and evaluated on the fundamental class of `M` for its complex orientation, is
the sum over the zeros of `s` of the local index of `s`, for the complex orientation of `V`
(reindexed to `Fin (2 r + 2)`) and that of `M`. -/
theorem complexManifoldEvalFundamentalClass_complexEulerClass_eq_sum_sectionIndex [CompactSpace M]
    (hE : finrank ℂ E = r + 1)
    {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedSpace ℂ G] [IsScalarTower ℝ ℂ G]
    [FiniteDimensional ℂ G]
    {V : M → Type} [TopologicalSpace (TotalSpace G V)] [∀ x, AddCommGroup (V x)]
    [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)] [∀ x, IsScalarTower ℝ ℂ (V x)]
    [∀ x, TopologicalSpace (V x)] [FiberBundle G V] [VectorBundle ℂ G V]
    (hG : finrank ℂ G = r + 1) {s : ∀ x, V x} (hs : Continuous fun x ↦ TotalSpace.mk' G x (s x))
    (hZ : {x | s x = 0}.Finite) :
    complexManifoldEvalFundamentalClass E M hE
        (((TopCat.of M).uliftIntegralCohomologyIso (2 * r + 2)).hom (complexEulerClass G V hG)) =
      ∑ z ∈ hZ.toFinset,
        ((VectorBundleOrientation.complex G V).reindex (finCongr (by rw [hG]; ring))).sectionIndex
          (by rw [finrank_real_eq_two_mul_finrank_complex, hG]; ring)
          (complexManifoldHomologicalOrientation E M hE) hs z := by
  rw [complexManifoldEvalFundamentalClass_def,
    HomologicalOrientation.evalFundamentalClass_uliftIntegralCohomologyIso_hom,
    complexEulerClass_def,
    VectorBundleOrientation.evalFundamentalClass_eulerClass_eq_sum_sectionIndex _ _ _ hs
      (finrank_real_of_finrank_complex_eq_add_one hE) hZ]

end SymplecticGeometry

end
