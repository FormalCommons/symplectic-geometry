/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Determinant
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Hermitian.RealChernClass

/-!
# The real first Chern class of a smooth complex vector bundle

Let `J : ContMDiffComplexStructure I ⊤ F V` be a smooth complex structure on a smooth real vector
bundle `V` over a boundaryless, finite-dimensional, Hausdorff, σ-compact smooth manifold `M`, and
let `G` be a complex model with `dim_ℝ F = 2 dim_ℂ G`. The determinant line
`TauCeti.DetBundle ℂ G J.toContinuousComplexStructure.Fiber` is a smooth complex line bundle
(`TauCeti.DetBundle.contMDiffVectorBundle`) with a smooth Hermitian metric
(`SymplecticGeometry.Bundle.ContMDiffComplexStructure.exists_hermitianMetric_detBundle`). This
file defines the real first Chern class of `J` as the real first Chern class
`Bundle.ContMDiffRiemannianMetric.realFirstChernClass` of the unitary frame bundle of the
determinant line for that metric. Since the latter does not depend on the metric
(`Bundle.ContMDiffRiemannianMetric.realFirstChernClass_eq_of_metric`), neither does the choice
made here.

## Main definitions and results

* `SymplecticGeometry.Bundle.ContMDiffComplexStructure.realFirstChernClass G J`: the real first
  Chern class of the smooth complex vector bundle given by `J`, a class in
  `TauCeti.deRhamCohomology I M 2`.
* `SymplecticGeometry.Bundle.ContMDiffComplexStructure.realFirstChernClass_eq_of_metric`: it is
  the real first Chern class of the unitary frame bundle of the determinant line for every smooth
  Hermitian metric on that line.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.7.
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton University Press, 1974, §14 and Appendix C.
-/

public section

noncomputable section

open Bundle Module TauCeti
open scoped Manifold ContDiff VectorBundle.ComplexToReal

namespace SymplecticGeometry.Bundle.ContMDiffComplexStructure

variable {EB HB M : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [FiniteDimensional ℝ EB]
  [TopologicalSpace HB] {I : ModelWithCorners ℝ EB HB} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace HB M] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  (G : Type*) [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G]
  [Fact (finrank ℝ F = 2 * finrank ℂ G)]

/-- The real first Chern class of a smooth complex vector bundle. For a smooth complex structure
`J` on a smooth real vector bundle `V` with model `F`, and a complex model `G` with
`dim_ℝ F = 2 dim_ℂ G`, it is the real first Chern class of the smooth principal `Circle`-bundle of
unitary frames of the determinant line `TauCeti.DetBundle ℂ G J.toContinuousComplexStructure.Fiber`,
for a smooth Hermitian metric on that line. It does not depend on the metric
(`SymplecticGeometry.Bundle.ContMDiffComplexStructure.realFirstChernClass_eq_of_metric`). -/
def realFirstChernClass (J : ContMDiffComplexStructure I ⊤ F V) : deRhamCohomology I M 2 :=
  (exists_hermitianMetric_detBundle G J).choose.realFirstChernClass
    (exists_hermitianMetric_detBundle G J).choose_spec

/-- The real first Chern class of `J` is that of the unitary frame bundle of its determinant line
for the metric that `exists_hermitianMetric_detBundle` chooses. -/
theorem realFirstChernClass_def (J : ContMDiffComplexStructure I ⊤ F V) :
    realFirstChernClass G J =
      (exists_hermitianMetric_detBundle G J).choose.realFirstChernClass
        (exists_hermitianMetric_detBundle G J).choose_spec :=
  (rfl)

/-- The real first Chern class of a smooth complex vector bundle, given by a smooth complex
structure `J`, is the real first Chern class of the unitary frame bundle of the determinant line
`TauCeti.DetBundle ℂ G J.toContinuousComplexStructure.Fiber` for every smooth metric `g` on that
line that multiplication by `Complex.I` preserves. -/
theorem realFirstChernClass_eq_of_metric (J : ContMDiffComplexStructure I ⊤ F V)
    (g : ContMDiffRiemannianMetric I ∞ ℂ
      (TauCeti.DetBundle ℂ G J.toContinuousComplexStructure.Fiber))
    (hI : ∀ x v w, g.inner x (Complex.I • v) (Complex.I • w) = g.inner x v w) :
    realFirstChernClass G J = g.realFirstChernClass hI :=
  ContMDiffRiemannianMetric.realFirstChernClass_eq_of_metric _ _ g hI

end SymplecticGeometry.Bundle.ContMDiffComplexStructure

end
