/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Determinant
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Hermitian.RealChernClass
public import SymplecticGeometry.Topology.VectorBundle.Complex.FirstChernClass
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Smooth
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.TopForm
public import TauCeti.Geometry.Manifold.DeRham.PoincarePairing.Basic
import SymplecticGeometry.Geometry.Manifold.VectorBundle.ChernNumber.ChernWeil

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

For a line bundle, Tau Ceti's `TauCeti.DetBundle.lineHomeomorph` identifies the determinant line
with the bundle, smoothly (`TauCeti.DetBundle.contMDiff_lineHomeomorph`). The unit vectors of the
unitary frames of the determinant line, carried along this identification, form a smooth
`Circle`-equivariant map to the nonzero vectors of the bundle, so the two real first Chern classes
agree (`SymplecticGeometry.Bundle.realFirstChernClass_eq_of_equivariant`).

Over a closed oriented surface, the class is compared with the integral first Chern class: a
closed representative integrates to the Chern number `chernNumber` of the complex bundle. Under
integration on de Rham cohomology, `TauCeti.deRhamCohomology.integral`, the class goes to the
Chern number of the determinant line
(`Bundle.ContMDiffRiemannianMetric.integral_realFirstChernClass`), which is that of the bundle
(`SymplecticGeometry.Bundle.chernNumber_detBundle`), and a closed form goes to its integral
(`TauCeti.deRhamCohomology.integral_mk`).

## Main definitions and results

* `SymplecticGeometry.Bundle.ContMDiffComplexStructure.realFirstChernClass G J`: the real first
  Chern class of the smooth complex vector bundle given by `J`, a class in
  `TauCeti.deRhamCohomology I M 2`.
* `SymplecticGeometry.Bundle.ContMDiffComplexStructure.realFirstChernClass_eq_of_metric`: it is
  the real first Chern class of the unitary frame bundle of the determinant line for every smooth
  Hermitian metric on that line.
* `SymplecticGeometry.Bundle.ContMDiffComplexStructure.realFirstChernClass_eq_of_finrank_eq_one`:
  for a line bundle, it is the real first Chern class of the unitary frame bundle of the bundle
  itself, for every smooth Hermitian metric on it.
* `SymplecticGeometry.Bundle.ContMDiffComplexStructure.integral_realFirstChernClass`: over a
  closed oriented surface, the integral of the class is the Chern number of the bundle.
* `SymplecticGeometry.Bundle.ContMDiffComplexStructure.integralTopForm_realFirstChernClass`: over
  a closed oriented surface, every closed representative of the class integrates to the Chern
  number of the bundle.

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

/-- **The real first Chern class of a smooth complex line bundle.** If the complex model `G` is a
line, the real first Chern class of a smooth complex structure `J` is the real first Chern class
of the unitary frame bundle of the line bundle `J.toContinuousComplexStructure.Fiber` itself, for
every smooth metric `g` on it that multiplication by `Complex.I` preserves. -/
theorem realFirstChernClass_eq_of_finrank_eq_one [Fact (finrank ℂ G = 1)]
    (J : ContMDiffComplexStructure I ⊤ F V)
    (g : ContMDiffRiemannianMetric I ∞ G J.toContinuousComplexStructure.Fiber)
    (hI : ∀ x v w, g.inner x (Complex.I • v) (Complex.I • w) = g.inner x v w) :
    realFirstChernClass G J = g.realFirstChernClass hI := by
  have hG : finrank ℂ G = 1 := Fact.out
  obtain ⟨g₀, hI₀⟩ := exists_hermitianMetric_detBundle G J
  rw [realFirstChernClass_eq_of_metric G J g₀ hI₀,
    ContMDiffRiemannianMetric.realFirstChernClass_def g₀ hI₀]
  let : RiemannianBundle (DetBundle ℂ G J.toContinuousComplexStructure.Fiber) :=
    ⟨g₀.toRiemannianMetric⟩
  let : ∀ x, InnerProductSpace ℂ (DetBundle ℂ G J.toContinuousComplexStructure.Fiber x) :=
    g₀.complexInnerProductSpace hI₀
  let : IsContinuousRiemannianBundle ℂ (DetBundle ℂ G J.toContinuousComplexStructure.Fiber) :=
    instIsContinuousRiemannianBundle g₀.toContinuousRiemannianMetric
  have : ContMDiffFiberBundle ∞ Circle
      (OrthonormalFrameBundle.Fiber ℂ ℂ (DetBundle ℂ G J.toContinuousComplexStructure.Fiber) ℂ)
      I (𝓡 1) :=
    contMDiffFiberBundle_circleFiber g₀ hI₀
  -- The unit vector of a unitary frame of the determinant line, carried to the bundle itself.
  refine realFirstChernClass_eq_of_equivariant g hI
    (fun x φ ↦ DetBundle.lineEquiv hG x (φ.frame 1)) ?_ (fun _ φ ↦ ?_) fun z _ φ ↦ ?_
  · exact ((DetBundle.contMDiff_lineHomeomorph hG).comp
      (contMDiff_circleFiber_frame_one g₀ hI₀)).congr fun _ ↦ by
        rw [Function.comp_apply, DetBundle.lineHomeomorph_apply]
  · exact (map_ne_zero_iff _ (DetBundle.lineEquiv hG _).injective).2
      (φ.frame.map_ne_zero_iff.2 one_ne_zero)
  · rw [OrthonormalFrameBundle.Fiber.frame_op_circle_smul_apply, mul_one, ← _root_.map_smul,
      ← _root_.map_smul, smul_eq_mul, mul_one]

section Surface

variable {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
  [IsManifold (𝓡 2) ∞ M] [T2Space M] [CompactSpace M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V (𝓡 2)]
  (G : Type*) [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G]
  [Fact (finrank ℝ F = 2 * finrank ℂ G)]

/-- **The real first Chern class integrates to the Chern number.** Let `M` be a closed smooth
surface with an orientation `o`, and `J` a smooth complex structure on a smooth real vector bundle
`V` over `M`. The integral over `M` of the real first Chern class of `J` is the first Chern number
of the complex vector bundle given by `J`, for the homological orientation of `o`. -/
theorem integral_realFirstChernClass (J : ContMDiffComplexStructure (𝓡 2) ⊤ F V)
    (o : Manifold.Orientation (𝓡 2) M (Fin 2)) :
    deRhamCohomology.integral o (realFirstChernClass G J) =
      chernNumber (o.toHomologicalOrientation finrank_euclideanSpace_fin)
        finrank_euclideanSpace_fin G J.toContinuousComplexStructure.Fiber := by
  obtain ⟨g, hI⟩ := exists_hermitianMetric_detBundle G J
  rw [realFirstChernClass_eq_of_metric G J g hI, g.integral_realFirstChernClass hI o,
    chernNumber_detBundle]

/-- **Closed representatives of the real first Chern class integrate to the Chern number.** Let
`M` be a closed smooth surface with an orientation `o`, and `J` a smooth complex structure on a
smooth real vector bundle `V` over `M`. The integral over `M` of every closed `2`-form whose de Rham
class is the real first Chern class of `J` is the first Chern number of the complex vector bundle
given by `J`, for the homological orientation of `o`. -/
theorem integralTopForm_realFirstChernClass (J : ContMDiffComplexStructure (𝓡 2) ⊤ F V)
    (o : Manifold.Orientation (𝓡 2) M (Fin 2)) {σ : SmoothForm (𝓡 2) M ℝ 2}
    (hσ : σ ∈ closedForms (𝓡 2) M 2)
    (hσJ : deRhamCohomology.mk (𝓡 2) 2 ⟨σ, hσ⟩ = realFirstChernClass G J) :
    integralTopForm o σ.val = chernNumber (o.toHomologicalOrientation finrank_euclideanSpace_fin)
      finrank_euclideanSpace_fin G J.toContinuousComplexStructure.Fiber := by
  rw [← integral_realFirstChernClass G J o, ← hσJ, deRhamCohomology.integral_mk]

end Surface

end SymplecticGeometry.Bundle.ContMDiffComplexStructure

end
