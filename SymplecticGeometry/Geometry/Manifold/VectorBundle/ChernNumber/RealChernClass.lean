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

For a line bundle, Tau Ceti's `TauCeti.DetBundle.lineHomeomorph` identifies the determinant line
with the bundle, smoothly (`TauCeti.DetBundle.contMDiff_lineHomeomorph`). The unit vectors of the
unitary frames of the determinant line, carried along this identification, form a smooth
`Circle`-equivariant map to the nonzero vectors of the bundle, so the two real first Chern classes
agree (`SymplecticGeometry.Bundle.realFirstChernClass_eq_of_equivariant`).

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
* `SymplecticGeometry.Bundle.ContMDiffComplexStructure.realFirstChernClass_pushforward`: a smooth
  isomorphism of real vector bundles that carries one smooth complex structure to another does not
  change the class, whatever the complex models of the two structures.

## Implementation notes

For `realFirstChernClass_pushforward`, the isomorphism `Φ` is complex-linear from
`J.toContinuousComplexStructure.Fiber` to `J'.toContinuousComplexStructure.Fiber`
(`TauCeti.Bundle.ContinuousComplexStructure.fiberEquivOfCommute`), and smooth on total spaces
(`SymplecticGeometry.Bundle.ContMDiffComplexStructure.contMDiff_fiberEquivOfCommute`), so it
induces a smooth map of determinant lines (`TauCeti.DetBundle.contMDiff_congrModelHomeomorph`).
That map is a smooth `ℂ`-linear isomorphism of determinant lines, so
`Bundle.ContMDiffRiemannianMetric.realFirstChernClass_congr` applies to it.

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

variable {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F'] [FiniteDimensional ℝ F']
  {V' : M → Type*} [∀ x, AddCommGroup (V' x)] [∀ x, Module ℝ (V' x)]
  [∀ x, TopologicalSpace (V' x)] [∀ x, IsTopologicalAddGroup (V' x)]
  [∀ x, ContinuousSMul ℝ (V' x)] [TopologicalSpace (TotalSpace F' V')]
  [FiberBundle F' V'] [VectorBundle ℝ F' V'] [ContMDiffVectorBundle ∞ F' V' I]
  (G' : Type*) [NormedAddCommGroup G'] [NormedSpace ℂ G'] [FiniteDimensional ℂ G']
  [Fact (finrank ℝ F' = 2 * finrank ℂ G')]

/-- **A complex-linear isomorphism does not change the real first Chern class.** Let `J` and `J'`
be smooth complex structures on smooth real vector bundles `V` and `V'` over the same base, with
complex models `G` and `G'`. If a family `Φ x : V x ≃ V' x` of real-linear isomorphisms is smooth
on total spaces and carries `J` to `J'`, that is `Φ x (J x v) = J' x (Φ x v)`, then `J` and `J'`
have the same real first Chern class. -/
theorem realFirstChernClass_pushforward (J : ContMDiffComplexStructure I ⊤ F V)
    (J' : ContMDiffComplexStructure I ⊤ F' V') (Φ : ∀ x, V x ≃L[ℝ] V' x)
    (hΦ : ContMDiff (I.prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, F')) ∞
      (fun p : TotalSpace F V ↦ TotalSpace.mk' F' p.proj (Φ p.proj p.snd)))
    (hJ : ∀ x v, Φ x (J x v) = J' x (Φ x v)) :
    realFirstChernClass G J = realFirstChernClass G' J' := by
  set K := J.toContinuousComplexStructure
  have hK : ∀ x v, Φ x (K x v) = J'.toContinuousComplexStructure x (Φ x v) := fun x v ↦ by
    rw [J.toContinuousComplexStructure_apply, J'.toContinuousComplexStructure_apply, hJ]
  -- `Φ` as a smooth complex-linear isomorphism of the complex bundles.
  set e := K.fiberEquivOfCommute J'.toContinuousComplexStructure Φ hK
  rw [realFirstChernClass_def, realFirstChernClass_def]
  exact ContMDiffRiemannianMetric.realFirstChernClass_congr _ _ _ _
    (DetBundle.congrModelEquiv (F₁ := G) (F' := G') e)
    ((DetBundle.contMDiff_congrModelHomeomorph e
      (J.contMDiff_fiberEquivOfCommute G J' G' Φ hΦ hK)).congr fun _ ↦
        (DetBundle.congrModelHomeomorph_apply ..).symm)

end SymplecticGeometry.Bundle.ContMDiffComplexStructure

end
