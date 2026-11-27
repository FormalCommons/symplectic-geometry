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
with the bundle, smoothly (`TauCeti.DetBundle.contMDiff_lineHomeomorph`), and fibrewise it is the
`ℂ`-linear isomorphism `TauCeti.DetBundle.lineEquiv`, so the two real first Chern classes agree
(`Bundle.ContMDiffRiemannianMetric.realFirstChernClass_congr`). Under pull-back, the determinant
line of the pulled-back structure is, smoothly and `ℂ`-linearly, the pull-back of the determinant
line, and `Bundle.ContMDiffRiemannianMetric.realFirstChernClass_eq_map_of_equiv` applies.

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
* `SymplecticGeometry.Bundle.ContMDiffComplexStructure.realFirstChernClass_pullback`: the real
  first Chern class of the pull-back of `J` along a smooth map `f` is the pull-back along `f` of
  that of `J`.
* `SymplecticGeometry.Bundle.ContMDiffComplexStructure.integral_realFirstChernClass`: over a
  closed oriented surface, the integral of the class is the Chern number of the bundle.
* `SymplecticGeometry.Bundle.ContMDiffComplexStructure.integralTopForm_realFirstChernClass`: over
  a closed oriented surface, every closed representative of the class integrates to the Chern
  number of the bundle.
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

open Bundle Module TauCeti TauCeti.OrthonormalFrameBundle
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
  rw [realFirstChernClass_eq_of_metric G J g₀ hI₀]
  -- The determinant line of a line bundle is the bundle itself, smoothly.
  exact g₀.realFirstChernClass_congr hI₀ g hI (DetBundle.lineEquiv hG)
    ((DetBundle.contMDiff_lineHomeomorph hG).congr fun _ ↦ (DetBundle.lineHomeomorph_apply ..).symm)

section Pullback

variable {EN HN N : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN] [FiniteDimensional ℝ EN]
  [TopologicalSpace HN] {I' : ModelWithCorners ℝ EN HN} [I'.Boundaryless] [TopologicalSpace N]
  [ChartedSpace HN N] [IsManifold I' ∞ N] [T2Space N] [SigmaCompactSpace N]
  {K : Type*} [FunLike K N M] [ContinuousMapClass K N M]

/-- **The real first Chern class of a smooth complex vector bundle is natural under pull-back.**
For a smooth complex structure `J` on `V` over `M` and a smooth map `f : N → M`, the real first
Chern class of the pull-back `J.pullback f hf`, a complex structure on `f *ᵖ V`, is the pull-back
along `f` of the real first Chern class of `J`. -/
theorem realFirstChernClass_pullback (J : ContMDiffComplexStructure I ⊤ F V) (f : K)
    (hf : ContMDiff I' I ∞ f) :
    haveI := Pullback.contMDiffVectorBundle (F := F) (E := V) hf
    realFirstChernClass G (J.pullback f hf) =
      deRhamCohomology.map f hf 2 (realFirstChernClass G J) := by
  have := Pullback.contMDiffVectorBundle (F := F) (E := V) hf
  obtain ⟨g', hI'⟩ := exists_hermitianMetric_detBundle G (J.pullback f hf)
  obtain ⟨g, hI⟩ := exists_hermitianMetric_detBundle G J
  rw [realFirstChernClass_eq_of_metric G _ g' hI', realFirstChernClass_eq_of_metric G J g hI]
  set L' := DetBundle ℂ G (J.pullback f hf).toContinuousComplexStructure.Fiber
  -- The determinant line of `J.pullback f hf` at `y` is that of `J` at `f y`: transport along
  -- `pullbackFiberEquiv`, then the determinant line of a pull-back is the pull-back of the
  -- determinant line.
  let e (y : N) : L' y ≃L[ℂ] DetBundle ℂ G J.toContinuousComplexStructure.Fiber (f y) :=
    (DetBundle.congrModelEquiv (F₁ := G) (F' := G) (J.pullbackFiberEquiv f hf) y).trans
      (DetBundle.pullbackEquiv (f : N → M) y).symm
  refine g.realFirstChernClass_eq_map_of_equiv hI g' hI' hf e
    ((((Pullback.contMDiff_lift f hf).comp
      (DetBundle.contMDiff_pullbackHomeomorph_symm (n := ∞) (G := G)
        (E := J.toContinuousComplexStructure.Fiber) f)).comp
      (DetBundle.contMDiff_congrModelHomeomorph _
        (J.contMDiff_pullbackFiberEquiv G f hf))).congr fun p ↦ ?_)
  simp only [Function.comp_apply, DetBundle.congrModelHomeomorph_apply,
    DetBundle.pullbackHomeomorph_symm_apply, e]
  exact (Pullback.lift_mk (F := ℂ) _ _ _).symm

end Pullback

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
