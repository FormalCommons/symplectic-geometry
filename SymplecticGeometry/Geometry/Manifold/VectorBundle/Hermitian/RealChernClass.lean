/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Hermitian.CircleBundle
public import SymplecticGeometry.Geometry.Manifold.FiberBundle.Principal.RealChernClass
public import TauCeti.Geometry.Manifold.VectorBundle.Pullback
import SymplecticGeometry.Topology.VectorBundle.Pullback
import SymplecticGeometry.Data.Bundle

/-!
# The real first Chern class of a Hermitian line bundle

Let `V` be a smooth complex line bundle over a finite-dimensional, boundaryless, Hausdorff,
σ-compact manifold `B`. A smooth `i`-invariant metric `g` on `V` makes it a Hermitian line bundle,
whose unitary frames form the smooth principal `Circle`-bundle
`SymplecticGeometry.Bundle.contMDiffFiberBundle_circleFiber`; it has a real first Chern class
`SymplecticGeometry.realFirstChernClass`, which this file names
`Bundle.ContMDiffRiemannianMetric.realFirstChernClass g hI`. It shows that this class does not
depend on `g` (`Bundle.ContMDiffRiemannianMetric.realFirstChernClass_eq_of_metric`), and that it
is natural under pull-back along a smooth map `f : B' → B`: for any smooth Hermitian metric on
Tau Ceti's pull-back bundle `f *ᵖ V`, the class of its unitary frame bundle is the pull-back
along `f` of that of `V` (`Bundle.ContMDiffRiemannianMetric.realFirstChernClass_pullback`).

Both rest on `SymplecticGeometry.Bundle.realFirstChernClass_eq_map_of_equivariant`. Given a smooth
map `σ` from a principal `Circle`-bundle `Q` over `B'` to the nonzero vectors of `V`, covering `f`
and commuting with the action of `Circle`, the map sending `q` to the `g`-unitary frame
`normalizedFrame (σ q)`, whose unit vector is `σ q / ‖σ q‖_g`, is a smooth map of circle bundles
over `f` (by `SymplecticGeometry.Bundle.contMDiffOn_normalizedFrame`) that commutes with the action
(`SymplecticGeometry.Bundle.normalizedFrame_circle_smul`). So the naturality of the real first
Chern class, `SymplecticGeometry.realFirstChernClass_map`, applies. For the change of metric, `σ`
sends a unitary frame `φ` of a second metric to its unit vector `φ 1`, over the identity of `B`.
For the pull-back, `σ` sends a unitary frame `φ` of `f *ᵖ V` over `x` to `φ 1 ∈ V (f x)`. In
both cases `σ` is smooth by `SymplecticGeometry.Bundle.contMDiff_circleFiber_frame_one`, followed
for the pull-back by Tau Ceti's `Bundle.Pullback.contMDiff_lift`, so no comparison of the metric on
`f *ᵖ V` with that of `V` is needed.

## Main results

* `Bundle.ContMDiffRiemannianMetric.realFirstChernClass`: the real first Chern class of the
  unitary frame bundle of a smooth Hermitian metric on a complex line bundle.
* `SymplecticGeometry.Bundle.realFirstChernClass_eq_map_of_equivariant`: the real first Chern class
  of a principal `Circle`-bundle with an equivariant smooth map to the nonzero vectors of `V` over
  `f` is the pull-back along `f` of that of the unitary frame bundle of `V`.
* `Bundle.ContMDiffRiemannianMetric.realFirstChernClass_eq_of_metric`: the real first Chern
  classes of the unitary frame bundles of two smooth Hermitian metrics on a complex line bundle
  are equal.
* `Bundle.ContMDiffRiemannianMetric.realFirstChernClass_pullback`: the real first Chern class
  of the unitary frame bundle of a Hermitian metric on `f *ᵖ V` is the pull-back along `f` of that
  of `V`, whatever the metrics.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.7
  (Chern classes of Hermitian line bundles, computed with a metric).
* S. Kobayashi and K. Nomizu, *Foundations of Differential Geometry*, Vol. I, Interscience, 1963,
  Chapter II, §6 (mappings of connections).
-/

public section

noncomputable section

open Bundle MulOpposite Module TauCeti TauCeti.OrthonormalFrameBundle
open scoped Manifold ContDiff

namespace SymplecticGeometry.Bundle

variable {EB HB B F : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  {IB : ModelWithCorners ℝ EB HB} [TopologicalSpace B] [ChartedSpace HB B] [IsManifold IB ∞ B]
  [IB.Boundaryless] [FiniteDimensional ℝ EB] [T2Space B] [SigmaCompactSpace B]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  [Fact (finrank ℂ F = 1)]
  {V : B → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)]
  [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℂ F V]

attribute [local instance] finrank_real_complex_fact'

open scoped VectorBundle.ComplexToReal Module.ComplexToReal

variable [ContMDiffVectorBundle ∞ F V IB]

variable (g : ContMDiffRiemannianMetric IB ∞ F V)
  (hI : ∀ x (v w : V x), g.inner x (Complex.I • v) (Complex.I • w) = g.inner x v w)

/-- The real first Chern class of a smooth Hermitian line bundle: for a smooth metric `g` on a
smooth complex line bundle `V` that is invariant under multiplication by `i`, the real first Chern
class `SymplecticGeometry.realFirstChernClass` of the smooth principal `Circle`-bundle of
`g`-unitary frames of `V`. It does not depend on `g`
(`Bundle.ContMDiffRiemannianMetric.realFirstChernClass_eq_of_metric`). -/
def _root_.Bundle.ContMDiffRiemannianMetric.realFirstChernClass : deRhamCohomology IB B 2 :=
  letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
  letI : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
  letI : IsContinuousRiemannianBundle F V :=
    instIsContinuousRiemannianBundle g.toContinuousRiemannianMetric
  haveI : ContMDiffFiberBundle ∞ Circle (Fiber ℂ F V ℂ) IB (𝓡 1) :=
    contMDiffFiberBundle_circleFiber g hI
  SymplecticGeometry.realFirstChernClass IB (Fiber ℂ F V ℂ)

theorem _root_.Bundle.ContMDiffRiemannianMetric.realFirstChernClass_def :
    g.realFirstChernClass hI =
      letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
      letI : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
      letI : IsContinuousRiemannianBundle F V :=
        instIsContinuousRiemannianBundle g.toContinuousRiemannianMetric
      haveI : ContMDiffFiberBundle ∞ Circle (Fiber ℂ F V ℂ) IB (𝓡 1) :=
        contMDiffFiberBundle_circleFiber g hI
      SymplecticGeometry.realFirstChernClass IB (Fiber ℂ F V ℂ) :=
  (rfl)

section Map

variable {EB' HB' B' : Type*} [NormedAddCommGroup EB'] [NormedSpace ℝ EB'] [TopologicalSpace HB']
  {IB' : ModelWithCorners ℝ EB' HB'} [TopologicalSpace B'] [ChartedSpace HB' B']
  [IsManifold IB' ∞ B'] [IB'.Boundaryless] [FiniteDimensional ℝ EB'] [T2Space B']
  [SigmaCompactSpace B']

/-- Let `Q` be a smooth principal `Circle`-bundle over `B'`, let `f : B' → B` be smooth, and let
`σ` be a smooth map from the total space of `Q` to the nonzero vectors of a smooth complex line
bundle `V` over `B`, sending the fibre over `x` to `V (f x)` and commuting with the actions of
`Circle`. Then the real first Chern class of `Q` is the pull-back along `f` of that of the unitary
frame bundle of any smooth Hermitian metric `g` on `V`. -/
theorem realFirstChernClass_eq_map_of_equivariant {Q : B' → Type*}
    [TopologicalSpace (TotalSpace Circle Q)] [∀ x, TopologicalSpace (Q x)] [FiberBundle Circle Q]
    [∀ x, MulAction Circleᵐᵒᵖ (Q x)] [PrincipalBundle Circle Q]
    [ContMDiffFiberBundle ∞ Circle Q IB' (𝓡 1)] {f : B' → B} (hf : ContMDiff IB' IB ∞ f)
    (σ : ∀ x, Q x → V (f x))
    (hσ : ContMDiff (IB'.prod (𝓡 1)) (IB.prod 𝓘(ℝ, F)) ∞ fun q : ManifoldTotalSpace Circle Q ↦
      (⟨f ((ManifoldTotalSpace.homeomorph _ _).symm q).proj,
        σ _ ((ManifoldTotalSpace.homeomorph _ _).symm q).snd⟩ : TotalSpace F V))
    (hσ₀ : ∀ x q, σ x q ≠ 0) (hσz : ∀ (z : Circle) x (q : Q x), σ x (op z • q) = (z : ℂ) • σ x q) :
    realFirstChernClass IB' Q = deRhamCohomology.map f hf 2 (g.realFirstChernClass hI) := by
  rw [ContMDiffRiemannianMetric.realFirstChernClass_def]
  let : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
  let : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
  let : IsContinuousRiemannianBundle F V :=
    instIsContinuousRiemannianBundle g.toContinuousRiemannianMetric
  have : ContMDiffFiberBundle ∞ Circle (Fiber ℂ F V ℂ) IB (𝓡 1) :=
    contMDiffFiberBundle_circleFiber g hI
  let h := ManifoldTotalSpace.homeomorph Circle Q
  let Φ : ManifoldTotalSpace Circle Q → ManifoldTotalSpace Circle (Fiber ℂ F V ℂ) := fun q ↦
    ManifoldTotalSpace.homeomorph Circle (Fiber ℂ F V ℂ)
      ⟨f (h.symm q).proj, normalizedFrame (F := F) (σ _ (h.symm q).snd)⟩
  have hΦ : ContMDiff (IB'.prod (𝓡 1)) (IB.prod (𝓡 1)) ∞ Φ := by
    rw [← contMDiffOn_univ]
    exact contMDiffOn_normalizedFrame g hI isOpen_univ hσ.contMDiffOn fun q _ ↦ hσ₀ _ _
  have hΦh (p : TotalSpace Circle Q) : Φ (h p) = ManifoldTotalSpace.homeomorph Circle
      (Fiber ℂ F V ℂ) ⟨f p.proj, normalizedFrame (F := F) (σ _ p.snd)⟩ := by
    simp only [Φ]
    rw [h.symm_apply_apply]
  have hΦz (z : Circle) (q : ManifoldTotalSpace Circle Q) : Φ (op z • q) = op z • Φ q := by
    obtain ⟨p, rfl⟩ := h.surjective q
    rw [ManifoldTotalSpace.smul_homeomorph, hΦh, hΦh, ManifoldTotalSpace.smul_homeomorph, hσz,
      normalizedFrame_circle_smul z (hσ₀ _ _)]
  exact realFirstChernClass_map hf hΦ hΦz (funext fun q ↦ by simp [Φ, h])

/-- **The real first Chern class of a Hermitian line bundle is natural under pull-back.** Let `g`
be a smooth `i`-invariant metric on a smooth complex line bundle `V` over `B`, let `f : B' → B` be
smooth, and let `g''` be any smooth `i`-invariant metric on the pull-back bundle `f *ᵖ V`. Then
the real first Chern class of the principal `Circle`-bundle of `g''`-unitary frames of `f *ᵖ V`
is the pull-back along `f` of that of the bundle of `g`-unitary frames of `V`. -/
theorem _root_.Bundle.ContMDiffRiemannianMetric.realFirstChernClass_pullback
    {K : Type*} [FunLike K B' B] [ContinuousMapClass K B' B] (f : K) (hf : ContMDiff IB' IB ∞ f)
    (g'' : ContMDiffRiemannianMetric IB' ∞ F ((f : B' → B) *ᵖ V))
    (hI'' : ∀ x (v w : ((f : B' → B) *ᵖ V) x),
      g''.inner x (Complex.I • v) (Complex.I • w) = g''.inner x v w) :
    haveI := _root_.Bundle.Pullback.contMDiffVectorBundle (F := F) (E := V) hf
    g''.realFirstChernClass hI'' = deRhamCohomology.map f hf 2 (g.realFirstChernClass hI) := by
  have := _root_.Bundle.Pullback.contMDiffVectorBundle (F := F) (E := V) hf
  let : RiemannianBundle ((f : B' → B) *ᵖ V) := ⟨g''.toRiemannianMetric⟩
  let : ∀ x, InnerProductSpace ℂ (((f : B' → B) *ᵖ V) x) := g''.complexInnerProductSpace hI''
  let : IsContinuousRiemannianBundle F ((f : B' → B) *ᵖ V) :=
    instIsContinuousRiemannianBundle g''.toContinuousRiemannianMetric
  have : ContMDiffFiberBundle ∞ Circle (Fiber ℂ F ((f : B' → B) *ᵖ V) ℂ) IB' (𝓡 1) :=
    contMDiffFiberBundle_circleFiber g'' hI''
  rw [ContMDiffRiemannianMetric.realFirstChernClass_def g'' hI'']
  refine realFirstChernClass_eq_map_of_equivariant g hI hf (fun _ φ ↦ φ.frame 1) ?_
    (fun _ φ ↦ φ.frame.map_ne_zero_iff.2 one_ne_zero) fun z _ φ ↦ ?_
  · -- The unit vectors of the frames, in `f *ᵖ V`, followed by `Pullback.lift f` into `V`.
    exact (_root_.Bundle.Pullback.contMDiff_lift f hf).comp
      (contMDiff_circleFiber_frame_one g'' hI'')
  · rw [Fiber.frame_op_circle_smul_apply, mul_one]
    simpa using φ.frame.map_smul (z : ℂ) 1

end Map

/-- Let `Q` be a smooth principal `Circle`-bundle over `B` with a smooth map `σ` from its total
space to the nonzero vectors of a smooth complex line bundle `V`, over the identity of `B`, that
commutes with the actions of `Circle`. Then the real first Chern class of `Q` is that of the
unitary frame bundle of any smooth Hermitian metric `g` on `V`. -/
theorem realFirstChernClass_eq_of_equivariant {Q : B → Type*}
    [TopologicalSpace (TotalSpace Circle Q)] [∀ x, TopologicalSpace (Q x)] [FiberBundle Circle Q]
    [∀ x, MulAction Circleᵐᵒᵖ (Q x)] [PrincipalBundle Circle Q]
    [ContMDiffFiberBundle ∞ Circle Q IB (𝓡 1)] (σ : ∀ x, Q x → V x)
    (hσ : ContMDiff (IB.prod (𝓡 1)) (IB.prod 𝓘(ℝ, F)) ∞ fun q : ManifoldTotalSpace Circle Q ↦
      (⟨((ManifoldTotalSpace.homeomorph _ _).symm q).proj,
        σ _ ((ManifoldTotalSpace.homeomorph _ _).symm q).snd⟩ : TotalSpace F V))
    (hσ₀ : ∀ x q, σ x q ≠ 0) (hσz : ∀ (z : Circle) x (q : Q x), σ x (op z • q) = (z : ℂ) • σ x q) :
    realFirstChernClass IB Q = g.realFirstChernClass hI := by
  rw [realFirstChernClass_eq_map_of_equivariant g hI contMDiff_id σ hσ hσ₀ hσz,
    deRhamCohomology.map_id, LinearMap.id_apply]

/-- **The real first Chern class of a Hermitian line bundle does not depend on the metric.** For
two smooth `i`-invariant metrics `g` and `g'` on a smooth complex line bundle `V`, the real first
Chern classes of the smooth principal `Circle`-bundles of `g`-unitary and of `g'`-unitary frames
of `V` are equal. -/
theorem _root_.Bundle.ContMDiffRiemannianMetric.realFirstChernClass_eq_of_metric
    (g' : ContMDiffRiemannianMetric IB ∞ F V)
    (hI' : ∀ x (v w : V x), g'.inner x (Complex.I • v) (Complex.I • w) = g'.inner x v w) :
    g.realFirstChernClass hI = g'.realFirstChernClass hI' := by
  rw [ContMDiffRiemannianMetric.realFirstChernClass_def g hI]
  let : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
  let : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
  let : IsContinuousRiemannianBundle F V :=
    instIsContinuousRiemannianBundle g.toContinuousRiemannianMetric
  have : ContMDiffFiberBundle ∞ Circle (Fiber ℂ F V ℂ) IB (𝓡 1) :=
    contMDiffFiberBundle_circleFiber g hI
  refine realFirstChernClass_eq_of_equivariant g' hI' (Q := Fiber ℂ F V ℂ) (fun _ φ ↦ φ.frame 1)
    ?_ (fun _ φ ↦ ?_) fun z _ φ ↦ ?_
  · exact contMDiff_circleFiber_frame_one g hI
  · exact φ.frame.map_ne_zero_iff.2 one_ne_zero
  · rw [Fiber.frame_op_circle_smul_apply, mul_one, ← _root_.map_smul, smul_eq_mul, mul_one]

end SymplecticGeometry.Bundle
