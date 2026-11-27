/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Hermitian
public import SymplecticGeometry.Topology.VectorBundle.Complex.RestrictScalars
import TauCeti.Geometry.Manifold.VectorBundle.Scalar

/-!
# Smooth Hermitian metrics and the smoothness of Hermitian products

The class `SymplecticGeometry.Bundle.ContMDiffHermitianMetric` bundles a smooth real metric `g`
on a complex vector bundle `V` with the proof `hI` that multiplication by `Complex.I` preserves
it. Its scoped instances `riemannianBundle`, `innerProductSpace` and
`isContinuousRiemannianBundle` give the fibres of `V` the norms and real inner products of `g`
and the Hermitian products `g.complexInnerProductSpace hI`, and make the fibre metric continuous,
so that a proof about `(g, hI)` installs all of them with one `let`. Statements spell these
instances out with `letI`, in terms of `g` and `hI`. The lemmas `riemannianBundle_def` and
`innerProductSpace_def` state what the instances are, and `real_inner_eq`, `inner_eq` and
`norm_sq_eq` give the real inner products, Hermitian products and norms of the fibres in terms
of the underlying real metric; two instances of the class are equal when their metrics are
(`ContMDiffHermitianMetric.ext`).

For a smooth `i`-invariant real metric `g` on a complex vector bundle `V`, Tau Ceti's
`Bundle.ContMDiffRiemannianMetric.contMDiff_hermitianPairing` says that the Hermitian product
`g.complexInnerProductSpace hI` of two smooth maps into the total space is smooth. This file gives
its version within a set at a point,
`Bundle.ContMDiffRiemannianMetric.contMDiffWithinAt_hermitianPairing`, with the same proof: the
product is `g(v, w) + i g(i v, w)`. The version on a set,
`Bundle.ContMDiffRiemannianMetric.contMDiffOn_hermitianPairing`, follows from it.
-/

public section

open Bundle
open scoped Manifold ContDiff

/-! ### Smooth Hermitian metrics as a class -/

section HermitianMetric

open scoped VectorBundle.ComplexToReal InnerProductSpace

namespace SymplecticGeometry.Bundle

/-- A smooth Hermitian metric on a complex vector bundle `V`: a `C^n` Riemannian metric `metric`
on the underlying real bundle for which multiplication by `Complex.I` is an isometry of each
fibre. After `open scoped SymplecticGeometry.Bundle.ContMDiffHermitianMetric`, its instances give
the fibres of `V` the norms and real inner products of `metric` and the Hermitian products
`metric.complexInnerProductSpace inner_I_smul`, so that a proof about a metric `g` with `hI`
installs them with `let : ContMDiffHermitianMetric I n F V := ⟨g, hI⟩`. The model `I`, the
smoothness `n` and the model fibre `F` are `outParam`s, since the goals of these instances
mention only `V`. -/
@[ext]
class ContMDiffHermitianMetric {EB HB : outParam Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
    [TopologicalSpace HB] (I : outParam (ModelWithCorners ℝ EB HB)) {B : Type*}
    [TopologicalSpace B] [ChartedSpace HB B] (n : outParam ℕ∞ω) (F : outParam Type*)
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
    (V : B → Type*) [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)]
    [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, TopologicalSpace (V x)]
    [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
    [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℂ F V] where
  /-- The underlying smooth real metric. -/
  metric : ContMDiffRiemannianMetric I n F V
  /-- Multiplication by `Complex.I` preserves the metric. -/
  inner_I_smul (x : B) (v w : V x) :
    metric.inner x (Complex.I • v) (Complex.I • w) = metric.inner x v w

namespace ContMDiffHermitianMetric

/- The arguments on the model side (`EB`, `HB`, the charts of `B`, `F` and the bundle structure
of `V`) are implicit here: the class assigns them. As instance arguments they would be searched
for before the class, since they occur in the goals of the instances below, and that search does
not end within the default limits. -/
variable {EB HB : Type*} {iEB : NormedAddCommGroup EB} {iEBℝ : NormedSpace ℝ EB}
  {iHB : TopologicalSpace HB} {I : ModelWithCorners ℝ EB HB} {B : Type*} [TopologicalSpace B]
  {cB : ChartedSpace HB B} {n : ℕ∞ω} {F : Type*} {iF : NormedAddCommGroup F}
  {iFℝ : NormedSpace ℝ F} {iFℂ : NormedSpace ℂ F}
  {V : B → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)]
  [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  {iTV : TopologicalSpace (TotalSpace F V)} {fV : FiberBundle F V} {vV : VectorBundle ℂ F V}
  [h : ContMDiffHermitianMetric I n F V]

/-- The fibre metric of a smooth Hermitian metric. -/
scoped instance riemannianBundle : RiemannianBundle V := ⟨h.metric.toRiemannianMetric⟩

/-- The Hermitian products of a smooth Hermitian metric on the fibres. -/
noncomputable scoped instance innerProductSpace (x : B) : InnerProductSpace ℂ (V x) :=
  h.metric.complexInnerProductSpace h.inner_I_smul x

/-- The fibre metric of a smooth Hermitian metric is continuous. -/
scoped instance isContinuousRiemannianBundle : IsContinuousRiemannianBundle F V :=
  instIsContinuousRiemannianBundle h.metric.toContinuousRiemannianMetric

/-- The fibre metric of a smooth Hermitian metric is that of its underlying real metric. -/
theorem riemannianBundle_def :
    (riemannianBundle : RiemannianBundle V) = ⟨h.metric.toRiemannianMetric⟩ := (rfl)

/-- The Hermitian products of a smooth Hermitian metric are those that Tau Ceti's
`Bundle.ContMDiffRiemannianMetric.complexInnerProductSpace` builds from its underlying real
metric. -/
theorem innerProductSpace_def (x : B) :
    innerProductSpace x = h.metric.complexInnerProductSpace h.inner_I_smul x := (rfl)

/-- The real inner product of two vectors of a fibre is the value of the underlying metric. -/
theorem real_inner_eq (x : B) (v w : V x) : ⟪v, w⟫_ℝ = h.metric.inner x v w :=
  h.metric.inner_eq x v w

/-- The Hermitian product of `v` and `w` is `g(v, w) + i g(i v, w)`, for the underlying real
metric `g`. -/
theorem inner_eq (x : B) (v w : V x) :
    ⟪v, w⟫_ℂ = (h.metric.inner x v w : ℂ) + Complex.I * (h.metric.inner x (Complex.I • v) w : ℂ) :=
  h.metric.complexInnerProductSpace_inner h.inner_I_smul x v w

/-- The squared norm of a vector of a fibre is the value of the underlying metric on it. -/
theorem norm_sq_eq (x : B) (v : V x) : ‖v‖ ^ 2 = h.metric.inner x v v :=
  h.metric.norm_sq x v

end ContMDiffHermitianMetric

end SymplecticGeometry.Bundle

end HermitianMetric

namespace Bundle.ContMDiffRiemannianMetric

variable {X H B F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [TopologicalSpace H] {IB : ModelWithCorners ℝ X H}
  [TopologicalSpace B] [ChartedSpace H B]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  {V : B → Type*}
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)]
  [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℂ F V]
  {n : ℕ∞ω}
  {XM HM M : Type*} [NormedAddCommGroup XM] [NormedSpace ℝ XM]
  [TopologicalSpace HM] {IM : ModelWithCorners ℝ XM HM}
  [TopologicalSpace M] [ChartedSpace HM M]

open scoped VectorBundle.ComplexToReal

open scoped SymplecticGeometry.Bundle.ContMDiffHermitianMetric in
/-- The Hermitian product of two maps into the total space over a common base map is `C^n`
within a set at a point where both maps are. -/
theorem contMDiffWithinAt_hermitianPairing (g : ContMDiffRiemannianMetric IB n F V)
    (hI : ∀ x (v w : V x), g.inner x (Complex.I • v) (Complex.I • w) = g.inner x v w)
    {b : M → B} {v w : ∀ m, V (b m)} {s : Set M} {x : M}
    (hv : ContMDiffWithinAt IM (IB.prod 𝓘(ℝ, F)) n
      (fun m ↦ (⟨b m, v m⟩ : TotalSpace F V)) s x)
    (hw : ContMDiffWithinAt IM (IB.prod 𝓘(ℝ, F)) n
      (fun m ↦ (⟨b m, w m⟩ : TotalSpace F V)) s x) :
    letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
    letI : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
    ContMDiffWithinAt IM 𝓘(ℝ, ℂ) n (fun m ↦ Inner.inner ℂ (v m) (w m)) s x := by
  let : SymplecticGeometry.Bundle.ContMDiffHermitianMetric IB n F V := ⟨g, hI⟩
  have hre := hv.inner_bundle hw
  have him := ((contMDiffWithinAt_const (c := Complex.I)).smul_totalSpace hv).inner_bundle hw
  have hh := (Complex.ofRealCLM.contMDiff.contMDiffAt.comp_contMDiffWithinAt x hre).add
    (him.smul (contMDiffWithinAt_const (I' := 𝓘(ℝ, ℂ)) (c := Complex.I)))
  have heq (m : M) : Inner.inner ℂ (v m) (w m) =
      Complex.ofRealCLM (Inner.inner ℝ (v m) (w m)) +
        Inner.inner ℝ (Complex.I • v m) (w m) • Complex.I := by
    rw [SymplecticGeometry.Bundle.ContMDiffHermitianMetric.inner_eq]
    simp [SymplecticGeometry.Bundle.ContMDiffHermitianMetric.real_inner_eq, Complex.real_smul,
      mul_comm]
  exact hh.congr (fun m _ ↦ heq m) (heq x)

/-- The Hermitian product of two maps into the total space over a common base map is `C^n` on a
set where both maps are. -/
theorem contMDiffOn_hermitianPairing (g : ContMDiffRiemannianMetric IB n F V)
    (hI : ∀ x (v w : V x), g.inner x (Complex.I • v) (Complex.I • w) = g.inner x v w)
    {b : M → B} {v w : ∀ m, V (b m)} {s : Set M}
    (hv : ContMDiffOn IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (⟨b m, v m⟩ : TotalSpace F V)) s)
    (hw : ContMDiffOn IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (⟨b m, w m⟩ : TotalSpace F V)) s) :
    letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
    letI : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
    ContMDiffOn IM 𝓘(ℝ, ℂ) n (fun m ↦ Inner.inner ℂ (v m) (w m)) s :=
  fun x hx ↦ g.contMDiffWithinAt_hermitianPairing hI (hv x hx) (hw x hx)

end Bundle.ContMDiffRiemannianMetric
