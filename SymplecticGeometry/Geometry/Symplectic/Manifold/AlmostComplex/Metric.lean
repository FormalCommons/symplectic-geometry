/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Symplectic.ComplexStructure.Basic
public import SymplecticGeometry.Geometry.Symplectic.Manifold.AlmostComplex.Metric.FromTauCeti
public import TauCeti.Geometry.Manifold.Riemannian.AlmostComplex

/-!
# The metric of a compatible pair on a manifold

Let `M` be a manifold modelled on a finite-dimensional space, `σ` a smooth two-form and `J` a
smooth almost complex structure on `M`, in the sense of Tau Ceti (`TauCeti.SmoothTwoForm` and
`TauCeti.SmoothAlmostComplexStructure`). When `σ` is compatible with `J`, the formula
`g_J(u, v) = σ(u, J v)` is a smooth Riemannian metric on `TM`. Conversely, a Riemannian metric `g`
with `g(J u, J v) = g(u, v)` gives the two-form `g(J u, v)`, which is compatible with `J`. For a
fixed `J` these two constructions are inverse to each other.

Both are the tangent-bundle case of the constructions of this library for a complex structure on
a vector bundle, `SymplecticGeometry.Bundle.ContMDiffTwoForm.Compatible.metric` and
`SymplecticGeometry.Bundle.ContMDiffComplexStructure.compatibleForm`, read through the
identifications `SymplecticGeometry.Bundle.ContMDiffTwoForm.tangentEquiv` of two-forms and
`SymplecticGeometry.Bundle.ContMDiffComplexStructure.tangentEquiv` of complex structures.

## Main definitions

* `TauCeti.SmoothTwoForm.Compatible.metric`: the metric `g_J(u, v) = σ(u, J v)` of a compatible
  pair, as a `Bundle.ContMDiffRiemannianMetric` on `TM`.
* `TauCeti.SmoothAlmostComplexStructure.compatibleFormEquiv`: for a fixed `J`, the bijection
  `g ↦ g(J ·, ·)` from the Riemannian metrics compatible with `J` to the two-forms compatible
  with `J`, which are nondegenerate (`TauCeti.SmoothTwoForm.Compatible.isNondegenerate`).

## Main results

* `TauCeti.SmoothTwoForm.Compatible.metric_inner`: `g_J(u, v) = σ(u, J v)`.
* `TauCeti.SmoothTwoForm.Compatible.inner_eq_eval₂`: with `g_J` installed as the
  `RiemannianBundle` metric of `TM`, `⟪u, v⟫ = σ(u, J v)`.
* `TauCeti.SmoothTwoForm.Compatible.metric_inner_apply_apply`: `g_J` is invariant under `J`.
* `TauCeti.SmoothAlmostComplexStructure.compatibleFormEquiv_apply_apply` (or `_apply_eval₂`) and
  `TauCeti.SmoothAlmostComplexStructure.compatibleFormEquiv_symm_apply_inner`: the two
  directions of the bijection are `σ(u, v) = g(J u, v)` and `g(u, v) = σ(u, J v)`.
* `TauCeti.SmoothAlmostComplexStructure.kahlerTwoForm_eq_compatibleFormEquiv`: Tau Ceti's Kähler
  form `TauCeti.SmoothAlmostComplexStructure.kahlerTwoForm` of the ambient `RiemannianBundle`
  metric is the form under the bijection of a compatible metric `g` that agrees with it.

For any `RiemannianBundle` metric on `TM` with `⟪u, v⟫ = σ(u, J v)`, the hypothesis of Tau Ceti's
`TauCeti.SmoothTwoForm.compatible_of_inner_eq`:

* `TauCeti.SmoothAlmostComplexStructure.inner_apply_left_eq_neg`: `J` is skew-adjoint.
* `TauCeti.SmoothTwoForm.val_eq_alternatingFormEquiv_kahlerForm`: at each point, `σ` is the
  Kähler form of `J`.

## Implementation notes

The skew-adjointness uses `TauCeti.SmoothAlmostComplexStructure.inner_apply_left_of_inner_eq`
(`⟪J u, w⟫ = σ(u, w)`), which rests on
`TauCeti.SmoothAlmostComplexStructure.inner_apply_apply_of_inner_eq` (`J` is orthogonal). Tau
Ceti's main branch has made both public, and this file imports them from its copy
`SymplecticGeometry.Geometry.Symplectic.Manifold.AlmostComplex.Metric.FromTauCeti`. The Kähler
form of `J` as a smooth form, `TauCeti.SmoothAlmostComplexStructure.kahlerTwoForm_eq_of_inner_eq`,
is in Tau Ceti's main branch too, and is not copied since nothing here uses it.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §4.1
-/

public section

noncomputable section

open _root_.Bundle
open scoped ContDiff RealInnerProductSpace

namespace TauCeti

open SymplecticGeometry.Bundle

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

namespace SmoothTwoForm

variable {σ : SmoothTwoForm I M} {J : SmoothAlmostComplexStructure I M}

/-- The Riemannian metric `g_J(u, v) = σ(u, J v)` on `TM` of a smooth two-form `σ` compatible
with a smooth almost complex structure `J`. -/
def Compatible.metric (hc : σ.Compatible J) :
    ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x) :=
  (ContMDiffTwoForm.compatible_tangentEquiv_symm_iff.2 hc).metric

/-- The metric of a compatible pair on `TM` is the bundle metric of the pair moved to the tangent
bundle. -/
theorem Compatible.metric_def (hc : σ.Compatible J) :
    hc.metric = (ContMDiffTwoForm.compatible_tangentEquiv_symm_iff.2 hc).metric :=
  (rfl)

/-- The metric of a compatible pair is `g_J(u, v) = σ(u, J v)`. -/
@[simp]
theorem Compatible.metric_inner (hc : σ.Compatible J) (x : M) (u v : TangentSpace I x) :
    hc.metric.inner x u v = σ.eval₂ x u (J x v) := by
  simp [Compatible.metric_def, ContMDiffTwoForm.bilinFormAt_apply]

/-- For a smooth two-form `σ` compatible with a smooth almost complex structure `J`, the inner
product of the metric `g_J` of the pair, installed as the Riemannian metric of `TM`, is
`⟪u, v⟫ = σ(u, J v)`. -/
theorem Compatible.inner_eq_eval₂ (hJ : σ.Compatible J) :
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨hJ.metric.toRiemannianMetric⟩
    ∀ x (u v : TangentSpace I x), ⟪u, v⟫ = σ.eval₂ x u (J x v) := fun x u v ↦ by
  rw [hJ.metric.inner_eq, Compatible.metric_inner]

/-- The metric of a compatible pair `(σ, J)` is invariant under `J`: `g_J(J u, J v) = g_J(u, v)`. -/
theorem Compatible.metric_inner_apply_apply (hc : σ.Compatible J) (x : M)
    (u v : TangentSpace I x) :
    hc.metric.inner x (J x u) (J x v) = hc.metric.inner x u v := by
  simpa using
    (ContMDiffTwoForm.compatible_tangentEquiv_symm_iff.2 hc).metric_inner_apply_apply x u v

end SmoothTwoForm

namespace SmoothAlmostComplexStructure

variable (J : SmoothAlmostComplexStructure I M)

/-- For a fixed smooth almost complex structure `J`, the bijection `g ↦ g(J ·, ·)` from the
Riemannian metrics `g` on `TM` compatible with `J`, `g(J u, J v) = g(u, v)`, to the smooth
two-forms compatible with `J`. Its inverse is `σ ↦ σ(·, J ·)`, the metric
`TauCeti.SmoothTwoForm.Compatible.metric`. The forms compatible with `J` are nondegenerate
(`TauCeti.SmoothTwoForm.Compatible.isNondegenerate`). -/
def compatibleFormEquiv :
    {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x) //
        ∀ x u v, g.inner x (J x u) (J x v) = g.inner x u v} ≃
      {σ : SmoothTwoForm I M // σ.Compatible J} where
  toFun g := ⟨ContMDiffTwoForm.tangentEquiv <| ContMDiffComplexStructure.compatibleForm g.val <|
      ContMDiffComplexStructure.tangentEquiv.symm (J.toContMDiff ⊤), by
    rw [← ContMDiffTwoForm.compatible_tangentEquiv_symm_iff, LinearEquiv.symm_apply_apply]
    exact ContMDiffComplexStructure.compatible_compatibleForm _ _⟩
  invFun σ := ⟨σ.property.metric, σ.property.metric_inner_apply_apply⟩
  left_inv g := Subtype.ext <| by
    have hg : ∀ x u v, g.val.inner x (ContMDiffComplexStructure.tangentEquiv.symm
        (J.toContMDiff ⊤) x u) (ContMDiffComplexStructure.tangentEquiv.symm
        (J.toContMDiff ⊤) x v) = g.val.inner x u v := by
      simpa using g.property
    dsimp only
    refine (SmoothTwoForm.Compatible.metric_def _).trans ?_
    simp only [LinearEquiv.symm_apply_apply]
    exact ContMDiffComplexStructure.metric_compatible_compatibleForm hg
  right_inv σ := Subtype.ext <|
    (congrArg ContMDiffTwoForm.tangentEquiv
      (ContMDiffTwoForm.Compatible.compatibleForm_metric _)).trans
        (LinearEquiv.apply_symm_apply _ _)

/-- The form of a metric `g` compatible with `J` is the two-form
`SymplecticGeometry.Bundle.ContMDiffComplexStructure.compatibleForm` of `g` and `J`, read on the
tangent bundle. -/
theorem compatibleFormEquiv_apply
    (g : {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x) //
      ∀ x u v, g.inner x (J x u) (J x v) = g.inner x u v}) :
    (J.compatibleFormEquiv g).val = ContMDiffTwoForm.tangentEquiv
      (ContMDiffComplexStructure.compatibleForm g.val
        (ContMDiffComplexStructure.tangentEquiv.symm (J.toContMDiff ⊤))) :=
  (rfl)

/-- The form of a metric `g` compatible with `J` is `σ(u, v) = g(J u, v)`. -/
@[simp]
theorem compatibleFormEquiv_apply_apply
    (g : {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x) //
      ∀ x u v, g.inner x (J x u) (J x v) = g.inner x u v})
    (x : M) (u v : TangentSpace I x) :
    (J.compatibleFormEquiv g).val.val x ![u, v] = g.val.inner x (J x u) v := by
  rw [compatibleFormEquiv_apply, ContMDiffTwoForm.tangentEquiv_apply,
    ContMDiffComplexStructure.compatibleForm_apply_of_invariant (by simpa using g.property)]
  simp

/-- The form of a metric `g` compatible with `J` is `σ(u, v) = g(J u, v)`, through Tau Ceti's
`TauCeti.SmoothBundleForm.eval₂`. -/
theorem compatibleFormEquiv_apply_eval₂
    (g : {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x) //
      ∀ x u v, g.inner x (J x u) (J x v) = g.inner x u v})
    (x : M) (u v : TangentSpace I x) :
    (J.compatibleFormEquiv g).val.eval₂ x u v = g.val.inner x (J x u) v := by
  simp

/-- The metric of a form compatible with `J` is `TauCeti.SmoothTwoForm.Compatible.metric`. -/
@[simp]
theorem compatibleFormEquiv_symm_apply (σ : {σ : SmoothTwoForm I M // σ.Compatible J}) :
    (J.compatibleFormEquiv.symm σ).val = σ.property.metric :=
  (rfl)

/-- The metric of a form `σ` compatible with `J` is `g(u, v) = σ(u, J v)`. -/
theorem compatibleFormEquiv_symm_apply_inner (σ : {σ : SmoothTwoForm I M // σ.Compatible J})
    (x : M) (u v : TangentSpace I x) :
    (J.compatibleFormEquiv.symm σ).val.inner x u v = σ.val.eval₂ x u (J x v) := by
  rw [compatibleFormEquiv_symm_apply, SmoothTwoForm.Compatible.metric_inner]

/-- Tau Ceti's Kähler form `TauCeti.SmoothAlmostComplexStructure.kahlerTwoForm`, built from the
ambient `RiemannianBundle` metric on `TM`, is the form under `compatibleFormEquiv` of any metric
`g` compatible with `J` that agrees with the ambient one: both are `σ(u, v) = g(J u, v)`. -/
theorem kahlerTwoForm_eq_compatibleFormEquiv [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    (hJ : ∀ (x : M) (u w : TangentSpace I x), ⟪J x u, J x w⟫ = ⟪u, w⟫)
    (g : {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x) //
      ∀ x u v, g.inner x (J x u) (J x v) = g.inner x u v})
    (hg : ∀ (x : M) (u v : TangentSpace I x), g.val.inner x u v = ⟪u, v⟫) :
    J.kahlerTwoForm hJ = (J.compatibleFormEquiv g).val := by
  refine SmoothBundleForm.ext_eval₂ fun x u w ↦ ?_
  rw [compatibleFormEquiv_apply_eval₂, SmoothBundleForm.eval₂_apply, kahlerTwoForm_apply_two, hg]

end SmoothAlmostComplexStructure

/-! ### Consequences of `⟪u, v⟫ = σ(u, J v)` -/

section InnerEq

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)] {σ : SmoothTwoForm I M}
  {J : SmoothAlmostComplexStructure I M}

namespace SmoothAlmostComplexStructure

omit [FiniteDimensional ℝ E] in
/-- If `⟪u, v⟫ = σ(u, J v)`, then `J` is skew-adjoint: `⟪J u, w⟫ = -⟪u, J w⟫`. -/
theorem inner_apply_left_eq_neg (hJ : ∀ x u v, ⟪u, v⟫ = σ.eval₂ x u (J x v)) (x : M)
    (u w : TangentSpace I x) : ⟪J x u, w⟫ = -⟪u, J x w⟫ := by
  rw [inner_apply_left_of_inner_eq hJ, hJ, apply_apply, SmoothBundleForm.eval₂_neg_right,
    _root_.neg_neg]

end SmoothAlmostComplexStructure

namespace SmoothTwoForm

/-- If `⟪u, v⟫ = σ(u, J v)`, then at each point `x` the form `σ` is the Kähler form
`(u, w) ↦ ⟪J u, w⟫` of the linear complex structure `J x`: the alternating form of its Kähler
two-vector `TauCeti.AlmostComplexStructure.kahlerForm`. -/
theorem val_eq_alternatingFormEquiv_kahlerForm (hJ : ∀ x u v, ⟪u, v⟫ = σ.eval₂ x u (J x v))
    (x : M) :
    σ.val x =
      (letI : FiniteDimensional ℝ (TangentSpace I x) :=
        VectorBundle.finiteDimensional ℝ E (TangentSpace I) x
       alternatingFormEquiv (TangentSpace I x) 2 (J.almostComplexStructureAt x).kahlerForm) := by
  let _ : FiniteDimensional ℝ (TangentSpace I x) :=
    VectorBundle.finiteDimensional ℝ E (TangentSpace I) x
  rw [AlmostComplexStructure.kahlerForm_eq_of_inner_eq
      (F := (alternatingFormEquiv _ 2).symm (σ.val x))
      fun u v ↦ by rw [inner_alternatingFormEquiv_symm_ιMulti, hJ, SmoothBundleForm.eval₂_apply,
        SmoothAlmostComplexStructure.almostComplexStructureAt_apply],
    LinearEquiv.apply_symm_apply]

end SmoothTwoForm

end InnerEq

end TauCeti

end
