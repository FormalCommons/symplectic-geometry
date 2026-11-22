/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Symplectic.ComplexStructure.Basic

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
* `TauCeti.SmoothAlmostComplexStructure.compatibleFormEquiv_apply_eval₂` and
  `TauCeti.SmoothAlmostComplexStructure.compatibleFormEquiv_symm_apply_inner`: the two
  directions of the bijection are `σ(u, v) = g(J u, v)` and `g(u, v) = σ(u, J v)`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §4.1
-/

public section

noncomputable section

open _root_.Bundle
open scoped ContDiff

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

/-- The metric of a compatible pair is `g_J(u, v) = σ(u, J v)`. -/
@[simp]
theorem Compatible.metric_inner (hc : σ.Compatible J) (x : M) (u v : TangentSpace I x) :
    hc.metric.inner x u v = σ.eval₂ x u (J x v) := by
  rw [Compatible.metric, ContMDiffTwoForm.Compatible.metric_inner,
    ContMDiffTwoForm.bilinFormAt_apply, ContMDiffTwoForm.tangentEquiv_symm_apply,
    SmoothBundleForm.eval₂_apply, ContMDiffComplexStructure.tangentEquiv_symm_apply,
    SmoothAlmostComplexStructure.toContMDiff_apply]

end SmoothTwoForm

namespace SmoothAlmostComplexStructure

variable (J : SmoothAlmostComplexStructure I M)

/-- The two-form `g(J u, v)` of a Riemannian metric `g` compatible with `J`, read on the tangent
bundle from `SymplecticGeometry.Bundle.ContMDiffComplexStructure.compatibleForm`. -/
private def formOfMetric (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) :
    SmoothTwoForm I M :=
  ContMDiffTwoForm.tangentEquiv <| ContMDiffComplexStructure.compatibleForm g <|
    ContMDiffComplexStructure.tangentEquiv.symm (J.toContMDiff ⊤)

private theorem formOfMetric_eval₂
    {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
    (hg : ∀ x u v, g.inner x (J x u) (J x v) = g.inner x u v) (x : M)
    (u v : TangentSpace I x) :
    (J.formOfMetric g).eval₂ x u v = g.inner x (J x u) v := by
  have h := hg x u (J x v)
  rw [J.apply_apply, map_neg] at h
  simp only [formOfMetric, SmoothBundleForm.eval₂_apply, ContMDiffTwoForm.tangentEquiv_apply,
    ContMDiffComplexStructure.compatibleForm_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, ContMDiffComplexStructure.tangentEquiv_symm_apply,
    toContMDiff_apply]
  beta_reduce at h ⊢
  linarith

/-- For a fixed smooth almost complex structure `J`, the bijection `g ↦ g(J ·, ·)` from the
Riemannian metrics `g` on `TM` compatible with `J`, `g(J u, J v) = g(u, v)`, to the smooth
two-forms compatible with `J`. Its inverse is `σ ↦ σ(·, J ·)`, the metric
`TauCeti.SmoothTwoForm.Compatible.metric`. The forms compatible with `J` are nondegenerate
(`TauCeti.SmoothTwoForm.Compatible.isNondegenerate`). -/
def compatibleFormEquiv :
    {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x) //
        ∀ x u v, g.inner x (J x u) (J x v) = g.inner x u v} ≃
      {σ : SmoothTwoForm I M // σ.Compatible J} where
  toFun g := ⟨J.formOfMetric g.val, by
    rw [formOfMetric, ← ContMDiffTwoForm.compatible_tangentEquiv_symm_iff,
      LinearEquiv.symm_apply_apply]
    exact ContMDiffComplexStructure.compatible_compatibleForm _ _⟩
  invFun σ := ⟨σ.property.metric, fun x u v ↦ by
    rw [SmoothTwoForm.Compatible.metric_inner, SmoothTwoForm.Compatible.metric_inner,
      ← σ.property.invariant.apply x u (J x v)]⟩
  left_inv g := Subtype.ext <| ContMDiffRiemannianMetric.ext fun x u v ↦ by
    rw [SmoothTwoForm.Compatible.metric_inner, J.formOfMetric_eval₂ g.property]
    exact g.property x u v
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
theorem compatibleFormEquiv_apply_eval₂
    (g : {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x) //
      ∀ x u v, g.inner x (J x u) (J x v) = g.inner x u v})
    (x : M) (u v : TangentSpace I x) :
    (J.compatibleFormEquiv g).val.eval₂ x u v = g.val.inner x (J x u) v :=
  J.formOfMetric_eval₂ g.property x u v

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

end SmoothAlmostComplexStructure

end TauCeti

end
