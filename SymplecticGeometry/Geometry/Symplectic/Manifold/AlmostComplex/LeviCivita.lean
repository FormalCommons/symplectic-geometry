/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.CovariantDerivative.TwoForm
public import SymplecticGeometry.Geometry.Symplectic.Manifold.AlmostComplex.Covariant
public import SymplecticGeometry.Geometry.Symplectic.Manifold.AlmostComplex.Metric
public import TauCeti.Geometry.Manifold.DifferentialForm.Closed
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric.Hom
import SymplecticGeometry.LinearAlgebra.ComplexStructure.Trilinear

/-!
# The Levi-Civita derivative of a compatible almost complex structure

Let `σ` be a smooth two-form and `J` a smooth almost complex structure on a manifold `M`, and
let `⟪·, ·⟫` be a Riemannian metric on `TM` with `⟪u, v⟫ = σ(u, J v)`. For a metric connection
`∇` on `TM` this file proves the identities of [McDuffSalamon2017], Lemma 4.1.14, for the
covariant derivative `∇J` of `J` (Tau Ceti's induced connection `cov.hom cov J.toEndomorphism`):

* `⟪(∇_u J) v, w⟫ + ⟪v, (∇_u J) w⟫ = 0`;
* `(∇_u σ)(v, w) = ⟪(∇_u J) v, w⟫`;
* if `∇` is also torsion free, `dσ(u, v, w)` is the cyclic sum of `⟪(∇_u J) v, w⟫`;
* if moreover `σ` is closed, `∇_{J v} J = -J ∘ ∇_v J`.

Together with the anticommutation `(∇_v J) ∘ J + J ∘ (∇_v J) = 0`
(`TauCeti.SmoothAlmostComplexStructure.hom_toEndomorphism_comp_add_comp_hom`), these give the
statement for a two-form `σ` compatible with `J` and the Levi-Civita connection of the metric
`g_J = σ(·, J ·)`.

## Main results

In the namespace `TauCeti.SmoothAlmostComplexStructure`, for a metric with
`⟪u, v⟫ = σ(u, J v)`:

* `inner_apply_left_eq_eval₂` and `inner_apply_left_eq_neg`: `⟪J u, w⟫ = σ(u, w)` and
  `⟪J u, w⟫ = -⟪u, J w⟫`.
* `inner_hom_apply_apply_eq`: `⟪(∇_u J) (J v), w⟫ = ⟪(∇_u J) v, J w⟫`.
* `inner_hom_apply_eq_neg`: `∇_u J` is skew-adjoint, for a metric connection.
* `hom_hom_flat_apply_eq_inner`: `(∇_u σ)(v, w) = ⟪(∇_u J) v, w⟫`, for a metric connection.
* `mextDeriv_apply_eq_inner`: `dσ` is the cyclic sum of `⟪(∇_u J) v, w⟫`, for a Levi-Civita
  connection.
* `hom_apply_eq_neg_comp`: `∇_{J v} J = -J ∘ ∇_v J` for a Levi-Civita connection and a closed
  `σ`.

In the namespace `TauCeti.SmoothTwoForm`:

* `Compatible.inner_eq_eval₂`: the metric `g_J` of a compatible pair, installed on `TM`, has
  `⟪u, v⟫ = σ(u, J v)`.
* `Compatible.leviCivita_hom_comp_add_and_inner_add_and_mextDeriv_and_apply`: the four
  identities for a compatible pair and the Levi-Civita connection of `g_J`.

## Implementation notes

The proofs follow the first, coordinate-free, proof of [McDuffSalamon2017], Lemma 4.1.14. The
skew-adjointness of `∇_u J` is Tau Ceti's
`CovariantDerivative.IsMetricCompatible.inner_hom_eq_neg` applied to `J`. The formula for `dσ`
comes from `CovariantDerivative.mextDeriv_smoothTwoForm_of_torsion_eq_zero`, and the last
identity from the linear algebra of `LinearMap.apply_left_eq_apply_right_of_cyclic`, applied to
the trilinear form `(u, v, w) ↦ ⟪(∇_u J) v, w⟫`.

The proof of `inner_apply_left_eq_eval₂` uses the rewrites of Tau Ceti's private
`TauCeti.inner_apply_apply_of_inner_eq` (in
`TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Metric`), which makes the same use of
`⟪u, v⟫ = σ(u, J v)`, `J² = -1` and the skew-symmetry of `σ`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  Lemma 4.1.14, equations (4.1.9)–(4.1.12).
* [V. Apostolov and T. Drăghici, *The curvature and the integrability of almost-Kähler manifolds:
  a survey*][ApostolovDraghici2003], §3.3, equation (7).
-/

public section

noncomputable section

open Bundle FiberBundle
open scoped ContDiff Manifold RealInnerProductSpace

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

namespace SmoothAlmostComplexStructure

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {σ : SmoothTwoForm I M} {J : SmoothAlmostComplexStructure I M}

omit [FiniteDimensional ℝ E] in
/-- If `⟪u, v⟫ = σ(u, J v)`, then the metric represents `σ` through `J`: `⟪J u, w⟫ = σ(u, w)`. -/
theorem inner_apply_left_eq_eval₂ (hJ : ∀ x u v, ⟪u, v⟫ = σ.eval₂ x u (J x v)) (x : M)
    (u w : TangentSpace I x) : ⟪J x u, w⟫ = σ.eval₂ x u w := by
  rw [real_inner_comm, hJ, apply_apply, SmoothBundleForm.eval₂_neg_right,
    ← SmoothBundleForm.eval₂_swap]

omit [FiniteDimensional ℝ E] in
/-- If `⟪u, v⟫ = σ(u, J v)`, then `J` is skew-adjoint: `⟪J u, w⟫ = -⟪u, J w⟫`. -/
theorem inner_apply_left_eq_neg (hJ : ∀ x u v, ⟪u, v⟫ = σ.eval₂ x u (J x v)) (x : M)
    (u w : TangentSpace I x) : ⟪J x u, w⟫ = -⟪u, J x w⟫ := by
  rw [inner_apply_left_eq_eval₂ hJ, hJ, apply_apply, SmoothBundleForm.eval₂_neg_right,
    _root_.neg_neg]

variable [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}

omit [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)] in
/-- If `⟪u, v⟫ = σ(u, J v)`, then `J` passes from one argument of `⟪(∇_u J) ·, ·⟫` to the other:
`⟪(∇_u J) (J v), w⟫ = ⟪(∇_u J) v, J w⟫`. -/
theorem inner_hom_apply_apply_eq (hJ : ∀ x u v, ⟪u, v⟫ = σ.eval₂ x u (J x v)) (x : M)
    (u v w : TangentSpace I x) :
    ⟪cov.hom cov J.toEndomorphism x u (J x v), w⟫ =
      ⟪cov.hom cov J.toEndomorphism x u v, J x w⟫ := by
  rw [← _root_.neg_neg (cov.hom cov J.toEndomorphism x u (J x v)),
    ← J.apply_hom_toEndomorphism_apply cov, inner_neg_left, inner_apply_left_eq_neg hJ,
    _root_.neg_neg]

/-- If `⟪u, v⟫ = σ(u, J v)` and `∇` is a metric connection, then `∇_u J` is skew-adjoint:
`⟪(∇_u J) v, w⟫ = -⟪v, (∇_u J) w⟫`. -/
theorem inner_hom_apply_eq_neg (hJ : ∀ x u v, ⟪u, v⟫ = σ.eval₂ x u (J x v))
    (hcov : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    (x : M) (u v w : TangentSpace I x) :
    ⟪cov.hom cov J.toEndomorphism x u v, w⟫ = -⟪v, cov.hom cov J.toEndomorphism x u w⟫ :=
  hcov.inner_hom_eq_neg (J.mdifferentiableAt_toEndomorphism x)
    (Filter.Eventually.of_forall fun y ↦ inner_apply_left_eq_neg hJ y) u v w

/-- If `⟪u, v⟫ = σ(u, J v)` and `∇` is a metric connection, then the covariant derivative of `σ`
is `(∇_u σ)(v, w) = ⟪(∇_u J) v, w⟫`. -/
theorem hom_hom_flat_apply_eq_inner (hJ : ∀ x u v, ⟪u, v⟫ = σ.eval₂ x u (J x v))
    (hcov : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    (x : M) (u v w : TangentSpace I x) :
    cov.hom (cov.hom (CovariantDerivative.trivial ℝ)) σ.flat x u v w =
      ⟪cov.hom cov J.toEndomorphism x u v, w⟫ := by
  have hV := mdifferentiableAt_extend I E v
  have hW := mdifferentiableAt_extend I E w
  have hJx := J.mdifferentiableAt_toEndomorphism x
  have hσ := σ.contMDiff_flat.mdifferentiableAt (x := x) (by simp)
  have hflat (y : M) (a b : TangentSpace I y) : σ.flat y a b = ⟪J y a, b⟫ := by
    rw [SmoothTwoForm.flat_apply, inner_apply_left_eq_eval₂ hJ]
  have h₁ := cov.hom_hom_apply cov (CovariantDerivative.trivial ℝ) hσ hV hW u
  have h₂ := cov.hom_apply cov hJx hV u
  have h₃ := hcov.mvfderiv_inner_eq (fun _ ↦ u) (hJx.clm_bundle_apply hV) hW
  simp only [extend_apply_self] at h₁ h₂ h₃
  rw [h₁, h₂, CovariantDerivative.trivial_apply]
  simp only [hflat]
  rw [h₃, inner_sub_left]
  abel

/-- If `⟪u, v⟫ = σ(u, J v)` and `∇` is a Levi-Civita connection, then the exterior derivative
of `σ` is the cyclic sum `dσ(u, v, w) = ⟪(∇_u J) v, w⟫ + ⟪(∇_v J) w, u⟫ + ⟪(∇_w J) u, v⟫`. -/
theorem mextDeriv_apply_eq_inner (hJ : ∀ x u v, ⟪u, v⟫ = σ.eval₂ x u (J x v))
    (hcov : cov.IsLeviCivitaConnection) (x : M) (u v w : TangentSpace I x) :
    mextDeriv σ.val x ![u, v, w] =
      ⟪cov.hom cov J.toEndomorphism x u v, w⟫ + ⟪cov.hom cov J.toEndomorphism x v w, u⟫ +
        ⟪cov.hom cov J.toEndomorphism x w u, v⟫ := by
  rw [cov.mextDeriv_smoothTwoForm_of_torsion_eq_zero σ (congr_fun hcov.torsion x),
    hom_hom_flat_apply_eq_inner hJ hcov.isMetricCompatible,
    hom_hom_flat_apply_eq_inner hJ hcov.isMetricCompatible,
    hom_hom_flat_apply_eq_inner hJ hcov.isMetricCompatible]

/-- If `⟪u, v⟫ = σ(u, J v)`, `∇` is a Levi-Civita connection and `σ` is closed, then
`v ↦ ∇_v J` is anti-linear for the complex structure `A ↦ J ∘ A`: `∇_{J v} J = -J ∘ ∇_v J`. -/
theorem hom_apply_eq_neg_comp (hJ : ∀ x u v, ⟪u, v⟫ = σ.eval₂ x u (J x v))
    (hcov : cov.IsLeviCivitaConnection) (hσ : σ.IsClosed) (x : M) (v : TangentSpace I x) :
    cov.hom cov J.toEndomorphism x (J x v) =
      -(J.toEndomorphism x).comp (cov.hom cov J.toEndomorphism x v) := by
  set D := cov.hom cov J.toEndomorphism x
  -- The trilinear form `α(u, v, w) = ⟪(∇_u J) v, w⟫`.
  let α : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ (fun u a ↦ innerₗ _ (D u a)) (fun _ _ _ ↦ by simp) (fun _ _ _ ↦ by simp)
      (fun _ _ _ ↦ by simp) (fun _ _ _ ↦ by simp)
  have hj : (J.toEndomorphism x : TangentSpace I x →ₗ[ℝ] TangentSpace I x) ∘ₗ
      (J.toEndomorphism x : TangentSpace I x →ₗ[ℝ] TangentSpace I x) = -LinearMap.id :=
    LinearMap.ext fun a ↦ J.apply_apply x a
  have hcyc (u a b : TangentSpace I x) : ⟪D u a, b⟫ + ⟪D a b, u⟫ + ⟪D b u, a⟫ = 0 := by
    rw [← mextDeriv_apply_eq_inner hJ hcov, σ.isClosed_iff_forall_mextDeriv_apply_eq_zero.1 hσ x]
    simp
  have h := LinearMap.apply_left_eq_apply_right_of_cyclic (α := α) hj
    (fun u a b ↦ inner_hom_apply_apply_eq hJ x u a b) (fun u a b ↦ hcyc u a b) v
  ext w : 1
  refine ext_inner_right ℝ fun z ↦ ?_
  have hz := h w z
  simp only [α, LinearMap.mk₂_apply, innerₗ_apply_apply, ContinuousLinearMap.coe_coe] at hz
  rw [hz, _root_.neg_apply, ContinuousLinearMap.comp_apply, inner_neg_left,
    inner_apply_left_eq_neg hJ, _root_.neg_neg]

end SmoothAlmostComplexStructure

namespace SmoothTwoForm

variable {σ : SmoothTwoForm I M} {J : SmoothAlmostComplexStructure I M}

/-- For a smooth two-form `σ` compatible with a smooth almost complex structure `J`, the inner
product of the metric `g_J` of the pair, installed as the Riemannian metric of `TM`, is
`⟪u, v⟫ = σ(u, J v)`. -/
theorem Compatible.inner_eq_eval₂ (hJ : σ.Compatible J) :
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨hJ.metric.toRiemannianMetric⟩
    ∀ x (u v : TangentSpace I x), ⟪u, v⟫ = σ.eval₂ x u (J x v) := fun x u v ↦ by
  rw [hJ.metric.inner_eq, Compatible.metric_inner]

/-- Let `σ` be a smooth two-form compatible with a smooth almost complex structure `J`, and let
`∇` be the Levi-Civita connection of the metric `g_J(u, v) = σ(u, J v)`. Then for all
`u v w : T_x M`:
* `(∇_v J) ∘ J + J ∘ (∇_v J) = 0`;
* `g_J((∇_u J) v, w) + g_J(v, (∇_u J) w) = 0`;
* `dσ(u, v, w) = g_J((∇_u J) v, w) + g_J((∇_v J) w, u) + g_J((∇_w J) u, v)`;
* if `σ` is closed, `∇_{J v} J = -J ∘ ∇_v J`.

Milestone: *Levi-Civita derivative of a compatible almost complex structure*. -/
theorem Compatible.leviCivita_hom_comp_add_and_inner_add_and_mextDeriv_and_apply
    (hJ : σ.Compatible J) :
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨hJ.metric.toRiemannianMetric⟩
    ∀ x (u v w : TangentSpace I x),
      ((CovariantDerivative.leviCivitaConnection I M).hom
            (CovariantDerivative.leviCivitaConnection I M) J.toEndomorphism x v).comp
          (J.toEndomorphism x) +
        (J.toEndomorphism x).comp ((CovariantDerivative.leviCivitaConnection I M).hom
            (CovariantDerivative.leviCivitaConnection I M) J.toEndomorphism x v) = 0 ∧
      ⟪(CovariantDerivative.leviCivitaConnection I M).hom
            (CovariantDerivative.leviCivitaConnection I M) J.toEndomorphism x u v, w⟫ +
          ⟪v, (CovariantDerivative.leviCivitaConnection I M).hom
            (CovariantDerivative.leviCivitaConnection I M) J.toEndomorphism x u w⟫ = 0 ∧
      mextDeriv σ.val x ![u, v, w] =
        ⟪(CovariantDerivative.leviCivitaConnection I M).hom
            (CovariantDerivative.leviCivitaConnection I M) J.toEndomorphism x u v, w⟫ +
          ⟪(CovariantDerivative.leviCivitaConnection I M).hom
            (CovariantDerivative.leviCivitaConnection I M) J.toEndomorphism x v w, u⟫ +
          ⟪(CovariantDerivative.leviCivitaConnection I M).hom
            (CovariantDerivative.leviCivitaConnection I M) J.toEndomorphism x w u, v⟫ ∧
      (σ.IsClosed →
        (CovariantDerivative.leviCivitaConnection I M).hom
            (CovariantDerivative.leviCivitaConnection I M) J.toEndomorphism x (J x v) =
          -(J.toEndomorphism x).comp ((CovariantDerivative.leviCivitaConnection I M).hom
            (CovariantDerivative.leviCivitaConnection I M) J.toEndomorphism x v)) := by
  let : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨hJ.metric.toRiemannianMetric⟩
  have hg := hJ.inner_eq_eval₂
  have hL := CovariantDerivative.isLeviCivitaConnection_leviCivitaConnection I (M := M)
  intro x u v w
  refine ⟨J.hom_toEndomorphism_comp_add_comp_hom _ x v, ?_,
    SmoothAlmostComplexStructure.mextDeriv_apply_eq_inner hg hL x u v w,
    fun hσ ↦ SmoothAlmostComplexStructure.hom_apply_eq_neg_comp hg hL hσ x v⟩
  rw [SmoothAlmostComplexStructure.inner_hom_apply_eq_neg hg hL.isMetricCompatible, neg_add_cancel]

end SmoothTwoForm

end TauCeti

end
