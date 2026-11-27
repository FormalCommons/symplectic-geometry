/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Riemannian.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.CauchyRiemann.OneZeroPart
import SymplecticGeometry.Analysis.Normed.Operator.ComplexLinearPart
import SymplecticGeometry.Geometry.Manifold.MFDeriv.Log
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric.Norm

/-!
# The `(1,0)` and `(0,1)` parts of the derivative at a critical point of the norm

Let `V` be a complex line bundle whose fibres carry a real inner product, the real part of a
Hermitian metric, and `∇` a connection on `V` compatible with it (Mathlib's
`CovariantDerivative.IsMetricCompatible`). For a section `σ`, Tau Ceti's
`CovariantDerivative.IsMetricCompatible.mvfderiv_norm_sq` gives `d|σ|²(v) = 2 ⟪∇_v σ, σ⟫`. So at a
critical point `x` of `|σ|²` every value of `∇σ(x)` is orthogonal to `σ x`, and if `σ x ≠ 0`,
`norm_add_I_smul_eq_norm_sub_I_smul` shows that, for an almost complex structure `j` on the base,
the `(1,0)`-part and the `(0,1)`-part of `∇σ(x)` have values of equal norms
(`CovariantDerivative.IsMetricCompatible.norm_oneZeroPart_apply_eq_norm_zeroOnePart_apply`), and
equal operator norms for any metric on the tangent bundle
(`CovariantDerivative.IsMetricCompatible.norm_oneZeroPart_eq_norm_zeroOnePart`). Away from the
zeros of `σ`, the critical points of `|σ|²` are those of `log |σ|²`
(`mvfderiv_log_comp_eq_zero_iff`),
which gives the same equality there
(`CovariantDerivative.IsMetricCompatible.norm_oneZeroPart_eq_norm_zeroOnePart_of_log`).

This is the first step of the lower bound on `|s|` at the critical points of `log |s|²` for
asymptotically holomorphic sections in [Donaldson1996].

## References

* [S. K. Donaldson, *Symplectic submanifolds and almost-complex geometry*][Donaldson1996].
-/

public section

open Bundle
open scoped Manifold ContDiff RealInnerProductSpace

namespace CovariantDerivative.IsMetricCompatible

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)] [∀ x, NormedSpace ℂ (V x)]
  [∀ x, IsScalarTower ℝ ℂ (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle 1 F V I] [IsContMDiffRiemannianBundle I 1 F V]
  {cov : CovariantDerivative I F V} {σ : Π x : M, V x} {x : M}
  (j : TauCeti.SmoothAlmostComplexStructure I M)

/-- For a metric connection on a bundle of complex lines, at a critical point `x` of `|σ|²` where
`σ x ≠ 0`, the `(1,0)`-part and the `(0,1)`-part of `∇σ(x)` have values of equal norms. -/
theorem norm_oneZeroPart_apply_eq_norm_zeroOnePart_apply (hcov : cov.IsMetricCompatible)
    (hV : Module.finrank ℂ (V x) = 1) (hσ : MDiffAt (T% σ) x) (hσx : σ x ≠ 0)
    (hcrit : mvfderiv I (fun y ↦ ‖σ y‖ ^ 2) x = 0) (v : TangentSpace I x) :
    ‖j.oneZeroPart (cov σ x) v‖ = ‖j.zeroOnePart (cov σ x) v‖ := by
  have h (w : TangentSpace I x) : ⟪cov σ x w, σ x⟫ = 0 := by
    have := hcov.mvfderiv_norm_sq hσ w
    rw [hcrit, zero_apply] at this
    linarith
  rw [j.oneZeroPart_apply, j.zeroOnePart_apply, norm_smul, norm_smul,
    norm_add_I_smul_eq_norm_sub_I_smul hV hσx (h v) (h _)]

/-- For a metric connection on a bundle of complex lines, at a critical point `x` of `|σ|²` where
`σ x ≠ 0`, the `(1,0)`-part and the `(0,1)`-part of `∇σ(x)` have equal operator norms, for any
metric on the tangent bundle. -/
theorem norm_oneZeroPart_eq_norm_zeroOnePart [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    (hcov : cov.IsMetricCompatible) (hV : Module.finrank ℂ (V x) = 1) (hσ : MDiffAt (T% σ) x)
    (hσx : σ x ≠ 0) (hcrit : mvfderiv I (fun y ↦ ‖σ y‖ ^ 2) x = 0) :
    ‖j.oneZeroPart (cov σ x)‖ = ‖j.zeroOnePart (cov σ x)‖ :=
  ContinuousLinearMap.opNorm_ext _ _
    (hcov.norm_oneZeroPart_apply_eq_norm_zeroOnePart_apply j hV hσ hσx hcrit)

/-- For a metric connection on a bundle of complex lines, at a critical point `x` of `log |σ|²`
where `σ x ≠ 0`, the `(1,0)`-part and the `(0,1)`-part of `∇σ(x)` have equal operator norms, for
any metric on the tangent bundle. -/
theorem norm_oneZeroPart_eq_norm_zeroOnePart_of_log
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)] (hcov : cov.IsMetricCompatible)
    (hV : Module.finrank ℂ (V x) = 1) (hσ : MDiffAt (T% σ) x) (hσx : σ x ≠ 0)
    (hcrit : mvfderiv I (fun y ↦ Real.log (‖σ y‖ ^ 2)) x = 0) :
    ‖j.oneZeroPart (cov σ x)‖ = ‖j.zeroOnePart (cov σ x)‖ := by
  have hd : MDiffAt (fun y ↦ ‖σ y‖ ^ 2) x := by
    simpa only [real_inner_self_eq_norm_sq] using hσ.inner_bundle hσ
  exact hcov.norm_oneZeroPart_eq_norm_zeroOnePart j hV hσ hσx
    ((mvfderiv_log_comp_eq_zero_iff hd (by positivity)).1 hcrit)

end CovariantDerivative.IsMetricCompatible

end
