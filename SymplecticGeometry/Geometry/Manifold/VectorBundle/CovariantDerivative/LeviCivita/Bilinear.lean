/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Basic
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Metric
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Basic
import TauCeti.Geometry.Manifold.MFDeriv.ContinuousLinearMap
import TauCeti.Geometry.Manifold.MFDeriv.Curve
import TauCeti.Geometry.Manifold.VectorField.LieBracket
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# The Gauss formula for a map isometric for a bilinear form

Let `f : M → F` be a `C²` map from a Riemannian manifold to a real normed space, and `B` a
symmetric continuous bilinear form on `F` such that `⟪v, w⟫ = B (df v) (df w)` for tangent vectors
`v w` of `M`. The form `B` need not be positive, nor nondegenerate on `F`: only its restriction to
the images of the differentials of `f` is an inner product. For a vector field `Y` on `M`,
`df Y : y ↦ df_y (Y y)` is an `F`-valued function on `M`, and `D_X (df Y)` is its derivative along
a vector field `X`. The Levi-Civita connection `∇` of `M` then satisfies

`⟪∇_X Y, w⟫ = B (D_X (df Y)) (df w)` for every tangent vector `w`,

and the same holds for the covariant derivative of a field along a curve. This is the Gauss
formula of Tau Ceti's
`CovariantDerivative.IsLeviCivitaConnection.inner_apply_eq_inner_mvfderiv` and
`CovariantDerivative.IsLeviCivitaConnection.inner_alongCurve_eq_inner`, for an ambient form that
is not an inner product, such as the trace form `(X, Y) ↦ ½ tr (X Y)` on endomorphisms, which is
positive only on self-adjoint maps. The proofs are Tau Ceti's, with the product rule for `B`
(from `TauCeti.mvfderiv_clm_apply` and `ContinuousLinearMap.hasDerivAt_of_bilinear`) in place of
the product rule for the inner product.

## Main results

* `CovariantDerivative.IsLeviCivitaConnection.inner_apply_eq_bilin_mvfderiv`: the Gauss formula
  for vector fields.
* `CovariantDerivative.IsLeviCivitaConnection.inner_alongCurve_eq_bilin`: the Gauss formula for
  fields along a curve.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Theorem 8.2 (the Gauss formula) and Theorem 5.10 (the Koszul formula).
-/

public section

open Bundle FiberBundle Manifold VectorField
open scoped ContDiff Manifold

namespace CovariantDerivative

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsManifold I 2 M]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  {cov : CovariantDerivative I E (fun x : M ↦ TangentSpace I x)}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {f : M → F} {B : F →L[ℝ] F →L[ℝ] ℝ}

/-- **The Gauss formula for a bilinear form.** Let `f : M → F` be a `C²` map into a real normed
space, and `B` a symmetric continuous bilinear form on `F` for which the differential of `f`
preserves inner products, `⟪v, w⟫ = B (df v) (df w)`. Then a Levi-Civita connection `∇`
satisfies `⟪∇_X Y, w⟫ = B (D_X (df Y)) (df w)`, where `D_X (df Y)` is the derivative along `X`
of `df Y : y ↦ df_y (Y y)`. -/
theorem IsLeviCivitaConnection.inner_apply_eq_bilin_mvfderiv (h : cov.IsLeviCivitaConnection)
    {x : M} (hf : ContMDiffAt I 𝓘(ℝ, F) 2 f x) (hB : ∀ u v, B u v = B v u)
    (hg : ∀ y (v w : TangentSpace I y), inner ℝ v w = B (mvfderiv I f y v) (mvfderiv I f y w))
    {X Y : Π y : M, TangentSpace I y} (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (w : TangentSpace I x) :
    inner ℝ (cov Y x (X x)) w =
      B (mvfderiv I (fun y ↦ mvfderiv I f y (Y y)) x (X x)) (mvfderiv I f x w) := by
  have : IsManifold I (minSmoothness ℝ 2) M := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  have hn : minSmoothness ℝ 2 ≤ (2 : ℕ∞ω) := by simp [minSmoothness_of_isRCLikeNormedField]
  let Z : Π y : M, TangentSpace I y := extend E w
  have hZ : MDiffAt (T% Z) x := mdifferentiableAt_extend I E w
  -- `D U V` is the ambient derivative of `df V` along `U`, and `A U V W` the Koszul building block.
  let D : (Π y : M, TangentSpace I y) → (Π y : M, TangentSpace I y) → F :=
    fun U V ↦ mvfderiv I (fun y ↦ mvfderiv I f y (V y)) x (U x)
  let A : (Π y : M, TangentSpace I y) → (Π y : M, TangentSpace I y) →
      (Π y : M, TangentSpace I y) → ℝ :=
    fun U V W ↦ B (D U V) (mvfderiv I f x (W x))
  -- The product rule for the induced inner product of two fields.
  have hdiff {U V W : Π y : M, TangentSpace I y} (hV : MDiffAt (T% V) x)
      (hW : MDiffAt (T% W) x) :
      mvfderiv I (fun y ↦ inner ℝ (V y) (W y)) x (U x) = A U V W + A U W V := by
    have heq : (fun y ↦ inner ℝ (V y) (W y)) =
        fun y ↦ B (mvfderiv I f y (V y)) (mvfderiv I f y (W y)) :=
      funext fun y ↦ hg y (V y) (W y)
    have hV' := TauCeti.mdifferentiableAt_mvfderiv_apply hf le_rfl hV
    have hW' := TauCeti.mdifferentiableAt_mvfderiv_apply hf le_rfl hW
    have hBV := B.mvfderiv_comp_apply hV' (U x)
    simp only [Function.comp_def] at hBV
    rw [heq, TauCeti.mvfderiv_clm_apply (A := fun y ↦ B (mvfderiv I f y (V y)))
      (B.mdifferentiableAt.comp x hV') hW', hBV, hB (mvfderiv I f x (V x))]
  -- The differential of `f` carries brackets to commutators of ambient derivatives.
  have hbracket {U V W : Π y : M, TangentSpace I y} (hU : MDiffAt (T% U) x)
      (hV : MDiffAt (T% V) x) :
      inner ℝ (mlieBracket I U V x) (W x) = A U V W - A V U W := by
    rw [hg, mvfderiv_mlieBracket hf hn hU hV, map_sub, sub_apply]
  have hk := h.two_inner_eq_koszul hX hY hZ
  rw [TauCeti.Manifold.koszul_apply, hdiff hY hZ, hdiff hZ hX, hdiff hX hY,
    hbracket hX hY, hbracket hX hZ, hbracket hY hZ] at hk
  have hw : Z x = w := by simp [Z]
  simp only [A, D, hw] at hk
  linarith

open TauCeti.Manifold in
/-- **The Gauss formula along a curve, for a bilinear form.** Let `f : M → F` be a `C²` map into
a real normed space, and `B` a symmetric continuous bilinear form on `F` for which the differential
of `f` preserves inner products. For a field `V` along a curve `γ`, whose ambient image
`r ↦ df (V r)` has derivative `a` at `t`, the covariant derivative of `V` along `γ` for a
Levi-Civita connection satisfies `⟪∇_t V, w⟫ = B a (df w)`. -/
theorem IsLeviCivitaConnection.inner_alongCurve_eq_bilin (hcov : cov.IsLeviCivitaConnection)
    {γ : ℝ → M} {V : ∀ r, TangentSpace I (γ r)} {t : ℝ} {a : F}
    (hf : ContMDiffAt I 𝓘(ℝ, F) 2 f (γ t)) (hB : ∀ u v, B u v = B v u)
    (hg : ∀ x (v w : TangentSpace I x), inner ℝ v w = B (mvfderiv I f x v) (mvfderiv I f x w))
    (hγ : MDifferentiableAt 𝓘(ℝ) I γ t)
    (hV : DifferentiableAt ℝ (sectionCoord ℝ (F := E) γ V (γ t)) t)
    (ha : HasDerivAt (fun r ↦ mvfderiv I f (γ r) (V r)) a t)
    (w : TangentSpace I (γ t)) :
    inner ℝ (alongCurve cov γ V t) w = B a (mvfderiv I f (γ t) w) := by
  let Z := extend E w
  have hZ : MDiffAt (T% Z) (γ t) := mdifferentiableAt_extend I E w
  have hZcoord : DifferentiableAt ℝ
      (sectionCoord ℝ (F := E) γ (fun r ↦ Z (γ r)) (γ t)) t :=
    differentiableAt_sectionCoord γ _ (hZ.comp t hγ)
      (mem_baseSet_trivializationAt E (TangentSpace I) (γ t))
  have hsource := hcov.isMetricCompatible.hasDerivAt_inner_alongCurve hγ hV hZcoord
  have htarget := B.hasDerivAt_of_bilinear (fun _ ↦ ha) (fun _ ↦ hasDerivAt_comp_curve
    (TauCeti.mdifferentiableAt_mvfderiv_apply hf le_rfl hZ)
    (hasMFDerivAt_curveVelocity hγ))
  have hpair : (fun r ↦ inner ℝ (V r) (Z (γ r))) =
      fun r ↦ B (mvfderiv I f (γ r) (V r)) (mvfderiv I f (γ r) (Z (γ r))) :=
    funext fun r ↦ hg _ _ _
  have hderiv := hsource.unique (hpair ▸ htarget)
  let X := extend E (curveVelocity I γ t)
  have hX : MDiffAt (T% X) (γ t) := mdifferentiableAt_extend I E _
  have hXv : X (γ t) = curveVelocity I γ t := by simp [X]
  have hgauss := hcov.inner_apply_eq_bilin_mvfderiv hf hB hg hX hZ (V t)
  rw [hXv, real_inner_comm (V t), hB _ (mvfderiv I f (γ t) (V t))] at hgauss
  rw [alongCurve_pullback cov γ _ (hasMFDerivAt_curveVelocity hγ) hZ] at hderiv
  simp only [Function.comp_apply] at hderiv
  have hw : Z (γ t) = w := by simp [Z]
  rw [hw] at hderiv
  linarith [hgauss]

end CovariantDerivative

end
