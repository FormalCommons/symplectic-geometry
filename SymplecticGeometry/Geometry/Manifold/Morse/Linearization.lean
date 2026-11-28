/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Morse.GradientLike
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Linearization
public import TauCeti.Analysis.ODE.Linear
public import TauCeti.Geometry.Manifold.Morse.Index
public import Mathlib.Analysis.InnerProductSpace.PiL2
import TauCeti.Geometry.Manifold.VectorField.Regularity
import TauCeti.Analysis.Calculus.ContDiff.Differentiable
import SymplecticGeometry.Geometry.Manifold.VectorField.Chart
import SymplecticGeometry.Geometry.Manifold.Morse.LocalCoordinates
import SymplecticGeometry.Analysis.Calculus.FDeriv.SecondOrder
import SymplecticGeometry.Analysis.Normed.Operator.Functional
import SymplecticGeometry.Topology.Algebra.Module.BilinearForm
import TauCeti.Analysis.Calculus.Morse.Index
import TauCeti.Analysis.ODE.ExponentialDichotomy
import SymplecticGeometry.Analysis.ODE.LyapunovBilinForm
import SymplecticGeometry.Analysis.InnerProductSpace.Ellipsoid

/-!
# The linearization of a gradient-like field at a critical point

Let `X` satisfy the gradient-like inequality for `f` near a critical point `p` of `f`, on a
manifold modelled on a finite-dimensional real space `E`, and let `X` be differentiable at `p`.
In the chart at `p`, write `B` for the second derivative of `f` and `A` for the linearization of
`X` at its zero `p` (Tau Ceti's `TauCeti.sectionLinearization`). Taken at second order at `p`,
the inequality bounds `‖A v‖ ^ 2 + ‖B v‖ ^ 2` by a multiple of `B v (A v)`. At a nondegenerate
critical point, where `B` is invertible, this makes `v ↦ B v (A v)` positive definite: the
Hessian is then a Lyapunov form for `A`. It follows that `A` is hyperbolic, and that its stable
subspace has dimension the Morse index of `f` at `p`.

Nothing here uses a symplectic or Weinstein structure; the index bound for a Weinstein structure
and the analysis of its stable discs build on these results.

## Main results

* `TauCeti.exists_pos_mul_norm_sq_add_norm_sq_le_fderiv_fderiv`: at any critical point `p` of a
  function `f` that is `C²` in the chart, if `X` is differentiable at `p` and satisfies the
  gradient-like inequality near `p`, there is `c > 0` with
  `c * (‖A v‖ ^ 2 + ‖B v‖ ^ 2) ≤ B v (A v)` for every `v`.
* `TauCeti.exists_pos_mul_norm_sq_add_sq_le_of_fderiv_fderiv_apply_eq_zero`: at such a point, if
  `f` is `C⁴` and `X` is `C³`, and `B e = 0`, the inequality read along the parabolas
  `t ↦ t • e + t ^ 2 • w` at order `t ^ 4`, in the same form
  `c * (‖β‖ ^ 2 + ‖α‖ ^ 2) ≤ α β`.
* `TauCeti.IsGradientLike.exists_pos_mul_norm_sq_le_hessian`: for `X` gradient-like and `p`
  nondegenerate, there is `c > 0` with `c * ‖v‖ ^ 2 ≤ H v (A v)` for every `v`, where `H` is the
  bilinear form of the Hessian in the chart.
* `TauCeti.IsGradientLike.exists_pos_mul_norm_sq_le_fderiv_fderiv`: the same bound for the second
  derivative `B`.
* `TauCeti.IsGradientLike.exists_projection_exponential_bounds`: the flow of `A` has an
  exponential dichotomy.
* `TauCeti.IsGradientLike.finrank_stableSubspace_eq_manifoldMorseIndex` and
  `TauCeti.IsGradientLike.finrank_range_eq_manifoldMorseIndex`: the stable subspace of `A`, which
  is the range of the projection of any such dichotomy, has dimension the Morse index of `f` at
  `p`.
* `TauCeti.IsGradientLike.exists_continuousLinearEquiv_stableSubspace`: at a critical point of
  index `m`, a continuous linear equivalence `L` from `EuclideanSpace ℝ (Fin m)` onto the stable
  subspace of `A` with `-B (L u) (L u) = ‖u‖ ^ 2`.

In the statements at a nondegenerate critical point, `A : E →L[ℝ] E` comes with a hypothesis
`A = sectionLinearization …`, since the linearization itself is a map between tangent spaces,
which carry no norm.

## Implementation notes

The gradient-like inequality in the chart at `p`,
`TauCeti.IsGradientLikeAt.exists_mul_le_fderiv_comp_symm`, gives near `p` an inequality
`κ * (‖X u‖ ^ 2 + (df_u e) ^ 2) ≤ df_u (X u)` in the chart, with `κ > 0` independent of `e` for
`‖e‖ ≤ 1`. It passes to second order by
`HasFDerivAt.mul_norm_sq_add_sq_apply_le_apply_apply_of_eventually`, and the supremum over such
`e` gives the bound with the norm of `B v`
(`ContinuousLinearMap.mul_norm_sq_add_opNorm_sq_le_of_forall_norm_le_one`). Nondegeneracy is not
needed for this; at a nondegenerate critical point, the invertibility of the Hessian then bounds
`‖v‖` by `‖B v‖`.

With `B` a symmetric bilinear Lyapunov form for `A`, the dichotomy and the index come from
`ContinuousLinearMap.exists_projection_exponential_bounds_of_le_apply` and
`ContinuousLinearMap.sigNeg_toQuadraticMap_eq_finrank_stableSubspace`, which transfer Tau Ceti's
inertia theorem to bilinear forms on a normed space. The Euclidean coordinate on the stable
subspace is `QuadraticMap.PosDef.exists_continuousLinearEquiv_euclideanSpace` applied to `-B`,
which is positive definite there by `ContinuousLinearMap.apply_self_neg_of_mem_stableSubspace`.

## References

* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  Proposition 9.23 (a), whose proof uses the second-order inequality at a critical point that
  need not be nondegenerate; Lemma 9.9, for the splitting of the linearization and the sign of
  the Hessian on its parts
-/

public section

open Bundle Filter Module NormedSpace Set TauCeti.Manifold
open scoped ContDiff Manifold NNReal Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}

/-- The gradient-like inequality near `p` in the chart at `p`, read against a vector `e` of the
chart with `‖e‖ ≤ 1`: with `Y` the field in the chart and a constant `κ > 0` that does not depend
on `e`, `κ * (‖Y u‖ ^ 2 + (df_u e) ^ 2) ≤ df_u (Y u)` near the image of `p`. -/
private theorem IsGradientLikeAt.exists_pos_eventually_mul_norm_sq_add_sq_le {p : M}
    (hX : IsGradientLikeAt f X p) {Y : E → E}
    (hY : Y = VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) p).symm X) :
    ∃ κ > 0, ∀ e : E, ‖e‖ ≤ 1 → ∀ᶠ u in 𝓝 (extChartAt 𝓘(ℝ, E) p p),
      κ * (‖Y u‖ ^ 2 + fderiv ℝ (f ∘ (extChartAt 𝓘(ℝ, E) p).symm) u e ^ 2) ≤
        fderiv ℝ (f ∘ (extChartAt 𝓘(ℝ, E) p).symm) u (Y u) := by
  obtain ⟨r₀, hr₀, c, hc, hball, h⟩ := hX.exists_mul_le_fderiv_comp_symm
    (IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℝ, E)) p) (mem_chart_source E p)
  refine ⟨c, hc, fun e he ↦ ?_⟩
  set φ := extChartAt 𝓘(ℝ, E) p
  have hφ : (φ : M → E) = chartAt E p := by simp [φ]
  have hφs : (φ.symm : E → M) = (chartAt E p).symm := by simp [φ]
  have hball' : Metric.ball (φ p) r₀ ∈ 𝓝 (φ p) := Metric.ball_mem_nhds _ hr₀
  filter_upwards [hball'] with u hu
  rw [hφ] at hu
  have hu' : u ∈ φ.target := by simpa [φ] using hball hu
  -- The field in the chart is the image of `X (φ.symm u)` by the differential of the chart.
  have hXY : Y u = mvfderiv 𝓘(ℝ, E) φ (φ.symm u) (X (φ.symm u)) := by
    have h : VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) φ.symm X (φ (φ.symm u)) =
        mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ (φ.symm u) (X (φ.symm u)) :=
      VectorField.mpullback_extChartAt_symm_apply_eq_mfderiv X (φ.map_target hu') (by simp)
    rw [φ.right_inv hu'] at h
    rw [hY, mvfderiv_apply_eq_mfderiv_apply]
    -- The two sides are stated in `E` and in the tangent space at `u`, which is `E`.
    exact h
  have hu := h u hu
  rw [← hφ, ← hφs, ← hXY] at hu
  have hDe : fderiv ℝ (f ∘ φ.symm) u e ^ 2 ≤ ‖fderiv ℝ (f ∘ φ.symm) u‖ ^ 2 := by
    rw [← sq_abs, ← Real.norm_eq_abs]
    gcongr
    exact (ContinuousLinearMap.le_opNorm _ e).trans (mul_le_of_le_one_right (norm_nonneg _) he)
  exact le_trans (by gcongr) hu

/-- **The gradient-like inequality at second order.** Let `X` be gradient-like for `f` near a
critical point `p` of `f` (`TauCeti.IsGradientLikeAt`). Let `f` be `C²` in the chart
at `p`, with second derivative `B` there, and let `X` be differentiable at `p`, with linearization
`A`. Then there is `c' > 0` with `c' * (‖A v‖ ^ 2 + ‖B v‖ ^ 2) ≤ B v (A v)` for every `v`. -/
theorem exists_pos_mul_norm_sq_add_norm_sq_le_fderiv_fderiv {p : M}
    (hX : IsGradientLikeAt f X p) (hp : p ∈ criticalPoints 𝓘(ℝ, E) f)
    (hf : ContDiffAt ℝ 2 (f ∘ (extChartAt 𝓘(ℝ, E) p).symm) (extChartAt 𝓘(ℝ, E) p p))
    (hXp : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E).tangent
      (fun x ↦ (X x : TangentBundle 𝓘(ℝ, E) M)) p)
    {A : E →L[ℝ] E} (hA : A = sectionLinearization (F := E) 𝓘(ℝ, E) id X p) :
    ∃ c > 0, ∀ v : E, c * (‖A v‖ ^ 2 +
      ‖fderiv ℝ (fderiv ℝ (f ∘ (extChartAt 𝓘(ℝ, E) p).symm)) (extChartAt 𝓘(ℝ, E) p p) v‖ ^ 2) ≤
      fderiv ℝ (fderiv ℝ (f ∘ (extChartAt 𝓘(ℝ, E) p).symm)) (extChartAt 𝓘(ℝ, E) p p) v (A v) := by
  -- At the critical point `p`, the inequality forces `X p = 0`.
  have hX₀ : X p = 0 := hX.eq_zero_iff.2 hp
  set φ := extChartAt 𝓘(ℝ, E) p
  set Y : E → E := VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) φ.symm X
  set B := fderiv ℝ (fderiv ℝ (f ∘ φ.symm)) (φ p)
  obtain ⟨κ, hκ, hev⟩ :=
    hX.exists_pos_eventually_mul_norm_sq_add_sq_le (Y := Y) rfl
  have hB : HasFDerivAt (fderiv ℝ (f ∘ φ.symm)) B (φ p) := hf.hasFDerivAt_fderiv le_rfl
  have hD₀ : fderiv ℝ (f ∘ φ.symm) (φ p) = 0 :=
    fderiv_comp_extChartAt_symm_eq_zero_of_mem_criticalPoints hp
  have hY : HasFDerivAt Y A (φ p) := hA ▸ hXp.hasFDerivAt_mpullback_extChartAt_symm
  have hY₀ : Y (φ p) = 0 := (VectorField.mpullback_extChartAt_symm_self X p).trans hX₀
  -- The inequality at second order, for each `e` with `‖e‖ ≤ 1`.
  have hBe (v e : E) (he : ‖e‖ ≤ 1) : κ * (‖A v‖ ^ 2 + B v e ^ 2) ≤ B v (A v) :=
    hB.mul_norm_sq_add_sq_apply_le_apply_apply_of_eventually hD₀ hY hY₀ (hev e he) v
  exact ⟨κ, hκ, fun v ↦ (B v).mul_norm_sq_add_opNorm_sq_le_of_forall_norm_le_one hκ.le (hBe v)⟩

/-- **The gradient-like inequality at fourth order, along the kernel of the Hessian.** Let `X` be
gradient-like for `f` near a critical point `p` of `f` (`TauCeti.IsGradientLikeAt`), let `f` be
`C⁴` in the chart at `p`, with derivatives `B = D²F` and `D³F` there, and let `X` be `C³` at `p`,
with `Y` its expression in the chart. Let `B e = 0`. Then there is `c > 0` such that, for every
`w`, with `α = B w + D³F e e / 2` and `β = DY w + D²Y e e / 2`,
`c * (‖β‖ ^ 2 + ‖α‖ ^ 2) ≤ α β`. This is the inequality read along the parabolas
`t ↦ t • e + t ^ 2 • w` of the chart, at order `t ^ 4`. -/
theorem exists_pos_mul_norm_sq_add_sq_le_of_fderiv_fderiv_apply_eq_zero {p : M}
    (hX : IsGradientLikeAt f X p) (hp : p ∈ criticalPoints 𝓘(ℝ, E) f)
    (hf : ContDiffAt ℝ 4 (f ∘ (extChartAt 𝓘(ℝ, E) p).symm) (extChartAt 𝓘(ℝ, E) p p))
    (hXp : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E).tangent 3
      (fun x ↦ (X x : TangentBundle 𝓘(ℝ, E) M)) p) {e : E}
    (he : fderiv ℝ (fderiv ℝ (f ∘ (extChartAt 𝓘(ℝ, E) p).symm)) (extChartAt 𝓘(ℝ, E) p p) e = 0) :
    ∃ c > 0, ∀ w : E,
      c * (‖fderiv ℝ (VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) p).symm X)
            (extChartAt 𝓘(ℝ, E) p p) w + (2⁻¹ : ℝ) • fderiv ℝ (fderiv ℝ
            (VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) p).symm X))
            (extChartAt 𝓘(ℝ, E) p p) e e‖ ^ 2 +
        ‖fderiv ℝ (fderiv ℝ (f ∘ (extChartAt 𝓘(ℝ, E) p).symm)) (extChartAt 𝓘(ℝ, E) p p) w +
          (2⁻¹ : ℝ) • fderiv ℝ (fderiv ℝ (fderiv ℝ (f ∘ (extChartAt 𝓘(ℝ, E) p).symm)))
            (extChartAt 𝓘(ℝ, E) p p) e e‖ ^ 2) ≤
      (fderiv ℝ (fderiv ℝ (f ∘ (extChartAt 𝓘(ℝ, E) p).symm)) (extChartAt 𝓘(ℝ, E) p p) w +
          (2⁻¹ : ℝ) • fderiv ℝ (fderiv ℝ (fderiv ℝ (f ∘ (extChartAt 𝓘(ℝ, E) p).symm)))
            (extChartAt 𝓘(ℝ, E) p p) e e)
        (fderiv ℝ (VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) p).symm X)
            (extChartAt 𝓘(ℝ, E) p p) w + (2⁻¹ : ℝ) • fderiv ℝ (fderiv ℝ
            (VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) p).symm X))
            (extChartAt 𝓘(ℝ, E) p p) e e) := by
  have hX₀ : X p = 0 := hX.eq_zero_iff.2 hp
  set φ := extChartAt 𝓘(ℝ, E) p
  set Y : E → E := VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) φ.symm X
  obtain ⟨κ, hκ, hev⟩ :=
    hX.exists_pos_eventually_mul_norm_sq_add_sq_le (Y := Y) rfl
  have hXd := hXp.mdifferentiableAt (by norm_num)
  have hY : ContDiffAt ℝ 3 Y (φ p) := hXp.contDiffAt_mpullback_extChartAt_symm
  have hY₀ : Y (φ p) = 0 := (VectorField.mpullback_extChartAt_symm_self X p).trans hX₀
  have hD₀ : fderiv ℝ (f ∘ φ.symm) (φ p) = 0 :=
    fderiv_comp_extChartAt_symm_eq_zero_of_mem_criticalPoints hp
  -- The linearization of `X` vanishes on `e`: at second order, it has the kernel of `B`.
  have hYe : fderiv ℝ Y (φ p) e = 0 := by
    set A : E →L[ℝ] E := sectionLinearization (F := E) 𝓘(ℝ, E) id X p
    obtain ⟨c₂, hc₂, h₂⟩ := exists_pos_mul_norm_sq_add_norm_sq_le_fderiv_fderiv hX hp
      (hf.of_le (by norm_num)) hXd (A := A) rfl
    have hA : HasFDerivAt Y A (φ p) := hXd.hasFDerivAt_mpullback_extChartAt_symm
    rw [hA.fderiv]
    exact (ContinuousLinearMap.ker_eq_ker_of_mul_norm_sq_add_norm_sq_le hc₂ h₂).le he
  exact ⟨κ, hκ, fun w ↦
    ContinuousLinearMap.mul_norm_sq_add_opNorm_sq_le_of_forall_norm_le_one hκ.le fun e' he' ↦
      (hf.fderiv_right (m := 3) (by norm_num))
        |>.mul_norm_sq_add_sq_le_of_eventually_of_fderiv_apply_eq_zero
        hD₀ he hY hY₀ hYe (hev e' he') w⟩

/-- **The gradient-like inequality at second order.** Let `X` be gradient-like for `f`, let `p` be
a nondegenerate critical point of `f`, and let `X` be differentiable at `p`. Write `H` for the
bilinear form of the Hessian of `f` read in the chart at `p`, and `A` for the linearization of `X`
at `p`. Then there is `c > 0` with `c * ‖v‖ ^ 2 ≤ H v (A v)` for every `v`. -/
theorem IsGradientLike.exists_pos_mul_norm_sq_le_hessian (hX : IsGradientLike f X) {p : M}
    (hp : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f p)
    (hXp : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E).tangent
      (fun x ↦ (X x : TangentBundle 𝓘(ℝ, E) M)) p) :
    ∃ c > 0, ∀ v : E, c * ‖v‖ ^ 2 ≤
      QuadraticMap.associated (hessianQuadraticForm (f ∘ (extChartAt 𝓘(ℝ, E) p).symm)
        (extChartAt 𝓘(ℝ, E) p p)) v (sectionLinearization (F := E) 𝓘(ℝ, E) id X p v) := by
  have hp' := (isManifoldNondegenerateCriticalPoint_iff _).1 hp
  set φ := extChartAt 𝓘(ℝ, E) p
  set B := fderiv ℝ (fderiv ℝ (f ∘ φ.symm)) (φ p)
  obtain ⟨κ, hκ, hκB⟩ := exists_pos_mul_norm_sq_add_norm_sq_le_fderiv_fderiv
    (hX.isGradientLikeAt p) hp.mem_criticalPoints hp'.contDiffAt hXp rfl
  obtain ⟨L, hL⟩ := hp'.isInvertible
  replace hL : (L : E →L[ℝ] E →L[ℝ] ℝ) = B := hL
  set C := ‖(L.symm : (E →L[ℝ] ℝ) →L[ℝ] E)‖
  refine ⟨κ / (C + 1) ^ 2, by positivity, fun v ↦ ?_⟩
  rw [associated_hessianQuadraticForm hp'.contDiffAt]
  refine le_of_le_of_eq ?_ (B.toBilinForm_apply v _).symm
  have hv : ‖v‖ ≤ C * ‖B v‖ := by
    have h := (L.symm : (E →L[ℝ] ℝ) →L[ℝ] E).le_opNorm (L v)
    rw [ContinuousLinearEquiv.coe_coe, L.symm_apply_apply] at h
    rwa [← hL]
  have hC : 0 ≤ C := norm_nonneg (L.symm : (E →L[ℝ] ℝ) →L[ℝ] E)
  have hv' : ‖v‖ ≤ (C + 1) * ‖B v‖ := hv.trans (by nlinarith [norm_nonneg (B v)])
  calc κ / (C + 1) ^ 2 * ‖v‖ ^ 2 ≤ κ / (C + 1) ^ 2 * ((C + 1) * ‖B v‖) ^ 2 := by gcongr
    _ = κ * ‖B v‖ ^ 2 := by field_simp
    _ ≤ _ := (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (sq_nonneg _)) hκ.le).trans (hκB v)

/-- **The gradient-like inequality at second order, for the second derivative.** Under the
hypotheses of `TauCeti.IsGradientLike.exists_pos_mul_norm_sq_le_hessian`, with `A` the
linearization of `X` at `p`, there is `c > 0` with `c * ‖v‖ ^ 2 ≤ D²(f ∘ φ⁻¹)(φ p) v (A v)` for
every `v`, where `φ` is the chart at `p`. -/
theorem IsGradientLike.exists_pos_mul_norm_sq_le_fderiv_fderiv (hX : IsGradientLike f X) {p : M}
    (hp : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f p)
    (hXp : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E).tangent
      (fun x ↦ (X x : TangentBundle 𝓘(ℝ, E) M)) p)
    {A : E →L[ℝ] E} (hA : A = sectionLinearization (F := E) 𝓘(ℝ, E) id X p) :
    ∃ c > 0, ∀ v : E, c * ‖v‖ ^ 2 ≤
      fderiv ℝ (fderiv ℝ (f ∘ (extChartAt 𝓘(ℝ, E) p).symm)) (extChartAt 𝓘(ℝ, E) p p) v (A v) := by
  subst hA
  obtain ⟨c, hc, h⟩ := hX.exists_pos_mul_norm_sq_le_hessian hp hXp
  rw [associated_hessianQuadraticForm
    ((isManifoldNondegenerateCriticalPoint_iff _).1 hp).contDiffAt] at h
  exact ⟨c, hc, fun v ↦ (h v).trans_eq (ContinuousLinearMap.toBilinForm_apply _ _ _)⟩

/-! ### The exponential dichotomy and the Morse index -/

/-- **Exponential dichotomy at a nondegenerate critical point.** Let `X` be gradient-like for `f`,
let `p` be a nondegenerate critical point of `f`, let `X` be differentiable at `p`, and let `A` be
the linearization of `X` at `p`. Then the flow of `A` has an exponential dichotomy: a projection
`P` commuting with `A`, and `K, α > 0`, such that `exp (t • A)` contracts the range of `P` at rate
`α` forward in time, and the kernel of `P` at rate `α` backward in time. -/
theorem IsGradientLike.exists_projection_exponential_bounds (hX : IsGradientLike f X) {p : M}
    (hp : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f p)
    (hXp : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E).tangent
      (fun x ↦ (X x : TangentBundle 𝓘(ℝ, E) M)) p)
    {A : E →L[ℝ] E} (hA : A = sectionLinearization (F := E) 𝓘(ℝ, E) id X p) :
    ∃ P : E →L[ℝ] E, IsIdempotentElem P ∧ Commute A P ∧ ∃ K α : ℝ≥0, 0 < K ∧ 0 < α ∧
      (∀ t : ℝ, 0 ≤ t → ∀ v : E, ‖exp (t • A) (P v)‖ ≤ K * Real.exp (-α * t) * ‖v‖) ∧
      (∀ t : ℝ, t ≤ 0 → ∀ v : E, ‖exp (t • A) (v - P v)‖ ≤ K * Real.exp (α * t) * ‖v‖) := by
  obtain ⟨c, hc, hcB⟩ := hX.exists_pos_mul_norm_sq_le_fderiv_fderiv hp hXp hA
  have hB := ((isManifoldNondegenerateCriticalPoint_iff _).1 hp).contDiffAt.isSymmSndFDerivAt
    (by simp)
  exact ContinuousLinearMap.exists_projection_exponential_bounds_of_le_apply hB hc hcB

/-- **The stable dimension of the linearization is the Morse index.** Let `X` be gradient-like
for `f`, let `p` be a nondegenerate critical point of `f`, let `X` be differentiable at `p`, and
let `A` be the linearization of `X` at `p`. Then the stable subspace of `A` has dimension the Morse
index of `f` at `p`. -/
theorem IsGradientLike.finrank_stableSubspace_eq_manifoldMorseIndex (hX : IsGradientLike f X)
    {p : M} (hp : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f p)
    (hXp : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E).tangent
      (fun x ↦ (X x : TangentBundle 𝓘(ℝ, E) M)) p)
    {A : E →L[ℝ] E} (hA : A = sectionLinearization (F := E) 𝓘(ℝ, E) id X p) :
    finrank ℝ A.stableSubspace = manifoldMorseIndex 𝓘(ℝ, E) f p := by
  obtain ⟨c, hc, hcB⟩ := hX.exists_pos_mul_norm_sq_le_fderiv_fderiv hp hXp hA
  have hB := ((isManifoldNondegenerateCriticalPoint_iff _).1 hp).contDiffAt.isSymmSndFDerivAt
    (by simp)
  rw [manifoldMorseIndex_def, morseIndex_def, hessianQuadraticForm_def,
    ContinuousLinearMap.sigNeg_toQuadraticMap_eq_finrank_stableSubspace hB hc hcB]

/-- **The Morse index from an exponential dichotomy.** Let `X` be gradient-like for `f`, let `p` be
a nondegenerate critical point of `f`, let `X` be differentiable at `p`, and let `A` be the
linearization of `X` at `p`. For every exponential dichotomy `P` of `A`, as in
`TauCeti.IsGradientLike.exists_projection_exponential_bounds`, the range of `P` has dimension the
Morse index of `f` at `p`. -/
theorem IsGradientLike.finrank_range_eq_manifoldMorseIndex (hX : IsGradientLike f X) {p : M}
    (hp : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f p)
    (hXp : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E).tangent
      (fun x ↦ (X x : TangentBundle 𝓘(ℝ, E) M)) p)
    {A : E →L[ℝ] E} (hA : A = sectionLinearization (F := E) 𝓘(ℝ, E) id X p)
    {P : E →L[ℝ] E} (hP : IsIdempotentElem P) (hAP : Commute A P) {K α : ℝ} (hα : 0 < α)
    (hs : ∀ t : ℝ, 0 ≤ t → ∀ v : E, ‖exp (t • A) (P v)‖ ≤ K * Real.exp (-α * t) * ‖v‖)
    (hu : ∀ t : ℝ, t ≤ 0 → ∀ v : E, ‖exp (t • A) (v - P v)‖ ≤ K * Real.exp (α * t) * ‖v‖) :
    finrank ℝ P.range = manifoldMorseIndex 𝓘(ℝ, E) f p := by
  rw [ContinuousLinearMap.range_eq_stableSubspace_of_exponential_bounds hα hP hAP hs hu,
    hX.finrank_stableSubspace_eq_manifoldMorseIndex hp hXp hA]

/-- **Euclidean coordinates on the stable subspace.** Let `X` be gradient-like for `f`, let `p`
be a nondegenerate critical point of `f` of Morse index `m`, let `X` be differentiable at `p`,
and let `A` be the linearization of `X` at `p`. Write `H` for the second derivative of `f` read
in the chart at `p`, which is negative definite on the stable subspace of `A`. Then some
continuous linear equivalence `L` from `EuclideanSpace ℝ (Fin m)` onto the stable subspace
satisfies `-H (L u) (L u) = ‖u‖ ^ 2` for every `u`. -/
theorem IsGradientLike.exists_continuousLinearEquiv_stableSubspace
    (hX : IsGradientLike f X) {p : M} (hp : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f p)
    (hXp : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E).tangent
      (fun x ↦ (X x : TangentBundle 𝓘(ℝ, E) M)) p)
    {A : E →L[ℝ] E} (hA : A = sectionLinearization (F := E) 𝓘(ℝ, E) id X p) {m : ℕ}
    (hm : manifoldMorseIndex 𝓘(ℝ, E) f p = m) :
    ∃ L : EuclideanSpace ℝ (Fin m) ≃L[ℝ] A.stableSubspace, ∀ u,
      -fderiv ℝ (fderiv ℝ (f ∘ (extChartAt 𝓘(ℝ, E) p).symm)) (extChartAt 𝓘(ℝ, E) p p)
        (L u) (L u) = ‖u‖ ^ 2 := by
  obtain ⟨c, hc, hcB⟩ := hX.exists_pos_mul_norm_sq_le_fderiv_fderiv hp hXp hA
  have hB := ((isManifoldNondegenerateCriticalPoint_iff _).1 hp).contDiffAt.isSymmSndFDerivAt
    (by simp)
  set H := fderiv ℝ (fderiv ℝ (f ∘ (extChartAt 𝓘(ℝ, E) p).symm)) (extChartAt 𝓘(ℝ, E) p p)
  set Q : QuadraticForm ℝ A.stableSubspace :=
    -(H.toBilinForm.toQuadraticMap.comp A.stableSubspace.subtype)
  have hQ (v : A.stableSubspace) : Q v = -H v v := by
    simp [Q, LinearMap.BilinMap.toQuadraticMap_apply]
  have hQpos : Q.PosDef := fun v hv ↦ by
    rw [hQ, neg_pos]
    exact ContinuousLinearMap.apply_self_neg_of_mem_stableSubspace hB hc hcB v.property
      (by simpa using hv)
  obtain ⟨L, hL⟩ := hQpos.exists_continuousLinearEquiv_euclideanSpace
    ((hX.finrank_stableSubspace_eq_manifoldMorseIndex hp hXp hA).trans hm)
  exact ⟨L, fun u ↦ (hQ _).symm.trans (hL u)⟩

end TauCeti

end
