/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Morse.GradientLike
public import TauCeti.Analysis.Calculus.Morse.Index
public import TauCeti.Geometry.Manifold.Morse.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Linearization
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic
import TauCeti.Geometry.Manifold.VectorField.Chart.Linearization
import TauCeti.Geometry.Manifold.VectorField.Regularity
import TauCeti.Topology.VectorBundle.Riemannian.Basic
import SymplecticGeometry.Analysis.Calculus.FDeriv.SecondOrder

/-!
# The linearization of a gradient-like field at a nondegenerate critical point

Let `X` be gradient-like for `f` (`TauCeti.IsGradientLike`) on a manifold modelled on a
finite-dimensional real space `E`, and let `p` be a nondegenerate critical point of `f`, with `X`
differentiable at `p`. In the chart at `p`, write `H` for the Hessian of `f` and `A` for the
linearization of `X` at its zero `p` (Tau Ceti's `TauCeti.sectionLinearization`). The
gradient-like inequality, taken at second order at `p`, makes `v ↦ H v (A v)` positive definite.
This is the first step of the analysis of the stable discs of a Weinstein structure at a
nondegenerate critical point: it makes `A` hyperbolic and relates its stable dimension to the
Morse index.

## Main results

* `TauCeti.IsGradientLike.exists_pos_mul_norm_sq_le_hessian`: there is `c > 0` with
  `c * ‖v‖ ^ 2 ≤ H v (A v)` for every `v`.

## Implementation notes

The metric `g` and the function `δ` of the gradient-like condition are only continuous in the
chart, so they are compared with their values at `p`. For a fixed vector `e` of the chart, the
Cauchy–Schwarz inequality `(df e) ^ 2 ≤ ‖grad f‖ ^ 2 * g(e, e)` gives near `p` an inequality
`κ * (df_u e) ^ 2 ≤ df_u (X u)` in the chart, with `κ > 0` independent of `e` for `‖e‖ ≤ 1`. It
passes to second order by `HasFDerivAt.mul_sq_apply_le_apply_apply_of_eventually`, and the
invertibility of the Hessian makes the resulting bound uniform in `v`.

## References

* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  Chapter 11
-/

public section

open Bundle Filter Set VectorField TauCeti.Manifold
open scoped ContDiff Manifold Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}

/-- The gradient-like inequality near a nondegenerate critical point `p`, read in the chart at
`p` against a vector `e` of the chart with `‖e‖ ≤ 1`, with a constant `κ > 0` that does not
depend on `e`. -/
private theorem IsGradientLike.exists_eventually_mul_sq_le (hX : IsGradientLike f X) {p : M}
    (hp : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f p) :
    ∃ κ > 0, ∀ e : E, ‖e‖ ≤ 1 → ∀ᶠ u in 𝓝 (extChartAt 𝓘(ℝ, E) p p),
      κ * fderiv ℝ (f ∘ (extChartAt 𝓘(ℝ, E) p).symm) u e ^ 2 ≤
        fderiv ℝ (f ∘ (extChartAt 𝓘(ℝ, E) p).symm) u
          (VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) p).symm X u) := by
  obtain ⟨g, δ, hδc, hδ, hg⟩ := (isGradientLike_def f X).1 hX
  let : RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) := ⟨g.toRiemannianMetric⟩
  set φ := extChartAt 𝓘(ℝ, E) p
  set G₀ : E →L[ℝ] E →L[ℝ] ℝ := g.inner p
  set N := ‖G₀‖
  refine ⟨δ p / (2 * (N + 1)), by have := hδ p; positivity, fun e he ↦ ?_⟩
  set T := trivializationAt E (TangentSpace 𝓘(ℝ, E)) p
  have hpT : p ∈ T.baseSet := FiberBundle.mem_baseSet_trivializationAt' p
  -- The vector `e` of the chart at `p`, as a vector field near `p`.
  set W : (y : M) → TangentSpace 𝓘(ℝ, E) y := fun y ↦ T.symm y e
  have hWp : W p = e := TangentBundle.trivializationAt_symm_apply_self p e
  have hWc : ContinuousAt (fun y ↦ TotalSpace.mk' E y (W y)) p :=
    (T.continuousAt_symm_prodMk_left hpT).congr <|
      (T.open_baseSet.eventually_mem hpT).mono fun y hy ↦ (T.mk_symm hy e).symm
  have hgW : ContinuousAt (fun y ↦ g.inner y (W y) (W y)) p :=
    g.toContinuousRiemannianMetric.continuousAt_inner (b := id) hWc hWc
  have hgWp : g.inner p (W p) (W p) < N + 1 := by
    rw [hWp]
    have h₁ : G₀ e e ≤ N * ‖e‖ * ‖e‖ := (le_abs_self _).trans (G₀.le_opNorm₂ e e)
    have h₂ : N * ‖e‖ * ‖e‖ ≤ N * 1 * 1 := by gcongr
    -- `G₀` is the metric at `p`, read as a bilinear form on `E`.
    change G₀ e e < N + 1
    linarith
  have hnear : ∀ᶠ y in 𝓝 p, δ p / 2 < δ y ∧ g.inner y (W y) (W y) < N + 1 :=
    (hδc.continuousAt.eventually (lt_mem_nhds (half_lt_self (hδ p)))).and
      (hgW.eventually (gt_mem_nhds hgWp))
  have hF : ∀ᶠ u in 𝓝 (φ p), DifferentiableAt ℝ (f ∘ φ.symm) u :=
    (((isManifoldNondegenerateCriticalPoint_iff _).1 hp).contDiffAt.eventually (by simp)).mono
      fun u hu ↦ hu.differentiableAt (by norm_num)
  have hsymm : Tendsto φ.symm (𝓝 (φ p)) (𝓝 p) := by
    have := continuousAt_extChartAt_symm (I := 𝓘(ℝ, E)) p
    rwa [ContinuousAt, extChartAt_to_inv] at this
  filter_upwards [hsymm.eventually hnear, hF, extChartAt_target_mem_nhds (I := 𝓘(ℝ, E)) p]
    with u ⟨hδu, hWu⟩ hFu hu
  set y := φ.symm u
  have hys : y ∈ φ.source := φ.map_target hu
  have hφy : φ y = u := φ.right_inv hu
  -- In the chart at `p`, the differential of `f` at `y` is that of `f ∘ φ.symm` at `u`.
  have hdf (w : TangentSpace 𝓘(ℝ, E) y) : mvfderiv 𝓘(ℝ, E) f y w =
      fderiv ℝ (f ∘ φ.symm) u (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ y w) := by
    rw [mvfderiv_apply_eq_mfderiv_apply,
      mfderiv_eq_fderiv_comp_mfderiv_extChartAt hys (by rwa [hφy]), hφy]
    -- A composition applied to `w`, whose middle space, the tangent space at `φ y`, is `E`.
    rfl
  have hys' : y ∈ (chartAt E p).source := by rwa [← extChartAt_source (I := 𝓘(ℝ, E))]
  have hWe : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ y (W y) = e := by
    simp only [W]
    rw [← T.symmL_apply (R := ℝ) (by simpa [T] using hys'),
      TangentBundle.symmL_trivializationAt hys']
    exact DFunLike.congr_fun
      (mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm' (I := 𝓘(ℝ, E)) hys) e
  have hXY : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ y (X y) =
      VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) φ.symm X u := by
    rw [← hφy]
    exact (VectorField.mpullback_extChartAt_symm_apply_eq_mfderiv X hys (by simp)).symm
  rw [← hWe, ← hXY, ← hdf, ← hdf]
  -- The Cauchy–Schwarz inequality for the gradient `G` of `f` at `y`.
  set G := mgradient 𝓘(ℝ, E) f y
  have hcs : mvfderiv 𝓘(ℝ, E) f y (W y) ^ 2 ≤ ‖G‖ ^ 2 * g.inner y (W y) (W y) := by
    rw [← inner_mgradient, ← g.inner_eq, ← real_inner_self_eq_norm_sq, sq]
    exact real_inner_mul_inner_self_le G (W y)
  have hXX : 0 ≤ g.inner y (X y) (X y) := g.toRiemannianMetric.inner_self_nonneg y (X y)
  have hgy := hg y
  have hδp := hδ p
  have hN : 0 ≤ N := norm_nonneg G₀
  calc δ p / (2 * (N + 1)) * mvfderiv 𝓘(ℝ, E) f y (W y) ^ 2
      ≤ δ p / (2 * (N + 1)) * (‖G‖ ^ 2 * (N + 1)) := by
        gcongr
        exact hcs.trans (by gcongr)
    _ = δ p / 2 * ‖G‖ ^ 2 := by field_simp
    _ ≤ δ y * (g.inner y (X y) (X y) + ‖G‖ ^ 2) := by nlinarith [sq_nonneg ‖G‖]
    _ ≤ _ := hgy
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
  set Y := VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) φ.symm X
  set B := fderiv ℝ (fderiv ℝ (f ∘ φ.symm)) (φ p)
  obtain ⟨κ, hκ, hev⟩ := hX.exists_eventually_mul_sq_le hp
  obtain ⟨L, hL⟩ := hp'.isInvertible
  replace hL : (L : E →L[ℝ] E →L[ℝ] ℝ) = B := hL
  have hB : HasFDerivAt (fderiv ℝ (f ∘ φ.symm)) B (φ p) :=
    ((hp'.contDiffAt.fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasFDerivAt
  have hY : DifferentiableAt ℝ Y (φ p) := by
    have := mdifferentiableAt_section_iff_differentiableAt_mpullbackWithin_extChartAt_symm.1 hXp
    rwa [𝓘(ℝ, E).range_eq_univ, mpullbackWithin_univ] at this
  have hY₀ : Y (φ p) = 0 := by
    have hXp0 : X p = 0 := hX.eq_zero_iff.2 (by
      rw [mvfderiv_eq_fderiv_comp_extChartAt_symm]; exact hp'.fderiv_eq_zero)
    simp only [Y, VectorField.mpullback_apply]
    rw [φ.left_inv (mem_extChartAt_source p), hXp0, map_zero]
  -- The inequality at second order, for every `v` and every `e` with `‖e‖ ≤ 1`.
  have key (v e : E) (he : ‖e‖ ≤ 1) : κ * B v e ^ 2 ≤ B v (fderiv ℝ Y (φ p) v) :=
    hB.mul_sq_apply_le_apply_apply_of_eventually hp'.fderiv_eq_zero hY.hasFDerivAt hY₀
      (hev e he) v
  set C := ‖(L.symm : (E →L[ℝ] ℝ) →L[ℝ] E)‖
  refine ⟨κ / (4 * (C + 1) ^ 2), by positivity, fun v ↦ ?_⟩
  have hA : (sectionLinearization (F := E) 𝓘(ℝ, E) id X p v : E) = fderiv ℝ Y (φ p) v := by
    refine (sectionLinearization_apply_eq_vectorFieldChartDerivative X p v).trans ?_
    rw [vectorFieldChartDerivative_def, ContinuousLinearMap.coe_coe]
  have hH : QuadraticMap.associated (hessianQuadraticForm (f ∘ φ.symm) (φ p)) v
      (sectionLinearization (F := E) 𝓘(ℝ, E) id X p v) = B v (fderiv ℝ Y (φ p) v) := by
    simp only [associated_hessianQuadraticForm hp'.contDiffAt,
      ContinuousLinearMap.toBilinForm_apply, hA]
    -- `B` is the local name of this second derivative.
    rfl
  rw [hH]
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  have hBv : B v ≠ 0 := by
    rw [← hL, ContinuousLinearEquiv.coe_coe]
    exact L.map_ne_zero_iff.2 hv
  obtain ⟨e, he, hlt⟩ := (B v).exists_lt_apply_of_lt_opNorm (half_lt_self (norm_pos_iff.2 hBv))
  have hv' : ‖v‖ ≤ C * ‖B v‖ := by
    have h := (L.symm : (E →L[ℝ] ℝ) →L[ℝ] E).le_opNorm (L v)
    rw [ContinuousLinearEquiv.coe_coe, L.symm_apply_apply] at h
    rwa [← hL]
  have h2 : ‖B v‖ ^ 2 / 4 ≤ B v e ^ 2 := by
    rw [Real.norm_eq_abs] at hlt
    nlinarith [norm_nonneg (B v), abs_nonneg (B v e), sq_abs (B v e)]
  have hC : 0 ≤ C := norm_nonneg (L.symm : (E →L[ℝ] ℝ) →L[ℝ] E)
  calc κ / (4 * (C + 1) ^ 2) * ‖v‖ ^ 2 ≤ κ / (4 * (C + 1) ^ 2) * ((C + 1) * ‖B v‖) ^ 2 := by
        gcongr
        nlinarith [norm_nonneg (B v)]
    _ = κ * (‖B v‖ ^ 2 / 4) := by field_simp
    _ ≤ κ * B v e ^ 2 := by gcongr
    _ ≤ _ := key v e he.le

end TauCeti
