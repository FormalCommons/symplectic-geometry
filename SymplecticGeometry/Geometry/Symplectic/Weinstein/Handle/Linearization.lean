/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Morse.GradientLike
public import TauCeti.Analysis.Calculus.Morse.Index
public import TauCeti.Analysis.ODE.Linear
public import TauCeti.Geometry.Manifold.Morse.Index
public import TauCeti.Geometry.Manifold.Morse.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Linearization
public import TauCeti.Geometry.Symplectic.Liouville.VectorField
public import SymplecticGeometry.Geometry.Symplectic.Weinstein.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Geometry.Manifold.Morse.CriticalPoints
import Mathlib.Geometry.Manifold.Riemannian.Basic
import TauCeti.Geometry.Manifold.Riemannian.Basic
import TauCeti.Analysis.Normed.Module.Alternating.Curry
import SymplecticGeometry.Analysis.ODE.Linear
import SymplecticGeometry.Geometry.Symplectic.Liouville.VectorField
import TauCeti.LinearAlgebra.BilinearForm.Orthogonal
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic
import TauCeti.Geometry.Manifold.VectorField.Regularity
import SymplecticGeometry.Geometry.Manifold.VectorField.Chart
import TauCeti.Topology.VectorBundle.Riemannian.Basic
import SymplecticGeometry.Analysis.Calculus.FDeriv.SecondOrder
import SymplecticGeometry.Analysis.ODE.LyapunovBilinForm
import SymplecticGeometry.Analysis.InnerProductSpace.Ellipsoid
import TauCeti.Analysis.ODE.ExponentialDichotomy
import TauCeti.Analysis.Calculus.ContDiff.Differentiable

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

At a zero `p` of a Liouville vector field `Z` of a two-form `σ`, the linearization `A` of `Z`
satisfies `σ_p (A u, v) + σ_p (u, A v) = σ_p (u, v)`
(`TauCeti.IsLiouvilleVectorField.apply_sectionLinearization_add`). Along the flow of `A` the
form `σ_p` then grows like `e ^ t`, so it vanishes on the stable subspace of `A`. For a Weinstein
structure, whose form is symplectic, the stable subspace at a nondegenerate critical point is
thus isotropic, and its dimension, the Morse index, is at most half the dimension of the
manifold.

## Main results

* `TauCeti.exists_pos_mul_norm_sq_add_norm_sq_le_fderiv_fderiv`: at any critical point `p` of a
  function `f` that is `C²` in the chart, if `X` is differentiable at `p` and satisfies the
  gradient-like inequality near `p`, there is `c > 0` with
  `c * (‖A v‖ ^ 2 + ‖B v‖ ^ 2) ≤ B v (A v)` for every `v`, where `B` is the second derivative of
  `f` in the chart.
* `TauCeti.IsGradientLike.exists_pos_mul_norm_sq_le_hessian`: there is `c > 0` with
  `c * ‖v‖ ^ 2 ≤ H v (A v)` for every `v`.
* `TauCeti.IsGradientLike.exists_projection_exponential_bounds`: the flow of `A` has an
  exponential dichotomy.
* `TauCeti.IsGradientLike.finrank_stableSubspace_eq_manifoldMorseIndex` and
  `TauCeti.IsGradientLike.finrank_range_eq_manifoldMorseIndex`: the stable subspace of `A`, which
  is the range of the projection of any such dichotomy, has dimension the Morse index of `f` at
  `p`.
* `TauCeti.IsGradientLike.exists_continuousLinearEquiv_stableSubspace`: at a critical point of
  index `m`, a continuous linear equivalence `L` from `EuclideanSpace ℝ (Fin m)` onto the stable
  subspace of `A` with `-H (L u) (L u) = ‖u‖ ^ 2`.
* `TauCeti.IsLiouvilleVectorField.apply_eq_zero_of_mem_stableSubspace`: at a zero of a Liouville
  field, the form vanishes on the stable subspace of the linearization.
* `SymplecticGeometry.IsWeinsteinStructure.two_mul_manifoldMorseIndex_le`: at a nondegenerate
  critical point of a Weinstein structure, twice the Morse index is at most the dimension.

In the dichotomy and index statements `A : E →L[ℝ] E` comes with a hypothesis
`A = sectionLinearization …`, since the linearization itself is a map between tangent spaces,
which carry no norm.

## Implementation notes

The metric `g` of the gradient-like condition is only continuous in the chart, so it is compared
with its value at `p`. For a fixed vector `e` of the chart, the Cauchy–Schwarz inequality
`(df e) ^ 2 ≤ ‖grad f‖ ^ 2 * g(e, e)`, together with a bound on the differential of the chart for
the norm of `g` (Mathlib's `eventually_norm_mfderiv_extChartAt_lt`), gives near `p` an inequality
`κ * (‖X u‖ ^ 2 + (df_u e) ^ 2) ≤ df_u (X u)` in the chart, with `κ > 0` independent of `e` for
`‖e‖ ≤ 1`. It passes to second order by
`HasFDerivAt.mul_norm_sq_add_sq_apply_le_apply_apply_of_eventually`, and a choice of `e` at which
`B v` is close to its norm makes the bound uniform in `v`. Nondegeneracy is not needed for this; at
a nondegenerate critical point, the invertibility of the Hessian then bounds `‖v‖` by `‖H v‖`.

The Hessian `H` is then a symmetric bilinear Lyapunov form for `A`, and the dichotomy and the
index come from `ContinuousLinearMap.exists_projection_exponential_bounds_of_le_apply` and
`ContinuousLinearMap.sigNeg_toQuadraticMap_eq_finrank_stableSubspace`, which transfer Tau Ceti's
inertia theorem to bilinear forms on a normed space.

The Euclidean coordinate on the stable subspace is
`QuadraticMap.PosDef.exists_continuousLinearEquiv_euclideanSpace` applied to `-H`, which is
positive definite there by `ContinuousLinearMap.apply_self_neg_of_mem_stableSubspace`.

## References

* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  Lemma 9.9, for the splitting of the linearization and the sign of the Hessian on its parts;
  Proposition 9.23 (a), whose proof uses the second-order inequality at a critical point that
  need not be nondegenerate;
  Proposition 11.9 (a), for the isotropy of the stable subspace, and the dimension bound stated
  after its parts
-/

public section

open Bundle Filter Module NormedSpace Set VectorField TauCeti.Manifold
open scoped ContDiff Manifold NNReal Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}

/-- The local gradient-like inequality near `p`, for a metric `g` and a constant `c > 0`, read in
the chart at `p` against a vector `e` of the chart with `‖e‖ ≤ 1`: with `Y` the field in the chart
and a constant `κ > 0` that does not depend on `e`, `κ * (‖Y u‖ ^ 2 + (df_u e) ^ 2) ≤ df_u (Y u)`
near the image of `p`, when `f` is differentiable there in the chart. -/
private theorem exists_eventually_mul_norm_sq_add_sq_le {p : M}
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)) {c : ℝ}
    (hc : 0 < c)
    (hg : letI : RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) := ⟨g.toRiemannianMetric⟩
      ∀ᶠ y in 𝓝 p, c * (g.inner y (X y) (X y) + ‖mgradient 𝓘(ℝ, E) f y‖ ^ 2) ≤
        mvfderiv 𝓘(ℝ, E) f y (X y))
    (hF : ∀ᶠ u in 𝓝 (extChartAt 𝓘(ℝ, E) p p),
      DifferentiableAt ℝ (f ∘ (extChartAt 𝓘(ℝ, E) p).symm) u)
    {Y : E → E} (hY : Y = VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) p).symm X) :
    ∃ κ > 0, ∀ e : E, ‖e‖ ≤ 1 → ∀ᶠ u in 𝓝 (extChartAt 𝓘(ℝ, E) p p),
      κ * (‖Y u‖ ^ 2 + fderiv ℝ (f ∘ (extChartAt 𝓘(ℝ, E) p).symm) u e ^ 2) ≤
        fderiv ℝ (f ∘ (extChartAt 𝓘(ℝ, E) p).symm) u (Y u) := by
  let : RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) := ⟨g.toRiemannianMetric⟩
  have : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := 𝓘(ℝ, E)) (n := ∞)
  set φ := extChartAt 𝓘(ℝ, E) p
  -- A bound for the differential of the chart, for the norm of `g` on the tangent spaces.
  obtain ⟨C, hC, hCφ⟩ := eventually_norm_mfderiv_extChartAt_lt 𝓘(ℝ, E) p
  set G₀ : E →L[ℝ] E →L[ℝ] ℝ := g.inner p
  set N := ‖G₀‖
  refine ⟨c / (C ^ 2 + N + 1), by positivity, fun e he ↦ ?_⟩
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
  have hnear := hg.and ((hgW.eventually (gt_mem_nhds hgWp)).and hCφ)
  have hsymm : Tendsto φ.symm (𝓝 (φ p)) (𝓝 p) := by
    have := continuousAt_extChartAt_symm (I := 𝓘(ℝ, E)) p
    rwa [ContinuousAt, extChartAt_to_inv] at this
  filter_upwards [hsymm.eventually hnear, hF, extChartAt_target_mem_nhds (I := 𝓘(ℝ, E)) p]
    with u ⟨hgy, hWu, hCy⟩ hFu hu
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
  have hXY : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ y (X y) = Y u := by
    rw [← hφy, hY]
    exact (VectorField.mpullback_extChartAt_symm_apply_eq_mfderiv X hys (by simp)).symm
  -- The field in the chart is bounded by its length for `g`.
  have hYu : ‖Y u‖ ^ 2 ≤ C ^ 2 * g.inner y (X y) (X y) := by
    let := normedAddCommGroupTangentSpaceVectorSpace (E := E)
    let := normedSpaceTangentSpaceVectorSpace (E := E)
    have h₁ := ((mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ y).le_opNorm (X y)).trans
      (mul_le_mul_of_nonneg_right hCy.le (norm_nonneg _))
    rw [← hXY, ← g.norm_sq y (X y)]
    exact (pow_le_pow_left₀ (norm_nonneg _) h₁ 2).trans_eq (mul_pow _ _ _)
  rw [← hWe, ← hXY, ← hdf, ← hdf, hXY]
  -- The Cauchy–Schwarz inequality for the gradient `G` of `f` at `y`.
  set G := mgradient 𝓘(ℝ, E) f y
  have hcs : mvfderiv 𝓘(ℝ, E) f y (W y) ^ 2 ≤ ‖G‖ ^ 2 * g.inner y (W y) (W y) := by
    rw [← inner_mgradient, ← g.inner_eq, ← real_inner_self_eq_norm_sq, sq]
    exact real_inner_mul_inner_self_le G (W y)
  have hXX : 0 ≤ g.inner y (X y) (X y) := g.toRiemannianMetric.inner_self_nonneg y (X y)
  have hN : 0 ≤ N := norm_nonneg G₀
  have hG : 0 ≤ ‖G‖ ^ 2 := sq_nonneg _
  calc c / (C ^ 2 + N + 1) * (‖Y u‖ ^ 2 + mvfderiv 𝓘(ℝ, E) f y (W y) ^ 2)
      ≤ c / (C ^ 2 + N + 1) * ((C ^ 2 + N + 1) * (g.inner y (X y) (X y) + ‖G‖ ^ 2)) := by
        gcongr
        nlinarith [hcs.trans (mul_le_mul_of_nonneg_left hWu.le hG), sq_nonneg C]
    _ = c * (g.inner y (X y) (X y) + ‖G‖ ^ 2) := by field_simp
    _ ≤ _ := hgy

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
  obtain ⟨U, hU, g, c, hc, hg⟩ := (isGradientLikeAt_def f X p).1 hX
  set φ := extChartAt 𝓘(ℝ, E) p
  set Y : E → E := VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) φ.symm X
  set B := fderiv ℝ (fderiv ℝ (f ∘ φ.symm)) (φ p)
  have hF : ∀ᶠ u in 𝓝 (φ p), DifferentiableAt ℝ (f ∘ φ.symm) u :=
    hf.eventually_differentiableAt (by simp)
  obtain ⟨κ, hκ, hev⟩ :=
    exists_eventually_mul_norm_sq_add_sq_le g hc (Filter.mem_of_superset hU hg) hF (Y := Y) rfl
  have hB : HasFDerivAt (fderiv ℝ (f ∘ φ.symm)) B (φ p) := hf.hasFDerivAt_fderiv le_rfl
  have hD₀ : fderiv ℝ (f ∘ φ.symm) (φ p) = 0 :=
    fderiv_comp_extChartAt_symm_eq_zero_of_mem_criticalPoints hp
  have hY : HasFDerivAt Y A (φ p) := hA ▸ hXp.hasFDerivAt_mpullback_extChartAt_symm
  have hY₀ : Y (φ p) = 0 := (VectorField.mpullback_extChartAt_symm_self X p).trans hX₀
  -- The inequality at second order, for each `e` with `‖e‖ ≤ 1`.
  have hBe (v e : E) (he : ‖e‖ ≤ 1) : κ * (‖A v‖ ^ 2 + B v e ^ 2) ≤ B v (A v) :=
    hB.mul_norm_sq_add_sq_apply_le_apply_apply_of_eventually hD₀ hY hY₀ (hev e he) v
  refine ⟨κ / 8, by positivity, fun v ↦ ?_⟩
  -- The norm of `B v` is attained, up to a factor `2`, at a vector of norm at most `1`.
  have hBv : κ * (‖A v‖ ^ 2 + ‖B v‖ ^ 2 / 4) ≤ B v (A v) := by
    rcases eq_or_ne (B v) 0 with h0 | h0
    · simpa [h0] using hBe v 0 (by simp)
    obtain ⟨e, he, hlt⟩ := (B v).exists_lt_apply_of_lt_opNorm (half_lt_self (norm_pos_iff.2 h0))
    rw [Real.norm_eq_abs] at hlt
    refine le_trans ?_ (hBe v e he.le)
    gcongr
    nlinarith [norm_nonneg (B v), abs_nonneg (B v e), sq_abs (B v e)]
  nlinarith [sq_nonneg ‖A v‖, sq_nonneg ‖B v‖]

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

/-! ### Isotropy of the stable subspace at a zero of a Liouville field -/

section Liouville

variable {H N : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I 1 N]

omit [FiniteDimensional ℝ E] in
/-- **The stable subspace at a zero of a Liouville field is isotropic.** Let `Z` be a Liouville
vector field of a two-form `σ` on a boundaryless manifold, let `p` be a zero of `Z`, and let `A`
be the linearization of `Z` at `p`. Then `σ_p (u, v) = 0` for all `u`, `v` in the stable
subspace of `A`. -/
theorem IsLiouvilleVectorField.apply_eq_zero_of_mem_stableSubspace [CompleteSpace E]
    {σ : RoughForm I N ℝ 2} {Z : (x : N) → TangentSpace I x} (hZ : IsLiouvilleVectorField σ Z)
    {p : N} (hp : Z p = 0) {A : E →L[ℝ] E} (hA : A = sectionLinearization (F := E) I id Z p)
    {u v : E} (hu : u ∈ A.stableSubspace) (hv : v ∈ A.stableSubspace) : σ p ![u, v] = 0 := by
  subst hA
  -- The value of `σ` at `p`, an alternating map on the tangent space `E` at `p`.
  let σ₀ : E [⋀^Fin 2]→L[ℝ] ℝ := σ p
  have hB (u v : E) : ContinuousAlternatingMap.flatL ℝ E ℝ σ₀ u v = σ p ![u, v] :=
    ContinuousAlternatingMap.flatL_apply_apply σ₀ u v
  rw [← hB]
  refine ContinuousLinearMap.apply_eq_zero_of_mem_stableSubspace (fun u v ↦ ?_) hu hv
  simp only [hB]
  exact hZ.apply_sectionLinearization_add hp u v

end Liouville

end TauCeti

/-! ### The index bound for a Weinstein structure -/

namespace SymplecticGeometry

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {σ : SmoothTwoForm 𝓘(ℝ, E) M} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x} {f : M → ℝ}

/-- **The index bound for a Weinstein structure.** At a nondegenerate critical point `p` of the
function of a Weinstein structure on a manifold modelled on `E`, twice the Morse index is at most
`dim E`: the stable subspace of the linearization of the field at `p` is isotropic for the
symplectic form, and has dimension the Morse index. -/
theorem IsWeinsteinStructure.two_mul_manifoldMorseIndex_le (hW : IsWeinsteinStructure σ X f)
    {p : M} (hp : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f p) :
    2 * manifoldMorseIndex 𝓘(ℝ, E) f p ≤ finrank ℝ E := by
  have hXp := hW.mdifferentiableAt_field p
  have hp0 : X p = 0 := hW.isGradientLike.eq_zero_iff.2 hp.mem_criticalPoints
  rw [← hW.isGradientLike.finrank_stableSubspace_eq_manifoldMorseIndex hp hXp rfl]
  refine LinearMap.BilinForm.two_mul_finrank_le_finrank_of_le_orthogonal
    (hW.isSymplectic.isNondegenerate.nondegenerate_bilinFormAt p) fun w hw ↦
      LinearMap.BilinForm.mem_orthogonal_iff.2 fun v hv ↦ ?_
  rw [SmoothForm.bilinFormAt_apply, SmoothBundleForm.eval₂_apply]
  exact hW.isLiouvilleVectorField.apply_eq_zero_of_mem_stableSubspace hp0 rfl hv hw

end SymplecticGeometry
