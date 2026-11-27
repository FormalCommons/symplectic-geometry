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
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic
import TauCeti.Geometry.Manifold.VectorField.Chart.Linearization
import TauCeti.Geometry.Manifold.VectorField.Regularity
import TauCeti.Topology.VectorBundle.Riemannian.Basic
import SymplecticGeometry.Analysis.Calculus.FDeriv.SecondOrder
import SymplecticGeometry.Analysis.ODE.LyapunovBilinForm
import TauCeti.Analysis.ODE.ExponentialDichotomy
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.LieDeriv

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

At a zero `p` of a Liouville vector field `Z` of a two-form `σ`, the condition `L_Z σ = σ`, read
at `p`, says that the linearization `A` of `Z` satisfies `σ_p (A u, v) + σ_p (u, A v) = σ_p (u, v)`.
The Lie derivative at a zero of the field involves only the derivative of the field
(`TauCeti.mlieDerivForm_apply_of_eq_zero`), so no regularity of `Z` or `σ` is needed.

## Main results

* `TauCeti.IsGradientLike.exists_pos_mul_norm_sq_le_hessian`: there is `c > 0` with
  `c * ‖v‖ ^ 2 ≤ H v (A v)` for every `v`.
* `TauCeti.IsGradientLike.exists_projection_exponential_bounds`: the flow of `A` has an
  exponential dichotomy.
* `TauCeti.IsGradientLike.finrank_stableSubspace_eq_manifoldMorseIndex` and
  `TauCeti.IsGradientLike.finrank_range_eq_manifoldMorseIndex`: the stable subspace of `A`, which
  is the range of the projection of any such dichotomy, has dimension the Morse index of `f` at
  `p`.
* `TauCeti.IsLiouvilleVectorField.apply_sectionLinearization_add`: the linearized Liouville
  identity at a zero of a Liouville field.

In the dichotomy and index statements `A : E →L[ℝ] E` comes with a hypothesis
`A = sectionLinearization …`, since the linearization itself is a map between tangent spaces,
which carry no norm.

## Implementation notes

The metric `g` and the function `δ` of the gradient-like condition are only continuous in the
chart, so they are compared with their values at `p`. For a fixed vector `e` of the chart, the
Cauchy–Schwarz inequality `(df e) ^ 2 ≤ ‖grad f‖ ^ 2 * g(e, e)` gives near `p` an inequality
`κ * (df_u e) ^ 2 ≤ df_u (X u)` in the chart, with `κ > 0` independent of `e` for `‖e‖ ≤ 1`. It
passes to second order by `HasFDerivAt.mul_sq_apply_le_apply_apply_of_eventually`, and the
invertibility of the Hessian makes the resulting bound uniform in `v`.

The Hessian `H` is then a symmetric bilinear Lyapunov form for `A`, and the dichotomy and the
index come from `ContinuousLinearMap.exists_projection_exponential_bounds_of_le_apply` and
`ContinuousLinearMap.sigNeg_toQuadraticMap_eq_finrank_stableSubspace`, which transfer Tau Ceti's
inertia theorem to bilinear forms on a normed space.

## References

* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  Chapter 11
-/

public section

open Bundle Filter Module NormedSpace Set VectorField TauCeti.Manifold
open scoped ContDiff Manifold NNReal Topology

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
    rwa [𝓘(ℝ, E).range_eq_univ, VectorField.mpullbackWithin_univ] at this
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

/-! ### The Liouville identity at a zero -/

section Liouville

variable {H N : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I 1 N]

omit [FiniteDimensional ℝ E] in
/-- **The linearized Liouville identity.** Let `Z` be a Liouville vector field of a two-form `σ`
(`L_Z σ = σ`) on a boundaryless manifold, and let `p` be a zero of `Z`, with linearization `A`.
Then `σ_p (A u, v) + σ_p (u, A v) = σ_p (u, v)` for all tangent vectors `u`, `v` at `p`: the
Lie derivative at a zero of the field is read off its linearization. -/
theorem IsLiouvilleVectorField.apply_sectionLinearization_add {σ : RoughForm I N ℝ 2}
    {Z : (x : N) → TangentSpace I x} (hZ : IsLiouvilleVectorField σ Z) {p : N} (hp : Z p = 0)
    (u v : TangentSpace I p) :
    σ p ![sectionLinearization (F := E) I id Z p u, v] +
        σ p ![u, sectionLinearization (F := E) I id Z p v] = σ p ![u, v] := by
  conv_rhs => rw [← isLiouvilleVectorField_iff.1 hZ]
  rw [mlieDerivForm_apply_of_eq_zero hp, Fin.sum_univ_two,
    sectionLinearization_apply_eq_vectorFieldChartDerivative,
    sectionLinearization_apply_eq_vectorFieldChartDerivative]
  -- Each entry of the updated pairs is computed by `Function.update` on `Fin 2`; the entries are
  -- tangent vectors at `p`, which `simp` does not match against vectors of `E`.
  congr 2 <;> funext i <;> fin_cases i <;> rfl

end Liouville

end TauCeti
