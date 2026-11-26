/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Sphere
public import SymplecticGeometry.Geometry.Manifold.Degree.Global
public import TauCeti.Geometry.Manifold.Orientation.Sphere
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import TauCeti.Analysis.InnerProductSpace.Reflection
import TauCeti.Geometry.Diffeomorphism.Sphere
import TauCeti.Geometry.Manifold.ContMDiff.ChartCutoff
import TauCeti.Geometry.Manifold.MFDeriv.Basic
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic
import TauCeti.Geometry.Sphere.Connected

/-!
# A map of degree one onto the sphere

Every compact nonempty Hausdorff manifold `M` of dimension `n ≥ 1`, modelled on `ℝⁿ`, with
an orientation, has a smooth map to the unit sphere `Sⁿ` of an oriented real inner product
space of dimension `n + 1` whose mapping degree `TauCeti.degree` is `1`, for the
outward-normal orientation `o.sphereOrientation` of the sphere
(`SymplecticGeometry.exists_contMDiff_degree_eq_one`). In particular every closed oriented
surface maps with degree one onto `S²`.

The map collapses the complement of a small coordinate ball onto a point. Fix a unit vector `v`,
a linear isometry `J` of `ℝⁿ` onto `v^⊥`, and a smooth cut-off `a : ℝⁿ → [0, ∞)`, a function of
`‖w‖²` that is positive for `‖w‖² < ε` and vanishes for `‖w‖² ≥ ε`. Then
`w ↦ (a² + ‖w‖²)⁻¹ (2a J w + (a² - ‖w‖²) v)` is smooth with values in the sphere; where
`a > 0` it is the inverse stereographic projection from `-v` of `2 J w / a`. It takes the
value `-v` where `a = 0` and the value `v` only at `w = 0`, where its derivative is
`(2 / a(0)) J`. Read in a chart of `M` around a point `x₀` and extended by `-v` off the chart,
it is a smooth map `M → Sⁿ` whose fibre over `v` is `{x₀}`, with invertible derivative at
`x₀`. So `v` is a regular value and the degree is the orientation sign at `x₀`, which is `1`
or `-1` (`TauCeti.degree_eq_orientationSign_of_preimage_eq_singleton`). In the second case a
reflection of the sphere, which reverses its orientation
(`Orientation.isOrientationReversingAt_unitSphereEquiv`), turns the map into one of degree `1`.

## Main results

* `SymplecticGeometry.exists_contMDiff_degree_eq_one`: a compact nonempty Hausdorff oriented
  manifold of dimension `n ≥ 1` has a smooth map of degree one to `Sⁿ`.

## References

* J. W. Milnor, *Topology from the Differentiable Viewpoint*, University Press of Virginia, 1965,
  §5 and §7.
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 17, section Degree Theory.
-/

public section

open Function Metric Module Set
open scoped ContDiff Manifold Topology RealInnerProductSpace

namespace SymplecticGeometry

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-! ### The model collapse onto the sphere -/

section Model

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The cut-off `s ↦ exp(-1/(ε - s))`, positive for `s < ε` and zero for `s ≥ ε`, as a function
of `s = ‖w‖²`. -/
private noncomputable def cutoff (ε s : ℝ) : ℝ :=
  expNegInvGlue (ε - s)

/-- The coefficient of `J w` in the model collapse, as a function of `s = ‖w‖²`. -/
private noncomputable def coeffJ (ε s : ℝ) : ℝ :=
  (cutoff ε s ^ 2 + s)⁻¹ * (2 * cutoff ε s)

/-- The coefficient of `v` in the model collapse, as a function of `s = ‖w‖²`. -/
private noncomputable def coeffV (ε s : ℝ) : ℝ :=
  (cutoff ε s ^ 2 + s)⁻¹ * (cutoff ε s ^ 2 - s)

/-- The model collapse `w ↦ (a² + ‖w‖²)⁻¹ (2a J w + (a² - ‖w‖²) v)`, with `a` the cut-off of
`‖w‖²`. -/
private noncomputable def collapse (J : V →ₗᵢ[ℝ] F) (v : F) (ε : ℝ) (w : V) : F :=
  coeffJ ε (‖w‖ ^ 2) • J w + coeffV ε (‖w‖ ^ 2) • v

private theorem contDiff_cutoff (ε : ℝ) : ContDiff ℝ ∞ (cutoff ε) :=
  expNegInvGlue.contDiff.comp (contDiff_const.sub contDiff_id)

private theorem cutoff_sq_add_pos {ε : ℝ} (hε : 0 < ε) {s : ℝ} (hs : 0 ≤ s) :
    0 < cutoff ε s ^ 2 + s := by
  rcases hs.eq_or_lt with rfl | hs
  · simpa [cutoff] using pow_pos (expNegInvGlue.pos_of_pos hε) 2
  · positivity

private theorem contDiff_collapse (J : V →ₗᵢ[ℝ] F) (v : F) {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ ∞ (collapse J v ε) := by
  have ha : ContDiff ℝ ∞ fun w : V ↦ cutoff ε (‖w‖ ^ 2) :=
    (contDiff_cutoff ε).comp (contDiff_norm_sq ℝ)
  have hd : ContDiff ℝ ∞ fun w : V ↦ (cutoff ε (‖w‖ ^ 2) ^ 2 + ‖w‖ ^ 2)⁻¹ :=
    ((ha.pow 2).add (contDiff_norm_sq ℝ)).inv fun w ↦
      (cutoff_sq_add_pos hε (sq_nonneg ‖w‖)).ne'
  exact ((hd.mul (contDiff_const.mul ha)).smul J.toContinuousLinearMap.contDiff).add
    ((hd.mul ((ha.pow 2).sub (contDiff_norm_sq ℝ))).smul contDiff_const)

variable {J : V →ₗᵢ[ℝ] F} {v : F} {ε : ℝ}

private theorem norm_collapse (hv : ‖v‖ = 1) (hJv : ∀ w, ⟪J w, v⟫ = 0) (hε : 0 < ε) (w : V) :
    ‖collapse J v ε w‖ = 1 := by
  have hpos := cutoff_sq_add_pos hε (sq_nonneg ‖w‖)
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_real
    (x := coeffJ ε (‖w‖ ^ 2) • J w) (y := coeffV ε (‖w‖ ^ 2) • v)
    (by rw [real_inner_smul_left, real_inner_smul_right, hJv, mul_zero, mul_zero])
  rw [← collapse, norm_smul, norm_smul, J.norm_map, hv, Real.norm_eq_abs, Real.norm_eq_abs] at h
  have h1 : ‖collapse J v ε w‖ * ‖collapse J v ε w‖ = 1 := by
    rw [h, mul_one, mul_mul_mul_comm, abs_mul_abs_self, abs_mul_abs_self, coeffJ, coeffV]
    field_simp
    ring
  nlinarith [norm_nonneg (collapse J v ε w)]

private theorem collapse_of_le (hε : 0 < ε) {w : V} (hw : ε ≤ ‖w‖ ^ 2) :
    collapse J v ε w = -v := by
  have h0 : cutoff ε (‖w‖ ^ 2) = 0 := expNegInvGlue.zero_of_nonpos (by linarith)
  have hs : ‖w‖ ^ 2 ≠ 0 := (hε.trans_le hw).ne'
  rw [collapse, coeffJ, coeffV, h0]
  simp [hs]

private theorem collapse_eq_iff (hv : ‖v‖ = 1) (hJv : ∀ w, ⟪J w, v⟫ = 0) (hε : 0 < ε) {w : V} :
    collapse J v ε w = v ↔ w = 0 := by
  have hpos := cutoff_sq_add_pos hε (sq_nonneg ‖w‖)
  refine ⟨fun h ↦ ?_, ?_⟩
  · have hi := congrArg (fun z ↦ ⟪z, v⟫) h
    simp only [collapse, inner_add_left, real_inner_smul_left, hJv, mul_zero, zero_add,
      real_inner_self_eq_norm_sq, hv, one_pow, mul_one, coeffV] at hi
    rw [inv_mul_eq_one₀ hpos.ne'] at hi
    have : ‖w‖ ^ 2 = 0 := by linarith
    simpa using this
  · rintro rfl
    have h0 := cutoff_sq_add_pos hε le_rfl
    rw [add_zero] at h0
    simp [collapse, coeffV, h0.ne']

private theorem hasFDerivAt_collapse (hε : 0 < ε) :
    HasFDerivAt (collapse J v ε) (coeffJ ε 0 • J.toContinuousLinearMap) 0 := by
  -- The coefficients are functions of `‖w‖²`, whose derivative vanishes at `0`.
  have hsq : HasFDerivAt (fun w : V ↦ ‖w‖ ^ 2) (0 : V →L[ℝ] ℝ) 0 := by
    simpa using (hasStrictFDerivAt_norm_sq (0 : V)).hasFDerivAt
  have hpt : ‖(0 : V)‖ ^ 2 = 0 := by simp
  have hd0 : cutoff ε 0 ^ 2 + 0 ≠ 0 := (cutoff_sq_add_pos hε le_rfl).ne'
  have hc : Differentiable ℝ (cutoff ε) := (contDiff_cutoff ε).differentiable (by simp)
  have hJ : DifferentiableAt ℝ (coeffJ ε) (‖(0 : V)‖ ^ 2) := by
    rw [hpt]
    exact (((hc 0).pow 2).add differentiableAt_id).inv hd0 |>.mul ((hc 0).const_mul 2)
  have hV : DifferentiableAt ℝ (coeffV ε) (‖(0 : V)‖ ^ 2) := by
    rw [hpt]
    exact (((hc 0).pow 2).add differentiableAt_id).inv hd0 |>.mul
      (((hc 0).pow 2).sub differentiableAt_id)
  have h := ((hJ.hasDerivAt.comp_hasFDerivAt (0 : V) hsq).smul
    J.toContinuousLinearMap.hasFDerivAt).add
    ((hV.hasDerivAt.comp_hasFDerivAt (0 : V) hsq).smul_const v)
  -- `collapse` is, by definition, the sum that `h` differentiates.
  convert h using 1
  · rfl
  · simp

end Model

/-! ### The collapse of a manifold onto the sphere -/

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

/-- The model collapse read in the chart `e` at `x₀`, centred at `e x₀`, with cut-off radius
`r / 2`, and extended by `-v` off the source of the chart. -/
private noncomputable def chartCollapse (J : EuclideanSpace ℝ (Fin n) →ₗᵢ[ℝ] F) (v : F) (x₀ : M)
    (r : ℝ) (x : M) : F :=
  open scoped Classical in
  if x ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x₀).source then
    collapse J v ((r / 2) ^ 2) (extChartAt (𝓡 n) x₀ x - extChartAt (𝓡 n) x₀ x₀)
  else -v

variable {J : EuclideanSpace ℝ (Fin n) →ₗᵢ[ℝ] F} {v : F} {x₀ : M} {r : ℝ}

private theorem chartCollapse_of_mem {x : M}
    (hx : x ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x₀).source) :
    chartCollapse J v x₀ r x =
      collapse J v ((r / 2) ^ 2) (extChartAt (𝓡 n) x₀ x - extChartAt (𝓡 n) x₀ x₀) :=
  ite_eq_left hx

private theorem chartCollapse_of_notMem {x : M}
    (hx : x ∉ (chartAt (EuclideanSpace ℝ (Fin n)) x₀).source) :
    chartCollapse J v x₀ r x = -v :=
  ite_eq_right hx

private theorem norm_chartCollapse (hv : ‖v‖ = 1) (hJv : ∀ w, ⟪J w, v⟫ = 0) (hr : 0 < r)
    (x : M) : ‖chartCollapse J v x₀ r x‖ = 1 := by
  by_cases hx : x ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x₀).source
  · rw [chartCollapse_of_mem hx]
    exact norm_collapse hv hJv (by positivity) _
  · rwa [chartCollapse_of_notMem hx, norm_neg]

private theorem chartCollapse_eq_iff (hv : ‖v‖ = 1) (hJv : ∀ w, ⟪J w, v⟫ = 0) (hr : 0 < r)
    {x : M} : chartCollapse J v x₀ r x = v ↔ x = x₀ := by
  by_cases hx : x ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x₀).source
  · rw [chartCollapse_of_mem hx, collapse_eq_iff hv hJv (by positivity), sub_eq_zero]
    exact ⟨fun h ↦ (extChartAt (𝓡 n) x₀).injOn (by rwa [extChartAt_source])
      (mem_extChartAt_source x₀) h, fun h ↦ h ▸ rfl⟩
  · rw [chartCollapse_of_notMem hx]
    refine iff_of_false (fun h ↦ ?_) fun h ↦ hx (by subst h; exact mem_chart_source _ _)
    have hi := congrArg (fun z ↦ ⟪z, v⟫) h
    simp only [inner_neg_left, real_inner_self_eq_norm_sq, hv] at hi
    norm_num at hi

variable [T2Space M] [IsManifold (𝓡 n) ∞ M]

private theorem contMDiff_chartCollapse (hr : 0 < r)
    (hball : ball (extChartAt (𝓡 n) x₀ x₀) r ⊆ (extChartAt (𝓡 n) x₀).target) :
    ContMDiff (𝓡 n) 𝓘(ℝ, F) ∞ (chartCollapse J v x₀ r) := by
  set c := extChartAt (𝓡 n) x₀ x₀
  -- The model collapse centred at `c` is `-v` outside the closed ball of radius `r / 2`.
  have hc (z : EuclideanSpace ℝ (Fin n)) (hz : r / 2 < dist z c) :
      collapse J v ((r / 2) ^ 2) (z - c) = -v := by
    rw [dist_eq_norm] at hz
    exact collapse_of_le (by positivity) (pow_le_pow_left₀ (by positivity) hz.le 2)
  obtain ⟨f, hf, hfs, hfc⟩ := TauCeti.Manifold.exists_contMDiff_eq_comp_extChartAt x₀
    (g := fun z ↦ collapse J v ((r / 2) ^ 2) (z - c))
    ((closedBall_subset_ball (by linarith)).trans hball)
    ((contDiff_collapse J v (by positivity)).comp (contDiff_id.sub contDiff_const)).contMDiff hc
  refine hf.congr fun x ↦ ?_
  by_cases hx : x ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x₀).source
  · rw [chartCollapse_of_mem hx]
    exact (hfs x hx).symm
  · rw [chartCollapse_of_notMem hx, hfc x hx]

omit [T2Space M] [IsManifold (𝓡 n) ∞ M] in
/-- The derivative of the chart collapse at the centre `x₀` is injective: in the chart it is a
nonzero multiple of `J`. -/
private theorem injective_mfderiv_chartCollapse (hr : 0 < r) :
    Injective (mfderiv (𝓡 n) 𝓘(ℝ, F) (chartCollapse J v x₀ r) x₀) := by
  set c := extChartAt (𝓡 n) x₀ x₀
  have hε : 0 < (r / 2) ^ 2 := by positivity
  have h1 : HasFDerivAt (fun z ↦ collapse J v ((r / 2) ^ 2) (z - c))
      (coeffJ ((r / 2) ^ 2) 0 • J.toContinuousLinearMap) c := by
    have h2 : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin n) ↦ z - c)
        (ContinuousLinearMap.id ℝ _) c := (hasFDerivAt_id c).sub_const c
    have h3 := hasFDerivAt_collapse (J := J) (v := v) hε
    rw [← sub_self c] at h3
    exact h3.comp (f := fun z ↦ z - c) c h2
  have hD : HasMFDerivAt (𝓡 n) 𝓘(ℝ, F) (chartCollapse J v x₀ r) x₀
      (coeffJ ((r / 2) ^ 2) 0 • J.toContinuousLinearMap) :=
    (h1.hasMFDerivAt.comp x₀ (TauCeti.hasMFDerivAt_extChartAt_self x₀)).congr_of_eventuallyEq
      (Filter.eventually_of_mem ((chartAt _ x₀).open_source.mem_nhds (mem_chart_source _ x₀))
        fun y hy ↦ chartCollapse_of_mem hy)
  have hcoeff : coeffJ ((r / 2) ^ 2) 0 ≠ 0 := by
    have := expNegInvGlue.pos_of_pos hε
    simp only [coeffJ, cutoff, sub_zero, add_zero]
    positivity
  rw [hD.mfderiv]
  exact fun a b hab ↦ J.injective (smul_right_injective F hcoeff hab)

variable [Fact (finrank ℝ F = n + 1)]

/-- A point `x₀` of a manifold modelled on `ℝⁿ` and a unit vector `v` of a space of dimension
`n + 1` give a smooth map to the unit sphere whose fibre over `v` is `{x₀}`, with invertible
derivative at `x₀`. -/
private theorem exists_contMDiff_preimage_eq_singleton (x₀ : M) {v : F} (hv : ‖v‖ = 1) :
    ∃ f : M → sphere (0 : F) 1, ContMDiff (𝓡 n) (𝓡 n) ∞ f ∧
      f ⁻¹' {⟨v, by simpa using hv⟩} = {x₀} ∧ (mfderiv (𝓡 n) (𝓡 n) f x₀).IsInvertible := by
  have hv0 : v ≠ 0 := by rintro rfl; simp at hv
  -- A linear isometry of `ℝⁿ` onto `v^⊥`.
  let J : EuclideanSpace ℝ (Fin n) →ₗᵢ[ℝ] F := (ℝ ∙ v)ᗮ.subtypeₗᵢ.comp
    (OrthonormalBasis.fromOrthogonalSpanSingleton n hv0).repr.symm.toLinearIsometry
  have hJv (w : EuclideanSpace ℝ (Fin n)) : ⟪J w, v⟫ = 0 := by
    rw [real_inner_comm]
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.1 (Submodule.coe_mem _)
  -- A ball of radius `r` around `e x₀` in the target of the chart `e` at `x₀`.
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1
    ((isOpen_extChartAt_target (I := 𝓡 n) x₀).mem_nhds (mem_extChartAt_target (I := 𝓡 n) x₀))
  have hG := contMDiff_chartCollapse (J := J) (v := v) hr hball
  have hGsph (x : M) : chartCollapse J v x₀ r x ∈ sphere (0 : F) 1 :=
    mem_sphere_zero_iff_norm.2 (norm_chartCollapse hv hJv hr x)
  refine ⟨codRestrict _ _ hGsph, hG.codRestrict_sphere hGsph, ?_, ?_⟩
  · ext x
    rw [mem_preimage, mem_singleton_iff, Subtype.ext_iff, val_codRestrict_apply,
      chartCollapse_eq_iff hv hJv hr, mem_singleton_iff]
  · have hinj := injective_mfderiv_chartCollapse (J := J) (v := v) (x₀ := x₀) hr
    have hcomp : chartCollapse J v x₀ r = Subtype.val ∘ codRestrict _ _ hGsph :=
      funext fun x ↦ (val_codRestrict_apply _ _ hGsph x).symm
    rw [hcomp] at hinj
    exact (TauCeti.isRegularPoint_iff_isInvertible_mfderiv rfl).1
      ((TauCeti.isRegularPoint_iff_injective_mfderiv rfl).2
        (TauCeti.injective_mfderiv_of_injective_mfderiv_comp
          ((contMDiff_coe_sphere (m := ∞) (n := n)).mdifferentiable (by simp) _)
          ((hG.codRestrict_sphere hGsph).mdifferentiable (by simp) x₀) hinj))

variable [CompactSpace M] [Nonempty M]

/-- **A map of degree one onto the sphere.** A compact nonempty Hausdorff manifold `M` of
dimension `n ≥ 1`, modelled on `ℝⁿ` and oriented by `o`, has a smooth map to the unit sphere of
an oriented real inner product space of dimension `n + 1` whose degree is `1`, for the
outward-normal orientation `o'.sphereOrientation` of the sphere. -/
theorem exists_contMDiff_degree_eq_one [NeZero n] (o : TauCeti.Manifold.Orientation (𝓡 n) M (Fin n))
    (o' : Orientation ℝ F (Fin (n + 1))) :
    ∃ f : M → sphere (0 : F) 1, ContMDiff (𝓡 n) (𝓡 n) ∞ f ∧
      TauCeti.degree o o'.sphereOrientation f = 1 := by
  have : ConnectedSpace (sphere (0 : F) 1) := TauCeti.connectedSpace_sphere n
  have : Nontrivial F := Module.nontrivial_of_finrank_eq_succ (Fact.out : finrank ℝ F = n + 1)
  have : FiniteDimensional ℝ F := .of_fact_finrank_eq_succ n
  obtain ⟨v, hv⟩ := exists_norm_eq F zero_le_one
  set y : sphere (0 : F) 1 := ⟨v, by simpa using hv⟩
  obtain ⟨f, hf, hfib, hinv⟩ :=
    exists_contMDiff_preimage_eq_singleton (n := n) (Classical.arbitrary M) (F := F) hv
  have hdeg := TauCeti.degree_eq_orientationSign_of_preimage_eq_singleton o o'.sphereOrientation
    hf hf.continuous.isProperMap hfib hinv
  rcases TauCeti.Manifold.Orientation.orientationSign_eq_one_or_eq_neg_one
    (o := o) (o' := o'.sphereOrientation) hinv with h | h
  · exact ⟨f, hf, hdeg.trans h⟩
  -- Otherwise compose with the reflection across `v^⊥`, which reverses the orientation.
  set R := ((ℝ ∙ v)ᗮ.reflection).unitSphereEquiv
  have hdet : LinearMap.det (((ℝ ∙ v)ᗮ.reflection).toLinearEquiv : F →ₗ[ℝ] F) < 0 := by
    have hv0 : v ≠ 0 := by rintro rfl; simp at hv
    rw [← LinearEquiv.coe_det, TauCeti.linearEquiv_det_reflection_orthogonal_singleton hv0]
    exact neg_one_lt_zero
  have hR : ContMDiff (𝓡 n) (𝓡 n) ∞ R := LinearIsometryEquiv.contMDiff_unitSphereEquiv _
  have hsign : TauCeti.Manifold.Orientation.orientationSign o o'.sphereOrientation (R ∘ f)
      (Classical.arbitrary M) = 1 := by
    rw [TauCeti.Manifold.Orientation.orientationSign_comp (hR.mdifferentiable (by simp) _)
      (hf.mdifferentiable (by simp) _), h,
      TauCeti.Manifold.Orientation.orientationSign_of_isOrientationReversingAt
        (o'.isOrientationReversingAt_unitSphereEquiv hdet _)]
    norm_num
  have hinv' : (mfderiv (𝓡 n) (𝓡 n) (R ∘ f) (Classical.arbitrary M)).IsInvertible := by
    by_contra hni
    rw [TauCeti.Manifold.Orientation.orientationSign_of_not_isInvertible hni] at hsign
    exact zero_ne_one hsign
  have hfib' : (R ∘ f) ⁻¹' {R y} = {Classical.arbitrary M} := by
    rw [preimage_comp, ← image_singleton (f := R), R.injective.preimage_image, hfib]
  refine ⟨R ∘ f, hR.comp hf, ?_⟩
  rw [TauCeti.degree_eq_orientationSign_of_preimage_eq_singleton o o'.sphereOrientation
    (hR.comp hf) (hR.comp hf).continuous.isProperMap hfib' hinv', hsign]

end SymplecticGeometry

end
