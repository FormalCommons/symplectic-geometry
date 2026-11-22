/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import SymplecticGeometry.Analysis.Calculus.ContDiff.Seeley.Extension
public import SymplecticGeometry.Geometry.Manifold.Boundary.Charts
public import SymplecticGeometry.Geometry.Manifold.Flow.Basic
public import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.Basic
public import SymplecticGeometry.Geometry.Manifold.MFDeriv.Chart
public import TauCeti.Geometry.Manifold.Boundary.Collar.Local
public import TauCeti.Geometry.Manifold.Boundary.Derivative
public import TauCeti.Geometry.Manifold.Boundary.Orientation
public import TauCeti.Geometry.Manifold.IntegralCurve.Interval
public import TauCeti.Geometry.Manifold.MFDeriv.Curve
public import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
public import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic
public import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# The flow of an outward field near a boundary point

Let `W` be a manifold modelled on the half-space `𝓡∂ (n + 1)` and `Y` a smooth vector field on
`W` that points out of `W` along its boundary (`TauCeti.IsOutwardPointingField`). Integral curves
of `Y` cannot start at a boundary point and go forward, but they can go backward, into the
interior. This file constructs them near a boundary point `p` and proves that they are unique.

In the extended chart `φ` at `p`, the field `Y` reads as a smooth map on the chart target, a
relatively open part of the half-space `{y | 0 ≤ y 0}`. Seeley's extension
(`SymplecticGeometry.exists_contDiff_eqOn_of_contDiffOn_halfSpace`) makes it, near `φ p`, the
restriction of a smooth field `w` on all of `ℝⁿ⁺¹`
(`TauCeti.exists_contDiff_eqOn_mpullbackWithin_extChartAt_symm`). Its flow (Tau Ceti's
`TauCeti.flowOf`, on the boundaryless space `ℝⁿ⁺¹`) is smooth. Since the zeroth coordinate of
`w` is negative at `φ p`, near `φ p` the zeroth coordinate of each trajectory is strictly
decreasing, so a trajectory starting on the boundary hyperplane is in the open half-space at
negative times and outside it at positive times. At negative times it stays where `w` is the
coordinate field of `Y`, so `φ⁻¹` carries it to an integral curve of `Y`.

Written in the boundary chart at `p` and with time reversed, the flow from the boundary is a map
`G (z, τ) = flowOf w (-τ 0) (z inserted as a point with zeroth coordinate 0)` between open subsets
of `ℝⁿ × ℝ¹` and `ℝⁿ⁺¹`. At `(z₀, 0)`, `z₀` the boundary chart reading of `p`, its derivative sends
`(u, σ)` to `-σ 0 • w (φ p)` plus `u` inserted with zeroth coordinate `0`; it is invertible since
`w (φ p)` is transverse to the boundary hyperplane, so by the inverse function theorem in the
boundaryless spaces `G` is a local diffeomorphism there
(`TauCeti.isLocalDiffeomorphAt_flowOf_euclideanHalfSpaceBoundaryParam`). This adapts the proof of
Tau Ceti's flow-out theorem `TauCeti.isLocalDiffeomorph_globalFlow_comp` (with its differential
`TauCeti.mfderiv_globalFlow_comp_apply`) at time zero, with the linear inclusion of the
hyperplane in place of an immersion; see also Lee, Theorem 9.20. Near that point `G` sends
`ℝⁿ × [0, ∞)` exactly into the half-space, so it restricts to a local diffeomorphism of the
half-space models (`PartialDiffeomorph.isLocalDiffeomorphAt_symm_comp_comp_model`), and in the
charts of `∂W × [0, ∞)` and `W` this is the map `(x, t) ↦ γ (-t, x)`.

Uniqueness: an integral curve of an outward field cannot meet the boundary at a time near which
it is defined on both sides, since the zeroth chart coordinate would have a local minimum with
negative derivative (`IsMIntegralCurveOn.mem_interior_of_isOutwardPointing`); so two integral
curves on `(-η, 0]` are in the interior at negative times, where Tau Ceti's uniqueness theorem
`IsMIntegralCurveOn.eqOn_of_isPreconnected` applies. When they start at a boundary point, they
first agree on some `[l, 0]` by Tau Ceti's
`IsMIntegralCurveOn.eqOn_Icc_of_lipschitzOnWith_extChartAt`, since in the chart the coordinate
field is the restriction of the Lipschitz field `w`.

## Main results

* `TauCeti.exists_contDiff_eqOn_mpullbackWithin_extChartAt_symm`: near a boundary point, the
  coordinate expression of a smooth field agrees with a smooth field on `ℝⁿ⁺¹`.
* `TauCeti.isLocalDiffeomorphAt_flowOf_euclideanHalfSpaceBoundaryParam`: the flow of a field
  transverse to the boundary hyperplane, out of that hyperplane, is a local diffeomorphism.
* `TauCeti.exists_isMIntegralCurveOn_of_isOutwardPointing`: integral curves of an outward field
  entering from the boundary near `p`, forming a local diffeomorphism `∂W × [0, η) → W`.
* `IsMIntegralCurveOn.eqOn_of_isOutwardPointing`: two integral curves of an outward field on
  `(-η, 0]` that agree at time `0` agree.

## References

* R. T. Seeley, *Extension of $C^\infty$ functions defined in a half space*,
  Proc. Amer. Math. Soc. 15 (1964), 625–626.
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218, 2013,
  Chapter 9 (flows; the flow-out theorem 9.20, and the collar theorem 9.25 that this file
  prepares).
* M. Hirsch, *Differential Topology*, Springer GTM 33, 1976, Chapter 4, Theorem 6.1.
-/

public section

open Set Filter Function Topology VectorField SymplecticGeometry
open scoped Manifold ContDiff

namespace TauCeti

variable {n : ℕ} {W : Type*} [TopologicalSpace W] [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
  {Y : (x : W) → TangentSpace (𝓡∂ (n + 1)) x}

/-- An integral curve of a vector field that points outward along the boundary is in the interior
at every time near which it is defined on both sides. -/
theorem _root_.IsMIntegralCurveOn.mem_interior_of_isOutwardPointing
    [IsManifold (𝓡∂ (n + 1)) 1 W]
    (hY : ∀ x ∈ (𝓡∂ (n + 1)).boundary W, IsOutwardPointing x (Y x)) {γ : ℝ → W} {s : Set ℝ}
    (hγ : IsMIntegralCurveOn γ Y s) {t : ℝ} (hs : s ∈ 𝓝 t) :
    γ t ∈ (𝓡∂ (n + 1)).interior W := by
  rw [← ModelWithCorners.compl_boundary]
  intro hb
  set φ := extChartAt (𝓡∂ (n + 1)) (γ t)
  -- The zeroth chart coordinate along `γ` has a local minimum `0` at `t` ...
  have hmin : IsLocalMin (fun r ↦ φ (γ r) 0) t := by
    have hc : ContinuousAt γ t := (hγ.continuousWithinAt (mem_of_mem_nhds hs)).continuousAt hs
    filter_upwards [hc.preimage_mem_nhds (extChartAt_source_mem_nhds (I := 𝓡∂ (n + 1)) (γ t))]
      with r hr
    have h := extChartAt_target_subset_range (γ t) (φ.map_source hr)
    rw [range_modelWithCornersEuclideanHalfSpace] at h
    rw [extChartAt_self_apply_zero hb]
    exact h
  -- ... but its derivative there is the zeroth coordinate of `Y (γ t)`, which is negative.
  have hd :=
    (PiLp.proj 2 (fun _ : Fin (n + 1) ↦ ℝ) 0).hasFDerivAt.comp_hasDerivAt t
      ((Manifold.hasDerivWithinAt_extChartAt_comp_curve (hγ t (mem_of_mem_nhds hs))).hasDerivAt hs)
  have hneg := (isOutwardPointing_iff.1 (hY _ hb)).2
  rw [mfderiv_extChartAt_self] at hneg
  exact hneg.ne (hmin.hasDerivAt_eq_zero hd)

variable [IsManifold (𝓡∂ (n + 1)) ∞ W]

/-- Near a boundary point `q`, the coordinate expression of a smooth vector field in the extended
chart at `q` agrees, on the half-space, with a smooth vector field on all of `ℝⁿ⁺¹`: Seeley's
extension across the boundary hyperplane. -/
theorem exists_contDiff_eqOn_mpullbackWithin_extChartAt_symm (hY : CMDiff ∞ (T% Y)) {q : W}
    (hq : q ∈ (𝓡∂ (n + 1)).boundary W) :
    ∃ w : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)), ContDiff ℝ ∞ w ∧
      ∃ V, IsOpen V ∧ extChartAt (𝓡∂ (n + 1)) q q ∈ V ∧
        V ∩ range (𝓡∂ (n + 1)) ⊆ (extChartAt (𝓡∂ (n + 1)) q).target ∧
        EqOn w (mpullbackWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) (𝓡∂ (n + 1))
          (extChartAt (𝓡∂ (n + 1)) q).symm Y (range (𝓡∂ (n + 1)))) (V ∩ range (𝓡∂ (n + 1))) := by
  set φ := extChartAt (𝓡∂ (n + 1)) q
  set f := mpullbackWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) (𝓡∂ (n + 1)) φ.symm Y
    (range (𝓡∂ (n + 1)))
  obtain ⟨U, hU, hqU, hUt⟩ :=
    mem_nhdsWithin.1 (extChartAt_target_mem_nhdsWithin (I := 𝓡∂ (n + 1)) q)
  rw [range_modelWithCornersEuclideanHalfSpace] at hUt
  -- Read `ℝⁿ⁺¹` as `ℝ × ℝⁿ`, with the normal coordinate first.
  set N := (ContinuousLinearEquiv.prodComm ℝ ℝ (EuclideanSpace ℝ (Fin n))).trans
    (euclideanHalfSpaceBoundaryNormalEquiv n)
  have hN0 (z : ℝ × EuclideanSpace ℝ (Fin n)) : N z 0 = z.1 := by
    obtain ⟨a, b⟩ := z
    simp [N]
  have hNs (y : EuclideanSpace ℝ (Fin (n + 1))) : (N.symm y).1 = y 0 := by
    rw [← hN0, N.apply_symm_apply]
  have hNq : N (0, (N.symm (φ q)).2) = φ q := by
    rw [← extChartAt_self_apply_zero hq, ← hNs, Prod.mk.eta, N.apply_symm_apply]
  obtain ⟨g, hg, V, hV, hqV, hgV⟩ := exists_contDiff_eqOn_of_contDiffOn_halfSpace
    (hU.preimage N.continuous) (f := f ∘ N)
    ((hY.contDiffOn_mpullbackWithin_extChartAt_symm (n := ∞) (by simp) q).comp N.contDiff.contDiffOn
      fun z (hz : z ∈ N ⁻¹' U ∩ {z | 0 ≤ z.1}) ↦
        hUt ⟨hz.1, show 0 ≤ N z 0 by rw [hN0]; exact hz.2⟩)
    (show N (0, (N.symm (φ q)).2) ∈ U by rw [hNq]; exact hqU)
  refine ⟨g ∘ N.symm, hg.comp N.symm.contDiff, N.symm ⁻¹' V ∩ U,
    (hV.preimage N.symm.continuous).inter hU, ⟨?_, hqU⟩, ?_, fun y hy ↦ ?_⟩
  · rw [mem_preimage, ← hNq, N.symm_apply_apply]
    exact hqV
  · rw [range_modelWithCornersEuclideanHalfSpace]
    exact fun y hy ↦ hUt ⟨hy.1.2, hy.2⟩
  · rw [range_modelWithCornersEuclideanHalfSpace] at hy
    have h := hgV ⟨hy.1.1, show 0 ≤ (N.symm y).1 by rw [hNs]; exact hy.2⟩
    rw [comp_apply, h]
    exact congrArg f (N.apply_symm_apply y)

section Box

variable {w : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}

/-- Near a point `y₀` at which a `C¹` field `w` on `ℝⁿ⁺¹` has negative zeroth coordinate, the
trajectories of its flow from the points of the boundary hyperplane near `y₀` are defined on a
common time interval `(-η, η)`, have `w` as derivative, stay in a given open neighbourhood `V` of
`y₀`, and have nonnegative (positive) zeroth coordinate exactly at nonpositive (negative) times. -/
private theorem exists_flowOf_box (hw : ContDiff ℝ 1 w) {V : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (hV : IsOpen V) {y₀ : EuclideanSpace ℝ (Fin (n + 1))} (hy₀ : y₀ ∈ V) (hw₀ : w y₀ 0 < 0) :
    ∃ η > 0, ∃ r > 0, ∀ y ∈ Metric.ball y₀ r, y 0 = 0 → ∀ s ∈ Ioo (-η) η,
      HasDerivAt (fun s ↦ flowOf (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))) w s y)
        (w (flowOf (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))) w s y)) s ∧
      flowOf (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))) w s y ∈ V ∧
      (0 ≤ flowOf (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))) w s y 0 ↔ s ≤ 0) ∧
      (0 < flowOf (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))) w s y 0 ↔ s < 0) := by
  set D := flowDomain (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))) w
  set Φ := fun p : ℝ × EuclideanSpace ℝ (Fin (n + 1)) ↦
    flowOf (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))) w p.1 p.2
  have hw1 : CMDiff 1 (fun y ↦ (⟨y, w y⟩ : TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
      (EuclideanSpace ℝ (Fin (n + 1))))) :=
    contMDiff_vectorSpace_iff_contDiff.2 hw
  have hD : IsOpen D := isOpen_flowDomain hw1
  have h0 : ((0 : ℝ), y₀) ∈ D := mem_flowDomain_zero hw1 y₀
  set O := V ∩ {z : EuclideanSpace ℝ (Fin (n + 1)) | w z 0 < 0}
  have hO : IsOpen O := hV.inter (isOpen_lt (by fun_prop) continuous_const)
  have hmem : D ∩ Φ ⁻¹' O ∈ 𝓝 (0, y₀) :=
    inter_mem (hD.mem_nhds h0) <|
      ((contDiffOn_flowOf_uncurry le_rfl hw).continuousOn.continuousAt (hD.mem_nhds h0)
        |>.preimage_mem_nhds (hO.mem_nhds (by
          have h := flowOf_zero (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))) w y₀
          exact h.symm ▸ ⟨hy₀, hw₀⟩)))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hmem
  have hbox : ∀ s ∈ Ioo (-ε) ε, ∀ y ∈ Metric.ball y₀ ε, (s, y) ∈ D ∧ Φ (s, y) ∈ O :=
    fun s hs y hy ↦ hball (by
      rw [← ball_prod_same, Real.ball_eq_Ioo, zero_sub, zero_add]
      exact ⟨hs, hy⟩)
  refine ⟨ε, hε, ε, hε, fun y hy hy0 ↦ ?_⟩
  have hderiv : ∀ s ∈ Ioo (-ε) ε, HasDerivAt (fun s ↦ Φ (s, y)) (w (Φ (s, y))) s :=
    fun s hs ↦ (hasDerivAt_comp_flowOf hw1 (hbox s hs y hy).1 (g := id) mdifferentiableAt_id)
      |>.congr_deriv ((mvfderiv_eq_fderiv_apply _ _ _).trans
        (by rw [fderiv_id, ContinuousLinearMap.id_apply]))
  -- The zeroth coordinate of a trajectory has derivative the zeroth coordinate of `w`.
  have hanti : StrictAntiOn (fun s ↦ Φ (s, y) 0) (Ioo (-ε) ε) := by
    have hd0 (s : ℝ) (hs : s ∈ Ioo (-ε) ε) :=
      (PiLp.proj 2 (fun _ : Fin (n + 1) ↦ ℝ) 0).hasFDerivAt.comp_hasDerivAt s (hderiv s hs)
    refine strictAntiOn_of_hasDerivWithinAt_neg (convex_Ioo _ _)
      (fun s hs ↦ (hd0 s hs).continuousAt.continuousWithinAt)
      (fun s hs ↦ (hd0 s (interior_subset hs)).hasDerivWithinAt) fun s hs ↦ ?_
    exact (hbox s (interior_subset hs) y hy).2.2
  intro s hs
  have hm : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith, hε⟩
  have hz : Φ (0, y) 0 = 0 := by
    have h := flowOf_zero (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))) w y
    simp only [Φ, h, hy0]
  have h1 := hanti.le_iff_ge hm hs
  have h2 := hanti.lt_iff_gt hm hs
  simp only [hz] at h1 h2
  exact ⟨hderiv s hs, (hbox s hs y hy).2.1, h1, h2⟩

/-- The flow of a smooth field `w` on `ℝⁿ⁺¹` out of the boundary hyperplane, with time reversed,
`(z, τ) ↦ flowOf w (-τ 0) z` for `z` in the hyperplane, is a local diffeomorphism at `(z₀, 0)`
when `w` is transverse to the hyperplane at `z₀`. -/
theorem isLocalDiffeomorphAt_flowOf_euclideanHalfSpaceBoundaryParam (hw : ContDiff ℝ ∞ w)
    (z₀ : EuclideanSpace ℝ (Fin n)) (hw₀ : w (euclideanHalfSpaceBoundaryParam n z₀) 0 ≠ 0) :
    IsLocalDiffeomorphAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin 1))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ∞
      (fun q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin 1) ↦
        flowOf (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))) w (-q.2 0)
          (euclideanHalfSpaceBoundaryParam n q.1)) (z₀, 0) := by
  set ι := euclideanHalfSpaceBoundaryParam n
  set L : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin 1) →L[ℝ]
      ℝ × EuclideanSpace ℝ (Fin (n + 1)) :=
    (-((PiLp.proj 2 (fun _ : Fin 1 ↦ ℝ) 0).comp (ContinuousLinearMap.snd ℝ _ _))).prod
      (ι.comp (ContinuousLinearMap.fst ℝ _ _))
  set G : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin (n + 1)) :=
    fun q ↦ flowOf (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))) w (-q.2 0) (ι q.1)
  have hLz₀ : L (z₀, 0) = (0, ι z₀) := by
    simp [L]
  have hw1 : CMDiff 1 (fun y ↦ (⟨y, w y⟩ : TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
      (EuclideanSpace ℝ (Fin (n + 1))))) :=
    contMDiff_vectorSpace_iff_contDiff.2 (hw.of_le (m := 1) (by simp))
  set D' := L ⁻¹' flowDomain (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))) w
  have hD' : IsOpen D' := (isOpen_flowDomain hw1).preimage L.continuous
  have hz₀D' : (z₀, (0 : EuclideanSpace ℝ (Fin 1))) ∈ D' := by
    simp only [D', mem_preimage, hLz₀]
    exact mem_flowDomain_zero hw1 _
  have hGs : ContDiffOn ℝ ∞ G D' :=
    (contDiffOn_flowOf_uncurry le_top hw).comp L.contDiff.contDiffOn fun _ hq ↦ hq
  have hGd : HasFDerivAt G (((ContinuousLinearMap.fst ℝ ℝ _).smulRight (w (ι z₀)) +
      ContinuousLinearMap.snd ℝ ℝ _).comp L) (z₀, 0) := by
    have h := hasFDerivAt_flowOf_uncurry_zero (hw.of_le (by simp)) (ι z₀)
    rw [← hLz₀] at h
    exact h.comp (z₀, 0) L.hasFDerivAt
  -- Its derivative at `(z₀, 0)` is injective, since `w (ι z₀)` leaves the boundary hyperplane.
  have hinj : Injective (((ContinuousLinearMap.fst ℝ ℝ _).smulRight (w (ι z₀)) +
      ContinuousLinearMap.snd ℝ ℝ _).comp L) := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨dz, dτ⟩ h
    simp only [L, ContinuousLinearMap.coe_comp, comp_apply, add_apply,
      ContinuousLinearMap.prod_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', neg_apply,
      PiLp.proj_apply] at h
    have h0 := congrArg (fun y : EuclideanSpace ℝ (Fin (n + 1)) ↦ y 0) h
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, ι,
      euclideanHalfSpaceBoundaryParam_apply_zero, add_zero, PiLp.zero_apply, mul_eq_zero,
      neg_eq_zero, hw₀, or_false] at h0
    have hτ : dτ = 0 := by
      ext i
      fin_cases i
      simpa using h0
    rw [hτ] at h
    simp only [PiLp.zero_apply, neg_zero, zero_smul, zero_add] at h
    have hz : dz = 0 := euclideanHalfSpaceBoundaryParam_injective n (by simpa [ι] using h)
    simp [hz, hτ]
  exact isLocalDiffeomorphAt_of_injective_mfderiv (contMDiffOn_iff_contDiffOn.2 hGs) hD' hz₀D'
      BoundarylessManifold.isInteriorPoint (by simp)
      (by rwa [mfderiv_eq_fderiv, hGd.fderiv]) (by simp)

/-- The flow of `w` from the boundary hyperplane, with time reversed, agrees near `(z₀, 0)`, and
inside a given open set `R`, with a partial diffeomorphism `Θ` that sends a point of its source
into the half-space exactly when the point lies in `ℝⁿ × [0, ∞)`, provided that this holds for the
flow on `R`. -/
private theorem exists_partialDiffeomorph_flowOf_boundaryParam (hw : ContDiff ℝ ∞ w)
    {z₀ : EuclideanSpace ℝ (Fin n)} (hw₀ : w (euclideanHalfSpaceBoundaryParam n z₀) 0 ≠ 0)
    {R : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin 1))} (hR : IsOpen R)
    (hz₀R : (z₀, 0) ∈ R)
    (hsign : ∀ q ∈ R, 0 ≤ flowOf (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))) w (-q.2 0)
      (euclideanHalfSpaceBoundaryParam n q.1) 0 ↔ 0 ≤ q.2 0) :
    ∃ Θ : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin 1))
        𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin 1))
        (EuclideanSpace ℝ (Fin (n + 1))) ∞,
      (z₀, 0) ∈ Θ.source ∧ Θ.source ⊆ R ∧
      (∀ q ∈ Θ.source, Θ q = flowOf (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))) w (-q.2 0)
        (euclideanHalfSpaceBoundaryParam n q.1)) ∧
      ∀ q ∈ Θ.source, Θ q ∈ range (𝓡∂ (n + 1)) ↔ q ∈ range ((𝓡 n).prod (𝓡∂ 1)) := by
  obtain ⟨Θ, hΘ0, hΘR, hGΘ⟩ := IsLocalDiffeomorphAt.exists_partialDiffeomorph_source_subset
    (isLocalDiffeomorphAt_flowOf_euclideanHalfSpaceBoundaryParam hw z₀ hw₀) (hR.mem_nhds hz₀R)
  refine ⟨Θ, hΘ0, hΘR, fun q hq ↦ (hGΘ hq).symm, ?_⟩
  rintro ⟨z, τ⟩ hq
  rw [← hGΘ hq, ModelWithCorners.range_prod, range_modelWithCornersEuclideanHalfSpace,
    range_modelWithCornersEuclideanHalfSpace]
  simp only [mem_ofPred_eq, mem_prod, modelWithCornersSelf_coe, range_id, mem_univ, true_and]
  exact hsign _ (hΘR hq)

end Box

/-- Let `Θ` be a partial diffeomorphism of `ℝⁿ × ℝ¹` into `ℝⁿ⁺¹` that sends a point of its source
into the half-space exactly when the point lies in `ℝⁿ × [0, ∞)`. A map on an open set `S` of
`∂W × [0, ∞)` which, read in the boundary chart at `p` and in the extended chart at `p`, is the
restriction of `Θ`, is a local diffeomorphism on `S`. -/
private theorem isLocalDiffeomorphOn_extChartAt_symm_comp {p : (𝓡∂ (n + 1)).boundary W}
    (Θ : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin 1))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin 1))
      (EuclideanSpace ℝ (Fin (n + 1))) ∞)
    (hΘ : ∀ q ∈ Θ.source, Θ q ∈ range (𝓡∂ (n + 1)) ↔ q ∈ range ((𝓡 n).prod (𝓡∂ 1)))
    {f : (𝓡∂ (n + 1)).boundary W × EuclideanHalfSpace 1 → EuclideanSpace ℝ (Fin (n + 1))}
    {S : Set ((𝓡∂ (n + 1)).boundary W × EuclideanHalfSpace 1)} (hS : IsOpen S)
    (hf : ∀ q ∈ S, q.1 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source ∧
      (chartAt (EuclideanSpace ℝ (Fin n)) p q.1, q.2.val) ∈ Θ.source ∧
      Θ (chartAt (EuclideanSpace ℝ (Fin n)) p q.1, q.2.val) = f q ∧
      f q ∈ (extChartAt (𝓡∂ (n + 1)) (p : W)).target) :
    IsLocalDiffeomorphOn ((𝓡 n).prod (𝓡∂ 1)) (𝓡∂ (n + 1)) ∞
      (fun q ↦ (extChartAt (𝓡∂ (n + 1)) (p : W)).symm (f q)) S := by
  have : IsManifold (𝓡 n) ∞ ((𝓡∂ (n + 1)).boundary W) := isManifold_boundary W
  set β := chartAt (EuclideanSpace ℝ (Fin n)) p
  set C := chartAt (ModelProd (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace 1))
    ((p, 0) : (𝓡∂ (n + 1)).boundary W × EuclideanHalfSpace 1)
  -- The product chart at `(p, 0)` is `β` times the identity, and the product model is the
  -- inclusion of `ℝⁿ × [0, ∞)`.
  have hCapply (q : (𝓡∂ (n + 1)).boundary W × EuclideanHalfSpace 1) : C q = (β q.1, q.2) := by
    simp only [C, β, prodChartedSpace_chartAt, chartAt_self_eq]
    rw [OpenPartialHomeomorph.prod_apply, OpenPartialHomeomorph.refl_apply]
    simp only [id_eq]
  have hCsrc (q : (𝓡∂ (n + 1)).boundary W × EuclideanHalfSpace 1) (hq : q.1 ∈ β.source) :
      q ∈ C.source := by
    simp only [C, prodChartedSpace_chartAt, OpenPartialHomeomorph.prod_source, chartAt_self_eq,
      OpenPartialHomeomorph.refl_source]
    exact ⟨hq, mem_univ _⟩
  have hI (q : EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1) :
      ((𝓡 n).prod (𝓡∂ 1)) q = (q.1, q.2.val) := by
    rw [modelWithCorners_prod_coe, Prod.map_apply, modelWithCornersSelf_coe, id_eq,
      modelWithCornersEuclideanHalfSpace_apply]
  have hCI (q : (𝓡∂ (n + 1)).boundary W × EuclideanHalfSpace 1) :
      ((𝓡 n).prod (𝓡∂ 1)) (C q) = (β q.1, q.2.val) := by
    rw [hCapply, hI]
  rintro ⟨q, hq⟩
  obtain ⟨hq1, hsrc, hval, htgt⟩ := hf q hq
  have hl := Θ.isLocalDiffeomorphAt_symm_comp_comp_model ((𝓡 n).prod (𝓡∂ 1)) (𝓡∂ (n + 1))
    hΘ (by rw [hCI]; exact hsrc)
  have hχ : (𝓡∂ (n + 1)).symm (Θ (((𝓡 n).prod (𝓡∂ 1)) (C q))) ∈
      (chartAt (EuclideanHalfSpace (n + 1)) (p : W)).target := by
    rw [extChartAt_target] at htgt
    rw [hCI, hval]
    exact htgt.1
  have hc := (C.isLocalDiffeomorphAt_of_mem_maximalAtlas (n := ∞)
    (IsManifold.chart_mem_maximalAtlas _) (hCsrc q hq1)).comp (hg := hl.comp (hg :=
      (OpenPartialHomeomorph.isLocalDiffeomorphAt_symm_of_mem_maximalAtlas
        (chartAt (EuclideanHalfSpace (n + 1)) (p : W))
        (IsManifold.chart_mem_maximalAtlas _) hχ)))
  refine hc.congr_of_eventuallyEq ?_
  filter_upwards [hS.mem_nhds hq] with q' hq'
  simp only [comp_apply, hCI, (hf q' hq').2.2.1, extChartAt_coe_symm]

/-- **Integral curves entering from the boundary.** Let `Y` be a smooth vector field pointing out
of `W` along its boundary, and `p` a boundary point. There are an open set `B ∋ p` of the
boundary, a time `η > 0` and a map `γ` such that for each `x ∈ B` the curve `s ↦ γ (s, x)` starts
at `x`, runs in the interior of `W` for `s ∈ (-η, 0)`, and is an integral curve of `Y` on
`(-η, 0]`. Moreover `(x, t) ↦ γ (-t, x)` is a local diffeomorphism on `B × [0, η)`, the time
interval being read as part of the one-dimensional half-space. -/
theorem exists_isMIntegralCurveOn_of_isOutwardPointing (hY : IsOutwardPointingField Y)
    (p : (𝓡∂ (n + 1)).boundary W) :
    ∃ (B : Set ((𝓡∂ (n + 1)).boundary W)) (η : ℝ)
      (γ : ℝ × (𝓡∂ (n + 1)).boundary W → W),
      IsOpen B ∧ p ∈ B ∧ 0 < η ∧ (∀ x ∈ B, γ (0, x) = x) ∧
      (∀ x ∈ B, ∀ s ∈ Ioo (-η) 0, γ (s, x) ∈ (𝓡∂ (n + 1)).interior W) ∧
      (∀ x ∈ B, IsMIntegralCurveOn (fun s ↦ γ (s, x)) Y (Ioc (-η) 0)) ∧
      IsLocalDiffeomorphOn ((𝓡 n).prod (𝓡∂ 1)) (𝓡∂ (n + 1)) ∞
        (fun q : (𝓡∂ (n + 1)).boundary W × EuclideanHalfSpace 1 ↦ γ (-q.2.val 0, q.1))
        (B ×ˢ EuclideanHalfSpace.normalIio η) := by
  obtain ⟨hYs, hYb⟩ := isOutwardPointingField_iff.1 hY
  set φ := extChartAt (𝓡∂ (n + 1)) (p : W)
  obtain ⟨w, hw, V, hV, hpV, hVt, hwv⟩ :=
    exists_contDiff_eqOn_mpullbackWithin_extChartAt_symm hYs p.property
  have hw₀ : w (φ p) 0 < 0 := by
    have h := (isOutwardPointing_iff.1 (hYb p p.property)).2
    rw [mfderiv_extChartAt_self] at h
    rwa [← mpullbackWithin_extChartAt_symm_self Y (p : W),
      ← hwv ⟨hpV, extChartAt_target_subset_range _ (mem_extChartAt_target _)⟩] at h
  obtain ⟨η₀, hη₀, r, hr, hbox⟩ := exists_flowOf_box (hw.of_le (by simp)) hV hpV hw₀
  -- At nonpositive times, trajectories from the boundary hyperplane stay where `w` is the
  -- coordinate field of `Y`.
  have hmemV : ∀ y ∈ Metric.ball (φ p) r, y 0 = 0 → ∀ s ∈ Ioc (-η₀) 0,
      flowOf (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))) w s y ∈ V ∩ range (𝓡∂ (n + 1)) := by
    intro y hy hy0 s hs
    have h := hbox y hy hy0 s ⟨hs.1, by linarith [hs.2]⟩
    rw [range_modelWithCornersEuclideanHalfSpace]
    exact ⟨h.2.1, h.2.2.1.2 hs.2⟩
  -- The flow from the boundary, read in the boundary chart `β` at `p` and with time reversed.
  set ι := euclideanHalfSpaceBoundaryParam n
  set β := chartAt (EuclideanSpace ℝ (Fin n)) p
  have hι (x : (𝓡∂ (n + 1)).boundary W) (hx : (x : W) ∈ φ.source) : ι (β x) = φ x := by
    have h := boundaryParam_extChartAt (α := p) (x := x)
      (by simpa [φ, extChartAt_source, boundaryChartedSpace_chartAt_source] using hx)
    rwa [extChartAt_coe, modelWithCornersSelf_coe, id_comp] at h
  have hz₀ : ι (β p) = φ p := hι p (mem_extChartAt_source _)
  obtain ⟨Θ, hΘ0, hΘR, hΘG, hcond⟩ := exists_partialDiffeomorph_flowOf_boundaryParam hw
    (z₀ := β p) (by rw [hz₀]; exact hw₀.ne)
    (R := {q | -q.2 0 ∈ Ioo (-η₀) η₀ ∧ ι q.1 ∈ Metric.ball (φ p) r})
    ((isOpen_Ioo.preimage (by fun_prop)).inter (Metric.isOpen_ball.preimage (by fun_prop)))
    ⟨by simp [hη₀], by rw [hz₀]; exact Metric.mem_ball_self hr⟩ fun q hq ↦ by
      rw [(hbox _ hq.2 (euclideanHalfSpaceBoundaryParam_apply_zero _) _ hq.1).2.2.1, neg_nonpos]
  -- A product box in the source of `Θ`, and the corresponding set `B` of boundary points.
  obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.1 Θ.open_source _ hΘ0
  set B : Set ((𝓡∂ (n + 1)).boundary W) := β.source ∩ β ⁻¹' Metric.ball (β p) ε
  have hB : IsOpen B := β.continuousOn.isOpen_inter_preimage β.open_source Metric.isOpen_ball
  have hBsrc : ∀ x ∈ B, (x : W) ∈ φ.source := fun x hx ↦ by
    simpa [boundaryChartedSpace_chartAt_source, β, φ] using hx.1
  have hBΘ : ∀ x ∈ B, ∀ τ : EuclideanSpace ℝ (Fin 1), ‖τ‖ < ε → (β x, τ) ∈ Θ.source :=
    fun x hx τ hτ ↦ hεsub (by
      rw [Metric.mem_ball, Prod.dist_eq]
      exact max_lt hx.2 (by simpa using hτ))
  have hBball : ∀ x ∈ B, φ x ∈ Metric.ball (φ p) r := fun x hx ↦ by
    rw [← hι x (hBsrc x hx)]
    exact (hΘR (hBΘ x hx 0 (by simpa using hε))).2
  have hB0 : ∀ x ∈ B, φ x 0 = 0 := fun x hx ↦ by
    rw [← hι x (hBsrc x hx)]
    exact euclideanHalfSpaceBoundaryParam_apply_zero _
  have hη (s : ℝ) (hs : -min η₀ ε < s) : -η₀ < s := lt_of_le_of_lt (neg_le_neg (min_le_left _ _)) hs
  refine ⟨B, min η₀ ε, fun q ↦ φ.symm (flowOf (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))) w q.1
    (φ q.2)), hB, ⟨mem_chart_source _ p, Metric.mem_ball_self hε⟩, lt_min hη₀ hε, fun x hx ↦ ?_,
    fun x hx s hs ↦ ?_, fun x hx s hs ↦ ?_, ?_⟩
  · -- The curves start on the boundary.
    have h := flowOf_zero (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))) w (φ x)
    simp only [h]
    exact φ.left_inv (hBsrc x hx)
  · -- They run in the interior at negative times.
    have h := hbox _ (hBball x hx) (hB0 x hx) s ⟨hη s hs.1, by linarith [hs.2]⟩
    exact extChartAt_symm_mem_interior
      (hVt (hmemV _ (hBball x hx) (hB0 x hx) s ⟨hη s hs.1, hs.2.le⟩)) (h.2.2.2.2 hs.2)
  · -- They are integral curves of `Y`: in the chart they solve `y' = w y`, and `w` is the
    -- coordinate field of `Y` there.
    have hmem : ∀ s ∈ Ioc (-min η₀ ε) 0,
        flowOf (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))) w s (φ x) ∈
          V ∩ range (𝓡∂ (n + 1)) := fun s hs ↦
      hmemV _ (hBball x hx) (hB0 x hx) s ⟨hη s hs.1, hs.2⟩
    have hd : HasDerivWithinAt
        (fun s ↦ flowOf (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))) w s (φ x))
        (mpullbackWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) (𝓡∂ (n + 1)) φ.symm Y
          (range (𝓡∂ (n + 1)))
          (flowOf (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))) w s (φ x)))
        (Ioc (-min η₀ ε) 0) s := by
      rw [← hwv (hmem s hs)]
      exact (hbox _ (hBball x hx) (hB0 x hx) s ⟨hη s hs.1, by linarith [hs.2]⟩).1.hasDerivWithinAt
    have h := Manifold.hasMFDerivWithinAt_extChartAt_symm_comp (hVt (hmem s hs))
      (eventually_nhdsWithin_of_forall fun r hr ↦ (hmem r hr).2) hd
    rwa [mfderivWithin_extChartAt_symm_mpullbackWithin (hVt (hmem s hs))] at h
  · -- Read in charts, `(x, t) ↦ γ (-t, x)` is the restriction of `Θ` to the half-spaces.
    refine isLocalDiffeomorphOn_extChartAt_symm_comp Θ hcond
      (hB.prod (EuclideanHalfSpace.isOpen_normalIio _)) fun q ⟨hq1, hq2⟩ ↦ ?_
    rw [EuclideanHalfSpace.mem_normalIio] at hq2
    have h0 : 0 ≤ q.2.val 0 := q.2.property
    have hnorm : ‖q.2.val‖ < ε := by
      have h : ‖q.2.val‖ = |q.2.val 0| := by
        simp [EuclideanSpace.norm_eq, Real.sqrt_sq_eq_abs]
      rw [h, abs_of_nonneg h0]
      exact lt_of_lt_of_le hq2 (min_le_right _ _)
    have hsrc := hBΘ _ hq1 _ hnorm
    refine ⟨hq1.1, hsrc, by rw [hΘG _ hsrc, hι _ (hBsrc _ hq1)], hVt (hmemV _ (hBball _ hq1)
      (hB0 _ hq1) _ ⟨by linarith [lt_of_lt_of_le hq2 (min_le_left _ _)], by linarith⟩)⟩

/-- Two integral curves of a smooth field on `(-η, 0]` that start at the same boundary point agree
on some interval `[l, 0]` with `-η < l < 0`: in the chart at that point, the coordinate field is
the restriction of a Lipschitz field. -/
private theorem exists_eqOn_Icc_of_mem_boundary (hY : CMDiff ∞ (T% Y)) {γ δ : ℝ → W} {η : ℝ}
    (hη : 0 < η) (hγ : IsMIntegralCurveOn γ Y (Ioc (-η) 0))
    (hδ : IsMIntegralCurveOn δ Y (Ioc (-η) 0)) (h0 : γ 0 = δ 0)
    (hb : γ 0 ∈ (𝓡∂ (n + 1)).boundary W) :
    ∃ l ∈ Ioo (-η) 0, EqOn γ δ (Icc l 0) := by
  set φ := extChartAt (𝓡∂ (n + 1)) (γ 0)
  obtain ⟨w, hw, V, hV, hqV, -, hwv⟩ := exists_contDiff_eqOn_mpullbackWithin_extChartAt_symm hY hb
  obtain ⟨K, T, hT, hK⟩ :=
    ((hw.of_le (m := 1) (by simp)).contDiffAt (x := φ (γ 0))).exists_lipschitzOnWith
  -- On `V ∩ T ∩ φ.target`, the coordinate field of `Y` is `w`, so it is Lipschitz there.
  have hlip : LipschitzOnWith K (fun y ↦ tangentCoordChange (𝓡∂ (n + 1)) (φ.symm y) (γ 0)
      (φ.symm y) (Y (φ.symm y))) (V ∩ T ∩ φ.target) := by
    have he (y : EuclideanSpace ℝ (Fin (n + 1))) (hy : y ∈ V ∩ T ∩ φ.target) :
        w y = tangentCoordChange (𝓡∂ (n + 1)) (φ.symm y) (γ 0) (φ.symm y) (Y (φ.symm y)) := by
      have hs : φ.symm y ∈ φ.source := φ.map_target hy.2
      have h := mpullbackWithin_extChartAt_symm_apply Y hs
      rw [φ.right_inv hy.2, TangentBundle.trivializationAt_apply_tangentCoordChange] at h
      rw [hwv ⟨hy.1.1, extChartAt_target_subset_range _ hy.2⟩]
      exact h
    intro a ha b hb
    dsimp only
    rw [← he a ha, ← he b hb]
    exact hK ha.1.2 hb.1.2
  -- Near time `0`, both curves stay in the chart, in `V` and in the Lipschitz set `T`.
  have hS : φ.source ∩ φ ⁻¹' (V ∩ T) ∈ 𝓝 (γ 0) :=
    inter_mem (extChartAt_source_mem_nhds (γ 0))
      ((continuousAt_extChartAt (γ 0)).preimage_mem_nhds (inter_mem (hV.mem_nhds hqV) hT))
  have h0mem : (0 : ℝ) ∈ Ioc (-η) 0 := ⟨by linarith, le_rfl⟩
  have hev := inter_mem ((hγ.continuousWithinAt h0mem).preimage_mem_nhdsWithin hS)
    ((hδ.continuousWithinAt h0mem).preimage_mem_nhdsWithin (h0 ▸ hS))
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhdsWithin_iff.1 hev
  set l := max (-ε / 2) (-η / 2)
  have hl : l ∈ Ioo (-η) 0 :=
    ⟨lt_max_of_lt_right (by linarith), max_lt (by linarith) (by linarith)⟩
  have hsub : Icc l 0 ⊆ Ioc (-η) 0 := fun r hr ↦ ⟨by linarith [hl.1, hr.1], hr.2⟩
  have hgood : ∀ r ∈ Icc l 0, (γ r ∈ φ.source ∧ φ (γ r) ∈ V ∩ T) ∧
      (δ r ∈ φ.source ∧ φ (δ r) ∈ V ∩ T) := fun r hr ↦ by
    refine hεsub ⟨?_, hsub hr⟩
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonpos hr.2]
    linarith [le_max_left (-ε / 2) (-η / 2), hr.1]
  exact ⟨l, hl, (hγ.mono hsub).eqOn_Icc_of_lipschitzOnWith_extChartAt (z := V ∩ T ∩ φ.target)
    (hδ.mono hsub)
    (fun r hr ↦ (hgood r hr).1.1) (fun r hr ↦ (hgood r hr).2.1)
    (fun r hr ↦ ⟨(hgood r hr).1.2, φ.map_source (hgood r hr).1.1⟩)
    (fun r hr ↦ ⟨(hgood r hr).2.2, φ.map_source (hgood r hr).2.1⟩) hlip ⟨hl.2.le, le_rfl⟩ h0⟩

/-- **Uniqueness of integral curves of an outward field.** Two integral curves on `(-η, 0]` of a
smooth vector field pointing outward along the boundary agree if they agree at time `0`. -/
theorem _root_.IsMIntegralCurveOn.eqOn_of_isOutwardPointing [T2Space W]
    (hY : IsOutwardPointingField Y) {γ δ : ℝ → W} {η : ℝ}
    (hγ : IsMIntegralCurveOn γ Y (Ioc (-η) 0)) (hδ : IsMIntegralCurveOn δ Y (Ioc (-η) 0))
    (h0 : γ 0 = δ 0) : EqOn γ δ (Ioc (-η) 0) := by
  obtain ⟨hYs, hYb⟩ := isOutwardPointingField_iff.1 hY
  rcases le_or_gt η 0 with hη | hη
  · intro t ht
    exact absurd (ht.1.trans_le ht.2) (by linarith)
  have hv : ∀ t ∈ Ioc (-η) 0,
      CMDiffAt 1 (fun x ↦ (⟨x, Y x⟩ : TangentBundle (𝓡∂ (n + 1)) W)) (γ t) :=
    fun t _ ↦ (hYs.of_le (by simp)).contMDiffAt
  -- At negative times, both curves are in the interior.
  have hint : ∀ t ∈ Ioo (-η) 0, γ t ∈ (𝓡∂ (n + 1)).interior W := fun t ht ↦
    hγ.mem_interior_of_isOutwardPointing hYb
      (mem_of_superset (Ioo_mem_nhds ht.1 ht.2) Ioo_subset_Ioc_self)
  by_cases hb : γ 0 ∈ (𝓡∂ (n + 1)).boundary W
  · obtain ⟨l, hl, hEq⟩ := exists_eqOn_Icc_of_mem_boundary hYs hη hγ hδ h0 hb
    have hIoo := IsMIntegralCurveOn.eqOn_of_isPreconnected (hγ.mono Ioo_subset_Ioc_self)
      (hδ.mono Ioo_subset_Ioc_self) isPreconnected_Ioo hl (fun t ht ↦ hint t ht)
      (fun t ht ↦ hv t (Ioo_subset_Ioc_self ht)) (hEq ⟨le_rfl, hl.2.le⟩)
    intro t ht
    rcases ht.2.lt_or_eq with ht0 | rfl
    · exact hIoo ⟨ht.1, ht0⟩
    · exact h0
  · refine IsMIntegralCurveOn.eqOn_of_isPreconnected hγ hδ isPreconnected_Ioc
      ⟨by linarith, le_rfl⟩ (fun t ht ↦ ?_) hv h0
    rcases ht.2.lt_or_eq with ht0 | rfl
    · exact hint t ⟨ht.1, ht0⟩
    · have h : γ 0 ∈ (𝓡∂ (n + 1)).interior W := by
        rw [← ModelWithCorners.compl_boundary]
        exact hb
      exact h

end TauCeti

end
