/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Geometry.Manifold.VectorField.Pullback
public import SymplecticGeometry.Analysis.Calculus.ContDiff.Seeley.Extension
public import SymplecticGeometry.Geometry.Manifold.Flow.Basic
public import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.Basic
public import TauCeti.Geometry.Manifold.Boundary.Charts
public import TauCeti.Geometry.Manifold.Boundary.Collar.Local
public import TauCeti.Geometry.Manifold.Boundary.Orientation
public import TauCeti.Geometry.Manifold.IntegralCurve.Interval
public import TauCeti.Geometry.Manifold.MFDeriv.Curve

/-!
# The flow of an outward field near a boundary point

Let `W` be a manifold modelled on the half-space `𝓡∂ (n + 1)` and `Y` a smooth vector field on
`W` that points out of `W` along its boundary (`TauCeti.IsOutwardPointingField`). Integral curves
of `Y` cannot start at a boundary point and go forward, but they can go backward, into the
interior. This file constructs them near a boundary point `p` and proves that they are unique.

In the extended chart `φ` at `p`, the field `Y` reads as a smooth map on the chart target, a
relatively open part of the half-space `{y | 0 ≤ y 0}`. Seeley's extension in the normal
coordinate, after a cut-off, and a bump function extend it to a smooth field `w` on all of
`ℝⁿ⁺¹` (`SymplecticGeometry.exists_contDiff_eqOn_of_contDiffOn_halfSpace`,
`TauCeti.exists_contDiff_eqOn_mpullbackWithin_extChartAt_symm`). Its flow (Tau Ceti's
`TauCeti.flowOf`, on the boundaryless space `ℝⁿ⁺¹`) is smooth. Since the zeroth coordinate of
`w` is negative at `φ p`, near `φ p` the zeroth coordinate of each trajectory is strictly
decreasing, so a trajectory starting on the boundary hyperplane is in the open half-space at
negative times and outside it at positive times. At negative times it stays where `w` is the
coordinate field of `Y`, so `φ⁻¹` carries it to an integral curve of `Y`.

Written in the boundary chart at `p` and with time reversed, the flow from the boundary is a map
`G (z, τ) = flowOf w (-τ 0) (z inserted as a point with zeroth coordinate 0)` between open subsets
of `ℝⁿ × ℝ¹` and `ℝⁿ⁺¹`. Its derivative at `(φ p, 0)` is invertible, since `w (φ p)` is
transverse to the boundary hyperplane, so by the inverse function theorem in the boundaryless
spaces it is a local diffeomorphism there; and near that point it sends `ℝⁿ × [0, ∞)` exactly
into the half-space. So it restricts to a local diffeomorphism of the half-space models
(`PartialDiffeomorph.isLocalDiffeomorphAt_symm_comp_comp_model`), and in the charts of
`∂W × [0, ∞)` and `W` this is the map `(x, t) ↦ γ (-t, x)`.

Uniqueness: an integral curve of an outward field cannot meet the boundary at a time near which
it is defined on both sides, since the zeroth chart coordinate would have a local minimum with
negative derivative (`IsMIntegralCurveOn.mem_interior_of_isOutwardPointing`); so two integral
curves on `(-η, 0]` are in the interior at negative times, where Tau Ceti's uniqueness theorem
`IsMIntegralCurveOn.eqOn_of_isPreconnected` applies. When they start at a boundary point, they
first agree on some `[l, 0]` by uniqueness for the equation of the extended field in the chart
(`ODE_solution_unique_of_mem_Icc_left`).

## Main results

* `SymplecticGeometry.exists_contDiff_eqOn_of_contDiffOn_halfSpace`: a map smooth on a relatively
  open part of the half-space agrees near a boundary point with a smooth map on `ℝⁿ⁺¹`.
* `TauCeti.isLocalDiffeomorphAt_flowOf_euclideanHalfSpaceBoundaryParam`: the flow of a field
  transverse to the boundary hyperplane, out of that hyperplane, is a local diffeomorphism.
* `TauCeti.exists_isMIntegralCurveOn_of_isOutwardPointing`: integral curves of an outward field
  entering from the boundary near `p`, forming a local diffeomorphism `∂W × [0, η) → W`.
* `IsMIntegralCurveOn.eqOn_of_isOutwardPointing`: two integral curves of an outward field on
  `(-η, 0]` that agree at time `0` agree.

## References

* R. T. Seeley, *Extension of $C^\infty$ functions defined in a half space*,
  Proc. Amer. Math. Soc. 15 (1964), 625–626.
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218, 2013, Chapter 9
  (flows, and the collar theorem 9.25 that this file prepares).
* M. Hirsch, *Differential Topology*, Springer GTM 33, 1976, Chapter 4, Theorem 6.1.
-/

public section

open Set Filter Function Topology VectorField SymplecticGeometry
open scoped Manifold ContDiff

section CoordinateField

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {V : (x : M) → TangentSpace I x}

/-- A smooth vector field, read in an extended chart, is smooth on the chart target. -/
theorem ContMDiff.contDiffOn_mpullbackWithin_extChartAt_symm [CompleteSpace E]
    (hV : CMDiff ∞ (T% V)) (x : M) :
    ContDiffOn ℝ ∞ (mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm V (range I))
      (extChartAt I x).target := fun y hy ↦
  contMDiffWithinAt_vectorSpace_iff_contDiffWithinAt.1 <|
    ContMDiffWithinAt.mpullbackWithin_vectorField_of_eq' (t := univ) (n := ∞)
      (hV _).contMDiffWithinAt (contMDiffWithinAt_extChartAt_symm_range x hy)
      (isInvertible_mfderivWithin_extChartAt_symm hy) hy
      (uniqueMDiffOn_iff_uniqueDiffOn.2 (uniqueDiffOn_extChartAt_target x)) (by simp) (by simp)
      (extChartAt_target_subset_range x) rfl

/-- The derivative of the inverse chart sends the coordinate expression of a vector field back to
the field. -/
theorem mfderivWithin_extChartAt_symm_mpullbackWithin {x : M} {y : E}
    (hy : y ∈ (extChartAt I x).target) :
    mfderivWithin 𝓘(ℝ, E) I (extChartAt I x).symm (range I) y
      (mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm V (range I) y) =
        V ((extChartAt I x).symm y) := by
  rw [mpullbackWithin_apply]
  exact ((isInvertible_mfderivWithin_extChartAt_symm hy).inverse_apply_eq.1 rfl).symm

/-- At the chart image of a point `z`, the coordinate expression of a vector field is the image of
the field at `z` under the derivative of the chart. -/
theorem mpullbackWithin_extChartAt_symm_apply_extChartAt {x z : M}
    (hz : z ∈ (extChartAt I x).source) :
    mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm V (range I) (extChartAt I x z) =
      mfderiv I 𝓘(ℝ, E) (extChartAt I x) z (V z) := by
  rw [mpullbackWithin_apply, (isInvertible_mfderivWithin_extChartAt_symm
    ((extChartAt I x).map_source hz)).inverse_apply_eq, (extChartAt I x).left_inv hz]
  exact (DFunLike.congr_fun (mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' hz)
    (V z)).symm

end CoordinateField

namespace SymplecticGeometry

section Extension

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Seeley's extension near a boundary point of the half-space.** A map on `ℝⁿ⁺¹` that is
smooth on the part of an open set `U` where the zeroth coordinate is nonnegative agrees, near a
point of `U` with vanishing zeroth coordinate and on that part, with a smooth map on `ℝⁿ⁺¹`. -/
theorem exists_contDiff_eqOn_of_contDiffOn_halfSpace {f : EuclideanSpace ℝ (Fin (n + 1)) → F}
    {U : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f (U ∩ {y | 0 ≤ y 0})) {y₀ : EuclideanSpace ℝ (Fin (n + 1))}
    (hy₀ : y₀ ∈ U) (hy₀0 : y₀ 0 = 0) :
    ∃ g : EuclideanSpace ℝ (Fin (n + 1)) → F, ContDiff ℝ ∞ g ∧
      ∃ V, IsOpen V ∧ y₀ ∈ V ∧ EqOn g f (V ∩ {y | 0 ≤ y 0}) := by
  set N := TauCeti.euclideanHalfSpaceBoundaryNormalEquiv n
  have hN0 := TauCeti.euclideanHalfSpaceBoundaryNormalEquiv_symm_apply_snd n
  have hNN (y : EuclideanSpace ℝ (Fin (n + 1))) : N ((N.symm y).1, (N.symm y).2) = y := by
    simp
  -- A box `B ×ˢ (-a, a)` around `N⁻¹ y₀` whose image lies in `U`.
  obtain ⟨B, a, hB, hzB, ha, hBa⟩ : ∃ B : Set (EuclideanSpace ℝ (Fin n)), ∃ a : ℝ, IsOpen B ∧
      (N.symm y₀).1 ∈ B ∧ 0 < a ∧ ∀ z ∈ B, ∀ s ∈ Ioo (-a) a, N (z, s) ∈ U := by
    have hmem : N ⁻¹' U ∈ 𝓝 ((N.symm y₀).1, (0 : ℝ)) := by
      refine (hU.preimage N.continuous).mem_nhds ?_
      rw [← hy₀0, ← hN0, mem_preimage, hNN]
      exact hy₀
    rw [nhds_prod_eq, mem_prod_iff] at hmem
    obtain ⟨u, hu, v, hv, huv⟩ := hmem
    obtain ⟨B, hBu, hB, hzB⟩ := mem_nhds_iff.1 hu
    obtain ⟨a, ha, hav⟩ := Metric.mem_nhds_iff.1 hv
    refine ⟨B, a, hB, hzB, ha, fun z hz s hs ↦ huv ⟨hBu hz, hav ?_⟩⟩
    rw [Real.ball_eq_Ioo, zero_sub, zero_add]
    exact hs
  -- The map read in `B × ℝ`, cut off in the normal coordinate.
  set χ : ℝ → ℝ := fun s ↦ seeleyCutoff (s / a)
  set f' : ℝ × EuclideanSpace ℝ (Fin n) → F := fun q ↦ χ q.1 • f (N (q.2, q.1))
  have hf' : ContDiffOn ℝ ∞ f' (Ici 0 ×ˢ B) := by
    refine contDiffOn_of_locally_contDiffOn fun q _ ↦ ?_
    rcases lt_or_ge q.1 a with hqa | hqa
    · refine ⟨Iio a ×ˢ univ, isOpen_Iio.prod isOpen_univ, ⟨hqa, trivial⟩, ?_⟩
      have hχ : ContDiff ℝ ∞ χ := contDiff_seeleyCutoff.comp (contDiff_id.div_const a)
      refine (hχ.comp contDiff_fst).contDiffOn.smul (hf.comp
        (N.contDiff.comp (contDiff_snd.prodMk contDiff_fst)).contDiffOn ?_)
      rintro r ⟨⟨hr0, hrB⟩, hra, -⟩
      refine ⟨hBa _ hrB _ ⟨by linarith [mem_Ici.1 hr0], hra⟩, ?_⟩
      simpa [N] using hr0
    · refine ⟨Ioi (3 / 4 * a) ×ˢ univ, isOpen_Ioi.prod isOpen_univ,
        ⟨show 3 / 4 * a < q.1 by linarith, trivial⟩, ?_⟩
      refine (contDiffOn_const (c := (0 : F))).congr fun r hr ↦ ?_
      have : χ r.1 = 0 := seeleyCutoff_eq_zero_of_le (by
        rw [le_div_iff₀ ha]; linarith [mem_Ioi.1 hr.2.1])
      simp [f', this]
  -- Seeley's extension of the cut-off map, read in `ℝⁿ⁺¹`.
  set g₀ : EuclideanSpace ℝ (Fin (n + 1)) → F :=
    fun y ↦ seeleyExtend (fun s ↦ f' (s, (N.symm y).1)) (N.symm y).2
  set O : Set (EuclideanSpace ℝ (Fin (n + 1))) := (fun y ↦ (N.symm y).1) ⁻¹' B
  have hO : IsOpen O := hB.preimage (continuous_fst.comp N.symm.continuous)
  have hg₀ : ContDiffOn ℝ ∞ g₀ O :=
    (contDiffOn_seeleyExtend hB hf').comp
      ((contDiff_snd.prodMk contDiff_fst).comp N.symm.contDiff).contDiffOn
      fun y hy ↦ ⟨trivial, hy⟩
  have hg₀f : ∀ y ∈ O, 0 ≤ y 0 → y 0 < a / 2 → g₀ y = f y := by
    intro y _ hy0 hya
    simp only [g₀]
    rw [show (N.symm y).2 = y 0 from hN0 y]
    rw [seeleyExtend_of_nonneg _ hy0]
    simp only [f', χ]
    rw [seeleyCutoff_eq_one_of_le (by rw [div_le_iff₀ ha]; linarith), one_smul, ← hN0, hNN]
  -- A bump function around `y₀`, supported in `O`.
  obtain ⟨r, hr, hrO⟩ := Metric.isOpen_iff.1 hO y₀ (show (N.symm y₀).1 ∈ B from hzB)
  let ρ : ContDiffBump y₀ := ⟨r / 4, r / 2, by positivity, by linarith⟩
  refine ⟨fun y ↦ ρ y • g₀ y, ?_, O ∩ (Metric.ball y₀ (r / 4) ∩ {y | y 0 < a / 2}),
    hO.inter (Metric.isOpen_ball.inter (isOpen_lt (by fun_prop)
      continuous_const)), ⟨hrO (Metric.mem_ball_self hr), Metric.mem_ball_self (by positivity),
      by simp [hy₀0, ha]⟩, ?_⟩
  · refine contDiff_iff_contDiffAt.2 fun y ↦ ?_
    by_cases hy : y ∈ Metric.ball y₀ r
    · exact ρ.contDiff.contDiffAt.smul (hg₀.contDiffAt (hO.mem_nhds (hrO hy)))
    · have hy' : y ∈ (Metric.closedBall y₀ (r / 2))ᶜ := fun h ↦
        hy (Metric.closedBall_subset_ball (by linarith) h)
      refine contDiffAt_const (c := (0 : F)).congr_of_eventuallyEq ?_
      filter_upwards [Metric.isClosed_closedBall.isOpen_compl.mem_nhds hy'] with y' hy''
      rw [ρ.zero_of_le_dist (le_of_lt (by simpa using hy'')), zero_smul]
  · rintro y ⟨⟨hyO, hyb, hya⟩, hy0⟩
    simp only
    rw [ρ.one_of_mem_closedBall (Metric.ball_subset_closedBall hyb), one_smul]
    exact hg₀f y hyO hy0 hya

end Extension

end SymplecticGeometry

namespace TauCeti

variable {n : ℕ} {W : Type*} [TopologicalSpace W] [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
  {Y : (x : W) → TangentSpace (𝓡∂ (n + 1)) x}

/-- The extended chart of a manifold modelled on the half-space reads a point of its target as a
boundary point exactly when its zeroth coordinate vanishes. -/
theorem extChartAt_symm_mem_boundary_iff {q : W} {z : EuclideanSpace ℝ (Fin (n + 1))}
    (hz : z ∈ (extChartAt (𝓡∂ (n + 1)) q).target) :
    (extChartAt (𝓡∂ (n + 1)) q).symm z ∈ (𝓡∂ (n + 1)).boundary W ↔ z 0 = 0 := by
  have hs := (extChartAt (𝓡∂ (n + 1)) q).map_target hz
  rw [extChartAt_source] at hs
  rw [ModelWithCorners.mem_boundary_euclideanHalfSpace_iff hs]
  have h := (extChartAt (𝓡∂ (n + 1)) q).right_inv hz
  rw [extChartAt_coe, comp_apply, modelWithCornersEuclideanHalfSpace_apply] at h
  rw [h]

/-- A point of the target of the extended chart at a boundary point `q` whose zeroth coordinate
is positive is read by the inverse chart as an interior point. -/
theorem extChartAt_symm_mem_interior {q : W} {z : EuclideanSpace ℝ (Fin (n + 1))}
    (hz : z ∈ (extChartAt (𝓡∂ (n + 1)) q).target) (hz0 : 0 < z 0) :
    (extChartAt (𝓡∂ (n + 1)) q).symm z ∈ (𝓡∂ (n + 1)).interior W := by
  rw [← ModelWithCorners.compl_boundary, mem_compl_iff, extChartAt_symm_mem_boundary_iff hz]
  exact hz0.ne'

/-- The extended chart at a boundary point sends it to the boundary hyperplane. -/
theorem extChartAt_self_apply_zero {q : W} (hq : q ∈ (𝓡∂ (n + 1)).boundary W) :
    extChartAt (𝓡∂ (n + 1)) q q 0 = 0 := by
  have h := (extChartAt_symm_mem_boundary_iff (W := W) (n := n)
    (mem_extChartAt_target (I := 𝓡∂ (n + 1)) q)).1
  rw [extChartAt_to_inv] at h
  exact h hq

/-- A boundary point read in the extended chart at a boundary point `p` is the zero-insertion of
its reading in the boundary chart at `p`. -/
theorem euclideanHalfSpaceBoundaryParam_chartAt_boundary {p x : (𝓡∂ (n + 1)).boundary W}
    (hx : (x : W) ∈ (extChartAt (𝓡∂ (n + 1)) (p : W)).source) :
    euclideanHalfSpaceBoundaryParam n (chartAt (EuclideanSpace ℝ (Fin n)) p x) =
      extChartAt (𝓡∂ (n + 1)) (p : W) x := by
  rw [extChartAt_source] at hx
  rw [boundaryChartedSpace_chartAt_apply, extChartAt_coe, comp_apply,
    modelWithCornersEuclideanHalfSpace_apply, ← EuclideanHalfSpace.boundaryParam_coe,
    EuclideanHalfSpace.boundaryProj_coe]
  exact congrArg Subtype.val (EuclideanHalfSpace.boundaryParam_boundaryProj
    ((ModelWithCorners.mem_boundary_euclideanHalfSpace_iff hx).1 x.property))

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
  obtain ⟨U, hU, hqU, hUt⟩ :=
    mem_nhdsWithin.1 (extChartAt_target_mem_nhdsWithin (I := 𝓡∂ (n + 1)) q)
  have hf := (hY.contDiffOn_mpullbackWithin_extChartAt_symm q).mono hUt
  rw [range_modelWithCornersEuclideanHalfSpace] at hf hUt
  obtain ⟨w, hw, V, hV, hqV, hwV⟩ :=
    exists_contDiff_eqOn_of_contDiffOn_halfSpace hU hf hqU (extChartAt_self_apply_zero hq)
  refine ⟨w, hw, V ∩ U, hV.inter hU, ⟨hqV, hqU⟩, ?_, ?_⟩ <;>
    rw [range_modelWithCornersEuclideanHalfSpace]
  · exact fun y hy ↦ hUt (show y ∈ U ∩ {y | 0 ≤ y 0} from ⟨hy.1.2, hy.2⟩)
  · exact hwV.mono fun y hy ↦ (show y ∈ V ∩ {y | 0 ≤ y 0} from ⟨hy.1.1, hy.2⟩)

section Box

variable {w : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}

/-- Near a point `y₀` at which a smooth field `w` on `ℝⁿ⁺¹` has negative zeroth coordinate, its
flow is defined, stays in a given open neighbourhood `V` of `y₀` and keeps that coordinate of `w`
negative, on a box of times and initial points; on it, the zeroth coordinate of each trajectory
is strictly decreasing. -/
private theorem exists_flowOf_box (hw : ContDiff ℝ ∞ w) {V : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (hV : IsOpen V) {y₀ : EuclideanSpace ℝ (Fin (n + 1))} (hy₀ : y₀ ∈ V) (hw₀ : w y₀ 0 < 0) :
    ∃ η > 0, ∃ r > 0, (∀ s ∈ Ioo (-η) η, ∀ y ∈ Metric.ball y₀ r,
      (s, y) ∈ flowDomain (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))) w ∧
        flowOf (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))) w s y ∈ V) ∧
      ∀ y ∈ Metric.ball y₀ r,
        StrictAntiOn (fun s ↦ flowOf (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))) w s y 0)
          (Ioo (-η) η) := by
  set D := flowDomain (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))) w
  have hw1 : CMDiff 1 (fun y ↦ (⟨y, w y⟩ : TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
      (EuclideanSpace ℝ (Fin (n + 1))))) :=
    contMDiff_vectorSpace_iff_contDiff.2 (hw.of_le (m := 1) (by simp))
  have hD : IsOpen D := isOpen_flowDomain hw1
  have h0 : ((0 : ℝ), y₀) ∈ D := mem_flowDomain_zero hw1 y₀
  have hcont : ContinuousAt (fun p : ℝ × EuclideanSpace ℝ (Fin (n + 1)) ↦
      flowOf (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))) w p.1 p.2) (0, y₀) :=
    (contDiffOn_flowOf_uncurry hw).continuousOn.continuousAt (hD.mem_nhds h0)
  set O := V ∩ {z : EuclideanSpace ℝ (Fin (n + 1)) | w z 0 < 0}
  have hO : IsOpen O := hV.inter (isOpen_lt (by fun_prop) continuous_const)
  have hmem : D ∩ (fun p : ℝ × EuclideanSpace ℝ (Fin (n + 1)) ↦
      flowOf (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))) w p.1 p.2) ⁻¹' O ∈ 𝓝 (0, y₀) :=
    inter_mem (hD.mem_nhds h0) (hcont.preimage_mem_nhds (hO.mem_nhds (by
      have h := flowOf_zero (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))) w y₀
      exact h.symm ▸ ⟨hy₀, hw₀⟩)))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hmem
  have hbox : ∀ s ∈ Ioo (-ε) ε, ∀ y ∈ Metric.ball y₀ ε, (s, y) ∈ D ∧
      flowOf (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))) w s y ∈ O := fun s hs y hy ↦
    hball (by
      rw [← ball_prod_same, Real.ball_eq_Ioo, zero_sub, zero_add]
      exact ⟨hs, hy⟩)
  refine ⟨ε, hε, ε, hε, fun s hs y hy ↦ ⟨(hbox s hs y hy).1, (hbox s hs y hy).2.1⟩,
    fun y hy ↦ ?_⟩
  -- The zeroth coordinate of a trajectory has derivative the zeroth coordinate of `w`.
  have hderiv : ∀ s ∈ Ioo (-ε) ε, HasDerivAt
      (fun s ↦ flowOf (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))) w s y 0)
      (w (flowOf (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))) w s y) 0) s := fun s hs ↦
    (PiLp.proj 2 (fun _ : Fin (n + 1) ↦ ℝ) 0).hasFDerivAt.comp_hasDerivAt s
      (hasDerivAt_flowOf hw (hbox s hs y hy).1)
  refine strictAntiOn_of_hasDerivWithinAt_neg (convex_Ioo _ _)
    (fun s hs ↦ (hderiv s hs).continuousAt.continuousWithinAt)
    (fun s hs ↦ (hderiv s (interior_subset hs)).hasDerivWithinAt) fun s hs ↦ ?_
  exact (hbox s (interior_subset hs) y hy).2.2

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
    (contDiffOn_flowOf_uncurry hw).comp L.contDiff.contDiffOn fun _ hq ↦ hq
  have hGd : HasFDerivAt G (((ContinuousLinearMap.fst ℝ ℝ _).smulRight (w (ι z₀)) +
      ContinuousLinearMap.snd ℝ ℝ _).comp L) (z₀, 0) := by
    have h := hasFDerivAt_flowOf_uncurry_zero hw (ι z₀)
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
end Box

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
  set φ := extChartAt (𝓡∂ (n + 1)) (p : W) with hφ
  obtain ⟨w, hw, V, hV, hpV, hVt, hwv⟩ :=
    exists_contDiff_eqOn_mpullbackWithin_extChartAt_symm hYs p.property
  have hpr : φ p ∈ range (𝓡∂ (n + 1)) :=
    extChartAt_target_subset_range _ (mem_extChartAt_target _)
  have hw₀ : w (φ p) 0 < 0 := by
    have h := (isOutwardPointing_iff.1 (hYb p p.property)).2
    rw [← mpullbackWithin_extChartAt_symm_apply_extChartAt (mem_extChartAt_source (p : W)),
      ← hwv ⟨hpV, hpr⟩] at h
    exact h
  obtain ⟨η₀, hη₀, r, hr, hbox, hanti⟩ := exists_flowOf_box hw hV hpV hw₀
  have hflow0 (y : EuclideanSpace ℝ (Fin (n + 1))) :
      flowOf (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))) w 0 y = y :=
    flowOf_zero _ y
  -- Along a trajectory from the boundary hyperplane, the zeroth coordinate is nonnegative exactly
  -- at nonpositive times.
  have hsign : ∀ y ∈ Metric.ball (φ p) r, y 0 = 0 → ∀ s ∈ Ioo (-η₀) η₀,
      (0 ≤ flowOf (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))) w s y 0 ↔ s ≤ 0) ∧
        (0 < flowOf (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))) w s y 0 ↔ s < 0) := by
    intro y hy hy0 s hs
    have h0 : flowOf (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))) w 0 y 0 = 0 := by
      rw [hflow0, hy0]
    have hm : (0 : ℝ) ∈ Ioo (-η₀) η₀ := ⟨by linarith, hη₀⟩
    have h1 := StrictAntiOn.le_iff_ge (hanti y hy) hm hs
    have h2 := StrictAntiOn.lt_iff_gt (hanti y hy) hm hs
    simp only [h0] at h1 h2
    exact ⟨h1, h2⟩
  have hmemV : ∀ y ∈ Metric.ball (φ p) r, y 0 = 0 → ∀ s ∈ Ioc (-η₀) 0,
      flowOf (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))) w s y ∈
        V ∩ range (𝓡∂ (n + 1)) := by
    intro y hy hy0 s hs
    have hs' : s ∈ Ioo (-η₀) η₀ := ⟨hs.1, by linarith [hs.2]⟩
    refine ⟨(hbox s hs' y hy).2, ?_⟩
    rw [range_modelWithCornersEuclideanHalfSpace]
    exact (hsign y hy hy0 s hs').1.2 hs.2
  -- The flow from the boundary, read in the boundary chart at `p` and with time reversed.
  set ι := euclideanHalfSpaceBoundaryParam n
  set z₀ := chartAt (EuclideanSpace ℝ (Fin n)) p p
  have hz₀ : ι z₀ = φ p :=
    euclideanHalfSpaceBoundaryParam_chartAt_boundary (mem_extChartAt_source _)
  have hGloc := isLocalDiffeomorphAt_flowOf_euclideanHalfSpaceBoundaryParam hw z₀
    (by rw [hz₀]; exact hw₀.ne)
  set G : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin (n + 1)) :=
    fun q ↦ flowOf (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))) w (-q.2 0) (ι q.1)
  -- A partial diffeomorphism agreeing with `G`, on whose source the sign lemma applies.
  obtain ⟨Θ, hΘ0, hGΘ⟩ := hGloc.exists_partialDiffeomorph
  set R : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin 1)) :=
    {q | -q.2 0 ∈ Ioo (-η₀) η₀ ∧ ι q.1 ∈ Metric.ball (φ p) r}
  have hR : IsOpen R :=
    (isOpen_Ioo.preimage (by fun_prop)).inter (Metric.isOpen_ball.preimage (by fun_prop))
  have hz₀R : (z₀, (0 : EuclideanSpace ℝ (Fin 1))) ∈ R :=
    ⟨by simp [hη₀], by rw [hz₀]; exact Metric.mem_ball_self hr⟩
  set Θ' := Θ.restrOpen R hR
  have hΘ'src : Θ'.source = Θ.source ∩ R := PartialDiffeomorph.restrOpen_source _ hR
  have hΘ'G : ∀ q ∈ Θ'.source, Θ' q = G q := fun q hq ↦ by
    rw [PartialDiffeomorph.coe_restrOpen, ← hGΘ (hΘ'src ▸ hq).1]
  have hcond : ∀ q ∈ Θ'.source,
      Θ' q ∈ range (𝓡∂ (n + 1)) ↔ q ∈ range ((𝓡 n).prod (𝓡∂ 1)) := by
    rintro ⟨z, τ⟩ hq
    rw [hΘ'G _ hq]
    rw [hΘ'src] at hq
    rw [ModelWithCorners.range_prod, range_modelWithCornersEuclideanHalfSpace,
      range_modelWithCornersEuclideanHalfSpace]
    simp only [mem_ofPred_eq, mem_prod, modelWithCornersSelf_coe, range_id, mem_univ, true_and]
    rw [(hsign (ι z) hq.2.2 (euclideanHalfSpaceBoundaryParam_apply_zero z) (-τ 0) hq.2.1).1,
      neg_nonpos]
  -- A product box in the source of `Θ'`, and the corresponding set `B` of boundary points.
  obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.1 Θ'.open_source (z₀, 0)
    (by rw [hΘ'src]; exact ⟨hΘ0, hz₀R⟩)
  set β := chartAt (EuclideanSpace ℝ (Fin n)) p
  set B : Set ((𝓡∂ (n + 1)).boundary W) := β.source ∩ β ⁻¹' Metric.ball z₀ ε
  have hB : IsOpen B := β.continuousOn.isOpen_inter_preimage β.open_source Metric.isOpen_ball
  have hpB : p ∈ B := ⟨mem_chart_source _ p, Metric.mem_ball_self hε⟩
  have hBsrc : ∀ x ∈ B, (x : W) ∈ φ.source := fun x hx ↦ by
    have h := hx.1
    rw [boundaryChartedSpace_chartAt_source] at h
    rw [extChartAt_source]
    exact h
  have hBΘ : ∀ x ∈ B, ∀ τ : EuclideanSpace ℝ (Fin 1), ‖τ‖ < ε → (β x, τ) ∈ Θ'.source :=
    fun x hx τ hτ ↦ hεsub (by
      rw [Metric.mem_ball, Prod.dist_eq]
      exact max_lt hx.2 (by simpa using hτ))
  have hBι : ∀ x ∈ B, ι (β x) = φ x := fun x hx ↦
    euclideanHalfSpaceBoundaryParam_chartAt_boundary (hBsrc x hx)
  have hBball : ∀ x ∈ B, φ x ∈ Metric.ball (φ p) r := fun x hx ↦ by
    have h := hBΘ x hx 0 (by simpa using hε)
    rw [hΘ'src] at h
    rw [← hBι x hx]
    exact h.2.2
  have hB0 : ∀ x ∈ B, φ x 0 = 0 := fun x hx ↦ by
    rw [← hBι x hx]
    exact euclideanHalfSpaceBoundaryParam_apply_zero _
  refine ⟨B, min η₀ ε, fun q ↦ φ.symm (flowOf (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))) w q.1
    (φ q.2)), hB, hpB, lt_min hη₀ hε, fun x hx ↦ ?_, fun x hx s hs ↦ ?_, fun x hx ↦ ?_, ?_⟩
  · -- The curves start on the boundary.
    simp only [hflow0]
    exact φ.left_inv (hBsrc x hx)
  · -- They run in the interior at negative times.
    have hs' : s ∈ Ioo (-η₀) η₀ := ⟨lt_of_le_of_lt (neg_le_neg (min_le_left _ _)) hs.1,
      by linarith [hs.2]⟩
    exact extChartAt_symm_mem_interior
      (hVt (hmemV _ (hBball x hx) (hB0 x hx) s ⟨hs'.1, hs.2.le⟩))
      ((hsign _ (hBball x hx) (hB0 x hx) s hs').2.2 hs.2)
  · -- They are integral curves of `Y`.
    have hmem : ∀ s ∈ Ioc (-min η₀ ε) 0,
        flowOf (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))) w s (φ x) ∈
          V ∩ range (𝓡∂ (n + 1)) := fun s hs ↦
      hmemV _ (hBball x hx) (hB0 x hx) s
        ⟨lt_of_le_of_lt (neg_le_neg (min_le_left _ _)) hs.1, hs.2⟩
    intro s hs
    have hs' : s ∈ Ioo (-η₀) η₀ := ⟨lt_of_le_of_lt (neg_le_neg (min_le_left _ _)) hs.1,
      by linarith [hs.2]⟩
    have ht := hVt (hmem s hs)
    have hd : HasDerivWithinAt
        (fun s ↦ flowOf (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))) w s (φ x))
        (mpullbackWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) (𝓡∂ (n + 1)) φ.symm Y
          (range (𝓡∂ (n + 1)))
          (flowOf (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))) w s (φ x)))
        (Ioc (-min η₀ ε) 0) s := by
      rw [← hwv (hmem s hs)]
      exact (hasDerivAt_flowOf hw (hbox s hs' _ (hBball x hx)).1).hasDerivWithinAt
    have h := Manifold.hasMFDerivWithinAt_extChartAt_symm_comp ht
      (eventually_nhdsWithin_of_forall fun r hr ↦ (hmem r hr).2) hd
    rwa [mfderivWithin_extChartAt_symm_mpullbackWithin ht] at h
  · -- Read in charts, `(x, t) ↦ γ (-t, x)` is the restriction of `Θ'` to the half-spaces.
    have : IsManifold (𝓡 n) ∞ ((𝓡∂ (n + 1)).boundary W) := isManifold_boundary W
    set C := chartAt (ModelProd (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace 1))
      ((p, 0) : (𝓡∂ (n + 1)).boundary W × EuclideanHalfSpace 1)
    have hCapply (q : (𝓡∂ (n + 1)).boundary W × EuclideanHalfSpace 1) : C q = (β q.1, q.2) := by
      simp only [C, β, prodChartedSpace_chartAt, chartAt_self_eq]
      rw [OpenPartialHomeomorph.prod_apply, OpenPartialHomeomorph.refl_apply]
      rfl
    have hCsrc (q : (𝓡∂ (n + 1)).boundary W × EuclideanHalfSpace 1) (hq : q.1 ∈ B) :
        q ∈ C.source := by
      simp only [C, prodChartedSpace_chartAt, OpenPartialHomeomorph.prod_source, chartAt_self_eq,
        OpenPartialHomeomorph.refl_source]
      exact ⟨hq.1, mem_univ _⟩
    have hI (q : EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1) :
        ((𝓡 n).prod (𝓡∂ 1)) q = (q.1, q.2.val) := rfl
    have hG (q : (𝓡∂ (n + 1)).boundary W × EuclideanHalfSpace 1)
        (hq : q ∈ B ×ˢ EuclideanHalfSpace.normalIio (min η₀ ε)) :
        ((𝓡 n).prod (𝓡∂ 1)) (C q) ∈ Θ'.source ∧
          Θ' (((𝓡 n).prod (𝓡∂ 1)) (C q)) =
            flowOf (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))) w (-q.2.val 0) (φ q.1) ∧
          flowOf (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))) w (-q.2.val 0) (φ q.1) ∈
            V ∩ range (𝓡∂ (n + 1)) := by
      obtain ⟨hq1, hq2⟩ := hq
      rw [EuclideanHalfSpace.mem_normalIio] at hq2
      have h0 : 0 ≤ q.2.val 0 := q.2.property
      have hnorm : ‖q.2.val‖ < ε := by
        have h : ‖q.2.val‖ = |q.2.val 0| := by
          simp [EuclideanSpace.norm_eq, Real.sqrt_sq_eq_abs]
        rw [h, abs_of_nonneg h0]
        exact lt_of_lt_of_le hq2 (min_le_right _ _)
      have hsrc : ((𝓡 n).prod (𝓡∂ 1)) (C q) ∈ Θ'.source := by
        rw [hCapply, hI]
        exact hBΘ _ hq1 _ hnorm
      refine ⟨hsrc, ?_, hmemV _ (hBball _ hq1) (hB0 _ hq1) _
        ⟨by linarith [lt_of_lt_of_le hq2 (min_le_left _ _)], by linarith⟩⟩
      rw [hΘ'G _ hsrc, hCapply, hI]
      simp only [G, hBι _ hq1]
    rintro ⟨q, hq⟩
    obtain ⟨hsrc, hval, hmem⟩ := hG q hq
    have hl := Θ'.isLocalDiffeomorphAt_symm_comp_comp_model ((𝓡 n).prod (𝓡∂ 1)) (𝓡∂ (n + 1))
      hcond hsrc
    have hχ : (𝓡∂ (n + 1)).symm (Θ' (((𝓡 n).prod (𝓡∂ 1)) (C q))) ∈
        (chartAt (EuclideanHalfSpace (n + 1)) (p : W)).target := by
      have h := hVt hmem
      rw [extChartAt_target] at h
      rw [hval]
      exact h.1
    have hc := (C.isLocalDiffeomorphAt_of_mem_maximalAtlas (n := ∞)
      (IsManifold.chart_mem_maximalAtlas _)
      (hCsrc q hq.1)).comp (hg := hl.comp (hg :=
        (OpenPartialHomeomorph.isLocalDiffeomorphAt_symm_of_mem_maximalAtlas
          (chartAt (EuclideanHalfSpace (n + 1)) (p : W))
          (IsManifold.chart_mem_maximalAtlas _) hχ)))
    refine hc.congr_of_eventuallyEq ?_
    filter_upwards [(hB.prod (EuclideanHalfSpace.isOpen_normalIio _)).mem_nhds hq] with q' hq'
    simp only [comp_apply, (hG q' hq').2.1, hφ, extChartAt_coe_symm]

/-- An integral curve of a vector field that points outward along the boundary is in the interior
at every time near which it is defined on both sides. -/
theorem _root_.IsMIntegralCurveOn.mem_interior_of_isOutwardPointing
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

/-- Two integral curves of a smooth field on `(-η, 0]` that start at the same boundary point agree
on some interval `[l, 0]` with `-η < l < 0`: in the chart at that point, both solve the equation of
the extended field. -/
private theorem exists_eqOn_Icc_of_mem_boundary (hY : CMDiff ∞ (T% Y)) {γ δ : ℝ → W} {η : ℝ}
    (hη : 0 < η) (hγ : IsMIntegralCurveOn γ Y (Ioc (-η) 0))
    (hδ : IsMIntegralCurveOn δ Y (Ioc (-η) 0)) (h0 : γ 0 = δ 0)
    (hb : γ 0 ∈ (𝓡∂ (n + 1)).boundary W) :
    ∃ l ∈ Ioo (-η) 0, EqOn γ δ (Icc l 0) := by
  set φ := extChartAt (𝓡∂ (n + 1)) (γ 0)
  obtain ⟨w, hw, V, hV, hqV, -, hwv⟩ := exists_contDiff_eqOn_mpullbackWithin_extChartAt_symm hY hb
  obtain ⟨K, T, hT, hK⟩ :=
    ((hw.of_le (m := 1) (by simp)).contDiffAt (x := φ (γ 0))).exists_lipschitzOnWith
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
  -- The chart images solve `y' = w y`, since `w` is the coordinate field on the half-space.
  have hderiv : ∀ c : ℝ → W, IsMIntegralCurveOn c Y (Ioc (-η) 0) →
      (∀ r ∈ Icc l 0, c r ∈ φ.source ∧ φ (c r) ∈ V ∩ T) → ∀ r ∈ Ioc l 0,
        HasDerivWithinAt (φ ∘ c) (w ((φ ∘ c) r)) (Iic r) r := by
    intro c hc hcg r hr
    have hr' : r ∈ Icc l 0 := Ioc_subset_Icc_self hr
    have hsrc := (hcg r hr').1
    have hd := Manifold.hasDerivWithinAt_comp_curve
      (mdifferentiableAt_extChartAt (by rwa [← extChartAt_source (I := 𝓡∂ (n + 1))]))
      (hc r (hsub hr'))
    have hrange : φ (c r) ∈ range (𝓡∂ (n + 1)) :=
      extChartAt_target_subset_range _ (φ.map_source hsrc)
    have hw' : w ((φ ∘ c) r) = mfderiv (𝓡∂ (n + 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) φ (c r)
        (Y (c r)) := by
      rw [comp_apply, hwv ⟨(hcg r hr').2.1, hrange⟩,
        mpullbackWithin_extChartAt_symm_apply_extChartAt hsrc]
    rw [hw']
    refine hd.mono_of_mem_nhdsWithin (mem_of_superset (Ioc_mem_nhdsLE (by linarith [hl.1, hr.1]))
      fun u hu ↦ ⟨hu.1, hu.2.trans hr.2⟩)
  have hcont : ∀ c : ℝ → W, IsMIntegralCurveOn c Y (Ioc (-η) 0) →
      (∀ r ∈ Icc l 0, c r ∈ φ.source ∧ φ (c r) ∈ V ∩ T) → ContinuousOn (φ ∘ c) (Icc l 0) :=
    fun c hc hcg ↦ (continuousOn_extChartAt (γ 0)).comp (hc.continuousOn.mono hsub)
      fun r hr ↦ (hcg r hr).1
  have heq := ODE_solution_unique_of_mem_Icc_left (v := fun _ ↦ w) (s := fun _ ↦ T)
    (fun _ _ ↦ hK) (hcont γ hγ fun r hr ↦ (hgood r hr).1)
    (hderiv γ hγ fun r hr ↦ (hgood r hr).1)
    (fun r hr ↦ ((hgood r (Ioc_subset_Icc_self hr)).1.2.2))
    (hcont δ hδ fun r hr ↦ (hgood r hr).2) (hderiv δ hδ fun r hr ↦ (hgood r hr).2)
    (fun r hr ↦ ((hgood r (Ioc_subset_Icc_self hr)).2.2.2)) (by simp only [comp_apply, h0])
  exact ⟨l, hl, fun r hr ↦ φ.injOn (hgood r hr).1.1 (hgood r hr).2.1 (heq hr)⟩

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
