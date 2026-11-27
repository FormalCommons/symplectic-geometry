/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Geometry.Manifold.Riemannian.Basic
import TauCeti.Geometry.Manifold.MFDeriv.Curve
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.Riemannian.Distance
import TauCeti.Geometry.Manifold.Riemannian.MetricBridge

/-!
# The Riemannian distance compared with distances in a normed space

This file bounds Mathlib's `Manifold.riemannianEDist` on a manifold `M` whose tangent spaces
carry a Riemannian metric, from above and from below, by distances in a real normed space `F`.

## The mean value inequality

For a map `f : F → M`, `C¹` at the points of the segment from `a` to `b`, the Riemannian
extended distance from `f a` to `f b` is at most any bound `C` on the norms of `df_z (b - a)` for
`z` on the segment: it is at most the length of the image of the segment under `f`.

The proof adapts Tau Ceti's `IsRiemannianManifold.edist_le_of_norm_mfderiv_le`, which states the
same bound for the distance of a Riemannian manifold with a given extended metric equal to its
Riemannian one; here no metric structure on `M` is assumed, and the conclusion is stated for
Mathlib's `Manifold.riemannianEDist`.

## Distances in a chart

Let `M` be Hausdorff and `φ : PartialDiffeomorph I 𝓘(ℝ, F) M F n`, `n ≥ 1`, a chart into a
proper space `F`. If the ball `B` of radius `R` about `φ x` lies in the target of `φ`, and the
differential of `φ` stretches Riemannian norms by at most `C ≠ 0` at every point of the source
whose image lies in `B`, then for every `z ∈ B`, `‖z - φ x‖ ≤ C · d(x, φ⁻¹ z)`, `d` the
Riemannian distance.

The proof bounds the length of each `C¹` path `γ` from `x` to `φ⁻¹ z`. As long as `γ` stays in
the preimage `W` of `B`, Tau Ceti's `TauCeti.Manifold.enorm_sub_le_mul_pathELength` bounds the
displacement of `φ ∘ γ` by `C` times the length of `γ`. A path from `x` with `C` times its length
less than `R` cannot leave `W` (`PartialDiffeomorph.mapsTo_of_mul_pathELength_lt`): while it
stays in `W` it stays in the image under `φ⁻¹` of a closed ball of radius `r < R`, a compact set,
so closed, and Mathlib's `IsClosed.Icc_subset_of_forall_mem_nhdsGT_of_Icc_subset` carries this to
all of `[0, 1]`. Applied to a path to `φ⁻¹ z`, its endpoint gives the bound. Applied to a path
to a point outside `W`, it shows that every point outside `W` is at distance at least `R / C`
from `x`.

This exit-time argument adapts the proof of Tau Ceti's
`TauCeti.IsAsymptoticallyEuclideanEnd.ofReal_mul_sub_le_riemannianEDist`, through its helper
`ofReal_mul_sub_le_riemannianEDist_of_lt`, which in turn follows Mathlib's
`setOfPred_riemannianEDist_lt_subset_nhds`. Here the path is kept in a ball of a chart rather
than in an annulus of an asymptotically Euclidean end.

## Main results

* `Manifold.riemannianEDist_le_of_norm_mfderiv_le`: the mean value inequality for
  `Manifold.riemannianEDist`.
* `PartialDiffeomorph.mapsTo_of_mul_pathELength_lt`: a short enough `C¹` path from `x` stays in
  the preimage of the ball.
* `PartialDiffeomorph.ofReal_norm_sub_le_mul_riemannianEDist`: the lower bound for the
  Riemannian distance by distances in the chart.
* `PartialDiffeomorph.ofReal_le_mul_riemannianEDist_of_notMem`: a point outside the preimage of
  the ball is at distance at least `R / C` from `x`.

## References

* [M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992], Chapter 7, §2
-/

public section

open Bundle Metric Set
open scoped ENNReal NNReal Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ∞ω}

namespace Manifold

/-- **The mean value inequality for the Riemannian distance.** Let `f` be a map from a real
normed space to a manifold with a Riemannian metric, `C¹` at every point of the segment from `a`
to `b`. If its differential at the points of that segment sends `b - a` to vectors of norm at
most `C`, then the Riemannian extended distance from `f a` to `f b` is at most `C`. -/
theorem riemannianEDist_le_of_norm_mfderiv_le {f : F → M} {a b : F} {C : ℝ}
    (hf : ∀ z ∈ segment ℝ a b, ContMDiffAt 𝓘(ℝ, F) I 1 f z)
    (hC : ∀ z ∈ segment ℝ a b, ‖mfderiv 𝓘(ℝ, F) I f z (b - a)‖ ≤ C) :
    riemannianEDist I (f a) (f b) ≤ ENNReal.ofReal C := by
  let c : ℝ → F := fun τ ↦ a + τ • (b - a)
  have hcseg : MapsTo c (Icc 0 1) (segment ℝ a b) := fun τ hτ ↦ by
    rw [segment_eq_image']
    exact ⟨τ, hτ, rfl⟩
  have hcderiv : ∀ τ, HasDerivAt c (b - a) τ := fun τ ↦
    (((hasDerivAt_id' τ).smul_const (b - a)).const_add a).congr_deriv (one_smul ℝ _)
  have hc : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, F) 1 c := by
    rw [contMDiff_iff_contDiff]
    exact contDiff_const.add (contDiff_id.smul contDiff_const)
  have hsmooth : CMDiff[Icc 0 1] 1 (f ∘ c) := fun τ hτ ↦
    (hf _ (hcseg hτ)).comp_contMDiffWithinAt τ hc.contMDiffAt.contMDiffWithinAt
  calc
    riemannianEDist I (f a) (f b) ≤ pathELength I (f ∘ c) 0 1 :=
      riemannianEDist_le_pathELength hsmooth (by simp [c]) (by simp [c]) zero_le_one
    _ = ∫⁻ τ in Ioo 0 1, ‖mfderiv 𝓘(ℝ, ℝ) I (f ∘ c) τ (1 : ℝ)‖ₑ :=
      pathELength_eq_lintegral_mfderiv_Ioo
    _ ≤ ∫⁻ _ in Ioo (0 : ℝ) 1, ENNReal.ofReal C := by
      refine MeasureTheory.setLIntegral_mono' measurableSet_Ioo fun τ hτ ↦ ?_
      have hτ' : c τ ∈ segment ℝ a b := hcseg (Ioo_subset_Icc_self hτ)
      rw [← TauCeti.Manifold.curveVelocity_apply,
        ((hf _ hτ').mdifferentiableAt one_ne_zero).curveVelocity_comp_mfderiv (hcderiv τ),
        ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hC _ hτ')
    _ = ENNReal.ofReal C := by simp

end Manifold

namespace PartialDiffeomorph

/-- Along a `C¹` path from `x` that stays in `φ.source ∩ φ ⁻¹' ball (φ x) R` up to time `t`,
`φ ∘ γ` moves by at most `C` times the length of the path on `[0, 1]`. -/
private theorem enorm_sub_le_mul_pathELength_of_forall_mem
    (φ : PartialDiffeomorph I 𝓘(ℝ, F) M F n) (hn : 1 ≤ n) {x : M} {R : ℝ} {C : ℝ≥0}
    (hC : ∀ y ∈ φ.source, φ y ∈ ball (φ x) R → ∀ v : TangentSpace I y,
      ‖mvfderiv I φ y v‖ ≤ C * ‖v‖)
    {γ : ℝ → M} (hγ0 : γ 0 = x) (hγ : CMDiff[Icc 0 1] 1 γ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hγW : ∀ u ∈ Icc 0 t, γ u ∈ φ.source ∩ φ ⁻¹' ball (φ x) R) :
    ‖φ (γ t) - φ x‖ₑ ≤ C * Manifold.pathELength I γ 0 1 := by
  have hγt : CMDiff[Icc 0 t] 1 γ := hγ.mono (Icc_subset_Icc le_rfl ht.2)
  have h := TauCeti.Manifold.enorm_sub_le_mul_pathELength (f := φ) ht.1
    (hγt.mdifferentiableOn one_ne_zero)
    (((φ.contMDiffOn.of_le hn).comp hγt fun u hu ↦ (hγW u hu).1))
    (fun u hu ↦ φ.mdifferentiableAt (zero_lt_one.trans_le hn).ne' (hγW u hu).1)
    fun u hu ↦ by
      have h := ENNReal.ofReal_le_ofReal
        (hC _ (hγW u hu).1 (hγW u hu).2 (mfderiv[Icc 0 t] γ u 1))
      rw [ofReal_norm, ENNReal.ofReal_mul (NNReal.coe_nonneg C), ofReal_norm,
        ENNReal.ofReal_coe_nnreal, mvfderiv_apply_eq_mfderiv_apply] at h
      -- The norm of `F` read on the tangent space `TangentSpace 𝓘(ℝ, F) _`, which is `F`.
      exact h
  rw [hγ0] at h
  exact h.trans (by gcongr; exact ht.2)

/-- **A short path stays in the chart's ball.** Let `φ` be a `C¹` partial diffeomorphism from
a Hausdorff manifold `M` with a Riemannian metric to a proper real normed space `F`, and `x` a
point of its source. Suppose the ball of radius `R` about `φ x` lies in the target of `φ`, and
the differential of `φ` stretches tangent vectors by at most `C` at the points of the source
whose image lies in that ball. Then a `C¹` path `γ` from `x` with `C` times its length on
`[0, 1]` less than `R` maps `[0, 1]` into `φ.source ∩ φ ⁻¹' ball (φ x) R`. -/
theorem mapsTo_of_mul_pathELength_lt [T2Space M] [ProperSpace F]
    (φ : PartialDiffeomorph I 𝓘(ℝ, F) M F n) (hn : 1 ≤ n) {x : M} (hx : x ∈ φ.source) {R : ℝ}
    (hR : ball (φ x) R ⊆ φ.target) {C : ℝ≥0}
    (hC : ∀ y ∈ φ.source, φ y ∈ ball (φ x) R → ∀ v : TangentSpace I y,
      ‖mvfderiv I φ y v‖ ≤ C * ‖v‖)
    {γ : ℝ → M} (hγ0 : γ 0 = x) (hγ : CMDiff[Icc 0 1] 1 γ)
    (hlt : C * Manifold.pathELength I γ 0 1 < ENNReal.ofReal R) :
    MapsTo γ (Icc 0 1) (φ.source ∩ φ ⁻¹' ball (φ x) R) := by
  set W := φ.source ∩ φ ⁻¹' ball (φ x) R
  have hW : IsOpen W :=
    φ.contMDiffOn.continuousOn.isOpen_inter_preimage φ.open_source isOpen_ball
  set r := (C * Manifold.pathELength I γ 0 1).toReal
  have hr : C * Manifold.pathELength I γ 0 1 = ENNReal.ofReal r :=
    (ENNReal.ofReal_toReal (hlt.trans ENNReal.ofReal_lt_top).ne).symm
  -- The image `K` under `φ.symm` of the closed ball of radius `r < R` is compact, so closed,
  -- and it lies in `W`.
  have hKball : closedBall (φ x) r ⊆ ball (φ x) R :=
    closedBall_subset_ball (ENNReal.toReal_lt_of_lt_ofReal hlt)
  set K := φ.toPartialEquiv.symm '' closedBall (φ x) r
  have hK : IsClosed K := ((isCompact_closedBall (φ x) r).image_of_continuousOn
    (φ.contMDiffOn_invFun.continuousOn.mono (hKball.trans hR))).isClosed
  have hKW : K ⊆ W := by
    rintro _ ⟨w, hw, rfl⟩
    have hwt := hR (hKball hw)
    exact ⟨φ.map_target hwt, by rw [mem_preimage, φ.right_inv hwt]; exact hKball hw⟩
  -- A path that stays in `W` up to time `t` lies in `K` at time `t`.
  have hstay : ∀ t ∈ Icc (0 : ℝ) 1, (∀ u ∈ Icc 0 t, γ u ∈ W) → γ t ∈ K := by
    intro t ht hγW
    refine ⟨φ (γ t), ?_, φ.left_inv (hγW t ⟨ht.1, le_rfl⟩).1⟩
    rw [mem_closedBall_iff_norm, ← ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg,
      ofReal_norm, ← hr]
    exact enorm_sub_le_mul_pathELength_of_forall_mem φ hn hC hγ0 hγ ht hγW
  -- So the closed set `γ ⁻¹' K` contains `[0, 1]`: if it contains `[0, t]`, then `γ` stays in
  -- the open set `W` a little past `t`, hence in `K`.
  suffices Icc 0 1 ⊆ γ ⁻¹' K from fun t ht ↦ hKW (this ht)
  have hK0 : (0 : ℝ) ∈ γ ⁻¹' K := by
    rw [mem_preimage, hγ0]
    exact ⟨φ x, mem_closedBall_self ENNReal.toReal_nonneg, φ.left_inv hx⟩
  refine IsClosed.Icc_subset_of_forall_mem_nhdsGT_of_Icc_subset ?_ hK0 fun t ht hsub ↦ ?_
  · rw [inter_comm]
    exact hγ.continuousOn.preimage_isClosed_of_isClosed isClosed_Icc hK
  have hIcc : Icc (0 : ℝ) 1 ∈ 𝓝[>] t :=
    Filter.mem_of_superset (Ioo_mem_nhdsGT ht.2) fun u hu ↦ ⟨ht.1.trans hu.1.le, hu.2.le⟩
  have hWt : γ ⁻¹' W ∩ Icc 0 1 ∈ 𝓝[>] t := Filter.inter_mem (nhdsWithin_le_of_mem hIcc
    ((hγ.continuousOn t ⟨ht.1, ht.2.le⟩).preimage_mem_nhdsWithin
      (hW.mem_nhds (hKW (hsub ⟨ht.1, le_rfl⟩))))) hIcc
  obtain ⟨u', hu', hsub'⟩ := (mem_nhdsGT_iff_exists_Ioo_subset' ht.2).1 hWt
  refine Filter.mem_of_superset (Ioo_mem_nhdsGT hu') fun u hu ↦ hstay u (hsub' hu).2 fun v hv ↦ ?_
  rcases le_or_gt v t with hvt | hvt
  · exact hKW (hsub ⟨hv.1, hvt⟩)
  · exact (hsub' ⟨hvt, hv.2.trans_lt hu.2⟩).1

/-- **Chart distances are bounded by the Riemannian distance.** Let `φ` be a `C¹` partial
diffeomorphism from a Hausdorff manifold `M` with a Riemannian metric to a proper real normed
space `F`, and `x` a point of its source. If the ball of radius `R` about `φ x` lies in the
target of `φ`, and the differential of `φ` stretches tangent vectors by at most `C ≠ 0` at the
points of the source whose image lies in that ball, then every `z` in the ball satisfies
`‖z - φ x‖ ≤ C · d(x, φ⁻¹ z)`, for `d` the Riemannian extended distance. -/
theorem ofReal_norm_sub_le_mul_riemannianEDist [T2Space M] [ProperSpace F]
    (φ : PartialDiffeomorph I 𝓘(ℝ, F) M F n) (hn : 1 ≤ n) {x : M} (hx : x ∈ φ.source) {R : ℝ}
    (hR : ball (φ x) R ⊆ φ.target) {C : ℝ≥0} (hC0 : C ≠ 0)
    (hC : ∀ y ∈ φ.source, φ y ∈ ball (φ x) R → ∀ v : TangentSpace I y,
      ‖mvfderiv I φ y v‖ ≤ C * ‖v‖)
    {z : F} (hz : z ∈ ball (φ x) R) :
    ENNReal.ofReal ‖z - φ x‖ ≤ C * Manifold.riemannianEDist I x (φ.symm z) := by
  have hC0' : (C : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.2 hC0
  -- A path shorter than `‖z - φ x‖ / C` would stay in the preimage of the ball, so its endpoint
  -- `φ.symm z` would be at most `C` times its length away from `x` in the chart.
  have key : ENNReal.ofReal ‖z - φ x‖ / C ≤ Manifold.riemannianEDist I x (φ.symm z) := by
    refine TauCeti.Manifold.le_riemannianEDist_of_forall_le_pathELength fun γ hγ0 hγ1 hγ ↦
      ENNReal.div_le_of_le_mul' ?_
    by_contra hlt
    rw [not_le] at hlt
    have hW := φ.mapsTo_of_mul_pathELength_lt hn hx hR hC hγ0 hγ
      (hlt.trans_le (ENNReal.ofReal_le_ofReal (mem_ball_iff_norm.1 hz).le))
    have h1 := enorm_sub_le_mul_pathELength_of_forall_mem φ hn hC hγ0 hγ
      ⟨zero_le_one, le_rfl⟩ fun u hu ↦ hW ⟨hu.1, hu.2⟩
    rw [hγ1, PartialDiffeomorph.symm_toPartialEquiv, φ.right_inv (hR hz), ← ofReal_norm] at h1
    exact hlt.not_ge h1
  calc ENNReal.ofReal ‖z - φ x‖ = C * (ENNReal.ofReal ‖z - φ x‖ / C) :=
        (ENNReal.mul_div_cancel hC0' ENNReal.coe_ne_top).symm
    _ ≤ C * Manifold.riemannianEDist I x (φ.symm z) := by gcongr

/-- **Points outside the chart's ball are far.** Under the hypotheses of
`PartialDiffeomorph.ofReal_norm_sub_le_mul_riemannianEDist`, every point `y` outside
`φ.source ∩ φ ⁻¹' ball (φ x) R` satisfies `R ≤ C · d(x, y)`, `d` the Riemannian distance. -/
theorem ofReal_le_mul_riemannianEDist_of_notMem [T2Space M] [ProperSpace F]
    (φ : PartialDiffeomorph I 𝓘(ℝ, F) M F n) (hn : 1 ≤ n) {x : M} (hx : x ∈ φ.source) {R : ℝ}
    (hR : ball (φ x) R ⊆ φ.target) {C : ℝ≥0} (hC0 : C ≠ 0)
    (hC : ∀ y ∈ φ.source, φ y ∈ ball (φ x) R → ∀ v : TangentSpace I y,
      ‖mvfderiv I φ y v‖ ≤ C * ‖v‖)
    {y : M} (hy : y ∉ φ.source ∩ φ ⁻¹' ball (φ x) R) :
    ENNReal.ofReal R ≤ C * Manifold.riemannianEDist I x y := by
  have hC0' : (C : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.2 hC0
  -- A path from `x` to `y` with `C` times its length less than `R` would end in the ball.
  have key : ENNReal.ofReal R / C ≤ Manifold.riemannianEDist I x y := by
    refine TauCeti.Manifold.le_riemannianEDist_of_forall_le_pathELength fun γ hγ0 hγ1 hγ ↦
      ENNReal.div_le_of_le_mul' (not_lt.1 fun hlt ↦ hy ?_)
    rw [← hγ1]
    exact φ.mapsTo_of_mul_pathELength_lt hn hx hR hC hγ0 hγ hlt ⟨zero_le_one, le_rfl⟩
  calc ENNReal.ofReal R = C * (ENNReal.ofReal R / C) :=
        (ENNReal.mul_div_cancel hC0' ENNReal.coe_ne_top).symm
    _ ≤ C * Manifold.riemannianEDist I x y := by gcongr

end PartialDiffeomorph

end
