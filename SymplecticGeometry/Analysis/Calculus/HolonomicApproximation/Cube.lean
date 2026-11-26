/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Topology.MetricSpace.Thickening
public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Geometry.Manifold.PartitionOfUnity
import SymplecticGeometry.Analysis.Calculus.FDeriv.AddSmulSub
import SymplecticGeometry.Analysis.Calculus.MeanValue
import SymplecticGeometry.Topology.MetricSpace.Thickening

/-!
# Holonomic approximation over a cube: the base of the induction

In the coordinates of `SymplecticGeometry.Analysis.Calculus.HolonomicApproximation.Basic`, on
`D = (Fin m → ℝ) × (Fin k → ℝ)` with sup norms, let `Q = closedBall 0 1 ×ˢ {0}` be the core
cube. The holonomic approximation theorem over `Q` is proved, following
[EliashbergMishachev2002], Chapter 3, by induction on the set `J` of core directions in which the
approximation is asked for, the other core coordinates being parameters. This file proves the
base case `J = ∅`, where only the transverse derivatives are tested.

There the diffeotopy is the identity, and the approximation is the transverse Taylor map
`T (u, v) = f (u, 0) + G (u, 0) (0, v)`, glued to `f` by a cutoff `c (u) κ (v)`: `c` is a smooth
function of the core point, `0` near the closed set `B` and `1` near the points `u` of the cube
with `(u, 0)` outside the open set `U` where `(f, G)` is holonomic, and `κ` is a smooth bump of
the transverse point, `1` on `‖v‖ ≤ ρ`. On `‖v‖ < ρ` the cutoff does not vary in the transverse
directions, so the transverse error of `f + c κ • (T - f)` is a convex combination of those of
`f` and of `T`. The first vanishes on `U`, and the cutoff is `1` where it may not; the second is
at most `‖G (u, 0) - G (u, v)‖`, small for `ρ` small by the uniform Taylor estimate
`IsCompact.exists_pos_norm_taylor_sub_le`.

The cutoff `c` comes from Mathlib's smooth Urysohn lemma
`exists_contMDiffMap_zero_one_nhds_of_isClosed`, and `κ` is a `ContDiffBump`.

## Main results

* `SymplecticGeometry.exists_holonomic_approximation_cube_empty`: holonomic approximation over
  the cube in no core direction, relative to `B`.

## References

* [Y. Eliashberg and N. Mishachev, *Introduction to the h-Principle*][EliashbergMishachev2002]
-/

public section

open Set Metric
open scoped Manifold ContDiff Topology

namespace SymplecticGeometry

variable {m k : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- For the transverse Taylor map `T (u, v) = f (u, 0) + G (u, 0) (0, v)` and a differentiable
function `c` of the core point, the derivative at `x` of `f + (c ∘ Prod.fst) • (T - f)` sends a
vector `w` with `w.1 = 0` to `D f (x) w + c (x.1) • (G (x.1, 0) w - D f (x) w)`: along `w`, the
cutoff does not vary and `T` has derivative `G (x.1, 0)`. -/
private theorem fderiv_add_smul_transverseTaylor_apply {f : (Fin m → ℝ) × (Fin k → ℝ) → F}
    {G : (Fin m → ℝ) × (Fin k → ℝ) → (Fin m → ℝ) × (Fin k → ℝ) →L[ℝ] F}
    {c : (Fin m → ℝ) → ℝ} (hf : Differentiable ℝ f) (hG : Differentiable ℝ G)
    (hc : Differentiable ℝ c) (x w : (Fin m → ℝ) × (Fin k → ℝ)) (hw : w.1 = 0) :
    fderiv ℝ (fun y ↦ f y + c y.1 • ((f (y.1, 0) + G (y.1, 0) (0, y.2)) - f y)) x w =
      fderiv ℝ f x w + c x.1 • (G (x.1, 0) w - fderiv ℝ f x w) := by
  set ι : (Fin m → ℝ) × (Fin k → ℝ) →L[ℝ] (Fin m → ℝ) × (Fin k → ℝ) :=
    (ContinuousLinearMap.inl ℝ _ _).comp (ContinuousLinearMap.fst ℝ _ _)
  set π : (Fin m → ℝ) × (Fin k → ℝ) →L[ℝ] (Fin m → ℝ) × (Fin k → ℝ) :=
    (ContinuousLinearMap.inr ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _)
  have hι : HasFDerivAt (fun y : (Fin m → ℝ) × (Fin k → ℝ) ↦ (y.1, (0 : Fin k → ℝ))) ι x :=
    ι.hasFDerivAt
  have hπ : HasFDerivAt (fun y : (Fin m → ℝ) × (Fin k → ℝ) ↦ ((0 : Fin m → ℝ), y.2)) π x :=
    π.hasFDerivAt
  have hT : HasFDerivAt (fun y ↦ f (y.1, 0) + G (y.1, 0) (0, y.2)) _ x :=
    ((hf _).hasFDerivAt.comp x hι).add (((hG _).hasFDerivAt.comp x hι).clm_apply hπ)
  have hc' : HasFDerivAt (fun y : (Fin m → ℝ) × (Fin k → ℝ) ↦ c y.1) _ x :=
    (hc x.1).hasFDerivAt.comp x (hasFDerivAt_fst (p := x))
  rw [((hf x).hasFDerivAt.add_smul_sub hT hc').fderiv]
  have hιw : ι w = 0 := by simp [ι, hw]
  have hπw : π w = w := by ext <;> simp [π, hw]
  simp only [add_apply, sub_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply, Function.comp_apply, hιw, hπw,
    map_zero, zero_apply, ContinuousLinearMap.coe_fst', hw, zero_smul, add_zero, zero_add]

/-- **Holonomic approximation over the cube in no core direction.** On
`D = (Fin m → ℝ) × (Fin k → ℝ)` with sup norms, let `Q = closedBall 0 1 ×ˢ {0}` be the core
cube, and let `(f, G)` be a smooth formal section that is holonomic (`D f = G`) on an open set
`U` containing `B ×ˢ {0}`, for a closed set `B` of core points. Let `ε, δ > 0`. Then there are a
diffeotopy `h` of `D`, a smooth map `f'` and an open set `V` such that:
* `h` is the identity and `f'` equals `f` off a compact subset of the `δ`-neighbourhood of `Q`;
* `h` moves every point by less than `δ`, keeps every core coordinate (the core coordinates
  outside `∅`), and is the identity at all times near `B ×ˢ {0}`;
* `V` contains the image of `Q` under `h 1`, and on `V` the map `f'` is `ε`-close to `f`, and
  `(D f' - G) w` has norm at most `ε ‖w‖` for every vector `w` whose core part lies in the
  directions `∅`, that is, every vector with zero core part;
* `f'` equals `f` near `B ×ˢ {0}`.

This is the case `J = ∅` of the induction over the core directions; in fact `h` is the identity
diffeotopy. -/
theorem exists_holonomic_approximation_cube_empty {f : (Fin m → ℝ) × (Fin k → ℝ) → F}
    {G : (Fin m → ℝ) × (Fin k → ℝ) → (Fin m → ℝ) × (Fin k → ℝ) →L[ℝ] F}
    (hf : ContDiff ℝ ∞ f) (hG : ContDiff ℝ ∞ G) {B : Set (Fin m → ℝ)} (hB : IsClosed B)
    {U : Set ((Fin m → ℝ) × (Fin k → ℝ))} (hU : IsOpen U) (hBU : B ×ˢ {0} ⊆ U)
    (hUf : ∀ x ∈ U, fderiv ℝ f x = G x) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ (h : TauCeti.Diffeotopy 𝓘(ℝ, (Fin m → ℝ) × (Fin k → ℝ)) ∞ ((Fin m → ℝ) × (Fin k → ℝ)))
      (f' : (Fin m → ℝ) × (Fin k → ℝ) → F) (V : Set ((Fin m → ℝ) × (Fin k → ℝ))),
      (∃ C, IsCompact C ∧ C ⊆ thickening δ (closedBall 0 1 ×ˢ {0}) ∧
        (∀ t, ∀ x ∉ C, h (t, x) = x) ∧ ∀ x ∉ C, f' x = f x) ∧
      (∀ t x, dist (h (t, x)) x < δ) ∧
      (∀ t x, ∀ i ∉ (∅ : Finset (Fin m)), (h (t, x)).1 i = x.1 i) ∧
      (∃ W ∈ 𝓝ˢ (B ×ˢ {0}), ∀ t, ∀ x ∈ W, h (t, x) = x) ∧
      IsOpen V ∧ (fun x ↦ h (1, x)) '' (closedBall 0 1 ×ˢ {0}) ⊆ V ∧ ContDiff ℝ ∞ f' ∧
      (∀ x ∈ V, ‖f' x - f x‖ < ε ∧ ∀ w : (Fin m → ℝ) × (Fin k → ℝ),
        (∀ i ∉ (∅ : Finset (Fin m)), w.1 i = 0) → ‖(fderiv ℝ f' x - G x) w‖ ≤ ε * ‖w‖) ∧
      ∃ U' ∈ 𝓝ˢ (B ×ˢ {0}), EqOn f' f U' := by
  set Q₁ : Set (Fin m → ℝ) := closedBall 0 1
  -- The core points `u` with `(u, 0) ∈ U`: an open set containing `B`.
  set A : Set (Fin m → ℝ) := (fun u ↦ (u, (0 : Fin k → ℝ))) ⁻¹' U
  have hA : IsOpen A := hU.preimage (continuous_id.prodMk continuous_const)
  have hBA : B ⊆ A := fun u hu ↦ hBU ⟨hu, rfl⟩
  -- The cutoff `c` of the core point: `0` near `B` and off the `δ / 2`-neighbourhood of the cube,
  -- `1` near the points of the cube outside `A`.
  obtain ⟨c', hc0, hc1, hcI⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed
    𝓘(ℝ, Fin m → ℝ) (n := (⊤ : ℕ∞))
    (hB.union (isOpen_thickening (δ := δ / 2) (E := Q₁)).isClosed_compl)
    (isClosed_closedBall.sdiff hA) (s := B ∪ (thickening (δ / 2) Q₁)ᶜ) (t := Q₁ \ A)
    (disjoint_left.2 fun u hu hu' ↦ hu.elim (fun huB ↦ hu'.2 (hBA huB))
      fun hu₂ ↦ hu₂ (self_subset_thickening (by positivity) _ hu'.1))
  set c : (Fin m → ℝ) → ℝ := ⇑c'
  have hc : ContDiff ℝ ∞ c := contMDiff_iff_contDiff.1 c'.contMDiff
  obtain ⟨O₀, hO₀, hBO₀, hO₀c⟩ := eventually_nhdsSet_iff_exists.1 hc0
  obtain ⟨O₁, hO₁, hQO₁, hO₁c⟩ := eventually_nhdsSet_iff_exists.1 hc1
  -- The uniform Taylor estimate over the compact set `closedBall 0 2 ×ˢ {0}`.
  have hK : IsCompact (closedBall (0 : Fin m → ℝ) 2 ×ˢ {(0 : Fin k → ℝ)}) :=
    (isCompact_closedBall _ _).prod isCompact_singleton
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn
    ((hf.continuous_fderiv (by simp)).sub hG.continuous).continuousOn
  obtain ⟨ρ₀, hρ₀, hT⟩ := hK.exists_pos_norm_taylor_sub_le (fun a _ ↦ hf.contDiffAt.of_le (by simp))
    (fun a _ ↦ hG.continuous.continuousAt) (half_pos hε)
  have hM₀ : 0 ≤ M := (norm_nonneg _).trans (hM (0, 0) ⟨mem_closedBall_self zero_le_two, rfl⟩)
  set ρ := min (min ρ₀ (δ / 4)) (ε / (2 * (M + ε / 2 + 1)))
  have hρ : 0 < ρ := lt_min (lt_min hρ₀ (by positivity)) (by positivity)
  have hρρ₀ : ρ ≤ ρ₀ := (min_le_left _ _).trans (min_le_left _ _)
  have hρδ : ρ ≤ δ / 4 := (min_le_left _ _).trans (min_le_right _ _)
  have hρε : (M + ε / 2) * ρ < ε := by
    calc (M + ε / 2) * ρ ≤ (M + ε / 2) * (ε / (2 * (M + ε / 2 + 1))) := by
          gcongr; exact min_le_right _ _
      _ < (M + ε / 2 + 1) * (ε / (M + ε / 2 + 1)) := by
          rw [mul_div_assoc', mul_div_assoc', div_lt_div_iff₀ (by positivity) (by positivity)]
          nlinarith [mul_pos hε (show 0 < M + ε / 2 + 1 by positivity)]
      _ = ε := mul_div_cancel₀ _ (by positivity)
  -- On the points `(u, v)` with `‖u‖ < 2` and `‖v‖ < ρ`, the transverse Taylor map is close to `f`
  -- and `G (u, 0)` is close to `G (u, v)`.
  have hTx : ∀ x : (Fin m → ℝ) × (Fin k → ℝ), ‖x.1‖ < 2 → ‖x.2‖ < ρ →
      ‖(f (x.1, 0) + G (x.1, 0) (0, x.2)) - f x‖ < ε ∧ ‖G (x.1, 0) - G x‖ ≤ ε / 2 := by
    intro x hx₁ hx₂
    have ha : (x.1, (0 : Fin k → ℝ)) ∈ closedBall (0 : Fin m → ℝ) 2 ×ˢ {(0 : Fin k → ℝ)} :=
      ⟨mem_closedBall_zero_iff.2 hx₁.le, rfl⟩
    have hxa : x - (x.1, 0) = (0, x.2) := by ext <;> simp
    have hxa' : ‖x - (x.1, 0)‖ = ‖x.2‖ := by rw [hxa, Prod.norm_def]; simp
    obtain ⟨h₁, h₂, -⟩ := hT _ ha x (by rw [hxa']; exact hx₂.trans_le hρρ₀)
    rw [hxa, show ‖((0 : Fin m → ℝ), x.2)‖ = ‖x.2‖ by simp [Prod.norm_def]] at h₁
    rw [fderiv_taylor] at h₂
    refine ⟨h₁.trans_lt ?_, h₂⟩
    calc (‖fderiv ℝ f (x.1, 0) - G (x.1, 0)‖ + ε / 2) * ‖x.2‖ ≤ (M + ε / 2) * ρ := by
          gcongr; exact hM _ ha
      _ < ε := hρε
  -- The transverse bump `κ`: `1` for `‖v‖ ≤ ρ` and `0` for `‖v‖ ≥ 2 ρ`.
  let κ : ContDiffBump (0 : Fin k → ℝ) := ⟨ρ, 2 * ρ, hρ, by linarith⟩
  set T : (Fin m → ℝ) × (Fin k → ℝ) → F := fun x ↦ f (x.1, 0) + G (x.1, 0) (0, x.2)
  set f' : (Fin m → ℝ) × (Fin k → ℝ) → F := fun x ↦ f x + (c x.1 * κ x.2) • (T x - f x)
  have hcκI : ∀ x : (Fin m → ℝ) × (Fin k → ℝ), 0 ≤ c x.1 * κ x.2 ∧ c x.1 * κ x.2 ≤ 1 :=
    fun x ↦ ⟨mul_nonneg (hcI _).1 κ.nonneg,
      (mul_le_of_le_one_left κ.nonneg (hcI _).2).trans κ.le_one⟩
  -- Near a point with `‖v‖ < ρ`, the bump is `1`.
  have hf'eq : ∀ x : (Fin m → ℝ) × (Fin k → ℝ), ‖x.2‖ < ρ →
      f' =ᶠ[𝓝 x] fun y ↦ f y + c y.1 • (T y - f y) := by
    intro x hx
    filter_upwards [(isOpen_ball.preimage continuous_snd).mem_nhds
      (mem_ball_zero_iff.2 hx : x.2 ∈ ball (0 : Fin k → ℝ) ρ)] with y hy
    rw [mem_preimage] at hy
    simp only [f', κ.one_of_mem_closedBall (ball_subset_closedBall hy), mul_one]
  set Q : Set ((Fin m → ℝ) × (Fin k → ℝ)) := Q₁ ×ˢ {0} with hQ
  set C : Set ((Fin m → ℝ) × (Fin k → ℝ)) := cthickening (δ / 2) Q₁ ×ˢ closedBall 0 (2 * ρ)
  set V : Set ((Fin m → ℝ) × (Fin k → ℝ)) :=
    (U ∪ O₁ ×ˢ univ) ∩ (ball 0 2 ×ˢ ball 0 ρ)
  have hf' : ContDiff ℝ ∞ f' := by
    have hι : ContDiff ℝ ∞ fun x : (Fin m → ℝ) × (Fin k → ℝ) ↦ (x.1, (0 : Fin k → ℝ)) :=
      contDiff_fst.prodMk contDiff_const
    exact hf.add (((hc.comp contDiff_fst).mul (κ.contDiff.comp contDiff_snd)).smul
      (((hf.comp hι).add ((hG.comp hι).clm_apply (contDiff_const.prodMk contDiff_snd))).sub hf))
  refine ⟨TauCeti.Diffeotopy.refl _ _ _, f', V, ⟨C, ?_, ?_, fun t x _ ↦ by simp, fun x hx ↦ ?_⟩,
    fun t x ↦ by simpa using hδ, fun t x i _ ↦ by simp, ⟨univ, Filter.univ_mem, by simp⟩,
    (hU.union (hO₁.prod isOpen_univ)).inter (isOpen_ball.prod isOpen_ball), ?_, hf',
    fun x hx ↦ ?_, ⟨Prod.fst ⁻¹' O₀, (hO₀.preimage continuous_fst).mem_nhdsSet.2
      fun x hx ↦ hBO₀ (Or.inl hx.1), fun x hx ↦ by simp [f', hO₀c _ hx]⟩⟩
  · exact (isCompact_closedBall _ _).cthickening.prod (isCompact_closedBall _ _)
  · rw [hQ, thickening_prod, thickening_singleton]
    exact prod_mono (cthickening_subset_thickening' hδ (by linarith) _)
      (closedBall_subset_ball (by linarith))
  · -- Off `C`, either `c` or `κ` vanishes.
    by_cases hx₁ : x.1 ∈ cthickening (δ / 2) Q₁
    · have hx₂ : x.2 ∉ closedBall 0 (2 * ρ) := fun h ↦ hx ⟨hx₁, h⟩
      rw [mem_closedBall, not_le] at hx₂
      simp [f', κ.zero_of_le_dist hx₂.le]
    · have : c x.1 = 0 :=
        hO₀c _ (hBO₀ <| Or.inr fun h ↦ hx₁ (thickening_subset_cthickening _ _ h))
      simp [f', this]
  · simp only [TauCeti.Diffeotopy.refl_apply, image_id']
    rintro x ⟨hx₁, hx₂⟩
    rw [mem_singleton_iff] at hx₂
    refine ⟨?_, ?_, ?_⟩
    · by_cases hxA : x.1 ∈ A
      · left
        have : (x.1, (0 : Fin k → ℝ)) = x := Prod.ext rfl hx₂.symm
        rw [← this]
        exact hxA
      · exact Or.inr ⟨hQO₁ ⟨hx₁, hxA⟩, trivial⟩
    · simpa using (mem_closedBall_zero_iff.1 hx₁).trans_lt one_lt_two
    · simpa [hx₂] using hρ
  · obtain ⟨hxU, hx₁, hx₂⟩ := hx
    rw [mem_ball_zero_iff] at hx₁ hx₂
    obtain ⟨hTf, hGx⟩ := hTx x hx₁ hx₂
    refine ⟨?_, fun w hw ↦ ?_⟩
    · simp only [f', add_sub_cancel_left, norm_smul, Real.norm_of_nonneg (hcκI x).1]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hcκI x).2).trans_lt hTf
    have hw₁ : w.1 = 0 := funext fun i ↦ hw i (Finset.notMem_empty i)
    rw [(hf'eq x hx₂).fderiv_eq, sub_apply,
      fderiv_add_smul_transverseTaylor_apply (hf.differentiable (by simp))
        (hG.differentiable (by simp)) (hc.differentiable (by simp)) x w hw₁]
    have hGw : ‖G (x.1, 0) w - G x w‖ ≤ ε * ‖w‖ := by
      rw [← sub_apply]
      exact ((G (x.1, 0) - G x).le_opNorm w).trans (by gcongr; linarith)
    rcases hxU with hxU | hxO₁
    · rw [hUf x hxU, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg (hcI _).1]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hcI _).2).trans hGw
    · rw [hO₁c _ hxO₁.1, one_smul, add_sub_cancel]
      exact hGw

end SymplecticGeometry

end
