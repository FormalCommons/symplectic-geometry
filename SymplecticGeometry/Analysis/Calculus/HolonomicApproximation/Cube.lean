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
import SymplecticGeometry.Analysis.Calculus.HolonomicApproximation.Direction
import SymplecticGeometry.Analysis.Calculus.HolonomicApproximation.Transport
import SymplecticGeometry.Analysis.Calculus.MeanValue
import SymplecticGeometry.Analysis.Normed.Operator.Pi
import SymplecticGeometry.Geometry.Diffeomorphism.Diffeotopy.Support
import SymplecticGeometry.Geometry.Manifold.Diffeomorph.CompactSupport
import SymplecticGeometry.Geometry.Manifold.Diffeomorph.FDeriv
import SymplecticGeometry.Topology.MetricSpace.Thickening

/-!
# Holonomic approximation over a cube

In the coordinates of `SymplecticGeometry.Analysis.Calculus.HolonomicApproximation.Basic`, on
`D = (Fin m → ℝ) × (Fin k → ℝ)` with sup norms, let `Q = closedBall 0 1 ×ˢ {0}` be the core
cube. The holonomic approximation theorem over `Q` is proved, following
[EliashbergMishachev2002], Chapter 3, by induction on the set `J` of core directions in which the
approximation is asked for, the other core coordinates being parameters. This file proves the
base case `J = ∅`, where only the transverse derivatives are tested, the step from `J'` to
`insert i₀ J'`, the statement for every `J` by induction on `J`, and its case
`J = Finset.univ` relative to the boundary sphere of the cube.

In the base case `J = ∅`, the diffeotopy is the identity, and the approximation is the
transverse Taylor map `T (u, v) = f (u, 0) + G (u, 0) (0, v)`, glued to `f` by a cutoff
`c (u) κ (v)`: `c` is a smooth function of the core point, `0` near the closed set `B` and `1`
near the points `u` of the cube with `(u, 0)` outside the open set `U` where `(f, G)` is
holonomic, and `κ` is a smooth bump of the transverse point, `1` on `‖v‖ ≤ ρ`. On `‖v‖ < ρ` the
cutoff does not vary in the transverse directions, so the transverse error of `f + c κ • (T - f)`
is a convex combination of those of `f` and of `T`. The first vanishes on `U`, and the cutoff is
`1` where it may not; the second is at most `‖G (u, 0) - G (u, v)‖`, small for `ρ` small by the
uniform Taylor estimate `IsCompact.exists_pos_norm_taylor_sub_le`.

The cutoff `c` comes from Mathlib's smooth Urysohn lemma
`exists_contMDiffMap_zero_one_nhds_of_isClosed`, and `κ` is a `ContDiffBump`.

For the step, the statement for `J'` gives a diffeotopy `h₁` with final map `Φ`, keeping the
core coordinates outside `J'`, and an approximation `f₁`. The datum
`G₁ = fderiv ℝ f₁ ∘L P + G ∘L (1 - P)`, for the projection `P` onto the vectors in the directions
`J'`, is holonomic in those directions everywhere and close to `G` where `f₁` approximates. Its
pullback along `Φ` is holonomic in the directions `J'` on the straight cube `Q`, so the
one-direction lemma `exists_holonomic_approximation_direction` applies to it, and gives a
diffeotopy `h₂` and an approximation `f₂'`. The result is the diffeotopy
`h₂.transDiffeomorph Φ * h₁` with the map `f₂' ∘ Φ.symm`; the errors are transported back by
the lemmas of `SymplecticGeometry.Analysis.Calculus.HolonomicApproximation.Transport`, with the
bounds on `Φ` of `Diffeomorph.exists_lipschitzWith_and_norm_fderiv_symm_le`.

## Main results

* `SymplecticGeometry.exists_holonomic_approximation_cube_empty`: holonomic approximation over
  the cube in no core direction, relative to `B`.
* `SymplecticGeometry.exists_holonomic_approximation_cube_directions_insert`: holonomic
  approximation in the directions `insert i₀ J'` from holonomic approximation in the
  directions `J'`.
* `SymplecticGeometry.exists_holonomic_approximation_cube_directions`: holonomic approximation
  over the cube in the core directions `J`, relative to a closed set `B` that contains the faces
  of the cube in the directions `J`.
* `SymplecticGeometry.exists_holonomic_approximation_cube`: holonomic approximation over the
  cube, relative to its boundary.

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

/-! ### The step from the directions `J'` to `insert i₀ J'` -/

/-- **The datum of the directions `J`.** Given smooth maps `f₁ : D → F` and `G : D → D →L[ℝ] F`,
there is a smooth `G₁`, namely `G₁ x := fderiv ℝ f₁ x ∘L P + G x ∘L (1 - P)` for the
projection `P` of `D` onto the vectors in the directions `J`, that agrees with `fderiv ℝ f₁` on
the vectors in the directions `J`, equals `G` wherever `fderiv ℝ f₁ = G`, and differs from `G`
on a vector `w` by `fderiv ℝ f₁ - G` on a vector in the directions `J` of norm at most `‖w‖`. -/
private theorem exists_datum_directions {f₁ : (Fin m → ℝ) × (Fin k → ℝ) → F}
    {G : (Fin m → ℝ) × (Fin k → ℝ) → (Fin m → ℝ) × (Fin k → ℝ) →L[ℝ] F}
    (hf₁ : ContDiff ℝ ∞ f₁) (hG : ContDiff ℝ ∞ G) (J : Finset (Fin m)) :
    ∃ G₁ : (Fin m → ℝ) × (Fin k → ℝ) → (Fin m → ℝ) × (Fin k → ℝ) →L[ℝ] F, ContDiff ℝ ∞ G₁ ∧
      (∀ x w, (∀ i ∉ J, w.1 i = 0) → fderiv ℝ f₁ x w = G₁ x w) ∧
      (∀ x, fderiv ℝ f₁ x = G x → G₁ x = G x) ∧
      ∀ x w, ∃ v : (Fin m → ℝ) × (Fin k → ℝ), (∀ i ∉ J, v.1 i = 0) ∧ ‖v‖ ≤ ‖w‖ ∧
        (G₁ x - G x) w = (fderiv ℝ f₁ x - G x) v := by
  set P : ((Fin m → ℝ) × (Fin k → ℝ)) →L[ℝ] (Fin m → ℝ) × (Fin k → ℝ) :=
    (ContinuousLinearMap.coordProj J).prodMap (ContinuousLinearMap.id ℝ _)
  refine ⟨fun x ↦ (fderiv ℝ f₁ x).comp P + (G x).comp (ContinuousLinearMap.id ℝ _ - P),
    ((hf₁.fderiv_right (by simp)).clm_comp contDiff_const).add (hG.clm_comp contDiff_const),
    fun x w hw ↦ ?_, fun x hx ↦ ?_, fun x w ↦ ⟨P w, fun i hi ↦ ?_,
      max_le_max (ContinuousLinearMap.norm_coordProj_apply_le J w.1) le_rfl, ?_⟩⟩
  · have hPw : P w = w := Prod.ext (ContinuousLinearMap.coordProj_apply_eq_self hw) rfl
    simp [hPw]
  · refine ContinuousLinearMap.ext fun w ↦ ?_
    simp [hx]
  · simp [P, hi]
  · simp only [sub_apply, add_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, map_sub]
    abel

/-- **The assembly estimate.** Let `Φ` be a diffeomorphism of `D` keeping the core coordinates
outside `J' ⊆ J`, with `‖fderiv ℝ Φ.symm (Φ z)‖ ≤ L`. Suppose that at `Φ z` the map `f₁` is
`ε₁`-close to `f` and its error against `G` is at most `ε₁` on the vectors in the directions `J'`,
that `G₁ - G` at `Φ z` is that error on a vector of no larger norm in the directions `J'`, and
that at `z` the map `f₂'` is `ε₂`-close to `f₁ ∘ Φ`, with error at most `ε₂` against the
pulled-back `G₁ (Φ z) ∘L fderiv ℝ Φ z` on the vectors in the directions `J`. Then at `Φ z` the
map `f₂' ∘ Φ.symm` is `(ε₂ + ε₁)`-close to `f`, and its error against `G` is at most
`ε₂ * L + ε₁` on the vectors in the directions `J`. -/
private theorem norm_comp_diffeomorph_symm_sub_lt_and_le
    {Φ : ((Fin m → ℝ) × (Fin k → ℝ)) ≃ₘ^∞⟮𝓘(ℝ, (Fin m → ℝ) × (Fin k → ℝ)),
      𝓘(ℝ, (Fin m → ℝ) × (Fin k → ℝ))⟯ ((Fin m → ℝ) × (Fin k → ℝ))}
    {J J' : Finset (Fin m)} (hΦ : ∀ x, ∀ i ∉ J', (Φ x).1 i = x.1 i) (hJ : J' ⊆ J)
    {f f₁ f₂' : (Fin m → ℝ) × (Fin k → ℝ) → F}
    {G G₁ : (Fin m → ℝ) × (Fin k → ℝ) → (Fin m → ℝ) × (Fin k → ℝ) →L[ℝ] F}
    {z : (Fin m → ℝ) × (Fin k → ℝ)} (hf₂' : DifferentiableAt ℝ f₂' z) {ε₁ ε₂ L : ℝ}
    (hε₂ : 0 ≤ ε₂) (hL : ‖fderiv ℝ Φ.symm (Φ z)‖ ≤ L)
    (hG₁ : ∀ w, ∃ v : (Fin m → ℝ) × (Fin k → ℝ), (∀ i ∉ J', v.1 i = 0) ∧ ‖v‖ ≤ ‖w‖ ∧
      (G₁ (Φ z) - G (Φ z)) w = (fderiv ℝ f₁ (Φ z) - G (Φ z)) v)
    (h₁ : ‖f₁ (Φ z) - f (Φ z)‖ < ε₁ ∧ ∀ w : (Fin m → ℝ) × (Fin k → ℝ),
      (∀ i ∉ J', w.1 i = 0) → ‖(fderiv ℝ f₁ (Φ z) - G (Φ z)) w‖ ≤ ε₁ * ‖w‖)
    (h₂ : ‖f₂' z - f₁ (Φ z)‖ < ε₂ ∧ ∀ w : (Fin m → ℝ) × (Fin k → ℝ),
      (∀ i ∉ J, w.1 i = 0) → ‖(fderiv ℝ f₂' z - (G₁ (Φ z)).comp (fderiv ℝ Φ z)) w‖ ≤ ε₂ * ‖w‖) :
    ‖(f₂' ∘ Φ.symm) (Φ z) - f (Φ z)‖ < ε₂ + ε₁ ∧ ∀ w : (Fin m → ℝ) × (Fin k → ℝ),
      (∀ i ∉ J, w.1 i = 0) → ‖(fderiv ℝ (f₂' ∘ Φ.symm) (Φ z) - G (Φ z)) w‖ ≤
        (ε₂ * L + ε₁) * ‖w‖ := by
  refine ⟨?_, fun w hw ↦ ?_⟩
  · rw [Function.comp_apply, Φ.symm_apply_apply,
      show f₂' z - f (Φ z) = (f₂' z - f₁ (Φ z)) + (f₁ (Φ z) - f (Φ z)) by abel]
    exact (norm_add_le _ _).trans_lt (add_lt_add h₂.1 h₁.1)
  obtain ⟨v, hv, hvw, hve⟩ := hG₁ w
  rw [show fderiv ℝ (f₂' ∘ Φ.symm) (Φ z) - G (Φ z) =
      (fderiv ℝ (f₂' ∘ Φ.symm) (Φ z) - G₁ (Φ z)) + (G₁ (Φ z) - G (Φ z)) by abel,
    add_apply, hve, add_mul]
  exact (norm_add_le _ _).trans (add_le_add
    (norm_fderiv_comp_diffeomorph_symm_sub_apply_le hΦ hJ hf₂' hε₂ h₂.2 hL hw)
    ((h₁.2 v hv).trans (mul_le_mul_of_nonneg_left hvw ((norm_nonneg _).trans h₁.1.le))))

/-- **The step of the induction over the core directions.** In the coordinates
`D = (Fin m → ℝ) × (Fin k → ℝ)` with sup norms and the core cube `Q = closedBall 0 1 ×ˢ {0}`,
let `(f, G)` be a formal section with `G` smooth, holonomic on an open set `U` containing
`B ×ˢ {0}`, for a closed set `B` of core points containing the faces of the cube in the
directions `insert i₀ J'`. If, for every `ε, δ > 0`, the conclusion of the inductive statement
holds for `(f, G)` in the directions `J'` (`ih`), then it holds for `(f, G)` in the directions
`insert i₀ J'`: there are a diffeotopy `h` of `D`, a smooth map `f'` and an open set `V` such
that
* `h` is the identity and `f'` equals `f` off a compact subset of the `δ`-neighbourhood of `Q`;
* `h` moves every point by less than `δ`, keeps the core coordinates outside `insert i₀ J'`,
  and is the identity at all times near `B ×ˢ {0}`;
* `V` contains the image of `Q` under `h 1`, and on `V` the map `f'` is `ε`-close to `f`, and
  `(D f' - G) w` has norm at most `ε ‖w‖` for every vector `w` in the directions `insert i₀ J'`;
* `f'` equals `f` near `B ×ˢ {0}`.

The diffeotopy runs the one for the directions `J'`, with final map `Φ`, and then the one of
`exists_holonomic_approximation_direction` for the section pulled back along `Φ`, conjugated by
`Φ`. -/
theorem exists_holonomic_approximation_cube_directions_insert (hk : 0 < k) (i₀ : Fin m)
    {J' : Finset (Fin m)} {f : (Fin m → ℝ) × (Fin k → ℝ) → F}
    {G : (Fin m → ℝ) × (Fin k → ℝ) → (Fin m → ℝ) × (Fin k → ℝ) →L[ℝ] F}
    (hG : ContDiff ℝ ∞ G) {B : Set (Fin m → ℝ)} (hB : IsClosed B)
    (hJB : ∀ u ∈ closedBall (0 : Fin m → ℝ) 1, (∃ i ∈ insert i₀ J', |u i| = 1) → u ∈ B)
    {U : Set ((Fin m → ℝ) × (Fin k → ℝ))} (hU : IsOpen U) (hBU : B ×ˢ {0} ⊆ U)
    (hUf : ∀ x ∈ U, fderiv ℝ f x = G x)
    (ih : ∀ ε δ : ℝ, 0 < ε → 0 < δ →
      ∃ (h : TauCeti.Diffeotopy 𝓘(ℝ, (Fin m → ℝ) × (Fin k → ℝ)) ∞ ((Fin m → ℝ) × (Fin k → ℝ)))
        (f' : (Fin m → ℝ) × (Fin k → ℝ) → F) (V : Set ((Fin m → ℝ) × (Fin k → ℝ))),
        (∃ C, IsCompact C ∧ C ⊆ thickening δ (closedBall 0 1 ×ˢ {0}) ∧
          (∀ t, ∀ x ∉ C, h (t, x) = x) ∧ ∀ x ∉ C, f' x = f x) ∧
        (∀ t x, dist (h (t, x)) x < δ) ∧
        (∀ t x, ∀ i ∉ J', (h (t, x)).1 i = x.1 i) ∧
        (∃ W ∈ 𝓝ˢ (B ×ˢ {0}), ∀ t, ∀ x ∈ W, h (t, x) = x) ∧
        IsOpen V ∧ (fun x ↦ h (1, x)) '' (closedBall 0 1 ×ˢ {0}) ⊆ V ∧ ContDiff ℝ ∞ f' ∧
        (∀ x ∈ V, ‖f' x - f x‖ < ε ∧ ∀ w : (Fin m → ℝ) × (Fin k → ℝ),
          (∀ i ∉ J', w.1 i = 0) → ‖(fderiv ℝ f' x - G x) w‖ ≤ ε * ‖w‖) ∧
        ∃ U' ∈ 𝓝ˢ (B ×ˢ {0}), EqOn f' f U')
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ (h : TauCeti.Diffeotopy 𝓘(ℝ, (Fin m → ℝ) × (Fin k → ℝ)) ∞ ((Fin m → ℝ) × (Fin k → ℝ)))
      (f' : (Fin m → ℝ) × (Fin k → ℝ) → F) (V : Set ((Fin m → ℝ) × (Fin k → ℝ))),
      (∃ C, IsCompact C ∧ C ⊆ thickening δ (closedBall 0 1 ×ˢ {0}) ∧
        (∀ t, ∀ x ∉ C, h (t, x) = x) ∧ ∀ x ∉ C, f' x = f x) ∧
      (∀ t x, dist (h (t, x)) x < δ) ∧
      (∀ t x, ∀ i ∉ insert i₀ J', (h (t, x)).1 i = x.1 i) ∧
      (∃ W ∈ 𝓝ˢ (B ×ˢ {0}), ∀ t, ∀ x ∈ W, h (t, x) = x) ∧
      IsOpen V ∧ (fun x ↦ h (1, x)) '' (closedBall 0 1 ×ˢ {0}) ⊆ V ∧ ContDiff ℝ ∞ f' ∧
      (∀ x ∈ V, ‖f' x - f x‖ < ε ∧ ∀ w : (Fin m → ℝ) × (Fin k → ℝ),
        (∀ i ∉ insert i₀ J', w.1 i = 0) → ‖(fderiv ℝ f' x - G x) w‖ ≤ ε * ‖w‖) ∧
      ∃ U' ∈ 𝓝ˢ (B ×ˢ {0}), EqOn f' f U' := by
  set Q : Set ((Fin m → ℝ) × (Fin k → ℝ)) := closedBall 0 1 ×ˢ {0}
  have hQ : IsCompact Q := (isCompact_closedBall _ _).prod isCompact_singleton
  -- Step 2a: the approximation in the directions `J'`, with final map `Φ`.
  obtain ⟨h₁, f₁, V₁, ⟨C₁, hC₁, hC₁δ, hh₁C₁, hf₁C₁⟩, hh₁δ, hh₁J', ⟨W₁, hW₁, hh₁W₁⟩, hV₁, hQV₁,
    hf₁, hf₁V₁, U₁, hU₁, hf₁U₁⟩ := ih (ε / 2) (δ / 2) (half_pos hε) (half_pos hδ)
  set Φ := h₁.final
  have hΦ : ∀ x, Φ x = h₁ (1, x) := h₁.final_apply
  have hΦJ' : ∀ x, ∀ i ∉ J', (Φ x).1 i = x.1 i := fun x i hi ↦ by rw [hΦ, hh₁J' 1 x i hi]
  obtain ⟨L, hL1, hΦL, hΦsL⟩ := Φ.exists_lipschitzWith_and_norm_fderiv_symm_le (by simp) hC₁
    fun x hx ↦ by rw [hΦ, hh₁C₁ 1 x hx]
  have hL0 : (0 : ℝ) < L := by exact_mod_cast zero_lt_one.trans_le hL1
  obtain ⟨G₁, hG₁, hf₁G₁, hG₁G, hG₁sub⟩ := exists_datum_directions hf₁ hG J'
  -- Step 2b: the datum pulled back along `Φ`, holonomic near `B ×ˢ {0}`.
  set f₂ := f₁ ∘ Φ
  set G₂ := fun x ↦ (G₁ (Φ x)).comp (fderiv ℝ Φ x)
  set U₂ := interior W₁ ∩ interior U₁ ∩ U
  have hBU₂ : B ×ˢ {0} ⊆ U₂ := fun x hx ↦ ⟨⟨subset_interior_iff_mem_nhdsSet.2 hW₁ hx,
    subset_interior_iff_mem_nhdsSet.2 hU₁ hx⟩, hBU hx⟩
  have hU₂f : ∀ x ∈ U₂, fderiv ℝ f₂ x = G₂ x := by
    intro x hx
    have hΦx : (Φ : _ → _) =ᶠ[𝓝 x] id := by
      filter_upwards [isOpen_interior.mem_nhds hx.1.1] with y hy
      rw [hΦ, hh₁W₁ 1 y (interior_subset hy), id]
    have hf₁x : f₁ =ᶠ[𝓝 x] f := by
      filter_upwards [isOpen_interior.mem_nhds hx.1.2] with y hy
      exact hf₁U₁ (interior_subset hy)
    have hf₂x : f₂ =ᶠ[𝓝 x] f := by
      filter_upwards [hΦx, hf₁x] with y h₁y h₂y
      simp only [f₂, Function.comp_apply, h₁y, id, h₂y]
    simp only [G₂, hΦx.eq_of_nhds, hΦx.fderiv_eq, fderiv_id, id, ContinuousLinearMap.comp_id]
    rw [hf₂x.fderiv_eq, hUf x hx.2, hG₁G x (by rw [hf₁x.fderiv_eq, hUf x hx.2])]
  -- Step 2c: the direction `i₀`, for the pulled-back datum.
  obtain ⟨δ₀, hδ₀, hδ₀V₁⟩ := hQ.exists_thickening_subset_open (hV₁.preimage Φ.continuous)
    fun x hx ↦ by rw [mem_preimage, hΦ]; exact hQV₁ ⟨x, hx, rfl⟩
  set δ₂ := min δ₀ (δ / (2 * L))
  have hδ₂ : 0 < δ₂ := lt_min hδ₀ (div_pos hδ (mul_pos two_pos hL0))
  have hLδ₂ : L * δ₂ ≤ δ / 2 := by
    calc (L : ℝ) * δ₂ ≤ L * (δ / (2 * L)) := by gcongr; exact min_le_right _ _
      _ = δ / 2 := by field_simp
  have hδ₂δ : δ₂ ≤ δ / 2 :=
    (le_mul_of_one_le_left hδ₂.le (by exact_mod_cast hL1)).trans hLδ₂
  have hε₂ : 0 < ε / (2 * L) := div_pos hε (mul_pos two_pos hL0)
  obtain ⟨h₂, f₂', V₂, ⟨C₂, hC₂, hC₂δ, hh₂C₂, hf₂'C₂⟩, hh₂δ, hh₂fst, hW₂, hV₂, hQV₂, hf₂',
    hf₂'V₂, U₂', hU₂', hf₂'U₂'⟩ := exists_holonomic_approximation_direction hk i₀
      (hf₁.comp Φ.contDiff) (Φ.contDiff_clm_comp_fderiv hG₁ (by simp))
      (fun u _ v hv ↦ fderiv_comp_diffeomorph_apply_eq hΦJ' subset_rfl
        (hf₁.differentiable (by simp) _) (fun w hw ↦ hf₁G₁ _ w hw) hv)
      hB hJB ((isOpen_interior.inter isOpen_interior).inter hU) hBU₂ hU₂f hε₂ hδ₂
  -- Step 2d: the assembly.
  refine ⟨h₂.transDiffeomorph Φ * h₁, f₂' ∘ Φ.symm, Φ '' V₂ ∩ V₁,
    ⟨C₁ ∪ Φ '' C₂, hC₁.union (hC₂.image Φ.continuous), union_subset
      (hC₁δ.trans (thickening_mono (by linarith) _)) ?_,
      TauCeti.Diffeotopy.transDiffeomorph_mul_apply_eq_self_of_notMem_union_image Φ hh₁C₁ hh₂C₂,
      fun x hx ↦ ?_⟩,
    fun t x ↦ (TauCeti.Diffeotopy.dist_transDiffeomorph_mul_apply_lt hΦL hh₁δ hh₂δ t x).trans_le
      (by linarith),
    fun t x i hi ↦ transDiffeomorph_final_mul_apply_fst_apply
      (fun t x i hi ↦ hh₁J' t x i fun h ↦ hi (Finset.mem_insert_of_mem h))
      (fun t x i _ ↦ by rw [hh₂fst]) t x hi,
    TauCeti.Diffeotopy.exists_mem_nhdsSet_transDiffeomorph_final_mul_apply_eq_self
      ⟨W₁, hW₁, hh₁W₁⟩ hW₂,
    (Φ.toHomeomorph.isOpen_image.2 hV₂).inter hV₁, fun y hy ↦ ⟨?_, ?_⟩,
    hf₂'.comp Φ.symm.contDiff, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨z, hz, hxz⟩ := mem_thickening_iff.1 (hC₂δ hx)
    refine mem_thickening_iff.2 ⟨z, hz, (dist_triangle _ x _).trans_lt ?_⟩
    have := hh₁δ 1 x
    rw [← hΦ] at this
    linarith
  · have hx₂ : Φ.symm x ∉ C₂ := fun h ↦ hx (Or.inr ⟨_, h, Φ.apply_symm_apply x⟩)
    simp only [Function.comp_apply, hf₂'C₂ _ hx₂, Φ.apply_symm_apply]
    exact hf₁C₁ x fun h ↦ hx (Or.inl h)
  · exact TauCeti.Diffeotopy.image_transDiffeomorph_final_mul_apply_one_subset hQV₂ hy
  · obtain ⟨x, hx, rfl⟩ := hy
    have e := DFunLike.congr_fun (TauCeti.Diffeotopy.final_transDiffeomorph_final_mul h₁ h₂) x
    rw [TauCeti.Diffeotopy.final_apply, Diffeomorph.mul_apply,
      TauCeti.Diffeotopy.final_apply h₂] at e
    rw [e]
    exact hδ₀V₁ (thickening_mono (min_le_left _ _) _ (mem_thickening_iff.2 ⟨x, hx, hh₂δ 1 x⟩))
  · rintro _ ⟨⟨z, hz, rfl⟩, hy⟩
    have hε₂L : ε / (2 * L) * L = ε / 2 := by field_simp
    have hε₂ε : ε / (2 * L) ≤ ε / 2 := by
      rw [← hε₂L]; exact le_mul_of_one_le_right hε₂.le (by exact_mod_cast hL1)
    obtain ⟨h₁, h₂⟩ := norm_comp_diffeomorph_symm_sub_lt_and_le hΦJ' (Finset.subset_insert i₀ J')
      (hf₂'.differentiable (by simp) z) hε₂.le (hΦsL _) (hG₁sub (Φ z)) (hf₁V₁ _ hy) (hf₂'V₂ z hz)
    exact ⟨h₁.trans_le (by linarith), fun w hw ↦ (h₂ w hw).trans_eq (by rw [hε₂L]; ring)⟩
  · refine ⟨W₁ ∩ U₁ ∩ U₂', Filter.inter_mem (Filter.inter_mem hW₁ hU₁) hU₂', fun y hy ↦ ?_⟩
    have hΦy : Φ y = y := by rw [hΦ, hh₁W₁ 1 y hy.1.1]
    have hΦsy : Φ.symm y = y := by
      calc Φ.symm y = Φ.symm (Φ y) := by rw [hΦy]
        _ = y := Φ.symm_apply_apply y
    simp only [Function.comp_apply, hΦsy, hf₂'U₂' hy.2, hΦy]
    exact hf₁U₁ hy.1.2

/-- **Holonomic approximation over the cube in the core directions `J`.** On
`D = (Fin m → ℝ) × (Fin k → ℝ)` with sup norms, `0 < k`, let `Q = closedBall 0 1 ×ˢ {0}` be the
core cube, and let `(f, G)` be a smooth formal section that is holonomic (`D f = G`) on an open
set `U` containing `B ×ˢ {0}`, for a closed set `B` of core points that contains every point of
the cube with a coordinate of absolute value `1` in a direction of `J`. Let `ε, δ > 0`. Then
there are a diffeotopy `h` of `D`, a smooth map `f'` and an open set `V` such that:
* `h` is the identity and `f'` equals `f` off a compact subset of the `δ`-neighbourhood of `Q`;
* `h` moves every point by less than `δ`, keeps the core coordinates outside `J`, and is the
  identity at all times near `B ×ˢ {0}`;
* `V` contains the image of `Q` under `h 1`, and on `V` the map `f'` is `ε`-close to `f`, and
  `(D f' - G) w` has norm at most `ε ‖w‖` for every vector `w` whose core part vanishes outside
  the directions `J`;
* `f'` equals `f` near `B ×ˢ {0}`. -/
theorem exists_holonomic_approximation_cube_directions (hk : 0 < k) (J : Finset (Fin m))
    {f : (Fin m → ℝ) × (Fin k → ℝ) → F}
    {G : (Fin m → ℝ) × (Fin k → ℝ) → (Fin m → ℝ) × (Fin k → ℝ) →L[ℝ] F}
    (hf : ContDiff ℝ ∞ f) (hG : ContDiff ℝ ∞ G) {B : Set (Fin m → ℝ)} (hB : IsClosed B)
    (hJB : ∀ u ∈ closedBall (0 : Fin m → ℝ) 1, (∃ i ∈ J, |u i| = 1) → u ∈ B)
    {U : Set ((Fin m → ℝ) × (Fin k → ℝ))} (hU : IsOpen U) (hBU : B ×ˢ {0} ⊆ U)
    (hUf : ∀ x ∈ U, fderiv ℝ f x = G x) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ (h : TauCeti.Diffeotopy 𝓘(ℝ, (Fin m → ℝ) × (Fin k → ℝ)) ∞ ((Fin m → ℝ) × (Fin k → ℝ)))
      (f' : (Fin m → ℝ) × (Fin k → ℝ) → F) (V : Set ((Fin m → ℝ) × (Fin k → ℝ))),
      (∃ C, IsCompact C ∧ C ⊆ thickening δ (closedBall 0 1 ×ˢ {0}) ∧
        (∀ t, ∀ x ∉ C, h (t, x) = x) ∧ ∀ x ∉ C, f' x = f x) ∧
      (∀ t x, dist (h (t, x)) x < δ) ∧
      (∀ t x, ∀ i ∉ J, (h (t, x)).1 i = x.1 i) ∧
      (∃ W ∈ 𝓝ˢ (B ×ˢ {0}), ∀ t, ∀ x ∈ W, h (t, x) = x) ∧
      IsOpen V ∧ (fun x ↦ h (1, x)) '' (closedBall 0 1 ×ˢ {0}) ⊆ V ∧ ContDiff ℝ ∞ f' ∧
      (∀ x ∈ V, ‖f' x - f x‖ < ε ∧ ∀ w : (Fin m → ℝ) × (Fin k → ℝ),
        (∀ i ∉ J, w.1 i = 0) → ‖(fderiv ℝ f' x - G x) w‖ ≤ ε * ‖w‖) ∧
      ∃ U' ∈ 𝓝ˢ (B ×ˢ {0}), EqOn f' f U' := by
  induction J using Finset.induction_on generalizing ε δ with
  | empty => exact exists_holonomic_approximation_cube_empty hf hG hB hU hBU hUf hε hδ
  | insert i₀ J' _ ih =>
    exact exists_holonomic_approximation_cube_directions_insert hk i₀ hG hB hJB hU hBU hUf
      (fun ε δ hε hδ ↦ ih (fun u hu ⟨i, hi, hui⟩ ↦ hJB u hu ⟨i, Finset.mem_insert_of_mem hi, hui⟩)
        hε hδ) hε hδ

/-- **Holonomic approximation over a cube.** On `D = (Fin m → ℝ) × (Fin k → ℝ)` with sup norms,
`0 < k`, let `Q = closedBall 0 1 ×ˢ {0}` be the core cube, and let `(f, G)` be a smooth formal
section that is holonomic (`D f = G`) on an open set `U` containing `sphere 0 1 ×ˢ {0}`, the
boundary of the cube. Let `ε, δ > 0`. Then there are a diffeotopy `h` of `D`, a smooth map `f'`
and an open set `V` such that:
* `h` is the identity and `f'` equals `f` off a compact subset of the `δ`-neighbourhood of `Q`;
* `h` moves every point by less than `δ`, and is the identity at all times near the boundary
  `sphere 0 1 ×ˢ {0}`;
* `V` contains the image of `Q` under `h 1`, and on `V` the map `f'` is `ε`-close to `f` and
  its derivative is `ε`-close to `G`;
* `f'` equals `f` near the boundary `sphere 0 1 ×ˢ {0}`. -/
theorem exists_holonomic_approximation_cube (hk : 0 < k) {f : (Fin m → ℝ) × (Fin k → ℝ) → F}
    {G : (Fin m → ℝ) × (Fin k → ℝ) → (Fin m → ℝ) × (Fin k → ℝ) →L[ℝ] F}
    (hf : ContDiff ℝ ∞ f) (hG : ContDiff ℝ ∞ G) {U : Set ((Fin m → ℝ) × (Fin k → ℝ))}
    (hU : IsOpen U) (hUf : ∀ x ∈ U, fderiv ℝ f x = G x) (hU' : sphere 0 1 ×ˢ {0} ⊆ U)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ (h : TauCeti.Diffeotopy 𝓘(ℝ, (Fin m → ℝ) × (Fin k → ℝ)) ∞ ((Fin m → ℝ) × (Fin k → ℝ)))
      (f' : (Fin m → ℝ) × (Fin k → ℝ) → F) (V : Set ((Fin m → ℝ) × (Fin k → ℝ))),
      (∃ C, IsCompact C ∧ C ⊆ thickening δ (closedBall 0 1 ×ˢ {0}) ∧
        (∀ t, ∀ x ∉ C, h (t, x) = x) ∧ ∀ x ∉ C, f' x = f x) ∧
      (∀ t x, dist (h (t, x)) x < δ) ∧
      (∃ W ∈ 𝓝ˢ (sphere 0 1 ×ˢ {0}), ∀ t, ∀ x ∈ W, h (t, x) = x) ∧
      IsOpen V ∧ (fun x ↦ h (1, x)) '' (closedBall 0 1 ×ˢ {0}) ⊆ V ∧
      ContDiff ℝ ∞ f' ∧ (∀ x ∈ V, ‖f' x - f x‖ < ε ∧ ‖fderiv ℝ f' x - G x‖ < ε) ∧
      ∃ U' ∈ 𝓝ˢ (sphere 0 1 ×ˢ {0}), EqOn f' f U' := by
  have hJB : ∀ u ∈ closedBall (0 : Fin m → ℝ) 1, (∃ i ∈ Finset.univ, |u i| = 1) →
      u ∈ sphere 0 1 := by
    rintro u hu ⟨i, -, hui⟩
    rw [mem_closedBall_zero_iff] at hu
    rw [mem_sphere_zero_iff_norm]
    refine le_antisymm hu ?_
    rw [← hui, ← Real.norm_eq_abs]
    exact norm_le_pi_norm u i
  obtain ⟨h, f', V, hC, hhδ, -, hW, hV, hQV, hf', hf'V, hU''⟩ :=
    exists_holonomic_approximation_cube_directions hk Finset.univ hf hG isClosed_sphere hJB hU hU'
      hUf (half_pos hε) hδ
  refine ⟨h, f', V, hC, hhδ, hW, hV, hQV, hf', fun x hx ↦ ?_, hU''⟩
  obtain ⟨h₁, h₂⟩ := hf'V x hx
  refine ⟨h₁.trans (half_lt_self hε), ?_⟩
  exact (ContinuousLinearMap.opNorm_le_bound _ (half_pos hε).le
    fun w ↦ h₂ w fun i hi ↦ absurd (Finset.mem_univ i) hi).trans_lt (half_lt_self hε)

end SymplecticGeometry

end
