/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.SmoothEmbedding
public import Mathlib.Order.Filter.AtTopBot.Defs
import TauCeti.Geometry.Manifold.MFDeriv.IsInvertible
import TauCeti.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.Neighborhood
import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.UnivBall
import SymplecticGeometry.Analysis.Normed.Module.Ball.Homeomorph

/-!
# Short straight segments through a point of a manifold

Let `M` be a Hausdorff smooth manifold without boundary, modelled on a nontrivial
finite-dimensional real normed space. Through every point `p` of `M`, and inside any given
neighbourhood of `p`, there is a smooth embedding `σ : ℝ → M` with `σ 0 = p` whose image is a
short straight segment in the extended chart at `p`, run through as `t` goes from `-∞` to `∞`.
As `t → -∞` it converges to the end point `q` of the segment, which `σ` does not reach, so the
closure of each backward half `σ '' Iic T` is that half together with `q`.

Such a segment starts a new ray in the construction of proper rays
(`Geometry/Manifold/ProperRay.lean`); the end point `q` records where the backward half of the
ray fails to be closed.

The proof takes the affine line `s ↦ e p + s • w` in the extended chart `e` at `p`, with `w` so
short that for `s ∈ [-1, 1]` the line stays in the target of `e` and `e.symm` maps it into `V`.
Composed with `e.symm`, the line is injective with injective differential on `[-1, 1]`; hence
it restricts to a smooth embedding on some open set around `[-1, 1]`
(`TauCeti.exists_isOpen_isSmoothEmbedding_of_injOn`). Precomposing with Mathlib's
`OpenPartialHomeomorph.univBall 0 1`, an increasing map of `ℝ` onto `(-1, 1)`, gives a smooth
embedding of `ℝ` (`Manifold.IsSmoothEmbedding.comp_univBall`). Its behaviour at `-∞`, with
`q` the image of `-1`, is that of any map continuous and injective on `[-1, 1]` precomposed
with `univBall 0 1` (`ContinuousOn.tendsto_comp_univBall_atBot`,
`Set.InjOn.notMem_range_comp_univBall`, `ContinuousOn.closure_image_comp_univBall_Iic`).

## Main results

* `SymplecticGeometry.exists_isSmoothEmbedding_real_of_mem_nhds`: a smooth embedding
  `σ : ℝ → M` through `p` with closure of its range in a given neighbourhood `V` of `p`,
  converging at `-∞` to a point `q` outside its range, with
  `closure (σ '' Iic T) = insert q (σ '' Iic T)` for every `T`.
* `SymplecticGeometry.exists_isSmoothEmbedding_real_pairwiseDisjoint_of_mem_nhds`: such
  segments through the points of a finite set at once, with pairwise disjoint closures of their
  ranges, by separating the points with disjoint open sets (`Set.Finite.t2_separation`).

## References

* [M. W. Hirsch, *Differential Topology*][Hirsch1976], Chapter 1, §3, for immersions and
  embeddings.
-/

public section

open Set Function Filter Topology Manifold OpenPartialHomeomorph
open scoped ContDiff

namespace SymplecticGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **A short smooth segment through a point.** Let `M` be a Hausdorff smooth manifold without
boundary, modelled on a nontrivial finite-dimensional real normed space, `p ∈ M` and `V` a
neighbourhood of `p`. There are a smooth embedding `σ : ℝ → M` with `σ 0 = p` and
`closure (range σ) ⊆ V`, and a point `q` outside the range of `σ` such that `σ t → q` as
`t → -∞` and, for every `T`, the closure of `σ '' Iic T` is `σ '' Iic T` together with `q`. -/
theorem exists_isSmoothEmbedding_real_of_mem_nhds {p : M} {V : Set M} (hV : V ∈ 𝓝 p) :
    ∃ σ : ℝ → M, ∃ q : M, IsSmoothEmbedding 𝓘(ℝ) I ∞ σ ∧ σ 0 = p ∧ closure (range σ) ⊆ V ∧
      Tendsto σ atBot (𝓝 q) ∧ q ∉ range σ ∧
      ∀ T, closure (σ '' Iic T) = insert q (σ '' Iic T) := by
  set e := extChartAt I p
  -- A ball around `e p` in the target of `e` whose points `e.symm` sends into `V`.
  obtain ⟨r, hr, hrV⟩ := Metric.mem_nhds_iff.1 (inter_mem (extChartAt_target_mem_nhds (I := I) p)
    ((continuousAt_extChartAt_symm (I := I) p).preimage_mem_nhds (by rwa [extChartAt_to_inv])))
  obtain ⟨w, hw⟩ := exists_norm_eq E (half_pos hr).le
  have hw0 : w ≠ 0 := norm_pos_iff.1 (hw ▸ half_pos hr)
  -- The straight line through `e p` in the direction `w`, and its image `f` in `M`.
  set L : ℝ → E := fun s ↦ e p + s • w
  have hL : ContDiff ℝ ∞ L := contDiff_const.add (contDiff_id.smul contDiff_const)
  set f : ℝ → M := e.symm ∘ L
  set K : Set ℝ := Icc (-1) 1
  have hLK : ∀ s ∈ K, L s ∈ e.target ∩ e.symm ⁻¹' V := fun s hs ↦ hrV <| by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, hw]
    have : ‖s‖ ≤ 1 := abs_le.2 hs
    nlinarith
  set O : Set ℝ := L ⁻¹' e.target
  have hO : IsOpen O := (isOpen_extChartAt_target p).preimage hL.continuous
  have hf : ContMDiffOn 𝓘(ℝ) I ∞ f O :=
    (contMDiffOn_extChartAt_symm p).comp hL.contMDiff.contMDiffOn fun _ h ↦ h
  have hinj : InjOn f K := fun s hs s' hs' h ↦
    smul_left_injective ℝ hw0 (add_left_cancel (e.symm.injOn (hLK s hs).1 (hLK s' hs').1 h))
  have himm : ∀ s ∈ K, Injective (mfderiv 𝓘(ℝ) I f s) := by
    intro s hs
    have h1 := TauCeti.isInvertible_mfderiv_extChartAt_symm (I := I) (hLK s hs).1
    have hLd : HasFDerivAt L ((1 : ℝ →L[ℝ] ℝ).smulRight w) s :=
      ((hasFDerivAt_id s).smul_const w).const_add (e p)
    refine TauCeti.injective_mfderiv_comp (f := L) h1.injective ?_
    rw [(hasMFDerivAt_iff_hasFDerivAt.2 hLd).mfderiv]
    have hinjL : Injective ((1 : ℝ →L[ℝ] ℝ).smulRight w) := fun a b h ↦
      smul_left_injective ℝ hw0 (by simpa using h)
    exact hinjL
  obtain ⟨W, hKW, -, hW⟩ := TauCeti.exists_isOpen_isSmoothEmbedding_of_injOn hO hf isCompact_Icc
    (fun s hs ↦ (hLK s hs).1) hinj himm
  -- Reparametrize `f` on `(-1, 1)` by Mathlib's map `univBall 0 1` of `ℝ` onto `(-1, 1)`.
  have hfK : ContinuousOn f (Icc (0 - 1) (0 + 1)) := by
    simpa using hf.continuousOn.mono fun s hs ↦ (hLK s hs).1
  have hinj' : InjOn f (Icc (0 - 1) (0 + 1)) := by simpa using hinj
  refine ⟨f ∘ univBall (0 : ℝ) 1, f (-1), hW.comp_univBall one_pos
    (fun t ht ↦ hKW (Ioo_subset_Icc_self (by simpa [Real.ball_eq_Ioo] using ht))) le_rfl,
    by simp [f, L, e], ?_, by simpa using hfK.tendsto_comp_univBall_atBot one_pos,
    by simpa using hinj'.notMem_range_comp_univBall one_pos,
    fun T ↦ by simpa using hfK.closure_image_comp_univBall_Iic one_pos T⟩
  refine (hfK.closure_range_comp_univBall_subset one_pos).trans ?_
  rintro _ ⟨s, hs, rfl⟩
  exact (hLK s (by simpa [K] using hs)).2

/-- **Disjoint short segments through finitely many points.** For a finite set `N` of points of
`M` and a neighbourhood `G p` of each `p ∈ N`, there are smooth embeddings `σ p : ℝ → M` and
points `q p` such that, for each `p ∈ N`, `σ p 0 = p`, the closure of the range of `σ p` lies in
`G p`, `σ p t → q p` as `t → -∞`, `q p` is not in the range of `σ p`, and for every `T` the
closure of `σ p '' Iic T` is `σ p '' Iic T` together with `q p`; moreover, the closures of the
ranges of the `σ p` are pairwise disjoint. -/
theorem exists_isSmoothEmbedding_real_pairwiseDisjoint_of_mem_nhds (N : Finset M) {G : M → Set M}
    (hG : ∀ p ∈ N, G p ∈ 𝓝 p) :
    ∃ (σ : M → ℝ → M) (q : M → M), (∀ p ∈ N, IsSmoothEmbedding 𝓘(ℝ) I ∞ (σ p)) ∧
      (∀ p ∈ N, σ p 0 = p) ∧ (∀ p ∈ N, closure (range (σ p)) ⊆ G p) ∧
      (∀ p ∈ N, Tendsto (σ p) atBot (𝓝 (q p))) ∧ (∀ p ∈ N, q p ∉ range (σ p)) ∧
      (∀ p ∈ N, ∀ T, closure (σ p '' Iic T) = insert (q p) (σ p '' Iic T)) ∧
      (N : Set M).PairwiseDisjoint fun p ↦ closure (range (σ p)) := by
  classical
  obtain ⟨U, hU, hUd⟩ := N.finite_toSet.t2_separation
  have hGU (p : M) (hp : p ∈ N) : G p ∩ U p ∈ 𝓝 p :=
    Filter.inter_mem (hG p hp) ((hU p).2.mem_nhds (hU p).1)
  choose! σ q hσ hσ0 hσV hσq hqσ hσcl using fun p (hp : p ∈ N) ↦
    exists_isSmoothEmbedding_real_of_mem_nhds (I := I) (hGU p hp)
  refine ⟨σ, q, hσ, hσ0, fun p hp ↦ (hσV p hp).trans inter_subset_left, hσq, hqσ, hσcl,
    fun a ha b hb hab ↦ ?_⟩
  exact (hUd ha hb hab).mono ((hσV a ha).trans inter_subset_right)
    ((hσV b hb).trans inter_subset_right)

end SymplecticGeometry

end
