/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.SmoothEmbedding
public import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.Neighborhood
import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.UnivBall

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
embedding of `ℝ` (`Manifold.IsSmoothEmbedding.comp_univBall`).

## Main results

* `SymplecticGeometry.exists_isSmoothEmbedding_real_of_mem_nhds`: a smooth embedding
  `σ : ℝ → M` through `p` with closure of its range in a given neighbourhood `V` of `p`,
  converging at `-∞` to a point `q` outside its range, with
  `closure (σ '' Iic T) = insert q (σ '' Iic T)` for every `T`.

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
    have hmem := (hLK s hs).1
    rw [mfderiv_comp s (((contMDiffOn_extChartAt_symm (n := ∞) p).contMDiffAt
      ((isOpen_extChartAt_target p).mem_nhds hmem)).mdifferentiableAt (by simp))
      (hL.contMDiff.mdifferentiableAt (by simp))]
    have h1 := isInvertible_mfderivWithin_extChartAt_symm (I := I) hmem
    rw [I.range_eq_univ, mfderivWithin_univ] at h1
    refine h1.injective.comp ?_
    have hLd : HasFDerivAt L ((1 : ℝ →L[ℝ] ℝ).smulRight w) s :=
      ((hasFDerivAt_id s).smul_const w).const_add (e p)
    rw [(hasMFDerivAt_iff_hasFDerivAt.2 hLd).mfderiv]
    have hinjL : Injective ((1 : ℝ →L[ℝ] ℝ).smulRight w) := fun a b h ↦
      smul_left_injective ℝ hw0 (by simpa using h)
    -- The tangent spaces of `ℝ` and `E` are `ℝ` and `E` by definition.
    exact hinjL
  obtain ⟨W, hKW, -, hW⟩ := TauCeti.exists_isOpen_isSmoothEmbedding_of_injOn hO hf isCompact_Icc
    (fun s hs ↦ (hLK s hs).1) hinj himm
  -- Reparametrize `f` on `(-1, 1)` by `u`, an increasing map of `ℝ` onto `(-1, 1)`.
  set u : ℝ → ℝ := ⇑(univBall (0 : ℝ) 1)
  have hu (t : ℝ) : u t ∈ Ioo (-1) 1 := by
    have := range_univBall (E := ℝ) (0 : ℝ) one_pos ▸ mem_range_self (f := u) t
    simpa [Real.ball_eq_Ioo] using this
  have hfK : ContinuousOn f K := hf.continuousOn.mono fun s hs ↦ (hLK s hs).1
  have hm1 : (-1 : ℝ) ∈ K := ⟨le_rfl, by norm_num⟩
  have htend : Tendsto (f ∘ u) atBot (𝓝 (f (-1))) :=
    (hf.continuousOn.continuousAt (hO.mem_nhds (hLK (-1) hm1).1)).tendsto.comp
      (by simpa using tendsto_univBall_real_atBot 0 one_pos)
  refine ⟨f ∘ u, f (-1), hW.comp_univBall one_pos
    (fun t ht ↦ hKW (Ioo_subset_Icc_self (by simpa [Real.ball_eq_Ioo] using ht))) le_rfl,
    by simp [u, f, L, e], ?_, htend, ?_, fun T ↦ ?_⟩
  · refine closure_minimal ?_ ((isCompact_Icc.image_of_continuousOn hfK).isClosed) |>.trans ?_
    · rintro _ ⟨t, rfl⟩
      exact mem_image_of_mem f (Ioo_subset_Icc_self (hu t))
    · rintro _ ⟨s, hs, rfl⟩
      exact (hLK s hs).2
  · rintro ⟨t, ht⟩
    exact (hu t).1.ne' (hinj (Ioo_subset_Icc_self (hu t)) hm1 ht)
  · refine (closure_minimal (subset_insert _ _) ?_).antisymm
      (insert_subset (mem_closure_of_tendsto htend ?_) subset_closure)
    · rw [image_comp, image_univBall_real_Iic 0 one_pos, zero_sub, ← image_insert_eq,
        insert_left_Ioc (hu T).1.le]
      exact (isCompact_Icc.image_of_continuousOn
        (hfK.mono (Icc_subset_Icc le_rfl (hu T).2.le))).isClosed
    · exact (eventually_le_atBot T).mono fun t ht ↦ mem_image_of_mem _ ht

end SymplecticGeometry

end
