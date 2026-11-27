/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import TauCeti.Analysis.Calculus.FDeriv.Remainder

/-!
# Functions vanishing to first order on a set

Let `D : E → G` be `C²` on an open set `U` of a finite-dimensional real normed space, and let
`D` and its derivative vanish at the points of a set `Z` that lie in `U`. Near a compact set
`K ⊆ Z` with `K ⊆ U`, the function is then quadratically small and its derivative linearly
small in the distance to `Z`: there is `A` with
`‖D x‖ ≤ A * infDist x Z ^ 2` and `‖fderiv ℝ D x‖ ≤ A * infDist x Z` for `x` near `K`
(`IsCompact.exists_eventually_norm_le_mul_infDist_sq_and_norm_fderiv_le_mul_infDist`).

The proof compares `x` with a nearest point `z` of `closure Z`, at which `D` and its derivative
vanish by continuity. The bound on `D x` is the second-order Taylor estimate at `z`, and the bound
on `fderiv ℝ D x` the Lipschitz bound of `fderiv ℝ D` at `z`, both uniform over the compact set of
such `z` near `K`; they are Tau Ceti's
`IsCompact.exists_pos_forall_norm_sub_sub_fderiv_sub_le_mul` and
`IsCompact.exists_pos_forall_norm_sub_le_mul`, applied to a constant family.

This is the calculus behind the Taylor bounds near a totally real submanifold in the proof of
Proposition 3.26 of Cieliebak–Eliashberg, where `Z` is the image of the submanifold in a chart.

## References

* [K. Cieliebak, Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  Proposition 3.26
-/

public section

open Filter Metric Set
open scoped Topology

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- **A function vanishing to first order on a set is quadratically small near it.** Let `D` be
`C²` on an open set `U` of a finite-dimensional real normed space, with `D z = 0` and
`fderiv ℝ D z = 0` at every `z ∈ Z ∩ U`. If `K ⊆ Z` is compact and `K ⊆ U`, there is `A` such
that `‖D x‖ ≤ A * infDist x Z ^ 2` and `‖fderiv ℝ D x‖ ≤ A * infDist x Z` for all `x` near
`K`. -/
theorem IsCompact.exists_eventually_norm_le_mul_infDist_sq_and_norm_fderiv_le_mul_infDist
    {D : E → G} {Z K U : Set E} (hK : IsCompact K) (hKZ : K ⊆ Z) (hU : IsOpen U) (hKU : K ⊆ U)
    (hD : ContDiffOn ℝ 2 D U) (hD0 : ∀ z ∈ Z ∩ U, D z = 0)
    (hD1 : ∀ z ∈ Z ∩ U, fderiv ℝ D z = 0) :
    ∃ A, ∀ᶠ x in 𝓝ˢ K,
      ‖D x‖ ≤ A * infDist x Z ^ 2 ∧ ‖fderiv ℝ D x‖ ≤ A * infDist x Z := by
  obtain ⟨r, hr, hrU⟩ := hK.exists_cthickening_subset_open hU hKU
  -- The base points: the points of `closure Z` near `K`, a compact subset of `U`.
  set S := closure Z ∩ cthickening r K
  have hS : IsCompact S := (hK.cthickening (r := r)).inter_left isClosed_closure
  have hSU : S ⊆ U := inter_subset_right.trans hrU
  -- `D` and its derivative vanish on `closure Z ∩ U`, by continuity on the open set `U`.
  have hsub : U ∩ closure Z ⊆ closure (U ∩ Z) := hU.inter_closure
  have hZ : U ∩ Z ⊆ U ∩ closure Z := inter_subset_inter_right U subset_closure
  have hS0 : ∀ z ∈ S, D z = 0 ∧ fderiv ℝ D z = 0 := fun z hz => by
    have hz' : z ∈ U ∩ closure Z := ⟨hSU hz, hz.1⟩
    exact ⟨Set.EqOn.of_subset_closure (s := U ∩ Z) (f := D) (g := 0)
        (fun y hy => hD0 y ⟨hy.2, hy.1⟩) (hD.continuousOn.mono inter_subset_left)
        continuousOn_const hZ hsub hz',
      Set.EqOn.of_subset_closure (s := U ∩ Z) (f := fderiv ℝ D) (g := 0)
        (fun y hy => hD1 y ⟨hy.2, hy.1⟩)
        ((hD.continuousOn_fderiv_of_isOpen hU (by norm_num)).mono inter_subset_left)
        continuousOn_const hZ hsub hz'⟩
  have hDz (z : E) (hz : z ∈ S) : ContDiffAt ℝ 2 D z := hD.contDiffAt (hU.mem_nhds (hSU hz))
  -- The uniform second-order remainder of `D`, and the uniform Lipschitz bound of its
  -- derivative, at the points of `S`.
  obtain ⟨δ₁, hδ₁, L₁, h₁⟩ := hS.exists_pos_forall_norm_sub_sub_fderiv_sub_le_mul
    (F := fun _ => D) (x := id) (fun z hz => (hDz z hz).comp (z, z) contDiffAt_snd)
    continuousOn_id
  obtain ⟨δ₂, hδ₂, L₂, h₂⟩ := hS.exists_pos_forall_norm_sub_le_mul
    (F := fun _ => fderiv ℝ D) (x := id)
    (fun z hz => ((hDz z hz).fderiv_right (m := 1) (by norm_num)).comp (z, z) contDiffAt_snd)
    continuousOn_id
  set ε := min (min δ₁ δ₂) (r / 2)
  have hε : 0 < ε := by positivity
  refine ⟨max L₁ L₂, eventually_of_mem (thickening_mem_nhdsSet K hε) fun x hx => ?_⟩
  obtain ⟨k, hk, hxk⟩ := mem_thickening_iff.1 hx
  -- A nearest point `z` of `closure Z` to `x` lies in `S`, at distance `infDist x Z < ε`.
  obtain ⟨z, hzZ, hxz⟩ :=
    isClosed_closure.exists_infDist_eq_dist ⟨k, subset_closure (hKZ hk)⟩ x
  rw [infDist_closure] at hxz
  have hdε : dist x z < ε := hxz ▸ (infDist_le_dist_of_mem (hKZ hk)).trans_lt hxk
  have hzS : z ∈ S := ⟨hzZ, mem_cthickening_of_dist_le z k r K hk (by
    linarith [dist_triangle z x k, dist_comm x z, min_le_right (min δ₁ δ₂) (r / 2)])⟩
  obtain ⟨hDz0, hDz1⟩ := hS0 z hzS
  have hd : ‖x - z‖ = infDist x Z := by rw [hxz, dist_eq_norm]
  have hd₁ : ‖x - z‖ ≤ δ₁ := by
    rw [← dist_eq_norm]; linarith [min_le_left (min δ₁ δ₂) (r / 2), min_le_left δ₁ δ₂]
  have hd₂ : ‖x - z‖ ≤ δ₂ := by
    rw [← dist_eq_norm]; linarith [min_le_left (min δ₁ δ₂) (r / 2), min_le_right δ₁ δ₂]
  constructor
  · have h := h₁ z hzS (x - z) 0 hd₁ (by simpa using hδ₁.le)
    simp only [id, add_sub_cancel, add_zero, sub_zero, hDz0, hDz1, norm_zero,
      zero_apply, max_eq_left (norm_nonneg _)] at h
    rw [← hd, sq, ← mul_assoc]
    exact h.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)) (norm_nonneg _))
  · have h := h₂ z hzS x hd₂
    simp only [id, hDz1, sub_zero] at h
    rw [← hd]
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
