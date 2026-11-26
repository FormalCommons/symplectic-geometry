/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Geometry.Manifold.ContMDiff.Defs
public import Mathlib.Topology.Homotopy.Contractible
public import SymplecticGeometry.Topology.Sets.Annulus
import SymplecticGeometry.Topology.Homotopy.Disc
import TauCeti.Geometry.Manifold.SmoothApprox.Basic

/-!
# Extending maps from an annulus over the disc

Let `0 ≤ a < a' < 1 < b` and let `f : ℂ → M` be `C^n` on the open annulus `a < ‖z‖ < b`, with
values in a Hausdorff boundaryless manifold modelled on a finite-dimensional real space. If the
loop of `f` on the unit circle is null-homotopic, then some `g : ℂ → M`, `C^n` on the open disc
`‖z‖ < b`, agrees with `f` on the smaller annulus `a' ≤ ‖z‖ < b`.

The proof first extends `f` continuously over the disc, by
`ContinuousOn.exists_continuousMap_eq_of_nullhomotopic` (`Topology/Homotopy/Disc.lean`): for
`a < r < a'` and `1 < R < b`, this gives a continuous map on `ℂ` with relatively compact image
that agrees with `f` on `r ≤ ‖z‖ ≤ R`. The relative Whitney approximation theorem (Tau Ceti's
`ContinuousMap.exists_contMDiff_homotopicRel_of_isCompact_closure_range`) replaces it by a `C^n`
map equal to it on the closed annulus `a' ≤ ‖z‖ ≤ 1`, and that map, continued by `f` outside the
circle of radius `a'`, is `g`.

## Main results

* `ContMDiffOn.exists_contMDiffOn_ball_eq_of_nullhomotopic`: the smooth extension above.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., GTM 218, Springer, 2013, Theorem 6.26
  (the relative Whitney approximation theorem).
-/

public section

open Metric Set Topology
open scoped Manifold ContDiff
open SymplecticGeometry (annulus annulus_mono mem_annulus)
open Complex (closedAnnulus isCompact_closedAnnulus mem_closedAnnulus)

variable {F G M : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace G] {J : ModelWithCorners ℝ F G} [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace G M] [IsManifold J ∞ M] [T2Space M]

/-- **Smooth extension over the disc.** Let `0 ≤ a < a' < 1 < b` and let `f : ℂ → M` be `C^n` on
the open annulus `a < ‖z‖ < b`. If the restriction `γ` of `f` to the unit circle is
null-homotopic, then there is `g : ℂ → M`, `C^n` on the open disc `‖z‖ < b`, with `g z = f z`
whenever `a' ≤ ‖z‖ < b`. -/
theorem ContMDiffOn.exists_contMDiffOn_ball_eq_of_nullhomotopic {n : ℕ∞} {a a' b : ℝ}
    (ha : 0 ≤ a) (haa' : a < a') (ha'1 : a' < 1) (h1b : 1 < b) {f : ℂ → M}
    (hf : ContMDiffOn 𝓘(ℝ, ℂ) J n f (annulus ℂ a b)) (γ : C(Circle, M))
    (hγ : ∀ ζ : Circle, γ ζ = f ζ) (hγ0 : γ.Nullhomotopic) :
    ∃ g : ℂ → M, ContMDiffOn 𝓘(ℝ, ℂ) J n g (ball 0 b) ∧
      ∀ z : ℂ, a' ≤ ‖z‖ → ‖z‖ < b → g z = f z := by
  set r₀ : ℝ := (a + a') / 2 with hr₀_def
  set b' : ℝ := (1 + b) / 2 with hb'_def
  -- a continuous extension `F₀` of `f` from the annulus `r₀ ≤ ‖z‖ ≤ b'` with relatively compact
  -- image
  obtain ⟨F₀, hF₀K, hF₀f⟩ := ContinuousOn.exists_continuousMap_eq_of_nullhomotopic
    (r := r₀) (R := b') (by linarith) (by linarith) (by linarith)
    (hf.continuousOn.mono fun z hz ↦ mem_annulus.2
      ⟨by linarith [(mem_closedAnnulus.1 hz).1], by linarith [(mem_closedAnnulus.1 hz).2]⟩)
    γ hγ hγ0
  set S : Set ℂ := closedAnnulus a' 1
  set U : Set ℂ := (annulus ℂ r₀ b' : Set ℂ)
  have hS : IsClosed S := (isCompact_closedAnnulus a' 1).isClosed
  have hU : IsOpen U := (annulus ℂ r₀ b').isOpen
  have hSU : S ⊆ U := fun z hz ↦ mem_annulus.2
    ⟨by linarith [(mem_closedAnnulus.1 hz).1], by linarith [(mem_closedAnnulus.1 hz).2]⟩
  have hF₀U (z : ℂ) (hz : z ∈ U) : F₀ z = f z :=
    hF₀f z (mem_annulus.1 hz).1.le (mem_annulus.1 hz).2.le
  -- the relative Whitney approximation gives a `C^n` map `g₀` equal to `F₀` on `S`
  obtain ⟨g₀, hg₀, hF₀g₀⟩ :=
    F₀.exists_contMDiff_homotopicRel_of_isCompact_closure_range (I := 𝓘(ℝ, ℂ)) n hF₀K hS
      (hU.mem_nhdsSet.2 hSU)
      ((hf.mono (annulus_mono (by linarith) (by linarith))).congr hF₀U)
  have hg₀f {z : ℂ} (hz : z ∈ S) : g₀ z = f z :=
    (hF₀g₀.fst_eq_snd hz).symm.trans (hF₀U z (hSU hz))
  -- `g₀` inside the circle of radius `a'`, and `f` outside
  let g : ℂ → M := fun z ↦ if ‖z‖ ≤ a' then g₀ z else f z
  have hgf {z : ℂ} (h₁ : a' ≤ ‖z‖) : g z = f z := by
    by_cases h : ‖z‖ ≤ a'
    · exact (ite_eq_left h).trans (hg₀f (mem_closedAnnulus.2 ⟨h₁, h.trans ha'1.le⟩))
    · exact ite_eq_right h
  have hgg₀ {z : ℂ} (h₁ : ‖z‖ < 1) : g z = g₀ z := by
    by_cases h : ‖z‖ ≤ a'
    · exact ite_eq_left h
    · rw [hgf (not_le.1 h).le, hg₀f (mem_closedAnnulus.2 ⟨(not_le.1 h).le, h₁.le⟩)]
  refine ⟨g, fun z hz ↦ ContMDiffAt.contMDiffWithinAt ?_, fun z h₁ _ ↦ hgf h₁⟩
  by_cases h : ‖z‖ < 1
  · exact (hg₀ z).congr_of_eventuallyEq <| Filter.eventually_of_mem
      ((isOpen_lt continuous_norm continuous_const).mem_nhds h) fun w hw ↦ hgg₀ hw
  · have hzV : (annulus ℂ a' b : Set ℂ) ∈ 𝓝 z :=
      (annulus ℂ a' b).isOpen.mem_nhds
        (mem_annulus.2 ⟨by linarith [not_lt.1 h], mem_ball_zero_iff.1 hz⟩)
    exact (hf.contMDiffAt (Filter.mem_of_superset hzV (annulus_mono haa'.le le_rfl))
      ).congr_of_eventuallyEq <| Filter.eventually_of_mem hzV fun w hw ↦
        hgf (mem_annulus.1 hw).1.le
