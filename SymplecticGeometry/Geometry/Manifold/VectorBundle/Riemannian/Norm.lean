/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import TauCeti.Geometry.Manifold.ContMDiff.Sqrt

/-!
# Smoothness of the norm of a section of a Riemannian bundle

For a `C^n` Riemannian metric on a vector bundle `E`, Mathlib's `ContMDiffWithinAt.inner_bundle`
says that the inner product of two `C^n` maps into the total space over a common base map is
`C^n`. This file deduces that the norm `‖v m‖` of such a map is `C^n` where `v` does not vanish
(`ContMDiffWithinAt.norm_bundle` and its variants), as the square root of `⟪v m, v m⟫`.
-/

public section

open Bundle
open scoped Manifold ContDiff

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {n : ℕ∞ω}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)] [∀ x, NormedAddCommGroup (E x)]
  [∀ x, InnerProductSpace ℝ (E x)] [FiberBundle F E] [VectorBundle ℝ F E]
  [IsContMDiffRiemannianBundle IB n F E]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  {HM : Type*} [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  {b : M → B} {v : ∀ x, E (b x)} {s : Set M} {x : M}

/-- The norm of a map into a Riemannian bundle that is `C^n` within a set at a point where it does
not vanish is `C^n` within that set there. -/
theorem ContMDiffWithinAt.norm_bundle
    (hv : ContMDiffWithinAt IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (v m : TotalSpace F E)) s x)
    (hx : v x ≠ 0) :
    ContMDiffWithinAt IM 𝓘(ℝ) n (fun m ↦ ‖v m‖) s x :=
  ((hv.inner_bundle hv).sqrt (inner_self_ne_zero.2 hx)).congr
    (fun _ _ ↦ norm_eq_sqrt_real_inner _) (norm_eq_sqrt_real_inner _)

/-- The norm of a map into a Riemannian bundle that is `C^n` at a point where it does not vanish
is `C^n` there. -/
theorem ContMDiffAt.norm_bundle
    (hv : ContMDiffAt IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (v m : TotalSpace F E)) x)
    (hx : v x ≠ 0) :
    ContMDiffAt IM 𝓘(ℝ) n (fun m ↦ ‖v m‖) x :=
  ContMDiffWithinAt.norm_bundle hv hx

/-- The norm of a map into a Riemannian bundle that is `C^n` on a set where it does not vanish is
`C^n` there. -/
theorem ContMDiffOn.norm_bundle
    (hv : ContMDiffOn IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (v m : TotalSpace F E)) s)
    (hs : ∀ x ∈ s, v x ≠ 0) :
    ContMDiffOn IM 𝓘(ℝ) n (fun m ↦ ‖v m‖) s :=
  fun x hx ↦ (hv x hx).norm_bundle (hs x hx)

/-- The norm of a nowhere-vanishing `C^n` map into a Riemannian bundle is `C^n`. -/
theorem ContMDiff.norm_bundle
    (hv : ContMDiff IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (v m : TotalSpace F E)))
    (h : ∀ x, v x ≠ 0) :
    ContMDiff IM 𝓘(ℝ) n (fun m ↦ ‖v m‖) :=
  fun x ↦ (hv x).norm_bundle (h x)
