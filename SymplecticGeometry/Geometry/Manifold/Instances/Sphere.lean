/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# Maps into the unit circle that are smooth on an open set

Mathlib's `ContMDiff.codRestrict_sphere` says that a map into the unit circle is smooth when its
composite with the inclusion `Circle → ℂ` is. This file gives the version on an open set of a
manifold, `ContMDiffOn.of_coe_circle`, obtained from Mathlib's lemma on the open set as a
manifold of its own (`contMDiffAt_subtype_iff`).
-/

public section

open Set TopologicalSpace
open scoped Manifold ContDiff

variable {m : ℕ∞ω} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I m M]

attribute [local instance] finrank_real_complex_fact'

/-- A map into `Circle` is `C^m` on an open set if its composite with the inclusion `Circle → ℂ`
is `C^m` there. -/
theorem ContMDiffOn.of_coe_circle {f : M → Circle} {s : Set M} (hs : IsOpen s)
    (hf : ContMDiffOn I 𝓘(ℝ, ℂ) m (fun x ↦ (f x : ℂ)) s) :
    ContMDiffOn I (𝓡 1) m f s := by
  intro x hx
  let U : Opens M := ⟨s, hs⟩
  have hU : ContMDiff I 𝓘(ℝ, ℂ) m fun y : U ↦ (f y : ℂ) := fun y ↦
    contMDiffAt_subtype_iff.2 ((hf y y.property).contMDiffAt (hs.mem_nhds y.property))
  have h : ContMDiff I (𝓡 1) m fun y : U ↦ f y :=
    hU.codRestrict_sphere (f := fun y : U ↦ (f y : ℂ)) fun y ↦ (f y).property
  exact (contMDiffAt_subtype_iff (U := U) (x := ⟨x, hx⟩)).1 (h ⟨x, hx⟩) |>.contMDiffWithinAt

omit [IsManifold I m M] in
/-- The inclusion `Circle → ℂ` is `C^m`. -/
theorem contMDiff_coe_circle : ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) m fun z : Circle ↦ (z : ℂ) :=
  contMDiff_coe_sphere (E := ℂ) (n := 1)
