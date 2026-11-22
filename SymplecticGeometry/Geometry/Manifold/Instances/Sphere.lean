/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# Maps into a unit sphere that are smooth on an open set

Mathlib's `ContMDiff.codRestrict_sphere` says that a map into the unit sphere of a real inner
product space `E` is smooth when its composite with the inclusion `sphere 0 1 → E` is. This file
gives the version on an open set of a manifold, `ContMDiffOn.of_coe_sphere`, obtained from
Mathlib's lemma on the open set as a manifold of its own (`contMDiffAt_subtype_iff`). For
`E = ℂ` it applies to maps into `Circle`.
-/

public section

open Set TopologicalSpace Metric Module
open scoped Manifold ContDiff

variable {m : ℕ∞ω} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ EM H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I m M]

/-- A map into the unit sphere of `E` is `C^m` on an open set if its composite with the inclusion
`sphere 0 1 → E` is `C^m` there. -/
theorem ContMDiffOn.of_coe_sphere {n : ℕ} [Fact (finrank ℝ E = n + 1)]
    {f : M → sphere (0 : E) 1} {s : Set M} (hs : IsOpen s)
    (hf : ContMDiffOn I 𝓘(ℝ, E) m (fun x ↦ (f x : E)) s) :
    ContMDiffOn I (𝓡 n) m f s := by
  intro x hx
  let U : Opens M := ⟨s, hs⟩
  have hU : ContMDiff I 𝓘(ℝ, E) m fun y : U ↦ (f y : E) := fun y ↦
    contMDiffAt_subtype_iff.2 ((hf y y.property).contMDiffAt (hs.mem_nhds y.property))
  have h : ContMDiff I (𝓡 n) m fun y : U ↦ f y :=
    hU.codRestrict_sphere (f := fun y : U ↦ (f y : E)) fun y ↦ (f y).property
  exact (contMDiffAt_subtype_iff (U := U) (x := ⟨x, hx⟩)).1 (h ⟨x, hx⟩) |>.contMDiffWithinAt
