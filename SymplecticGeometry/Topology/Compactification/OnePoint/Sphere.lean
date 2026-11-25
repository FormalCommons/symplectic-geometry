/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Compactification.OnePoint.Sphere

/-!
# Stereographic projection and the one-point compactification of a hyperplane

Evaluation lemmas for Mathlib's homeomorphism `onePointHyperplaneHomeoUnitSphere` between the
one-point compactification of the hyperplane `(ℝ ∙ v)ᗮ` and the unit sphere: it sends `∞` to `v`
and agrees with the inverse of the stereographic projection `stereographic` on the hyperplane.
Also `stereographicHomeomorph`, the stereographic projection from a point `v` of the unit sphere
as a homeomorphism of the complement of `v` onto `(ℝ ∙ v)ᗮ`.
-/

public section

open Metric OnePoint Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The stereographic projection from a point `v` of the unit sphere, as a homeomorphism of the
complement of `v` onto the hyperplane `(ℝ ∙ v)ᗮ`. -/
noncomputable def stereographicHomeomorph (v : sphere (0 : E) 1) :
    ({v}ᶜ : Set (sphere (0 : E) 1)) ≃ₜ (ℝ ∙ (v : E))ᗮ :=
  ((Homeomorph.setCongr (stereographic_source (norm_eq_of_mem_sphere v)).symm).trans
    (stereographic (norm_eq_of_mem_sphere v)).toHomeomorphSourceTarget).trans
    ((Homeomorph.setCongr (stereographic_target (norm_eq_of_mem_sphere v))).trans
      (Homeomorph.Set.univ _))

@[simp]
theorem stereographicHomeomorph_apply (v : sphere (0 : E) 1)
    (x : ({v}ᶜ : Set (sphere (0 : E) 1))) :
    stereographicHomeomorph v x = stereographic (norm_eq_of_mem_sphere v) x :=
  (rfl)

@[simp]
theorem coe_stereographicHomeomorph_symm_apply (v : sphere (0 : E) 1) (w : (ℝ ∙ (v : E))ᗮ) :
    ((stereographicHomeomorph v).symm w : sphere (0 : E) 1) =
      (stereographic (norm_eq_of_mem_sphere v)).symm w :=
  (rfl)

variable [FiniteDimensional ℝ E]

@[simp]
theorem onePointHyperplaneHomeoUnitSphere_apply_infty (v : sphere (0 : E) 1) :
    onePointHyperplaneHomeoUnitSphere (norm_eq_of_mem_sphere v) ∞ = v := by
  rw [onePointHyperplaneHomeoUnitSphere, OnePoint.equivOfIsEmbeddingOfRangeEq_apply_infty]

@[simp]
theorem onePointHyperplaneHomeoUnitSphere_apply_coe {v : E} (hv : ‖v‖ = 1) (w : (ℝ ∙ v)ᗮ) :
    onePointHyperplaneHomeoUnitSphere hv w = (stereographic hv).symm w := by
  rw [onePointHyperplaneHomeoUnitSphere, OnePoint.equivOfIsEmbeddingOfRangeEq_apply_coe]
