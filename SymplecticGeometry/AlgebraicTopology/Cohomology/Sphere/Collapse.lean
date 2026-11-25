/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Sphere.Stereographic
public import TauCeti.Topology.Compactification.OnePoint.Collapse
public import SymplecticGeometry.Topology.Compactification.OnePoint.Sphere

/-!
# The collapse map `S^a × S^b → S^{a+b}`

For finite-dimensional real inner product spaces `E`, `F`, `G` with
`finrank ℝ E + finrank ℝ F = finrank ℝ G + 1`, so that their unit spheres have dimensions `a`, `b`
and `a + b`, and base points `p`, `q`, `r` of these spheres, `SymplecticGeometry.sphereCollapse`
is a continuous map `sphere (0 : E) 1 × sphere (0 : F) 1 → sphere (0 : G) 1` that factors
through the smash product: it sends the wedge `{p} × S^b ∪ S^a × {q}` to `r`, and maps the
complement of the wedge homeomorphically onto the complement of `r`.

The inverse stereographic projections from `p` and `q` embed `(ℝ ∙ p)ᗮ × (ℝ ∙ q)ᗮ` as the
complement of the wedge. The map is Tau Ceti's collapse `TauCeti.onePointCollapse` of
`S^a × S^b` onto the one-point compactification of `(ℝ ∙ r)ᗮ` along this embedding and a linear
equivalence `(ℝ ∙ p)ᗮ × (ℝ ∙ q)ᗮ ≃ (ℝ ∙ r)ᗮ`, followed by Mathlib's homeomorphism
`onePointHyperplaneHomeoUnitSphere` of that compactification with the sphere of `G`.

## Main definitions and results

* `SymplecticGeometry.sphereCollapse`: the collapse map.
* `SymplecticGeometry.sphereCollapse_eq_iff`: it takes the value `r` exactly on the wedge.
* `SymplecticGeometry.sphereCollapseHomeomorph`: its restriction to the complement of the
  wedge, as a homeomorphism onto the complement of `r`
  (`SymplecticGeometry.coe_sphereCollapseHomeomorph_apply`).

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Chapter 0 (the smash
  product of spheres, `S^a ∧ S^b ≅ S^{a+b}`).
-/

public section

open Metric Module OnePoint Set TauCeti

namespace SymplecticGeometry

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G]

/-- The product of the inverse stereographic projections from `p` and `q`: an open embedding of
`(ℝ ∙ p)ᗮ × (ℝ ∙ q)ᗮ` onto the complement of the wedge `{p} × S^b ∪ S^a × {q}`. -/
noncomputable def sphereProdStereographicSymm (p : sphere (0 : E) 1) (q : sphere (0 : F) 1) :
    (ℝ ∙ (p : E))ᗮ × (ℝ ∙ (q : F))ᗮ → sphere (0 : E) 1 × sphere (0 : F) 1 :=
  Prod.map (stereographic (norm_eq_of_mem_sphere p)).symm
    (stereographic (norm_eq_of_mem_sphere q)).symm

theorem sphereProdStereographicSymm_def (p : sphere (0 : E) 1) (q : sphere (0 : F) 1) :
    sphereProdStereographicSymm p q = Prod.map (stereographic (norm_eq_of_mem_sphere p)).symm
      (stereographic (norm_eq_of_mem_sphere q)).symm :=
  (rfl)

theorem isOpenEmbedding_sphereProdStereographicSymm (p : sphere (0 : E) 1)
    (q : sphere (0 : F) 1) : Topology.IsOpenEmbedding (sphereProdStereographicSymm p q) := by
  rw [sphereProdStereographicSymm_def]
  exact (isOpenEmbedding_stereographic_symm _).prodMap (isOpenEmbedding_stereographic_symm _)

theorem range_sphereProdStereographicSymm (p : sphere (0 : E) 1) (q : sphere (0 : F) 1) :
    range (sphereProdStereographicSymm p q) = {p}ᶜ ×ˢ {q}ᶜ := by
  rw [sphereProdStereographicSymm_def, range_prodMap,
    range_stereographic_symm (norm_eq_of_mem_sphere p) p.property,
    range_stereographic_symm (norm_eq_of_mem_sphere q) q.property]

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [FiniteDimensional ℝ G]

/-- A continuous linear equivalence of `(ℝ ∙ p)ᗮ × (ℝ ∙ q)ᗮ` with `(ℝ ∙ r)ᗮ`, for unit vectors
`p`, `q`, `r` of finite-dimensional inner product spaces with
`finrank ℝ E + finrank ℝ F = finrank ℝ G + 1`. It is chosen, and used to build
`SymplecticGeometry.sphereCollapse`. -/
noncomputable def sphereCollapseEquiv (h : finrank ℝ E + finrank ℝ F = finrank ℝ G + 1)
    (p : sphere (0 : E) 1) (q : sphere (0 : F) 1) (r : sphere (0 : G) 1) :
    ((ℝ ∙ (p : E))ᗮ × (ℝ ∙ (q : F))ᗮ) ≃L[ℝ] (ℝ ∙ (r : G))ᗮ :=
  (FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq <| by
    have hE := (ℝ ∙ (p : E)).finrank_add_finrank_orthogonal
    have hF := (ℝ ∙ (q : F)).finrank_add_finrank_orthogonal
    have hG := (ℝ ∙ (r : G)).finrank_add_finrank_orthogonal
    rw [finrank_span_singleton (ne_zero_of_mem_unit_sphere _)] at hE hF hG
    rw [finrank_prod]
    omega).some

/-- The collapse map `S^a × S^b → S^{a+b}` of unit spheres, for base points `p`, `q`, `r`: it
sends the wedge `{p} × S^b ∪ S^a × {q}` to `r` and the complement of the wedge homeomorphically
onto the complement of `r`. -/
noncomputable def sphereCollapse (h : finrank ℝ E + finrank ℝ F = finrank ℝ G + 1)
    (p : sphere (0 : E) 1) (q : sphere (0 : F) 1) (r : sphere (0 : G) 1) :
    C(sphere (0 : E) 1 × sphere (0 : F) 1, sphere (0 : G) 1) where
  toFun z := onePointHyperplaneHomeoUnitSphere (norm_eq_of_mem_sphere r)
    (onePointCollapse (sphereProdStereographicSymm p q) (sphereCollapseEquiv h p q r) z)
  continuous_toFun := (onePointHyperplaneHomeoUnitSphere _).continuous.comp <|
    continuous_onePointCollapse (isOpenEmbedding_sphereProdStereographicSymm p q)
      (sphereCollapseEquiv h p q r).toHomeomorph.isProperMap

variable (h : finrank ℝ E + finrank ℝ F = finrank ℝ G + 1)
  (p : sphere (0 : E) 1) (q : sphere (0 : F) 1) (r : sphere (0 : G) 1)

theorem sphereCollapse_def (z : sphere (0 : E) 1 × sphere (0 : F) 1) :
    sphereCollapse h p q r z = onePointHyperplaneHomeoUnitSphere (norm_eq_of_mem_sphere r)
      (onePointCollapse (sphereProdStereographicSymm p q) (sphereCollapseEquiv h p q r) z) :=
  (rfl)

/-- On the complement of the wedge, parametrized by the inverse stereographic projections from
`p` and `q`, the collapse map is `sphereCollapseEquiv` followed by the inverse stereographic
projection from `r`. -/
@[simp]
theorem sphereCollapse_sphereProdStereographicSymm (w : (ℝ ∙ (p : E))ᗮ × (ℝ ∙ (q : F))ᗮ) :
    sphereCollapse h p q r (sphereProdStereographicSymm p q w) =
      (stereographic (norm_eq_of_mem_sphere r)).symm (sphereCollapseEquiv h p q r w) := by
  rw [sphereCollapse_def,
    onePointCollapse_apply (isOpenEmbedding_sphereProdStereographicSymm p q).injective,
    onePointHyperplaneHomeoUnitSphere_apply_coe]

/-- Off the wedge, the collapse map is stereographic projection of each factor, followed by
`sphereCollapseEquiv` and the inverse stereographic projection from `r`. -/
theorem sphereCollapse_apply_of_ne {x : sphere (0 : E) 1} {y : sphere (0 : F) 1} (hx : x ≠ p)
    (hy : y ≠ q) :
    sphereCollapse h p q r (x, y) = (stereographic (norm_eq_of_mem_sphere r)).symm
      (sphereCollapseEquiv h p q r
        (stereographic (norm_eq_of_mem_sphere p) x,
          stereographic (norm_eq_of_mem_sphere q) y)) := by
  rw [← sphereCollapse_sphereProdStereographicSymm, sphereProdStereographicSymm_def,
    Prod.map_apply, (stereographic _).left_inv (by simpa using hx),
    (stereographic _).left_inv (by simpa using hy)]

/-- The collapse map takes the value `r` exactly on the wedge `{p} × S^b ∪ S^a × {q}`. -/
theorem sphereCollapse_eq_iff {z : sphere (0 : E) 1 × sphere (0 : F) 1} :
    sphereCollapse h p q r z = r ↔ z.1 = p ∨ z.2 = q := by
  have hr : (onePointHyperplaneHomeoUnitSphere (norm_eq_of_mem_sphere r)).symm r = ∞ :=
    Homeomorph.symm_apply_eq _ |>.2
      (Subtype.ext (TauCeti.coe_onePointHyperplaneHomeoUnitSphere_infty _)).symm
  rw [sphereCollapse_def, ← Homeomorph.eq_symm_apply, hr,
    onePointCollapse_eq_infty_iff (isOpenEmbedding_sphereProdStereographicSymm p q).injective,
    range_sphereProdStereographicSymm, mem_prod, not_and_or, mem_compl_singleton_iff,
    mem_compl_singleton_iff, not_not, not_not]

@[simp]
theorem sphereCollapse_apply_left (y : sphere (0 : F) 1) : sphereCollapse h p q r (p, y) = r :=
  (sphereCollapse_eq_iff h p q r).2 (.inl rfl)

@[simp]
theorem sphereCollapse_apply_right (x : sphere (0 : E) 1) : sphereCollapse h p q r (x, q) = r :=
  (sphereCollapse_eq_iff h p q r).2 (.inr rfl)

/-- The restriction of the collapse map to the complement `{p}ᶜ ×ˢ {q}ᶜ` of the wedge, as a
homeomorphism onto the complement of `r`. -/
noncomputable def sphereCollapseHomeomorph :
    (({p}ᶜ ×ˢ {q}ᶜ : Set (sphere (0 : E) 1 × sphere (0 : F) 1))) ≃ₜ
      ({r}ᶜ : Set (sphere (0 : G) 1)) :=
  (Homeomorph.Set.prod _ _).trans <|
    ((stereographicHomeomorph p).prodCongr (stereographicHomeomorph q)).trans <|
      (sphereCollapseEquiv h p q r).toHomeomorph.trans (stereographicHomeomorph r).symm

@[simp]
theorem coe_sphereCollapseHomeomorph_apply
    (z : ({p}ᶜ ×ˢ {q}ᶜ : Set (sphere (0 : E) 1 × sphere (0 : F) 1))) :
    (sphereCollapseHomeomorph h p q r z : sphere (0 : G) 1) = sphereCollapse h p q r z := by
  obtain ⟨⟨x, y⟩, hxy⟩ := z
  rw [sphereCollapse_apply_of_ne h p q r hxy.1 hxy.2]
  simp only [sphereCollapseHomeomorph, Homeomorph.trans_apply]
  -- `Homeomorph.Set.prod_apply` is stated for the unfolded subtype, which `simp` does not match
  have hz : Homeomorph.Set.prod ({p}ᶜ : Set (sphere (0 : E) 1)) {q}ᶜ ⟨(x, y), hxy⟩ =
      (⟨x, hxy.1⟩, ⟨y, hxy.2⟩) :=
    Homeomorph.Set.prod_apply _ _ _
  rw [hz]
  simp

end SymplecticGeometry

end
