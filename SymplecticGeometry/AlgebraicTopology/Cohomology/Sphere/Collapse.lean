/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Sphere.Stereographic
public import TauCeti.Topology.Compactification.OnePoint.Collapse
public import SymplecticGeometry.Topology.Compactification.OnePoint.Sphere
public import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.Degree
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Prod
public import TauCeti.Geometry.Manifold.Instances.TopCatSphere
public import SymplecticGeometry.AlgebraicTopology.Cohomology.Sphere.Generator

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
* `SymplecticGeometry.isLocalHomeomorphOn_sphereCollapse`,
  `SymplecticGeometry.preimage_sphereCollapse_singleton`: off the wedge the collapse map is a
  local homeomorphism, and each point there is the only point of its fibre.
* `SymplecticGeometry.exists_singularHomologyMap_sphereCollapse_singularHomologyCross_eq_zsmul`:
  in integral homology of degree `a + b`, the collapse map sends the cross product `γ_a × γ_b`
  of the standard generators of the homology of the spheres to `±γ_{a+b}`.
* `SymplecticGeometry.exists_singularCohomologyMap_sphereCollapse_eq_smul_singularCup` and
  `SymplecticGeometry.exists_singularCohomologyMap_sphereCollapse_eq_smul_integralCup`: in
  cohomology of degree `a + b` with coefficients `ℤ`, and in integral cohomology, there is one
  sign `ε = ±1` such that the collapse map pulls each class `u` back to
  `(ε * ⟨u, γ_{a+b}⟩) • (pr₁^* θ_a ⌣ pr₂^* θ_b)`, with `θ_a`, `θ_b` the dual generators of the
  top cohomology of the spheres.

The last three results are read on Tau Ceti's spheres `TopCat.sphere`. For the first, the cross
product is a fundamental class
(`TauCeti.IsFundamentalClass.singularHomologyTopCatSphereGenerator_singularHomologyCross`), and
so is `γ_{a+b}`. A point off the wedge has a one-point fibre at which the map is a local
homeomorphism, so `TauCeti.IsFundamentalClass.map_eq_or_eq_neg_of_isLocalHomeomorphOn_unit`
gives the sign. For the other two, a class `x` of degree `a + b` on `S^a × S^b` is
`⟨x, γ_a × γ_b⟩ • (pr₁^* θ_a ⌣ pr₂^* θ_b)`
(`TopCat.eq_singularKronecker_smul_singularCup_sphereGenerator`), and for `x = κ^* u` the
naturality of the Kronecker pairing gives `⟨κ^* u, γ_a × γ_b⟩ = ⟨u, κ_*(γ_a × γ_b)⟩ =
ε * ⟨u, γ_{a+b}⟩`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Chapter 0 (the smash
  product of spheres, `S^a ∧ S^b ≅ S^{a+b}`), and Section 3.3 (fundamental classes and the
  local degree).
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

/-- Off the wedge `{p} × S^b ∪ S^a × {q}`, the collapse map is a local homeomorphism. -/
theorem isLocalHomeomorphOn_sphereCollapse :
    IsLocalHomeomorphOn (sphereCollapse h p q r) ({p}ᶜ ×ˢ {q}ᶜ) := by
  have hU : IsOpen ({p}ᶜ ×ˢ {q}ᶜ : Set (sphere (0 : E) 1 × sphere (0 : F) 1)) :=
    isOpen_compl_singleton.prod isOpen_compl_singleton
  refine (isLocalHomeomorphOn_iff_isOpenEmbedding_restrict _).2 fun z hz ↦
    ⟨_, hU.mem_nhds hz, ?_⟩
  have : ({p}ᶜ ×ˢ {q}ᶜ : Set (sphere (0 : E) 1 × sphere (0 : F) 1)).domRestrict
      (sphereCollapse h p q r) = Subtype.val ∘ sphereCollapseHomeomorph h p q r :=
    funext fun z ↦ (coe_sphereCollapseHomeomorph_apply h p q r z).symm
  rw [this]
  exact isOpen_compl_singleton.isOpenEmbedding_subtypeVal.comp
    (sphereCollapseHomeomorph h p q r).isOpenEmbedding

/-- A point `z` off the wedge is the only point that the collapse map sends to its image. -/
theorem preimage_sphereCollapse_singleton {z : sphere (0 : E) 1 × sphere (0 : F) 1}
    (hz : z ∈ ({p}ᶜ ×ˢ {q}ᶜ : Set (sphere (0 : E) 1 × sphere (0 : F) 1))) :
    sphereCollapse h p q r ⁻¹' {sphereCollapse h p q r z} = {z} := by
  refine Set.eq_singleton_iff_unique_mem.2 ⟨rfl, fun w hw ↦ ?_⟩
  rw [Set.mem_preimage, Set.mem_singleton_iff, sphereCollapse_def, sphereCollapse_def,
    EmbeddingLike.apply_eq_iff_eq,
    onePointCollapse_eq_onePointCollapse_iff
      (isOpenEmbedding_sphereProdStereographicSymm p q).injective
      (sphereCollapseEquiv h p q r).injective, range_sphereProdStereographicSymm] at hw
  exact hw.resolve_right fun h ↦ h.2 hz

section Homology

open CategoryTheory MonoidalCategory AlgebraicTopology

variable {d e : ℕ} (hE : finrank ℝ E = d + 1 + 1) (hF : finrank ℝ F = e + 1 + 1)

/-- **The collapse map has degree `±1`.** Let `a = d + 1` and `b = e + 1`, and read the collapse
map `S^a × S^b → S^{a+b}` on Tau Ceti's spheres `TopCat.sphere` through
`TauCeti.sphereHomeomorphTopCatSphere`. In integral homology of degree `a + b` it sends the cross
product `γ_a × γ_b` of the standard generators `TauCeti.singularHomologyTopCatSphereGenerator`,
read with coefficients `ℤ` through the unitor `ℤ ⊗ ℤ ≅ ℤ`, to `ε • γ_{a+b}` with `ε = ±1`. -/
theorem exists_singularHomologyMap_sphereCollapse_singularHomologyCross_eq_zsmul :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      (((singularHomologyFunctor (ModuleCat.{0} ℤ) (d + 1 + (e + 1))).obj
          (𝟙_ (ModuleCat.{0} ℤ))).map (TopCat.ofHom
            (((sphereHomeomorphTopCatSphere (by omega) :
                  sphere (0 : G) 1 ≃ₜ TopCat.sphere.{0} (d + 1 + e + 1)) :
                C(sphere (0 : G) 1, TopCat.sphere.{0} (d + 1 + e + 1))).comp
              ((sphereCollapse h p q r).comp
                (((sphereHomeomorphTopCatSphere hE).symm.prodCongr
                  (sphereHomeomorphTopCatSphere hF).symm :
                    TopCat.sphere.{0} (d + 1) × TopCat.sphere.{0} (e + 1) ≃ₜ _) :
                  C(TopCat.sphere.{0} (d + 1) × TopCat.sphere.{0} (e + 1),
                    sphere (0 : E) 1 × sphere (0 : F) 1)))))).hom
        (((singularHomologyFunctor (ModuleCat.{0} ℤ) (d + 1 + (e + 1))).map
            (λ_ (𝟙_ (ModuleCat.{0} ℤ))).hom).app
          (TopCat.sphere.{0} (d + 1) ⊗ TopCat.sphere.{0} (e + 1))
          ((TopCat.singularHomologyCross _ _ (𝟙_ (ModuleCat.{0} ℤ)) (𝟙_ (ModuleCat.{0} ℤ))
            (d + 1) (e + 1) (d + 1 + (e + 1)) rfl).hom
            (singularHomologyTopCatSphereGenerator ℤ d ⊗ₜ
              singularHomologyTopCatSphereGenerator ℤ e))) =
        ε • singularHomologyTopCatSphereGenerator ℤ (d + 1 + e) := by
  set Ψ : TopCat.sphere.{0} (d + 1) × TopCat.sphere.{0} (e + 1) ≃ₜ
      sphere (0 : E) 1 × sphere (0 : F) 1 :=
    (sphereHomeomorphTopCatSphere hE).symm.prodCongr (sphereHomeomorphTopCatSphere hF).symm
  set Φ : sphere (0 : G) 1 ≃ₜ TopCat.sphere.{0} (d + 1 + e + 1) :=
    sphereHomeomorphTopCatSphere (by omega)
  set f : C(TopCat.sphere.{0} (d + 1) × TopCat.sphere.{0} (e + 1),
      TopCat.sphere.{0} (d + 1 + e + 1)) :=
    (Φ : C(sphere (0 : G) 1, TopCat.sphere.{0} (d + 1 + e + 1))).comp
      ((sphereCollapse h p q r).comp (Ψ : C(_, sphere (0 : E) 1 × sphere (0 : F) 1)))
  set μ := ((singularHomologyFunctor (ModuleCat.{0} ℤ) (d + 1 + (e + 1))).map
      (λ_ (𝟙_ (ModuleCat.{0} ℤ))).hom).app
    (TopCat.sphere.{0} (d + 1) ⊗ TopCat.sphere.{0} (e + 1))
    ((TopCat.singularHomologyCross _ _ (𝟙_ (ModuleCat.{0} ℤ)) (𝟙_ (ModuleCat.{0} ℤ))
      (d + 1) (e + 1) (d + 1 + (e + 1)) rfl).hom
      (singularHomologyTopCatSphereGenerator ℤ d ⊗ₜ singularHomologyTopCatSphereGenerator ℤ e))
  have hμ : IsFundamentalClass (M := TopCat.sphere.{0} (d + 1) × TopCat.sphere.{0} (e + 1)) μ :=
    (isFundamentalClass_singularHomologyFunctor_map_app_iff _ _).2
    (IsFundamentalClass.singularHomologyTopCatSphereGenerator_singularHomologyCross
      (N := TopCat.sphere.{0} (e + 1)) (F := ULift.{0} (Fin (e + 1)) → ℝ) (by simp)
      (isFundamentalClass_singularHomologyTopCatSphereGenerator ℤ e))
  -- `f` is a local homeomorphism near a point off the wedge, the only point of its fibre.
  set x := Ψ.symm (-p, -q)
  have hx : Ψ x ∈ ({p}ᶜ ×ˢ {q}ᶜ : Set (sphere (0 : E) 1 × sphere (0 : F) 1)) := by
    simp only [x, Homeomorph.apply_symm_apply]
    exact ⟨fun h ↦ ne_neg_of_mem_unit_sphere ℝ p h.symm,
      fun h ↦ ne_neg_of_mem_unit_sphere ℝ q h.symm⟩
  have hf : (f : _ → _) = Φ ∘ (sphereCollapse h p q r ∘ Ψ) := by
    simp only [ContinuousMap.coe_comp, ContinuousMap.coe_mk, f]
  have hfib : f ⁻¹' {f x} = {x} := by
    ext y
    refine ⟨fun hy ↦ Ψ.injective ?_, fun hy ↦ hy ▸ Set.mem_singleton _⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff, hf, Function.comp_apply,
      Φ.injective.eq_iff] at hy
    rw [← Set.mem_singleton_iff, ← Set.mem_preimage,
      preimage_sphereCollapse_singleton h p q r hx] at hy
    exact Set.mem_singleton_iff.1 hy
  have hs : IsLocalHomeomorphOn f (Ψ ⁻¹' ({p}ᶜ ×ˢ {q}ᶜ)) := by
    rw [hf]
    exact Φ.isLocalHomeomorph.isLocalHomeomorphOn.comp
      ((isLocalHomeomorphOn_sphereCollapse h p q r).comp
        (Ψ.isLocalHomeomorph.isLocalHomeomorphOn.mono (Set.subset_univ _)) fun _ hy ↦ hy)
      (Set.mapsTo_univ _ _)
  let : ChartedSpace ((ULift.{0} (Fin (d + 1)) → ℝ) × (ULift.{0} (Fin (e + 1)) → ℝ))
      (TopCat.sphere.{0} (d + 1) × TopCat.sphere.{0} (e + 1)) :=
    prodChartedSpace _ _ _ _
  -- Stated on `TopCat.of`, so that unification does not unfold `TopCat.sphere` and pick a
  -- topology other than the instance on it.
  set ν : ((TopCat.toSSet.obj (TopCat.of (TopCat.sphere.{0} (d + 1 + e + 1)))).homology
      (ModuleCat.of ℤ ℤ) (d + 1 + (e + 1)) : ModuleCat.{0} ℤ) :=
    singularHomologyTopCatSphereGenerator ℤ (d + 1 + e)
  have hν : IsFundamentalClass ν :=
    isFundamentalClass_singularHomologyTopCatSphereGenerator ℤ (d + 1 + e)
  rcases hμ.map_eq_or_eq_neg_of_isLocalHomeomorphOn_unit
      (E := (ULift.{0} (Fin (d + 1)) → ℝ) × (ULift.{0} (Fin (e + 1)) → ℝ))
      (F := ULift.{0} (Fin (d + 1 + e + 1)) → ℝ) (by simp) (by simp; omega) hν hfib hs hx
    with hf' | hf'
  · exact ⟨1, .inl rfl, hf'.trans (one_zsmul _).symm⟩
  · exact ⟨-1, .inr rfl, hf'.trans (neg_one_zsmul _).symm⟩

section SingularCohomology

/- Cohomology with coefficients `ℤ` is taken here with the `ℤ`-linear structure
`ModuleCat.instLinear` of `ModuleCat ℤ`, the one with which Tau Ceti states its sphere generators
and its cup products over a commutative ring, rather than the structure
`Linear.preadditiveIntLinear` of a preadditive category. -/
attribute [local instance high] ModuleCat.instLinear

/-- **The collapse map in cohomology.** Let `a = d + 1` and `b = e + 1`, and read the collapse
map `κ : S^a × S^b → S^{a+b}` on Tau Ceti's spheres `TopCat.sphere` through
`TauCeti.sphereHomeomorphTopCatSphere`. There is a sign `ε = ±1` such that every class
`u ∈ H^{a+b}(S^{a+b}; ℤ)` pulls back to `κ^* u = (ε * ⟨u, γ_{a+b}⟩) • (pr₁^* θ_a ⌣ pr₂^* θ_b)`,
where `⟨u, γ_{a+b}⟩` is the evaluation `TauCeti.singularCohomologyTopCatSphereEquiv` of `u` on
the standard generator and `θ_a`, `θ_b` are the dual generators
`TauCeti.singularCohomologyTopCatSphereGenerator`. -/
theorem exists_singularCohomologyMap_sphereCollapse_eq_smul_singularCup :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      ∀ u : (TopCat.sphere.{0} (d + 1 + e + 1)).singularCohomology (𝟙_ (ModuleCat.{0} ℤ)) ℤ
        (𝟙_ (ModuleCat.{0} ℤ)) (d + 1 + (e + 1)),
      TopCat.singularCohomologyMap (TopCat.ofHom
            (X := ↑(TopCat.sphere.{0} (d + 1) ⊗ TopCat.sphere.{0} (e + 1)))
            (Y := ↑(TopCat.sphere.{0} (d + 1 + e + 1)))
            (((sphereHomeomorphTopCatSphere (by omega) :
                  sphere (0 : G) 1 ≃ₜ TopCat.sphere.{0} (d + 1 + e + 1)) :
                C(sphere (0 : G) 1, TopCat.sphere.{0} (d + 1 + e + 1))).comp
              ((sphereCollapse h p q r).comp
                (((sphereHomeomorphTopCatSphere hE).symm.prodCongr
                  (sphereHomeomorphTopCatSphere hF).symm :
                    TopCat.sphere.{0} (d + 1) × TopCat.sphere.{0} (e + 1) ≃ₜ _) :
                  C(TopCat.sphere.{0} (d + 1) × TopCat.sphere.{0} (e + 1),
                    sphere (0 : E) 1 × sphere (0 : F) 1)))))
          (d + 1 + (e + 1)) u =
        (ε * singularCohomologyTopCatSphereEquiv ℤ (𝟙_ (ModuleCat.{0} ℤ)) (d + 1 + e) u) •
          (TopCat.sphere.{0} (d + 1) ⊗ TopCat.sphere.{0} (e + 1)).singularCup ℤ (λ_ _).inv
            (λ_ _).hom (d + 1) (e + 1) (d + 1 + (e + 1)) rfl
            (TopCat.singularCohomologyMap (CartesianMonoidalCategory.fst _ _) (d + 1)
              (singularCohomologyTopCatSphereGenerator ℤ d))
            (TopCat.singularCohomologyMap (CartesianMonoidalCategory.snd _ _) (e + 1)
              (singularCohomologyTopCatSphereGenerator ℤ e)) := by
  obtain ⟨ε, hε, hγ⟩ :=
    exists_singularHomologyMap_sphereCollapse_singularHomologyCross_eq_zsmul h p q r hE hF
  refine ⟨ε, hε, fun u ↦ ?_⟩
  rw [TopCat.eq_singularKronecker_smul_singularCup_sphereGenerator ℤ rfl
    (TopCat.singularCohomologyMap _ _ u)]
  -- `(ε * _) • _` is the action of `ℤ` on an additive group here, and the module action over
  -- `ℤ` in `eq_singularKronecker_smul_singularCup_sphereGenerator`.
  rw [← Int.cast_smul_eq_zsmul ℤ, Int.cast_id]
  congr 1
  rw [TopCat.singularKronecker_naturality, ConcreteCategory.comp_apply]
  -- `hγ` reads the map with source the product type rather than the monoidal product.
  refine (congrArg ((TopCat.sphere.{0} (d + 1 + e + 1)).singularKronecker ℤ _ u).hom hγ).trans ?_
  rw [map_zsmul, singularCohomologyTopCatSphereEquiv_apply, smul_eq_mul]
  -- The two sides differ only in writing the degree as `d + 1 + (e + 1)` or `d + 1 + e + 1`.
  rfl

end SingularCohomology

/-- **The collapse map in integral cohomology.** Let `a = d + 1` and `b = e + 1`, and read the
collapse map `κ : S^a × S^b → S^{a+b}` on Tau Ceti's spheres `TopCat.sphere` through
`TauCeti.sphereHomeomorphTopCatSphere`. There is a sign `ε = ±1` such that every class
`u ∈ H^{a+b}(S^{a+b}; ℤ)` of the integral cohomology `TopCat.integralCohomology` pulls back to
`κ^* u = (ε * ⟨u, γ_{a+b}⟩) • (pr₁^* θ_a ⌣ pr₂^* θ_b)`, the cup product being
`TopCat.integralCup`. Here `⟨u, γ_{a+b}⟩` is the evaluation
`TauCeti.singularCohomologyTopCatSphereEquiv` of `u` on the standard generator, and `θ_a`, `θ_b`
are the dual generators `TauCeti.singularCohomologyTopCatSphereGenerator`, both read in integral
cohomology through `TopCat.integralCohomologyEquiv`. -/
theorem exists_singularCohomologyMap_sphereCollapse_eq_smul_integralCup :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      ∀ u : (TopCat.sphere.{0} (d + 1 + e + 1)).integralCohomology (d + 1 + (e + 1)),
      TopCat.singularCohomologyMap (TopCat.ofHom
            (X := ↑(TopCat.sphere.{0} (d + 1) ⊗ TopCat.sphere.{0} (e + 1)))
            (Y := ↑(TopCat.sphere.{0} (d + 1 + e + 1)))
            (((sphereHomeomorphTopCatSphere (by omega) :
                  sphere (0 : G) 1 ≃ₜ TopCat.sphere.{0} (d + 1 + e + 1)) :
                C(sphere (0 : G) 1, TopCat.sphere.{0} (d + 1 + e + 1))).comp
              ((sphereCollapse h p q r).comp
                (((sphereHomeomorphTopCatSphere hE).symm.prodCongr
                  (sphereHomeomorphTopCatSphere hF).symm :
                    TopCat.sphere.{0} (d + 1) × TopCat.sphere.{0} (e + 1) ≃ₜ _) :
                  C(TopCat.sphere.{0} (d + 1) × TopCat.sphere.{0} (e + 1),
                    sphere (0 : E) 1 × sphere (0 : F) 1)))))
          (d + 1 + (e + 1)) u =
        (ε * singularCohomologyTopCatSphereEquiv ℤ (𝟙_ (ModuleCat.{0} ℤ)) (d + 1 + e)
            ((TopCat.sphere.{0} (d + 1 + e + 1)).integralCohomologyEquiv (d + 1 + (e + 1)) u)) •
          (TopCat.sphere.{0} (d + 1) ⊗ TopCat.sphere.{0} (e + 1)).integralCup (d + 1) (e + 1)
            (d + 1 + (e + 1)) rfl
            (TopCat.singularCohomologyMap (CartesianMonoidalCategory.fst _ _) (d + 1)
              (((TopCat.sphere.{0} (d + 1)).integralCohomologyEquiv (d + 1)).symm
                (singularCohomologyTopCatSphereGenerator ℤ d)))
            (TopCat.singularCohomologyMap (CartesianMonoidalCategory.snd _ _) (e + 1)
              (((TopCat.sphere.{0} (e + 1)).integralCohomologyEquiv (e + 1)).symm
                (singularCohomologyTopCatSphereGenerator ℤ e))) := by
  obtain ⟨ε, hε, hu⟩ :=
    exists_singularCohomologyMap_sphereCollapse_eq_smul_singularCup h p q r hE hF
  refine ⟨ε, hε, fun u ↦ ?_⟩
  obtain ⟨v, rfl⟩ := ((TopCat.sphere.{0} (d + 1 + e + 1)).integralCohomologyEquiv
    (d + 1 + (e + 1))).symm.surjective u
  rw [LinearEquiv.apply_symm_apply, ← TopCat.integralCohomologyEquiv_symm_naturality, hu,
    map_zsmul, TopCat.integralCohomologyEquiv_symm_singularCup,
    TopCat.integralCohomologyEquiv_symm_naturality, TopCat.integralCohomologyEquiv_symm_naturality]

end Homology

end SymplecticGeometry

end
