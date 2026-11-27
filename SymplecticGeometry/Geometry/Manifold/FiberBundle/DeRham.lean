/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.FiberBundle.MapFiber
public import TauCeti.Geometry.Manifold.DeRham.Map
public import SymplecticGeometry.Geometry.Manifold.DeRham.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
import Mathlib.Geometry.Manifold.Instances.Icc
import SymplecticGeometry.Geometry.Manifold.DeRham.Map
import TauCeti.Geometry.Manifold.ContMDiff.Curve
import TauCeti.Geometry.Manifold.DeRham.HomotopyInvariance

/-!
# Fibre inclusions in de Rham cohomology

Let `e` be a trivialization of a map `proj : M → B` with model fibre `F`, whose inverse is smooth.
Its fibre inclusions `v ↦ e⁻¹ (b, v)` are smooth maps `F → M`, so they induce maps on de Rham
cohomology. This file compares these maps for different points and different charts: over nearby
points of the base set of `e` they agree, and two charts whose coordinate change over a point
preserves a closed form `σ` on `F` send a class to the class of `σ` together. These are the
cohomological counterparts of the pull-back identities of
`SymplecticGeometry/Geometry/Manifold/FiberBundle/RestrictsTo.lean`.

## Main results

* `Bundle.Trivialization.eventually_map_fiberInclusionMap_eq`: the fibre inclusions of a smooth
  trivialization over nearby points of its base set induce the same map on cohomology, since
  they are homotopic along a short smooth curve in the base set
  (`TauCeti.eventually_exists_contMDiff_curve`, `TauCeti.deRhamCohomology.map_eq_of_homotopy`).
* `Bundle.Trivialization.map_fiberInclusionMap_eq_comp`: over a point of two base sets, the map
  induced by the fibre inclusion of one chart factors through that of the other chart and the
  map induced by their coordinate change.
* `Bundle.Trivialization.map_fiberInclusionMap_eq_of_mem_diffeomorphStabilizer`: the fibre
  inclusions of two charts over a point, whose coordinate change preserves `σ`, send a class to
  the class of `σ` together.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §6.1 (proof of Theorem 6.1.4).
-/

public section

open Bundle Set Topology TauCeti
open scoped Manifold ContDiff

namespace Bundle.Trivialization

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] {HB : Type*}
  [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {B : Type*} [TopologicalSpace B]
  [ChartedSpace HB B]
  {EF : Type*} [NormedAddCommGroup EF] [NormedSpace ℝ EF] {HF : Type*} [TopologicalSpace HF]
  {IF : ModelWithCorners ℝ EF HF} {F : Type*} [TopologicalSpace F] [ChartedSpace HF F]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners ℝ EM HM} {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  [IsManifold IM 2 M]
  {proj : M → B} {k : ℕ}

/-- **Fibre inclusions over nearby points.** Let `e` be a trivialization of `proj` with smooth
inverse, over a smooth base. For every `b'` close enough to a point `b` of the base set of `e`,
the fibre inclusions of `e` over `b` and over `b'` induce the same map on de Rham cohomology:
they are smoothly homotopic through the fibre inclusions over a smooth curve from `b` to `b'` in
the base set. -/
theorem eventually_map_fiberInclusionMap_eq [IsManifold IB ∞ B] [IsManifold IF ∞ F]
    {e : Trivialization F proj}
    (he : ContMDiffOn (IB.prod IF) IM ∞ e.toOpenPartialHomeomorph.symm e.target) {b : B}
    (hb : b ∈ e.baseSet) (k : ℕ) :
    ∀ᶠ b' in 𝓝 b, ∃ hb' : b' ∈ e.baseSet,
      deRhamCohomology.map (e.fiberInclusionMap hb') (e.contMDiff_fiberInclusionMap he hb') k =
        deRhamCohomology.map (e.fiberInclusionMap hb) (e.contMDiff_fiberInclusionMap he hb) k := by
  filter_upwards [eventually_exists_contMDiff_curve (I := IB) (n := ⊤)
    (e.open_baseSet.mem_nhds hb)] with b' ⟨γ, hγ, h₀, h₁, hγe⟩
  refine ⟨h₁ 1 le_rfl ▸ hγe 1, ?_⟩
  refine (deRhamCohomology.map_eq_of_homotopy _ _
    (F := fun q : F × Icc (0 : ℝ) 1 ↦ e.toOpenPartialHomeomorph.symm (γ q.2, q.1))
    (he.comp_contMDiff (((hγ.comp contMDiff_subtypeVal_Icc).comp contMDiff_snd).prodMk
      contMDiff_fst) fun q ↦ e.mem_target.2 (hγe _)) (fun v ↦ ?_) (fun v ↦ ?_) k).symm
  · simp [h₀ 0 le_rfl, fiberInclusionMap_apply]
  · simp [h₁ 1 le_rfl, fiberInclusionMap_apply]

/-- **Fibre inclusions through two charts in cohomology.** Let `e` and `e'` be trivializations
of `proj` with smooth inverses, and `φ` a diffeomorphism of the fibre that is their coordinate
change over `b`. The map on de Rham cohomology induced by the fibre inclusion of `e` over `b` is
that of the fibre inclusion of `e'` over `b` followed by the map that `φ` induces. -/
theorem map_fiberInclusionMap_eq_comp [IsManifold IF 2 F] {e e' : Trivialization F proj}
    (he : ContMDiffOn (IB.prod IF) IM ∞ e.toOpenPartialHomeomorph.symm e.target)
    (he' : ContMDiffOn (IB.prod IF) IM ∞ e'.toOpenPartialHomeomorph.symm e'.target) {b : B}
    (hb : b ∈ e.baseSet) (hb' : b ∈ e'.baseSet) {φ : F ≃ₘ⟮IF, IF⟯ F}
    (hφe : ⇑φ = e.coordChange e' b) (k : ℕ) :
    deRhamCohomology.map (e.fiberInclusionMap hb) (e.contMDiff_fiberInclusionMap he hb) k =
      deRhamCohomology.map φ φ.contMDiff k ∘ₗ
        deRhamCohomology.map (e'.fiberInclusionMap hb') (e'.contMDiff_fiberInclusionMap he' hb')
          k := by
  rw [← deRhamCohomology.map_comp]
  congr 1
  rw [hφe]
  exact funext fun v ↦ (e.fiberInclusionMap_coordChange e' hb hb' v).symm

/-- **Charts related by a stabilizing coordinate change, in cohomology.** Let `e` and `e'` be
trivializations of `proj` with smooth inverses, whose coordinate change over `b` is a
diffeomorphism `φ` of the fibre that preserves a closed form `σ`. If the fibre inclusion of `e'`
over `b` sends a class `a` to the class of `σ`, so does that of `e`. -/
theorem map_fiberInclusionMap_eq_of_mem_diffeomorphStabilizer [IsManifold IF 2 F]
    {e e' : Trivialization F proj}
    (he : ContMDiffOn (IB.prod IF) IM ∞ e.toOpenPartialHomeomorph.symm e.target)
    (he' : ContMDiffOn (IB.prod IF) IM ∞ e'.toOpenPartialHomeomorph.symm e'.target) {b : B}
    (hb : b ∈ e.baseSet) (hb' : b ∈ e'.baseSet) {σ : SmoothForm IF F ℝ k} (hσ : σ.IsClosed)
    {φ : F ≃ₘ⟮IF, IF⟯ F} (hφ : φ ∈ SmoothForm.diffeomorphStabilizer σ)
    (hφe : ⇑φ = e.coordChange e' b) {a : deRhamCohomology IM M k}
    (h : deRhamCohomology.map (e'.fiberInclusionMap hb') (e'.contMDiff_fiberInclusionMap he' hb')
        k a = deRhamCohomology.mk IF k ⟨σ, hσ.mem_closedForms⟩) :
    deRhamCohomology.map (e.fiberInclusionMap hb) (e.contMDiff_fiberInclusionMap he hb) k a =
      deRhamCohomology.mk IF k ⟨σ, hσ.mem_closedForms⟩ := by
  rw [map_fiberInclusionMap_eq_comp he he' hb hb' hφe, LinearMap.comp_apply, h]
  exact deRhamCohomology.map_mk_of_mem_diffeomorphStabilizer hφ

end Bundle.Trivialization

end
