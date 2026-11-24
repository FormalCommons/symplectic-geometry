/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.Reduction.ZeroLevel.Basic
public import SymplecticGeometry.Geometry.Manifold.Foliation.Orbit
public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap.Level
public import TauCeti.Geometry.Symplectic.Lagrangian.Manifold
public import TauCeti.Geometry.Symplectic.Lagrangian.Presymplectic
import SymplecticGeometry.Geometry.Manifold.Foliation.Constancy

/-!
# The zero level of a moment map: coisotropy and characteristic leaves

Let a Lie group `G` act smoothly on a Hausdorff manifold `(M, σ)` with nondegenerate `σ` and
coadjoint-equivariant moment map `μ : M → 𝔤*`, freely at the points of `Z = μ⁻¹(0)`. With the
atlases of `ZeroLevel/Basic.lean`, this file describes the form `i^* σ` that `σ` induces on `Z`
through the inclusion `i : Z → M`.

* `isCoisotropicMap_coe_zeroLevel`: the inclusion `i` is a coisotropic map. Its tangent images
  are the kernels `ker dμ_z` (`range_mfderiv_coe_zeroLevel`), and `ker dμ_z` is coisotropic since
  `0` is fixed by the coadjoint action (Tau Ceti's `IsMomentMap.isCoisotropic_ker_differential_iff`
  with `lieAnnihilator_zero`). No dimension count is needed, and an empty level is no special case.
* `ker_bilinFormAt_mpullback_coe_zeroLevel`: if `G` also acts properly on `Z`, the kernel of
  `(i^* σ)_z` is the kernel of the differential of the orbit projection `π : Z → Z / G` at `z`:
  the null directions of the level are its orbit directions. This combines Tau Ceti's
  `IsMomentMap.ker_bilinFormAt_mpullback` at `c = 0` with
  `ker_mfderiv_quotientMk_zeroLevel_eq_comap_map_lieAnnihilator`.
* `fundamentalVectorField_mem_distribution_characteristicFoliation_zeroLevel`: if `σ` is
  symplectic, the fundamental vector fields of the action on `Z` are tangent to the
  characteristic foliation of `i`. The inclusion sends them into the orbit directions of `M`, and
  at a point of `Z` these are the null directions of `i^* σ` (Tau Ceti's
  `IsMomentMap.ker_bilinFormAt_mpullback` at `c = 0`); no properness is needed.
* `mulInvariantExp_smul_mem_leaf_characteristicFoliation_zeroLevel` and
  `orbit_subset_leaf_characteristicFoliation_zeroLevel`: for `ξ` in the Lie algebra of `G` and `z`
  in `Z`, the point `exp ξ • z` lies on the leaf through `z` of the characteristic foliation of
  `i`, and for connected `G` so does the whole orbit of `z`. These are
  `TauCeti.Foliation.mulInvariantExp_smul_mem_leaf` and `TauCeti.Foliation.orbit_subset_leaf`
  of `Foliation/Orbit.lean`, applied with the previous item.
* `leaf_characteristicFoliation_zeroLevel_subset_orbit` and
  `leaf_characteristicFoliation_zeroLevel`: if `G` also acts properly on `Z`, each characteristic
  leaf of `i` lies in an orbit, and for connected `G` the leaf through `z` is the orbit of `z`. By
  `ker_bilinFormAt_mpullback_coe_zeroLevel` the foliation is tangent to the kernels of `dπ`, so `π`
  is constant on each leaf (`TauCeti.Foliation.SameLeaf.apply_eq_of_le_ker`), and a fibre of `π`
  is an orbit.

All declarations are in the namespace `TauCeti.SmoothTwoForm.IsEquivariantMomentMap`, beside those
of `ZeroLevel/Basic.lean`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  Proposition 5.4.13.
* J. Marsden, A. Weinstein, *Reduction of symplectic manifolds with symmetry*, Reports on
  Mathematical Physics 5 (1974), 121–130.
* K. Meyer, *Symmetries and integrals in mechanics*, in *Dynamical Systems* (M. Peixoto, ed.),
  Academic Press, 1973, 259–273.
-/

public section

open Module
open scoped Manifold ContDiff

namespace TauCeti

namespace SmoothTwoForm

namespace IsEquivariantMomentMap

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M] [T2Space M]
  [MulAction G M] [ContMDiffSMul I I' ∞ G M]
  {σ : SmoothTwoForm I' M} {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)} {n : ℕ}
  (h : σ.IsEquivariantMomentMap μ) (hσ : σ.IsNondegenerate)
  (hfree : ∀ x, μ x = 0 → MulAction.stabilizer G x = ⊥)
  (hn : finrank ℝ E' - finrank ℝ (GroupLieAlgebra I G) = n)

/-- **The zero level is coisotropic.** If `σ` is nondegenerate and `G` acts freely at every point
of `μ⁻¹(0)`, the inclusion of the zero level into `M`, for the atlas `zeroLevelChartedSpace`, is a
coisotropic map: each tangent image `ker dμ_z` contains its symplectic complement. -/
theorem isCoisotropicMap_coe_zeroLevel :
    letI := h.zeroLevelChartedSpace hσ hfree hn
    hσ.IsCoisotropicMap 𝓘(ℝ, Fin n → ℝ) (Subtype.val : h.zeroLevel → M) := by
  let := h.zeroLevelChartedSpace hσ hfree hn
  refine IsNondegenerate.isCoisotropicMap_iff.2 fun z ↦ ?_
  rw [h.range_mfderiv_coe_zeroLevel hσ hfree hn z,
    h.toIsMomentMap.isCoisotropic_ker_differential_iff hσ (h.momentCocycle_eq_zero z),
    h.mem_zeroLevel.1 z.property, lieAnnihilator_zero]

/-- **The null directions of the zero level are the orbit directions.** If moreover `G` acts
properly on the zero level, then at each of its points `z` the kernel of the form `i^* σ` induced
by the inclusion `i` is the kernel of the differential at `z` of the orbit projection
`μ⁻¹(0) → μ⁻¹(0) / G`, for the atlases `zeroLevelChartedSpace` and
`zeroLevelQuotientChartedSpace`. -/
theorem ker_bilinFormAt_mpullback_coe_zeroLevel [ProperSMul G h.zeroLevel] (z : h.zeroLevel) :
    letI := h.zeroLevelChartedSpace hσ hfree hn
    letI := h.zeroLevelQuotientChartedSpace hσ hfree hn
    haveI := h.isManifold_zeroLevel hσ hfree hn
    LinearMap.ker ((SmoothForm.mpullback Subtype.val
        (h.isSmoothEmbedding_coe_zeroLevel hσ hfree hn).contMDiff σ).bilinFormAt z) =
      (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, ProperSMul.QuotientModelSpace E (Fin n → ℝ))
        (Quotient.mk (MulAction.orbitRel G h.zeroLevel)) z).ker := by
  let := h.zeroLevelChartedSpace hσ hfree hn
  have := h.isManifold_zeroLevel hσ hfree hn
  rw [h.ker_mfderiv_quotientMk_zeroLevel_eq_comap_map_lieAnnihilator hσ hfree hn,
    h.toIsMomentMap.ker_bilinFormAt_mpullback _ (hσ.nondegenerate_bilinFormAt z)
      (h.momentCocycle_eq_zero z) (h.range_mfderiv_coe_zeroLevel hσ hfree hn z),
    h.mem_zeroLevel.1 z.property]

/-! ### Orbits lie in characteristic leaves -/

section Leaves

variable (hσ : σ.IsSymplectic)

/-- **The fundamental vector fields are tangent to the characteristic foliation.** If `σ` is
symplectic and `G` acts freely at every point of `μ⁻¹(0)`, then for every `ξ` in the Lie algebra
of `G` and every point `z` of the zero level, the value at `z` of the fundamental vector field of
`ξ` on the zero level lies in the tangent space at `z` of the characteristic foliation of the
inclusion of the zero level. -/
theorem fundamentalVectorField_mem_distribution_characteristicFoliation_zeroLevel
    (ξ : GroupLieAlgebra I G) (z : h.zeroLevel) :
    letI := h.zeroLevelChartedSpace hσ.isNondegenerate hfree hn
    haveI := h.isManifold_zeroLevel hσ.isNondegenerate hfree hn
    haveI : IsManifold 𝓘(ℝ, Fin n → ℝ) (1 + 1) h.zeroLevel := .of_le (n := ∞) (by norm_num)
    fundamentalVectorField 𝓘(ℝ, Fin n → ℝ) ξ z ∈
      ((h.isCoisotropicMap_coe_zeroLevel hσ.isNondegenerate hfree hn).characteristicFoliation
        (h.isSmoothEmbedding_coe_zeroLevel hσ.isNondegenerate hfree hn).isImmersion
        (h.isSmoothEmbedding_coe_zeroLevel hσ.isNondegenerate hfree hn).contMDiff hσ.isClosed
        le_rfl).distribution z := by
  let := h.zeroLevelChartedSpace hσ.isNondegenerate hfree hn
  have := h.isManifold_zeroLevel hσ.isNondegenerate hfree hn
  have : IsManifold 𝓘(ℝ, Fin n → ℝ) (1 + 1) h.zeroLevel := .of_le (n := ∞) (by norm_num)
  have := h.contMDiffSMul_zeroLevel hσ.isNondegenerate hfree hn
  have hemb := h.isSmoothEmbedding_coe_zeroLevel hσ.isNondegenerate hfree hn
  rw [IsNondegenerate.IsCoisotropicMap.characteristicFoliation_distribution,
    h.toIsMomentMap.ker_bilinFormAt_mpullback _
      (hσ.isNondegenerate.nondegenerate_bilinFormAt _) (h.momentCocycle_eq_zero _)
      (h.range_mfderiv_coe_zeroLevel hσ.isNondegenerate hfree hn _),
    h.mem_zeroLevel.1 z.property, lieAnnihilator_zero, LieSubalgebra.top_toSubmodule,
    Submodule.map_top, ← InfinitesimalAction.orbitTangent_eq_range, Submodule.mem_comap,
    ContinuousLinearMap.coe_coe,
    mfderiv_fundamentalVectorField_of_map_smul (hemb.contMDiff.mdifferentiableAt (by simp))
      ((ContMDiffSMul.contMDiff_smul_const (I := I) (n := ∞) _).mdifferentiableAt (by simp))
      (fun g ↦ SubMulAction.val_smul g _), ← InfinitesimalAction.fundamental_apply]
  exact (InfinitesimalAction.fundamental I G I' M).mem_orbitTangent _ ξ

/-- **Exponential translates stay on the characteristic leaf.** If `σ` is symplectic and `G` acts
freely at every point of `μ⁻¹(0)`, then for every `ξ` in the Lie algebra of `G` and every point
`z` of the zero level, `exp ξ • z` lies on the leaf through `z` of the characteristic foliation of
the inclusion of the zero level. -/
theorem mulInvariantExp_smul_mem_leaf_characteristicFoliation_zeroLevel [T2Space G]
    [BoundarylessManifold I G] (ξ : GroupLieAlgebra I G) (z : h.zeroLevel) :
    letI := h.zeroLevelChartedSpace hσ.isNondegenerate hfree hn
    haveI := h.isManifold_zeroLevel hσ.isNondegenerate hfree hn
    haveI : IsManifold 𝓘(ℝ, Fin n → ℝ) (1 + 1) h.zeroLevel := .of_le (n := ∞) (by norm_num)
    mulInvariantExp ξ • z ∈
      ((h.isCoisotropicMap_coe_zeroLevel hσ.isNondegenerate hfree hn).characteristicFoliation
        (h.isSmoothEmbedding_coe_zeroLevel hσ.isNondegenerate hfree hn).isImmersion
        (h.isSmoothEmbedding_coe_zeroLevel hσ.isNondegenerate hfree hn).contMDiff hσ.isClosed
        le_rfl).leaf z := by
  let := h.zeroLevelChartedSpace hσ.isNondegenerate hfree hn
  have := h.isManifold_zeroLevel hσ.isNondegenerate hfree hn
  have : IsManifold 𝓘(ℝ, Fin n → ℝ) (1 + 1) h.zeroLevel := .of_le (n := ∞) (by norm_num)
  have := h.contMDiffSMul_zeroLevel hσ.isNondegenerate hfree hn
  exact Foliation.mulInvariantExp_smul_mem_leaf _
    (h.fundamentalVectorField_mem_distribution_characteristicFoliation_zeroLevel hfree hn hσ) ξ z

/-- **Orbits of the zero level lie in characteristic leaves.** If `σ` is symplectic and the
connected group `G` acts freely at every point of `μ⁻¹(0)`, then the orbit of each point `z` of
the zero level is contained in the leaf through `z` of the characteristic foliation of the
inclusion of the zero level. -/
theorem orbit_subset_leaf_characteristicFoliation_zeroLevel [ConnectedSpace G]
    (z : h.zeroLevel) :
    letI := h.zeroLevelChartedSpace hσ.isNondegenerate hfree hn
    haveI := h.isManifold_zeroLevel hσ.isNondegenerate hfree hn
    haveI : IsManifold 𝓘(ℝ, Fin n → ℝ) (1 + 1) h.zeroLevel := .of_le (n := ∞) (by norm_num)
    MulAction.orbit G z ⊆
      ((h.isCoisotropicMap_coe_zeroLevel hσ.isNondegenerate hfree hn).characteristicFoliation
        (h.isSmoothEmbedding_coe_zeroLevel hσ.isNondegenerate hfree hn).isImmersion
        (h.isSmoothEmbedding_coe_zeroLevel hσ.isNondegenerate hfree hn).contMDiff hσ.isClosed
        le_rfl).leaf z := by
  let := h.zeroLevelChartedSpace hσ.isNondegenerate hfree hn
  have := h.isManifold_zeroLevel hσ.isNondegenerate hfree hn
  have : IsManifold 𝓘(ℝ, Fin n → ℝ) (1 + 1) h.zeroLevel := .of_le (n := ∞) (by norm_num)
  have := h.contMDiffSMul_zeroLevel hσ.isNondegenerate hfree hn
  exact Foliation.orbit_subset_leaf _
    (h.fundamentalVectorField_mem_distribution_characteristicFoliation_zeroLevel hfree hn hσ) z

/-- **Characteristic leaves of the zero level lie in orbits.** If `σ` is symplectic and `G` acts
freely at every point of `μ⁻¹(0)` and properly on the zero level, then the leaf through each point
`z` of the zero level of the characteristic foliation of the inclusion of the zero level is
contained in the orbit of `z`. -/
theorem leaf_characteristicFoliation_zeroLevel_subset_orbit [ProperSMul G h.zeroLevel]
    (z : h.zeroLevel) :
    letI := h.zeroLevelChartedSpace hσ.isNondegenerate hfree hn
    haveI := h.isManifold_zeroLevel hσ.isNondegenerate hfree hn
    haveI : IsManifold 𝓘(ℝ, Fin n → ℝ) (1 + 1) h.zeroLevel := .of_le (n := ∞) (by norm_num)
    ((h.isCoisotropicMap_coe_zeroLevel hσ.isNondegenerate hfree hn).characteristicFoliation
        (h.isSmoothEmbedding_coe_zeroLevel hσ.isNondegenerate hfree hn).isImmersion
        (h.isSmoothEmbedding_coe_zeroLevel hσ.isNondegenerate hfree hn).contMDiff hσ.isClosed
        le_rfl).leaf z ⊆
      MulAction.orbit G z := by
  let := h.zeroLevelChartedSpace hσ.isNondegenerate hfree hn
  let := h.zeroLevelQuotientChartedSpace hσ.isNondegenerate hfree hn
  have := h.isManifold_zeroLevel hσ.isNondegenerate hfree hn
  have : IsManifold 𝓘(ℝ, Fin n → ℝ) (1 + 1) h.zeroLevel := .of_le (n := ∞) (by norm_num)
  have : IsManifold 𝓘(ℝ, ProperSMul.QuotientModelSpace E (Fin n → ℝ)) 1
      (MulAction.orbitRel.Quotient G h.zeroLevel) :=
    (h.isManifold_zeroLevelQuotient hσ.isNondegenerate hfree hn).of_le (by norm_num)
  intro y hy
  -- The orbit projection is constant on the leaf, whose tangent spaces are the kernels of its
  -- differential.
  have hq := (Foliation.mem_leaf.1 hy).apply_eq_of_le_ker
    ((h.isSubmersion_quotientMk_zeroLevel hσ.isNondegenerate hfree hn).contMDiff.mdifferentiable
      (by simp))
    fun x ↦ by
      rw [IsNondegenerate.IsCoisotropicMap.characteristicFoliation_distribution,
        h.ker_bilinFormAt_mpullback_coe_zeroLevel hσ.isNondegenerate hfree hn]
  exact MulAction.mem_orbit_symm.1 (MulAction.orbitRel_apply.1 (Quotient.exact hq))

/-- **The characteristic leaves of the zero level are the orbits.** If `σ` is symplectic and the
connected group `G` acts freely at every point of `μ⁻¹(0)` and properly on the zero level, then
the leaf through each point `z` of the zero level of the characteristic foliation of the
inclusion of the zero level is the orbit of `z`. -/
theorem leaf_characteristicFoliation_zeroLevel [ConnectedSpace G] [ProperSMul G h.zeroLevel]
    (z : h.zeroLevel) :
    letI := h.zeroLevelChartedSpace hσ.isNondegenerate hfree hn
    haveI := h.isManifold_zeroLevel hσ.isNondegenerate hfree hn
    haveI : IsManifold 𝓘(ℝ, Fin n → ℝ) (1 + 1) h.zeroLevel := .of_le (n := ∞) (by norm_num)
    ((h.isCoisotropicMap_coe_zeroLevel hσ.isNondegenerate hfree hn).characteristicFoliation
        (h.isSmoothEmbedding_coe_zeroLevel hσ.isNondegenerate hfree hn).isImmersion
        (h.isSmoothEmbedding_coe_zeroLevel hσ.isNondegenerate hfree hn).contMDiff hσ.isClosed
        le_rfl).leaf z =
      MulAction.orbit G z :=
  (h.leaf_characteristicFoliation_zeroLevel_subset_orbit hfree hn hσ z).antisymm
    (h.orbit_subset_leaf_characteristicFoliation_zeroLevel hfree hn hσ z)

end Leaves

end IsEquivariantMomentMap

end SmoothTwoForm

end TauCeti

end
