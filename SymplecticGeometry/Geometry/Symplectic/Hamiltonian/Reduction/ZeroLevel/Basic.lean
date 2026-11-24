/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Reduction.ReducedSpace
public import SymplecticGeometry.Topology.Algebra.ProperAction.Basic

-- `zeroLevelChartedSpace` is `levelSubMulActionChartedSpace 0`, which needs the two levels to
-- have the same points by definition; that unfolds the body of `levelSubMulAction`.
import all TauCeti.Geometry.Symplectic.Hamiltonian.EquivariantMomentMap.LevelAction
import TauCeti.Geometry.Lie.Subgroup.Stabilizer
import SymplecticGeometry.Geometry.Lie.FundamentalVectorField

/-!
# The zero level of an equivariant moment map and its quotient by the group

Let a Lie group `G` act smoothly on a Hausdorff manifold `(M, σ)` with coadjoint-equivariant
moment map `μ : M → 𝔤*` (`TauCeti.SmoothTwoForm.IsEquivariantMomentMap`, in Tau Ceti's sign).
Since `0 ∈ 𝔤*` is fixed by the coadjoint action, the level `Z = μ⁻¹(0)` is invariant under all of
`G`, not only under a coadjoint stabilizer. This file treats `Z` as a `G`-space and builds the
reduced space `Z / G` when `G` acts freely at the points of `Z` and properly on `Z`; no properness
on all of `M` is assumed.

* `zeroLevel`: the level `μ⁻¹(0)` as a `SubMulAction` of `G`. The instance
  `SubMulAction.properSMul` gives properness on it from a proper action on `M`, and
  `isCancelSMul_zeroLevel` gives freeness.
* `zeroLevelChartedSpace`, `isManifold_zeroLevel`, `isSmoothEmbedding_coe_zeroLevel`,
  `range_mfderiv_coe_zeroLevel`: freeness makes `0` a regular value, so `Z` is an embedded
  submanifold of `M`, modelled on `Fin n → ℝ` for `n = dim M - dim 𝔤`, with tangent spaces
  `ker dμ`. `contMDiffSMul_zeroLevel`: `G` acts smoothly on it, and
  `finrank_add_finrank_zeroLevel`: `n + dim 𝔤 = dim M` once `Z` has a point.
* `zeroLevelQuotientChartedSpace`, `isManifold_zeroLevelQuotient`,
  `isSubmersion_quotientMk_zeroLevel`: the quotient manifold theorem for the free proper action of
  `G` on `Z`.
* `ker_mfderiv_quotientMk_zeroLevel`: the vertical vectors of `π : Z → Z / G` at `z` are those
  that the inclusion `i` sends into the orbit tangent space `𝔤 · z` of `M`, and
  `ker_mfderiv_quotientMk_zeroLevel_eq_comap_map_lieAnnihilator` says the same in the form of Tau
  Ceti's level-data theorems.
* `existsUnique_isSymplectic_mpullback_quotientMk_zeroLevel_eq_mpullback`: the
  **Marsden–Weinstein–Meyer theorem** at `0`: a unique symplectic form `ω_red` on `Z / G` with
  `π^* ω_red = i^* σ`.
* `finrank_quotientModelSpace_zeroLevel`: `dim (Z / G) + 2 dim 𝔤 = dim M` once `Z` has a point.

All declarations are in the namespace `TauCeti.SmoothTwoForm.IsEquivariantMomentMap`, beside
Tau Ceti's `levelSubMulAction`, so that they can move there unchanged. The zero level has the
points of Tau Ceti's level `levelSubMulAction 0`, so its atlas is `levelSubMulActionChartedSpace 0`
and `isManifold_zeroLevel`, `isSmoothEmbedding_coe_zeroLevel` and `range_mfderiv_coe_zeroLevel`
are `isManifold_levelSubMulAction`, `isSmoothEmbedding_coe_levelSubMulAction` and
`range_mfderiv_coe_levelSubMulAction` at `c = 0`. The proofs of
`existsUnique_isSymplectic_mpullback_quotientMk_zeroLevel_eq_mpullback` and
`finrank_quotientModelSpace_zeroLevel` adapt those of Tau Ceti's
`existsUnique_isSymplectic_mpullback_quotientMk_eq_mpullback` and
`finrank_quotientModelSpace_add_finrank_add_finrank_lieAnnihilator`
(`TauCeti/Geometry/Symplectic/Hamiltonian/Reduction/ReducedSpace.lean`) from the coadjoint
stabilizer `G_c` to the whole group `G` at `c = 0`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  Proposition 5.4.13 and Remark 5.4.14.
* J. Marsden, A. Weinstein, *Reduction of symplectic manifolds with symmetry*, Reports on
  Mathematical Physics 5 (1974), 121–130.
* K. Meyer, *Symmetries and integrals in mechanics*, in *Dynamical Systems* (M. Peixoto, ed.),
  Academic Press, 1973, 259–273.
-/

public section

noncomputable section

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
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M]
  [MulAction G M] [ContMDiffSMul I I' ∞ G M]
  {σ : SmoothTwoForm I' M} {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)} {n : ℕ}

/-! ### The zero level as a `G`-space -/

/-- **The zero level as a `G`-space.** The level `μ⁻¹(0)` of an equivariant moment map, as a
`SubMulAction` of the whole group `G`: it is invariant since `0` is fixed by the coadjoint action.
Its points are those with `μ x = 0`, with the subspace topology. -/
def zeroLevel (h : σ.IsEquivariantMomentMap μ) : SubMulAction G M where
  carrier := μ ⁻¹' {0}
  smul_mem' g x hx := by
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hx ⊢
    rw [h.apply_smul, hx, map_zero]

variable (h : σ.IsEquivariantMomentMap μ)

/-- A point lies in the zero level exactly when `μ` vanishes there. -/
@[simp]
theorem mem_zeroLevel {x : M} : x ∈ h.zeroLevel ↔ μ x = 0 :=
  Iff.rfl

/-- The underlying set of the zero level is the preimage `μ⁻¹(0)`. -/
@[simp]
theorem coe_zeroLevel : (h.zeroLevel : Set M) = μ ⁻¹' {0} :=
  (rfl)

/-- **Freeness on the zero level.** If `G` acts freely at every point of `μ⁻¹(0)`, it acts freely
on the zero level. -/
theorem isCancelSMul_zeroLevel (hfree : ∀ x, μ x = 0 → MulAction.stabilizer G x = ⊥) :
    IsCancelSMul G h.zeroLevel :=
  isCancelSMul_iff_stabilizer_eq_bot.2 fun z ↦ by
    rw [SubMulAction.stabilizer_of_subMul]
    exact hfree z z.property

/-! ### The zero level as a manifold -/

variable [I'.Boundaryless] [T2Space M]

/-- **The atlas of the zero level.** If the form is nondegenerate and `G` acts freely at every
point of `μ⁻¹(0)`, then `0` is a regular value of `μ`, and the zero level carries Tau Ceti's atlas
`levelSubMulActionChartedSpace` of the level at `0`, modelled on `Fin n → ℝ` for
`n = dim M - dim 𝔤`; the two `SubMulAction`s have the same points. -/
@[instance_reducible]
def zeroLevelChartedSpace (hσ : σ.IsNondegenerate)
    (hfree : ∀ x, μ x = 0 → MulAction.stabilizer G x = ⊥)
    (hn : finrank ℝ E' - finrank ℝ (GroupLieAlgebra I G) = n) :
    ChartedSpace (Fin n → ℝ) h.zeroLevel :=
  h.levelSubMulActionChartedSpace 0
    (h.forall_differential_surjective_of_stabilizer_eq_bot hσ hfree) hn

section Level

variable (hσ : σ.IsNondegenerate) (hfree : ∀ x, μ x = 0 → MulAction.stabilizer G x = ⊥)
  (hn : finrank ℝ E' - finrank ℝ (GroupLieAlgebra I G) = n)

/-- **The zero level is a smooth manifold**, for the atlas `zeroLevelChartedSpace`. -/
theorem isManifold_zeroLevel :
    letI := h.zeroLevelChartedSpace hσ hfree hn
    IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ h.zeroLevel :=
  h.isManifold_levelSubMulAction (c := 0) _ hn

/-- **The zero level is an embedded submanifold**: its inclusion into `M` is a smooth
embedding. -/
theorem isSmoothEmbedding_coe_zeroLevel :
    letI := h.zeroLevelChartedSpace hσ hfree hn
    Manifold.IsSmoothEmbedding 𝓘(ℝ, Fin n → ℝ) I' ∞ (Subtype.val : h.zeroLevel → M) :=
  h.isSmoothEmbedding_coe_levelSubMulAction (c := 0) _ hn

/-- **The tangent space of the zero level is the kernel of `dμ`**: at `z`, the differential of
the inclusion has range `ker dμ_z`. -/
theorem range_mfderiv_coe_zeroLevel (z : h.zeroLevel) :
    letI := h.zeroLevelChartedSpace hσ hfree hn
    LinearMap.range (mfderiv 𝓘(ℝ, Fin n → ℝ) I' (Subtype.val : h.zeroLevel → M) z).toLinearMap =
      LinearMap.ker (h.differential z) :=
  h.range_mfderiv_coe_levelSubMulAction (c := 0) _ hn z

/-- **`G` acts smoothly on the zero level**, for the atlas `zeroLevelChartedSpace`. -/
theorem contMDiffSMul_zeroLevel :
    letI := h.zeroLevelChartedSpace hσ hfree hn
    ContMDiffSMul I 𝓘(ℝ, Fin n → ℝ) ∞ G h.zeroLevel :=
  letI := h.zeroLevelChartedSpace hσ hfree hn
  (h.isSmoothEmbedding_coe_zeroLevel hσ hfree hn).contMDiffSMul contMDiff_id
    fun g z ↦ SubMulAction.val_smul g z

include hσ hfree hn in
/-- **The dimension of the zero level.** If the zero level has a point `z`, then
`n + dim 𝔤 = dim M`, so the truncated subtraction in `hn` is the honest one. -/
theorem finrank_add_finrank_zeroLevel (z : h.zeroLevel) :
    n + finrank ℝ (GroupLieAlgebra I G) = finrank ℝ E' := by
  have := h.toIsMomentMap.finrank_ker_differential_add_finrank (hσ.nondegenerate_bilinFormAt z)
    (Lie.isotropy_eq_bot_of_stabilizer_eq_bot (hfree z z.property))
  omega

end Level

/-! ### The quotient by `G` -/

section Quotient

variable (hσ : σ.IsNondegenerate) (hfree : ∀ x, μ x = 0 → MulAction.stabilizer G x = ⊥)
  (hn : finrank ℝ E' - finrank ℝ (GroupLieAlgebra I G) = n) [ProperSMul G h.zeroLevel]

omit [ProperSMul G h.zeroLevel] in
/-- The hypotheses of the quotient manifold theorem for the action of `G` on the zero level,
other than properness. -/
private theorem quotient_hypotheses :
    letI := h.zeroLevelChartedSpace hσ hfree hn
    IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ h.zeroLevel ∧
      ContMDiffSMul I 𝓘(ℝ, Fin n → ℝ) ∞ G h.zeroLevel ∧ IsCancelSMul G h.zeroLevel :=
  ⟨h.isManifold_zeroLevel hσ hfree hn, h.contMDiffSMul_zeroLevel hσ hfree hn,
    h.isCancelSMul_zeroLevel hfree⟩

/-- **The atlas of the reduced space** `μ⁻¹(0) / G`: the slice charts of the quotient manifold
theorem `ProperSMul.orbitRelQuotientChartedSpace`, for the free and proper action of `G` on the
zero level. -/
@[instance_reducible]
def zeroLevelQuotientChartedSpace :
    ChartedSpace (ProperSMul.QuotientModelSpace E (Fin n → ℝ))
      (MulAction.orbitRel.Quotient G h.zeroLevel) :=
  letI := h.zeroLevelChartedSpace hσ hfree hn
  haveI := (h.quotient_hypotheses hσ hfree hn).1
  haveI := (h.quotient_hypotheses hσ hfree hn).2.1
  haveI := (h.quotient_hypotheses hσ hfree hn).2.2
  ProperSMul.orbitRelQuotientChartedSpace I G 𝓘(ℝ, Fin n → ℝ) h.zeroLevel

/-- **The reduced space `μ⁻¹(0) / G` is a smooth manifold**, for the atlas
`zeroLevelQuotientChartedSpace`. -/
theorem isManifold_zeroLevelQuotient :
    letI := h.zeroLevelQuotientChartedSpace hσ hfree hn
    IsManifold 𝓘(ℝ, ProperSMul.QuotientModelSpace E (Fin n → ℝ)) ∞
      (MulAction.orbitRel.Quotient G h.zeroLevel) := by
  let := h.zeroLevelChartedSpace hσ hfree hn
  obtain ⟨_, _, _⟩ := h.quotient_hypotheses hσ hfree hn
  exact ProperSMul.instIsManifoldOrbitRelQuotient

/-- **The orbit projection `μ⁻¹(0) → μ⁻¹(0) / G` is a smooth submersion.** -/
theorem isSubmersion_quotientMk_zeroLevel :
    letI := h.zeroLevelChartedSpace hσ hfree hn
    letI := h.zeroLevelQuotientChartedSpace hσ hfree hn
    Manifold.IsSubmersion 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, ProperSMul.QuotientModelSpace E (Fin n → ℝ)) ∞
      (Quotient.mk (MulAction.orbitRel G h.zeroLevel)) := by
  let := h.zeroLevelChartedSpace hσ hfree hn
  obtain ⟨_, _, _⟩ := h.quotient_hypotheses hσ hfree hn
  exact ProperSMul.isSubmersion_quotientMk

/-- **The vertical directions of the reduced space are the orbit directions.** At a point `z` of
the zero level, a tangent vector is in the kernel of the differential of the orbit projection
`μ⁻¹(0) → μ⁻¹(0) / G` exactly when the differential of the inclusion `i` sends it into the orbit
tangent space `𝔤 · z` of `M`. -/
theorem ker_mfderiv_quotientMk_zeroLevel (z : h.zeroLevel) :
    letI := h.zeroLevelChartedSpace hσ hfree hn
    letI := h.zeroLevelQuotientChartedSpace hσ hfree hn
    (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, ProperSMul.QuotientModelSpace E (Fin n → ℝ))
        (Quotient.mk (MulAction.orbitRel G h.zeroLevel)) z).ker =
      ((InfinitesimalAction.fundamental I G I' M).orbitTangent z).comap
        (mfderiv 𝓘(ℝ, Fin n → ℝ) I' (Subtype.val : h.zeroLevel → M) z).toLinearMap := by
  let := h.zeroLevelChartedSpace hσ hfree hn
  obtain ⟨_, _, _⟩ := h.quotient_hypotheses hσ hfree hn
  have hemb := h.isSmoothEmbedding_coe_zeroLevel hσ hfree hn
  set di := (mfderiv 𝓘(ℝ, Fin n → ℝ) I' (Subtype.val : h.zeroLevel → M) z).toLinearMap
  rw [ProperSMul.ker_mfderiv_quotientMk]
  have hdi : Function.Injective di := hemb.isImmersion.mfderiv_injective (by simp) z
  -- `di` carries the orbit tangent spaces of the zero level onto those of `M`.
  have hVW : ((InfinitesimalAction.fundamental I G 𝓘(ℝ, Fin n → ℝ) h.zeroLevel).orbitTangent z).map
      di = (InfinitesimalAction.fundamental I G I' M).orbitTangent (z : M) :=
    InfinitesimalAction.map_orbitTangent_fundamental_of_map_smul
      (hemb.contMDiff.mdifferentiableAt (by simp)) (fun g ↦ SubMulAction.val_smul g z)
  rw [← hVW, Submodule.comap_map_eq_of_injective hdi]

/-- **The vertical directions of the reduced space, through the annihilator of `0`.** The kernel
of the differential of the orbit projection at `z` consists of the tangent vectors that `di` sends
into `𝔤_0 · z`, for the annihilator `𝔤_0 = lieAnnihilator ℝ 𝔤 0`, which is all of `𝔤`. This is the
form of `ker_mfderiv_quotientMk_zeroLevel` that Tau Ceti's level-data theorems take. -/
theorem ker_mfderiv_quotientMk_zeroLevel_eq_comap_map_lieAnnihilator (z : h.zeroLevel) :
    letI := h.zeroLevelChartedSpace hσ hfree hn
    letI := h.zeroLevelQuotientChartedSpace hσ hfree hn
    (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, ProperSMul.QuotientModelSpace E (Fin n → ℝ))
        (Quotient.mk (MulAction.orbitRel G h.zeroLevel)) z).ker =
      ((lieAnnihilator ℝ (GroupLieAlgebra I G)
          (0 : Module.Dual ℝ (GroupLieAlgebra I G))).toSubmodule.map
        ((InfinitesimalAction.fundamental I G I' M).eval z)).comap
        (mfderiv 𝓘(ℝ, Fin n → ℝ) I' (Subtype.val : h.zeroLevel → M) z).toLinearMap := by
  rw [h.ker_mfderiv_quotientMk_zeroLevel hσ hfree hn, lieAnnihilator_zero,
    LieSubalgebra.top_toSubmodule, Submodule.map_top, InfinitesimalAction.orbitTangent_eq_range]

/-- **The Marsden–Weinstein–Meyer theorem at the zero level.** Let `G` act smoothly by
symplectomorphisms on a symplectic manifold `(M, σ)`, with coadjoint-equivariant moment map `μ`,
freely at every point of `μ⁻¹(0)` and properly on `μ⁻¹(0)`. Then the reduced space `μ⁻¹(0) / G`
carries a unique symplectic form `ω_red` with `π^* ω_red = i^* σ`, for the orbit projection
`π : μ⁻¹(0) → μ⁻¹(0) / G` and the inclusion `i : μ⁻¹(0) → M`. -/
theorem existsUnique_isSymplectic_mpullback_quotientMk_zeroLevel_eq_mpullback
    (hσ : σ.IsSymplectic)
    (hG : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ)
    (hfree : ∀ x, μ x = 0 → MulAction.stabilizer G x = ⊥)
    (hn : finrank ℝ E' - finrank ℝ (GroupLieAlgebra I G) = n) :
    letI := h.zeroLevelChartedSpace hσ.isNondegenerate hfree hn
    letI := h.zeroLevelQuotientChartedSpace hσ.isNondegenerate hfree hn
    haveI := h.isManifold_zeroLevel hσ.isNondegenerate hfree hn
    haveI := h.isManifold_zeroLevelQuotient hσ.isNondegenerate hfree hn
    ∃! η : SmoothTwoForm 𝓘(ℝ, ProperSMul.QuotientModelSpace E (Fin n → ℝ))
        (MulAction.orbitRel.Quotient G h.zeroLevel),
      η.IsSymplectic ∧
        SmoothForm.mpullback _
            (h.isSubmersion_quotientMk_zeroLevel hσ.isNondegenerate hfree hn).contMDiff η =
          SmoothForm.mpullback Subtype.val
            (h.isSmoothEmbedding_coe_zeroLevel hσ.isNondegenerate hfree hn).contMDiff σ := by
  let := h.zeroLevelChartedSpace hσ.isNondegenerate hfree hn
  have := h.isManifold_zeroLevel hσ.isNondegenerate hfree hn
  have := h.contMDiffSMul_zeroLevel hσ.isNondegenerate hfree hn
  let := h.zeroLevelQuotientChartedSpace hσ.isNondegenerate hfree hn
  have := h.isManifold_zeroLevelQuotient hσ.isNondegenerate hfree hn
  exact h.existsUnique_isSymplectic_mpullback_eq_mpullback hσ hG
    (h.isSmoothEmbedding_coe_zeroLevel hσ.isNondegenerate hfree hn).contMDiff
    (fun z ↦ z.property) (h.range_mfderiv_coe_zeroLevel hσ.isNondegenerate hfree hn)
    (h.isSubmersion_quotientMk_zeroLevel hσ.isNondegenerate hfree hn) Quotient.mk_surjective
    (h.ker_mfderiv_quotientMk_zeroLevel_eq_comap_map_lieAnnihilator hσ.isNondegenerate hfree hn)
    (fun g ↦ ContMDiffSMul.contMDiff_const_smul (I := I) g)
    (fun g z ↦ Quotient.sound (MulAction.orbitRel_apply.2 (MulAction.mem_orbit z g)))
    (fun z z' hzz' ↦
      MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 (Quotient.exact hzz'.symm)))
    id fun g z ↦ SubMulAction.val_smul g z

include hσ hfree hn in
/-- **The dimension of the reduced space at zero.** If the zero level has a point `z`, the
reduced space `μ⁻¹(0) / G` has dimension `dim M - 2 dim 𝔤`: its model space satisfies
`dim (μ⁻¹(0) / G) + 2 dim 𝔤 = dim M`. -/
theorem finrank_quotientModelSpace_zeroLevel (z : h.zeroLevel) :
    finrank ℝ (ProperSMul.QuotientModelSpace E (Fin n → ℝ)) +
      2 * finrank ℝ (GroupLieAlgebra I G) = finrank ℝ E' := by
  let := h.zeroLevelChartedSpace hσ hfree hn
  have hemb := h.isSmoothEmbedding_coe_zeroLevel hσ hfree hn
  let := h.zeroLevelQuotientChartedSpace hσ hfree hn
  have hz : μ z = 0 := z.property
  have := h.toIsMomentMap.finrank_add_finrank_add_finrank_lieAnnihilator
    (hσ.nondegenerate_bilinFormAt z) hz (h.momentCocycle_eq_zero z)
    (h.range_mfderiv_coe_zeroLevel hσ hfree hn z)
    (hemb.isImmersion.mfderiv_injective (by simp) z)
    (Lie.isotropy_eq_bot_of_stabilizer_eq_bot (hfree z hz))
    ((h.isSubmersion_quotientMk_zeroLevel hσ hfree hn).surjective_mfderiv (by simp) z)
    (h.ker_mfderiv_quotientMk_zeroLevel_eq_comap_map_lieAnnihilator hσ hfree hn z)
  rw [lieAnnihilator_zero, LieSubalgebra.topEquiv.toLinearEquiv.finrank_eq] at this
  omega

end Quotient

end IsEquivariantMomentMap

end SmoothTwoForm

end TauCeti

end

end
