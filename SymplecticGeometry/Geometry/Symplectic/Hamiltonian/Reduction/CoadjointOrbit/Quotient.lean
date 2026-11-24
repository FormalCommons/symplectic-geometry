/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.Reduction.CoadjointOrbit.Level
public import SymplecticGeometry.Geometry.Symplectic.Manifold.Prod
public import TauCeti.Geometry.Symplectic.Hamiltonian.Reduction.Naturality
-- The atlases of the product's zero level and of its quotient here must agree by definition with
-- those of `ZeroLevel/Basic.lean`, which unfolds the bodies of `zeroLevelProdChartedSpace`,
-- `zeroLevelChartedSpace` and `zeroLevelQuotientChartedSpace`.
import all SymplecticGeometry.Geometry.Symplectic.Hamiltonian.Reduction.CoadjointOrbit.Level
import all SymplecticGeometry.Geometry.Symplectic.Hamiltonian.Reduction.ZeroLevel.Basic

/-!
# Reduction at a coadjoint orbit

Let a Lie group `G` act smoothly on `(M, σ)` with coadjoint-equivariant moment map `μ`
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap`, in Tau Ceti's sign), let `η : 𝔤*` have an
embedded coadjoint orbit `O = G ⧸ G_η`, with orbit map `ι` and KKS form `ω_O`, and let `G` act
freely and properly on the preimage `Q = orbitLevel η` of the orbit. `CoadjointOrbit/Level.lean`
makes `Q` a manifold through the graph `orbitLevelGraph`, a `G`-equivariant diffeomorphism onto
the zero level `P` of the moment map `(x, q) ↦ μ x + ι q` of `σ.prod ω_O` on `M × O`. This file
builds the reduced space `Q / G` and compares it with `P / G`.

* `orbitLevelQuotientChartedSpace`, `isManifold_orbitLevelQuotient`,
  `isSubmersion_quotientMk_orbitLevel`: the quotient manifold theorem for the free proper action
  of `G` on `Q`; `zeroLevelProdQuotientChartedSpace` and its two lemmas are the atlas of `P / G`
  from `ZeroLevel/Basic.lean`, for the product form.
* `orbitLevelQuotientDiffeomorph`, `orbitLevelQuotientDiffeomorph_mk`: the graph descends to a
  diffeomorphism `Q / G ≃ P / G` (Tau Ceti's `ProperSMul.orbitRelQuotientDiffeomorph`).
* `mpullback_orbitLevelGraph_prod`: the product form pulls back along the graph to
  `i^* σ + (orbitLevelProj)^* ω_O`, by `TauCeti.SmoothTwoForm.prod_def`.
* `existsUnique_isSymplectic_mpullback_quotientMk_orbitLevel_eq_mpullback_add_mpullback`: `Q / G`
  carries a unique symplectic form `ω_red` with `π^* ω_red = i^* σ + (orbitLevelProj)^* ω_O`. It is
  the pullback along the diffeomorphism of the reduced form of `P / G`, and
  `mpullback_orbitLevelQuotientDiffeomorph` says that this pullback is every such `ω_red`, a case
  of Tau Ceti's `SmoothForm.mpullback_eq_of_mpullback_eq`.
* `finrank_quotientModelSpace_orbitLevel`: `dim (Q / G) + 2 dim 𝔤 = dim M + dim O` once `Q` has a
  point, from `finrank_quotientModelSpace_zeroLevel` for the product.
* `SymplecticGeometry.symplecticReduction_coadjointOrbit`: reduction at a coadjoint orbit in the
  sign of `DESIGN.md`, where the moment map is `fun x ↦ -μ x` for Tau Ceti's predicates, so that
  `Q` is the preimage `μ⁻¹(O)`.

The route through the product, rather than through Tau Ceti's shifting map, follows the proof of
McDuff–Salamon, Proposition 5.4.15. The building declarations are in the namespace
`TauCeti.SmoothTwoForm.IsEquivariantMomentMap`, beside those of `CoadjointOrbit/Level.lean`; the
milestone is in `SymplecticGeometry`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  Example 5.3.11 and Proposition 5.4.15.
* [A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, Berlin, 2001][CannasdaSilva2001Lectures], Lecture 23.
* [V. Guillemin, S. Sternberg, *Symplectic Techniques in Physics*][GuilleminSternberg1990],
  Section 26.
* J.-P. Ortega, T. S. Ratiu, *Momentum Maps and Hamiltonian Reduction*, Progress in Mathematics
  222, Birkhäuser, 2004, Section 6.1.
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
  {σ : SmoothTwoForm I' M} {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)}
  (h : σ.IsEquivariantMomentMap μ) {η : Module.Dual ℝ (GroupLieAlgebra I G)}

/-- **Freeness on the preimage of the orbit.** If `G` acts freely at every point of the preimage
of the orbit of `η`, it acts freely on that preimage. -/
theorem isCancelSMul_orbitLevel (hfree : ∀ x ∈ h.orbitLevel η, MulAction.stabilizer G x = ⊥) :
    IsCancelSMul G (h.orbitLevel η) :=
  isCancelSMul_iff_stabilizer_eq_bot.2 fun x ↦ by
    rw [SubMulAction.stabilizer_of_subMul]
    exact hfree x x.property

variable [I.Boundaryless] [I'.Boundaryless] [T2Space M] {m : ℕ}
  (hemb : Topology.IsEmbedding fun q : G ⧸ (Lie.coadjointRepresentation ℝ I G).stabilizer η ↦
    ⇑((Lie.coadjointRepresentation ℝ I G).orbitMap η q))
  (hσ : σ.IsNondegenerate) (hfree : ∀ x ∈ h.orbitLevel η, MulAction.stabilizer G x = ⊥)
  (hm : finrank ℝ E' + finrank ℝ (Subgroup.QuotientModelSpace I
    ((Lie.coadjointRepresentation ℝ I G).stabilizer η)) - finrank ℝ (GroupLieAlgebra I G) = m)

/-- **The graph is smooth**, for the atlases `orbitLevelChartedSpace` and
`zeroLevelProdChartedSpace`. -/
theorem contMDiff_orbitLevelGraph :
    letI := h.orbitLevelChartedSpace hemb hσ hfree hm
    letI := h.zeroLevelProdChartedSpace hemb hσ hfree hm
    ContMDiff 𝓘(ℝ, Fin m → ℝ) 𝓘(ℝ, Fin m → ℝ) ∞ (h.orbitLevelGraph hemb) := by
  let := h.orbitLevelChartedSpace hemb hσ hfree hm
  let := h.zeroLevelProdChartedSpace hemb hσ hfree hm
  rw [← h.coe_orbitLevelGraphDiffeomorph hemb hσ hfree hm]
  exact (h.orbitLevelGraphDiffeomorph hemb hσ hfree hm).contMDiff

/-- **The two-form of the preimage of the orbit.** Pulling the product form
`σ.prod η.coadjointOrbitForm` back along the graph `x ↦ (x, orbitLevelProj x)` gives
`i^* σ + (orbitLevelProj)^* ω_O`, for the inclusion `i` of the preimage into `M`. -/
theorem mpullback_orbitLevelGraph_prod :
    letI := h.orbitLevelChartedSpace hemb hσ hfree hm
    letI := h.zeroLevelProdChartedSpace hemb hσ hfree hm
    haveI := h.isManifold_orbitLevel hemb hσ hfree hm
    haveI := h.isManifold_zeroLevelProd hemb hσ hfree hm
    SmoothForm.mpullback (Subtype.val ∘ h.orbitLevelGraph hemb)
        ((h.isSmoothEmbedding_coe_zeroLevelProd hemb hσ hfree hm).contMDiff.comp
          (h.contMDiff_orbitLevelGraph hemb hσ hfree hm)) (σ.prod η.coadjointOrbitForm) =
      SmoothForm.mpullback Subtype.val
          (h.isSmoothEmbedding_coe_orbitLevel hemb hσ hfree hm).contMDiff
          σ +
        SmoothForm.mpullback (h.orbitLevelProj hemb) (h.contMDiff_orbitLevelProj hemb hσ hfree hm)
          η.coadjointOrbitForm := by
  let := h.orbitLevelChartedSpace hemb hσ hfree hm
  let := h.zeroLevelProdChartedSpace hemb hσ hfree hm
  have := h.isManifold_orbitLevel hemb hσ hfree hm
  have := h.isManifold_zeroLevelProd hemb hσ hfree hm
  have : T2Space (G ⧸ (Lie.coadjointRepresentation ℝ I G).stabilizer η) := hemb.t2Space
  refine (congrArg (SmoothForm.mpullback _ _) (prod_def σ η.coadjointOrbitForm)).trans ?_
  rw [map_add, SmoothForm.mpullback_mpullback, SmoothForm.mpullback_mpullback]
  simp only [Function.comp_def, coe_orbitLevelGraph]

/-! ### The quotients by `G` -/

section Quotient

variable [ProperSMul G (h.orbitLevel η)]

omit [ProperSMul G (h.orbitLevel η)] in
/-- The hypotheses of the quotient manifold theorem for the action of `G` on the preimage of the
orbit, other than properness. -/
private theorem quotient_hypotheses :
    letI := h.orbitLevelChartedSpace hemb hσ hfree hm
    IsManifold 𝓘(ℝ, Fin m → ℝ) ∞ (h.orbitLevel η) ∧
      ContMDiffSMul I 𝓘(ℝ, Fin m → ℝ) ∞ G (h.orbitLevel η) ∧ IsCancelSMul G (h.orbitLevel η) :=
  ⟨h.isManifold_orbitLevel hemb hσ hfree hm, h.contMDiffSMul_orbitLevel hemb hσ hfree hm,
    h.isCancelSMul_orbitLevel hfree⟩

include hσ hfree hm in
/-- **The atlas of the reduced space at the orbit** `Q / G`: the slice charts of the quotient
manifold theorem `ProperSMul.orbitRelQuotientChartedSpace`, for the free and proper action of `G`
on the preimage `Q` of the orbit with the atlas `orbitLevelChartedSpace`. -/
@[instance_reducible]
def orbitLevelQuotientChartedSpace :
    ChartedSpace (ProperSMul.QuotientModelSpace E (Fin m → ℝ))
      (MulAction.orbitRel.Quotient G (h.orbitLevel η)) :=
  letI := h.orbitLevelChartedSpace hemb hσ hfree hm
  haveI := (h.quotient_hypotheses hemb hσ hfree hm).1
  haveI := (h.quotient_hypotheses hemb hσ hfree hm).2.1
  haveI := (h.quotient_hypotheses hemb hσ hfree hm).2.2
  ProperSMul.orbitRelQuotientChartedSpace I G 𝓘(ℝ, Fin m → ℝ) (h.orbitLevel η)

/-- **The reduced space at the orbit is a smooth manifold**, for the atlas
`orbitLevelQuotientChartedSpace`. -/
theorem isManifold_orbitLevelQuotient :
    letI := h.orbitLevelQuotientChartedSpace hemb hσ hfree hm
    IsManifold 𝓘(ℝ, ProperSMul.QuotientModelSpace E (Fin m → ℝ)) ∞
      (MulAction.orbitRel.Quotient G (h.orbitLevel η)) := by
  let := h.orbitLevelChartedSpace hemb hσ hfree hm
  obtain ⟨_, _, _⟩ := h.quotient_hypotheses hemb hσ hfree hm
  exact ProperSMul.instIsManifoldOrbitRelQuotient

/-- **The orbit projection `Q → Q / G` is a smooth submersion**, for the atlases
`orbitLevelChartedSpace` and `orbitLevelQuotientChartedSpace`. -/
theorem isSubmersion_quotientMk_orbitLevel :
    letI := h.orbitLevelChartedSpace hemb hσ hfree hm
    letI := h.orbitLevelQuotientChartedSpace hemb hσ hfree hm
    Manifold.IsSubmersion 𝓘(ℝ, Fin m → ℝ) 𝓘(ℝ, ProperSMul.QuotientModelSpace E (Fin m → ℝ)) ∞
      (Quotient.mk (MulAction.orbitRel G (h.orbitLevel η))) := by
  let := h.orbitLevelChartedSpace hemb hσ hfree hm
  obtain ⟨_, _, _⟩ := h.quotient_hypotheses hemb hσ hfree hm
  exact ProperSMul.isSubmersion_quotientMk

include hemb hσ hfree hm in
/-- The atlas of the quotient by `G` of the zero level of the product moment map
`(x, q) ↦ μ x + ι q` on `M × (G ⧸ G_η)`: the atlas `zeroLevelQuotientChartedSpace` of the product
form, for the atlas `zeroLevelProdChartedSpace` of that level, with properness from
`properSMul_zeroLevel_prod`. -/
@[instance_reducible]
def zeroLevelProdQuotientChartedSpace :
    ChartedSpace (ProperSMul.QuotientModelSpace E (Fin m → ℝ))
      (MulAction.orbitRel.Quotient G
        (h.prod η.isEquivariantMomentMap_coadjointOrbitForm).zeroLevel) :=
  haveI : T2Space (G ⧸ (Lie.coadjointRepresentation ℝ I G).stabilizer η) := hemb.t2Space
  haveI := h.properSMul_zeroLevel_prod hemb
  (h.prod η.isEquivariantMomentMap_coadjointOrbitForm).zeroLevelQuotientChartedSpace
    (hσ.prod η.isSymplectic_coadjointOrbitForm.isNondegenerate)
    (h.stabilizer_zeroLevel_prod_eq_bot η hfree) (n := m) (by rwa [Module.finrank_prod])

/-- The quotient by `G` of the zero level of the product moment map is a smooth manifold, for the
atlas `zeroLevelProdQuotientChartedSpace`. -/
theorem isManifold_zeroLevelProdQuotient :
    letI := h.zeroLevelProdQuotientChartedSpace hemb hσ hfree hm
    IsManifold 𝓘(ℝ, ProperSMul.QuotientModelSpace E (Fin m → ℝ)) ∞
      (MulAction.orbitRel.Quotient G
        (h.prod η.isEquivariantMomentMap_coadjointOrbitForm).zeroLevel) :=
  haveI : T2Space (G ⧸ (Lie.coadjointRepresentation ℝ I G).stabilizer η) := hemb.t2Space
  haveI := h.properSMul_zeroLevel_prod hemb
  (h.prod η.isEquivariantMomentMap_coadjointOrbitForm).isManifold_zeroLevelQuotient
    (hσ.prod η.isSymplectic_coadjointOrbitForm.isNondegenerate)
    (h.stabilizer_zeroLevel_prod_eq_bot η hfree) (n := m) (by rwa [Module.finrank_prod])

/-- The orbit projection of the zero level of the product moment map onto its quotient by `G` is
a smooth submersion, for the atlases `zeroLevelProdChartedSpace` and
`zeroLevelProdQuotientChartedSpace`. -/
theorem isSubmersion_quotientMk_zeroLevelProd :
    letI := h.zeroLevelProdChartedSpace hemb hσ hfree hm
    letI := h.zeroLevelProdQuotientChartedSpace hemb hσ hfree hm
    Manifold.IsSubmersion 𝓘(ℝ, Fin m → ℝ) 𝓘(ℝ, ProperSMul.QuotientModelSpace E (Fin m → ℝ)) ∞
      (Quotient.mk (MulAction.orbitRel G
        (h.prod η.isEquivariantMomentMap_coadjointOrbitForm).zeroLevel)) :=
  haveI : T2Space (G ⧸ (Lie.coadjointRepresentation ℝ I G).stabilizer η) := hemb.t2Space
  haveI := h.properSMul_zeroLevel_prod hemb
  (h.prod η.isEquivariantMomentMap_coadjointOrbitForm).isSubmersion_quotientMk_zeroLevel
    (hσ.prod η.isSymplectic_coadjointOrbitForm.isNondegenerate)
    (h.stabilizer_zeroLevel_prod_eq_bot η hfree) (n := m) (by rwa [Module.finrank_prod])

/-- **The two reduced spaces are diffeomorphic.** The graph `orbitLevelGraphDiffeomorph` is
`G`-equivariant, so it descends to a diffeomorphism from the reduced space `Q / G` at the orbit
onto the quotient by `G` of the zero level of the product moment map on `M × (G ⧸ G_η)`
(`ProperSMul.orbitRelQuotientDiffeomorph`). -/
def orbitLevelQuotientDiffeomorph :
    letI := h.orbitLevelQuotientChartedSpace hemb hσ hfree hm
    letI := h.zeroLevelProdQuotientChartedSpace hemb hσ hfree hm
    MulAction.orbitRel.Quotient G (h.orbitLevel η) ≃ₘ⟮𝓘(ℝ, ProperSMul.QuotientModelSpace E
        (Fin m → ℝ)), 𝓘(ℝ, ProperSMul.QuotientModelSpace E (Fin m → ℝ))⟯
      MulAction.orbitRel.Quotient G
        (h.prod η.isEquivariantMomentMap_coadjointOrbitForm).zeroLevel :=
  letI := h.orbitLevelChartedSpace hemb hσ hfree hm
  letI := h.zeroLevelProdChartedSpace hemb hσ hfree hm
  haveI := (h.quotient_hypotheses hemb hσ hfree hm).1
  haveI := (h.quotient_hypotheses hemb hσ hfree hm).2.1
  haveI := (h.quotient_hypotheses hemb hσ hfree hm).2.2
  haveI : T2Space (G ⧸ (Lie.coadjointRepresentation ℝ I G).stabilizer η) := hemb.t2Space
  haveI := h.properSMul_zeroLevel_prod hemb
  haveI := h.isManifold_zeroLevelProd hemb hσ hfree hm
  haveI : ContMDiffSMul I 𝓘(ℝ, Fin m → ℝ) ∞ G
      (h.prod η.isEquivariantMomentMap_coadjointOrbitForm).zeroLevel :=
    (h.prod η.isEquivariantMomentMap_coadjointOrbitForm).contMDiffSMul_zeroLevel
    (hσ.prod η.isSymplectic_coadjointOrbitForm.isNondegenerate)
    (h.stabilizer_zeroLevel_prod_eq_bot η hfree) (n := m) (by rwa [Module.finrank_prod])
  haveI := (h.prod η.isEquivariantMomentMap_coadjointOrbitForm).isCancelSMul_zeroLevel
    (h.stabilizer_zeroLevel_prod_eq_bot η hfree)
  ProperSMul.orbitRelQuotientDiffeomorph I I le_rfl (MulEquiv.refl G)
    (h.orbitLevelGraphDiffeomorph hemb hσ hfree hm) fun g x ↦ by
      rw [coe_orbitLevelGraphDiffeomorph, orbitLevelGraph_smul, MulEquiv.refl_apply]

/-- `orbitLevelQuotientDiffeomorph` sends the class of `x` to the class of its graph. -/
theorem orbitLevelQuotientDiffeomorph_mk (x : h.orbitLevel η) :
    letI := h.orbitLevelQuotientChartedSpace hemb hσ hfree hm
    letI := h.zeroLevelProdQuotientChartedSpace hemb hσ hfree hm
    h.orbitLevelQuotientDiffeomorph hemb hσ hfree hm
        (Quotient.mk (MulAction.orbitRel G (h.orbitLevel η)) x) =
      Quotient.mk (MulAction.orbitRel G
        (h.prod η.isEquivariantMomentMap_coadjointOrbitForm).zeroLevel)
        (h.orbitLevelGraph hemb x) := by
  simp only [orbitLevelQuotientDiffeomorph, ProperSMul.orbitRelQuotientDiffeomorph_mk,
    coe_orbitLevelGraphDiffeomorph]

/-- **The reduced form of the product's zero level, carried to the reduced space at the orbit.**
Let `ωred` be a form on `Q / G` with `π_Q^* ωred = i^* σ + (orbitLevelProj)^* ω_O`, and `ωP` a
form on the quotient of the product's zero level with `π_P^* ωP = j^* (σ.prod ω_O)`, for the
inclusions `i` of `Q` into `M` and `j` of the level into `M × (G ⧸ G_η)`. Then
`orbitLevelQuotientDiffeomorph` pulls `ωP` back to `ωred`. -/
theorem mpullback_orbitLevelQuotientDiffeomorph :
    letI := h.orbitLevelChartedSpace hemb hσ hfree hm
    letI := h.orbitLevelQuotientChartedSpace hemb hσ hfree hm
    letI := h.zeroLevelProdChartedSpace hemb hσ hfree hm
    letI := h.zeroLevelProdQuotientChartedSpace hemb hσ hfree hm
    haveI := h.isManifold_orbitLevel hemb hσ hfree hm
    haveI := h.isManifold_orbitLevelQuotient hemb hσ hfree hm
    haveI := h.isManifold_zeroLevelProd hemb hσ hfree hm
    haveI := h.isManifold_zeroLevelProdQuotient hemb hσ hfree hm
    ∀ (ωred : SmoothTwoForm 𝓘(ℝ, ProperSMul.QuotientModelSpace E (Fin m → ℝ))
        (MulAction.orbitRel.Quotient G (h.orbitLevel η)))
      (ωP : SmoothTwoForm 𝓘(ℝ, ProperSMul.QuotientModelSpace E (Fin m → ℝ))
        (MulAction.orbitRel.Quotient G
          (h.prod η.isEquivariantMomentMap_coadjointOrbitForm).zeroLevel)),
      SmoothForm.mpullback _
          (h.isSubmersion_quotientMk_orbitLevel hemb hσ hfree hm).contMDiff ωred =
          SmoothForm.mpullback Subtype.val
              (h.isSmoothEmbedding_coe_orbitLevel hemb hσ hfree hm).contMDiff σ +
            SmoothForm.mpullback (h.orbitLevelProj hemb)
              (h.contMDiff_orbitLevelProj hemb hσ hfree hm) η.coadjointOrbitForm →
      SmoothForm.mpullback _
          (h.isSubmersion_quotientMk_zeroLevelProd hemb hσ hfree hm).contMDiff ωP =
          SmoothForm.mpullback Subtype.val
            (h.isSmoothEmbedding_coe_zeroLevelProd hemb hσ hfree hm).contMDiff
            (σ.prod η.coadjointOrbitForm) →
      SmoothForm.mpullback _ (h.orbitLevelQuotientDiffeomorph hemb hσ hfree hm).contMDiff ωP =
        ωred := by
  let := h.orbitLevelChartedSpace hemb hσ hfree hm
  let := h.orbitLevelQuotientChartedSpace hemb hσ hfree hm
  let := h.zeroLevelProdChartedSpace hemb hσ hfree hm
  let := h.zeroLevelProdQuotientChartedSpace hemb hσ hfree hm
  have := h.isManifold_orbitLevel hemb hσ hfree hm
  have := h.isManifold_orbitLevelQuotient hemb hσ hfree hm
  have := h.isManifold_zeroLevelProd hemb hσ hfree hm
  have := h.isManifold_zeroLevelProdQuotient hemb hσ hfree hm
  have : T2Space (G ⧸ (Lie.coadjointRepresentation ℝ I G).stabilizer η) := hemb.t2Space
  intro ωred ωP hred hω
  have hπ := h.isSubmersion_quotientMk_orbitLevel hemb hσ hfree hm
  have hj := h.isSmoothEmbedding_coe_zeroLevelProd hemb hσ hfree hm
  have hg := h.contMDiff_orbitLevelGraph hemb hσ hfree hm
  exact SmoothForm.mpullback_eq_of_mpullback_eq (hj.contMDiff.comp hg) hπ.contMDiff hj.contMDiff
    (h.isSubmersion_quotientMk_zeroLevelProd hemb hσ hfree hm).contMDiff
    (hred.trans (h.mpullback_orbitLevelGraph_prod hemb hσ hfree hm).symm) hω
    Quotient.mk_surjective (fun z ↦ hπ.surjective_mfderiv (by simp) z) hg
    (SmoothForm.mpullback_mpullback _ _ _ _ _) _
    (funext (h.orbitLevelQuotientDiffeomorph_mk hemb hσ hfree hm))

/-- **The reduced form at a coadjoint orbit.** Let `G` act smoothly by symplectomorphisms on a
symplectic manifold `(M, σ)`, with coadjoint-equivariant moment map `μ`, let the orbit map `ι` of
`η` be a topological embedding, and let `G` act freely and properly on the preimage `Q` of the
orbit. Then the reduced space `Q / G` carries a unique symplectic form `ω_red` with
`π^* ω_red = i^* σ + (orbitLevelProj)^* ω_O`, for the orbit projection `π : Q → Q / G`, the
inclusion `i : Q → M`, the map `orbitLevelProj : Q → G ⧸ G_η` and the KKS form `ω_O` of the
orbit. -/
theorem existsUnique_isSymplectic_mpullback_quotientMk_orbitLevel_eq_mpullback_add_mpullback
    (hσ : σ.IsSymplectic)
    (hG : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ) :
    letI := h.orbitLevelChartedSpace hemb hσ.isNondegenerate hfree hm
    letI := h.orbitLevelQuotientChartedSpace hemb hσ.isNondegenerate hfree hm
    haveI := h.isManifold_orbitLevel hemb hσ.isNondegenerate hfree hm
    haveI := h.isManifold_orbitLevelQuotient hemb hσ.isNondegenerate hfree hm
    ∃! ωred : SmoothTwoForm 𝓘(ℝ, ProperSMul.QuotientModelSpace E (Fin m → ℝ))
        (MulAction.orbitRel.Quotient G (h.orbitLevel η)),
      ωred.IsSymplectic ∧
        SmoothForm.mpullback _
            (h.isSubmersion_quotientMk_orbitLevel hemb hσ.isNondegenerate hfree hm).contMDiff ωred =
          SmoothForm.mpullback Subtype.val
              (h.isSmoothEmbedding_coe_orbitLevel hemb hσ.isNondegenerate hfree hm).contMDiff σ +
            SmoothForm.mpullback (h.orbitLevelProj hemb)
              (h.contMDiff_orbitLevelProj hemb hσ.isNondegenerate hfree hm)
              η.coadjointOrbitForm := by
  let := h.orbitLevelChartedSpace hemb hσ.isNondegenerate hfree hm
  let := h.orbitLevelQuotientChartedSpace hemb hσ.isNondegenerate hfree hm
  let := h.zeroLevelProdChartedSpace hemb hσ.isNondegenerate hfree hm
  let := h.zeroLevelProdQuotientChartedSpace hemb hσ.isNondegenerate hfree hm
  have := h.isManifold_orbitLevel hemb hσ.isNondegenerate hfree hm
  have := h.isManifold_orbitLevelQuotient hemb hσ.isNondegenerate hfree hm
  have := h.isManifold_zeroLevelProd hemb hσ.isNondegenerate hfree hm
  have := h.isManifold_zeroLevelProdQuotient hemb hσ.isNondegenerate hfree hm
  have : T2Space (G ⧸ (Lie.coadjointRepresentation ℝ I G).stabilizer η) := hemb.t2Space
  have := h.properSMul_zeroLevel_prod hemb
  -- The reduced form of the product's zero level, pulled back along the diffeomorphism.
  obtain ⟨ωP, ⟨hωs, hω⟩, -⟩ :=
    (h.prod η.isEquivariantMomentMap_coadjointOrbitForm)
      |>.existsUnique_isSymplectic_mpullback_quotientMk_zeroLevel_eq_mpullback
      (hσ.prod η.isSymplectic_coadjointOrbitForm)
      (fun g ↦ mpullback_smul_prod (IG := I) g (hG g) (η.mpullback_smul_coadjointOrbitForm g
        (ContMDiffSMul.contMDiff_const_smul (I := I) g)))
      (h.stabilizer_zeroLevel_prod_eq_bot η hfree) (n := m) (by rwa [Module.finrank_prod])
  let D := h.orbitLevelQuotientDiffeomorph hemb hσ.isNondegenerate hfree hm
  have hD := h.mpullback_orbitLevelQuotientDiffeomorph hemb hσ.isNondegenerate hfree hm
  have hπ := h.isSubmersion_quotientMk_orbitLevel hemb hσ.isNondegenerate hfree hm
  have hπP := h.isSubmersion_quotientMk_zeroLevelProd hemb hσ.isNondegenerate hfree hm
  have hg := h.contMDiff_orbitLevelGraph hemb hσ.isNondegenerate hfree hm
  refine ⟨SmoothForm.mpullback D D.contMDiff ωP,
    ⟨(D.isLocalDiffeomorph.isSymplectic_mpullback_iff D.surjective).2 hωs, ?_⟩,
    fun ω₁ hω₁ ↦ (hD ω₁ ωP hω₁.2 hω).symm⟩
  -- `π_Q^* D^* ω = graph^* π_P^* ω = graph^* j^* (σ.prod ω_O)`.
  rw [SmoothForm.mpullback_mpullback_of_comp_eq hπ.contMDiff D.contMDiff hg hπP.contMDiff
      (funext (h.orbitLevelQuotientDiffeomorph_mk hemb hσ.isNondegenerate hfree hm)),
    hω, SmoothForm.mpullback_mpullback, h.mpullback_orbitLevelGraph_prod]

include hemb hσ hfree hm in
/-- **The dimension of the reduced space at a coadjoint orbit.** If the preimage `Q` of the orbit
`O` of `η` has a point, then `dim (Q / G) + 2 dim 𝔤 = dim M + dim O`. -/
theorem finrank_quotientModelSpace_orbitLevel (x : h.orbitLevel η) :
    finrank ℝ (ProperSMul.QuotientModelSpace E (Fin m → ℝ)) +
        2 * finrank ℝ (GroupLieAlgebra I G) =
      finrank ℝ E' + finrank ℝ (Subgroup.QuotientModelSpace I
        ((Lie.coadjointRepresentation ℝ I G).stabilizer η)) := by
  have : T2Space (G ⧸ (Lie.coadjointRepresentation ℝ I G).stabilizer η) := hemb.t2Space
  have := h.properSMul_zeroLevel_prod hemb
  rw [← Module.finrank_prod]
  exact (h.prod η.isEquivariantMomentMap_coadjointOrbitForm).finrank_quotientModelSpace_zeroLevel
    (hσ.prod η.isSymplectic_coadjointOrbitForm.isNondegenerate)
    (h.stabilizer_zeroLevel_prod_eq_bot η hfree) (n := m) (by rwa [Module.finrank_prod])
    (h.orbitLevelGraph hemb x)

end Quotient

end IsEquivariantMomentMap

end SmoothTwoForm

end TauCeti

namespace SymplecticGeometry

open TauCeti TauCeti.SmoothTwoForm TauCeti.SmoothTwoForm.IsEquivariantMomentMap

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M] [T2Space M]
  [MulAction G M] [ContMDiffSMul I I' ∞ G M] {m : ℕ}

/-- **Reduction at a coadjoint orbit.** Let a connected Lie group `G` act smoothly by
symplectomorphisms on a symplectic manifold `(M, σ)` with coadjoint-equivariant moment map `μ`, in
the sign where `d⟨μ, ξ⟩ = -ι_{ξ_M} σ` (so that `fun x ↦ -μ x` is a moment map in Tau Ceti's sign).
Let `η ∈ 𝔤*` have an embedded coadjoint orbit `O`, with orbit map `ι : G ⧸ G_η → 𝔤*` and KKS form
`ω_O`, and let `G` act freely and properly on `Q = μ⁻¹(O)`. Then, for the atlases of
`Q` (`orbitLevelChartedSpace`, of dimension `m = dim M + dim O - dim 𝔤`), of `Q / G`, and of the
quotient of the zero level `P` of the moment map `(x, q) ↦ ι q - μ x` of `σ.prod ω_O` on `M × O`:
1. `dμ` is onto at every point of `Q`, so that `μ` is transverse to `O`;
2. `Q` is a manifold and its inclusion `i` into `M` is a smooth embedding;
3. `Q / G` is a manifold with a unique symplectic form `ω_red` such that
   `π^* ω_red = i^* σ + (μ|_Q)^* ω_O`, for the orbit projection `π` and the map
   `μ|_Q = orbitLevelProj : Q → G ⧸ G_η`;
4. if `Q` is nonempty, `dim (Q / G) + 2 dim 𝔤 = dim M + dim O`;
5. the diffeomorphism `orbitLevelQuotientDiffeomorph : Q / G → P / G` pulls the reduced form of
   `P / G` back to that of `Q / G`.

Milestone: *Reduction at a coadjoint orbit and the shifting construction*. -/
theorem symplecticReduction_coadjointOrbit [ConnectedSpace G] {σ : SmoothTwoForm I' M}
    {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)} (hσ : σ.IsSymplectic)
    (hG : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ)
    (h : σ.IsEquivariantMomentMap fun x ↦ -μ x) (η : Module.Dual ℝ (GroupLieAlgebra I G))
    (hemb : Topology.IsEmbedding fun q : G ⧸ (Lie.coadjointRepresentation ℝ I G).stabilizer η ↦
      ⇑((Lie.coadjointRepresentation ℝ I G).orbitMap η q))
    (hfree : ∀ x, μ x ∈ Set.range ((Lie.coadjointRepresentation ℝ I G).orbitMap η) →
      MulAction.stabilizer G x = ⊥)
    [ProperSMul G (h.orbitLevel η)]
    (hm : finrank ℝ E' + finrank ℝ (Subgroup.QuotientModelSpace I
      ((Lie.coadjointRepresentation ℝ I G).stabilizer η)) - finrank ℝ (GroupLieAlgebra I G) = m) :
    have hfree' : ∀ x ∈ h.orbitLevel η, MulAction.stabilizer G x = ⊥ :=
      fun x hx ↦ hfree x (by simpa using hx)
    letI := h.orbitLevelChartedSpace hemb hσ.isNondegenerate hfree' hm
    letI := h.orbitLevelQuotientChartedSpace hemb hσ.isNondegenerate hfree' hm
    letI := h.zeroLevelProdChartedSpace hemb hσ.isNondegenerate hfree' hm
    letI := h.zeroLevelProdQuotientChartedSpace hemb hσ.isNondegenerate hfree' hm
    haveI := h.isManifold_orbitLevel hemb hσ.isNondegenerate hfree' hm
    haveI := h.isManifold_orbitLevelQuotient hemb hσ.isNondegenerate hfree' hm
    haveI := h.isManifold_zeroLevelProd hemb hσ.isNondegenerate hfree' hm
    haveI := h.isManifold_zeroLevelProdQuotient hemb hσ.isNondegenerate hfree' hm
    (∀ x, μ x ∈ Set.range ((Lie.coadjointRepresentation ℝ I G).orbitMap η) →
      Function.Surjective (h.differential x)) ∧
    (IsManifold 𝓘(ℝ, Fin m → ℝ) ∞ (h.orbitLevel η) ∧
      Manifold.IsSmoothEmbedding 𝓘(ℝ, Fin m → ℝ) I' ∞ (Subtype.val : h.orbitLevel η → M)) ∧
    (IsManifold 𝓘(ℝ, ProperSMul.QuotientModelSpace E (Fin m → ℝ)) ∞
        (MulAction.orbitRel.Quotient G (h.orbitLevel η)) ∧
      ∃! ωred : SmoothTwoForm 𝓘(ℝ, ProperSMul.QuotientModelSpace E (Fin m → ℝ))
          (MulAction.orbitRel.Quotient G (h.orbitLevel η)),
        ωred.IsSymplectic ∧
          SmoothForm.mpullback _
              (h.isSubmersion_quotientMk_orbitLevel hemb hσ.isNondegenerate hfree' hm).contMDiff
              ωred =
            SmoothForm.mpullback Subtype.val
                (h.isSmoothEmbedding_coe_orbitLevel hemb hσ.isNondegenerate hfree' hm).contMDiff σ +
              SmoothForm.mpullback (h.orbitLevelProj hemb)
                (h.contMDiff_orbitLevelProj hemb hσ.isNondegenerate hfree' hm)
                η.coadjointOrbitForm) ∧
    (Nonempty (h.orbitLevel η) →
      finrank ℝ (ProperSMul.QuotientModelSpace E (Fin m → ℝ)) +
          2 * finrank ℝ (GroupLieAlgebra I G) =
        finrank ℝ E' + finrank ℝ (Subgroup.QuotientModelSpace I
          ((Lie.coadjointRepresentation ℝ I G).stabilizer η))) ∧
    ∀ (ωred : SmoothTwoForm 𝓘(ℝ, ProperSMul.QuotientModelSpace E (Fin m → ℝ))
        (MulAction.orbitRel.Quotient G (h.orbitLevel η)))
      (ωP : SmoothTwoForm 𝓘(ℝ, ProperSMul.QuotientModelSpace E (Fin m → ℝ))
        (MulAction.orbitRel.Quotient G
          (h.prod η.isEquivariantMomentMap_coadjointOrbitForm).zeroLevel)),
      SmoothForm.mpullback _
          (h.isSubmersion_quotientMk_orbitLevel hemb hσ.isNondegenerate hfree' hm).contMDiff ωred =
          SmoothForm.mpullback Subtype.val
              (h.isSmoothEmbedding_coe_orbitLevel hemb hσ.isNondegenerate hfree' hm).contMDiff σ +
            SmoothForm.mpullback (h.orbitLevelProj hemb)
              (h.contMDiff_orbitLevelProj hemb hσ.isNondegenerate hfree' hm) η.coadjointOrbitForm →
      SmoothForm.mpullback _
          (h.isSubmersion_quotientMk_zeroLevelProd hemb hσ.isNondegenerate hfree' hm).contMDiff ωP =
          SmoothForm.mpullback Subtype.val
            (h.isSmoothEmbedding_coe_zeroLevelProd hemb hσ.isNondegenerate hfree' hm).contMDiff
            (σ.prod η.coadjointOrbitForm) →
      SmoothForm.mpullback _
          (h.orbitLevelQuotientDiffeomorph hemb hσ.isNondegenerate hfree' hm).contMDiff ωP =
        ωred := by
  intro hfree'
  exact ⟨fun x hx ↦ h.differential_surjective_of_mem_orbitLevel η hσ.isNondegenerate hfree' x
      (by simpa using hx),
    ⟨h.isManifold_orbitLevel hemb hσ.isNondegenerate hfree' hm,
      h.isSmoothEmbedding_coe_orbitLevel hemb hσ.isNondegenerate hfree' hm⟩,
    ⟨h.isManifold_orbitLevelQuotient hemb hσ.isNondegenerate hfree' hm,
      h.existsUnique_isSymplectic_mpullback_quotientMk_orbitLevel_eq_mpullback_add_mpullback hemb
        hfree' hm hσ hG⟩,
    fun ⟨x⟩ ↦ h.finrank_quotientModelSpace_orbitLevel hemb hσ.isNondegenerate hfree' hm x,
    h.mpullback_orbitLevelQuotientDiffeomorph hemb hσ.isNondegenerate hfree' hm⟩

end SymplecticGeometry

end

end
