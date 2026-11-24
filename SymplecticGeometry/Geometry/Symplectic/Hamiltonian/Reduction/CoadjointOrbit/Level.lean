/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Homeomorph.Lemmas
public import TauCeti.Geometry.Manifold.PullbackGroupoid
public import TauCeti.Geometry.Symplectic.Coadjoint.Orbit
public import TauCeti.Geometry.Symplectic.Hamiltonian.EquivariantMomentMap.Prod
public import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.Reduction.ZeroLevel.Basic

/-!
# The preimage of an embedded coadjoint orbit under a moment map

Consider a smooth action of a Lie group `G` on `(M, σ)` with coadjoint-equivariant moment map
`μ : M → 𝔤*` (`TauCeti.SmoothTwoForm.IsEquivariantMomentMap`, in Tau Ceti's sign), and fix
`η : 𝔤*`. Write `O = G ⧸ G_η` for the coadjoint orbit of `η` as a manifold, with its orbit map
`ι = (Lie.coadjointRepresentation ℝ I G).orbitMap η` and its KKS form
`Module.Dual.coadjointOrbitForm η`, of which `ι` is an equivariant moment map. On the product
`M × O` with the form `σ.prod η.coadjointOrbitForm`, the map `(x, q) ↦ μ x + ι q` is then an
equivariant moment map (`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.prod`), whose zero level is
the graph of `x ↦ ι⁻¹(-μ x)` over the points `x` with `-μ x` in the orbit.

This file is the passage from the preimage `Q` of the orbit to that zero level, the first step
of reduction at a coadjoint orbit through the product:

* `orbitLevel`: the points `x` with `-μ x ∈ O`, as a `SubMulAction` of `G`. In the opposite
  sign convention, where the moment map is `-μ`, this is the preimage of the orbit `O`.
  `properSMul_orbitLevel`: a proper action on `M` restricts to it.
* `orbitLevelGraph`: if `ι` is a topological embedding into `𝔤 → ℝ`, the graph map
  `x ↦ (x, ι⁻¹(-μ x))` is a homeomorphism from `Q` onto the zero level of the product, with
  inverse the first projection; it is `G`-equivariant (`orbitLevelGraph_smul`).
* `stabilizer_zeroLevel_prod_eq_bot` and `properSMul_zeroLevel_prod`: freeness on `Q` gives
  freeness at every point of the product's zero level, and properness on `Q` gives properness on
  that level, so the zero-level results of `ZeroLevel/Basic.lean` apply to the product.
* `differential_surjective_of_mem_orbitLevel`: freeness on `Q` makes `dμ` onto at every point of
  `Q`, so that `μ` is transverse to the orbit there.
* `orbitLevelProj`: the map `x ↦ ι⁻¹(-μ x)` from `Q` to the orbit, the second component of the
  graph (`coe_orbitLevelGraph`); it is `G`-equivariant (`orbitLevelProj_smul`).
* `zeroLevelProdChartedSpace`: if moreover `M` is boundaryless and Hausdorff, `σ` is
  nondegenerate and `G` acts freely on `Q`, the atlas `zeroLevelChartedSpace` of the product's
  zero level for the product form, modelled on `Fin m → ℝ`, `m = dim M + dim O - dim 𝔤`.
* `orbitLevelChartedSpace`, `isManifold_orbitLevel`: under the same hypotheses `Q` is a manifold,
  with that atlas carried over by the graph (Tau Ceti's `Homeomorph.pullbackChartedSpace`).
  `orbitLevelGraphDiffeomorph`: the graph is then a diffeomorphism onto that level, and
  `contMDiffSMul_orbitLevel`, `contMDiff_orbitLevelProj`: the action of `G` on `Q` and the map
  `orbitLevelProj` are smooth.

All declarations are in the namespace `TauCeti.SmoothTwoForm.IsEquivariantMomentMap`, beside
`zeroLevel`. The proof of `properSMul_orbitLevel` is that of `properSMul_zeroLevel`, adapted from
Tau Ceti's `properSMul_levelSubMulAction`.

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

/-! ### The preimage of the orbit as a `G`-space -/

/-- **The preimage of a coadjoint orbit.** For a covector `η`, the points `x` such that `-μ x`
lies in the coadjoint orbit of `η`, that is, in the range of the orbit map
`ι = (Lie.coadjointRepresentation ℝ I G).orbitMap η`, as a `SubMulAction` of `G`: it is invariant
since `μ` and `ι` are equivariant. The sign is chosen so that this is the preimage of the orbit
for the moment map `-μ` of the opposite convention, and so that it is the set of first components
of the zero level of the product moment map `(x, q) ↦ μ x + ι q` on `M × (G ⧸ G_η)`. -/
def orbitLevel (h : σ.IsEquivariantMomentMap μ) (η : Module.Dual ℝ (GroupLieAlgebra I G)) :
    SubMulAction G M where
  carrier := {x | -μ x ∈ Set.range ((Lie.coadjointRepresentation ℝ I G).orbitMap η)}
  smul_mem' g x := by
    rintro ⟨q, hq⟩
    refine ⟨g • q, ?_⟩
    rw [Representation.orbitMap_smul, hq, h.apply_smul, map_neg]

variable (h : σ.IsEquivariantMomentMap μ) (η : Module.Dual ℝ (GroupLieAlgebra I G))

/-- A point lies in the preimage of the orbit of `η` exactly when `-μ x` is in the range of the
orbit map. -/
@[simp]
theorem mem_orbitLevel {x : M} :
    x ∈ h.orbitLevel η ↔ -μ x ∈ Set.range ((Lie.coadjointRepresentation ℝ I G).orbitMap η) :=
  Iff.rfl

/-- **Properness on the preimage of the orbit.** If `G` acts properly on `M`, it acts properly on
the preimage of the orbit of `η`. -/
theorem properSMul_orbitLevel [ProperSMul G M] : ProperSMul G (h.orbitLevel η) :=
  Topology.IsEmbedding.subtypeVal.properSMul fun g x ↦ SubMulAction.val_smul g x

/-- **Freeness on the product's zero level.** If `G` acts freely at every point of the preimage
of the orbit of `η`, it acts freely at every point of the zero level of the product moment map
`(x, q) ↦ μ x + ι q`. -/
theorem stabilizer_zeroLevel_prod_eq_bot
    (hfree : ∀ x ∈ h.orbitLevel η, MulAction.stabilizer G x = ⊥)
    (p : M × (G ⧸ (Lie.coadjointRepresentation ℝ I G).stabilizer η))
    (hp : μ p.1 + (Lie.coadjointRepresentation ℝ I G).orbitMap η p.2 = 0) :
    MulAction.stabilizer G p = ⊥ := by
  rw [eq_bot_iff, ← hfree p.1 ⟨p.2, (neg_eq_of_add_eq_zero_right hp).symm⟩]
  intro g hg
  rw [MulAction.mem_stabilizer_iff] at hg ⊢
  rw [← Prod.smul_fst, hg]

/-- **Regularity on the preimage of the orbit.** If the form is nondegenerate and `G` acts freely
at every point of the preimage of the orbit of `η`, then `dμ` is onto at each of its points. -/
theorem differential_surjective_of_mem_orbitLevel [BoundarylessManifold I' M] [T2Space M]
    (hσ : σ.IsNondegenerate) (hfree : ∀ x ∈ h.orbitLevel η, MulAction.stabilizer G x = ⊥) :
    ∀ x ∈ h.orbitLevel η, Function.Surjective (h.differential x) :=
  fun x hx ↦ h.toIsMomentMap.differential_surjective_of_stabilizer_eq_bot
    (hσ.nondegenerate_bilinFormAt x) (hfree x hx)

/-! ### The graph over the preimage of the orbit -/

section Graph

variable {η}
  (hemb : Topology.IsEmbedding fun q : G ⧸ (Lie.coadjointRepresentation ℝ I G).stabilizer η ↦
    ⇑((Lie.coadjointRepresentation ℝ I G).orbitMap η q))

/-- The point `ι⁻¹(-μ x)` of the orbit, through the homeomorphism of the orbit with its image. -/
private def graphSnd (x : h.orbitLevel η) :
    G ⧸ (Lie.coadjointRepresentation ℝ I G).stabilizer η :=
  hemb.toHomeomorph.symm ⟨⇑(-μ x), by
    obtain ⟨q, hq⟩ := x.property
    exact ⟨q, congrArg DFunLike.coe hq⟩⟩

private theorem orbitMap_graphSnd (x : h.orbitLevel η) :
    (Lie.coadjointRepresentation ℝ I G).orbitMap η (graphSnd h hemb x) = -μ x :=
  DFunLike.coe_injective <| by
    rw [graphSnd, ← Topology.IsEmbedding.toHomeomorph_apply_coe hemb, Homeomorph.apply_symm_apply]

private theorem continuous_graphSnd : Continuous (graphSnd h hemb) := by
  refine hemb.toHomeomorph.symm.continuous.comp (Continuous.subtype_mk (continuous_pi fun ξ ↦ ?_) _)
  simp only [LinearMap.neg_apply]
  exact continuous_neg.comp ((h.toIsMomentMap.contMDiff ξ).continuous.comp continuous_subtypeVal)

variable [I.Boundaryless]

/-- The first component of a point of the zero level of the product moment map
`(x, q) ↦ μ x + ι q` lies in the preimage of the orbit. -/
theorem fst_mem_orbitLevel_of_mem_zeroLevel
    {p : M × (G ⧸ (Lie.coadjointRepresentation ℝ I G).stabilizer η)}
    (hp : p ∈ (h.prod η.isEquivariantMomentMap_coadjointOrbitForm).zeroLevel) :
    p.1 ∈ h.orbitLevel η :=
  ⟨p.2, (neg_eq_of_add_eq_zero_right
    ((h.prod η.isEquivariantMomentMap_coadjointOrbitForm).mem_zeroLevel.1 hp)).symm⟩

/-- **The graph over the preimage of an embedded orbit.** If the orbit map `ι` of `η` is a
topological embedding into `𝔤 → ℝ`, the map `x ↦ (x, ι⁻¹(-μ x))` is a homeomorphism from the
preimage of the orbit onto the zero level of the product moment map `(x, q) ↦ μ x + ι q` on
`M × (G ⧸ G_η)`, with inverse the first projection. -/
def orbitLevelGraph :
    h.orbitLevel η ≃ₜ (h.prod η.isEquivariantMomentMap_coadjointOrbitForm).zeroLevel where
  toFun x := ⟨((x : M), graphSnd h hemb x),
    (h.prod η.isEquivariantMomentMap_coadjointOrbitForm).mem_zeroLevel.2 <| by
      rw [orbitMap_graphSnd, add_neg_cancel]⟩
  invFun p := ⟨p.val.1, h.fst_mem_orbitLevel_of_mem_zeroLevel p.property⟩
  left_inv _ := rfl
  right_inv p := by
    refine Subtype.ext (Prod.ext rfl ((Lie.coadjointRepresentation ℝ I G).orbitMap_injective η ?_))
    rw [orbitMap_graphSnd]
    exact neg_eq_of_add_eq_zero_right
      ((h.prod η.isEquivariantMomentMap_coadjointOrbitForm).mem_zeroLevel.1 p.property)
  continuous_toFun := (continuous_subtypeVal.prodMk (continuous_graphSnd h hemb)).subtype_mk _
  continuous_invFun := (continuous_fst.comp continuous_subtypeVal).subtype_mk _

/-- The first component of the graph of `x` is `x`. -/
@[simp]
theorem orbitLevelGraph_fst (x : h.orbitLevel η) :
    (h.orbitLevelGraph hemb x).val.1 = x :=
  (rfl)

/-- The second component of the graph of `x` is the point of the orbit with `ι q = -μ x`. -/
@[simp]
theorem orbitMap_orbitLevelGraph_snd (x : h.orbitLevel η) :
    (Lie.coadjointRepresentation ℝ I G).orbitMap η (h.orbitLevelGraph hemb x).val.2 = -μ x :=
  orbitMap_graphSnd h hemb x

/-- The inverse of the graph is the first projection. -/
@[simp]
theorem coe_orbitLevelGraph_symm_apply
    (p : (h.prod η.isEquivariantMomentMap_coadjointOrbitForm).zeroLevel) :
    ((h.orbitLevelGraph hemb).symm p : M) = p.val.1 :=
  (rfl)

/-- **The graph is equivariant**: it intertwines the action of `G` on the preimage of the orbit
with the diagonal action on the product's zero level. -/
theorem orbitLevelGraph_smul (g : G) (x : h.orbitLevel η) :
    h.orbitLevelGraph hemb (g • x) = g • h.orbitLevelGraph hemb x := by
  refine Subtype.ext (Prod.ext rfl ((Lie.coadjointRepresentation ℝ I G).orbitMap_injective η ?_))
  rw [SubMulAction.val_smul, Prod.smul_snd, Representation.orbitMap_smul,
    orbitMap_orbitLevelGraph_snd, orbitMap_orbitLevelGraph_snd, SubMulAction.val_smul,
    h.apply_smul, map_neg]

include hemb in
/-- **Properness on the product's zero level.** If `G` acts properly on the preimage of an
embedded orbit, it acts properly on the zero level of the product moment map. -/
theorem properSMul_zeroLevel_prod [ProperSMul G (h.orbitLevel η)] :
    ProperSMul G (h.prod η.isEquivariantMomentMap_coadjointOrbitForm).zeroLevel :=
  (h.orbitLevelGraph hemb).symm.isEmbedding.properSMul fun g p ↦ by
    ext
    rw [coe_orbitLevelGraph_symm_apply, SubMulAction.val_smul, SubMulAction.val_smul,
      coe_orbitLevelGraph_symm_apply, Prod.smul_fst]

/-- The map from the preimage of an embedded orbit to the orbit, `x ↦ ι⁻¹(-μ x)`: the second
component of the graph `orbitLevelGraph`. -/
def orbitLevelProj (x : h.orbitLevel η) : G ⧸ (Lie.coadjointRepresentation ℝ I G).stabilizer η :=
  (h.orbitLevelGraph hemb x).val.2

/-- `orbitLevelProj` takes `x` to the second component of its graph. -/
theorem orbitLevelProj_apply (x : h.orbitLevel η) :
    h.orbitLevelProj hemb x = (h.orbitLevelGraph hemb x).val.2 :=
  (rfl)

/-- The point `orbitLevelProj x` of the orbit is sent by the orbit map to `-μ x`. -/
@[simp]
theorem orbitMap_orbitLevelProj (x : h.orbitLevel η) :
    (Lie.coadjointRepresentation ℝ I G).orbitMap η (h.orbitLevelProj hemb x) = -μ x := by
  rw [orbitLevelProj_apply, orbitMap_orbitLevelGraph_snd]

/-- The graph of `x` is the pair `(x, orbitLevelProj x)`. -/
theorem coe_orbitLevelGraph (x : h.orbitLevel η) :
    (h.orbitLevelGraph hemb x : M × (G ⧸ (Lie.coadjointRepresentation ℝ I G).stabilizer η)) =
      ((x : M), h.orbitLevelProj hemb x) :=
  (rfl)

/-- **`orbitLevelProj` is equivariant**: it intertwines the action of `G` on the preimage of the
orbit with its action on `G ⧸ G_η`. -/
theorem orbitLevelProj_smul (g : G) (x : h.orbitLevel η) :
    h.orbitLevelProj hemb (g • x) = g • h.orbitLevelProj hemb x := by
  simp only [orbitLevelProj_apply, orbitLevelGraph_smul, SubMulAction.val_smul, Prod.smul_snd]

/-! ### The atlas of the preimage of the orbit -/

section Atlas

/-! The atlas of the product's zero level is `zeroLevelChartedSpace` for the product form, which
is nondegenerate (`TauCeti.SmoothTwoForm.IsNondegenerate.prod`), with freeness from
`stabilizer_zeroLevel_prod_eq_bot`; the orbit is Hausdorff since it embeds into `𝔤 → ℝ`, and
`dim (M × O) = dim M + dim O` (`Module.finrank_prod`). -/

variable [I'.Boundaryless] [T2Space M] {m : ℕ} (hσ : σ.IsNondegenerate)
  (hfree : ∀ x ∈ h.orbitLevel η, MulAction.stabilizer G x = ⊥)
  (hm : finrank ℝ E' + finrank ℝ (Subgroup.QuotientModelSpace I
    ((Lie.coadjointRepresentation ℝ I G).stabilizer η)) - finrank ℝ (GroupLieAlgebra I G) = m)

include hσ hfree hm in
/-- The atlas of the zero level of the product moment map on `M × (G ⧸ G_η)`: the atlas
`zeroLevelChartedSpace` for the product form `σ.prod η.coadjointOrbitForm`, which is nondegenerate
when `σ` is, with freeness at every point of that level given by freeness on the preimage of the
orbit (`stabilizer_zeroLevel_prod_eq_bot`). It is modelled on `Fin m → ℝ` for
`m = dim M + dim (G ⧸ G_η) - dim 𝔤`. -/
@[instance_reducible]
def zeroLevelProdChartedSpace :
    ChartedSpace (Fin m → ℝ) (h.prod η.isEquivariantMomentMap_coadjointOrbitForm).zeroLevel :=
  haveI : T2Space (G ⧸ (Lie.coadjointRepresentation ℝ I G).stabilizer η) := hemb.t2Space
  (h.prod η.isEquivariantMomentMap_coadjointOrbitForm).zeroLevelChartedSpace
    (hσ.prod η.isSymplectic_coadjointOrbitForm.isNondegenerate)
    (h.stabilizer_zeroLevel_prod_eq_bot η hfree) (n := m) (by rwa [Module.finrank_prod])

/-- The zero level of the product moment map is a smooth manifold, for the atlas
`zeroLevelProdChartedSpace`. -/
theorem isManifold_zeroLevelProd :
    letI := h.zeroLevelProdChartedSpace hemb hσ hfree hm
    IsManifold 𝓘(ℝ, Fin m → ℝ) ∞ (h.prod η.isEquivariantMomentMap_coadjointOrbitForm).zeroLevel :=
  haveI : T2Space (G ⧸ (Lie.coadjointRepresentation ℝ I G).stabilizer η) := hemb.t2Space
  (h.prod η.isEquivariantMomentMap_coadjointOrbitForm).isManifold_zeroLevel
    (hσ.prod η.isSymplectic_coadjointOrbitForm.isNondegenerate)
    (h.stabilizer_zeroLevel_prod_eq_bot η hfree) (n := m) (by rwa [Module.finrank_prod])

/-- The inclusion of the zero level of the product moment map into `M × (G ⧸ G_η)` is a smooth
embedding, for the atlas `zeroLevelProdChartedSpace`. -/
theorem isSmoothEmbedding_coe_zeroLevelProd :
    letI := h.zeroLevelProdChartedSpace hemb hσ hfree hm
    Manifold.IsSmoothEmbedding 𝓘(ℝ, Fin m → ℝ)
      (I'.prod 𝓘(ℝ, Subgroup.QuotientModelSpace I
        ((Lie.coadjointRepresentation ℝ I G).stabilizer η))) ∞
      (Subtype.val : (h.prod η.isEquivariantMomentMap_coadjointOrbitForm).zeroLevel →
        M × (G ⧸ (Lie.coadjointRepresentation ℝ I G).stabilizer η)) :=
  haveI : T2Space (G ⧸ (Lie.coadjointRepresentation ℝ I G).stabilizer η) := hemb.t2Space
  (h.prod η.isEquivariantMomentMap_coadjointOrbitForm).isSmoothEmbedding_coe_zeroLevel
    (hσ.prod η.isSymplectic_coadjointOrbitForm.isNondegenerate)
    (h.stabilizer_zeroLevel_prod_eq_bot η hfree) (n := m) (by rwa [Module.finrank_prod])

include hσ hfree hm in
/-- **The atlas of the preimage of an embedded orbit.** If the form is nondegenerate, the orbit
map of `η` is a topological embedding and `G` acts freely at every point of the preimage of the
orbit, then the preimage carries the atlas `zeroLevelProdChartedSpace` of the zero level of the
product moment map on `M × (G ⧸ G_η)`, pulled back along the graph homeomorphism
`orbitLevelGraph`. It is modelled on `Fin m → ℝ` for `m = dim M + dim (G ⧸ G_η) - dim 𝔤`. -/
@[instance_reducible]
def orbitLevelChartedSpace : ChartedSpace (Fin m → ℝ) (h.orbitLevel η) :=
  letI := h.zeroLevelProdChartedSpace hemb hσ hfree hm
  (h.orbitLevelGraph hemb).pullbackChartedSpace

/-- **The preimage of an embedded orbit is a smooth manifold**, for the atlas
`orbitLevelChartedSpace`. -/
theorem isManifold_orbitLevel :
    letI := h.orbitLevelChartedSpace hemb hσ hfree hm
    IsManifold 𝓘(ℝ, Fin m → ℝ) ∞ (h.orbitLevel η) :=
  letI := h.zeroLevelProdChartedSpace hemb hσ hfree hm
  haveI := h.isManifold_zeroLevelProd hemb hσ hfree hm
  (h.orbitLevelGraph hemb).pullback_isManifold _ _

/-- **The graph is a diffeomorphism** from the preimage of an embedded orbit, with the atlas
`orbitLevelChartedSpace`, onto the zero level of the product moment map, with the atlas
`zeroLevelProdChartedSpace`. -/
def orbitLevelGraphDiffeomorph :
    letI := h.orbitLevelChartedSpace hemb hσ hfree hm
    letI := h.zeroLevelProdChartedSpace hemb hσ hfree hm
    h.orbitLevel η ≃ₘ⟮𝓘(ℝ, Fin m → ℝ), 𝓘(ℝ, Fin m → ℝ)⟯
      (h.prod η.isEquivariantMomentMap_coadjointOrbitForm).zeroLevel :=
  letI := h.zeroLevelProdChartedSpace hemb hσ hfree hm
  (h.orbitLevelGraph hemb).pullbackDiffeomorph _ _

/-- The diffeomorphism `orbitLevelGraphDiffeomorph` is the graph map `orbitLevelGraph`. -/
@[simp]
theorem coe_orbitLevelGraphDiffeomorph :
    letI := h.orbitLevelChartedSpace hemb hσ hfree hm
    letI := h.zeroLevelProdChartedSpace hemb hσ hfree hm
    ⇑(h.orbitLevelGraphDiffeomorph hemb hσ hfree hm) = h.orbitLevelGraph hemb :=
  letI := h.zeroLevelProdChartedSpace hemb hσ hfree hm
  (h.orbitLevelGraph hemb).coe_pullbackDiffeomorph _ _

/-- The inverse of `orbitLevelGraphDiffeomorph` is the inverse of `orbitLevelGraph`. -/
@[simp]
theorem coe_orbitLevelGraphDiffeomorph_symm :
    letI := h.orbitLevelChartedSpace hemb hσ hfree hm
    letI := h.zeroLevelProdChartedSpace hemb hσ hfree hm
    ⇑(h.orbitLevelGraphDiffeomorph hemb hσ hfree hm).symm = (h.orbitLevelGraph hemb).symm :=
  letI := h.zeroLevelProdChartedSpace hemb hσ hfree hm
  (h.orbitLevelGraph hemb).coe_pullbackDiffeomorph_symm _ _

/-- **`G` acts smoothly on the preimage of an embedded orbit**, for the atlas
`orbitLevelChartedSpace`. -/
theorem contMDiffSMul_orbitLevel :
    letI := h.orbitLevelChartedSpace hemb hσ hfree hm
    ContMDiffSMul I 𝓘(ℝ, Fin m → ℝ) ∞ G (h.orbitLevel η) :=
  letI := h.zeroLevelProdChartedSpace hemb hσ hfree hm
  letI := h.orbitLevelChartedSpace hemb hσ hfree hm
  haveI := h.isManifold_zeroLevelProd hemb hσ hfree hm
  haveI := h.isManifold_orbitLevel hemb hσ hfree hm
  -- Through the graph, the action on the preimage is the action on the product's level.
  (isSmoothEmbedding_comp_diffeomorph (h.orbitLevelGraphDiffeomorph hemb hσ hfree hm)
    (h.isSmoothEmbedding_coe_zeroLevelProd hemb hσ hfree hm)).contMDiffSMul contMDiff_id
    fun g x ↦ by simp [h.orbitLevelGraph_smul hemb g x]

/-- **The map to the orbit is smooth**: `orbitLevelProj` is smooth for the atlas
`orbitLevelChartedSpace` of the preimage and the manifold structure of `G ⧸ G_η`. -/
theorem contMDiff_orbitLevelProj :
    letI := h.orbitLevelChartedSpace hemb hσ hfree hm
    ContMDiff 𝓘(ℝ, Fin m → ℝ)
      𝓘(ℝ, Subgroup.QuotientModelSpace I ((Lie.coadjointRepresentation ℝ I G).stabilizer η)) ∞
      (h.orbitLevelProj hemb) := by
  let := h.zeroLevelProdChartedSpace hemb hσ hfree hm
  let := h.orbitLevelChartedSpace hemb hσ hfree hm
  let Φ := h.orbitLevelGraphDiffeomorph hemb hσ hfree hm
  have hΦ : ⇑Φ = h.orbitLevelGraph hemb := h.coe_orbitLevelGraphDiffeomorph hemb hσ hfree hm
  -- `orbitLevelProj` is the inclusion of the product's level, then `Prod.snd`, after the graph.
  have hsmooth := contMDiff_snd.comp <|
    (h.isSmoothEmbedding_coe_zeroLevelProd hemb hσ hfree hm).contMDiff.comp Φ.contMDiff
  rw [hΦ] at hsmooth
  exact hsmooth.congr (h.orbitLevelProj_apply hemb)

end Atlas

end Graph

end IsEquivariantMomentMap

end SmoothTwoForm

end TauCeti

end

end
