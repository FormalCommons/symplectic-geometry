/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Homeomorph.Lemmas
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

This file is the topological part of the passage from the preimage `Q` of the orbit to that zero
level, the first step of reduction at a coadjoint orbit through the product:

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
theorem differential_surjective_of_mem_orbitLevel [I'.Boundaryless] [T2Space M]
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

end Graph

end IsEquivariantMomentMap

end SmoothTwoForm

end TauCeti

end

end
