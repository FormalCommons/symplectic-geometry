/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.RangeProjection
public import TauCeti.Topology.VectorBundle.Trivialization
public import SymplecticGeometry.Topology.VectorBundle.ProjectiveBundle.Tautological
public import SymplecticGeometry.Topology.VectorBundle.TrivialEmbedding
public import TauCeti.Topology.VectorBundle.IdempotentRange
import SymplecticGeometry.Analysis.InnerProductSpace.Projection.Basic
import SymplecticGeometry.Topology.FiberBundle.Prod
import SymplecticGeometry.Topology.VectorBundle.Complement

/-!
# The splitting of the pull-back of a vector bundle to its projective bundle

Let `E → B` be a vector bundle over `ℝ` or `ℂ` with finite-dimensional model fibre `G`, over a
compact normal (for instance compact Hausdorff) base, and let `π : P(E) → B` be its projective
bundle. The pull-back `π^* E` contains the tautological line `S`, whose fibre over a line `p ⊆ E b`
is `p` itself. This file builds a complement of `S` in `π^* E`, so that `π^* E ≅ S ⊕ S^⊥`. With the
injectivity of `π^*` on cohomology, this is the one step of the splitting principle: a statement
about vector bundles that holds for lines and is compatible with direct sums can be proved by
induction on the rank.

The complement is orthogonal for a Hermitian metric pulled back from a trivial bundle. Tau Ceti's
`TauCeti.exists_continuous_injective_fin_of_compactSpace` gives a fibrewise injection of `E` into
some `𝕜ᴺ`, continuous on the total space; `SymplecticGeometry.Bundle.trivialEmbedding`, defined in
`SymplecticGeometry.Topology.VectorBundle.TrivialEmbedding`, is a choice of one, read in
`EuclideanSpace 𝕜 (Fin N)`. For a line `p ⊆ E b`, write `P_{j(E)}` and `P_{j(S)}`
for the orthogonal projections onto the images of `E b` and of `p`. Their difference
`ProjectiveBundle.tautologicalComplementProjection` is the orthogonal projection onto the
orthogonal complement of the image of `p` in that of `E b`
(`Submodule.starProjection_sub_starProjection_of_le`). It depends continuously on `p`, since both
projections do by Tau Ceti's `TauCeti.continuous_bundle_range_starProjection`, applied to `π^* E`
and to `S`. So its ranges form a vector bundle `ProjectiveBundle.tautologicalComplement`, a
subbundle of the trivial bundle, by Tau Ceti's `TauCeti.rangeVectorBundle`; its rank is one less
than that of `E`.

The splitting `ProjectiveBundle.pullbackEquivTautologicalProdComplement` sends a vector `v ∈ E b`
to its component in `p`, the vector of `p` whose image is `P_{j(S)} (j v)`, and to the projection
of `j v` onto the complement. It is injective, hence bijective by counting dimensions. Its first
component is read through the left inverse of `j` given by Tau Ceti's
`TauCeti.bundleComplementFiberEquiv`, whose continuity on total spaces is
`TauCeti.continuous_bundleComplementFiberEquiv_symm_fst`; so the splitting is continuous on total
spaces.

## Main definitions

* `ProjectiveBundle.tautologicalComplementProjection 𝕜 G E p`: the projection `P_{j(E)} - P_{j(S)}`.
* `ProjectiveBundle.tautologicalComplement 𝕜 G E`: the complement of the tautological line, with its
  `FiberBundle` and `VectorBundle` instances, of model fibre `Fin (finrank 𝕜 G - 1) → 𝕜`.
* `ProjectiveBundle.pullbackEquivTautologicalProdComplement 𝕜 G E p`: the fibrewise isomorphism of
  `π^* E` with `Tautological 𝕜 G E ×ᵇ tautologicalComplement 𝕜 G E`.

## Main results

* `ProjectiveBundle.continuous_tautologicalComplementProjection`: the projections depend
  continuously on the line.
* `ProjectiveBundle.finrank_range_tautologicalComplementProjection`: the complement has rank
  `finrank 𝕜 G - 1`.
* `ProjectiveBundle.pullbackEquivTautologicalProdComplement_apply_of_mem` and
  `ProjectiveBundle.pullbackEquivTautologicalProdComplement_apply_coe`: the splitting is the
  identity on the tautological line.
* `ProjectiveBundle.continuous_pullbackEquivTautologicalProdComplement`: the splitting is
  continuous on total spaces.

## References

* [R. Bott, L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982], §21 (the splitting
  principle).
* A. Hatcher, *Vector Bundles and K-Theory*, Proposition 1.4 (complements of subbundles of a
  trivial bundle, over a compact Hausdorff base) and §3.1 (the splitting principle).
-/

public section

noncomputable section

open Bundle Function Module Set
open scoped LinearAlgebra.Projectivization

namespace SymplecticGeometry.Bundle

variable {𝕜 : Type*} [RCLike 𝕜] {B : Type*} [TopologicalSpace B] [CompactSpace B] [NormalSpace B]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] [FiniteDimensional 𝕜 G]
  {E : B → Type*} [∀ b, AddCommGroup (E b)] [∀ b, Module 𝕜 (E b)] [∀ b, TopologicalSpace (E b)]
  [TopologicalSpace (TotalSpace G E)] [FiberBundle G E] [VectorBundle 𝕜 G E]

/-! ### The complement of the tautological line -/

namespace ProjectiveBundle

variable (𝕜 G E) in
/-- The orthogonal projection, in the Euclidean space of `trivialEmbedding`, onto the orthogonal
complement of the image of the line `p` inside the image of the fibre `E b` that contains it:
the difference of the projections onto the image of `E b` and onto the image of `p`. -/
def tautologicalComplementProjection (p : ProjectiveBundle 𝕜 G E) :
    EuclideanSpace 𝕜 (Fin (trivialEmbeddingDim 𝕜 G E)) →L[𝕜]
      EuclideanSpace 𝕜 (Fin (trivialEmbeddingDim 𝕜 G E)) :=
  (trivialEmbedding 𝕜 G E p.proj).range.starProjection -
    (p.snd.submodule.map (trivialEmbedding 𝕜 G E p.proj : E p.proj →ₗ[𝕜] _)).starProjection

theorem tautologicalComplementProjection_def (p : ProjectiveBundle 𝕜 G E) :
    tautologicalComplementProjection 𝕜 G E p =
      (trivialEmbedding 𝕜 G E p.proj).range.starProjection -
        (p.snd.submodule.map (trivialEmbedding 𝕜 G E p.proj : E p.proj →ₗ[𝕜] _)).starProjection :=
  (rfl)

/-- `tautologicalComplementProjection 𝕜 G E p` is the orthogonal projection onto the orthogonal
complement of the image of the line `p` in the image of `E b`. -/
theorem tautologicalComplementProjection_eq (p : ProjectiveBundle 𝕜 G E) :
    tautologicalComplementProjection 𝕜 G E p =
      ((p.snd.submodule.map (trivialEmbedding 𝕜 G E p.proj : E p.proj →ₗ[𝕜] _))ᗮ ⊓
        (trivialEmbedding 𝕜 G E p.proj).range).starProjection :=
  Submodule.starProjection_sub_starProjection_of_le LinearMap.map_le_range

/-- `tautologicalComplementProjection 𝕜 G E p` is idempotent. -/
theorem isIdempotentElem_tautologicalComplementProjection (p : ProjectiveBundle 𝕜 G E) :
    IsIdempotentElem (tautologicalComplementProjection 𝕜 G E p) := by
  rw [tautologicalComplementProjection_eq]
  exact Submodule.isIdempotentElem_starProjection _

/-- The range of `tautologicalComplementProjection 𝕜 G E p` is the orthogonal complement of the
image of the line `p` in the image of `E b`. -/
theorem range_tautologicalComplementProjection (p : ProjectiveBundle 𝕜 G E) :
    (tautologicalComplementProjection 𝕜 G E p).range =
      (p.snd.submodule.map (trivialEmbedding 𝕜 G E p.proj : E p.proj →ₗ[𝕜] _))ᗮ ⊓
        (trivialEmbedding 𝕜 G E p.proj).range := by
  rw [tautologicalComplementProjection_eq, Submodule.range_starProjection]

/-- The projections onto the images of the lines `p` depend continuously on `p`. -/
theorem continuous_starProjection_map_tautological :
    Continuous fun p : ProjectiveBundle 𝕜 G E ↦
      (p.snd.submodule.map (trivialEmbedding 𝕜 G E p.proj).toLinearMap).starProjection := by
  refine (TauCeti.continuous_bundle_range_starProjection (F := 𝕜)
    (E := Tautological 𝕜 G E) (fun p ↦ trivialEmbedding 𝕜 G E p.proj ∘L p.snd.submodule.subtypeL)
    ((continuous_trivialEmbedding 𝕜 G E).comp (continuous_toTotalSpace_tautological 𝕜 G E))
    fun p ↦ (injective_trivialEmbedding 𝕜 G E p.proj).comp Subtype.val_injective).congr fun p ↦ ?_
  congr 1
  rw [ContinuousLinearMap.toLinearMap_comp, LinearMap.range_comp,
    Submodule.toLinearMap_subtypeL, Submodule.range_subtype]

/-- The projections `tautologicalComplementProjection 𝕜 G E p` depend continuously on the line
`p`. -/
theorem continuous_tautologicalComplementProjection :
    Continuous (tautologicalComplementProjection 𝕜 G E) :=
  (TauCeti.continuous_bundle_range_starProjection (F := G)
    (E := projection 𝕜 G E *ᵖ E) (fun p ↦ trivialEmbedding 𝕜 G E p.proj)
    ((continuous_trivialEmbedding 𝕜 G E).comp (Pullback.continuous_lift G E (projection 𝕜 G E)))
    fun p ↦ injective_trivialEmbedding 𝕜 G E p.proj).sub continuous_starProjection_map_tautological

/-- The orthogonal complement of the line `p` in `E b` has dimension `finrank 𝕜 G - 1`. -/
theorem finrank_range_tautologicalComplementProjection (p : ProjectiveBundle 𝕜 G E) :
    finrank 𝕜 (tautologicalComplementProjection 𝕜 G E p).range = finrank 𝕜 G - 1 := by
  have hS : finrank 𝕜 (p.snd.submodule.map (trivialEmbedding 𝕜 G E p.proj).toLinearMap) = 1 :=
    (Submodule.equivMapOfInjective (trivialEmbedding 𝕜 G E p.proj).toLinearMap
      (injective_trivialEmbedding 𝕜 G E p.proj)
      p.snd.submodule).finrank_eq.symm.trans (Projectivization.finrank_submodule _)
  have hE : finrank 𝕜 (trivialEmbedding 𝕜 G E p.proj).toLinearMap.range = finrank 𝕜 G :=
    (LinearMap.finrank_range_of_inj (injective_trivialEmbedding 𝕜 G E p.proj)).trans
      (VectorBundle.finrank_eq 𝕜 G E p.proj)
  have hle := Submodule.finrank_mono
    (LinearMap.map_le_range (f := (trivialEmbedding 𝕜 G E p.proj).toLinearMap)
    (p := p.snd.submodule))
  rw [range_tautologicalComplementProjection]
  refine Submodule.finrank_add_inf_finrank_orthogonal' LinearMap.map_le_range ?_
  rw [hS, hE]
  omega

variable (𝕜 G E) in
/-- The complement of the tautological line in the pull-back of `E` to its projective bundle:
over a line `p ⊆ E b`, the orthogonal complement of the image of `p` in the image of `E b`, in the
Euclidean space of `trivialEmbedding`. It is a vector bundle of rank `finrank 𝕜 G - 1`, a subbundle
of the trivial bundle with that Euclidean space as fibre. -/
abbrev tautologicalComplement : ProjectiveBundle 𝕜 G E → Type _ :=
  fun p ↦ (tautologicalComplementProjection 𝕜 G E p).range

/-- Each fibre of the complement of the tautological line is isomorphic to
`Fin (finrank 𝕜 G - 1) → 𝕜`. -/
theorem nonempty_continuousLinearEquiv_tautologicalComplement (p : ProjectiveBundle 𝕜 G E) :
    Nonempty ((Fin (finrank 𝕜 G - 1) → 𝕜) ≃L[𝕜] tautologicalComplement 𝕜 G E p) :=
  ⟨ContinuousLinearEquiv.ofFinrankEq (by
    rw [finrank_fin_fun, finrank_range_tautologicalComplementProjection])⟩

/-- The complement of the tautological line is a fibre bundle, with the topology of a subspace of
the trivial bundle: Tau Ceti's `TauCeti.rangeFiberBundle`. -/
instance : FiberBundle (Fin (finrank 𝕜 G - 1) → 𝕜) (tautologicalComplement 𝕜 G E) :=
  TauCeti.rangeFiberBundle (F' := Fin (finrank 𝕜 G - 1) → 𝕜)
    (continuous_tautologicalComplementProjection (𝕜 := 𝕜) (G := G) (E := E))
    isIdempotentElem_tautologicalComplementProjection
    nonempty_continuousLinearEquiv_tautologicalComplement

/-- The complement of the tautological line is a vector bundle of rank `finrank 𝕜 G - 1`. -/
instance : VectorBundle 𝕜 (Fin (finrank 𝕜 G - 1) → 𝕜) (tautologicalComplement 𝕜 G E) :=
  TauCeti.rangeVectorBundle (F' := Fin (finrank 𝕜 G - 1) → 𝕜)
    (continuous_tautologicalComplementProjection (𝕜 := 𝕜) (G := G) (E := E))
    isIdempotentElem_tautologicalComplementProjection
    nonempty_continuousLinearEquiv_tautologicalComplement

/-! ### The splitting of the pull-back -/

section Splitting

variable (𝕜 G E) in
/-- `trivialEmbedding`, pulled back to the projective bundle. -/
private def pullbackEmbedding (p : ProjectiveBundle 𝕜 G E) :
    (projection 𝕜 G E *ᵖ E) p →L[𝕜] EuclideanSpace 𝕜 (Fin (trivialEmbeddingDim 𝕜 G E)) :=
  trivialEmbedding 𝕜 G E p.proj

private theorem continuous_pullbackEmbedding :
    Continuous fun v : TotalSpace G (projection 𝕜 G E *ᵖ E) ↦
      pullbackEmbedding 𝕜 G E v.proj v.snd :=
  (continuous_trivialEmbedding 𝕜 G E).comp (Pullback.continuous_lift G E (projection 𝕜 G E))

private theorem injective_pullbackEmbedding (p : ProjectiveBundle 𝕜 G E) :
    Injective (pullbackEmbedding 𝕜 G E p) :=
  injective_trivialEmbedding 𝕜 G E p.proj

/-- The vector of `E b` whose image is the projection of `u` onto the image of `E b`. -/
private def leftInverse (p : ProjectiveBundle 𝕜 G E) :
    EuclideanSpace 𝕜 (Fin (trivialEmbeddingDim 𝕜 G E)) →L[𝕜] E p.proj :=
  have : ∀ b, IsTopologicalAddGroup (E b) := VectorBundle.isTopologicalAddGroup 𝕜 G E
  have : ∀ b, ContinuousSMul 𝕜 (E b) := VectorBundle.continuousSMul 𝕜 G E
  ContinuousLinearMap.fst 𝕜 _ _ ∘L (TauCeti.bundleComplementFiberEquiv (F := G)
    (E := projection 𝕜 G E *ᵖ E) (pullbackEmbedding 𝕜 G E) injective_pullbackEmbedding
      p).symm.toContinuousLinearMap

private theorem leftInverse_apply (p : ProjectiveBundle 𝕜 G E)
    (u : EuclideanSpace 𝕜 (Fin (trivialEmbeddingDim 𝕜 G E))) :
    have : ∀ b, IsTopologicalAddGroup (E b) := VectorBundle.isTopologicalAddGroup 𝕜 G E
    have : ∀ b, ContinuousSMul 𝕜 (E b) := VectorBundle.continuousSMul 𝕜 G E
    leftInverse p u = ((TauCeti.bundleComplementFiberEquiv (F := G)
      (E := projection 𝕜 G E *ᵖ E) (pullbackEmbedding 𝕜 G E) injective_pullbackEmbedding
        p).symm u).1 :=
  (rfl)

private theorem trivialEmbedding_leftInverse (p : ProjectiveBundle 𝕜 G E)
    (u : EuclideanSpace 𝕜 (Fin (trivialEmbeddingDim 𝕜 G E))) :
    trivialEmbedding 𝕜 G E p.proj (leftInverse p u) =
      (trivialEmbedding 𝕜 G E p.proj).range.starProjection u :=
  have : ∀ b, IsTopologicalAddGroup (E b) := VectorBundle.isTopologicalAddGroup 𝕜 G E
  have : ∀ b, ContinuousSMul 𝕜 (E b) := VectorBundle.continuousSMul 𝕜 G E
  TauCeti.bundleComplementFiberEquiv_symm_apply_fst (F := G) (E := projection 𝕜 G E *ᵖ E)
    (pullbackEmbedding 𝕜 G E) injective_pullbackEmbedding p u

private theorem leftInverse_starProjection_mem (p : ProjectiveBundle 𝕜 G E) (v : E p.proj) :
    leftInverse p ((p.snd.submodule.map (trivialEmbedding 𝕜 G E p.proj).toLinearMap).starProjection
      (trivialEmbedding 𝕜 G E p.proj v)) ∈ p.snd.submodule := by
  obtain ⟨s, hs, hsu⟩ := Submodule.mem_map.1
    (Submodule.starProjection_apply_mem
      (p.snd.submodule.map (trivialEmbedding 𝕜 G E p.proj).toLinearMap)
      (trivialEmbedding 𝕜 G E p.proj v))
  convert hs
  refine injective_trivialEmbedding 𝕜 G E p.proj ?_
  rw [trivialEmbedding_leftInverse, ← hsu, ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.starProjection_range_apply]

/-- The component in the line `p` of a vector of `E b`. -/
private def tautologicalPart (p : ProjectiveBundle 𝕜 G E) : E p.proj →L[𝕜] p.snd.submodule :=
  (leftInverse p ∘L
    (p.snd.submodule.map (trivialEmbedding 𝕜 G E p.proj).toLinearMap).starProjection ∘L
      trivialEmbedding 𝕜 G E p.proj).codRestrict p.snd.submodule
    fun v ↦ leftInverse_starProjection_mem p v

private theorem coe_tautologicalPart (p : ProjectiveBundle 𝕜 G E) (v : E p.proj) :
    (tautologicalPart p v : E p.proj) =
      leftInverse p
        ((p.snd.submodule.map (trivialEmbedding 𝕜 G E p.proj).toLinearMap).starProjection
          (trivialEmbedding 𝕜 G E p.proj v)) :=
  (rfl)

private theorem trivialEmbedding_tautologicalPart (p : ProjectiveBundle 𝕜 G E) (v : E p.proj) :
    trivialEmbedding 𝕜 G E p.proj (tautologicalPart p v : E p.proj) =
      (p.snd.submodule.map (trivialEmbedding 𝕜 G E p.proj).toLinearMap).starProjection
        (trivialEmbedding 𝕜 G E p.proj v) := by
  rw [coe_tautologicalPart, trivialEmbedding_leftInverse, Submodule.starProjection_eq_self_iff.2
    (LinearMap.map_le_range (Submodule.starProjection_apply_mem _ _))]

private theorem starProjection_map_add_tautologicalComplementProjection
    (p : ProjectiveBundle 𝕜 G E) (u : EuclideanSpace 𝕜 (Fin (trivialEmbeddingDim 𝕜 G E))) :
    (p.snd.submodule.map (trivialEmbedding 𝕜 G E p.proj).toLinearMap).starProjection u +
        tautologicalComplementProjection 𝕜 G E p u =
      (trivialEmbedding 𝕜 G E p.proj).range.starProjection u := by
  rw [tautologicalComplementProjection_def, sub_apply, add_sub_cancel]

/-- The splitting of `E b` along the line `p` and its complement, as a continuous linear map. -/
private def splitting (p : ProjectiveBundle 𝕜 G E) :
    E p.proj →L[𝕜] p.snd.submodule × tautologicalComplement 𝕜 G E p :=
  (tautologicalPart p).prod
    ((tautologicalComplementProjection 𝕜 G E p).rangeRestrict ∘L trivialEmbedding 𝕜 G E p.proj)

private theorem injective_splitting (p : ProjectiveBundle 𝕜 G E) : Injective (splitting p) := by
  refine (injective_iff_map_eq_zero _).2 fun v hv ↦ injective_trivialEmbedding 𝕜 G E p.proj ?_
  have h₁ : (tautologicalPart p v : E p.proj) = 0 := congrArg (fun x ↦ (x.1 : E p.proj)) hv
  have h₂ : tautologicalComplementProjection 𝕜 G E p (trivialEmbedding 𝕜 G E p.proj v) = 0 :=
    congrArg (fun x ↦ (x.2 : EuclideanSpace 𝕜 (Fin (trivialEmbeddingDim 𝕜 G E)))) hv
  calc trivialEmbedding 𝕜 G E p.proj v
      = (trivialEmbedding 𝕜 G E p.proj).range.starProjection (trivialEmbedding 𝕜 G E p.proj v) :=
        (ContinuousLinearMap.starProjection_range_apply _ v).symm
    _ = tautologicalComplementProjection 𝕜 G E p (trivialEmbedding 𝕜 G E p.proj v) +
        trivialEmbedding 𝕜 G E p.proj (tautologicalPart p v : E p.proj) := by
        rw [trivialEmbedding_tautologicalPart, tautologicalComplementProjection_def,
          sub_apply, sub_add_cancel]
    _ = trivialEmbedding 𝕜 G E p.proj 0 := by rw [h₁, h₂, zero_add]

private theorem finrank_eq_finrank_prod (p : ProjectiveBundle 𝕜 G E) :
    finrank 𝕜 (E p.proj) = finrank 𝕜 (p.snd.submodule × tautologicalComplement 𝕜 G E p) := by
  have := VectorBundle.finiteDimensional 𝕜 G E p.proj
  have hE := VectorBundle.finrank_eq 𝕜 G E p.proj
  have hl := Submodule.finrank_le p.snd.submodule
  rw [Projectivization.finrank_submodule, hE] at hl
  rw [finrank_prod, Projectivization.finrank_submodule,
    finrank_range_tautologicalComplementProjection, hE]
  omega

variable (𝕜 G E) in
/-- The splitting of the pull-back of `E` to its projective bundle: over a line `p ⊆ E b`, the
isomorphism of `E b` with the sum of the line `p` and of its complement
`tautologicalComplement 𝕜 G E p`, which sends a vector to its two components. It is continuous on
total spaces (`continuous_pullbackEquivTautologicalProdComplement`). -/
def pullbackEquivTautologicalProdComplement (p : ProjectiveBundle 𝕜 G E) :
    (projection 𝕜 G E *ᵖ E) p ≃L[𝕜] (Tautological 𝕜 G E ×ᵇ tautologicalComplement 𝕜 G E) p :=
  have : ∀ b, IsTopologicalAddGroup (E b) := VectorBundle.isTopologicalAddGroup 𝕜 G E
  have : ∀ b, ContinuousSMul 𝕜 (E b) := VectorBundle.continuousSMul 𝕜 G E
  have := VectorBundle.finiteDimensional 𝕜 G E p.proj
  have := FiberBundle.t2Space G E p.proj
  ((splitting p).toLinearMap.linearEquivOfInjective (injective_splitting p)
    (finrank_eq_finrank_prod p)).toContinuousLinearEquiv

private theorem pullbackEquivTautologicalProdComplement_apply (p : ProjectiveBundle 𝕜 G E)
    (v : (projection 𝕜 G E *ᵖ E) p) :
    pullbackEquivTautologicalProdComplement 𝕜 G E p v = splitting p v :=
  (rfl)

private theorem coe_pullbackEquivTautologicalProdComplement_fst (p : ProjectiveBundle 𝕜 G E)
    (v : (projection 𝕜 G E *ᵖ E) p) :
    ((pullbackEquivTautologicalProdComplement 𝕜 G E p v).1 : E p.proj) =
      leftInverse p
        ((p.snd.submodule.map (trivialEmbedding 𝕜 G E p.proj).toLinearMap).starProjection
          (trivialEmbedding 𝕜 G E p.proj v)) :=
  coe_tautologicalPart p v

/-- The first component of `pullbackEquivTautologicalProdComplement` is the vector of the line `p`
whose image is the projection of the image of `v` onto the image of `p`. -/
@[simp]
theorem trivialEmbedding_pullbackEquivTautologicalProdComplement_fst (p : ProjectiveBundle 𝕜 G E)
    (v : (projection 𝕜 G E *ᵖ E) p) :
    trivialEmbedding 𝕜 G E p.proj (pullbackEquivTautologicalProdComplement 𝕜 G E p v).1 =
      (p.snd.submodule.map (trivialEmbedding 𝕜 G E p.proj).toLinearMap).starProjection
        (trivialEmbedding 𝕜 G E p.proj v) := by
  rw [pullbackEquivTautologicalProdComplement_apply]
  exact trivialEmbedding_tautologicalPart p v

/-- The second component of `pullbackEquivTautologicalProdComplement` is the projection of the
image of `v` onto the complement of the line. -/
@[simp]
theorem coe_pullbackEquivTautologicalProdComplement_snd (p : ProjectiveBundle 𝕜 G E)
    (v : (projection 𝕜 G E *ᵖ E) p) :
    ((pullbackEquivTautologicalProdComplement 𝕜 G E p v).2 :
        EuclideanSpace 𝕜 (Fin (trivialEmbeddingDim 𝕜 G E))) =
      tautologicalComplementProjection 𝕜 G E p (trivialEmbedding 𝕜 G E p.proj v) :=
  (rfl)

/-- The inverse of `pullbackEquivTautologicalProdComplement` adds the two components, read in the
Euclidean space of `trivialEmbedding`. -/
@[simp]
theorem trivialEmbedding_pullbackEquivTautologicalProdComplement_symm (p : ProjectiveBundle 𝕜 G E)
    (x : (Tautological 𝕜 G E ×ᵇ tautologicalComplement 𝕜 G E) p) :
    trivialEmbedding 𝕜 G E p.proj ((pullbackEquivTautologicalProdComplement 𝕜 G E p).symm x) =
      trivialEmbedding 𝕜 G E p.proj (x.1 : E p.proj) + x.2 := by
  have h₁ := trivialEmbedding_pullbackEquivTautologicalProdComplement_fst p
    ((pullbackEquivTautologicalProdComplement 𝕜 G E p).symm x)
  have h₂ := coe_pullbackEquivTautologicalProdComplement_snd p
    ((pullbackEquivTautologicalProdComplement 𝕜 G E p).symm x)
  rw [ContinuousLinearEquiv.apply_symm_apply] at h₁ h₂
  rw [h₁, h₂, starProjection_map_add_tautologicalComplementProjection]
  exact (ContinuousLinearMap.starProjection_range_apply _ _).symm

/-- On the line `p` itself, `pullbackEquivTautologicalProdComplement` is the inclusion of the
first summand. -/
@[simp]
theorem pullbackEquivTautologicalProdComplement_apply_of_mem (p : ProjectiveBundle 𝕜 G E)
    (v : (projection 𝕜 G E *ᵖ E) p) (hv : v ∈ p.snd.submodule) :
    pullbackEquivTautologicalProdComplement 𝕜 G E p v = (⟨v, hv⟩, 0) := by
  have hmap : ∀ w ∈ p.snd.submodule, trivialEmbedding 𝕜 G E p.proj w ∈
      p.snd.submodule.map (trivialEmbedding 𝕜 G E p.proj).toLinearMap :=
    fun w hw ↦ Submodule.mem_map_of_mem hw
  have h₀ : ∀ w ∈ p.snd.submodule,
      tautologicalComplementProjection 𝕜 G E p (trivialEmbedding 𝕜 G E p.proj w) = 0 := by
    intro w hw
    rw [tautologicalComplementProjection_def, sub_apply,
      Submodule.starProjection_eq_self_iff.2 (hmap w hw),
      ContinuousLinearMap.starProjection_range_apply, sub_self]
  refine Prod.ext (Subtype.ext (injective_trivialEmbedding 𝕜 G E p.proj ?_))
    (Subtype.ext ((coe_pullbackEquivTautologicalProdComplement_snd p v).trans (h₀ v hv)))
  rw [trivialEmbedding_pullbackEquivTautologicalProdComplement_fst]
  exact Submodule.starProjection_eq_self_iff.2 (hmap v hv)

/-- On a vector `v` of the line `p`, `pullbackEquivTautologicalProdComplement` gives `(v, 0)`. -/
@[simp]
theorem pullbackEquivTautologicalProdComplement_apply_coe (p : ProjectiveBundle 𝕜 G E)
    (v : p.snd.submodule) :
    pullbackEquivTautologicalProdComplement 𝕜 G E p (v : E p.proj) = (v, 0) :=
  pullbackEquivTautologicalProdComplement_apply_of_mem p _ v.property

/-- The splitting `pullbackEquivTautologicalProdComplement` is continuous on total spaces. -/
theorem continuous_pullbackEquivTautologicalProdComplement :
    Continuous fun v : TotalSpace G (projection 𝕜 G E *ᵖ E) ↦
      TotalSpace.mk' (𝕜 × (Fin (finrank 𝕜 G - 1) → 𝕜))
        (E := Tautological 𝕜 G E ×ᵇ tautologicalComplement 𝕜 G E) v.proj
        (pullbackEquivTautologicalProdComplement 𝕜 G E v.proj v.snd) := by
  have : ∀ b, IsTopologicalAddGroup (E b) := VectorBundle.isTopologicalAddGroup 𝕜 G E
  have : ∀ b, ContinuousSMul 𝕜 (E b) := VectorBundle.continuousSMul 𝕜 G E
  have hp := FiberBundle.continuous_proj G (projection 𝕜 G E *ᵖ E)
  refine Bundle.Prod.continuous_totalSpace_prod_iff.2 ⟨continuous_totalSpace_tautological_iff.2
    ⟨hp, ?_⟩, (TauCeti.isEmbedding_totalSpace_range _ _).continuous_iff.2 ?_⟩
  · have hL := (Pullback.continuous_lift G E (projection 𝕜 G E)).comp
      ((TauCeti.continuous_bundleComplementFiberEquiv_symm_fst (F := G)
        (E := projection 𝕜 G E *ᵖ E) (pullbackEmbedding 𝕜 G E)
        continuous_pullbackEmbedding injective_pullbackEmbedding).comp
        (hp.prodMk ((continuous_starProjection_map_tautological.comp hp).clm_apply
          continuous_pullbackEmbedding)))
    -- `Pullback.lift` keeps the vector and maps the base point by the projection.
    exact hL.congr fun v ↦ congrArg (TotalSpace.mk _)
      ((coe_pullbackEquivTautologicalProdComplement_fst v.proj v.snd).trans
        (leftInverse_apply _ _)).symm
  · exact (hp.prodMk ((continuous_tautologicalComplementProjection.comp hp).clm_apply
      continuous_pullbackEmbedding)).congr fun v ↦
        Prod.ext rfl (coe_pullbackEquivTautologicalProdComplement_snd v.proj v.snd).symm

end Splitting

end ProjectiveBundle

end SymplecticGeometry.Bundle

end
