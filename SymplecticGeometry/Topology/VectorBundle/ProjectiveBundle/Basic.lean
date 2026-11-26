/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.LocalAtTarget
public import Mathlib.Topology.VectorBundle.Constructions
public import TauCeti.Topology.Algebra.Projectivization
public import TauCeti.Topology.FiberBundle.Proper
public import TauCeti.Topology.FiberBundle.Pullback
public import TauCeti.Topology.FiberBundle.Separation
public import TauCeti.Topology.Homotopy.DeformationRetract
public import TauCeti.Topology.VectorBundle.Hom
public import TauCeti.Topology.VectorBundle.Pullback
public import TauCeti.Topology.VectorBundle.Smul
public import TauCeti.Topology.VectorBundle.ZeroSection

import SymplecticGeometry.Topology.FiberBundle.Basic
import SymplecticGeometry.Topology.Algebra.Projectivization
import SymplecticGeometry.Topology.VectorBundle.ZeroSet

/-!
# The projective bundle of a vector bundle

Let `E → B` be a topological vector bundle with model fibre `G` over a nontrivially normed field
`𝕜`. Its projective bundle `SymplecticGeometry.Bundle.ProjectiveBundle 𝕜 G E` has the projective
space `ℙ 𝕜 (E b)` of lines of `E b` as fibre over `b`, and model fibre `ℙ 𝕜 G`. A linear
trivialization `e` of `E` induces a pretrivialization, sending a line `ℓ ⊆ E b` over the base set
of `e` to `(b, e_b ℓ)`; its coordinate changes are continuous because those of `E` are, and the
map of projective spaces induced by a linear map depends jointly continuously on the map and the
point (Tau Ceti's `Projectivization.continuousAt_linearProjection`). Mathlib's `FiberPrebundle`
turns these into the topology and the `FiberBundle (ℙ 𝕜 G)` structure of the projective bundle.

The map `ProjectiveBundle.mk'` sending a nonzero vector of `E`, a point of Tau Ceti's
`TauCeti.zeroSectionCompl G E`, to the line it spans is an open
quotient map onto the projective bundle (`ProjectiveBundle.isOpenQuotientMap_mk'`), as
`Projectivization.mk'` is for a single projective space. So a map out of the projective bundle is
continuous as soon as it is continuous on nonzero vectors (`ProjectiveBundle.continuous_iff`);
this gives the continuity of all the maps below.

Over `ℝ` or `ℂ` and in finite rank the fibre `ℙ 𝕜 G` is compact Hausdorff, so the projective bundle
is compact over a compact base by the instance `FiberBundle.compactSpace_totalSpace`, and
Hausdorff over a Hausdorff base by Tau Ceti's instance `TauCeti.FiberBundle.t2Space_totalSpace`;
this file imports both for its users.

For a direct sum `E₁ ×ᵇ E₂`, the projective bundles of `E₁` and of `E₂` embed as disjoint closed
subspaces through `v₁ ↦ (v₁, 0)` and `v₂ ↦ (0, v₂)`. The complement of the second one retracts onto
the first through the lines spanned by `(v₁, t v₂)`, `t ∈ [0, 1]`: this is a deformation retraction,
for which `𝕜` must contain `ℝ`, and the inclusion of the projective bundle of `E₁` into that
complement is a homotopy equivalence.

## Main definitions

* `SymplecticGeometry.Bundle.ProjectiveBundle 𝕜 G E`: the projective bundle, with its
  `FiberBundle (ℙ 𝕜 G)` structure from `ProjectiveBundle.fiberPrebundle`.
* `ProjectiveBundle.mk`, `ProjectiveBundle.mk'`: the line spanned by a nonzero vector.
* `ProjectiveBundle.projection`: the projection to the base, as a continuous map.
* `ProjectiveBundle.map`: the homeomorphism induced by a fibrewise linear equivalence of finite
  rank vector bundles that is continuous on total spaces.
* `ProjectiveBundle.pullbackMap f`: the map from the projective bundle of `f *ᵖ E` to that of `E`
  over `f`; `ProjectiveBundle.pullbackHomeomorph f` identifies the projective bundle of `f *ᵖ E`
  with the pull-back along `f` of that of `E`.
* `ProjectiveBundle.inl`, `ProjectiveBundle.inr`: the embeddings of the projective bundles of the
  summands into that of a direct sum, and `ProjectiveBundle.prodComm`, the exchange of the
  summands.
* `ProjectiveBundle.inlRetraction`: the retraction of the complement of the range of `inr` onto
  the projective bundle of `E₁`, and `ProjectiveBundle.inlHomotopyEquiv`, the homotopy
  equivalence it gives.

## Main results

* `ProjectiveBundle.isOpenQuotientMap_mk'`: lines spanned by nonzero vectors form an open quotient.
* `ProjectiveBundle.continuous_mapProjectivization_of_continuous`: a fibrewise linear equivalence
  that is continuous on total spaces induces a continuous map of projective bundles.
* `ProjectiveBundle.isClosedEmbedding_inl`, `ProjectiveBundle.isClosedEmbedding_inr`,
  `ProjectiveBundle.disjoint_range_inl_inr`: the projective bundles of the summands are disjoint
  closed subspaces of that of the direct sum.
* `ProjectiveBundle.homotopic_inlCompl_comp_inlRetraction`: the deformation of the complement of
  the range of `inr` onto the range of `inl`.

## Implementation notes

The continuous projection is named `ProjectiveBundle.projection` rather than
`ProjectiveBundle.proj`: since `ProjectiveBundle` is an abbreviation, a declaration
`ProjectiveBundle.proj` would take over the field notation `p.proj` for every point `p` of a
projective bundle. The coordinate changes of the projective bundle are continuous by Tau Ceti's
`Projectivization.continuousAt_linearProjection`, applied to the coordinate changes of `E`.

## References

* [R. Bott, L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982], §20 (the
  projective bundle of a vector bundle).
* A. Hatcher, *Vector Bundles and K-Theory*, version 2.2 (2017), §3.1, proof of Theorem 3.2 (the
  projective bundles of the summands of a direct sum, and the deformation retraction of the
  complement of one onto the other).
-/

public section

noncomputable section

open Bundle Set Topology
open TauCeti (zeroSectionCompl mem_zeroSectionCompl)
open scoped LinearAlgebra.Projectivization

namespace SymplecticGeometry.Bundle

variable (𝕜 : Type*) {B : Type*} [NontriviallyNormedField 𝕜]
  (G : Type*) [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  (E : B → Type*) [∀ b, AddCommGroup (E b)] [∀ b, Module 𝕜 (E b)]

/-- The projective bundle of a vector bundle `E` over `B` with model fibre `G`: the bundle over
`B` whose fibre over `b` is the projective space `ℙ 𝕜 (E b)` of lines in `E b`, with model fibre
`ℙ 𝕜 G`. -/
abbrev ProjectiveBundle := TotalSpace (ℙ 𝕜 G) fun b ↦ ℙ 𝕜 (E b)

namespace ProjectiveBundle

variable {𝕜 G E}

/-! ### Lines spanned by nonzero vectors -/

variable (𝕜) in
/-- The line spanned by a nonzero vector `v` of `E`, as a point of the projective bundle over the
base point of `v`. -/
def mk (v : TotalSpace G E) (hv : v.snd ≠ 0) : ProjectiveBundle 𝕜 G E :=
  ⟨v.proj, Projectivization.mk 𝕜 v.snd hv⟩

@[simp]
theorem proj_mk (v : TotalSpace G E) (hv : v.snd ≠ 0) : (mk 𝕜 v hv).proj = v.proj :=
  (rfl)

theorem mk_def (v : TotalSpace G E) (hv : v.snd ≠ 0) :
    mk 𝕜 v hv = ⟨v.proj, Projectivization.mk 𝕜 v.snd hv⟩ :=
  (rfl)

@[simp]
theorem mk_mk (b : B) (v : E b) (hv : v ≠ 0) :
    mk 𝕜 (TotalSpace.mk' G b v) hv = ⟨b, Projectivization.mk 𝕜 v hv⟩ :=
  (rfl)

/-- Two nonzero vectors of the same fibre span the same line exactly when one is a unit multiple of
the other. -/
theorem mk_eq_mk_iff {b : B} {v w : E b} (hv : v ≠ 0) (hw : w ≠ 0) :
    mk 𝕜 (TotalSpace.mk' G b v) hv = mk 𝕜 (TotalSpace.mk' G b w) hw ↔ ∃ a : 𝕜ˣ, a • w = v := by
  rw [mk_mk, mk_mk, TotalSpace.mk_inj, Projectivization.mk_eq_mk_iff]

variable (𝕜 G E) in
/-- The line spanned by a nonzero vector of `E`, as a map from the nonzero vectors of `E` onto the
projective bundle. -/
def mk' (v : zeroSectionCompl G E) : ProjectiveBundle 𝕜 G E :=
  mk 𝕜 v.val (mem_zeroSectionCompl.1 v.property)

theorem mk'_eq_mk (v : zeroSectionCompl G E) :
    mk' 𝕜 G E v = mk 𝕜 v.val (mem_zeroSectionCompl.1 v.property) :=
  (rfl)

theorem mk_rep (p : ProjectiveBundle 𝕜 G E) : mk 𝕜 ⟨p.proj, p.snd.rep⟩ p.snd.rep_ne_zero = p := by
  rw [mk_mk, Projectivization.mk_rep]

theorem mk'_surjective : Function.Surjective (mk' 𝕜 G E) := fun p ↦
  ⟨⟨⟨p.proj, p.snd.rep⟩, mem_zeroSectionCompl.2 p.snd.rep_ne_zero⟩, mk_rep p⟩

variable [TopologicalSpace B] [TopologicalSpace (TotalSpace G E)] [∀ b, TopologicalSpace (E b)]
  [FiberBundle G E]

/-- The fibre of `E` over `b` identified with the model fibre by `e` when `b` lies in the base set
of `e`, and by the trivialization at `b` otherwise. -/
private def fiberEquiv [VectorBundle 𝕜 G E] (e : Trivialization G (π G E)) [e.IsLinear 𝕜]
    (b : B) : E b ≃L[𝕜] G :=
  open Classical in
  if hb : b ∈ e.baseSet then e.continuousLinearEquivAt 𝕜 b hb
  else VectorBundle.continuousLinearEquivAt 𝕜 G E b

private theorem fiberEquiv_of_mem [VectorBundle 𝕜 G E] (e : Trivialization G (π G E))
    [e.IsLinear 𝕜] {b : B} (hb : b ∈ e.baseSet) :
    fiberEquiv e b = e.continuousLinearEquivAt 𝕜 b hb :=
  dite_eq_left hb

variable [VectorBundle 𝕜 G E]

variable (𝕜) in
/-- The pretrivialization of the projective bundle induced by a linear trivialization `e` of `E`:
over the base set of `e`, it sends a line `ℓ ⊆ E b` to `(b, e_b ℓ)`. -/
def pretrivialization (e : Trivialization G (π G E)) [e.IsLinear 𝕜] :
    Pretrivialization (ℙ 𝕜 G) (π (ℙ 𝕜 G) fun b ↦ ℙ 𝕜 (E b)) where
  toFun p := (p.proj, (fiberEquiv e p.proj).mapProjectivization p.snd)
  invFun q := ⟨q.1, (fiberEquiv e q.1).symm.mapProjectivization q.2⟩
  source := π (ℙ 𝕜 G) (fun b ↦ ℙ 𝕜 (E b)) ⁻¹' e.baseSet
  target := e.baseSet ×ˢ univ
  map_source' _ hp := ⟨hp, mem_univ _⟩
  map_target' _ hq := hq.1
  left_inv' p _ := by simp
  right_inv' q _ := by simp
  open_target := e.open_baseSet.prod isOpen_univ
  baseSet := e.baseSet
  open_baseSet := e.open_baseSet
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

theorem pretrivialization_apply (e : Trivialization G (π G E)) [e.IsLinear 𝕜]
    (p : ProjectiveBundle 𝕜 G E) (hp : p.proj ∈ e.baseSet) :
    pretrivialization 𝕜 e p =
      (p.proj, (e.continuousLinearEquivAt 𝕜 p.proj hp).mapProjectivization p.snd) := by
  simp [pretrivialization, Pretrivialization.toFun', fiberEquiv_of_mem e hp]

theorem pretrivialization_symm_apply (e : Trivialization G (π G E)) [e.IsLinear 𝕜] {b : B}
    (hb : b ∈ e.baseSet) (x : ℙ 𝕜 G) :
    (pretrivialization 𝕜 e).toPartialEquiv.symm (b, x) =
      ⟨b, (e.continuousLinearEquivAt 𝕜 b hb).symm.mapProjectivization x⟩ := by
  rw [← fiberEquiv_of_mem e hb]
  rfl

@[simp]
theorem pretrivialization_source (e : Trivialization G (π G E)) [e.IsLinear 𝕜] :
    (pretrivialization 𝕜 e).source = π (ℙ 𝕜 G) (fun b ↦ ℙ 𝕜 (E b)) ⁻¹' e.baseSet :=
  (rfl)

@[simp]
theorem pretrivialization_target (e : Trivialization G (π G E)) [e.IsLinear 𝕜] :
    (pretrivialization 𝕜 e).target = e.baseSet ×ˢ univ :=
  (rfl)

@[simp]
theorem pretrivialization_baseSet (e : Trivialization G (π G E)) [e.IsLinear 𝕜] :
    (pretrivialization 𝕜 e).baseSet = e.baseSet :=
  (rfl)

@[simp]
theorem proj_pretrivialization_symm (e : Trivialization G (π G E)) [e.IsLinear 𝕜]
    (q : B × ℙ 𝕜 G) : ((pretrivialization 𝕜 e).toPartialEquiv.symm q).proj = q.1 :=
  (rfl)

variable (𝕜 G E) in
/-- The fibre prebundle structure of the projective bundle, with the pretrivializations induced by
the trivializations of the atlas of `E`. -/
def fiberPrebundle : FiberPrebundle (ℙ 𝕜 G) fun b ↦ ℙ 𝕜 (E b) where
  pretrivializationAtlas :=
    {e' | ∃ (e : Trivialization G (π G E)) (_ : MemTrivializationAtlas e),
      e' = pretrivialization 𝕜 e}
  pretrivializationAt b := pretrivialization 𝕜 (trivializationAt G E b)
  mem_base_pretrivializationAt b := mem_baseSet_trivializationAt G E b
  pretrivialization_mem_atlas b := ⟨_, inferInstance, rfl⟩
  continuous_trivChange := by
    rintro _ ⟨e, he, rfl⟩ _ ⟨e', he', rfl⟩
    have hs : (pretrivialization 𝕜 e').target ∩
        (pretrivialization 𝕜 e').toPartialEquiv.symm ⁻¹' (pretrivialization 𝕜 e).source =
        (e'.baseSet ∩ e.baseSet) ×ˢ univ := by
      ext q
      simp only [mem_inter_iff, mem_preimage, proj_pretrivialization_symm, mem_prod, mem_univ,
        and_true, pretrivialization_target, pretrivialization_source]
    rw [hs]
    refine (continuous_fst.continuousOn.prodMk (g := fun q : B × ℙ 𝕜 G ↦
      (e'.coordChangeL 𝕜 e q.1).mapProjectivization q.2) ?_).congr fun q hq ↦ ?_
    · -- The maps of `ℙ 𝕜 G` induced by the coordinate changes of `E` depend jointly continuously
      -- on the base point and the line, by Tau Ceti's `continuousAt_linearProjection`.
      rcases isEmpty_or_nonempty (ℙ 𝕜 G) with hG | hG
      · exact fun q _ ↦ isEmptyElim q.2
      let s := e'.baseSet ∩ e.baseSet
      let L (t : s) : G →ₗ[𝕜] G := (e'.coordChangeL 𝕜 e t : G →L[𝕜] G)
      have hL : Continuous fun p : s × G ↦ L p.1 p.2 :=
        ((continuousOn_coordChange 𝕜 e' e).domRestrict.comp continuous_fst).clm_apply continuous_snd
      have hg : Continuous fun p : s × ℙ 𝕜 G ↦
          (e'.coordChangeL 𝕜 e p.1).mapProjectivization p.2 := by
        refine (continuous_iff_continuousAt.2 fun p ↦ Projectivization.continuousAt_linearProjection
          hL ?_).congr fun p ↦ ?_
        · rw [Projectivization.mem_linearProjectionDomain_iff]
          exact (map_ne_zero_iff _ (e'.coordChangeL 𝕜 e p.1).injective).2 p.2.rep_ne_zero
        · obtain ⟨t, y⟩ := p
          induction y using Projectivization.ind with | h v hv =>
          exact (Projectivization.linearProjection_mk (L t) hv
            ((map_ne_zero_iff _ (e'.coordChangeL 𝕜 e t).injective).2 hv)).trans
            (ContinuousLinearEquiv.mapProjectivization_mk _ v hv).symm
      rw [continuousOn_iff_continuous_domRestrict]
      exact hg.comp (f := fun p : ↥(s ×ˢ (univ : Set (ℙ 𝕜 G))) ↦
        ((⟨p.val.1, p.property.1⟩ : s), p.val.2)) (by fun_prop)
    obtain ⟨⟨hq', hq⟩, -⟩ := hq
    rw [Function.comp_apply, pretrivialization_symm_apply e' hq',
      pretrivialization_apply e _ hq]
    dsimp only
    rw [← e'.comp_continuousLinearEquivAt_eq_coord_change e ⟨hq', hq⟩,
      ContinuousLinearEquiv.mapProjectivization_trans]
    exact congrArg (Prod.mk q.1) (Homeomorph.trans_apply _ _ _).symm
  totalSpaceMk_isInducing b := by
    have hb := mem_baseSet_trivializationAt G E b
    let φ := ((trivializationAt G E b).continuousLinearEquivAt 𝕜 b hb).mapProjectivization
    have h : (pretrivialization 𝕜 (trivializationAt G E b) ∘ TotalSpace.mk b) =
        fun x ↦ (b, φ x) :=
      funext fun x ↦ pretrivialization_apply _ ⟨b, x⟩ hb
    rw [h]
    exact IsInducing.of_comp (by fun_prop) continuous_snd φ.isInducing

instance : TopologicalSpace (ProjectiveBundle 𝕜 G E) := (fiberPrebundle 𝕜 G E).totalSpaceTopology

instance : FiberBundle (ℙ 𝕜 G) fun b ↦ ℙ 𝕜 (E b) := (fiberPrebundle 𝕜 G E).toFiberBundle

theorem trivializationAt_baseSet (b : B) :
    (trivializationAt (ℙ 𝕜 G) (fun b ↦ ℙ 𝕜 (E b)) b).baseSet = (trivializationAt G E b).baseSet :=
  (rfl)

/-- The trivialization of the projective bundle at `b` sends a line `ℓ ⊆ E b'` over a point of
its base set to `(b', e_{b'} ℓ)`, for the trivialization `e` of `E` at `b`. -/
theorem trivializationAt_apply {b : B} (p : ProjectiveBundle 𝕜 G E)
    (hp : p.proj ∈ (trivializationAt G E b).baseSet) :
    trivializationAt (ℙ 𝕜 G) (fun b ↦ ℙ 𝕜 (E b)) b p =
      (p.proj, ((trivializationAt G E b).continuousLinearEquivAt 𝕜 p.proj hp).mapProjectivization
        p.snd) :=
  pretrivialization_apply _ p hp

theorem trivializationAt_symm_apply {b b' : B} (hb' : b' ∈ (trivializationAt G E b).baseSet)
    (x : ℙ 𝕜 G) :
    (trivializationAt (ℙ 𝕜 G) (fun b ↦ ℙ 𝕜 (E b)) b).toOpenPartialHomeomorph.symm (b', x) =
      ⟨b', ((trivializationAt G E b).continuousLinearEquivAt 𝕜 b' hb').symm.mapProjectivization
        x⟩ :=
  pretrivialization_symm_apply _ hb' x

/-- Read in the trivialization of `E` at `b₀`, the inverse of the trivialization maps the line
`p`, read in the trivialization of the projective bundle at `b₀`, into `p`. -/
theorem symmL_mem_submodule {b₀ : B} {p : ProjectiveBundle 𝕜 G E} {w : G}
    (hw : w ∈ (trivializationAt (ℙ 𝕜 G) (fun b ↦ ℙ 𝕜 (E b)) b₀ p).2.submodule) :
    (trivializationAt G E b₀).symmL 𝕜 p.proj w ∈ p.snd.submodule := by
  by_cases hp : p.proj ∈ (trivializationAt G E b₀).baseSet
  · rw [trivializationAt_apply _ hp, ContinuousLinearEquiv.submodule_mapProjectivization] at hw
    obtain ⟨u, hu, rfl⟩ := hw
    rw [← Trivialization.symm_continuousLinearEquivAt_eq' _ hp, ContinuousLinearEquiv.coe_coe]
    simpa [Trivialization.symm_apply_apply_mk _ hp] using hu
  · rw [Trivialization.symmL_apply_of_notMem _ hp]
    exact zero_mem _

/-- On the base set, a vector of the line `p` is sent by the trivialization of `E` at `b₀` into
the line `p` read in the trivialization of the projective bundle at `b₀`. -/
theorem trivializationAt_mem_submodule {b₀ : B} {p : ProjectiveBundle 𝕜 G E}
    (hp : p.proj ∈ (trivializationAt G E b₀).baseSet) {v : E p.proj} (hv : v ∈ p.snd.submodule) :
    (trivializationAt G E b₀ ⟨p.proj, v⟩).2 ∈
      (trivializationAt (ℙ 𝕜 G) (fun b ↦ ℙ 𝕜 (E b)) b₀ p).2.submodule := by
  rw [trivializationAt_apply _ hp, ContinuousLinearEquiv.submodule_mapProjectivization,
    (trivializationAt G E b₀).apply_eq_prod_continuousLinearEquivAt 𝕜 _ hp]
  exact Submodule.mem_map_of_mem hv

/-- Read in the trivialization of `E` at `b`, the line spanned by a nonzero vector `v` over the base
set is the line spanned by the coordinates of `v`. -/
theorem trivializationAt_mk {b : B} (v : TotalSpace G E) (hv : v.snd ≠ 0)
    (hb : v.proj ∈ (trivializationAt G E b).baseSet) :
    trivializationAt (ℙ 𝕜 G) (fun b ↦ ℙ 𝕜 (E b)) b (mk 𝕜 v hv) =
      (v.proj, Projectivization.mk 𝕜 (trivializationAt G E b v).2
        (((trivializationAt G E b).snd_apply_ne_zero_iff 𝕜 hb).2 hv)) := by
  rw [mk_def, trivializationAt_apply _ hb]
  simp

/-- The projective bundle of a vector bundle of rank zero is empty: its fibres have no lines. -/
theorem isEmpty_of_finrank_eq_zero [FiniteDimensional 𝕜 G] (hG : Module.finrank 𝕜 G = 0) :
    IsEmpty (ProjectiveBundle 𝕜 G E) :=
  ⟨fun p ↦ p.snd.rep_ne_zero <| by
    have : Subsingleton G := Module.finrank_zero_iff.1 hG
    have := (VectorBundle.continuousLinearEquivAt 𝕜 G E p.proj).toLinearEquiv.toEquiv.subsingleton
    exact Subsingleton.elim _ _⟩

/-- The line spanned by a nonzero vector depends continuously on the vector. -/
theorem continuous_mk' : Continuous (mk' 𝕜 G E) := by
  refine continuous_iff_continuousAt.2 fun v ↦ ?_
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨((FiberBundle.continuous_proj G E).comp continuous_subtypeVal).continuousAt, ?_⟩
  let e := trivializationAt G E v.val.proj
  let U := {w : zeroSectionCompl G E | w.val.proj ∈ e.baseSet}
  have hU : IsOpen U :=
    e.open_baseSet.preimage ((FiberBundle.continuous_proj G E).comp continuous_subtypeVal)
  refine ContinuousOn.continuousAt ?_ (hU.mem_nhds (mem_baseSet_trivializationAt G E _))
  have he : ContinuousOn (fun w : zeroSectionCompl G E ↦ (e w.val).2) U :=
    (e.continuousOn.comp continuous_subtypeVal.continuousOn fun w hw ↦ e.mem_source.2 hw).snd
  rw [continuousOn_iff_continuous_domRestrict]
  refine (Projectivization.continuous_mk (K := 𝕜) he.domRestrict fun w ↦
    (e.snd_apply_ne_zero_iff 𝕜 w.property).2 (mem_zeroSectionCompl.1 w.val.property)).congr
      fun w ↦ ?_
  exact (congrArg Prod.snd (trivializationAt_mk w.val.val (mem_zeroSectionCompl.1 w.val.property)
    w.property)).symm

/-- The lines spanned by an open set of nonzero vectors form an open set. -/
theorem isOpenMap_mk' : IsOpenMap (mk' 𝕜 G E) := by
  intro U hU
  refine isOpen_iff_forall_mem_open.2 ?_
  rintro _ ⟨v, hvU, rfl⟩
  let e := trivializationAt G E v.val.proj
  let eP := trivializationAt (ℙ 𝕜 G) (fun b ↦ ℙ 𝕜 (E b)) v.val.proj
  -- The nonzero vectors over the base set of `e`, in the coordinates of `e`.
  let σ (q : {q : B × {w : G // w ≠ 0} // q.1 ∈ e.baseSet}) : zeroSectionCompl G E :=
    ⟨e.toOpenPartialHomeomorph.symm (q.val.1, q.val.2.val), by
      rw [← e.mk_symm q.property, mem_zeroSectionCompl]
      exact (e.symm_apply_ne_zero_iff 𝕜 q.property).2 q.val.2.property⟩
  have hσ : Continuous σ :=
    (e.toOpenPartialHomeomorph.continuousOn_symm.comp_continuous
      (f := fun q : {q : B × {w : G // w ≠ 0} // q.1 ∈ e.baseSet} ↦ (q.val.1, q.val.2.val))
      (by fun_prop) fun q ↦
      e.mk_mem_target.2 q.property).subtype_mk _
  have hbase : IsOpen {q : B × {w : G // w ≠ 0} | q.1 ∈ e.baseSet} :=
    e.open_baseSet.preimage continuous_fst
  let W := Subtype.val '' (σ ⁻¹' U)
  have hW : IsOpen W := hbase.isOpenMap_subtypeVal _ (hU.preimage hσ)
  let O := Prod.map id (Projectivization.mk' 𝕜) '' W
  have hO : IsOpen O :=
    (IsOpenQuotientMap.id.prodMap Projectivization.isOpenQuotientMap_mk').isOpenMap _ hW
  have hv : v.val.proj ∈ e.baseSet := mem_baseSet_trivializationAt G E _
  refine ⟨eP.source ∩ eP ⁻¹' O, ?_, eP.isOpen_inter_preimage hO, ?_, ?_⟩
  · rintro p ⟨hp, _, ⟨q, hqU, rfl⟩, hpq⟩
    have h1 : (σ q).val.proj = q.val.1 := e.proj_symm_apply' q.property
    have h2 : e (σ q).val = (q.val.1, q.val.2.val) := e.apply_symm_apply' q.property
    have h3 : (σ q).val.proj ∈ e.baseSet := h1 ▸ q.property
    refine ⟨σ q, hqU, eP.injOn ((eP.mem_source (x := mk' 𝕜 G E (σ q))).2 h3) hp ?_⟩
    rw [Trivialization.coe_coe, ← hpq, mk'_eq_mk, trivializationAt_mk _ _ h3]
    refine Prod.ext h1 ?_
    simp only [Prod.map_snd, Projectivization.mk'_eq_mk]
    congr 1
    exact congrArg Prod.snd h2
  · exact eP.mem_source.2 hv
  · have hv0 : (e v.val).2 ≠ 0 :=
      (e.snd_apply_ne_zero_iff 𝕜 hv).2 (mem_zeroSectionCompl.1 v.property)
    let qv : {q : B × {w : G // w ≠ 0} // q.1 ∈ e.baseSet} := ⟨(v.val.proj, ⟨_, hv0⟩), hv⟩
    have hσv : σ qv = v := Subtype.ext ((congrArg _ (e.mk_proj_snd' hv)).trans
      (e.symm_apply_apply (e.mem_source.2 hv)))
    refine ⟨qv.val, ⟨qv, by simpa only [mem_preimage, hσv] using hvU, rfl⟩, ?_⟩
    · rw [mk'_eq_mk, trivializationAt_mk _ _ hv]
      simp [qv, e, Projectivization.mk'_eq_mk]

/-- **The projective bundle is the quotient of the nonzero vectors.** The map sending a nonzero
vector of `E` to the line it spans is an open quotient map. -/
theorem isOpenQuotientMap_mk' : IsOpenQuotientMap (mk' 𝕜 G E) :=
  ⟨mk'_surjective, continuous_mk', isOpenMap_mk'⟩

/-- A map out of the projective bundle is continuous exactly when it is continuous on the nonzero
vectors of `E`, composed with the map sending a vector to the line it spans. -/
theorem continuous_iff {X : Type*} [TopologicalSpace X] {g : ProjectiveBundle 𝕜 G E → X} :
    Continuous g ↔ Continuous (g ∘ mk' 𝕜 G E) :=
  isOpenQuotientMap_mk'.isQuotientMap.continuous_iff

/-- The line spanned by a continuous family of nonzero vectors of `E` depends continuously on the
parameter. -/
theorem continuous_mk {X : Type*} [TopologicalSpace X] {g : X → TotalSpace G E}
    (hg : Continuous g) (hg₀ : ∀ x, (g x).snd ≠ 0) : Continuous fun x ↦ mk 𝕜 (g x) (hg₀ x) :=
  continuous_mk'.comp (f := fun x ↦ ⟨g x, mem_zeroSectionCompl.2 (hg₀ x)⟩) (hg.subtype_mk _)

/-! ### The projection -/

variable (𝕜 G E) in
/-- The projection of the projective bundle to the base, as a continuous map. -/
@[expose] def projection : C(ProjectiveBundle 𝕜 G E, B) :=
  ⟨TotalSpace.proj, FiberBundle.continuous_proj _ _⟩

@[simp]
theorem projection_apply (p : ProjectiveBundle 𝕜 G E) : projection 𝕜 G E p = p.proj :=
  (rfl)

/-! ### Fibrewise isomorphisms -/

section Map

variable {G' : Type*} [NormedAddCommGroup G'] [NormedSpace 𝕜 G'] {E' : B → Type*}
  [∀ b, AddCommGroup (E' b)] [∀ b, Module 𝕜 (E' b)] [TopologicalSpace (TotalSpace G' E')]
  [∀ b, TopologicalSpace (E' b)] [FiberBundle G' E'] [VectorBundle 𝕜 G' E']

/-- A fibrewise continuous linear equivalence `φ b : E b ≃L[𝕜] E' b` which is continuous on total
spaces induces a continuous map of projective bundles, sending a line `ℓ ⊆ E b` to `φ b ℓ`. -/
theorem continuous_mapProjectivization_of_continuous {φ : ∀ b, E b ≃L[𝕜] E' b}
    (hφ : Continuous fun v : TotalSpace G E ↦ TotalSpace.mk' G' v.proj (φ v.proj v.snd)) :
    Continuous fun p : ProjectiveBundle 𝕜 G E ↦
      (⟨p.proj, (φ p.proj).mapProjectivization p.snd⟩ : ProjectiveBundle 𝕜 G' E') := by
  rw [continuous_iff]
  refine (continuous_mk (hφ.comp continuous_subtypeVal) fun v ↦
    (map_ne_zero_iff _ (φ _).injective).2 (mem_zeroSectionCompl.1 v.property)).congr fun v ↦ ?_
  conv_rhs => rw [Function.comp_apply, mk'_eq_mk, mk_def]
  rw [mk_def]
  simp only [ContinuousLinearEquiv.mapProjectivization_mk]
  rfl

/-- The homeomorphism of projective bundles over `B` induced by a fibrewise continuous linear
equivalence `φ b : E b ≃L[𝕜] E' b` that is continuous on total spaces: it sends a line `ℓ ⊆ E b`
to its image `φ b ℓ`. The inverse is continuous since `G` is finite-dimensional. -/
@[expose] def map [CompleteSpace 𝕜] [FiniteDimensional 𝕜 G] (φ : ∀ b, E b ≃L[𝕜] E' b)
    (hφ : Continuous fun v : TotalSpace G E ↦ TotalSpace.mk' G' v.proj (φ v.proj v.snd)) :
    ProjectiveBundle 𝕜 G E ≃ₜ ProjectiveBundle 𝕜 G' E' where
  toFun p := ⟨p.proj, (φ p.proj).mapProjectivization p.snd⟩
  invFun p := ⟨p.proj, (φ p.proj).symm.mapProjectivization p.snd⟩
  left_inv p := by simp
  right_inv p := by simp
  continuous_toFun := continuous_mapProjectivization_of_continuous hφ
  continuous_invFun := continuous_mapProjectivization_of_continuous (φ := fun b ↦ (φ b).symm)
    (TauCeti.continuous_bundle_symm φ hφ)

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 G] {φ : ∀ b, E b ≃L[𝕜] E' b}
  (hφ : Continuous fun v : TotalSpace G E ↦ TotalSpace.mk' G' v.proj (φ v.proj v.snd))

@[simp]
theorem map_apply (p : ProjectiveBundle 𝕜 G E) :
    map φ hφ p = ⟨p.proj, (φ p.proj).mapProjectivization p.snd⟩ :=
  (rfl)

@[simp]
theorem map_symm_apply (p : ProjectiveBundle 𝕜 G' E') :
    (map φ hφ).symm p = ⟨p.proj, (φ p.proj).symm.mapProjectivization p.snd⟩ :=
  (rfl)

theorem proj_map (p : ProjectiveBundle 𝕜 G E) : (map φ hφ p).proj = p.proj :=
  (rfl)

theorem map_mk (v : TotalSpace G E) (hv : v.snd ≠ 0) :
    map φ hφ (mk 𝕜 v hv) =
      mk 𝕜 (TotalSpace.mk' G' v.proj (φ v.proj v.snd)) ((map_ne_zero_iff _ (φ _).injective).2 hv) :=
  by
  obtain ⟨b, x⟩ := v
  simp

end Map

/-! ### Pull-backs -/

section Pullback

variable {B' : Type*} [TopologicalSpace B'] (f : C(B', B))

variable (𝕜 G E) in
/-- The map from the projective bundle of the pull-back `f *ᵖ E` to that of `E`, over `f`: a line
in the fibre `E (f b')` over `b'` goes to the same line over `f b'`. -/
@[expose] def pullbackMap : C(ProjectiveBundle 𝕜 G (f *ᵖ E), ProjectiveBundle 𝕜 G E) where
  toFun p := ⟨f p.proj, p.snd⟩
  continuous_toFun := by
    rw [continuous_iff]
    exact (continuous_mk ((Pullback.continuous_lift G E f).comp continuous_subtypeVal)
      fun v ↦ (mem_zeroSectionCompl.1 v.property : v.val.snd ≠ 0)).congr fun v ↦ (rfl)

@[simp]
theorem pullbackMap_apply (p : ProjectiveBundle 𝕜 G (f *ᵖ E)) :
    pullbackMap 𝕜 G E f p = ⟨f p.proj, p.snd⟩ :=
  (rfl)

theorem proj_pullbackMap (p : ProjectiveBundle 𝕜 G (f *ᵖ E)) :
    (pullbackMap 𝕜 G E f p).proj = f p.proj :=
  (rfl)

variable (𝕜 G E) in
/-- The projective bundle of the pull-back `f *ᵖ E` is the pull-back along `f` of the projective
bundle of `E`: the two have the same points, and the identity is a homeomorphism. -/
def pullbackHomeomorph :
    ProjectiveBundle 𝕜 G (f *ᵖ E) ≃ₜ TotalSpace (ℙ 𝕜 G) (f *ᵖ fun b ↦ ℙ 𝕜 (E b)) where
  toFun p := ⟨p.proj, p.snd⟩
  invFun p := ⟨p.proj, p.snd⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    Pullback.continuous_iff.2 ⟨FiberBundle.continuous_proj _ _, (pullbackMap 𝕜 G E f).continuous⟩
  continuous_invFun := by
    refine continuous_iff_continuousAt.2 fun z ↦ ?_
    rw [FiberBundle.continuousAt_totalSpace]
    refine ⟨(Pullback.continuous_proj _ _ _).continuousAt, ?_⟩
    let e := trivializationAt G E (f z.proj)
    let eP := trivializationAt (ℙ 𝕜 G) (fun b ↦ ℙ 𝕜 (E b)) (f z.proj)
    have hN : ∀ᶠ y : TotalSpace (ℙ 𝕜 G) (f *ᵖ fun b ↦ ℙ 𝕜 (E b)) in 𝓝 z,
        f y.proj ∈ e.baseSet :=
      (f.continuous.comp (Pullback.continuous_proj _ _ _)).continuousAt
        |>.eventually_mem_baseSet_trivializationAt G E
    refine ContinuousAt.congr (f := fun y ↦ (eP (Pullback.lift f y)).2) ?_ ?_
    · exact (eP.continuousAt (eP.mem_source.2 (mem_baseSet_trivializationAt G E _))).snd.comp
        (Pullback.continuous_lift _ _ f).continuousAt
    · filter_upwards [hN] with ⟨b', x⟩ hy
      have hcle : (trivializationAt G (f *ᵖ E) z.proj).continuousLinearEquivAt 𝕜 b' hy =
          e.continuousLinearEquivAt 𝕜 (f b') hy :=
        Trivialization.continuousLinearEquivAt_pullback (𝕜 := 𝕜) e f b' hy
      -- The families `f *ᵖ fun b ↦ ℙ 𝕜 (E b)` and `fun b' ↦ ℙ 𝕜 ((f *ᵖ E) b')` have the same fibres
      -- by definition of `Bundle.Pullback`; `change` reads `x` as a point of the second one.
      change (eP ⟨f b', x⟩).2 = (trivializationAt (ℙ 𝕜 G) (fun b ↦ ℙ 𝕜 ((f *ᵖ E) b)) z.proj
        (⟨b', x⟩ : ProjectiveBundle 𝕜 G (f *ᵖ E))).2
      rw [trivializationAt_apply (E := E) ⟨f b', x⟩ hy,
        trivializationAt_apply (E := f *ᵖ E) ⟨b', x⟩ hy, hcle]
      rfl

@[simp]
theorem pullbackHomeomorph_apply (p : ProjectiveBundle 𝕜 G (f *ᵖ E)) :
    pullbackHomeomorph 𝕜 G E f p = ⟨p.proj, p.snd⟩ :=
  (rfl)

@[simp]
theorem pullbackHomeomorph_symm_apply (p : TotalSpace (ℙ 𝕜 G) (f *ᵖ fun b ↦ ℙ 𝕜 (E b))) :
    (pullbackHomeomorph 𝕜 G E f).symm p = ⟨p.proj, p.snd⟩ :=
  (rfl)

end Pullback

/-! ### Direct sums -/

section Prod

variable {G₁ : Type*} [NormedAddCommGroup G₁] [NormedSpace 𝕜 G₁] {E₁ : B → Type*}
  [∀ b, AddCommGroup (E₁ b)] [∀ b, Module 𝕜 (E₁ b)] [TopologicalSpace (TotalSpace G₁ E₁)]
  [∀ b, TopologicalSpace (E₁ b)] [FiberBundle G₁ E₁] [VectorBundle 𝕜 G₁ E₁]
  {G₂ : Type*} [NormedAddCommGroup G₂] [NormedSpace 𝕜 G₂] {E₂ : B → Type*}
  [∀ b, AddCommGroup (E₂ b)] [∀ b, Module 𝕜 (E₂ b)] [TopologicalSpace (TotalSpace G₂ E₂)]
  [∀ b, TopologicalSpace (E₂ b)] [FiberBundle G₂ E₂] [VectorBundle 𝕜 G₂ E₂]

variable (G₂ E₂) in
/-- The embedding of the projective bundle of `E₁` into that of the direct sum `E₁ ×ᵇ E₂`: a line
`ℓ ⊆ E₁ b` goes to the line `ℓ × 0`. -/
@[expose] def inl : C(ProjectiveBundle 𝕜 G₁ E₁, ProjectiveBundle 𝕜 (G₁ × G₂) (E₁ ×ᵇ E₂)) where
  toFun p := ⟨p.proj, Projectivization.map (LinearMap.inl 𝕜 (E₁ p.proj) (E₂ p.proj))
    LinearMap.inl_injective p.snd⟩
  continuous_toFun := by
    rw [continuous_iff]
    refine (continuous_mk (g := fun v ↦ TotalSpace.mk' (G₁ × G₂) (E := E₁ ×ᵇ E₂) v.val.proj
      (v.val.snd, 0)) ((FiberBundle.Prod.isInducing_diag G₁ E₁ G₂ E₂).continuous_iff.2
      (continuous_subtypeVal.prodMk ((Trivialization.continuous_zeroSection 𝕜).comp
        ((FiberBundle.continuous_proj G₁ E₁).comp continuous_subtypeVal)))) fun v ↦ ?_).congr
          fun v ↦ ?_
    · simpa using mem_zeroSectionCompl.1 v.property
    · rw [Function.comp_apply, mk'_eq_mk, mk_def, mk_def]
      simp [Projectivization.map_mk]

variable (G₁ E₁) in
/-- The embedding of the projective bundle of `E₂` into that of the direct sum `E₁ ×ᵇ E₂`: a line
`ℓ ⊆ E₂ b` goes to the line `0 × ℓ`. -/
@[expose] def inr : C(ProjectiveBundle 𝕜 G₂ E₂, ProjectiveBundle 𝕜 (G₁ × G₂) (E₁ ×ᵇ E₂)) where
  toFun p := ⟨p.proj, Projectivization.map (LinearMap.inr 𝕜 (E₁ p.proj) (E₂ p.proj))
    LinearMap.inr_injective p.snd⟩
  continuous_toFun := by
    rw [continuous_iff]
    refine (continuous_mk (g := fun v ↦ TotalSpace.mk' (G₁ × G₂) (E := E₁ ×ᵇ E₂) v.val.proj
      (0, v.val.snd)) ((FiberBundle.Prod.isInducing_diag G₁ E₁ G₂ E₂).continuous_iff.2
      (((Trivialization.continuous_zeroSection 𝕜).comp
        ((FiberBundle.continuous_proj G₂ E₂).comp continuous_subtypeVal)).prodMk
          continuous_subtypeVal)) fun v ↦ ?_).congr fun v ↦ ?_
    · simpa using mem_zeroSectionCompl.1 v.property
    · rw [Function.comp_apply, mk'_eq_mk, mk_def, mk_def]
      simp [Projectivization.map_mk]

@[simp]
theorem inl_apply (p : ProjectiveBundle 𝕜 G₁ E₁) :
    inl G₂ E₂ p = ⟨p.proj, Projectivization.map (LinearMap.inl 𝕜 (E₁ p.proj) (E₂ p.proj))
      LinearMap.inl_injective p.snd⟩ :=
  (rfl)

@[simp]
theorem inr_apply (p : ProjectiveBundle 𝕜 G₂ E₂) :
    inr G₁ E₁ p = ⟨p.proj, Projectivization.map (LinearMap.inr 𝕜 (E₁ p.proj) (E₂ p.proj))
      LinearMap.inr_injective p.snd⟩ :=
  (rfl)

theorem inl_mk (v : TotalSpace G₁ E₁) (hv : v.snd ≠ 0) :
    inl G₂ E₂ (mk 𝕜 v hv) =
      mk 𝕜 (TotalSpace.mk' (G₁ × G₂) (E := E₁ ×ᵇ E₂) v.proj (v.snd, 0)) (by simpa using hv) := by
  obtain ⟨b, x⟩ := v
  simp [Projectivization.map_mk]

theorem inr_mk (v : TotalSpace G₂ E₂) (hv : v.snd ≠ 0) :
    inr G₁ E₁ (mk 𝕜 v hv) =
      mk 𝕜 (TotalSpace.mk' (G₁ × G₂) (E := E₁ ×ᵇ E₂) v.proj (0, v.snd)) (by simpa using hv) := by
  obtain ⟨b, x⟩ := v
  simp [Projectivization.map_mk]

theorem mk_mem_range_inl_iff (v : TotalSpace (G₁ × G₂) (E₁ ×ᵇ E₂)) (hv : v.snd ≠ 0) :
    mk 𝕜 v hv ∈ range (inl G₂ E₂) ↔ v.snd.2 = 0 := by
  obtain ⟨b, v₁, v₂⟩ := v
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨p, h⟩
    obtain ⟨⟨⟨b', y⟩, hy⟩, rfl⟩ := mk'_surjective p
    rw [mk'_eq_mk, inl_mk] at h
    obtain rfl : b' = b := congrArg TotalSpace.proj h
    obtain ⟨a, ha⟩ := (mk_eq_mk_iff _ _).1 h
    simpa [Units.smul_def] using congrArg Prod.snd ha
  · have h : v₂ = 0 := h
    have hv₁ : v₁ ≠ 0 := fun h₁ ↦ hv (by simp [h, h₁])
    refine ⟨mk 𝕜 ⟨b, v₁⟩ hv₁, ?_⟩
    rw [inl_mk, mk_mk, mk_mk]
    congr 2
    exact Prod.ext rfl h.symm

theorem mk_mem_range_inr_iff (v : TotalSpace (G₁ × G₂) (E₁ ×ᵇ E₂)) (hv : v.snd ≠ 0) :
    mk 𝕜 v hv ∈ range (inr G₁ E₁) ↔ v.snd.1 = 0 := by
  obtain ⟨b, v₁, v₂⟩ := v
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨p, h⟩
    obtain ⟨⟨⟨b', y⟩, hy⟩, rfl⟩ := mk'_surjective p
    rw [mk'_eq_mk, inr_mk] at h
    obtain rfl : b' = b := congrArg TotalSpace.proj h
    obtain ⟨a, ha⟩ := (mk_eq_mk_iff _ _).1 h
    simpa [Units.smul_def] using congrArg Prod.fst ha
  · have h : v₁ = 0 := h
    have hv₂ : v₂ ≠ 0 := fun h₂ ↦ hv (by simp [h, h₂])
    refine ⟨mk 𝕜 ⟨b, v₂⟩ hv₂, ?_⟩
    rw [inr_mk, mk_mk, mk_mk]
    congr 2
    exact Prod.ext h.symm rfl

/-- The projective bundles of `E₁` and `E₂` meet nowhere in that of `E₁ ×ᵇ E₂`. -/
theorem disjoint_range_inl_inr :
    Disjoint (range (inl G₂ E₂ : _ → ProjectiveBundle 𝕜 (G₁ × G₂) (E₁ ×ᵇ E₂)))
      (range (inr G₁ E₁)) := by
  refine Set.disjoint_left.2 ?_
  rintro _ ⟨p, rfl⟩ hp
  rw [← mk_rep p, inl_mk, mk_mem_range_inr_iff] at hp
  exact p.snd.rep_ne_zero hp

theorem fst_rep_ne_zero_of_notMem_range_inr {p : ProjectiveBundle 𝕜 (G₁ × G₂) (E₁ ×ᵇ E₂)}
    (hp : p ∉ range (inr G₁ E₁)) : p.snd.rep.1 ≠ 0 := by
  rwa [← mk_rep p, mk_mem_range_inr_iff] at hp

/-- The retraction of the complement of the projective bundle of `E₂` in that of `E₁ ×ᵇ E₂` onto
the projective bundle of `E₁`: the line spanned by `(v₁, v₂)`, with `v₁ ≠ 0`, goes to the line
spanned by `v₁`. -/
def inlRetraction :
    C(((range (inr G₁ E₁))ᶜ : Set (ProjectiveBundle 𝕜 (G₁ × G₂) (E₁ ×ᵇ E₂))),
      ProjectiveBundle 𝕜 G₁ E₁) where
  toFun p := mk 𝕜 ⟨p.val.proj, p.val.snd.rep.1⟩ (fst_rep_ne_zero_of_notMem_range_inr p.property)
  continuous_toFun := by
    have hq := (isOpenQuotientMap_mk' (𝕜 := 𝕜) (G := G₁ × G₂) (E := E₁ ×ᵇ E₂)).restrictPreimage
      (range (inr G₁ E₁))ᶜ
    rw [hq.isQuotientMap.continuous_iff]
    refine (continuous_mk (g := fun v ↦ TotalSpace.mk' G₁ v.val.val.proj v.val.val.snd.1)
      ((continuous_fst.comp (FiberBundle.Prod.isInducing_diag G₁ E₁ G₂ E₂).continuous).comp
        (continuous_subtypeVal.comp continuous_subtypeVal))
      fun v ↦ (mk_mem_range_inr_iff _ (mem_zeroSectionCompl.1 v.val.property)).not.1
        v.property).congr fun v ↦ ?_
    obtain ⟨⟨⟨b, w⟩, hw'⟩, hv⟩ := v
    have hw : w ≠ 0 := mem_zeroSectionCompl.1 hw'
    have hw₁ : LinearMap.fst 𝕜 (E₁ b) (E₂ b) w ≠ 0 := (mk_mem_range_inr_iff _ hw).not.1 hv
    have : Nonempty (ℙ 𝕜 (E₁ b)) := ⟨Projectivization.mk 𝕜 _ hw₁⟩
    simp only [Function.comp_apply, restrictPreimage_mk, mk_def]
    congr 1
    -- The line spanned by the first component of a vector depends only on the line of the vector.
    exact (Projectivization.linearProjection_mk _ hw hw₁).symm.trans
      ((congrArg _ (Projectivization.mk_rep _).symm).trans
        (Projectivization.linearProjection_mk _ _ (fst_rep_ne_zero_of_notMem_range_inr hv)))

@[simp]
theorem inlRetraction_apply
    (p : ((range (inr G₁ E₁))ᶜ : Set (ProjectiveBundle 𝕜 (G₁ × G₂) (E₁ ×ᵇ E₂)))) :
    inlRetraction p =
      mk 𝕜 ⟨p.val.proj, p.val.snd.rep.1⟩ (fst_rep_ne_zero_of_notMem_range_inr p.property) :=
  (rfl)

theorem inlRetraction_mk (v : TotalSpace (G₁ × G₂) (E₁ ×ᵇ E₂)) (hv : v.snd ≠ 0)
    (h : mk 𝕜 v hv ∈ (range (inr G₁ E₁))ᶜ) :
    inlRetraction ⟨mk 𝕜 v hv, h⟩ =
      mk 𝕜 ⟨v.proj, v.snd.1⟩ ((mk_mem_range_inr_iff _ hv).not.1 h) := by
  obtain ⟨b, w⟩ := v
  have hw₁ : LinearMap.fst 𝕜 (E₁ b) (E₂ b) w ≠ 0 := (mk_mem_range_inr_iff _ hv).not.1 h
  have : Nonempty (ℙ 𝕜 (E₁ b)) := ⟨Projectivization.mk 𝕜 _ hw₁⟩
  simp only [inlRetraction_apply, mk_mk]
  congr 1
  exact (Projectivization.linearProjection_mk _ _
    (fst_rep_ne_zero_of_notMem_range_inr h)).symm.trans
    ((congrArg _ (Projectivization.mk_rep _)).trans (Projectivization.linearProjection_mk _ hv hw₁))

variable (G₂ E₂) in
/-- The embedding `inl` of the projective bundle of `E₁`, as a map into the complement of the
range of `inr`. -/
def inlCompl :
    C(ProjectiveBundle 𝕜 G₁ E₁,
      ((range (inr G₁ E₁))ᶜ : Set (ProjectiveBundle 𝕜 (G₁ × G₂) (E₁ ×ᵇ E₂)))) :=
  ⟨fun p ↦ ⟨inl G₂ E₂ p, disjoint_left.1 disjoint_range_inl_inr (mem_range_self p)⟩,
    (inl G₂ E₂).continuous.subtype_mk _⟩

@[simp]
theorem coe_inlCompl_apply (p : ProjectiveBundle 𝕜 G₁ E₁) :
    (inlCompl G₂ E₂ p : ProjectiveBundle 𝕜 (G₁ × G₂) (E₁ ×ᵇ E₂)) = inl G₂ E₂ p :=
  (rfl)

/-- `inlRetraction` is a left inverse of `inl`. -/
theorem inlRetraction_inlCompl (p : ProjectiveBundle 𝕜 G₁ E₁) :
    inlRetraction (inlCompl G₂ E₂ p) = p := by
  obtain ⟨⟨v, hv'⟩, rfl⟩ := mk'_surjective p
  have hv : v.snd ≠ 0 := mem_zeroSectionCompl.1 hv'
  have h : inlCompl G₂ E₂ (mk' 𝕜 G₁ E₁ ⟨v, hv'⟩) =
      ⟨mk 𝕜 (TotalSpace.mk' (G₁ × G₂) (E := E₁ ×ᵇ E₂) v.proj (v.snd, 0)) (by simpa using hv),
        by rw [← inl_mk v hv]; exact (inlCompl G₂ E₂ _).property⟩ :=
    Subtype.ext (inl_mk v hv)
  rw [h, inlRetraction_mk, mk'_eq_mk]

theorem isEmbedding_inlCompl : IsEmbedding (inlCompl G₂ E₂ : ProjectiveBundle 𝕜 G₁ E₁ → _) :=
  Function.LeftInverse.isEmbedding inlRetraction_inlCompl inlRetraction.continuous
    (inlCompl G₂ E₂).continuous

/-- The lines of `E₁ ×ᵇ E₂` that do not lie in `E₁` form an open set. -/
theorem isOpen_compl_range_inl :
    IsOpen (range (inl G₂ E₂ : ProjectiveBundle 𝕜 G₁ E₁ → _))ᶜ := by
  rw [← isOpenQuotientMap_mk'.isQuotientMap.isOpen_preimage]
  have hs : Continuous fun v : zeroSectionCompl (G₁ × G₂) (E₁ ×ᵇ E₂) ↦
      TotalSpace.mk' G₂ v.val.proj v.val.snd.2 :=
    (continuous_snd.comp (FiberBundle.Prod.isInducing_diag G₁ E₁ G₂ E₂).continuous).comp
      continuous_subtypeVal
  convert (VectorBundle.isClosed_setOfPred_eq_zero 𝕜 hs).isOpen_compl using 1
  ext v
  simp only [mem_preimage, mem_compl_iff, mem_ofPred_eq, mk'_eq_mk, mk_mem_range_inl_iff]

/-- The projective bundle of `E₁` embeds into that of `E₁ ×ᵇ E₂` as a closed subspace. -/
theorem isClosedEmbedding_inl : IsClosedEmbedding (inl G₂ E₂ : ProjectiveBundle 𝕜 G₁ E₁ → _) :=
  ⟨IsEmbedding.subtypeVal.comp isEmbedding_inlCompl, isOpen_compl_iff.1 isOpen_compl_range_inl⟩

/-- The homeomorphism of projective bundles exchanging the two summands of a direct sum: the line
spanned by `(v₁, v₂)` goes to the line spanned by `(v₂, v₁)`. -/
def prodComm :
    ProjectiveBundle 𝕜 (G₁ × G₂) (E₁ ×ᵇ E₂) ≃ₜ ProjectiveBundle 𝕜 (G₂ × G₁) (E₂ ×ᵇ E₁) where
  toFun p := ⟨p.proj,
    (ContinuousLinearEquiv.prodComm 𝕜 (E₁ p.proj) (E₂ p.proj)).mapProjectivization p.snd⟩
  invFun p := ⟨p.proj,
    (ContinuousLinearEquiv.prodComm 𝕜 (E₂ p.proj) (E₁ p.proj)).mapProjectivization p.snd⟩
  left_inv := by
    rintro ⟨b, x⟩
    induction x using Projectivization.ind with | h x hx => simp
  right_inv := by
    rintro ⟨b, x⟩
    induction x using Projectivization.ind with | h x hx => simp
  continuous_toFun := continuous_mapProjectivization_of_continuous
    (φ := fun b ↦ ContinuousLinearEquiv.prodComm 𝕜 (E₁ b) (E₂ b)) (by
    simp only [ContinuousLinearEquiv.prodComm_apply, Prod.swap]
    exact (FiberBundle.Prod.isInducing_diag G₂ E₂ G₁ E₁).continuous_iff.2
      ((continuous_snd.comp (FiberBundle.Prod.isInducing_diag G₁ E₁ G₂ E₂).continuous).prodMk
        (continuous_fst.comp (FiberBundle.Prod.isInducing_diag G₁ E₁ G₂ E₂).continuous)))
  continuous_invFun := continuous_mapProjectivization_of_continuous
    (φ := fun b ↦ ContinuousLinearEquiv.prodComm 𝕜 (E₂ b) (E₁ b)) (by
    simp only [ContinuousLinearEquiv.prodComm_apply, Prod.swap]
    exact (FiberBundle.Prod.isInducing_diag G₁ E₁ G₂ E₂).continuous_iff.2
      ((continuous_snd.comp (FiberBundle.Prod.isInducing_diag G₂ E₂ G₁ E₁).continuous).prodMk
        (continuous_fst.comp (FiberBundle.Prod.isInducing_diag G₂ E₂ G₁ E₁).continuous)))

@[simp]
theorem prodComm_apply (p : ProjectiveBundle 𝕜 (G₁ × G₂) (E₁ ×ᵇ E₂)) :
    prodComm p = ⟨p.proj,
      (ContinuousLinearEquiv.prodComm 𝕜 (E₁ p.proj) (E₂ p.proj)).mapProjectivization p.snd⟩ :=
  (rfl)

@[simp]
theorem prodComm_symm :
    (prodComm : ProjectiveBundle 𝕜 (G₁ × G₂) (E₁ ×ᵇ E₂) ≃ₜ _).symm = prodComm :=
  (rfl)

theorem prodComm_inl (p : ProjectiveBundle 𝕜 G₁ E₁) : prodComm (inl G₂ E₂ p) = inr G₂ E₂ p := by
  obtain ⟨⟨⟨b, v⟩, hv⟩, rfl⟩ := mk'_surjective p
  rw [mk'_eq_mk, inl_mk, inr_mk]
  simp

theorem prodComm_inr (p : ProjectiveBundle 𝕜 G₂ E₂) : prodComm (inr G₁ E₁ p) = inl G₁ E₁ p := by
  obtain ⟨⟨⟨b, v⟩, hv⟩, rfl⟩ := mk'_surjective p
  rw [mk'_eq_mk, inl_mk, inr_mk]
  simp

/-- The projective bundle of `E₂` embeds into that of `E₁ ×ᵇ E₂` as a closed subspace. -/
theorem isClosedEmbedding_inr : IsClosedEmbedding (inr G₁ E₁ : ProjectiveBundle 𝕜 G₂ E₂ → _) := by
  have h : (inr G₁ E₁ : ProjectiveBundle 𝕜 G₂ E₂ → _) = prodComm ∘ inl G₁ E₁ :=
    funext fun p ↦ (prodComm_inl p).symm
  rw [h]
  exact prodComm.isClosedEmbedding.comp isClosedEmbedding_inl

section Homotopy

variable [NormedAlgebra ℝ 𝕜]

/-- **The deformation retraction onto the projective bundle of `E₁`.** On the complement of the
projective bundle of `E₂` in that of `E₁ ×ᵇ E₂`, the lines spanned by `(v₁, t v₂)`, `t ∈ [0, 1]`,
form a homotopy from `inl ∘ inlRetraction` to the identity. -/
theorem homotopic_inlCompl_comp_inlRetraction :
    ((inlCompl G₂ E₂).comp inlRetraction).Homotopic
      (ContinuousMap.id
        ((range (inr G₁ E₁))ᶜ : Set (ProjectiveBundle 𝕜 (G₁ × G₂) (E₁ ×ᵇ E₂)))) := by
  have hq := (isOpenQuotientMap_mk' (𝕜 := 𝕜) (G := G₁ × G₂) (E := E₁ ×ᵇ E₂)).restrictPreimage
    (range (inr G₁ E₁))ᶜ
  -- The linear map `(v₁, v₂) ↦ (v₁, t v₂)` of a fibre.
  let L (t : unitInterval) (b : B) : (E₁ b × E₂ b) →ₗ[𝕜] E₁ b × E₂ b :=
    LinearMap.id.prodMap (algebraMap ℝ 𝕜 t • LinearMap.id)
  have hL (t : unitInterval) {b : B} {w : E₁ b × E₂ b} (hw : w.1 ≠ 0) : L t b w ≠ 0 :=
    fun h ↦ hw (congrArg Prod.fst h)
  let H (x : unitInterval × ((range (inr G₁ E₁))ᶜ :
      Set (ProjectiveBundle 𝕜 (G₁ × G₂) (E₁ ×ᵇ E₂)))) :
      ((range (inr G₁ E₁))ᶜ : Set (ProjectiveBundle 𝕜 (G₁ × G₂) (E₁ ×ᵇ E₂))) :=
    ⟨mk 𝕜 ⟨x.2.val.proj, L x.1 _ x.2.val.snd.rep⟩
      (hL _ (fst_rep_ne_zero_of_notMem_range_inr x.2.property)),
      (mk_mem_range_inr_iff _ _).not.2 (fst_rep_ne_zero_of_notMem_range_inr x.2.property)⟩
  have hH : Continuous H := by
    rw [(IsOpenQuotientMap.id.prodMap hq).isQuotientMap.continuous_iff]
    have hv : Continuous fun x : unitInterval × (mk' 𝕜 (G₁ × G₂) (E₁ ×ᵇ E₂) ⁻¹'
        (range (inr G₁ E₁))ᶜ) ↦ x.2.val.val :=
      continuous_subtypeVal.comp (continuous_subtypeVal.comp continuous_snd)
    have hg : Continuous fun x : unitInterval × (mk' 𝕜 (G₁ × G₂) (E₁ ×ᵇ E₂) ⁻¹'
        (range (inr G₁ E₁))ᶜ) ↦ TotalSpace.mk' (G₁ × G₂) (E := E₁ ×ᵇ E₂) x.2.val.val.proj
          (x.2.val.val.snd.1, algebraMap ℝ 𝕜 x.1 • x.2.val.val.snd.2) :=
      (FiberBundle.Prod.isInducing_diag G₁ E₁ G₂ E₂).continuous_iff.2
      (((continuous_fst.comp (FiberBundle.Prod.isInducing_diag G₁ E₁ G₂ E₂).continuous).comp
        hv).prodMk (Continuous.smul_totalSpace ((continuous_algebraMap ℝ 𝕜).comp
          (continuous_subtypeVal.comp continuous_fst))
          ((continuous_snd.comp (FiberBundle.Prod.isInducing_diag G₁ E₁ G₂ E₂).continuous).comp
            hv)))
    refine ((continuous_mk hg fun x h ↦
      (mk_mem_range_inr_iff _ (mem_zeroSectionCompl.1 x.2.val.property)).not.1 x.2.property
        (congrArg Prod.fst h)).subtype_mk
      fun x ↦ by
        rw [mem_compl_iff, mk_mem_range_inr_iff]
        exact (mk_mem_range_inr_iff _ (mem_zeroSectionCompl.1 x.2.val.property)).not.1
          x.2.property).congr
      fun x ↦ Subtype.ext ?_
    obtain ⟨t, ⟨⟨b, w⟩, hw'⟩, hx⟩ := x
    have hw : w ≠ 0 := mem_zeroSectionCompl.1 hw'
    have hw₁ : L t b w ≠ 0 := hL t ((mk_mem_range_inr_iff _ hw).not.1 hx)
    have : Nonempty (ℙ 𝕜 (E₁ b × E₂ b)) := ⟨Projectivization.mk 𝕜 _ hw₁⟩
    simp only [H, Function.comp_apply, Prod.map_apply, id_eq, restrictPreimage_mk, mk_def]
    congr 1
    -- The line spanned by `L t b w` depends only on the line spanned by `w`.
    exact (Projectivization.linearProjection_mk (L t b) hw hw₁).symm.trans
      ((congrArg (Projectivization.linearProjection (L t b)) (Projectivization.mk_rep _).symm).trans
        (Projectivization.linearProjection_mk (L t b) _
          (hL t (fst_rep_ne_zero_of_notMem_range_inr hx))))
  refine ⟨⟨⟨H, hH⟩, fun p ↦ ?_, fun p ↦ ?_⟩⟩
  · refine Subtype.ext ?_
    simp [H, L, Projectivization.map_mk]
  · refine Subtype.ext ?_
    simp [H, L]

/-- The projective bundle of `E₁` is homotopy equivalent, through `inl` and `inlRetraction`, to
the complement of the projective bundle of `E₂` in that of `E₁ ×ᵇ E₂`. -/
def inlHomotopyEquiv :
    ContinuousMap.HomotopyEquiv (ProjectiveBundle 𝕜 G₁ E₁)
      ((range (inr G₁ E₁))ᶜ : Set (ProjectiveBundle 𝕜 (G₁ × G₂) (E₁ ×ᵇ E₂))) :=
  ContinuousMap.HomotopyEquiv.ofDeformationRetraction (inlCompl G₂ E₂) inlRetraction
    inlRetraction_inlCompl homotopic_inlCompl_comp_inlRetraction

@[simp]
theorem inlHomotopyEquiv_toFun :
    (inlHomotopyEquiv : ContinuousMap.HomotopyEquiv (ProjectiveBundle 𝕜 G₁ E₁) _).toFun =
      inlCompl G₂ E₂ :=
  ContinuousMap.HomotopyEquiv.ofDeformationRetraction_toFun ..

@[simp]
theorem inlHomotopyEquiv_invFun :
    (inlHomotopyEquiv : ContinuousMap.HomotopyEquiv (ProjectiveBundle 𝕜 G₁ E₁)
      ((range (inr G₁ E₁))ᶜ : Set (ProjectiveBundle 𝕜 (G₁ × G₂) (E₁ ×ᵇ E₂)))).invFun =
      inlRetraction :=
  ContinuousMap.HomotopyEquiv.ofDeformationRetraction_invFun ..

end Homotopy

end Prod

end ProjectiveBundle

end SymplecticGeometry.Bundle

end
