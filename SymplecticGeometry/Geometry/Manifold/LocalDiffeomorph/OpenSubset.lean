/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.Basic

/-!
# Maps into open subsets, and inclusions between them, as local diffeomorphisms

Let `W` be an open subset of a manifold `N`, charted by the restrictions of the charts of `N`. A
map `g` into `W` is a `C^n` local diffeomorphism at `x` exactly when its composite
`Subtype.val ∘ g` with the inclusion of `W` is one: Tau Ceti's
`TauCeti.isLocalDiffeomorph_subtype_val` makes the inclusion a local diffeomorphism, which can be
cancelled on the left (`IsLocalDiffeomorphAt.comp_iff_left`). Continuity of `g` need not be
assumed, since either side gives it, `W` carrying the subspace topology. The domain of `g` is any
manifold, for instance a nested open subset. In particular, for open subsets `U ≤ W` of `M` the
inclusion `Opens.inclusion h : U → W` is a `C^n` local diffeomorphism.

A partial diffeomorphism `Φ : M → N` and an open subset `V` of its target give a diffeomorphism
from the open set `Φ.source ∩ Φ ⁻¹' V` onto `V` that agrees with `Φ`
(`PartialDiffeomorph.exists_diffeomorph_of_subset_target`). It restricts `Φ` with Tau Ceti's
`PartialDiffeomorph.restrOpen`, reads the restriction as a diffeomorphism between its source and
target (`PartialDiffeomorph.toDiffeomorphSourceTarget`), and identifies that target with `V`
(`Diffeomorph.subtype`). The proof adapts the restriction step in the proof of Tau Ceti's
`TauCeti.exists_diffeomorph_opens_of_isInteriorPoint`. Charts adapted to a distribution are
restricted in this way to a product of balls, where the leaves become slices
(`PartialDiffeomorph.exists_diffeomorph_ball_prod_ball`).

## Main results

* `TauCeti.isLocalDiffeomorphAt_subtypeVal_comp_iff`,
  `TauCeti.isLocalDiffeomorph_subtypeVal_comp_iff`: a map into an open subset is a local
  diffeomorphism exactly when its composite with the inclusion of that subset is.
* `TauCeti.isLocalDiffeomorph_inclusion`: the inclusion `U → W` of open subsets `U ≤ W` is a
  `C^n` local diffeomorphism.
* `PartialDiffeomorph.exists_diffeomorph_of_subset_target`: a partial diffeomorphism restricts to
  a diffeomorphism onto any open subset of its target.
* `PartialDiffeomorph.exists_diffeomorph_ball_prod_ball`: a partial diffeomorphism into `F₁ × F₂`
  that sends `x` to `0` and whose target contains the unit ball restricts to a diffeomorphism from
  a neighbourhood of `x` onto the product of the unit balls of `F₁` and `F₂`.
-/

public section

open TopologicalSpace
open scoped Manifold

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {n : WithTop ℕ∞}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type*} [TopologicalSpace G]
  {J : ModelWithCorners 𝕜 F G} {N : Type*} [TopologicalSpace N] [ChartedSpace G N]

/-- A map `g` into an open subset `W` of `N` is a `C^n` local diffeomorphism at `x` if and only if
its composite with the inclusion `W → N` is. -/
theorem isLocalDiffeomorphAt_subtypeVal_comp_iff {W : Opens N} {g : M → W} {x : M} :
    IsLocalDiffeomorphAt I J n (Subtype.val ∘ g) x ↔ IsLocalDiffeomorphAt I J n g x :=
  ⟨fun h ↦ (IsLocalDiffeomorphAt.comp_iff_left (isLocalDiffeomorph_subtype_val _)
      (Topology.IsInducing.subtypeVal.continuousAt_iff.2 h.contMDiffAt.continuousAt)).1 h,
    fun h ↦ h.comp (hg := isLocalDiffeomorph_subtype_val _)⟩

/-- A map `g` into an open subset `W` of `N` is a `C^n` local diffeomorphism if and only if its
composite with the inclusion `W → N` is. -/
theorem isLocalDiffeomorph_subtypeVal_comp_iff {W : Opens N} {g : M → W} :
    IsLocalDiffeomorph I J n (Subtype.val ∘ g) ↔ IsLocalDiffeomorph I J n g :=
  forall_congr' fun _ ↦ isLocalDiffeomorphAt_subtypeVal_comp_iff

/-- For open subsets `U ≤ W` of `M`, each charted by the restrictions of the charts of `M`, the
inclusion `U → W` is a `C^n` local diffeomorphism. -/
theorem isLocalDiffeomorph_inclusion {U W : Opens M} (h : U ≤ W) :
    IsLocalDiffeomorph I I n (Opens.inclusion h) :=
  isLocalDiffeomorph_subtypeVal_comp_iff.1
    ((Set.val_comp_inclusion h).symm ▸ isLocalDiffeomorph_subtype_val)

end TauCeti

namespace PartialDiffeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {n : WithTop ℕ∞}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type*} [TopologicalSpace G]
  {J : ModelWithCorners 𝕜 F G} {N : Type*} [TopologicalSpace N] [ChartedSpace G N]

/-- A partial diffeomorphism `Φ : M → N` restricts to a `C^n` diffeomorphism `Ψ` from the open set
`U = Φ.source ∩ Φ ⁻¹' V` onto any open subset `V` of its target, with `Ψ u = Φ u` for `u ∈ U`;
both open sets carry the charts restricted from `M` and `N`. -/
theorem exists_diffeomorph_of_subset_target (Φ : PartialDiffeomorph I J M N n) (V : Opens N)
    (hV : (V : Set N) ⊆ Φ.target) :
    ∃ (U : Opens M) (Ψ : U ≃ₘ^n⟮I, J⟯ V),
      (U : Set M) = Φ.source ∩ Φ ⁻¹' V ∧ ∀ u : U, (Ψ u : N) = Φ u := by
  have hs : IsOpen (Φ.source ∩ Φ ⁻¹' V) :=
    Φ.toOpenPartialHomeomorph.isOpen_inter_preimage V.isOpen
  let Φ' := Φ.restrOpen _ hs
  have htarget (v : N) : v ∈ Φ'.target ↔ v ∈ V := by
    rw [Φ.restrOpen_target]
    refine ⟨fun hv ↦ Φ.right_inv hv.1 ▸ hv.2.2, fun hv ↦ ?_⟩
    have hvt : v ∈ Φ.target := hV hv
    exact ⟨hvt, Φ.map_target hvt, by simpa [Φ.right_inv hvt] using hv⟩
  refine ⟨⟨Φ'.source, Φ'.open_source⟩, Φ'.toDiffeomorphSourceTarget.trans
    (Diffeomorph.subtype (Diffeomorph.refl _ _ n) fun v ↦ htarget v), by simp [Φ'],
    fun u ↦ ?_⟩
  rw [Diffeomorph.coe_trans, Function.comp_apply]
  refine (Diffeomorph.subtype_apply_coe _ _ _).trans ?_
  rw [Diffeomorph.coe_refl, id, toDiffeomorphSourceTarget_apply_coe, coe_restrOpen]

/-- A partial diffeomorphism `Φ : M → F₁ × F₂` with `Φ x = 0` whose target contains the unit ball
restricts to a `C^n` diffeomorphism `Ψ` from an open neighbourhood `U` of `x` onto the product
`ball 0 1 ×ˢ ball 0 1` of the unit balls of `F₁` and `F₂`, with `Ψ x = 0`; every `u ∈ U` lies in
the source of `Φ`, and `Ψ u = Φ u`. -/
theorem exists_diffeomorph_ball_prod_ball {F₁ F₂ : Type*} [NormedAddCommGroup F₁]
    [NormedSpace 𝕜 F₁] [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
    (Φ : PartialDiffeomorph I 𝓘(𝕜, F₁ × F₂) M (F₁ × F₂) n) {x : M} (hx : x ∈ Φ.source)
    (h0 : Φ x = 0) (hball : Metric.ball 0 1 ⊆ Φ.target) :
    ∃ (U : Opens M) (hxU : x ∈ U) (Ψ : U ≃ₘ^n⟮I, 𝓘(𝕜, F₁ × F₂)⟯
        (⟨Metric.ball 0 1 ×ˢ Metric.ball 0 1, Metric.isOpen_ball.prod Metric.isOpen_ball⟩ :
          Opens (F₁ × F₂))),
      (Ψ ⟨x, hxU⟩ : F₁ × F₂) = 0 ∧ ∀ u : U, (u : M) ∈ Φ.source ∧ (Ψ u : F₁ × F₂) = Φ u := by
  obtain ⟨U, Ψ, hU, hΨ⟩ := Φ.exists_diffeomorph_of_subset_target
    ⟨Metric.ball 0 1 ×ˢ Metric.ball 0 1, Metric.isOpen_ball.prod Metric.isOpen_ball⟩
    (by rw [Opens.coe_mk, ball_prod_same]; exact hball)
  have hmem (y : M) : y ∈ U ↔ y ∈ Φ.source ∧ Φ y ∈ Metric.ball 0 1 ×ˢ Metric.ball 0 1 := by
    rw [← SetLike.mem_coe, hU, Set.mem_inter_iff, Set.mem_preimage, Opens.coe_mk]
  have hxU : x ∈ U := (hmem x).2 ⟨hx, by simp [h0]⟩
  exact ⟨U, hxU, Ψ, by rw [hΨ, h0], fun u ↦ ⟨((hmem u).1 u.property).1, hΨ u⟩⟩

end PartialDiffeomorph

end
