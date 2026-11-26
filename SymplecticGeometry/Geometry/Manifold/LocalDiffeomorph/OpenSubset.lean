/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.Diffeomorph.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic

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

For a partial diffeomorphism `Φ`, Tau Ceti's diffeomorphism
`PartialDiffeomorph.toDiffeomorphSourceTarget` between its source and target, followed by the
inclusion of the target, is the inclusion of the source followed by `Φ`
(`PartialDiffeomorph.subtypeVal_comp_toDiffeomorphSourceTarget`). Hence its differential is that
of `Φ` (`PartialDiffeomorph.mfderiv_toDiffeomorphSourceTarget_apply`, by Tau Ceti's
`TauCeti.Manifold.mfderiv_apply_of_subtype_val_comp_eq`), as for Tau Ceti's
`PartialDiffeomorph.liftOpens_comp_subtypeVal` and `PartialDiffeomorph.mfderiv_liftOpens_apply_coe`.

A partial diffeomorphism `Φ : M → N` and an open subset `V` of its target give a diffeomorphism
from the open set `Φ.source ∩ Φ ⁻¹' V` onto `V` that agrees with `Φ`
(`PartialDiffeomorph.exists_diffeomorph_of_subset_target`). It restricts `Φ` with Tau Ceti's
`PartialDiffeomorph.restrOpen`, reads the restriction as a diffeomorphism between its source and
target (`PartialDiffeomorph.toDiffeomorphSourceTarget`), and identifies that target with `V`
(`Diffeomorph.subtype`). The proof adapts the restriction step in the proof of Tau Ceti's
`TauCeti.exists_diffeomorph_opens_of_isInteriorPoint`. Charts adapted to a distribution are
restricted in this way to a product of balls, where the leaves become slices
(`PartialDiffeomorph.exists_diffeomorph_ball_prod_ball`).

Tau Ceti reads a partial diffeomorphism `Φ` between open subsets `U` and `V` in the ambient
manifolds as `PartialDiffeomorph.liftOpens`. The points of the source of `Φ` lie in the source
of the lift, and there the diffeomorphism between the source and the target of the lift takes the
values of `Φ` (Tau Ceti's `PartialDiffeomorph.liftOpens_source`,
`PartialDiffeomorph.liftOpens_apply_coe` and
`PartialDiffeomorph.toDiffeomorphSourceTarget_apply_coe`). When `U = V`, it has identity
differential at a point exactly when `Φ` has, by Tau Ceti's
`TauCeti.Manifold.mfderiv_eq_id_iff_of_comp_subtype_val`; so a point that `Φ` fixes with identity
differential is fixed by it, with identity differential. The lift maps a subset `C` of `U` onto
the image of `C` under `Φ` (`PartialDiffeomorph.image_liftOpens`). When `Φ` is a diffeomorphism
between `U` and `V`, the lift has source `U` and target `V`, and takes the values of `Φ` on `U`
(`Diffeomorph.toPartialDiffeomorph_liftOpens_source`,
`Diffeomorph.toPartialDiffeomorph_liftOpens_target`,
`Diffeomorph.toPartialDiffeomorph_liftOpens_apply_coe`). A diffeomorphism from `M` onto an open
subset of `N`, followed by the inclusion, is a local diffeomorphism from `M` to `N`
(`Diffeomorph.isLocalDiffeomorph_subtypeVal_comp`), by the first point above.

## Main results

* `TauCeti.isLocalDiffeomorphAt_subtypeVal_comp_iff`,
  `TauCeti.isLocalDiffeomorph_subtypeVal_comp_iff`: a map into an open subset is a local
  diffeomorphism exactly when its composite with the inclusion of that subset is.
* `TauCeti.isLocalDiffeomorph_inclusion`: the inclusion `U → W` of open subsets `U ≤ W` is a
  `C^n` local diffeomorphism.
* `PartialDiffeomorph.restrOpen_target_eq_of_subset`: restricting a partial diffeomorphism to the
  preimage of a subset of its target gives one with that subset as target.
* `PartialDiffeomorph.exists_diffeomorph_of_subset_target`: a partial diffeomorphism restricts to
  a diffeomorphism onto any open subset of its target.
* `PartialDiffeomorph.exists_diffeomorph_ball_prod_ball`: a partial diffeomorphism into `F₁ × F₂`
  that sends `x` to `0` and whose target contains the unit ball restricts to a diffeomorphism from
  a neighbourhood of `x` onto the product of the unit balls of `F₁` and `F₂`.
* `PartialDiffeomorph.exists_toDiffeomorphSourceTarget_liftOpens_eq_and_mfderiv_eq_id`: a fixed
  point of a partial diffeomorphism of an open subset with identity differential stays one when
  the partial diffeomorphism is read in the ambient manifold.
* `PartialDiffeomorph.image_liftOpens`: a partial diffeomorphism between open subsets `U` and
  `V`, read as a partial diffeomorphism of the ambient manifolds, maps each subset of `U` onto its
  image under it.
* `Diffeomorph.toPartialDiffeomorph_liftOpens_source`,
  `Diffeomorph.toPartialDiffeomorph_liftOpens_target`,
  `Diffeomorph.toPartialDiffeomorph_liftOpens_apply_coe`: a diffeomorphism between open subsets
  `U` and `V`, read as a partial diffeomorphism of the ambient manifolds, has source `U` and
  target `V`, and agrees with the diffeomorphism on `U`.
* `Diffeomorph.isLocalDiffeomorph_subtypeVal_comp`: a diffeomorphism onto an open subset,
  followed by the inclusion of that subset, is a local diffeomorphism.
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

/-- The diffeomorphism between the source and the target of a partial diffeomorphism `Φ`, followed
by the inclusion of the target, is `Φ` on the source. -/
theorem subtypeVal_comp_toDiffeomorphSourceTarget (Φ : PartialDiffeomorph I J M N n) :
    Subtype.val ∘ ⇑Φ.toDiffeomorphSourceTarget = ⇑Φ ∘ Subtype.val :=
  funext Φ.toDiffeomorphSourceTarget_apply_coe

/-- The diffeomorphism between the source and the target of a partial diffeomorphism `Φ` has the
differential of `Φ`, the tangent spaces of the source and the target being those of `M` and
`N`. -/
theorem mfderiv_toDiffeomorphSourceTarget_apply (Φ : PartialDiffeomorph I J M N n)
    (x : (⟨Φ.source, Φ.open_source⟩ : Opens M)) (v : TangentSpace I (x : M)) :
    mfderiv I J Φ.toDiffeomorphSourceTarget x v = mfderiv I J Φ x v :=
  TauCeti.Manifold.mfderiv_apply_of_subtype_val_comp_eq
    Φ.subtypeVal_comp_toDiffeomorphSourceTarget v

/-- Restricting a partial diffeomorphism `Φ` to the open set `Φ.source ∩ Φ ⁻¹' t`, for a subset `t`
of its target, gives a partial diffeomorphism with target `t`. -/
theorem restrOpen_target_eq_of_subset (Φ : PartialDiffeomorph I J M N n) {t : Set N}
    (ht : t ⊆ Φ.target) (hs : IsOpen (Φ.source ∩ Φ ⁻¹' t)) :
    (Φ.restrOpen _ hs).target = t := by
  ext y
  rw [Φ.restrOpen_target]
  exact ⟨fun hy ↦ Φ.right_inv hy.1 ▸ hy.2.2,
    fun hy ↦ ⟨ht hy, Φ.map_target (ht hy), by simpa [Φ.right_inv (ht hy)] using hy⟩⟩

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
    rw [Φ.restrOpen_target_eq_of_subset hV hs, SetLike.mem_coe]
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

section LiftOpens

variable {U : Opens M}

/-- Let `Φ` be a partial diffeomorphism of an open subset `U` of `M`. At a point `x` of `U` in the
source of `Φ.liftOpens`, the diffeomorphism between the source and the target of `Φ.liftOpens`
has identity differential if and only if `Φ` has identity differential at `x`. -/
theorem mfderiv_toDiffeomorphSourceTarget_liftOpens_eq_id_iff (Φ : PartialDiffeomorph I I U U n)
    (hU : Nonempty U) (x : U) (hx : (x : M) ∈ (Φ.liftOpens hU hU).source) :
    mfderiv I I (Φ.liftOpens hU hU).toDiffeomorphSourceTarget ⟨x, hx⟩ =
        ContinuousLinearMap.id 𝕜 (TangentSpace I (x : M)) ↔
      mfderiv I I Φ x = ContinuousLinearMap.id 𝕜 (TangentSpace I x) :=
  (TauCeti.Manifold.mfderiv_eq_id_iff_of_comp_subtype_val
      (Φ.liftOpens hU hU).subtypeVal_comp_toDiffeomorphSourceTarget).trans
    (TauCeti.Manifold.mfderiv_eq_id_iff_of_comp_subtype_val
      (Φ.liftOpens_comp_subtypeVal hU hU).symm).symm

/-- If a partial diffeomorphism `Φ` of an open subset `U` of `M` fixes a point `x` of its source,
with identity differential there, then `x` lies in the source of `Φ.liftOpens`, and the
diffeomorphism between the source and the target of `Φ.liftOpens` fixes `x`, with identity
differential there. -/
theorem exists_toDiffeomorphSourceTarget_liftOpens_eq_and_mfderiv_eq_id
    (Φ : PartialDiffeomorph I I U U n) (hU : Nonempty U) {x : U} (hx : x ∈ Φ.source)
    (hfix : Φ x = x) (hd : mfderiv I I Φ x = ContinuousLinearMap.id 𝕜 (TangentSpace I x)) :
    ∃ h : (x : M) ∈ (Φ.liftOpens hU hU).source,
      ((Φ.liftOpens hU hU).toDiffeomorphSourceTarget ⟨x, h⟩ : M) = x ∧
      mfderiv I I (Φ.liftOpens hU hU).toDiffeomorphSourceTarget ⟨x, h⟩ =
        ContinuousLinearMap.id 𝕜 (TangentSpace I (x : M)) :=
  ⟨by simp [hx], by simp [hfix],
    (Φ.mfderiv_toDiffeomorphSourceTarget_liftOpens_eq_id_iff hU x _).2 hd⟩

/-- A partial diffeomorphism `Ψ` between open subsets `U` of `M` and `V` of `N`, read as a partial
diffeomorphism from `M` to `N`, maps a subset `C` of `U` onto the image of `C` under `Ψ`. -/
theorem image_liftOpens {V : Opens N} (Ψ : PartialDiffeomorph I J U V n) (hU : Nonempty U)
    (hV : Nonempty V) {C : Set M} (hC : C ⊆ U) :
    Ψ.liftOpens hU hV '' C = (fun x : U ↦ (Ψ x : N)) '' (Subtype.val ⁻¹' C) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hC hx⟩, hx, (Ψ.liftOpens_apply_coe hU hV _).symm⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, Ψ.liftOpens_apply_coe hU hV x⟩

end LiftOpens

end PartialDiffeomorph

namespace Diffeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {n : WithTop ℕ∞}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type*} [TopologicalSpace G]
  {J : ModelWithCorners 𝕜 F G} {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {U : Opens M} {V : Opens N} (Φ : U ≃ₘ^n⟮I, J⟯ V) (hU : Nonempty U) (hV : Nonempty V)

/-- A diffeomorphism `Φ` between open subsets `U` of `M` and `V` of `N`, read as a partial
diffeomorphism from `M` to `N`, has source `U`. -/
theorem toPartialDiffeomorph_liftOpens_source :
    (Φ.toPartialDiffeomorph.liftOpens hU hV).source = U := by
  simp

/-- A diffeomorphism `Φ` between open subsets `U` of `M` and `V` of `N`, read as a partial
diffeomorphism from `M` to `N`, has target `V`. -/
theorem toPartialDiffeomorph_liftOpens_target :
    (Φ.toPartialDiffeomorph.liftOpens hU hV).target = V := by
  simp

/-- A diffeomorphism `Φ` between open subsets `U` of `M` and `V` of `N`, read as a partial
diffeomorphism from `M` to `N`, takes the values of `Φ` on `U`. -/
theorem toPartialDiffeomorph_liftOpens_apply_coe (x : U) :
    Φ.toPartialDiffeomorph.liftOpens hU hV x = Φ x := by
  rw [PartialDiffeomorph.liftOpens_apply_coe, coe_toPartialDiffeomorph]

/-- A diffeomorphism `Ψ` from `M` onto an open subset `V` of `N`, followed by the inclusion of `V`,
is a `C^n` local diffeomorphism from `M` to `N`. -/
theorem isLocalDiffeomorph_subtypeVal_comp (Ψ : M ≃ₘ^n⟮I, J⟯ V) :
    IsLocalDiffeomorph I J n (fun x ↦ (Ψ x : N)) :=
  TauCeti.isLocalDiffeomorph_subtypeVal_comp_iff.2 Ψ.isLocalDiffeomorph

end Diffeomorph

end
