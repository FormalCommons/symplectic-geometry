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
assumed, since either side gives it, `W` carrying the subspace topology. So a map `f` that is a
local diffeomorphism at `x`, with `f x` in `W`, lifts, near `x`, to a map into `W` that is one
too (`IsLocalDiffeomorphAt.exists_subtypeVal_comp_eventuallyEq`): `f` is continuous at `x`, so it
maps a neighbourhood of `x` into `W`; take `f y` where it lies in `W`, and `f x` elsewhere. The
domain of `g` is any manifold, for instance a nested open subset. In particular, for open subsets
`U ≤ W` of `M` the inclusion `Opens.inclusion h : U → W` is a `C^n` local diffeomorphism, and a
map that is a local diffeomorphism at each point of an open subset `U`, and maps `U` into an open
subset `V`, restricts to a local diffeomorphism from `U` to `V`
(`IsLocalDiffeomorphOn.mapsToRestrict`).

For a partial diffeomorphism `Φ`, Tau Ceti's diffeomorphism
`PartialDiffeomorph.toDiffeomorphSourceTarget` between its source and target, followed by the
inclusion of the target, is the inclusion of the source followed by `Φ`
(`PartialDiffeomorph.subtypeVal_comp_toDiffeomorphSourceTarget`). Hence its differential is that
of `Φ` (`PartialDiffeomorph.mfderiv_toDiffeomorphSourceTarget_apply`, by Tau Ceti's
`TauCeti.Manifold.mfderiv_apply_of_subtype_val_comp_eq`), as for Tau Ceti's
`PartialDiffeomorph.liftOpens_comp_subtypeVal` and `PartialDiffeomorph.mfderiv_liftOpens_apply_coe`.

A partial diffeomorphism `Φ : M → N` and an open subset `V` of its target give a diffeomorphism
from the open set `Φ.source ∩ Φ ⁻¹' V` onto `V` that agrees with `Φ`
(`PartialDiffeomorph.exists_diffeomorph_of_subset_target`): it is the restriction
`Diffeomorph.restrOpens`, below, of the diffeomorphism
`PartialDiffeomorph.toDiffeomorphSourceTarget` between the source and the target of `Φ`. Charts
adapted to a distribution are restricted in this way to a product of balls, where the leaves
become slices (`PartialDiffeomorph.exists_diffeomorph_ball_prod_ball`).

A diffeomorphism `Φ` between open subsets `U₀` of `M` and `V₀` of `N` restricts to a
diffeomorphism `Diffeomorph.restrOpens` from `U ≤ U₀` onto `V ≤ V₀`, for open sets that correspond
under `Φ`; it takes the values of `Φ` (`Diffeomorph.coe_restrOpens_apply`). It is Tau Ceti's
`Diffeomorph.subtype`, between the preimages of `U` and `V` in `U₀` and `V₀`, composed on both
sides with Tau Ceti's `Diffeomorph.nestedOpen`. Applied to
`PartialDiffeomorph.toDiffeomorphSourceTarget`, it restricts a partial diffeomorphism to open
subsets of its source and target that correspond under it. For equal open subsets `U = V` of
`M`, `Diffeomorph.setCongr` is the identity of `M` read as a diffeomorphism from `U` to `V`, as
Mathlib's `Homeomorph.setCongr` is for homeomorphisms.

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
(`Diffeomorph.isLocalDiffeomorph_subtypeVal_comp`), by the first point above. So a map that
agrees on an open subset `U` with a diffeomorphism from `U` onto an open subset is a local
diffeomorphism at each point of `U` (`Diffeomorph.isLocalDiffeomorphAt_of_coe_eq`).

## Main results

* `TauCeti.isLocalDiffeomorphAt_subtypeVal_comp_iff`,
  `TauCeti.isLocalDiffeomorph_subtypeVal_comp_iff`: a map into an open subset is a local
  diffeomorphism exactly when its composite with the inclusion of that subset is.
* `IsLocalDiffeomorphAt.exists_subtypeVal_comp_eventuallyEq`: a local diffeomorphism at `x`
  that sends `x` into an open subset lifts, near `x`, to a local diffeomorphism into that subset.
* `IsLocalDiffeomorphOn.mapsToRestrict`: a map that is a local diffeomorphism on an open subset,
  and maps it into an open subset, restricts to a local diffeomorphism between them.
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
* `Diffeomorph.isLocalDiffeomorphAt_of_coe_eq`: a map that agrees on an open subset with a
  diffeomorphism onto an open subset is a local diffeomorphism at each point of that subset.
* `Diffeomorph.restrOpens`, `Diffeomorph.coe_restrOpens_apply`: a diffeomorphism between open
  subsets restricts to a diffeomorphism between smaller open subsets that correspond under it.
* `Diffeomorph.setCongr`, `Diffeomorph.coe_setCongr_apply`: the identity between two equal
  open subsets, as a diffeomorphism.
-/

public section

open TopologicalSpace
open scoped Manifold Topology

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

namespace IsLocalDiffeomorphAt

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {n : WithTop ℕ∞}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type*} [TopologicalSpace G]
  {J : ModelWithCorners 𝕜 F G} {N : Type*} [TopologicalSpace N] [ChartedSpace G N]

/-- A map `f : M → N` that is a `C^n` local diffeomorphism at `x`, with `f x` in an open subset
`W` of `N`, lifts near `x` to a map `g : M → W` that is a `C^n` local diffeomorphism at `x`: its
composite with the inclusion `W → N` agrees with `f` near `x`. -/
theorem exists_subtypeVal_comp_eventuallyEq {W : Opens N} {f : M → N} {x : M}
    (hf : IsLocalDiffeomorphAt I J n f x) (hW : f x ∈ W) :
    ∃ g : M → W, IsLocalDiffeomorphAt I J n g x ∧ Subtype.val ∘ g =ᶠ[𝓝 x] f := by
  classical
  have hW' : ∀ᶠ y in 𝓝 x, f y ∈ W :=
    hf.contMDiffAt.continuousAt.preimage_mem_nhds (W.isOpen.mem_nhds hW)
  let g : M → W := fun y ↦ if h : f y ∈ W then ⟨f y, h⟩ else ⟨f x, hW⟩
  have hg : Subtype.val ∘ g =ᶠ[𝓝 x] f := by
    filter_upwards [hW'] with y hy
    simp only [g, Function.comp_apply, dite_eq_left hy]
  exact ⟨g, TauCeti.isLocalDiffeomorphAt_subtypeVal_comp_iff.1 (hf.congr_of_eventuallyEq hg), hg⟩

end IsLocalDiffeomorphAt

namespace IsLocalDiffeomorphOn

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {n : WithTop ℕ∞}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type*} [TopologicalSpace G]
  {J : ModelWithCorners 𝕜 F G} {N : Type*} [TopologicalSpace N] [ChartedSpace G N]

/-- A map `f : M → N` that is a `C^n` local diffeomorphism on an open subset `U` of `M`, and maps
`U` into an open subset `V` of `N`, restricts to a `C^n` local diffeomorphism from `U` to `V`. -/
theorem mapsToRestrict {f : M → N} {U : Opens M} (hf : IsLocalDiffeomorphOn I J n f U)
    {V : Opens N} (h : Set.MapsTo f U V) :
    IsLocalDiffeomorph (M := U) (N := V) I J n (h.restrict f U V) :=
  TauCeti.isLocalDiffeomorph_subtypeVal_comp_iff.1 fun x ↦
    ((TauCeti.isLocalDiffeomorph_subtype_val (I := I) x).comp (hg := hf x)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall h.val_restrict_apply)

end IsLocalDiffeomorphOn

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
  exact ⟨fun hy ↦ Φ.toPartialEquiv.right_inv hy.1 ▸ hy.2.2,
    fun hy ↦ ⟨ht hy, Φ.map_target (ht hy), by simpa [Φ.toPartialEquiv.right_inv (ht hy)] using hy⟩⟩

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

/-- A map `f : M → N` that agrees on an open subset `U` of `M` with a diffeomorphism `Ψ` from `U`
onto an open subset `V` of `N` is a `C^n` local diffeomorphism at each point of `U`. -/
theorem isLocalDiffeomorphAt_of_coe_eq (Ψ : U ≃ₘ^n⟮I, J⟯ V) {f : M → N}
    (hf : ∀ x : U, f x = Ψ x) (x : U) : IsLocalDiffeomorphAt I J n f x := by
  have h : IsLocalDiffeomorphAt I J n (f ∘ Subtype.val) x :=
    (Ψ.isLocalDiffeomorph_subtypeVal_comp x).congr_of_eventuallyEq
      (Filter.Eventually.of_forall hf)
  exact (TauCeti.isLocalDiffeomorph_subtype_val x).comp_iff_right.1 h

section RestrOpens

variable {U₀ : Opens M} {V₀ : Opens N}

/-- The restriction of a `C^n` diffeomorphism `Φ` between open subsets `U₀` of `M` and `V₀` of
`N` to open subsets `U ≤ U₀` and `V ≤ V₀` that correspond under `Φ`, in that a point of `U₀`
lies in `U` exactly when its image lies in `V`: the diffeomorphism from `U` onto `V` that takes
the values of `Φ` (`Diffeomorph.coe_restrOpens_apply`). -/
noncomputable def restrOpens (Φ : U₀ ≃ₘ^n⟮I, J⟯ V₀) (hU : U ≤ U₀) (hV : V ≤ V₀)
    (h : ∀ x : U₀, (x : M) ∈ U ↔ (Φ x : N) ∈ V) : U ≃ₘ^n⟮I, J⟯ V :=
  (nestedOpen hU).symm.trans
    ((Φ.subtype (U := Opens.comap ⟨Subtype.val, continuous_subtypeVal⟩ U)
      (V := Opens.comap ⟨Subtype.val, continuous_subtypeVal⟩ V) h).trans (nestedOpen hV))

/-- `Diffeomorph.restrOpens` is Tau Ceti's `Diffeomorph.subtype` of `Φ`, between the preimages of
`U` in `U₀` and of `V` in `V₀`, read on `U` and `V` through `Diffeomorph.nestedOpen`. -/
theorem restrOpens_def (Φ : U₀ ≃ₘ^n⟮I, J⟯ V₀) (hU : U ≤ U₀) (hV : V ≤ V₀)
    (h : ∀ x : U₀, (x : M) ∈ U ↔ (Φ x : N) ∈ V) :
    Φ.restrOpens hU hV h = (nestedOpen hU).symm.trans
      ((Φ.subtype (U := Opens.comap ⟨Subtype.val, continuous_subtypeVal⟩ U)
        (V := Opens.comap ⟨Subtype.val, continuous_subtypeVal⟩ V) h).trans (nestedOpen hV)) :=
  (rfl)

/-- The restriction `Diffeomorph.restrOpens` of `Φ` takes the values of `Φ`. -/
@[simp]
theorem coe_restrOpens_apply (Φ : U₀ ≃ₘ^n⟮I, J⟯ V₀) (hU : U ≤ U₀) (hV : V ≤ V₀)
    (h : ∀ x : U₀, (x : M) ∈ U ↔ (Φ x : N) ∈ V) (x : U) :
    (Φ.restrOpens hU hV h x : N) = Φ ⟨x, hU x.property⟩ := by
  simp only [restrOpens_def, coe_trans, Function.comp_apply, nestedOpen_apply,
    nestedOpen_symm_apply]
  exact congrArg Subtype.val <| Φ.subtype_apply_coe
    (U := Opens.comap ⟨Subtype.val, continuous_subtypeVal⟩ U)
    (V := Opens.comap ⟨Subtype.val, continuous_subtypeVal⟩ V) h
      ⟨⟨x, hU x.property⟩, x.property⟩

/-- The inverse of the restriction `Diffeomorph.restrOpens` of `Φ` takes the values of the
inverse of `Φ`. -/
@[simp]
theorem coe_restrOpens_symm_apply (Φ : U₀ ≃ₘ^n⟮I, J⟯ V₀) (hU : U ≤ U₀) (hV : V ≤ V₀)
    (h : ∀ x : U₀, (x : M) ∈ U ↔ (Φ x : N) ∈ V) (y : V) :
    ((Φ.restrOpens hU hV h).symm y : M) = Φ.symm ⟨y, hV y.property⟩ := by
  simp only [restrOpens_def, symm_trans', symm_symm, coe_trans, Function.comp_apply,
    nestedOpen_symm_apply, nestedOpen_apply]
  exact congrArg Subtype.val <| Φ.subtype_symm_apply_coe
    (U := Opens.comap ⟨Subtype.val, continuous_subtypeVal⟩ U)
    (V := Opens.comap ⟨Subtype.val, continuous_subtypeVal⟩ V) h
      ⟨⟨y, hV y.property⟩, y.property⟩

end RestrOpens

section SetCongr

/-- The identity of `M` as a `C^n` diffeomorphism between two equal open subsets `U = V` of `M`,
the smooth form of Mathlib's `Homeomorph.setCongr`. -/
def setCongr {U V : Opens M} (h : U = V) : U ≃ₘ^n⟮I, I⟯ V :=
  (Diffeomorph.refl I M n).subtype fun _ ↦ by rw [h, coe_refl, id_eq]

/-- `Diffeomorph.setCongr` is Tau Ceti's `Diffeomorph.subtype` of the identity of `M`. -/
theorem setCongr_def {U V : Opens M} (h : U = V) :
    setCongr (I := I) (n := n) h =
      (Diffeomorph.refl I M n).subtype fun _ ↦ by rw [h, coe_refl, id_eq] :=
  (rfl)

/-- The diffeomorphism `Diffeomorph.setCongr` keeps the underlying point. -/
@[simp]
theorem coe_setCongr_apply {U V : Opens M} (h : U = V) (x : U) :
    (setCongr (I := I) (n := n) h x : M) = x :=
  subtype_apply_coe _ _ x

/-- The inverse of `Diffeomorph.setCongr` keeps the underlying point. -/
@[simp]
theorem coe_setCongr_symm_apply {U V : Opens M} (h : U = V) (y : V) :
    ((setCongr (I := I) (n := n) h).symm y : M) = y :=
  subtype_symm_apply_coe _ _ y

end SetCongr

end Diffeomorph

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
  refine ⟨⟨_, hs⟩, Φ.toDiffeomorphSourceTarget.restrOpens (U := ⟨_, hs⟩) (V := V)
    (SetLike.coe_subset_coe.1 Set.inter_subset_left) (SetLike.coe_subset_coe.1 hV) fun x ↦ ?_,
    Opens.coe_mk, fun u ↦ ?_⟩
  · rw [Opens.mem_mk, Set.mem_inter_iff, Set.mem_preimage, toDiffeomorphSourceTarget_apply_coe]
    exact and_iff_right (Opens.mem_mk.1 x.property)
  · exact (Diffeomorph.coe_restrOpens_apply _ _ _ _ u).trans
      (toDiffeomorphSourceTarget_apply_coe _ _)

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
