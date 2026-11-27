/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Gluing.Pair
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.GroupTheory.QuotientGroup.Basic

import SymplecticGeometry.AlgebraicTopology.FundamentalGroup.VanKampen
import TauCeti.AlgebraicTopology.FundamentalGroup.HomotopyEquiv

/-!
# The fundamental group of two spaces glued along open subsets

Let `φ : U₁ ≃ₜ U₂` be a homeomorphism of open subsets of `M₁` and `M₂`. The glued space
`GluedAlong φ` is covered by the open ranges of `inl` and `inr`, which meet in `inl '' U₁`
(`GluedAlong.range_inl_inter_range_inr`). So it is path connected when `M₁` and `M₂` are and
`U₁` is nonempty, and by van Kampen, when moreover `U₁` is path connected and `M₂` is simply
connected, `inl` induces a surjection `π₁(M₁, x) → π₁(GluedAlong φ, inl x)` for `x ∈ U₁`,
whose kernel is the normal closure of the image of `π₁(U₁, x)`: gluing a simply connected
space along `U₁` kills exactly the loops of `U₁`.

The proof applies `FundamentalGroup.map_subtypeVal_surjective_of_simplyConnectedSpace` and
`FundamentalGroup.ker_map_subtypeVal_eq_normalClosure_range_of_simplyConnectedSpace` to the cover
of the glued space by the ranges of `inl` and `inr`, the latter homeomorphic to `M₂`, and
transports the result to `M₁` and `U₁` along the homeomorphisms of `M₁` onto the range of `inl`
and of `U₁` onto the overlap. The bijectivity of the induced maps of these homeomorphisms is
Tau Ceti's `ContinuousMap.HomotopyEquiv.fundamentalGroup_map_bijective`.

## Main results

* `SymplecticGeometry.GluedAlong.pathConnectedSpace`: the glued space is path connected.
* `SymplecticGeometry.GluedAlong.map_inl_surjective`,
  `SymplecticGeometry.GluedAlong.ker_map_inl`: the map induced by `inl` on fundamental groups
  is surjective, with kernel the normal closure of the image of `π₁(U₁, x)`.
* `SymplecticGeometry.GluedAlong.fundamentalGroupMulEquiv`: the resulting isomorphism from the
  quotient of `π₁(M₁, x)` onto `π₁(GluedAlong φ, inl x)`, and its values
  `fundamentalGroupMulEquiv_mk`, `fundamentalGroupMulEquiv_mk_fromPath`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Cambridge University Press, 2002, Theorem 1.20.
-/

public section

noncomputable section

open Set TopologicalSpace Topology

namespace SymplecticGeometry

namespace GluedAlong

universe u

variable {M₁ M₂ : Type u} [TopologicalSpace M₁] [TopologicalSpace M₂]
  {U₁ : Opens M₁} {U₂ : Opens M₂} (φ : U₁ ≃ₜ U₂)

/-- The space glued from two path connected spaces along a nonempty open subset is path
connected. -/
theorem pathConnectedSpace [PathConnectedSpace M₁] [PathConnectedSpace M₂]
    (hU : (U₁ : Set M₁).Nonempty) : PathConnectedSpace (GluedAlong φ) := by
  obtain ⟨x, hx⟩ := hU
  rw [pathConnectedSpace_iff_univ, ← range_inl_union_range_inr]
  exact (isPathConnected_range (continuous_inl φ)).union (isPathConnected_range (continuous_inr φ))
    (range_inl_inter_range_inr φ ▸ ⟨inl φ x, x, hx, rfl⟩)

/-- The map `π₁(M₁, x) → π₁(GluedAlong φ, inl x)` induced by `inl`, read through the
homeomorphism of `M₁` onto the range of `inl`, is the map induced by the inclusion of that
range. -/
private theorem map_inlContinuousMap_eq (x : M₁) :
    FundamentalGroup.map (inlContinuousMap φ) x =
      (FundamentalGroup.map (ContinuousMap.subtypeVal (range (inl φ)))
        ⟨inl φ x, mem_range_self _⟩).comp
      (FundamentalGroup.map
        ((isOpenEmbedding_inl φ).isEmbedding.toHomeomorph : C(M₁, range (inl φ))) x) :=
  FundamentalGroup.map_comp (ContinuousMap.subtypeVal (range (inl φ)))
    ((isOpenEmbedding_inl φ).isEmbedding.toHomeomorph : C(M₁, range (inl φ))) x

variable [PathConnectedSpace M₁] [SimplyConnectedSpace M₂]

/-- The surjectivity and the kernel of the map induced by the inclusion of the range of `inl`,
at `inl x`, given by van Kampen with the simply connected range of `inr`. -/
private theorem vanKampen (hU : IsPathConnected (U₁ : Set M₁)) (x : U₁) :
    Function.Surjective (FundamentalGroup.map (ContinuousMap.subtypeVal (range (inl φ)))
        ⟨inl φ x, mem_range_self _⟩) ∧
      (FundamentalGroup.map (ContinuousMap.subtypeVal (range (inl φ)))
        ⟨inl φ x, mem_range_self _⟩).ker = Subgroup.normalClosure
          (range (FundamentalGroup.map (ContinuousMap.inclusion inter_subset_left)
            (⟨inl φ x, mem_range_self _, inl_mem_range_inr_iff φ |>.2 x.property⟩ :
              ↥(range (inl φ) ∩ range (inr φ))))) := by
  have hCover : interior (range (inl φ)) ∪ interior (range (inr φ)) = univ := by
    rw [(isOpen_range_inl φ).interior_eq, (isOpen_range_inr φ).interior_eq,
      range_inl_union_range_inr]
  have : SimplyConnectedSpace (range (inr φ)) :=
    (isOpenEmbedding_inr φ).isEmbedding.toHomeomorph.symm.toHomotopyEquiv.simplyConnectedSpace
  have hAB : IsPathConnected (range (inl φ) ∩ range (inr φ)) :=
    range_inl_inter_range_inr φ ▸ hU.image (continuous_inl φ)
  have hxB := inl_mem_range_inr_iff φ |>.2 x.property
  exact ⟨FundamentalGroup.map_subtypeVal_surjective_of_simplyConnectedSpace
      hCover (isPathConnected_range (continuous_inl φ)) hAB (mem_range_self _) hxB,
    FundamentalGroup.ker_map_subtypeVal_eq_normalClosure_range_of_simplyConnectedSpace
      hCover (isPathConnected_range (continuous_inl φ)) hAB (mem_range_self _) hxB⟩

/-- **Van Kampen for the glued space, surjectivity.** If `M₁` is path connected, `M₂` simply
connected and `U₁` path connected, then for `x ∈ U₁` the map `π₁(M₁, x) → π₁(GluedAlong φ, inl x)`
induced by `inl` is surjective. -/
theorem map_inl_surjective (hU : IsPathConnected (U₁ : Set M₁)) (x : U₁) :
    Function.Surjective (FundamentalGroup.map (inlContinuousMap φ) (x : M₁)) := by
  intro q
  obtain ⟨p, rfl⟩ := (vanKampen φ hU x).1 q
  obtain ⟨r, rfl⟩ := ((isOpenEmbedding_inl φ).isEmbedding.toHomeomorph.toHomotopyEquiv
    |>.fundamentalGroup_map_bijective (x : M₁)).surjective p
  exact ⟨r, by rw [map_inlContinuousMap_eq]; exact MonoidHom.comp_apply _ _ _⟩

/-- **Van Kampen for the glued space, the kernel.** If `M₁` is path connected, `M₂` simply
connected and `U₁` path connected, then for `x ∈ U₁` the kernel of the map
`π₁(M₁, x) → π₁(GluedAlong φ, inl x)` induced by `inl` is the normal closure of the range of the
map induced by the inclusion `U₁ → M₁`. -/
-- The domain of `subtypeVal` is given as `↥U₁`, the `simp` normal form of `↥(U₁ : Set M₁)`,
-- so that `simp` lemmas about these maps, such as `fundamentalGroupMulEquiv_mk`, still apply
-- after `SetLike.coe_sort_coe`.
theorem ker_map_inl (hU : IsPathConnected (U₁ : Set M₁)) (x : U₁) :
    (FundamentalGroup.map (inlContinuousMap φ) (x : M₁)).ker =
      Subgroup.normalClosure
        (range (FundamentalGroup.map (X := U₁) (ContinuousMap.subtypeVal (U₁ : Set M₁)) x) :
          Set (FundamentalGroup M₁ x)) := by
  let e := (isOpenEmbedding_inl φ).isEmbedding.toHomeomorph
  let e' : U₁ ≃ₜ ↥(range (inl φ) ∩ range (inr φ)) :=
    ((isOpenEmbedding_inl φ).isEmbedding.homeomorphImage (U₁ : Set M₁)).trans
      (Homeomorph.setCongr (range_inl_inter_range_inr φ).symm)
  have hsq : (FundamentalGroup.map (e : C(M₁, range (inl φ))) (x : M₁)).comp
      (FundamentalGroup.map (X := U₁) (ContinuousMap.subtypeVal (U₁ : Set M₁)) x) =
      (FundamentalGroup.map (ContinuousMap.inclusion inter_subset_left)
        (⟨inl φ x, mem_range_self _, inl_mem_range_inr_iff φ |>.2 x.property⟩ :
          ↥(range (inl φ) ∩ range (inr φ)))).comp
      (FundamentalGroup.map (e' : C(U₁, ↥(range (inl φ) ∩ range (inr φ)))) x) :=
    (FundamentalGroup.map_comp _ _ _).symm.trans
      (FundamentalGroup.map_comp (ContinuousMap.inclusion inter_subset_left)
        (e' : C(U₁, ↥(range (inl φ) ∩ range (inr φ)))) x)
  have hf := e.toHomotopyEquiv.fundamentalGroup_map_bijective (x : M₁)
  -- The steps below are stated as terms: their base points agree only up to unfolding `e`.
  have hrange : range (FundamentalGroup.map (ContinuousMap.inclusion inter_subset_left)
      (⟨inl φ x, mem_range_self _, inl_mem_range_inr_iff φ |>.2 x.property⟩ :
        ↥(range (inl φ) ∩ range (inr φ)))) =
      FundamentalGroup.map (e : C(M₁, range (inl φ))) (x : M₁) ''
        range (FundamentalGroup.map (X := U₁) (ContinuousMap.subtypeVal (U₁ : Set M₁)) x) :=
    ((e'.toHomotopyEquiv.fundamentalGroup_map_bijective x).surjective.range_comp _).symm.trans
      ((congrArg (fun h : FundamentalGroup U₁ x →* _ ↦ range ⇑h) hsq.symm).trans
        (range_comp (FundamentalGroup.map (e : C(M₁, range (inl φ))) (x : M₁))
          (FundamentalGroup.map (X := U₁) (ContinuousMap.subtypeVal (U₁ : Set M₁)) x)))
  exact (congrArg MonoidHom.ker (map_inlContinuousMap_eq φ x)).trans <|
    (MonoidHom.comap_ker _ _).symm.trans <|
    (congrArg (Subgroup.comap _) (vanKampen φ hU x).2).trans <|
    (congrArg (fun s ↦ (Subgroup.normalClosure s).comap _) hrange).trans <|
    (congrArg (Subgroup.comap _) (Subgroup.map_normalClosure _ _ hf.surjective).symm).trans <|
    Subgroup.comap_map_eq_self_of_injective hf.injective _

/-- **Van Kampen for the glued space.** If `M₁` is path connected, `M₂` simply connected and
`U₁` path connected, then for `x ∈ U₁` the map induced by `inl` gives an isomorphism from the
quotient of `π₁(M₁, x)` by the normal closure of the image of `π₁(U₁, x)` onto
`π₁(GluedAlong φ, inl x)`. -/
def fundamentalGroupMulEquiv (hU : IsPathConnected (U₁ : Set M₁)) (x : U₁) :
    FundamentalGroup M₁ x ⧸ Subgroup.normalClosure
        (range (FundamentalGroup.map (X := U₁) (ContinuousMap.subtypeVal (U₁ : Set M₁)) x) :
          Set (FundamentalGroup M₁ x)) ≃*
      FundamentalGroup (GluedAlong φ) (inlContinuousMap φ x) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_map_inl φ hU x).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (map_inl_surjective φ hU x))

/-- The isomorphism `fundamentalGroupMulEquiv` sends the class of `g ∈ π₁(M₁, x)` to its image
under the map induced by `inl`. -/
@[simp]
theorem fundamentalGroupMulEquiv_mk (hU : IsPathConnected (U₁ : Set M₁)) (x : U₁)
    (g : FundamentalGroup M₁ x) :
    fundamentalGroupMulEquiv φ hU x (QuotientGroup.mk g) =
      FundamentalGroup.map (inlContinuousMap φ) (x : M₁) g :=
  (rfl)

/-- The isomorphism `fundamentalGroupMulEquiv` sends the class of a loop `γ` of `M₁` at `x` to
the class of the loop `inl ∘ γ`. -/
theorem fundamentalGroupMulEquiv_mk_fromPath (hU : IsPathConnected (U₁ : Set M₁)) (x : U₁)
    (γ : Path (x : M₁) x) :
    fundamentalGroupMulEquiv φ hU x
        (QuotientGroup.mk (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ))) =
      FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk (γ.map (inlContinuousMap φ).continuous)) := by
  rw [fundamentalGroupMulEquiv_mk]
  exact TauCeti.FundamentalGroup.map_fromPath _ _ γ

end GluedAlong

end SymplecticGeometry

end
