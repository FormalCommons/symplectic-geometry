/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Basic
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.ZeroDim.Basic
public import TauCeti.Topology.Category.TopPair.ContinuousLinearEquiv
public import Mathlib.LinearAlgebra.Orientation
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.OpenEmbedding
public import SymplecticGeometry.Topology.OpenPartialHomeomorph.SourceRestrict
import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.OpenEmbedding
import SymplecticGeometry.Topology.Category.TopPair
import SymplecticGeometry.LinearAlgebra.Orientation.Basic
import TauCeti.AlgebraicTopology.Singular.ReducedRelative

/-!
# Zero-dimensional local orientations under isomorphisms of pairs

At a point `x` with a zero-dimensional chart, Tau Ceti's
`TauCeti.localOrientationOfZeroDimChart` is the class of `x` in `H₀(M, M ∖ {x}; ℤ)`. An
isomorphism of pairs `(M, M ∖ {x}) ≅ (N, N ∖ {y})` always sends `x` to `y`
(`TopPair.iso_ofSubset_compl_singleton_hom_fst_apply`), so it carries the class of `x`
to the class of `y`. Hence it carries this local orientation at `x` to the one at `y`,
whichever zero-dimensional charts select them (`TauCeti.localOrientationOfZeroDimChart_map`).
This is the rank-zero counterpart of Tau Ceti's `Orientation.localOrientation_map`, where in
positive rank the local orientation is selected by an orientation of the model space. For
instance, through `h.complZeroPairIso`, a continuous linear equivalence `h : P ≃L[ℝ] P'` of
zero-dimensional spaces carries the local orientation of the identity chart of `P` at the
origin to that of `P'`.

An orientation `ω` of a zero-dimensional real normed space `P` is either the positive orientation
of the empty index type or its negative. It selects the local orientation
`Orientation.localOrientationOfZeroDim ω hP` of `P` at the origin: the class of the origin when
`ω` is positive, and its negative otherwise. This is the rank-zero counterpart of Tau Ceti's
`Orientation.localOrientation`, and, like it, it is natural under continuous linear equivalences
(`Orientation.localOrientationOfZeroDim_map`) and reverses with `ω`
(`Orientation.localOrientationOfZeroDim_neg`).

Tau Ceti's `TauCeti.Manifold.Orientation.localOrientationOfZeroDim` selects a local orientation
at each point of a zero-dimensional manifold from a smooth orientation `o`. It reads the class in
the chart `chartAt` and the sign from the tangent orientation, so it is not the local orientation
selected here by `o.orientationAt x` by definition. Still, any isomorphism of pairs
`(M, M ∖ {x}) ≅ (E, E ∖ {0})` carries the one to the other
(`TauCeti.Manifold.Orientation.localOrientationOfZeroDim_map`). In particular, on the model space
`P` with the constant orientation `Manifold.Orientation.model ω`, it selects at the origin the
same class as `ω` does here (`TauCeti.Manifold.Orientation.localOrientationOfZeroDim_model`).
In the same way, a chart `c : M → E` with `c x = 0`, read on its source through
`TauCeti.localHomologyIsoOfIsOpenEmbedding`, carries the homological orientation
`o.toHomologicalOrientationOfZeroDim` at `x` to the one selected by `o.orientationAt x`
(`TauCeti.Manifold.Orientation.localHomologyMap_sourceRestrict_toHomologicalOrientationOfZeroDim`).

## Main definitions

* `Orientation.localOrientationOfZeroDim`: the local orientation at the origin selected by an
  orientation of a zero-dimensional space.

## Main results

* `TauCeti.localOrientationOfZeroDimChart_map`: the point-class local orientation of a
  zero-dimensional chart is natural under isomorphisms of pairs.
* `Orientation.localOrientationOfZeroDim_map`: the local orientation selected by an orientation
  of a zero-dimensional space is natural under continuous linear equivalences.
* `TauCeti.Manifold.Orientation.localOrientationOfZeroDim_map`: an isomorphism of pairs
  `(M, M ∖ {x}) ≅ (E, E ∖ {0})` carries the local orientation of a zero-dimensional oriented
  manifold at `x` to the one selected by its tangent orientation at `x`.
* `TauCeti.Manifold.Orientation.localOrientationOfZeroDim_model`: the manifold local orientation
  of the constant orientation of the model space, at the origin, is the linear one.
* `TauCeti.Manifold.Orientation.localHomologyMap_sourceRestrict_toHomologicalOrientationOfZeroDim`:
  a chart of a zero-dimensional oriented manifold at `x`, centred at `x`, carries its local
  orientation at `x` to the one selected by the tangent orientation at `x`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3.
-/

public section

open CategoryTheory Module

universe w

namespace TauCeti

/-- Let `x ∈ M` and `y ∈ N` have zero-dimensional charts `φ` and `ψ`. An isomorphism of pairs
`e : (M, M ∖ {x}) ≅ (N, N ∖ {y})` carries the local orientation of `φ` at `x`, the class of
`x`, to the local orientation of `ψ` at `y`. -/
theorem localOrientationOfZeroDimChart_map {M N E F : Type w} [TopologicalSpace M] [T2Space M]
    [TopologicalSpace N] [T2Space N]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (φ : OpenPartialHomeomorph M E) (ψ : OpenPartialHomeomorph N F) {x : M} {y : N}
    (hx : x ∈ φ.source) (hy : y ∈ ψ.source) (hE : finrank ℝ E = 0) (hF : finrank ℝ F = 0)
    (e : TopPair.ofSubset ({x}ᶜ : Set (TopCat.of M)) ≅
      TopPair.ofSubset ({y}ᶜ : Set (TopCat.of N))) :
    (localOrientationOfZeroDimChart φ hx hE).map e = localOrientationOfZeroDimChart ψ hy hF := by
  refine Subtype.ext ?_
  rw [LocalOrientation.coe_map, localOrientationOfZeroDimChart_coe,
    localOrientationOfZeroDimChart_coe, localHomologyPointClass_def, localHomologyPointClass_def]
  exact ConcreteCategory.congr_hom (TopPair.singularHomology₀Section_singularHomologyMap _
    (ModuleCat.of ℤ (ULift.{w} ℤ)) e.hom x y
    (TopPair.iso_ofSubset_compl_singleton_hom_fst_apply e)) 1

end TauCeti

namespace Orientation

open TauCeti

variable {P Q : Type w} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q]

open Classical in
/-- **The local orientation selected by an orientation of a zero-dimensional space.** An
orientation `ω` of a real normed space `P` of dimension zero selects the local orientation of `P`
at the origin given by the class of the origin (the local orientation of the identity chart),
when `ω` is the positive orientation of the empty index type, and its negative otherwise. -/
noncomputable def localOrientationOfZeroDim (ω : Orientation ℝ P (Fin 0)) (hP : finrank ℝ P = 0) :
    LocalOrientation P 0 0 :=
  if ω = positiveOrientation then
    localOrientationOfZeroDimChart (OpenPartialHomeomorph.refl P)
      (OpenPartialHomeomorph.mem_refl_source _) hP
  else -localOrientationOfZeroDimChart (OpenPartialHomeomorph.refl P)
      (OpenPartialHomeomorph.mem_refl_source _) hP

open Classical in
theorem localOrientationOfZeroDim_def (ω : Orientation ℝ P (Fin 0)) (hP : finrank ℝ P = 0) :
    ω.localOrientationOfZeroDim hP =
      if ω = positiveOrientation then
        localOrientationOfZeroDimChart (OpenPartialHomeomorph.refl P)
          (OpenPartialHomeomorph.mem_refl_source _) hP
      else -localOrientationOfZeroDimChart (OpenPartialHomeomorph.refl P)
          (OpenPartialHomeomorph.mem_refl_source _) hP :=
  (rfl)

/-- The positive orientation of a zero-dimensional space selects the class of the origin. -/
@[simp]
theorem localOrientationOfZeroDim_positiveOrientation (hP : finrank ℝ P = 0) :
    (positiveOrientation : Orientation ℝ P (Fin 0)).localOrientationOfZeroDim hP =
      localOrientationOfZeroDimChart (OpenPartialHomeomorph.refl P)
        (OpenPartialHomeomorph.mem_refl_source _) hP := by
  rw [localOrientationOfZeroDim_def, ite_eq_left rfl]

/-- Reversing an orientation of a zero-dimensional space reverses the local orientation it
selects. -/
@[simp]
theorem localOrientationOfZeroDim_neg (ω : Orientation ℝ P (Fin 0)) (hP : finrank ℝ P = 0) :
    (-ω).localOrientationOfZeroDim hP = -ω.localOrientationOfZeroDim hP := by
  rcases eq_or_eq_neg_of_isEmpty ω with rfl | rfl
  · rw [localOrientationOfZeroDim_def, ite_eq_right (Module.Ray.ne_neg_self _).symm,
      localOrientationOfZeroDim_positiveOrientation]
  · rw [neg_neg (G := Orientation ℝ P (Fin 0)), localOrientationOfZeroDim_def (-_),
      ite_eq_right (Module.Ray.ne_neg_self _).symm, localOrientationOfZeroDim_positiveOrientation,
      neg_neg]

open Classical in
/-- The local orientation selected by `ω` is the class of the origin of `P`, with the sign `+`
when `ω` is the positive orientation and `-` otherwise. -/
theorem coe_localOrientationOfZeroDim (ω : Orientation ℝ P (Fin 0)) (hP : finrank ℝ P = 0) :
    (ω.localOrientationOfZeroDim hP).val =
      if ω = positiveOrientation then
        localHomologyPointClass (ModuleCat.of ℤ (ULift.{w} ℤ)) {(0 : P)} 0 1
      else -localHomologyPointClass (ModuleCat.of ℤ (ULift.{w} ℤ)) {(0 : P)} 0 1 := by
  rw [localOrientationOfZeroDim_def]
  split_ifs <;> simp

/-- **Naturality of the selected local orientations in dimension zero.** A continuous linear
equivalence `f : P ≃L[ℝ] Q` of zero-dimensional spaces carries the local orientation selected by
`ω` to the local orientation selected by the transported orientation `ω.map f`. -/
theorem localOrientationOfZeroDim_map (f : P ≃L[ℝ] Q) (ω : Orientation ℝ P (Fin 0))
    (hP : finrank ℝ P = 0) (hQ : finrank ℝ Q = 0) :
    (ω.map _ f.toLinearEquiv).localOrientationOfZeroDim hQ =
      (ω.localOrientationOfZeroDim hP).map f.complZeroPairIso := by
  have hpt := localOrientationOfZeroDimChart_map (OpenPartialHomeomorph.refl P)
    (OpenPartialHomeomorph.refl Q) (OpenPartialHomeomorph.mem_refl_source _)
    (OpenPartialHomeomorph.mem_refl_source _) hP hQ f.complZeroPairIso
  rw [localOrientationOfZeroDim_def, localOrientationOfZeroDim_def,
    map_eq_positiveOrientation_iff]
  split_ifs
  · exact hpt.symm
  · rw [LocalOrientation.map_neg, hpt]

end Orientation

namespace TauCeti.Manifold.Orientation

open scoped _root_.Manifold

section Chart

variable {M E : Type w} {H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I 1 M] [ChartedSpace E M]

/-- Let `o` be an orientation of a zero-dimensional manifold `M` modelled on `E`, and `x ∈ M`.
An isomorphism of pairs `e : (M, M ∖ {x}) ≅ (E, E ∖ {0})` carries the local orientation that `o`
selects at `x` to the local orientation of `E` at the origin selected by the tangent orientation
`o.orientationAt x`, an orientation of `E`. -/
theorem localOrientationOfZeroDim_map (o : Manifold.Orientation I M (Fin 0)) (x : M)
    (e : TopPair.ofSubset ({x}ᶜ : Set (TopCat.of M)) ≅
      TopPair.ofSubset ({0}ᶜ : Set (TopCat.of E))) :
    (o.localOrientationOfZeroDim x).map e =
      _root_.Orientation.localOrientationOfZeroDim (P := E) (o.orientationAt x)
        o.finrank_eq_zero := by
  have hpt := localOrientationOfZeroDimChart_map (chartAt E x) (OpenPartialHomeomorph.refl E)
    (mem_chart_source E x) (OpenPartialHomeomorph.mem_refl_source _) o.finrank_eq_zero
    o.finrank_eq_zero e
  rw [localOrientationOfZeroDim_eq_ite o (chartAt E x) (mem_chart_source E x) o.finrank_eq_zero,
    apply_ite (LocalOrientation.map · e), LocalOrientation.map_neg, hpt]
  -- The condition on the left compares orientations of `TangentSpace I x`, which is `E` by
  -- definition, so the definition of the right side matches it only up to that unfolding.
  exact (_root_.Orientation.localOrientationOfZeroDim_def (P := E) _ _).symm

/-- Let `o` be an orientation of a zero-dimensional manifold `M` modelled on `E`, and `c` a chart
of `M` with values in `E` sending `x` to the origin. The local orientation of `M` at `x` given by
`o`, as a homological orientation, carried back to the source of `c` and then forward by `c`, is
the local orientation of `E` at the origin selected by the tangent orientation `o.orientationAt x`:
the class of the origin, negated when `o.orientationAt x` is not the positive orientation. -/
theorem localHomologyMap_sourceRestrict_toHomologicalOrientationOfZeroDim
    (o : Manifold.Orientation I M (Fin 0)) (c : OpenPartialHomeomorph M E) {x : M}
    (hx : x ∈ c.source) (hcx : c x = 0) :
    localHomologyMap (ModuleCat.of ℤ (ULift.{w} ℤ)) c.sourceRestrict
        (hcx ▸ (c.sourceRestrict_preimage_singleton hx).subset) 0
        ((localHomologyIsoOfIsOpenEmbedding (ModuleCat.of ℤ (ULift.{w} ℤ))
          c.open_source.isOpenEmbedding_subtypeVal ⟨x, hx⟩ 0).inv
          (o.toHomologicalOrientationOfZeroDim x).val) =
      (_root_.Orientation.localOrientationOfZeroDim (P := E) (o.orientationAt x)
        o.finrank_eq_zero).val := by
  -- The inverse identification carries the class of `x` to the class of `x` in the source.
  have hinv : (localHomologyIsoOfIsOpenEmbedding (ModuleCat.of ℤ (ULift.{w} ℤ))
      c.open_source.isOpenEmbedding_subtypeVal ⟨x, hx⟩ 0).inv
        (localHomologyPointClass (ModuleCat.of ℤ (ULift.{w} ℤ)) {x} x 1) =
      localHomologyPointClass (ModuleCat.of ℤ (ULift.{w} ℤ)) ({⟨x, hx⟩} : Set c.source)
        ⟨x, hx⟩ 1 := by
    have h := ConcreteCategory.congr_hom ((Iso.eq_comp_inv _).2
      (localHomologyPointClass_comp_localHomologyIsoOfIsOpenEmbedding_hom
        (ModuleCat.of ℤ (ULift.{w} ℤ)) c.open_source.isOpenEmbedding_subtypeVal ⟨x, hx⟩)) 1
    rw [ConcreteCategory.comp_apply] at h
    exact h.symm
  -- The chart carries it to the class of the origin.
  have hpt : localHomologyMap (ModuleCat.of ℤ (ULift.{w} ℤ)) c.sourceRestrict
      (hcx ▸ (c.sourceRestrict_preimage_singleton hx).subset) 0
        (localHomologyPointClass (ModuleCat.of ℤ (ULift.{w} ℤ)) ({⟨x, hx⟩} : Set c.source)
        ⟨x, hx⟩ 1) =
      localHomologyPointClass (ModuleCat.of ℤ (ULift.{w} ℤ)) {(0 : E)} 0 1 := by
    rw [localHomologyPointClass_map_apply, OpenPartialHomeomorph.sourceRestrict_apply, hcx]
  refine Eq.trans ?_ (_root_.Orientation.coe_localOrientationOfZeroDim (P := E) (o.orientationAt x)
    o.finrank_eq_zero).symm
  rw [toHomologicalOrientationOfZeroDim_apply, localOrientationOfZeroDim_coe,
    apply_ite (DFunLike.coe _), apply_ite (DFunLike.coe _), map_neg, map_neg, hinv, hpt]
  -- The two conditions compare orientations of `TangentSpace I x` and of `E`, which is the same
  -- type only by definition, so they agree only up to unfolding it.
  rfl

end Chart

variable {P : Type w} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

/-- On a zero-dimensional real normed space `P`, seen as a manifold modelled on itself, the
local orientation at the origin selected by the constant orientation `model ω` is the local
orientation selected by `ω`. -/
@[simp]
theorem localOrientationOfZeroDim_model (ω : _root_.Orientation ℝ P (Fin 0))
    (hι : Fintype.card (Fin 0) = finrank ℝ P) :
    (model (I := 𝓘(ℝ, P)) ω hι).localOrientationOfZeroDim (0 : P) =
      ω.localOrientationOfZeroDim (hι.symm.trans (Fintype.card_fin 0)) := by
  rw [← LocalOrientation.map_refl ((model (I := 𝓘(ℝ, P)) ω hι).localOrientationOfZeroDim 0),
    localOrientationOfZeroDim_map, orientationAt_model]

end TauCeti.Manifold.Orientation

end
