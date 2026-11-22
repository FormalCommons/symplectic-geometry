/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Chart
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Linear

/-!
# The local orientation of the identity chart, through the sphere

Let `E` be a real inner product space of dimension `n + 1`, oriented by `o`, and `p` a point of
`E`. Tau Ceti's local orientation of `E` at `p` selected by the identity chart and `o`
(`OpenPartialHomeomorph.localOrientationOfOrientedChart`) is a class of `H_{n+1}(E, E ∖ {p})`.
This file computes its image under the connecting morphism of the pair `(E, E ∖ {p})` followed by
radial projection about `p` onto the unit sphere: it is the generator of the reduced homology of
the unit sphere selected by `o` (`TauCeti.reducedSingularHomologySphereIsoOfOrientation`).

It also compares this local orientation with the one that Tau Ceti selects from `o` alone
(`Orientation.localOrientation`), which is defined through the Euclidean model: at the origin the
two agree. A linear isometry `f : F ≃ₗᵢ[ℝ] E` commutes with the connecting morphisms and with
radial projection, so it carries the identity-chart local orientation of `F` to that of `E`; applied
to an isometry from the Euclidean model, where Tau Ceti proves the agreement
(`Orientation.localOrientation_euclideanSpace`), this gives it on `E`. The radial projection step
adapts Tau Ceti's private
`TauCeti.snd_ofSubsetMap_linearIsometryEquiv_comp_complSingletonHomotopyEquivSphere` to the origin,
and the comparison of the identity charts follows the proof of Tau Ceti's
`TauCeti.singularHomologyComplSingletonIsoOfOrientation_transHomeomorph_linearIsometryEquiv`.

## Main results

* `OpenPartialHomeomorph.map_reducedSingularHomologyδ_localOrientationOfOrientedChart_refl`: the
  local orientation of the identity chart, sent through the connecting morphism and radial
  projection, is the oriented generator of the unit sphere.
* `LinearIsometryEquiv.snd_complZeroPairIso_hom_comp_complSingletonHomotopyEquivSphere`: linear
  isometries commute with radial projection about the origin.
* `OpenPartialHomeomorph.localOrientationOfOrientedChart_refl_map_linearIsometryEquiv`: linear
  isometries carry the identity-chart local orientations at the origin to one another.
* `Orientation.localOrientation_eq_localOrientationOfOrientedChart_refl`: on an inner product
  space, the local orientation selected by an orientation is the one of the identity chart.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.3 (local
  orientations and the generators of the homology of spheres).
-/

public section

noncomputable section

open CategoryTheory TauCeti AlgebraicTopology Module

universe w

namespace OpenPartialHomeomorph

variable {E : Type w} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **The local orientation of the identity chart, through the sphere.** The local orientation
of `E` at `p` selected by the identity chart and the orientation `o`, sent through the connecting
morphism of the pair `(E, E ∖ {p})` and radial projection about `p`, is the generator of the
reduced homology of the unit sphere selected by `o`. -/
theorem map_reducedSingularHomologyδ_localOrientationOfOrientedChart_refl {p : E}
    (hp : p ∈ (OpenPartialHomeomorph.refl E).source) {n : ℕ}
    (o : Orientation ℝ E (Fin (n + 1))) (hE : finrank ℝ E = n + 1) :
    (reducedSingularHomologyFunctor (ModuleCat.of ℤ (ULift.{w} ℤ)) n).map
        (TopCat.ofHom (complSingletonHomotopyEquivSphere p).toFun)
      ((TopPair.ofSubset ({p}ᶜ : Set (TopCat.of E))).reducedSingularHomologyδ
        (ModuleCat.of ℤ (ULift.{w} ℤ)) n
        ((OpenPartialHomeomorph.refl E).localOrientationOfOrientedChart hp o hE).val) =
      (reducedSingularHomologySphereIsoOfOrientation (ModuleCat.of ℤ (ULift.{w} ℤ)) o hE).inv
        1 := by
  have h := singularHomologyComplSingletonIsoOfOrientation_refl_hom
    (ModuleCat.of ℤ (ULift.{w} ℤ)) hp o hE
  rw [OpenPartialHomeomorph.coe_localOrientationOfOrientedChart]
  set e := singularHomologyComplSingletonIsoOfOrientation (ModuleCat.of ℤ (ULift.{w} ℤ))
    (OpenPartialHomeomorph.refl E) hp o hE
  set s := reducedSingularHomologySphereIsoOfOrientation (ModuleCat.of ℤ (ULift.{w} ℤ)) o hE
  apply (ConcreteCategory.bijective_of_isIso s.hom).1
  calc s.hom _ = e.hom (e.inv 1) := by
        rw [h, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
        -- The two sides differ only in how the degree of the local homology class is written,
        -- as `n + 1` or as the degree of the pair's homology.
        rfl
    _ = s.hom (s.inv 1) := by rw [Iso.inv_hom_id_apply, Iso.inv_hom_id_apply]


end OpenPartialHomeomorph

namespace LinearIsometryEquiv

variable {E F : Type w} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- A linear isometry equivalence `f` commutes with radial projection about the origin onto the
unit spheres: on the complements of the origin, `f` followed by radial projection is radial
projection followed by the restriction of `f` to the unit spheres. -/
theorem snd_complZeroPairIso_hom_comp_complSingletonHomotopyEquivSphere (f : F ≃ₗᵢ[ℝ] E) :
    TopPair.Hom.snd f.toContinuousLinearEquiv.complZeroPairIso.hom ≫
        TopCat.ofHom (complSingletonHomotopyEquivSphere (0 : E)).toFun =
      TopCat.ofHom (complSingletonHomotopyEquivSphere (0 : F)).toFun ≫
        TopCat.ofHom ⟨f.toLinearIsometry.unitSphereMap,
          f.toLinearIsometry.continuous_unitSphereMap⟩ := by
  rw [ContinuousLinearEquiv.complZeroPairIso_hom]
  ext z
  -- The subspace of `TopPair.ofSubset` is the subtype only after unfolding the pair.
  erw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
  refine (coe_complSingletonHomotopyEquivSphere_apply (0 : E) _).trans ?_
  erw [TopPair.ofSubsetMap_snd_apply]
  simp only [TopCat.hom_ofHom, ContinuousMap.coe_mk, LinearIsometry.coe_unitSphereMap_apply,
    LinearIsometryEquiv.coe_toLinearIsometry, sub_zero]
  erw [coe_complSingletonHomotopyEquivSphere_apply]
  simp

end LinearIsometryEquiv

namespace OpenPartialHomeomorph

variable {E F : Type w} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- A linear isometry equivalence `f : F ≃ₗᵢ[ℝ] E` carries the local orientation of `F` at the
origin selected by the identity chart and an orientation `o` to the one of `E` selected by the
identity chart and the transported orientation `o.map f`. -/
theorem localOrientationOfOrientedChart_refl_map_linearIsometryEquiv (f : F ≃ₗᵢ[ℝ] E)
    (hF0 : (0 : F) ∈ (OpenPartialHomeomorph.refl F).source)
    (hE0 : (0 : E) ∈ (OpenPartialHomeomorph.refl E).source) {n : ℕ}
    (o : Orientation ℝ F (Fin (n + 1))) (hF : finrank ℝ F = n + 1) (hE : finrank ℝ E = n + 1) :
    ((OpenPartialHomeomorph.refl F).localOrientationOfOrientedChart hF0 o hF).map
        f.toContinuousLinearEquiv.complZeroPairIso =
      (OpenPartialHomeomorph.refl E).localOrientationOfOrientedChart hE0
        (o.map _ f.toLinearEquiv) hE := by
  set R := ModuleCat.of ℤ (ULift.{w} ℤ)
  set eE := singularHomologyComplSingletonIsoOfOrientation R (OpenPartialHomeomorph.refl E)
    hE0 (o.map _ f.toLinearEquiv) hE
  set eF := singularHomologyComplSingletonIsoOfOrientation R (OpenPartialHomeomorph.refl F)
    hF0 o hF
  -- Through the connecting morphisms and radial projections, `f` intertwines the oriented local
  -- homology isomorphisms of the two identity charts.
  have key : TopPair.singularHomologyMap f.toContinuousLinearEquiv.complZeroPairIso.hom R (n + 1) ≫
      eE.hom = eF.hom := by
    simp only [eE, eF, singularHomologyComplSingletonIsoOfOrientation_refl_hom]
    rw [← TopPair.reducedSingularHomologyδ_naturality_assoc]
    -- The composite is only type-correct after unfolding the subspace of the pair.
    erw [← Functor.map_comp_assoc,
      f.snd_complZeroPairIso_hom_comp_complSingletonHomotopyEquivSphere, Functor.map_comp_assoc,
      reducedSingularHomologySphereIsoOfOrientation_hom_naturality R o
        (o.map (Fin (n + 1)) f.toLinearEquiv) f rfl hF]
  apply Subtype.ext
  rw [LocalOrientation.coe_map, coe_localOrientationOfOrientedChart,
    coe_localOrientationOfOrientedChart]
  apply (ConcreteCategory.bijective_of_isIso eE.hom).1
  rw [Iso.inv_hom_id_apply, ← ConcreteCategory.comp_apply, key, Iso.inv_hom_id_apply]

end OpenPartialHomeomorph

namespace Orientation

variable {E : Type w} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **The local orientation selected by an orientation is the one of the identity chart.** On a
real inner product space `E` of dimension `n + 1`, the local orientation at the origin selected by
an orientation `ω` (`Orientation.localOrientation`) is the one selected by the identity chart and
`ω`. -/
theorem localOrientation_eq_localOrientationOfOrientedChart_refl {n : ℕ}
    (ω : Orientation ℝ E (Fin (n + 1))) (hE : finrank ℝ E = n + 1)
    (h0 : (0 : E) ∈ (OpenPartialHomeomorph.refl E).source) :
    ω.localOrientation hE =
      (OpenPartialHomeomorph.refl E).localOrientationOfOrientedChart h0 ω hE := by
  have hF := finrank_euclideanSpace_ulift_fin.{w} (n + 1)
  let f : EuclideanSpace ℝ (ULift.{w} (Fin (n + 1))) ≃ₗᵢ[ℝ] E :=
    (EuclideanSpace.basisFun (ULift.{w} (Fin (n + 1))) ℝ).equiv
      (ω.finOrthonormalBasis (Nat.succ_pos n) hE) Equiv.ulift
  set ω' := ω.map _ f.symm.toLinearEquiv
  have hω : ω'.map _ f.toLinearEquiv = ω := by
    rw [← Orientation.map_trans]
    convert DFunLike.congr_fun (Orientation.map_refl (R := ℝ) (M := E) (Fin (n + 1))) ω using 2
    · ext x
      simp
    · rfl
  -- The underlying linear equivalence of `f` as a continuous linear equivalence.
  have hf : f.toContinuousLinearEquiv.toLinearEquiv = f.toLinearEquiv := rfl
  calc ω.localOrientation hE
      = (ω'.map _ f.toContinuousLinearEquiv.toLinearEquiv).localOrientation hE := by rw [hf, hω]
    _ = (ω'.localOrientation hF).map f.toContinuousLinearEquiv.complZeroPairIso :=
        localOrientation_map _ _ hF hE
    _ = (OpenPartialHomeomorph.refl E).localOrientationOfOrientedChart h0
          (ω'.map _ f.toLinearEquiv) hE := by
        rw [localOrientation_euclideanSpace]
        exact OpenPartialHomeomorph.localOrientationOfOrientedChart_refl_map_linearIsometryEquiv
          f _ h0 _ hF hE
    _ = _ := by rw [hω]

end Orientation
