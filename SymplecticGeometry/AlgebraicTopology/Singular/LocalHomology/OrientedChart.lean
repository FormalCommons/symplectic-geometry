/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.Orientation.Linear
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Chart
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Smooth
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic

/-!
# The local orientation of the identity chart

Let `E` be a real inner product space of dimension `n + 1`, oriented by `o`, and `p` a point of
`E`. Tau Ceti's local orientation of `E` at `p` selected by the identity chart and `o`
(`OpenPartialHomeomorph.localOrientationOfOrientedChart`) is a class of `H_{n+1}(E, E ∖ {p})`.
This file computes its image under the connecting morphism of the pair `(E, E ∖ {p})` followed by
radial projection about `p` onto the unit sphere: it is the generator of the reduced homology of
the unit sphere selected by `o` (`TauCeti.reducedSingularHomologySphereIsoOfOrientation`).

It then centers charts at a point. For a chart `φ` of a space `M` with values in `E`, the map
`x ↦ φ x - φ z` on the source of `φ` carries the local orientation of `M` at `z` selected by `φ`
and `o` to `o.localOrientation`. This is the form in which Tau Ceti's computation of the local
index of a section at a transverse zero
(`TauCeti.VectorBundleOrientation.sectionIndex_eq_sign_det_of_hasFDerivAt`) takes the orientation
of its chart.

Finally it reads the local orientations of an oriented `C¹` manifold `M`, modelled on a real normed
space `E` that need not carry an inner product, in the centered chart at `z` with values in `E`:
there they become the local orientation of `E` at the origin selected by the orientation of the
fibre at `z`, read in the trivialization of the tangent bundle at `z`.

## Main results

* `OpenPartialHomeomorph.map_reducedSingularHomologyδ_localOrientationOfOrientedChart_refl`: the
  local orientation of the identity chart, sent through the connecting morphism and radial
  projection, is the oriented generator of the unit sphere.
* `OpenPartialHomeomorph.localHomologyMap_sub_localOrientationOfOrientedChart`: the chart `φ`,
  translated so that `φ z` is the origin, carries the local orientation that it selects at `z` to
  `Orientation.localOrientation`.
* `Orientation.localHomologyMap_localOrientation`: a continuous linear equivalence `f` carries
  `ω.localOrientation` to `(ω.map f).localOrientation` in local homology at the origin.
* `TauCeti.Manifold.Orientation.localHomologyMap_sub_toHomologicalOrientation`: the centered chart
  of `M` at `z` carries the local orientation of `o.toHomologicalOrientation` at `z` to the local
  orientation of `E` at the origin selected by `o` at `z`.

## Implementation notes

The proof of `OpenPartialHomeomorph.localHomologyMap_sub_localOrientationOfOrientedChart`
follows the pattern of Tau Ceti's
`OpenPartialHomeomorph.localHomologyMap_localOrientationOfOrientedChart`: a map whose expression in
two charts has derivative of determinant one carries the local orientation of the first chart to
that of the second, and an open set is removed through the excision isomorphism. At the origin it
then uses `Orientation.localOrientation_eq_localOrientationOfOrientedChart_refl`, from
`SymplecticGeometry/AlgebraicTopology/Singular/LocalHomology/Orientation/Linear.lean`.

For `TauCeti.Manifold.Orientation.localHomologyMap_sub_toHomologicalOrientation`, the chart is
followed by a linear identification `L` of `E` with a Euclidean space; Tau Ceti's
`TauCeti.localOrientationOfManifoldOrientation_eq_localOrientationOfOrientedChart_transHomeomorph`
reads the local orientation of `M` in that chart, the centered case above applies, and
`Orientation.localHomologyMap_localOrientation` for `L⁻¹` carries the result back to `E`.

Tau Ceti's main branch, at commit 55525ca, which the pinned version of Tau Ceti does not have,
proves a more general result in
`TauCeti/AlgebraicTopology/Singular/LocalHomology/Orientation/Linear.lean`:
`OpenPartialHomeomorph.localHomologyMap_chart_localOrientationOfOrientedChart` adds a linear
equivalence `L` after the centered chart. With `L` the identity it is
`OpenPartialHomeomorph.localHomologyMap_sub_localOrientationOfOrientedChart`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.3 (local
  orientations and the generators of the homology of spheres).
-/

public section

noncomputable section

open CategoryTheory TauCeti AlgebraicTopology Module Set Topology TopologicalSpace

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


/-! ### The identity chart at the origin and translated charts -/

/-- **Centering a chart at a point.** Fix an orientation `ω` of an inner product space `F` of
dimension `n + 1`, a chart `φ : M → F`, and a point `z` of the source of `φ`. Restrict the
local orientation `φ.localOrientationOfOrientedChart hz ω hF` to the open source of `φ`, using
the excision equivalence. On local homology, the map `x ↦ φ x - φ z` from that source to `F`
then sends this restricted class to `ω.localOrientation hF`, a class at `0 ∈ F`. -/
theorem localHomologyMap_sub_localOrientationOfOrientedChart
    {M F : Type w} [TopologicalSpace M] [T1Space M] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {n : ℕ} (φ : OpenPartialHomeomorph M F) {z : M} (hz : z ∈ φ.source)
    (ω : Orientation ℝ F (Fin (n + 1))) (hF : finrank ℝ F = n + 1) :
    localHomologyMap (ModuleCat.of ℤ (ULift.{w} ℤ))
        (⟨fun x : φ.source ↦ φ x - φ z, φ.continuousOn.domRestrict.sub continuous_const⟩ :
          C(φ.source, F)) (S := {⟨z, hz⟩}) (T := {0})
        (by
          rintro x hx
          exact Subtype.ext (φ.injOn x.property hz (sub_eq_zero.1 hx))) (n + 1)
        ((φ.open_source.isOpenEmbedding_subtypeVal.localOrientationEquiv ⟨z, hz⟩
          (n + 1)).symm (φ.localOrientationOfOrientedChart hz ω hF)).val =
      (ω.localOrientation hF).val := by
  have := FiniteDimensional.of_finrank_eq_succ hF
  set R := ModuleCat.of ℤ (ULift.{w} ℤ)
  -- The chart `φ₁` of the source `s` of `φ`, and the translated chart map `g`.
  let s : Opens M := ⟨φ.source, φ.open_source⟩
  have hs : Nonempty s := ⟨⟨z, hz⟩⟩
  set φ₁ := φ.subtypeRestr hs
  set g : C(φ.source, F) :=
    ⟨fun x : φ.source ↦ φ x - φ z, φ.continuousOn.domRestrict.sub continuous_const⟩
  have hg : ∀ x, g x = φ x - φ z := fun _ ↦ rfl
  have hz₁ : (⟨z, hz⟩ : φ.source) ∈ φ₁.source := by simpa [φ₁] using hz
  -- Read in the source of `φ`, the local orientation of `φ` is the one of `φ₁`.
  have h₁ : (φ.open_source.isOpenEmbedding_subtypeVal.localOrientationEquiv ⟨z, hz⟩
      (n + 1)).symm (φ.localOrientationOfOrientedChart hz ω hF) =
      φ₁.localOrientationOfOrientedChart hz₁ ω hF := by
    apply (φ.open_source.isOpenEmbedding_subtypeVal.localOrientationEquiv ⟨z, hz⟩
      (n + 1)).injective
    rw [Equiv.apply_symm_apply]
    apply Subtype.ext
    rw [IsOpenEmbedding.coe_localOrientationEquiv, localHomologyIsoOfIsOpenEmbedding_hom]
    exact (φ₁.localHomologyMap_localOrientationOfOrientedChart ω hF
      ⟨Subtype.val, continuous_subtypeVal⟩ φ hz₁ hz (Filter.Eventually.of_forall fun _ ↦ rfl)
      fun x hx ↦ Subtype.ext hx).symm
  -- In the charts `φ₁` and the identity chart, `g` reads as a translation, of derivative the
  -- identity.
  have hU : ∀ y ∈ (univ : Set φ.source), g y = g ⟨z, hz⟩ → y = ⟨z, hz⟩ := fun y _ hy ↦
    Subtype.ext (φ.injOn y.property hz (sub_left_injective hy))
  have hf : HasFDerivAt ((OpenPartialHomeomorph.refl F) ∘ g ∘ φ₁.symm)
      (ContinuousLinearMap.id ℝ F) (φ₁ ⟨z, hz⟩) := by
    refine ((hasFDerivAt_id _).sub_const (φ z)).congr_of_eventuallyEq ?_
    filter_upwards [φ₁.open_target.mem_nhds (φ₁.map_source hz₁)] with y hy
    have h := φ.subtypeRestr_symm_apply hs hy
    simp only [Function.comp_apply] at h
    simp only [Function.comp_apply, OpenPartialHomeomorph.refl_apply, id_eq]
    rw [hg, h, φ.right_inv hy.1]
  have hdet : (ContinuousLinearMap.id ℝ F).det = 1 := LinearMap.det_id
  have key := φ₁.localHomologyMap_restrict_localOrientationOfOrientedChart ω hF
    (OpenPartialHomeomorph.refl F) g hz₁ (mem_univ _) isOpen_univ (mem_univ _) hU hf
    (hdet ▸ one_ne_zero)
  rw [hdet, sign_one, SignType.coe_one, one_smul] at key
  -- The same statement at the origin, which is `g z` only up to `sub_self`.
  have key' : ∀ (p : F) (hp : p ∈ (OpenPartialHomeomorph.refl F).source)
      (h : (g : C(s, F)).restrict (univ : Set s) ⁻¹' {p} ⊆
        {(⟨⟨z, hz⟩, mem_univ _⟩ : (univ : Set s))}), g ⟨z, hz⟩ = p →
      localHomologyMap R ((g : C(s, F)).restrict (univ : Set s)) h (n + 1)
        (((isOpen_univ (X := s)).isOpenEmbedding_subtypeVal.localOrientationEquiv
          ⟨⟨z, hz⟩, mem_univ _⟩ (n + 1)).symm (φ₁.localOrientationOfOrientedChart hz₁ ω hF)).val =
      ((OpenPartialHomeomorph.refl F).localOrientationOfOrientedChart hp ω hF).val := by
    rintro p hp h rfl
    exact key
  have h₅ := key' 0 (mem_univ 0) (fun y hy ↦ Subtype.ext (hU y.val (mem_univ _)
    (hy.trans (sub_self (φ z)).symm))) (sub_self (φ z))
  rw [← Orientation.localOrientation_eq_localOrientationOfOrientedChart_refl ω hF] at h₅
  -- Remove the open set `univ` through its excision isomorphism.
  have h' := (isOpen_univ (X := s)).isOpenEmbedding_subtypeVal
    |>.localHomologyMap_localOrientationEquiv_symm
    ⟨⟨z, hz⟩, mem_univ _⟩ (φ₁.localOrientationOfOrientedChart hz₁ ω hF) fun _ hy ↦ Subtype.ext hy
  rw [h₁, ← h₅, ← h', ← ConcreteCategory.comp_apply]
  exact ConcreteCategory.congr_hom (localHomologyMap_comp _ _ _ _ _ _) _

end OpenPartialHomeomorph

namespace Orientation

variable {F G : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] {n : ℕ}

/-- A continuous linear equivalence `f : F ≃L[ℝ] G` sends, in local homology at the origin, the
local orientation of `F` selected by `ω` to the local orientation of `G` selected by `ω.map f`. -/
theorem localHomologyMap_localOrientation (f : F ≃L[ℝ] G) (ω : Orientation ℝ F (Fin (n + 1)))
    (hF : finrank ℝ F = n + 1) (hG : finrank ℝ G = n + 1)
    (h : ((f : F →L[ℝ] G) : C(F, G)) ⁻¹' {0} ⊆ {0}) :
    localHomologyMap (ModuleCat.of ℤ (ULift.{w} ℤ)) ((f : F →L[ℝ] G) : C(F, G)) h (n + 1)
        (ω.localOrientation hF).val =
      ((ω.map _ f.toLinearEquiv).localOrientation hG).val := by
  rw [Orientation.localOrientation_map f ω hF hG, LocalOrientation.coe_map,
    ContinuousLinearEquiv.complZeroPairIso_hom, localHomologyMap_def]

end Orientation

namespace TauCeti.Manifold.Orientation

open Bundle

variable {E H : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [ChartedSpace E M]
  [IsManifold I 1 M] {m : ℕ} (hE : finrank ℝ E = m + 1)
  (o : Manifold.Orientation I M (Fin (m + 1)))

/-- In the chart `φ` of `M` at `z` with values in the model `E`, the map `x ↦ φ x - φ z` carries
the local orientation of `M` at `z` given by `o` to the local orientation of `E` at the origin
given by `o` at `z`, read in the trivialization of the tangent bundle at `z`. -/
theorem localHomologyMap_sub_toHomologicalOrientation (z : M) :
    localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ))
        (⟨fun x : ((chartAt H z).transHomeomorph I.toHomeomorph).source ↦
            (chartAt H z).transHomeomorph I.toHomeomorph x -
              (chartAt H z).transHomeomorph I.toHomeomorph z,
          ((chartAt H z).transHomeomorph I.toHomeomorph).continuousOn.domRestrict.sub
            continuous_const⟩ :
          C(((chartAt H z).transHomeomorph I.toHomeomorph).source, E))
        (S := {⟨z, by simp⟩}) (T := {0})
        (by
          rintro x hx
          exact Subtype.ext (((chartAt H z).transHomeomorph I.toHomeomorph).injOn x.property
            (by simp) (sub_eq_zero.1 hx))) (m + 1)
        ((((chartAt H z).transHomeomorph I.toHomeomorph).open_source.isOpenEmbedding_subtypeVal
          |>.localOrientationEquiv ⟨z, by simp⟩ (m + 1)).symm
          (o.toHomologicalOrientation hE z)).val =
      (((trivializationAt E (TangentSpace I) z).mapOrientation (Fin (m + 1))
        (FiberBundle.mem_baseSet_trivializationAt' z)
        (o.toVectorBundleOrientation z)).localOrientation hE).val := by
  set φ : OpenPartialHomeomorph M E := (chartAt H z).transHomeomorph I.toHomeomorph
  set ν := (trivializationAt E (TangentSpace I) z).mapOrientation (Fin (m + 1))
    (FiberBundle.mem_baseSet_trivializationAt' z) (o.toVectorBundleOrientation z)
  -- A linear identification `L` of `E` with a Euclidean space, and the chart `φ'` it gives.
  have hF : finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) = m + 1 := finrank_euclideanSpace_fin
  let L : E ≃L[ℝ] EuclideanSpace ℝ (Fin (m + 1)) :=
    ContinuousLinearEquiv.ofFinrankEq (hE.trans hF.symm)
  set φ' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (m + 1))) :=
    (chartAt H z).transHomeomorph (I.toHomeomorph.trans L.toHomeomorph)
  have hz' : z ∈ φ'.source := by simp [φ']
  -- The trivialization at `z` is the identity on the fibre at `z`.
  have hν : o.orientationAt z = ν := by
    simp only [ν, Trivialization.mapOrientation_apply, toVectorBundleOrientation_apply]
    have hid : (trivializationAt E (TangentSpace I) z).linearEquivAt ℝ z
        (FiberBundle.mem_baseSet_trivializationAt' z) = LinearEquiv.refl ℝ E :=
      LinearEquiv.ext fun v ↦ by
        rw [Trivialization.linearEquivAt_apply, ← Trivialization.continuousLinearMapAt_apply_of_mem
          ℝ _ (FiberBundle.mem_baseSet_trivializationAt' z)]
        exact continuousLinearMapAt_trivializationAt_self z v
    rw [hid]
    exact (congrFun (congrArg DFunLike.coe (Orientation.map_refl (Fin (m + 1)))) _).symm
  have h₁ : o.toHomologicalOrientation hE z =
      φ'.localOrientationOfOrientedChart hz' (ν.map (Fin (m + 1)) L.toLinearEquiv) hF := by
    rw [toHomologicalOrientation_apply]
    exact localOrientationOfManifoldOrientation_eq_localOrientationOfOrientedChart_transHomeomorph
      o hE z hν L hF
  have h₂ := φ'.localHomologyMap_sub_localOrientationOfOrientedChart hz'
    (ν.map (Fin (m + 1)) L.toLinearEquiv) hF
  rw [← h₁] at h₂
  -- Carry `h₂` back to `E` by `L⁻¹`.
  have h₄ := Orientation.localHomologyMap_localOrientation L.symm
    (ν.map (Fin (m + 1)) L.toLinearEquiv) hF hE (fun y hy ↦ by simpa using hy)
  rw [show (ν.map (Fin (m + 1)) L.toLinearEquiv).map (Fin (m + 1)) L.symm.toLinearEquiv = ν from
    Orientation.map_symm_map L.toLinearEquiv ν] at h₄
  rw [← h₄, ← h₂, ← ConcreteCategory.comp_apply]
  refine Eq.trans ?_ (ConcreteCategory.congr_hom (localHomologyMap_comp _ _ _ _ _ _) _).symm
  congr 3
  ext x
  -- Unfold the composite of the continuous maps to its values.
  change φ x - φ z = L.symm (L (φ x) - L (φ z))
  rw [← map_sub, ContinuousLinearEquiv.symm_apply_apply]

end TauCeti.Manifold.Orientation
