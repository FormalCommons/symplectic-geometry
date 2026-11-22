/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Chart
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Linear
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Smooth

/-!
# The local orientation of the identity chart

Let `E` be a real inner product space of dimension `n + 1`, oriented by `o`, and `p` a point of
`E`. Tau Ceti's local orientation of `E` at `p` selected by the identity chart and `o`
(`OpenPartialHomeomorph.localOrientationOfOrientedChart`) is a class of `H_{n+1}(E, E ∖ {p})`.
This file computes its image under the connecting morphism of the pair `(E, E ∖ {p})` followed by
radial projection about `p` onto the unit sphere: it is the generator of the reduced homology of
the unit sphere selected by `o` (`TauCeti.reducedSingularHomologySphereIsoOfOrientation`).

At the origin, the local orientation of the identity chart is the local orientation
`Orientation.localOrientation` that Tau Ceti attaches to `o` through a linear equivalence with the
Euclidean model. Consequently, for a chart `φ` of a space `M` with values in `E`, the map
`x ↦ φ x - φ z` on the source of `φ` carries the local orientation of `M` at `z` selected by `φ`
and `o` to `o.localOrientation`. This is the form in which Tau Ceti's computation of the local
index of a section at a transverse zero
(`TauCeti.VectorBundleOrientation.sectionIndex_eq_sign_det_of_hasFDerivAt`) takes the orientation
of its chart.

## Main results

* `OpenPartialHomeomorph.map_reducedSingularHomologyδ_localOrientationOfOrientedChart_refl`: the
  local orientation of the identity chart, sent through the connecting morphism and radial
  projection, is the oriented generator of the unit sphere.
* `Orientation.localOrientation_eq_localOrientationOfOrientedChart_refl`: at the origin, the local
  orientation of the identity chart is `Orientation.localOrientation`.
* `OpenPartialHomeomorph.localHomologyMap_sub_localOrientationOfOrientedChart`: the chart `φ`,
  translated so that `φ z` is the origin, carries the local orientation that it selects at `z` to
  `Orientation.localOrientation`.

## Implementation notes

The last two proofs follow the pattern of Tau Ceti's
`OpenPartialHomeomorph.localHomologyMap_localOrientationOfOrientedChart`: a map whose expression in
two charts has derivative of determinant one carries the local orientation of the first chart to
that of the second, and an open set is removed through the excision isomorphism.

Tau Ceti's main branch proves both results at commit 55525ca, in
`TauCeti/AlgebraicTopology/Singular/LocalHomology/Orientation/Linear.lean`. The pinned version
of Tau Ceti does not have that commit. There,
`Orientation.localOrientation_eq_localOrientationOfOrientedChart_refl` has the same name and
statement, without the membership hypothesis `h0`. Its proof follows the same steps as ours:
`Orientation.localOrientation_map` along a linear isometry with the Euclidean model,
`Orientation.localOrientation_euclideanSpace`, and then the injectivity of the map induced by
`ContinuousLinearEquiv.complZeroPairIso`. Our middle step uses chart naturality where Tau Ceti
uses `LinearIsometryEquiv.localHomologyMap_localOrientationOfOrientedChart_refl`.
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

/-- **The local orientation of an oriented inner product space at the origin** is the one
selected by the identity chart: Tau Ceti's `Orientation.localOrientation`, defined through a
linear equivalence with the Euclidean model, agrees with
`OpenPartialHomeomorph.localOrientationOfOrientedChart` of the identity chart. -/
theorem _root_.Orientation.localOrientation_eq_localOrientationOfOrientedChart_refl
    {F : Type w} [NormedAddCommGroup F] [InnerProductSpace ℝ F] {n : ℕ}
    (ω : Orientation ℝ F (Fin (n + 1))) (hF : finrank ℝ F = n + 1)
    (h0 : (0 : F) ∈ (OpenPartialHomeomorph.refl F).source) :
    ω.localOrientation hF =
      (OpenPartialHomeomorph.refl F).localOrientationOfOrientedChart h0 ω hF := by
  have := FiniteDimensional.of_finrank_eq_succ hF
  have hM : finrank ℝ (EuclideanSpace ℝ (ULift.{w} (Fin (n + 1)))) = n + 1 :=
    finrank_euclideanSpace_ulift_fin (n + 1)
  -- An oriented isometry `e` of `F` with the Euclidean model, along which both sides are compared
  -- with the identity chart of the model.
  let e : F ≃ₗᵢ[ℝ] EuclideanSpace ℝ (ULift.{w} (Fin (n + 1))) :=
    ((ω.finOrthonormalBasis (Nat.succ_pos n) hF).reindex Equiv.ulift.symm).repr
  have h₁ := Orientation.localOrientation_map e.toContinuousLinearEquiv ω hF hM
  rw [Orientation.localOrientation_euclideanSpace] at h₁
  have h₂ := (OpenPartialHomeomorph.refl F)
    |>.localOrientationOfOrientedChart_transHomeomorph_linearIsometryEquiv
    (mem_univ 0) ω hF e hM
  -- The continuous map underlying `e`, written as `complZeroPairIso_hom` writes it.
  set eC : C(F, EuclideanSpace ℝ (ULift.{w} (Fin (n + 1)))) :=
    ((e.toContinuousLinearEquiv : F →L[ℝ] EuclideanSpace ℝ (ULift.{w} (Fin (n + 1)))) :
      C(F, EuclideanSpace ℝ (ULift.{w} (Fin (n + 1)))))
  -- Naturality of chart orientations along `e`, at the image `e 0` of the origin, which is the
  -- origin only up to `map_zero`.
  have key : ∀ (p : EuclideanSpace ℝ (ULift.{w} (Fin (n + 1))))
      (hp : p ∈ (OpenPartialHomeomorph.refl _).source) (h : eC ⁻¹' {p} ⊆ {0}),
      eC 0 = p →
      localHomologyMap (ModuleCat.of ℤ (ULift.{w} ℤ)) eC h (n + 1)
        (((OpenPartialHomeomorph.refl F).transHomeomorph
          e.toHomeomorph).localOrientationOfOrientedChart (by simp)
          (ω.map (Fin (n + 1)) e.toLinearEquiv) hM).val =
      ((OpenPartialHomeomorph.refl _).localOrientationOfOrientedChart hp
        (ω.map (Fin (n + 1)) e.toLinearEquiv) hM).val := by
    rintro p hp h rfl
    have h₃ := ((OpenPartialHomeomorph.refl F).transHomeomorph
      e.toHomeomorph).localHomologyMap_localOrientationOfOrientedChart
      (ω.map (Fin (n + 1)) e.toLinearEquiv) hM eC (OpenPartialHomeomorph.refl _)
      (a := 0) (by simp) hp (Filter.Eventually.of_forall fun _ ↦ rfl) h
    exact h₃
  have h₄ := key 0 (mem_univ 0) (fun x hx ↦ by simpa [eC] using hx)
    (by simp [eC])
  rw [h₂] at h₄
  apply Subtype.ext
  apply (ConcreteCategory.bijective_of_isIso (TopPair.singularHomologyMap
    e.toContinuousLinearEquiv.complZeroPairIso.hom (ModuleCat.of ℤ (ULift.{w} ℤ)) (n + 1))).1
  rw [← LocalOrientation.coe_map, ← h₁, ContinuousLinearEquiv.complZeroPairIso_hom]
  rw [← localHomologyMap_def]
  exact h₄.symm

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
  rw [← Orientation.localOrientation_eq_localOrientationOfOrientedChart_refl ω hF (mem_univ 0)]
    at h₅
  -- Remove the open set `univ` through its excision isomorphism.
  have h' := (isOpen_univ (X := s)).isOpenEmbedding_subtypeVal
    |>.localHomologyMap_localOrientationEquiv_symm
    ⟨⟨z, hz⟩, mem_univ _⟩ (φ₁.localOrientationOfOrientedChart hz₁ ω hF) fun _ hy ↦ Subtype.ext hy
  rw [h₁, ← h₅, ← h', ← ConcreteCategory.comp_apply]
  exact ConcreteCategory.congr_hom (localHomologyMap_comp _ _ _ _ _ _) _

end OpenPartialHomeomorph
