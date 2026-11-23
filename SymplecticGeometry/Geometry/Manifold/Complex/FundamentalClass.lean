/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Complex.Determinant
public import SymplecticGeometry.Geometry.Manifold.Complex.HomologicalOrientation
public import TauCeti.Geometry.Manifold.Complex.FundamentalClass

/-!
# The canonical orientation of `ℂ` under holomorphic and antiholomorphic maps

Complex conjugation reverses Tau Ceti's canonical homological orientation
`TauCeti.complexHomologicalOrientation` of `ℂ`, and of open sets of `ℂ`, since its real derivative
`Complex.conjCLE` has determinant `-1`. The file also gives a form of Tau Ceti's
`TauCeti.comap_complexHomologicalOrientation`, which says that an open local biholomorphism of
Riemann surfaces preserves their canonical orientations, for an open embedding between open sets
of the two surfaces that acts as such a map.

The proof for `ℂ` compares two charts at a point `x`: the chart `OpenPartialHomeomorph.refl` and
conjugation itself, seen as a chart. Tau Ceti's
`OpenPartialHomeomorph.coe_localOrientationOfOrientedChart_eq_sign_det_smul` says that the local
orientations these charts select differ by the sign of `det conjCLE`, that is by `-1`, and
`OpenPartialHomeomorph.localHomologyMap_localOrientationOfOrientedChart` says that conjugation
carries the one selected by the conjugation chart at `x` to the one selected by `refl` at
`conj x`.

The proof follows Tau Ceti's `TauCeti.comap_complexHomologicalOrientation`, the statement for a
holomorphic map, with its sign step taken from
`TauCeti.complexHomologicalOrientation_apply_of_mem_maximalAtlas`; here the determinant is `-1`
where those have a positive one.

## Main results

* `TauCeti.comap_conjCLE_complexHomologicalOrientation`: pulling the canonical orientation of `ℂ`
  back along `conj` gives its negation.
* `TauCeti.comap_conj_complexHomologicalOrientation`: the same for an open embedding `U → V`
  between open sets of `ℂ` that acts as `conj`.
* `TauCeti.comap_complexHomologicalOrientation_of_comp_eq`: an open embedding `U → V` between
  open sets of Riemann surfaces that acts as an open embedding `T` which is a `C^k` local
  biholomorphism preserves their canonical orientations.
* `SymplecticGeometry.complexManifoldHomologicalOrientation_eq_complexHomologicalOrientation`:
  on a Riemann surface, the library's homological orientation of a complex manifold of complex
  dimension `0 + 1` is Tau Ceti's `TauCeti.complexHomologicalOrientation`, so that Tau Ceti's
  results on the latter apply to it.
-/

public section

noncomputable section

open Topology ComplexConjugate Manifold

namespace TauCeti

/-- Complex conjugation reverses the canonical homological orientation of `ℂ`: pulling it back
along `conj` gives its negation. -/
theorem comap_conjCLE_complexHomologicalOrientation :
    (complexHomologicalOrientation ℂ).comap Complex.conjCLE.toHomeomorph.isOpenEmbedding =
      -complexHomologicalOrientation ℂ := by
  ext x : 1
  apply (Complex.conjCLE.toHomeomorph.isOpenEmbedding.localOrientationEquiv x 2).injective
  rw [HomologicalOrientation.localOrientationEquiv_comap_apply, HomologicalOrientation.neg_apply,
    IsOpenEmbedding.localOrientationEquiv_neg, ← neg_eq_iff_eq_neg, eq_comm]
  apply Subtype.ext
  rw [complexHomologicalOrientation_apply, complexHomologicalOrientation_apply,
    IsOpenEmbedding.coe_localOrientationEquiv, localHomologyIsoOfIsOpenEmbedding_hom,
    LocalOrientation.coe_neg]
  simp only [chartAt_self_eq]
  -- Conjugation, as a chart, selects the opposite of the local orientation selected by `refl`.
  have e := (OpenPartialHomeomorph.refl ℂ).coe_localOrientationOfOrientedChart_eq_sign_det_smul
    Complex.orientation Complex.finrank_real_complex
    Complex.conjCLE.toHomeomorph.toOpenPartialHomeomorph (Set.mem_univ x) (Set.mem_univ x)
    (f' := (Complex.conjCLE : ℂ →L[ℝ] ℂ)) (by simpa using Complex.conjCLE.hasFDerivAt)
    (by rw [Complex.det_conjCLE]; norm_num)
  rw [Complex.det_conjCLE, sign_neg (by norm_num : (-1 : ℝ) < 0), SignType.coe_neg_one,
    neg_one_zsmul] at e
  -- Conjugation carries the local orientation of its own chart to that of `refl`.
  have n := Complex.conjCLE.toHomeomorph.toOpenPartialHomeomorph
    |>.localHomologyMap_localOrientationOfOrientedChart Complex.orientation
      Complex.finrank_real_complex ⟨_, Complex.conjCLE.toHomeomorph.continuous⟩
      (OpenPartialHomeomorph.refl ℂ) (Set.mem_univ x) (Set.mem_univ _)
      (Filter.Eventually.of_forall fun _ ↦ rfl) (fun _ h ↦ Complex.conjCLE.injective h)
  rw [← neg_neg ((OpenPartialHomeomorph.refl ℂ).localOrientationOfOrientedChart _ _ _).val, ← e,
    map_neg]
  exact congrArg Neg.neg n

/-- Complex conjugation reverses the canonical homological orientations of open sets of `ℂ`:
pulling the orientation of `V` back along an open embedding `f : U → V` that acts as `conj`
gives the negation of the orientation of `U`. -/
theorem comap_conj_complexHomologicalOrientation {U V : TopologicalSpace.Opens ℂ} {f : U → V}
    (hf : IsOpenEmbedding f) (hfc : ∀ z, (f z : ℂ) = conj (z : ℂ)) :
    (complexHomologicalOrientation V).comap hf = -complexHomologicalOrientation U := by
  have hU : IsOpenEmbedding (Subtype.val : U → ℂ) := U.isOpen.isOpenEmbedding_subtypeVal
  have hV : IsOpenEmbedding (Subtype.val : V → ℂ) := V.isOpen.isOpenEmbedding_subtypeVal
  conv_lhs => rw [← comap_subtypeVal_complexHomologicalOrientation hV]
  rw [HomologicalOrientation.comap_comap_of_comp_eq _ hV hf
      (Complex.conjCLE.toHomeomorph.isOpenEmbedding.comp hU) (funext hfc),
    ← HomologicalOrientation.comap_comap _ Complex.conjCLE.toHomeomorph.isOpenEmbedding hU,
    comap_conjCLE_complexHomologicalOrientation, HomologicalOrientation.comap_neg,
    comap_subtypeVal_complexHomologicalOrientation]

/-- Let `U` and `V` be open sets of Riemann surfaces `M` and `N`, and `f : U → V` an open
embedding that acts as `T : M → N`, an open embedding which is a `C^k` local biholomorphism, for
`k ≠ 0`. Then pulling the canonical orientation of `V` back along `f` gives that of `U`. -/
theorem comap_complexHomologicalOrientation_of_comp_eq
    {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ, ℂ) 1 M]
    {N : Type} [TopologicalSpace N] [T2Space N] [ChartedSpace ℂ N] [IsManifold 𝓘(ℂ, ℂ) 1 N]
    {U : TopologicalSpace.Opens M} {V : TopologicalSpace.Opens N} {f : U → V}
    (hf : IsOpenEmbedding f) {k : WithTop ℕ∞} [NeZero k] {T : M → N} (hT : IsOpenEmbedding T)
    (hT' : IsLocalDiffeomorph 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) k T)
    (h : Subtype.val ∘ f = T ∘ Subtype.val) :
    (complexHomologicalOrientation V).comap hf = complexHomologicalOrientation U := by
  rw [← comap_subtypeVal_complexHomologicalOrientation U.isOpenEmbedding',
    ← comap_subtypeVal_complexHomologicalOrientation V.isOpenEmbedding',
    HomologicalOrientation.comap_comap,
    ← HomologicalOrientation.comap_comap_of_comp_eq _ hT U.isOpenEmbedding'
      (V.isOpenEmbedding'.comp hf) h.symm,
    comap_complexHomologicalOrientation hT hT']

end TauCeti

namespace SymplecticGeometry

open Module TauCeti

/-- On a Riemann surface `M`, a complex manifold modelled on `ℂ`, the homological orientation
`complexManifoldHomologicalOrientation ℂ M hE` of complex dimension `0 + 1` is Tau Ceti's
canonical homological orientation `complexHomologicalOrientation M`. -/
theorem complexManifoldHomologicalOrientation_eq_complexHomologicalOrientation
    {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ, ℂ) 1 M]
    (hE : finrank ℂ ℂ = 0 + 1) :
    complexManifoldHomologicalOrientation ℂ M hE = complexHomologicalOrientation M := by
  rw [complexManifoldHomologicalOrientation_def, complexManifoldOrientationOfFinrank_def,
    complexHomologicalOrientation_def]

end SymplecticGeometry

end
