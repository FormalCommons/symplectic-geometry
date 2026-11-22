/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Complex.Determinant
public import TauCeti.Geometry.Manifold.Complex.FundamentalClass

/-!
# Complex conjugation and the canonical orientation of `ℂ`

Complex conjugation reverses Tau Ceti's canonical homological orientation
`TauCeti.complexHomologicalOrientation` of `ℂ`, and of open sets of `ℂ`, since its real derivative
`Complex.conjCLE` has determinant `-1`.

The proof for `ℂ` compares two charts at a point `x`: the chart `OpenPartialHomeomorph.refl` and
conjugation itself, seen as a chart. Tau Ceti's
`OpenPartialHomeomorph.coe_localOrientationOfOrientedChart_eq_sign_det_smul` says that the local
orientations these charts select differ by the sign of `det conjCLE`, that is by `-1`, and
`OpenPartialHomeomorph.localHomologyMap_localOrientationOfOrientedChart` says that conjugation
carries the one selected by the conjugation chart at `x` to the one selected by `refl` at
`conj x`.

## Main results

* `TauCeti.comap_conjCLE_complexHomologicalOrientation`: pulling the canonical orientation of `ℂ`
  back along `conj` gives its negation.
* `TauCeti.comap_conj_complexHomologicalOrientation`: the same for an open embedding `U → V`
  between open sets of `ℂ` that acts as `conj`.
-/

public section

noncomputable section

open Topology ComplexConjugate

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

end TauCeti

end
