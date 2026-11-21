/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import SymplecticGeometry.LinearAlgebra.Symplectic.Lagrangian.Action
public import SymplecticGeometry.Topology.Grassmannian.Lagrangian.Basic
public import TauCeti.Topology.Algebra.GroupAction.Transitive
public import TauCeti.Topology.Algebra.UnitaryGroup
public import TauCeti.Topology.Homeomorph.Quotient

/-!
# The Lagrangian Grassmannian as the homogeneous space `U(n)/O(n)`

Write `ℒ ι` for the space of Lagrangian subspaces of the standard model `(StdSpace ι, ω₀)`, with
the topology of orthogonal projections, and `unitaryFrame U = U • {y = 0}` for the Lagrangian
framed by a unitary matrix `U`. This file shows that the topology of `ℒ ι` is the quotient topology
of `unitaryFrame`, and that the symplectic and unitary groups act continuously.

## Main definitions and results

* `SymplecticGeometry.LagrangianGrassmannian.starProjection_unitaryFrame`: the projection onto
  `unitaryFrame U` is `R P₀ Rᵀ`, for `R` the realification of `U` and `P₀` the projection onto
  `{y = 0}`; hence `continuous_unitaryFrame`.
* `ℒ ι` is compact (a `CompactSpace` instance).
* `SymplecticGeometry.LagrangianGrassmannian.quotientHomeomorph`: the homeomorphism
  `U(n) ⧸ O(n) ≃ₜ ℒ ι` induced by `unitaryFrame`, built from Tau Ceti's
  `TauCeti.quotientStabilizerHomeomorph` and the stabilizer `stabilizer_horizontal`.
* `SymplecticGeometry.LagrangianGrassmannian.isOpenQuotientMap_unitaryFrame` and
  `isQuotientMap_unitaryFrame`: `unitaryFrame` is an open quotient map.
* `ContinuousSMul` instances for `GLSymplectic ι ℝ` and `unitaryGroup ι ℂ` acting on `ℒ ι`.

The construction of the homeomorphism follows Tau Ceti's
`TauCeti.quaternionUnitarySphereQuotientHomeomorph`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.3.
-/

public section

namespace SymplecticGeometry

open Matrix TauCeti StdSpace

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local notation "ℒ" ι => LagrangianGrassmannian (stdForm ι)

namespace LagrangianGrassmannian

/-- The orthogonal projection onto the Lagrangian framed by `U` is `R P₀ Rᵀ`, where `R` is the
realification of `U` and `P₀` the projection onto the horizontal Lagrangian. -/
theorem starProjection_unitaryFrame (U : unitaryGroup ι ℂ) :
    (unitaryFrame U : Submodule ℝ (StdSpace ι)).starProjection =
      toEuclideanCLM (n := ι ⊕ ι) (𝕜 := ℝ) (U : Matrix ι ι ℂ).realify *
        (horizontal ι : Submodule ℝ (StdSpace ι)).starProjection *
          toEuclideanCLM (n := ι ⊕ ι) (𝕜 := ℝ) (star (U : Matrix ι ι ℂ).realify) := by
  have hR : (U : Matrix ι ι ℂ).realify ∈ unitary (Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) :=
    realify_mem_orthogonalGroup_iff.2 U.property
  set u : unitary (StdSpace ι →L[ℝ] StdSpace ι) :=
    ⟨toEuclideanCLM (n := ι ⊕ ι) (𝕜 := ℝ) (U : Matrix ι ι ℂ).realify, Unitary.map_mem _ hR⟩
  have hu : (Unitary.linearIsometryEquiv u).toLinearEquiv.toLinearMap =
      toEuclideanLin (U : Matrix ι ι ℂ).realify := rfl
  ext1 v
  rw [unitaryFrame_def, coe_unitary_smul, ← hu, Submodule.starProjection_map_apply]
  rw [map_star]
  rfl

/-- The Lagrangian framed by a unitary matrix depends continuously on it. -/
theorem continuous_unitaryFrame : Continuous (unitaryFrame : unitaryGroup ι ℂ → ℒ ι) := by
  have hR : Continuous fun U : unitaryGroup ι ℂ ↦ (U : Matrix ι ι ℂ).realify := by
    simp_rw [← GLSymplectic.coe_ofUnitary]
    exact Units.continuous_val.comp (continuous_subtypeVal.comp GLSymplectic.continuous_ofUnitary)
  have hE : Continuous (toEuclideanCLM (n := ι ⊕ ι) (𝕜 := ℝ)) :=
    LinearMap.continuous_of_finiteDimensional
      (toEuclideanCLM (n := ι ⊕ ι) (𝕜 := ℝ)).toAlgEquiv.toLinearEquiv.toLinearMap
  rw [continuous_iff_continuous_starProjection]
  simp_rw [starProjection_unitaryFrame]
  exact ((hE.comp hR).mul continuous_const).mul (hE.comp (continuous_star.comp hR))

/-- The Lagrangian Grassmannian is compact, as the image of the compact group `U(n)`. -/
instance {κ : Type*} [Fintype κ] : CompactSpace (ℒ κ) := by
  classical
  exact unitaryFrame_surjective.compactSpace continuous_unitaryFrame

variable (ι) in
/-- **The Lagrangian Grassmannian is `U(n)/O(n)`.** The unitary frame map `U ↦ U • {y = 0}`
induces a homeomorphism from the quotient of `U(n)` by the real orthogonal subgroup `O(n)` onto
the space of Lagrangian subspaces of `StdSpace ι`. -/
noncomputable def quotientHomeomorph :
    unitaryGroup ι ℂ ⧸ UnitaryGroup.realSubgroup ι ≃ₜ ℒ ι :=
  (Homeomorph.Quotient.congrRight fun _ _ ↦ by rw [stabilizer_horizontal]).trans
    (quotientStabilizerHomeomorph _ (horizontal ι)
      (continuous_unitaryFrame.congr unitaryFrame_def))

@[simp]
theorem quotientHomeomorph_mk (U : unitaryGroup ι ℂ) :
    quotientHomeomorph ι (QuotientGroup.mk U) = unitaryFrame U := by
  rw [quotientHomeomorph, Homeomorph.trans_apply, Homeomorph.Quotient.congrRight_mk,
    quotientStabilizerHomeomorph_mk, unitaryFrame_def]

/-- The unitary frame map is an open quotient map: it is the quotient map `U(n) → U(n)/O(n)`
followed by `quotientHomeomorph`. -/
theorem isOpenQuotientMap_unitaryFrame :
    IsOpenQuotientMap (unitaryFrame : unitaryGroup ι ℂ → ℒ ι) := by
  have h : (quotientHomeomorph ι ∘ QuotientGroup.mk : unitaryGroup ι ℂ → ℒ ι) = unitaryFrame :=
    funext quotientHomeomorph_mk
  exact h ▸ (quotientHomeomorph ι).isOpenQuotientMap.comp QuotientGroup.isOpenQuotientMap_mk

/-- The unitary frame map is a quotient map: a map out of `ℒ ι` is continuous as soon as its
composite with `unitaryFrame` is. -/
theorem isQuotientMap_unitaryFrame :
    Topology.IsQuotientMap (unitaryFrame : unitaryGroup ι ℂ → ℒ ι) :=
  isOpenQuotientMap_unitaryFrame.isQuotientMap

/-! ### Continuity of the actions -/

/-- The real `2n × n` frame `g · fromRows (Re U) (Im U)`; its columns span `g • unitaryFrame U`. -/
private noncomputable def smulFrame (g : GLSymplectic ι ℝ) (U : unitaryGroup ι ℂ) :
    Matrix (ι ⊕ ι) ι ℝ :=
  ((g : GL (ι ⊕ ι) ℝ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) *
    fromRows ((U : Matrix ι ι ℂ).map Complex.re) ((U : Matrix ι ι ℂ).map Complex.im)

private theorem coe_smul_unitaryFrame (g : GLSymplectic ι ℝ) (U : unitaryGroup ι ℂ) :
    ((g • unitaryFrame U : ℒ ι) : Submodule ℝ (StdSpace ι)) =
      LinearMap.range
        (toEuclideanLin (fromRows (smulFrame g U).toRows₁ (smulFrame g U).toRows₂)) := by
  rw [fromRows_toRows, coe_smul, coe_unitaryFrame, ← LinearMap.range_comp, smulFrame,
    toLpLin_mul_same]

private theorem isLagrangian_smulFrame (g : GLSymplectic ι ℝ) (U : unitaryGroup ι ℂ) :
    (stdForm ι).IsLagrangian (LinearMap.range
      (toEuclideanLin (fromRows (smulFrame g U).toRows₁ (smulFrame g U).toRows₂))) :=
  coe_smul_unitaryFrame g U ▸ (g • unitaryFrame U).isLagrangian

/-- The complex frame `X + i Y` of `smulFrame g U = fromRows X Y`, as an invertible matrix. -/
private noncomputable def smulFrameGL (g : GLSymplectic ι ℝ) (U : unitaryGroup ι ℂ) : GL ι ℂ :=
  GeneralLinearGroup.mkOfDetNeZero _
    (det_ne_zero_of_isLagrangian_range_fromRows (isLagrangian_smulFrame g U))

/-- A unitary frame of `g • unitaryFrame U`, the orthonormalization of `smulFrameGL g U`. -/
private noncomputable def smulUnitary (g : GLSymplectic ι ℝ) (U : unitaryGroup ι ℂ) :
    unitaryGroup ι ℂ :=
  ⟨GeneralLinearGroup.realOrthonormalize (smulFrameGL g U),
    GeneralLinearGroup.realOrthonormalize_mem_unitaryGroup
      (map_im_conjTranspose_mul_self_eq_zero_of_transpose_mul_eq
        ((isLagrangian_range_fromRows_iff _ _).1 (isLagrangian_smulFrame g U)).2)⟩

private theorem smul_unitaryFrame_eq (g : GLSymplectic ι ℝ) (U : unitaryGroup ι ℂ) :
    g • unitaryFrame U = unitaryFrame (smulUnitary g U) :=
  toSubmodule_injective <| by
    rw [coe_unitaryFrame_eq_map, smulUnitary, GeneralLinearGroup.realImage_realOrthonormalize,
      smulFrameGL, GeneralLinearGroup.val_mkOfDetNeZero, coe_smul_unitaryFrame,
      range_toEuclideanLin_fromRows_eq_map_realImage]

private theorem continuous_smulUnitary :
    Continuous fun p : GLSymplectic ι ℝ × unitaryGroup ι ℂ ↦ smulUnitary p.1 p.2 := by
  have hA : Continuous fun p : GLSymplectic ι ℝ × unitaryGroup ι ℂ ↦ smulFrame p.1 p.2 := by
    have hg : Continuous fun g : GLSymplectic ι ℝ ↦
        ((g : GL (ι ⊕ ι) ℝ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) :=
      Units.continuous_val.comp continuous_subtypeVal
    have hU : Continuous fun p : GLSymplectic ι ℝ × unitaryGroup ι ℂ ↦ (p.2 : Matrix ι ι ℂ) :=
      continuous_subtypeVal.comp continuous_snd
    exact (hg.comp continuous_fst).matrix_mul (continuous_matrix fun i j ↦ by
      cases i <;> simp only [fromRows_apply_inl, fromRows_apply_inr, map_apply]
      exacts [Complex.continuous_re.comp (hU.matrix_elem _ _),
        Complex.continuous_im.comp (hU.matrix_elem _ _)])
  have hM : Continuous fun p : GLSymplectic ι ℝ × unitaryGroup ι ℂ ↦
      ((smulFrameGL p.1 p.2 : GL ι ℂ) : Matrix ι ι ℂ) := by
    simp only [smulFrameGL, GeneralLinearGroup.val_mkOfDetNeZero]
    have h₁ : Continuous fun p : GLSymplectic ι ℝ × unitaryGroup ι ℂ ↦
        (smulFrame p.1 p.2).toRows₁ :=
      continuous_matrix fun i j ↦ hA.matrix_elem (Sum.inl i) j
    have h₂ : Continuous fun p : GLSymplectic ι ℝ × unitaryGroup ι ℂ ↦
        (smulFrame p.1 p.2).toRows₂ :=
      continuous_matrix fun i j ↦ hA.matrix_elem (Sum.inr i) j
    exact (h₁.matrix_map Complex.continuous_ofReal).add
      ((h₂.matrix_map Complex.continuous_ofReal).const_smul Complex.I)
  have hGL : Continuous fun p : GLSymplectic ι ℝ × unitaryGroup ι ℂ ↦ smulFrameGL p.1 p.2 := by
    refine Units.continuous_iff.2 ⟨hM, ?_⟩
    simp only [Matrix.coe_units_inv, Matrix.inv_def, Ring.inverse_eq_inv']
    exact (hM.matrix_det.inv₀ fun p ↦ (smulFrameGL p.1 p.2).isUnit.map detMonoidHom |>.ne_zero)
      |>.smul hM.matrix_adjugate
  exact continuous_induced_rng.2
    (Units.continuous_val.comp (GeneralLinearGroup.continuous_realOrthonormalize hGL))

/-- The symplectic group `Sp(2n)` acts continuously on the Lagrangian Grassmannian. -/
instance : ContinuousSMul (GLSymplectic ι ℝ) (ℒ ι) := by
  refine ⟨(((IsOpenQuotientMap.id (X := GLSymplectic ι ℝ)).prodMap
    (isOpenQuotientMap_unitaryFrame (ι := ι))).continuous_comp_iff).1 ?_⟩
  simp only [Function.comp_def, Prod.map_fst, Prod.map_snd, id_eq, smul_unitaryFrame_eq]
  exact continuous_unitaryFrame.comp continuous_smulUnitary

/-- The unitary group `U(n)` acts continuously on the Lagrangian Grassmannian. -/
instance : ContinuousSMul (unitaryGroup ι ℂ) (ℒ ι) :=
  ⟨by
    simp only [unitary_smul_def]
    exact (GLSymplectic.continuous_ofUnitary.comp continuous_fst).smul continuous_snd⟩

end LagrangianGrassmannian

end SymplecticGeometry

end
