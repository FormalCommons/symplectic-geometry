/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import TauCeti.Analysis.InnerProductSpace.Projection.Basic
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
* `SymplecticGeometry.LagrangianGrassmannian.continuous_unitaryOfFrame` and
  `continuous_ofFrame`: the unitary matrix of a Lagrangian frame, and the Lagrangian
  that the frame spans, depend continuously on the frame.
* `ContinuousSMul` instances for `GLSymplectic ι ℝ` and `unitaryGroup ι ℂ` acting on `ℒ ι`, and
  `SymplecticGeometry.LagrangianGrassmannian.continuous_rotate`: rotations are continuous in the
  angle, so `rotationPath Λ ε`, `s ↦ rotate (ε s) Λ`, is a path from `Λ` to `rotate ε Λ`.

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
  let u : unitary (StdSpace ι →L[ℝ] StdSpace ι) :=
    ⟨toEuclideanCLM (n := ι ⊕ ι) (𝕜 := ℝ) (U : Matrix ι ι ℂ).realify,
      Unitary.map_mem _ (realify_mem_orthogonalGroup_iff.2 U.property)⟩
  have hu : ((u : StdSpace ι →L[ℝ] StdSpace ι) : StdSpace ι →ₗ[ℝ] StdSpace ι) =
      toEuclideanLin (U : Matrix ι ι ℂ).realify :=
    coe_toEuclideanCLM_eq_toEuclideanLin _
  have he : ((Unitary.linearIsometryEquiv u).toLinearEquiv : StdSpace ι →ₗ[ℝ] StdSpace ι) =
      (u : StdSpace ι →L[ℝ] StdSpace ι) :=
    LinearMap.ext fun x ↦ DFunLike.congr_fun (Unitary.coe_linearIsometryEquiv_apply u) x
  rw [unitaryFrame_def, coe_unitary_smul, ← hu, ← he,
    ← LinearIsometryEquiv.conjStarAlgEquiv_starProjection,
    Unitary.conjStarAlgEquiv_unitaryLinearIsometryEquiv, Unitary.conjStarAlgAut_apply, map_star]

/-- The Lagrangian framed by a unitary matrix depends continuously on it. -/
theorem continuous_unitaryFrame : Continuous (unitaryFrame : unitaryGroup ι ℂ → ℒ ι) := by
  have hR : Continuous fun U : unitaryGroup ι ℂ ↦ (U : Matrix ι ι ℂ).realify :=
    Matrix.isClosedEmbedding_realify.continuous.comp continuous_subtypeVal
  rw [continuous_iff_continuous_starProjection]
  simp_rw [starProjection_unitaryFrame]
  exact ((continuous_toEuclideanCLM.comp hR).mul continuous_const).mul
    (continuous_toEuclideanCLM.comp (continuous_star.comp hR))

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

/-! ### Continuity in the frame -/

open scoped Matrix.Norms.L2Operator in
/-- The unitary matrix of a Lagrangian frame `fromRows X Y` depends continuously on the frame. -/
theorem continuous_unitaryOfFrame {T : Type*} [TopologicalSpace T] {X Y : T → Matrix ι ι ℝ}
    (hX : Continuous X) (hY : Continuous Y)
    (h : ∀ t, (stdForm ι).IsLagrangian
      (LinearMap.range (toEuclideanLin (fromRows (X t) (Y t))))) :
    Continuous fun t ↦ unitaryOfFrame (h t) := by
  have hM : Continuous fun t ↦ (X t).map Complex.ofReal + Complex.I • (Y t).map Complex.ofReal :=
    (hX.matrix_map Complex.continuous_ofReal).add
      ((hY.matrix_map Complex.continuous_ofReal).const_smul Complex.I)
  have hGL : Continuous fun t ↦ GeneralLinearGroup.mkOfDetNeZero _
      (det_ne_zero_of_isLagrangian_range_fromRows (h t)) :=
    Units.isOpenEmbedding_val.continuous_iff.2 hM
  simp_rw [continuous_induced_rng, Function.comp_def, coe_unitaryOfFrame]
  exact Units.continuous_val.comp (GeneralLinearGroup.continuous_realOrthonormalize hGL)

/-- The Lagrangian spanned by a continuous family of Lagrangian frames `fromRows X Y` depends
continuously on the parameter. -/
theorem continuous_ofFrame {T : Type*} [TopologicalSpace T] {X Y : T → Matrix ι ι ℝ}
    (hX : Continuous X) (hY : Continuous Y)
    (h : ∀ t, (stdForm ι).IsLagrangian
      (LinearMap.range (toEuclideanLin (fromRows (X t) (Y t))))) :
    Continuous fun t ↦ ofFrame (X t) (Y t) (h t) := by
  simp_rw [← unitaryFrame_unitaryOfFrame]
  exact continuous_unitaryFrame.comp (continuous_unitaryOfFrame hX hY h)

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
  rw [fromRows_toRows, coe_smul_of_coe_eq g (coe_unitaryFrame U), smulFrame]

private theorem isLagrangian_smulFrame (g : GLSymplectic ι ℝ) (U : unitaryGroup ι ℂ) :
    (stdForm ι).IsLagrangian (LinearMap.range
      (toEuclideanLin (fromRows (smulFrame g U).toRows₁ (smulFrame g U).toRows₂))) :=
  coe_smul_unitaryFrame g U ▸ (g • unitaryFrame U).isLagrangian

private theorem continuous_smulFrame :
    Continuous fun p : GLSymplectic ι ℝ × unitaryGroup ι ℂ ↦ smulFrame p.1 p.2 := by
  have hg : Continuous fun g : GLSymplectic ι ℝ ↦
      ((g : GL (ι ⊕ ι) ℝ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) :=
    Units.continuous_val.comp continuous_subtypeVal
  have hU : Continuous fun p : GLSymplectic ι ℝ × unitaryGroup ι ℂ ↦ (p.2 : Matrix ι ι ℂ) :=
    continuous_subtypeVal.comp continuous_snd
  exact (hg.comp continuous_fst).matrix_mul (continuous_matrix fun i j ↦ by
    cases i <;> simp only [fromRows_apply_inl, fromRows_apply_inr, map_apply]
    exacts [Complex.continuous_re.comp (hU.matrix_elem _ _),
      Complex.continuous_im.comp (hU.matrix_elem _ _)])

/-- The symplectic group `Sp(2n)` acts continuously on the Lagrangian Grassmannian. -/
instance : ContinuousSMul (GLSymplectic ι ℝ) (ℒ ι) := by
  refine ⟨(((IsOpenQuotientMap.id (X := GLSymplectic ι ℝ)).prodMap
    (isOpenQuotientMap_unitaryFrame (ι := ι))).continuous_comp_iff).1 ?_⟩
  have h : ∀ p : GLSymplectic ι ℝ × unitaryGroup ι ℂ,
      p.1 • unitaryFrame p.2 = ofFrame _ _ (isLagrangian_smulFrame p.1 p.2) :=
    fun p ↦ toSubmodule_injective <| by rw [coe_ofFrame, coe_smul_unitaryFrame]
  simp only [Function.comp_def, Prod.map_fst, Prod.map_snd, id_eq, h]
  exact continuous_ofFrame
    (continuous_matrix fun i j ↦ continuous_smulFrame.matrix_elem (Sum.inl i) j)
    (continuous_matrix fun i j ↦ continuous_smulFrame.matrix_elem (Sum.inr i) j) _

/-- The unitary group `U(n)` acts continuously on the Lagrangian Grassmannian. -/
instance : ContinuousSMul (unitaryGroup ι ℂ) (ℒ ι) :=
  ⟨by
    simp only [unitary_smul_def]
    exact (GLSymplectic.continuous_ofUnitary.comp continuous_fst).smul continuous_snd⟩

/-- The rotation `θ ↦ rotate θ Λ` of a Lagrangian depends continuously on the angle. -/
theorem continuous_rotate (Λ : ℒ ι) : Continuous fun θ : ℝ ↦ rotate θ Λ := by
  have h : Continuous fun θ : ℝ ↦
      UnitaryGroup.scalarHom ι ℂ (circleEquivUnitary (Circle.exp θ)) :=
    continuous_induced_rng.2 <| by
      simp only [Function.comp_def, UnitaryGroup.coe_scalarHom, coe_circleEquivUnitary,
        scalar_apply]
      fun_prop
  simp_rw [rotate_def]
  exact h.smul continuous_const

/-- The **rotation** `s ↦ e^{ε s J₀} Λ`, `s ∈ [0, 1]`, of a Lagrangian `Λ` through the angle `ε`,
from `Λ` to `rotate ε Λ`. -/
noncomputable def rotationPath (Λ : ℒ ι) (ε : ℝ) : Path Λ (rotate ε Λ) where
  toFun t := rotate (ε * t) Λ
  continuous_toFun := (continuous_rotate Λ).comp (continuous_const.mul continuous_subtypeVal)
  source' := by simp
  target' := by simp

@[simp]
theorem rotationPath_apply (Λ : ℒ ι) (ε : ℝ) (t : unitInterval) :
    rotationPath Λ ε t = rotate (ε * t) Λ :=
  (rfl)

end LagrangianGrassmannian

end SymplecticGeometry

end
