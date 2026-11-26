/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Topology.Grassmannian.Lagrangian.Sum
public import TauCeti.Analysis.Matrix.UnitaryGroup.Maslov.Loop
public import TauCeti.Analysis.Matrix.UnitaryGroup.Maslov.Multiplicity
public import SymplecticGeometry.Topology.Grassmannian.Lagrangian.Quotient
import SymplecticGeometry.Topology.Grassmannian.Lagrangian.Fibration

/-!
# The Maslov phase and the Maslov index of loops of Lagrangian subspaces

Write `ℒ ι` for the space of Lagrangian subspaces of the standard model `(StdSpace ι, ω₀)`, and
`unitaryFrame U = U • {y = 0}` for the Lagrangian framed by a unitary matrix `U = X + i Y`.

## Main definitions

* `SymplecticGeometry.LagrangianGrassmannian.souriau : ℒ ι → U(n)`, the Souriau map
  `Λ ↦ U Uᵀ` for any unitary frame `U` of `Λ`. Two frames of one Lagrangian differ by a real
  orthogonal matrix on the right, which does not change `U Uᵀ`, and conversely
  (`unitaryFrame_eq_unitaryFrame_iff_souriau_eq`); so `souriau` is well defined, continuous and
  injective, hence a closed embedding (`isClosedEmbedding_souriau`).
* `SymplecticGeometry.LagrangianGrassmannian.maslovPhase Λ = det (souriau Λ)`, the map
  `ρ : ℒ(n) → S¹` of McDuff–Salamon; on a unitary frame it is `(det U)²`, and `rotate θ`
  multiplies it by `e^{2inθ}` (`maslovPhase_rotate`). `maslovPhaseMap` is `ρ` as a bundled
  continuous map.
* `SymplecticGeometry.LagrangianGrassmannian.maslovIndex γ`, for a loop `γ : Path Λ Λ`, the degree
  of the circle loop `t ↦ ρ (γ t)`.
* `SymplecticGeometry.LagrangianGrassmannian.halfTurnLoop k`, the loop
  `t ↦ rotate (π k t) {y = 0} = e^{iπkt} • {y = 0}`, `0 ≤ t ≤ 1`.

## Main results

* Invariance of the index under free homotopies of loops (`maslovIndex_eq_of_homotopy`), its
  behaviour under constant loops, concatenation, reversal and relabelling of coordinates, and on
  loops of unitary frames (`maslovIndex_map_unitaryFrame`): all read off `Circle.degree`.
* `maslovIndex_eq_totallyRealLoop_maslovIndex`: for every lift of a loop to a path of unitary
  frames, the index is Tau Ceti's index `TauCeti.TotallyRealLoop.maslovIndex` of the corresponding
  loop of totally real subspaces of `ℂⁿ`; such a lift exists since `unitaryFrame` is a fibration
  (`exists_realImageLoop_maslovIndex_eq`).
* `maslovIndex_sum`: the index of a direct sum of loops is the sum of the indices.
* `angleChange_map_detCircle`: along a path of unitary frames of a loop `γ`, the determinant has
  angle change `π μ(γ)`; so a path of frames from `U` to `V` has
  `det (U⁻¹ V) = e^{iπμ(γ)}` (`detCircle_inv_mul_eq_exp`), and if `det (X + i Y)(t) = e^{i α(t)}`
  along it, with `α` continuous, the index is `(α 1 - α 0) / π` (`maslovIndex_eq_sub_div_pi`).
* `maslovIndex_halfTurnLoop`: the loop `halfTurnLoop k` has index `k n`; for `n = 1`, `k = 1`
  this is the normalization of the index.

## Implementation notes

Much of this file adapts Tau Ceti's Maslov index of loops of symplectic matrices
(`TauCeti/Analysis/Matrix/SymplecticGroup/Maslov.lean`) and its index of loops of totally real
subspaces (`TauCeti/LinearAlgebra/TotallyReal/Loop.lean`,
`TauCeti/LinearAlgebra/TotallyReal/Maslov/Index.lean`), with `ℒ ι` and its phase
`maslovPhase` in place of the symplectic group or of totally real subspaces and their phases:

* the definition `maslovIndex` is that of `TauCeti.GLSymplectic.maslovIndex`, and
  `maslovIndex_eq_of_homotopy`, `maslovIndex_eq_of_homotopic`, `maslovIndex_refl`,
  `maslovIndex_trans`, `maslovIndex_symm` and `maslovIndex_sum` follow the proofs of
  `TauCeti.GLSymplectic.maslovIndex_eq_of_homotopy`,
  `TauCeti.GLSymplectic.maslovIndex_eq_of_homotopic`, `TauCeti.GLSymplectic.maslovIndex_refl`,
  `TauCeti.GLSymplectic.maslovIndex_trans`, `TauCeti.GLSymplectic.maslovIndex_symm` and
  `TauCeti.GLSymplectic.maslovIndex_sum`;
* `halfTurnLoop` is the loop `TauCeti.TotallyRealLoop.rotationZPow` of `k` half-turns, and
  `maslovIndex_halfTurnLoop` is the analogue of `TauCeti.TotallyRealLoop.maslovIndex_rotationZPow`.
  `maslovPhase_rotate`, `maslovPhase_halfTurnLoop` and `maslovIndex_halfTurnLoop` split the proof of
  `TauCeti.GLSymplectic.maslovIndex_scalarRotationLoop` into the phase and its degree.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.3
  (Theorem 2.3.7 and its proof).
* [J. Robbin, D. Salamon, *The Maslov index for paths*][RobbinSalamon1993], §2.
-/

public section

namespace SymplecticGeometry

open Matrix TauCeti
open Matrix.UnitaryGroup (detCircle continuous_detCircle coe_detCircle detCircle_sum)
open scoped unitInterval

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

local notation "ℒ" ι => LagrangianGrassmannian (stdForm ι)

namespace LagrangianGrassmannian

/-! ### The Souriau map -/

/-- Two unitary matrices frame the same Lagrangian iff they have the same Souriau map
`U Uᵀ`. -/
theorem unitaryFrame_eq_unitaryFrame_iff_souriau_eq {U V : unitaryGroup ι ℂ} :
    unitaryFrame U = unitaryFrame V ↔ UnitaryGroup.souriau U = UnitaryGroup.souriau V := by
  rw [← toSubmodule_inj, coe_unitaryFrame_eq_map, coe_unitaryFrame_eq_map,
    (Submodule.map_injective_of_injective (StdSpace.complexEuclideanEquiv ι).injective).eq_iff,
    UnitaryGroup.realImage_eq_realImage_iff_souriau_eq]

/-- The **Souriau map** `Λ ↦ U Uᵀ` of the Lagrangian Grassmannian into the unitary group, where
`U` is any unitary frame of `Λ`: the descent of `Matrix.UnitaryGroup.souriau` along the quotient
map `unitaryFrame`. -/
noncomputable def souriau (Λ : ℒ ι) : unitaryGroup ι ℂ :=
  (isQuotientMap_unitaryFrame (ι := ι)).lift
    (f := ⟨unitaryFrame (ι := ι), continuous_unitaryFrame⟩)
    ⟨UnitaryGroup.souriau, UnitaryGroup.continuous_souriau⟩
    (fun _ _ h ↦ unitaryFrame_eq_unitaryFrame_iff_souriau_eq.1 h) Λ

theorem souriau_def (Λ : ℒ ι) :
    souriau Λ =
      (isQuotientMap_unitaryFrame (ι := ι)).lift
        (f := ⟨unitaryFrame (ι := ι), continuous_unitaryFrame⟩)
        ⟨UnitaryGroup.souriau, UnitaryGroup.continuous_souriau⟩
        (fun _ _ h ↦ unitaryFrame_eq_unitaryFrame_iff_souriau_eq.1 h) Λ :=
  (rfl)

/-- The Souriau map of the Lagrangian framed by `U` is `U Uᵀ`. -/
@[simp]
theorem souriau_unitaryFrame (U : unitaryGroup ι ℂ) :
    souriau (unitaryFrame U) = UnitaryGroup.souriau U :=
  DFunLike.congr_fun ((isQuotientMap_unitaryFrame (ι := ι)).lift_comp
    (f := ⟨unitaryFrame (ι := ι), continuous_unitaryFrame⟩)
    ⟨UnitaryGroup.souriau, UnitaryGroup.continuous_souriau⟩
    (fun _ _ h ↦ unitaryFrame_eq_unitaryFrame_iff_souriau_eq.1 h)) U

/-- The Souriau map of the horizontal Lagrangian `{y = 0}` is the identity. -/
@[simp]
theorem souriau_horizontal : souriau (horizontal ι) = 1 := by
  rw [← unitaryFrame_one, souriau_unitaryFrame]
  exact Subtype.ext (by simp)

/-- The Souriau map is continuous. -/
@[continuity, fun_prop]
theorem continuous_souriau : Continuous (souriau : (ℒ ι) → unitaryGroup ι ℂ) :=
  ContinuousMap.continuous _

/-- A Lagrangian subspace is determined by its Souriau map. -/
theorem souriau_injective : Function.Injective (souriau : (ℒ ι) → unitaryGroup ι ℂ) := by
  intro Λ Λ' h
  obtain ⟨U, rfl⟩ := unitaryFrame_surjective Λ
  obtain ⟨V, rfl⟩ := unitaryFrame_surjective Λ'
  rw [souriau_unitaryFrame, souriau_unitaryFrame] at h
  exact unitaryFrame_eq_unitaryFrame_iff_souriau_eq.2 h

/-- The Souriau map is a closed embedding of `ℒ ι` into the unitary group: it is a continuous
injection from a compact space into a Hausdorff space. -/
theorem isClosedEmbedding_souriau :
    Topology.IsClosedEmbedding (souriau : (ℒ ι) → unitaryGroup ι ℂ) :=
  continuous_souriau.isClosedEmbedding souriau_injective

/-- The Souriau map of a direct sum is the block-diagonal sum of the Souriau maps. -/
@[simp]
theorem souriau_sum (Λ : ℒ ι) (Λ' : ℒ κ) :
    souriau (sum (Λ, Λ')) = UnitaryGroup.sum (souriau Λ, souriau Λ') := by
  obtain ⟨U, rfl⟩ := unitaryFrame_surjective Λ
  obtain ⟨V, rfl⟩ := unitaryFrame_surjective Λ'
  rw [sum_unitaryFrame, souriau_unitaryFrame, souriau_unitaryFrame, souriau_unitaryFrame,
    UnitaryGroup.souriau_sum]

/-- Relabelling the coordinate pairs along `e` reindexes the Souriau map along `e`. -/
@[simp]
theorem souriau_reindex (e : ι ≃ κ) (Λ : ℒ ι) :
    souriau (reindex e Λ) = unitaryReindexContinuousMulEquiv ℂ e (souriau Λ) := by
  obtain ⟨U, rfl⟩ := unitaryFrame_surjective Λ
  rw [reindex_unitaryFrame, souriau_unitaryFrame, souriau_unitaryFrame]
  refine Subtype.ext ?_
  simp only [UnitaryGroup.coe_souriau, coe_unitaryReindexContinuousMulEquiv_apply, reindex_apply,
    transpose_submatrix, submatrix_mul_equiv]

/-- Under the action of a unitary matrix `U` on `ℒ ι`, the Souriau map transforms by the
congruence `W ↦ U W Uᵀ`: `souriau (U • Λ) = U (souriau Λ) Uᵀ`. -/
@[simp]
theorem souriau_unitary_smul (U : unitaryGroup ι ℂ) (Λ : ℒ ι) :
    souriau (U • Λ) = U * souriau Λ * UnitaryGroup.transpose U := by
  obtain ⟨W, rfl⟩ := unitaryFrame_surjective Λ
  rw [← unitaryFrame_mul, souriau_unitaryFrame, souriau_unitaryFrame]
  refine Subtype.ext ?_
  rw [UnitaryGroup.coe_souriau_mul_left]
  simp

/-- **The eigenvalue `1` of the Souriau map.** Its multiplicity as a root of the characteristic
polynomial of `souriau Λ` is the dimension of `Λ ∩ {y = 0}`. -/
theorem rootMultiplicity_one_charpoly_souriau (Λ : ℒ ι) :
    (souriau Λ : Matrix ι ι ℂ).charpoly.rootMultiplicity 1 =
      Module.finrank ℝ ↥((Λ : Submodule ℝ (StdSpace ι)) ⊓ horizontal ι) := by
  obtain ⟨U, rfl⟩ := unitaryFrame_surjective Λ
  rw [souriau_unitaryFrame, UnitaryGroup.rootMultiplicity_one_charpoly_souriau,
    finrank_unitaryFrame_inf_horizontal]

/-! ### The Maslov phase -/

/-- The **Maslov phase** `ρ(Λ) = det (U Uᵀ) = (det U)²` of a Lagrangian subspace `Λ` with unitary
frame `U`. -/
noncomputable def maslovPhase (Λ : ℒ ι) : Circle :=
  detCircle (souriau Λ)

theorem maslovPhase_def (Λ : ℒ ι) : maslovPhase Λ = detCircle (souriau Λ) :=
  (rfl)

/-- The Maslov phase is continuous. -/
@[continuity, fun_prop]
theorem continuous_maslovPhase : Continuous (maslovPhase : (ℒ ι) → Circle) :=
  continuous_detCircle.comp continuous_souriau

/-- The Maslov phase `ρ : ℒ(n) → S¹` as a bundled continuous map. -/
noncomputable def maslovPhaseMap : C(ℒ ι, Circle) :=
  ⟨maslovPhase, continuous_maslovPhase⟩

@[simp]
theorem coe_maslovPhaseMap : ⇑(maslovPhaseMap : C(ℒ ι, Circle)) = maslovPhase :=
  (rfl)

theorem maslovPhaseMap_apply (Λ : ℒ ι) : maslovPhaseMap Λ = maslovPhase Λ :=
  (rfl)

/-- A homotopy, with fixed ends, of paths of Lagrangians gives a homotopy, with fixed ends, of
their Maslov phase paths `t ↦ ρ (γ t)` in the circle. -/
theorem homotopic_map_maslovPhase {Λ Λ' : ℒ ι} {γ₀ γ₁ : Path Λ Λ'} (h : γ₀.Homotopic γ₁) :
    (γ₀.map continuous_maslovPhase).Homotopic (γ₁.map continuous_maslovPhase) :=
  h.map maslovPhaseMap

/-- The Maslov phase of the Lagrangian framed by `U` is `(det U)²`. -/
@[simp]
theorem maslovPhase_unitaryFrame (U : unitaryGroup ι ℂ) :
    maslovPhase (unitaryFrame U) = detCircle U ^ 2 := by
  rw [maslovPhase_def, souriau_unitaryFrame, UnitaryGroup.detCircle_souriau]

/-- The horizontal Lagrangian has Maslov phase `1`. -/
@[simp]
theorem maslovPhase_horizontal : maslovPhase (horizontal ι) = 1 := by
  simp [maslovPhase_def]

/-- The Maslov phase of a direct sum is the product of the Maslov phases. -/
@[simp]
theorem maslovPhase_sum (Λ : ℒ ι) (Λ' : ℒ κ) :
    maslovPhase (sum (Λ, Λ')) = maslovPhase Λ * maslovPhase Λ' := by
  rw [maslovPhase_def, souriau_sum, detCircle_sum, maslovPhase_def, maslovPhase_def]

/-- Relabelling the coordinate pairs does not change the Maslov phase. -/
@[simp]
theorem maslovPhase_reindex (e : ι ≃ κ) (Λ : ℒ ι) : maslovPhase (reindex e Λ) = maslovPhase Λ := by
  rw [maslovPhase_def, souriau_reindex, maslovPhase_def]
  refine Circle.ext ?_
  rw [coe_detCircle, coe_detCircle, coe_unitaryReindexContinuousMulEquiv_apply, det_reindex_self]

/-- A unitary matrix `U`, acting through its realification, multiplies the Maslov phase by
`(det U)²`. -/
@[simp]
theorem maslovPhase_unitary_smul (U : unitaryGroup ι ℂ) (Λ : ℒ ι) :
    maslovPhase (U • Λ) = detCircle U ^ 2 * maslovPhase Λ := by
  obtain ⟨W, rfl⟩ := unitaryFrame_surjective Λ
  rw [← unitaryFrame_mul, maslovPhase_unitaryFrame, maslovPhase_unitaryFrame,
    map_mul, mul_pow]

/-- The rotation `rotate θ` multiplies the Maslov phase by `e^{2inθ}`, where `n` is the
cardinality of `ι`. -/
@[simp]
theorem maslovPhase_rotate (θ : ℝ) (Λ : ℒ ι) :
    maslovPhase (rotate θ Λ) = Circle.exp (2 * Fintype.card ι * θ) * maslovPhase Λ := by
  rw [rotate_def, maslovPhase_unitary_smul]
  congr 1
  refine Circle.ext ?_
  simp [Circle.coe_exp, ← Complex.exp_natCast_mul]
  ring_nf

/-! ### The Maslov index of a loop -/

/-- The **Maslov index** of a loop `γ` of Lagrangian subspaces: the degree of the circle loop
`t ↦ ρ(γ t)`, where `ρ` is the Maslov phase `maslovPhase`. -/
noncomputable def maslovIndex {Λ : ℒ ι} (γ : Path Λ Λ) : ℤ :=
  Circle.degree (γ.map continuous_maslovPhase)

theorem maslovIndex_def {Λ : ℒ ι} (γ : Path Λ Λ) :
    maslovIndex γ = Circle.degree (γ.map continuous_maslovPhase) :=
  (rfl)

/-- **Homotopy invariance.** If `F` is a homotopy from the loop `γ₀` to the loop `γ₁` through loops
of Lagrangian subspaces (`F (s, 0) = F (s, 1)` for every `s`; the base point may move), the two
loops have the same Maslov index. -/
theorem maslovIndex_eq_of_homotopy {Λ Λ' : ℒ ι} (γ₀ : Path Λ Λ) (γ₁ : Path Λ' Λ')
    (F : C(I × I, ℒ ι)) (h₀ : ∀ t, F (0, t) = γ₀ t) (h₁ : ∀ t, F (1, t) = γ₁ t)
    (hF : ∀ s, F (s, 0) = F (s, 1)) :
    maslovIndex γ₀ = maslovIndex γ₁ :=
  Circle.degree_eq_of_homotopy _ _
    (maslovPhaseMap.comp F)
    (fun t ↦ by simp [h₀]) (fun t ↦ by simp [h₁]) (fun s ↦ by simp [hF])

/-- Loops that are homotopic relative to their base point have the same Maslov index. -/
theorem maslovIndex_eq_of_homotopic {Λ : ℒ ι} {γ₀ γ₁ : Path Λ Λ} (h : γ₀.Homotopic γ₁) :
    maslovIndex γ₀ = maslovIndex γ₁ :=
  Circle.degree_eq_of_homotopic (homotopic_map_maslovPhase h)

/-- A constant loop has Maslov index zero. -/
@[simp]
theorem maslovIndex_refl (Λ : ℒ ι) : maslovIndex (Path.refl Λ) = 0 :=
  (Circle.degree_congr _ (Path.refl (maslovPhase Λ)) fun _ ↦ by simp).trans (Circle.degree_refl _)

/-- The Maslov index is additive under concatenation of loops. -/
@[simp]
theorem maslovIndex_trans {Λ : ℒ ι} (γ₁ γ₂ : Path Λ Λ) :
    maslovIndex (γ₁.trans γ₂) = maslovIndex γ₁ + maslovIndex γ₂ := by
  rw [maslovIndex, Path.map_trans, Circle.degree_trans, maslovIndex, maslovIndex]

/-- Reversing a loop negates its Maslov index. -/
@[simp]
theorem maslovIndex_symm {Λ : ℒ ι} (γ : Path Λ Λ) : maslovIndex γ.symm = -maslovIndex γ := by
  rw [maslovIndex, ← Path.map_symm, Circle.degree_symm, maslovIndex]

/-- Relabelling the coordinate pairs does not change the Maslov index of a loop. -/
@[simp]
theorem maslovIndex_reindex (e : ι ≃ κ) {Λ : ℒ ι} (γ : Path Λ Λ) :
    maslovIndex (γ.map (continuous_reindex e)) = maslovIndex γ :=
  Circle.degree_congr _ _ fun t ↦ by simp

/-- The Maslov index of the loop of Lagrangians framed by a loop `δ` of unitary matrices is twice
the degree of the loop of determinants `t ↦ det (δ t)`. -/
theorem maslovIndex_map_unitaryFrame {U : unitaryGroup ι ℂ} (δ : Path U U) :
    maslovIndex (δ.map continuous_unitaryFrame) =
      2 * Circle.degree (δ.map continuous_detCircle) := by
  rw [maslovIndex_def, Circle.degree_congr _ ((δ.map continuous_detCircle).map (continuous_pow 2))
    fun t ↦ by simp, Circle.degree_map_pow]
  push_cast
  ring

/-! ### Comparison with Tau Ceti's index of totally real loops -/

/-- **The index of a Lagrangian loop is Tau Ceti's index of totally real loops.** Let `δ` be a
path of unitary frames of a loop `γ`, so that `unitaryFrame (δ t) = γ t`. Then the Maslov index of
`γ` is the index `TauCeti.TotallyRealLoop.maslovIndex` of the loop `t ↦ δ t ℝⁿ` of Lagrangian
subspaces of `ℂⁿ` (`Matrix.UnitaryGroup.realImageLoop`). -/
theorem maslovIndex_eq_totallyRealLoop_maslovIndex {Λ : ℒ ι} (γ : Path Λ Λ)
    {U V : unitaryGroup ι ℂ} (δ : Path U V) (hδ : ∀ t, unitaryFrame (δ t) = γ t)
    (h : UnitaryGroup.souriau U = UnitaryGroup.souriau V) :
    maslovIndex γ = (UnitaryGroup.realImageLoop δ h).maslovIndex := by
  have hR := UnitaryGroup.maslovIndex_realImageLoop δ h
  rw [UnitaryGroup.maslovIndex_eq_degree δ h] at hR
  have hγ : maslovIndex γ =
      Circle.degree ((UnitaryGroup.detSouriauPath δ).cast rfl (congrArg detCircle h)) :=
    Circle.degree_congr _ _ fun t ↦ by
      rw [Path.map_coe, Function.comp_apply, ← hδ t, maslovPhase_def, souriau_unitaryFrame,
        Path.cast_coe, UnitaryGroup.detSouriauPath_apply]
  rw [hγ]
  exact_mod_cast hR.symm

/-- Every loop of Lagrangian subspaces has a lift `δ` to a path of unitary frames, and its Maslov
index is Tau Ceti's index of the loop of totally real subspaces `t ↦ δ t ℝⁿ` of `ℂⁿ`. -/
theorem exists_realImageLoop_maslovIndex_eq {Λ : ℒ ι} (γ : Path Λ Λ) :
    ∃ (U V : unitaryGroup ι ℂ) (δ : Path U V) (h : UnitaryGroup.souriau U = UnitaryGroup.souriau V),
      (∀ t, unitaryFrame (δ t) = γ t) ∧
        (UnitaryGroup.realImageLoop δ h).maslovIndex = maslovIndex γ := by
  obtain ⟨U, hU⟩ := unitaryFrame_surjective Λ
  obtain ⟨V, δ, hδ⟩ := exists_path_lift_unitaryFrame γ hU
  have h : UnitaryGroup.souriau U = UnitaryGroup.souriau V :=
    unitaryFrame_eq_unitaryFrame_iff_souriau_eq.1 <| by
      have h₀ := hδ 0
      have h₁ := hδ 1
      rw [Path.source, Path.source] at h₀
      rw [Path.target, Path.target] at h₁
      rw [h₀, h₁]
  exact ⟨U, V, δ, h, hδ, (maslovIndex_eq_totallyRealLoop_maslovIndex γ δ hδ h).symm⟩

/-! ### Direct sums and the angle of a frame -/

/-- **The direct-sum property.** The Maslov index of the direct sum `t ↦ γ t ⊕ γ' t` of two loops
of Lagrangian subspaces is the sum of their Maslov indices. -/
@[simp]
theorem maslovIndex_sum {Λ : ℒ ι} {Λ' : ℒ κ} (γ : Path Λ Λ) (γ' : Path Λ' Λ') :
    maslovIndex ((γ.prod γ').map continuous_sum) = maslovIndex γ + maslovIndex γ' := by
  rw [maslovIndex_def, maslovIndex_def, maslovIndex_def, ← Circle.degree_mul]
  exact Circle.degree_congr _ _ fun t ↦ by simp

/-- Along a path `δ` of unitary frames of a loop `γ` (`unitaryFrame (δ t) = γ t`), the determinant
turns through the angle `π μ(γ)`. -/
theorem angleChange_map_detCircle {Λ : ℒ ι} (γ : Path Λ Λ) {U V : unitaryGroup ι ℂ}
    (δ : Path U V) (hδ : ∀ t, unitaryFrame (δ t) = γ t) :
    Circle.angleChange (δ.map continuous_detCircle) = maslovIndex γ * Real.pi := by
  have h := Circle.angleChange_eq_degree_mul (γ.map continuous_maslovPhase)
  rw [← Circle.angleChange_congr ((δ.map continuous_detCircle).mul (δ.map continuous_detCircle))
    _ fun t ↦ by simp [← hδ t, sq], Circle.angleChange_mul, ← maslovIndex_def] at h
  linarith

/-- **The index as the angle of a frame.** Let `δ` be a path of unitary frames of a loop `γ`, and
`det (δ t) = e^{i α(t)}` with `α` continuous. Then the Maslov index of `γ` is
`(α 1 - α 0) / π`. -/
theorem maslovIndex_eq_sub_div_pi {Λ : ℒ ι} (γ : Path Λ Λ) {U V : unitaryGroup ι ℂ}
    (δ : Path U V) (hδ : ∀ t, unitaryFrame (δ t) = γ t) {α : I → ℝ} (hα : Continuous α)
    (h : ∀ t, (δ t : Matrix ι ι ℂ).det = Complex.exp (α t * Complex.I)) :
    (maslovIndex γ : ℝ) = (α 1 - α 0) / Real.pi := by
  have hsub := Circle.angleChange_eq_sub (δ.map continuous_detCircle) hα fun t ↦ Circle.ext <| by
    rw [Path.map_coe, Function.comp_apply, coe_detCircle, h t, Circle.coe_exp]
  rw [angleChange_map_detCircle γ δ hδ] at hsub
  rw [eq_div_iff Real.pi_ne_zero, hsub]

/-- If a path `δ` of unitary frames of a loop `γ` runs from `U` to `V`, then `det (U⁻¹ V)` is
`(-1)^μ(γ)`, written `e^{iπμ(γ)}`. -/
theorem detCircle_inv_mul_eq_exp {Λ : ℒ ι} (γ : Path Λ Λ) {U V : unitaryGroup ι ℂ}
    (δ : Path U V) (hδ : ∀ t, unitaryFrame (δ t) = γ t) :
    detCircle (U⁻¹ * V) = Circle.exp (maslovIndex γ * Real.pi) := by
  rw [← angleChange_map_detCircle γ δ hδ, Circle.exp_angleChange, map_mul, map_inv,
    div_eq_inv_mul]

/-! ### Half-turns -/

/-- The loop `t ↦ rotate (π k t) {y = 0}`, `0 ≤ t ≤ 1`, of Lagrangian subspaces, turning the
horizontal Lagrangian through `k` half-turns: the rotation `rotationPath` through the angle `π k`,
which closes up since `e^{iπk} = ±1`. -/
noncomputable def halfTurnLoop (k : ℤ) : Path (horizontal ι) (horizontal ι) :=
  (rotationPath (horizontal ι) (Real.pi * k)).cast rfl
    (by rw [mul_comm, rotate_int_mul_pi])

/-- The loop `halfTurnLoop k` at time `t` is the rotation of `{y = 0}` by the angle `π k t`. -/
theorem halfTurnLoop_apply (k : ℤ) (t : I) :
    halfTurnLoop k t = rotate (Real.pi * k * t) (horizontal ι) :=
  rotationPath_apply _ _ t

/-- The Maslov phase of `halfTurnLoop k` at time `t` is `e^{2iπnkt}`, where `n` is the
cardinality of `ι`. -/
@[simp]
theorem maslovPhase_halfTurnLoop (k : ℤ) (t : I) :
    maslovPhase (halfTurnLoop (ι := ι) k t) =
      Circle.exp (2 * Fintype.card ι * (Real.pi * k * t)) := by
  rw [halfTurnLoop_apply, maslovPhase_rotate, maslovPhase_horizontal, mul_one]

/-- **Normalization.** The loop of `k` half-turns of the horizontal Lagrangian of `StdSpace ι` has
Maslov index `k n`, where `n` is the cardinality of `ι`. In particular the half-turn
`t ↦ e^{iπt} ℝ` in `ℒ(1)` has Maslov index `1`. -/
@[simp]
theorem maslovIndex_halfTurnLoop (k : ℤ) :
    maslovIndex (halfTurnLoop (ι := ι) k) = k * Fintype.card ι := by
  refine Circle.degree_eq_of_sub_eq _ (θ := fun t ↦ 2 * Fintype.card ι * (Real.pi * k * t))
    (by fun_prop) (fun t ↦ by rw [Path.map_coe, Function.comp_apply, maslovPhase_halfTurnLoop])
    (by simp only [Set.Icc.coe_one, Set.Icc.coe_zero]; push_cast; ring)

end LagrangianGrassmannian

end SymplecticGeometry

end
