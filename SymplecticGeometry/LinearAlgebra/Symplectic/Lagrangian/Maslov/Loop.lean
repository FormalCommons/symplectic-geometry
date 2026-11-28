/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Topology.Algebra.OrthogonalGroup
public import SymplecticGeometry.LinearAlgebra.Symplectic.Lagrangian.Maslov.Basic
public import TauCeti.Analysis.Matrix.SymplecticGroup.Maslov
import SymplecticGeometry.Analysis.Matrix.SymplecticGroup.Maslov
import SymplecticGeometry.Analysis.Matrix.UnitaryGroup.FundamentalGroup
import SymplecticGeometry.LinearAlgebra.Symplectic.Lagrangian.Maslov.Product
import TauCeti.LinearAlgebra.Matrix.OfReal
import TauCeti.LinearAlgebra.Matrix.OrthogonalGroup.Unitary
import SymplecticGeometry.Topology.Grassmannian.Lagrangian.Fibration
import SymplecticGeometry.Topology.Homotopy.Path

/-!
# The Maslov index of loops of Lagrangian subspaces: classification and uniqueness

Write `ℒ ι` for the space of Lagrangian subspaces of the standard model `(StdSpace ι, ω₀)`,
`unitaryFrame U = U • {y = 0}` for the Lagrangian framed by a unitary matrix `U`, and
`μ(γ) = deg(ρ ∘ γ)` for the Maslov index of a loop `γ` in `ℒ ι`
(`SymplecticGeometry.LagrangianGrassmannian.maslovIndex`). This file proves that `μ` classifies
loops up to homotopy, and that it is the only function on loops, in every dimension, that
satisfies the four axioms of `IsLagrangianMaslovIndex` (homotopy, product, direct sum, zero).

Two loops `γ : Path Λ Λ` and `γ' : Path Λ' Λ'` are *freely homotopic* when
`(γ : C(I, ℒ ι)).HomotopicWith γ' fun p ↦ p 0 = p 1`, that is, homotopic through loops whose base
point may move.

* **Classification.** Lift a loop `γ` at `unitaryFrame U` to a path `δ` of unitary frames starting
  at `U` (`exists_path_lift_unitaryFrame`). The angle change of `det ∘ δ` is `π μ(γ)`
  (`angleChange_map_detCircle`, in `Maslov/Basic.lean`), so the end `δ 1 = U W`, with `W` real
  orthogonal, has `det W = (-1)^μ(γ)`. If `γ'` has the same index and lifts to `δ'`, ending at
  `U W'`, then `det W = det W'`; since two orthogonal matrices with the same determinant are
  joined in `O(n)`, multiplying `δ` on the right by a path of orthogonal matrices from `1` to
  `W⁻¹ W'` gives a lift of `γ` that ends at the end of `δ'`, and still has angle change `π μ(γ)`.
  Paths in `U(n)` with the same ends are homotopic exactly when `det` has the same angle change
  along them (`Matrix.UnitaryGroup.homotopic_iff_angleChange_eq`, from the isomorphism
  `π₁(U(n)) ≅ π₁(S¹)`), and the homotopy of lifts maps to one of `γ` and `γ'`.
* **Uniqueness.** A family `μ n` of functions on loops in `ℒ (Fin n)` with the four axioms
  (`SymplecticGeometry.IsLagrangianMaslovIndex`) agrees with the index: on `ℒ (Fin 1)` the loop
  `halfTurnLoop (2 j)` has the index of the symplectic rotation loop `symplecticRotationLoop j`
  acting on a constant loop, hence value `2 j`; the direct sum of `halfTurnLoop k` with itself has
  the index of the direct sum of `halfTurnLoop (2 k)` with a constant loop, hence `halfTurnLoop k`
  has value `k`; and every loop in `ℒ (Fin (n + 1))` is freely homotopic to the direct sum of a
  constant loop and a half-turn (`homotopicWith_reindex_sum_halfTurnLoop`).

## Main results

* `SymplecticGeometry.LagrangianGrassmannian.maslovIndex_eq_iff_homotopic`,
  `SymplecticGeometry.LagrangianGrassmannian.homotopicWith_iff_maslovIndex_eq`: the index
  classifies loops up to homotopy with fixed ends and up to free homotopy.
* `SymplecticGeometry.LagrangianGrassmannian.homotopicWith_reindex_sum_halfTurnLoop`: the normal
  form of a loop in `ℒ (Fin (n + 1))`.
* `SymplecticGeometry.isLagrangianMaslovIndex_iff_and_maslovIndex_halfTurnLoop`: the axioms
  `IsLagrangianMaslovIndex` characterize `γ ↦ deg(ρ ∘ γ)`, and the half-turn in `ℒ (Fin 1)` has
  index `1`.

## Implementation notes

The free form of the classification and the uniqueness argument follow
`TauCeti.GLSymplectic.homotopicWith_iff_maslovIndex_eq` and `SymplecticGeometry.isMaslovIndex_iff`
(`Analysis/Matrix/SymplecticGroup/Maslov.lean`), the corresponding results for loops of
symplectic matrices.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.3
  (Theorem 2.3.7).
-/

public section

open Matrix TauCeti
open Matrix.UnitaryGroup (detCircle continuous_detCircle coe_detCircle)
open scoped unitInterval

namespace SymplecticGeometry

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local notation "ℒ " ι => LagrangianGrassmannian (stdForm ι)

namespace LagrangianGrassmannian

/-- A path `γ` of Lagrangians that is the image of a path `δ` of unitary frames is homotopic to
the image `γ'` of any path homotopic to `δ`. -/
private theorem homotopic_of_homotopic_lift {Λ₀ Λ₁ : ℒ ι} {γ γ' : Path Λ₀ Λ₁}
    {U V : unitaryGroup ι ℂ} {δ δ' : Path U V} (hδ : ∀ t, unitaryFrame (δ t) = γ t)
    (hδ' : ∀ t, unitaryFrame (δ' t) = γ' t) (h : δ.Homotopic δ') : γ.Homotopic γ' := by
  obtain rfl : unitaryFrame U = Λ₀ := by simpa using hδ 0
  obtain rfl : unitaryFrame V = Λ₁ := by simpa using hδ 1
  obtain rfl : δ.map continuous_unitaryFrame = γ := Path.ext (funext hδ)
  obtain rfl : δ'.map continuous_unitaryFrame = γ' := Path.ext (funext hδ')
  exact h.map ⟨unitaryFrame, continuous_unitaryFrame⟩

/-! ### Classification of loops -/

/-- **The Maslov index classifies loops up to homotopy with fixed ends.** Two loops of Lagrangian
subspaces at the same point are homotopic relative to their ends exactly when their Maslov indices
agree; that is, `ρ` induces an injection `π₁(ℒ(n)) → π₁(S¹)`. -/
theorem maslovIndex_eq_iff_homotopic {Λ : ℒ ι} {γ γ' : Path Λ Λ} :
    maslovIndex γ = maslovIndex γ' ↔ γ.Homotopic γ' := by
  refine ⟨fun h ↦ ?_, maslovIndex_eq_of_homotopic⟩
  obtain ⟨U, hU⟩ := unitaryFrame_surjective Λ
  obtain ⟨V, δ, hδ⟩ := exists_path_lift_unitaryFrame γ hU
  obtain ⟨V', δ', hδ'⟩ := exists_path_lift_unitaryFrame γ' hU
  -- The two lifts end at `U W` and `U W'`, with `W`, `W'` orthogonal of the same determinant.
  have hreal {V : unitaryGroup ι ℂ} {γ : Path Λ Λ} (δ : Path U V)
      (hδ : ∀ t, unitaryFrame (δ t) = γ t) : U⁻¹ * V ∈ UnitaryGroup.realSubgroup ι :=
    unitaryFrame_eq_unitaryFrame_iff.1 (by rw [hU, ← δ.target, hδ, γ.target])
  obtain ⟨O, hO, hOW⟩ := UnitaryGroup.mem_realSubgroup_iff_exists.1 (hreal δ hδ)
  obtain ⟨O', hO', hOW'⟩ := UnitaryGroup.mem_realSubgroup_iff_exists.1 (hreal δ' hδ')
  have hdet : O.det = O'.det := by
    have h₁ := congrArg ((↑) : Circle → ℂ) (detCircle_inv_mul_eq_exp γ δ hδ)
    have h₂ := congrArg ((↑) : Circle → ℂ) (detCircle_inv_mul_eq_exp γ' δ' hδ')
    rw [coe_detCircle, ← hOW, det_map_ofReal] at h₁
    rw [coe_detCircle, ← hOW', det_map_ofReal, ← h] at h₂
    exact_mod_cast h₁.trans h₂.symm
  -- A path of orthogonal matrices from `W` to `W'`, as unitary matrices.
  let φ := TauCeti.orthogonalComplexMatrix (n := ι)
  have hφ : Continuous φ := TauCeti.continuous_orthogonalComplexMatrix
  let ε : Path (φ ⟨O, hO⟩) (φ ⟨O', hO'⟩) :=
    ((TauCeti.Matrix.joined_orthogonalGroup_iff_det_eq.2 hdet).somePath).map hφ
  have hε₀ : φ ⟨O, hO⟩ = U⁻¹ * V := Subtype.ext <| by rw [← hOW]; ext; simp [φ]
  have hε₁ : φ ⟨O', hO'⟩ = U⁻¹ * V' := Subtype.ext <| by rw [← hOW']; ext; simp [φ]
  -- Correct `δ` on the right by `(U⁻¹ V)⁻¹ ε`; it now ends at `V'` and still lifts `γ`.
  let δ₂ : Path U V' := (δ.mul (ε.map (continuous_const_mul (U⁻¹ * V)⁻¹))).cast
    (by rw [hε₀, inv_mul_cancel, mul_one])
    (by rw [hε₁, _root_.mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left,
      mul_inv_cancel_left])
  have hδ₂ (t : I) : unitaryFrame (δ₂ t) = γ t := by
    rw [← hδ t]
    refine (unitaryFrame_eq_unitaryFrame_iff.2 ?_).symm
    simp only [δ₂, Path.cast_coe, Path.mul_apply, Path.map_coe, Function.comp_apply,
      inv_mul_cancel_left]
    exact mul_mem (inv_mem (hreal δ hδ))
      (UnitaryGroup.orthogonalComplexMatrix_mem_realSubgroup _)
  refine homotopic_of_homotopic_lift hδ₂ hδ' (UnitaryGroup.homotopic_iff_angleChange_eq.2 ?_)
  rw [angleChange_map_detCircle γ δ₂ hδ₂, angleChange_map_detCircle γ' δ' hδ', h]

/-- Loops of Lagrangian subspaces that are freely homotopic have the same Maslov index. -/
theorem maslovIndex_eq_of_homotopicWith {Λ Λ' : ℒ ι} {γ : Path Λ Λ} {γ' : Path Λ' Λ'}
    (h : (γ : C(I, ℒ ι)).HomotopicWith (γ' : C(I, ℒ ι)) fun p ↦ p 0 = p 1) :
    maslovIndex γ = maslovIndex γ' := by
  obtain ⟨F⟩ := h
  exact maslovIndex_eq_of_homotopy γ γ' F.toContinuousMap (fun t ↦ F.apply_zero t)
    (fun t ↦ F.apply_one t) fun s ↦ F.prop s

/-- **The homotopy axiom.** Two loops of Lagrangian subspaces, at any base points, are freely
homotopic (homotopic through loops) exactly when their Maslov indices agree. -/
theorem homotopicWith_iff_maslovIndex_eq {Λ Λ' : ℒ ι} (γ : Path Λ Λ) (γ' : Path Λ' Λ') :
    (γ : C(I, ℒ ι)).HomotopicWith (γ' : C(I, ℒ ι)) (fun p ↦ p 0 = p 1) ↔
      maslovIndex γ = maslovIndex γ' := by
  refine ⟨maslovIndex_eq_of_homotopicWith, fun h ↦ ?_⟩
  -- Conjugate `γ'` to a loop at `Λ` along a path from `Λ` to `Λ'`, the image of a path of frames.
  obtain ⟨U, rfl⟩ := unitaryFrame_surjective Λ
  obtain ⟨U', rfl⟩ := unitaryFrame_surjective Λ'
  let χ := (PathConnectedSpace.somePath U U').map continuous_unitaryFrame
  have hχ := Path.homotopicWith_trans_trans_symm χ γ'
  have hγ : γ.Homotopic ((χ.trans γ').trans χ.symm) :=
    maslovIndex_eq_iff_homotopic.1 (h.trans (maslovIndex_eq_of_homotopicWith hχ).symm)
  exact hγ.homotopicWith.trans hχ

/-- **Normal form of a loop.** A loop `γ` in `ℒ (Fin (n + 1))` is freely homotopic to the direct
sum of the constant loop at the horizontal Lagrangian of `StdSpace (Fin n)` and the loop
`halfTurnLoop k` of `ℒ (Fin 1)`, with `k` the Maslov index of `γ`, read in `Fin (n + 1)` along
`finSumFinEquiv`. -/
theorem homotopicWith_reindex_sum_halfTurnLoop {n : ℕ} {Λ : ℒ (Fin (n + 1))} (γ : Path Λ Λ) :
    (γ : C(I, ℒ (Fin (n + 1)))).HomotopicWith
      ((((Path.refl (horizontal (Fin n))).prod
        (halfTurnLoop (ι := Fin 1) (maslovIndex γ))).map continuous_sum).map
          (continuous_reindex finSumFinEquiv) : C(I, ℒ (Fin (n + 1))))
      fun p ↦ p 0 = p 1 :=
  (homotopicWith_iff_maslovIndex_eq _ _).2 (by
    rw [maslovIndex_reindex, maslovIndex_sum, maslovIndex_refl, maslovIndex_halfTurnLoop]
    simp)

end LagrangianGrassmannian

/-! ### Uniqueness -/

open LagrangianGrassmannian

/-- The axioms of the Maslov index of loops of Lagrangian subspaces, for a family `μ n` of
integer-valued functions on loops in `ℒ (Fin n)`, one for each `n : ℕ`:

* *homotopy*: two loops are freely homotopic exactly when they have the same value;
* *product*: a loop `Ψ` of symplectic matrices acting on a loop `γ` gives the value of `γ` plus
  twice the Maslov index `TauCeti.GLSymplectic.maslovIndex Ψ`;
* *direct sum*: the direct sum of loops in `ℒ (Fin n)` and `ℒ (Fin m)`, read in `ℒ (Fin (n + m))`
  along `finSumFinEquiv`, has the sum of their values;
* *zero*: constant loops have value `0`. -/
structure IsLagrangianMaslovIndex (μ : (n : ℕ) → (Λ : ℒ (Fin n)) → Path Λ Λ → ℤ) : Prop where
  homotopicWith_iff {n : ℕ} {Λ Λ' : ℒ (Fin n)} (γ : Path Λ Λ) (γ' : Path Λ' Λ') :
    (γ : C(I, ℒ (Fin n))).HomotopicWith (γ' : C(I, ℒ (Fin n))) (fun p ↦ p 0 = p 1) ↔
      μ n Λ γ = μ n Λ' γ'
  smul {n : ℕ} {A : GLSymplectic (Fin n) ℝ} {Λ : ℒ (Fin n)} (Ψ : Path A A) (γ : Path Λ Λ) :
    μ n (A • Λ) ((Ψ.prod γ).map continuous_smul) = μ n Λ γ + 2 * GLSymplectic.maslovIndex Ψ
  sum {n m : ℕ} {Λ : ℒ (Fin n)} {Λ' : ℒ (Fin m)} (γ : Path Λ Λ) (γ' : Path Λ' Λ') :
    μ (n + m) _ (((γ.prod γ').map continuous_sum).map (continuous_reindex finSumFinEquiv)) =
      μ n Λ γ + μ m Λ' γ'
  refl {n : ℕ} (Λ : ℒ (Fin n)) : μ n Λ (Path.refl Λ) = 0

namespace IsLagrangianMaslovIndex

variable {μ : (n : ℕ) → (Λ : ℒ (Fin n)) → Path Λ Λ → ℤ} (hμ : IsLagrangianMaslovIndex μ)
include hμ

/-- Loops with the same Maslov index have the same value. -/
theorem eq_of_maslovIndex_eq {n : ℕ} {Λ Λ' : ℒ (Fin n)} {γ : Path Λ Λ} {γ' : Path Λ' Λ'}
    (h : maslovIndex γ = maslovIndex γ') : μ n Λ γ = μ n Λ' γ' :=
  (hμ.homotopicWith_iff γ γ').1 ((homotopicWith_iff_maslovIndex_eq γ γ').2 h)

/-- The loop `halfTurnLoop (2 j)` in `ℒ (Fin 1)` has value `2 j`: it has the index of the rotation
loop `symplecticRotationLoop j` acting on the constant loop. -/
theorem apply_halfTurnLoop_two_mul (j : ℤ) :
    μ 1 _ (halfTurnLoop (ι := Fin 1) (2 * j)) = 2 * j := by
  have h := hμ.smul (symplecticRotationLoop j) (Path.refl (horizontal (Fin 1)))
  rw [hμ.refl, maslovIndex_symplecticRotationLoop, zero_add] at h
  refine (hμ.eq_of_maslovIndex_eq ?_).trans h
  simp

/-- The loop `halfTurnLoop k` of `k` half-turns in `ℒ (Fin 1)` has value `k`. -/
theorem apply_halfTurnLoop (k : ℤ) : μ 1 _ (halfTurnLoop (ι := Fin 1) k) = k := by
  -- The direct sum of the loop with itself has the index of `halfTurnLoop (2 k)` plus a constant.
  have h := hμ.eq_of_maslovIndex_eq
    (γ := ((((halfTurnLoop (ι := Fin 1) k).prod (halfTurnLoop (ι := Fin 1) k)).map
      continuous_sum).map (continuous_reindex finSumFinEquiv)))
    (γ' := ((((halfTurnLoop (ι := Fin 1) (2 * k)).prod
      (Path.refl (horizontal (Fin 1)))).map continuous_sum).map
        (continuous_reindex finSumFinEquiv))) (by
      simp only [maslovIndex_reindex, maslovIndex_sum, maslovIndex_halfTurnLoop, maslovIndex_refl]
      ring)
  rw [hμ.sum, hμ.sum, hμ.refl, hμ.apply_halfTurnLoop_two_mul] at h
  omega

/-- A family satisfying the axioms agrees with the Maslov index on every loop. -/
theorem apply_eq_maslovIndex {n : ℕ} {Λ : ℒ (Fin n)} (γ : Path Λ Λ) :
    μ n Λ γ = maslovIndex γ := by
  cases n with
  | zero =>
    -- `ρ` is constant on `ℒ(0)`, so every loop has index zero.
    have h : maslovIndex γ = 0 := by
      rw [maslovIndex_def, Circle.degree_congr _ (Path.refl (maslovPhase Λ)) fun t ↦ ?_,
        Circle.degree_refl]
      simp [maslovPhase_def, Subsingleton.elim (souriau (γ t)) (souriau Λ)]
    rw [h, ← hμ.refl Λ]
    exact hμ.eq_of_maslovIndex_eq (by rw [h, maslovIndex_refl])
  | succ n =>
    rw [(hμ.homotopicWith_iff _ _).1 (homotopicWith_reindex_sum_halfTurnLoop γ), hμ.sum, hμ.refl,
      hμ.apply_halfTurnLoop, zero_add]

end IsLagrangianMaslovIndex

/-- The Maslov index `maslovIndex` of loops of Lagrangian subspaces satisfies the four axioms of
`IsLagrangianMaslovIndex`. -/
theorem isLagrangianMaslovIndex_maslovIndex :
    IsLagrangianMaslovIndex fun _ _ γ ↦ maslovIndex γ :=
  ⟨homotopicWith_iff_maslovIndex_eq, maslovIndex_smul,
    fun γ γ' ↦ by rw [maslovIndex_reindex, maslovIndex_sum], maslovIndex_refl⟩

/-- **The Maslov index of loops of Lagrangian subspaces.** A family `μ n` of integer-valued
functions on loops in `ℒ(n) = ℒ (Fin n)`, one for each `n`, satisfies the four axioms of
`IsLagrangianMaslovIndex` if and only if it is `γ ↦ deg(ρ ∘ γ)`, the
degree of the circle loop `t ↦ ρ(γ t)`, where `ρ = maslovPhase` is `det (U²)` for any unitary
frame `U` of the Lagrangian (`maslovPhase_unitaryFrame`). So such a family exists, is unique, and
is `maslovIndex`; and it has the normalization that the half-turn `t ↦ e^{iπt} ℝ` in `ℒ(1)` has
index `1`.

Milestone: *Maslov index for loops of Lagrangian subspaces*. -/
theorem isLagrangianMaslovIndex_iff_and_maslovIndex_halfTurnLoop :
    (∀ μ : (n : ℕ) → (Λ : ℒ (Fin n)) → Path Λ Λ → ℤ,
      IsLagrangianMaslovIndex μ ↔ μ = fun _ _ γ ↦ Circle.degree (γ.map continuous_maslovPhase)) ∧
      maslovIndex (halfTurnLoop (ι := Fin 1) 1) = 1 := by
  refine ⟨fun μ ↦ ⟨fun hμ ↦ funext fun n ↦ funext fun Λ ↦ funext fun γ ↦
    (hμ.apply_eq_maslovIndex γ).trans (maslovIndex_def γ), ?_⟩, by simp⟩
  rintro rfl
  simpa only [maslovIndex_def] using isLagrangianMaslovIndex_maslovIndex

end SymplecticGeometry

end
