/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Topology.Grassmannian.Lagrangian.Fibration
public import SymplecticGeometry.Topology.Grassmannian.Lagrangian.Sum
public import TauCeti.Analysis.Matrix.UnitaryGroup.Maslov.Loop

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
  `ρ : ℒ(n) → S¹` of McDuff–Salamon; on a unitary frame it is `(det U)²`.
* `SymplecticGeometry.LagrangianGrassmannian.maslovIndex γ`, for a loop `γ : Path Λ Λ`, the degree
  of the circle loop `t ↦ ρ (γ t)`.
* `SymplecticGeometry.LagrangianGrassmannian.halfTurnLoop k`, the loop
  `t ↦ e^{iπkt} • {y = 0}`, `0 ≤ t ≤ 1`.

## Main results

* Invariance of the index under free homotopies of loops (`maslovIndex_eq_of_homotopy`), its
  behaviour under constant loops, concatenation, reversal and relabelling of coordinates, and on
  loops of unitary frames (`maslovIndex_map_unitaryFrame`): all read off `Circle.degree`.
* `maslovIndex_eq_totallyRealLoop_maslovIndex`: for every lift of a loop to a path of unitary
  frames, the index is Tau Ceti's index `TauCeti.TotallyRealLoop.maslovIndex` of the corresponding
  loop of totally real subspaces of `ℂⁿ`; such a lift exists since `unitaryFrame` is a fibration
  (`exists_realImageLoop_maslovIndex_eq`).
* `maslovIndex_sum`: the index of a direct sum of loops is the sum of the indices.
* `maslovIndex_eq_sub_div_pi`: if `det (X + i Y)(t) = e^{i α(t)}` along a path of unitary frames
  of the loop, with `α` continuous, the index is `(α 1 - α 0) / π`.
* `maslovIndex_halfTurnLoop`: the loop `halfTurnLoop k` has index `k n`; for `n = 1`, `k = 1`
  this is the normalization of the index.

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
    ((⟨maslovPhase, continuous_maslovPhase⟩ : C(ℒ ι, Circle)).comp F)
    (fun t ↦ by simp [h₀]) (fun t ↦ by simp [h₁]) (fun s ↦ by simp [hF])

/-- Loops that are homotopic relative to their base point have the same Maslov index. -/
theorem maslovIndex_eq_of_homotopic {Λ : ℒ ι} {γ₀ γ₁ : Path Λ Λ} (h : γ₀.Homotopic γ₁) :
    maslovIndex γ₀ = maslovIndex γ₁ :=
  Circle.degree_eq_of_homotopic (h.map ⟨maslovPhase, continuous_maslovPhase⟩)

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

/-- **The index as the angle of a frame.** Let `δ` be a path of unitary frames of a loop `γ`, and
`det (δ t) = e^{i α(t)}` with `α` continuous. Then the Maslov index of `γ` is
`(α 1 - α 0) / π`. -/
theorem maslovIndex_eq_sub_div_pi {Λ : ℒ ι} (γ : Path Λ Λ) {U V : unitaryGroup ι ℂ}
    (δ : Path U V) (hδ : ∀ t, unitaryFrame (δ t) = γ t) {α : I → ℝ} (hα : Continuous α)
    (h : ∀ t, (δ t : Matrix ι ι ℂ).det = Complex.exp (α t * Complex.I)) :
    (maslovIndex γ : ℝ) = (α 1 - α 0) / Real.pi := by
  have hsub := Circle.sub_eq_degree_mul (γ.map continuous_maslovPhase)
    (θ := fun t ↦ 2 * α t) (continuous_const.mul hα) fun t ↦ Circle.ext <| by
      rw [Path.map_coe, Function.comp_apply, ← hδ t, maslovPhase_unitaryFrame, Circle.coe_pow,
        coe_detCircle, h t, Circle.coe_exp, ← Complex.exp_natCast_mul]
      push_cast
      ring_nf
  rw [maslovIndex_def, eq_div_iff Real.pi_ne_zero]
  linarith

/-! ### Half-turns -/

/-- The loop `t ↦ e^{iπkt} • {y = 0}`, `0 ≤ t ≤ 1`, of Lagrangian subspaces, turning the
horizontal Lagrangian through `k` half-turns; it closes up since `e^{iπk} = ±1`. -/
noncomputable def halfTurnLoop (k : ℤ) : Path (horizontal ι) (horizontal ι) where
  toFun t := unitaryFrame ⟨(Circle.exp (Real.pi * k * t) : ℂ) • (1 : Matrix ι ι ℂ),
    Unitary.smul_mem_of_mem (Circle.exp _).coe_mem_unitary (one_mem _)⟩
  continuous_toFun := continuous_unitaryFrame.comp (Continuous.subtype_mk (by fun_prop) _)
  source' := by
    rw [← unitaryFrame_one]
    congr 1
    exact Subtype.ext (by simp)
  target' := by
    rw [← unitaryFrame_one, unitaryFrame_eq_unitaryFrame_iff_souriau_eq]
    refine Subtype.ext ?_
    have h : Complex.exp (Real.pi * k * Complex.I) * Complex.exp (Real.pi * k * Complex.I) = 1 := by
      rw [← Complex.exp_add, show (Real.pi : ℂ) * k * Complex.I + Real.pi * k * Complex.I =
        k * (2 * Real.pi * Complex.I) by ring, Complex.exp_int_mul_two_pi_mul_I]
    simp [smul_smul, h]

/-- The loop `halfTurnLoop k` at time `t` is the Lagrangian framed by `e^{iπkt} I`. -/
theorem halfTurnLoop_apply (k : ℤ) (t : I) :
    halfTurnLoop k t = unitaryFrame ⟨(Circle.exp (Real.pi * k * t) : ℂ) • (1 : Matrix ι ι ℂ),
      Unitary.smul_mem_of_mem (Circle.exp _).coe_mem_unitary (one_mem _)⟩ :=
  (rfl)

/-- The Maslov phase of `halfTurnLoop k` at time `t` is `e^{2iπnkt}`, where `n` is the
cardinality of `ι`. -/
@[simp]
theorem maslovPhase_halfTurnLoop (k : ℤ) (t : I) :
    maslovPhase (halfTurnLoop (ι := ι) k t) =
      Circle.exp (2 * Fintype.card ι * (Real.pi * k * t)) := by
  refine Circle.ext ?_
  rw [halfTurnLoop_apply, maslovPhase_unitaryFrame, Circle.coe_pow, coe_detCircle, det_smul,
    det_one, mul_one, ← pow_mul, Circle.coe_exp, Circle.coe_exp, ← Complex.exp_natCast_mul]
  push_cast
  ring_nf

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
