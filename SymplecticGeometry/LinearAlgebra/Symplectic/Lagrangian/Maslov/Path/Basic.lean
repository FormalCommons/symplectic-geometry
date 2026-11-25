/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Subpath
public import SymplecticGeometry.LinearAlgebra.Symplectic.Lagrangian.Maslov.Basic
public import TauCeti.Analysis.Matrix.UnitaryGroup.Maslov.Localization
public import TauCeti.Analysis.Matrix.UnitaryGroup.Maslov.Multiplicity
public import TauCeti.LinearAlgebra.TotallyReal.Maslov.Transverse

/-!
# The Maslov index of paths of Lagrangian subspaces

Write `ℒ ι` for the space of Lagrangian subspaces of the standard model `(StdSpace ι, ω₀)`, and
`unitaryFrame U = U • {y = 0}` for the Lagrangian framed by a unitary matrix `U = X + i Y`. This
file defines the Robbin–Salamon index `μ(γ, V)` of a path `γ` in `ℒ ι` relative to a Lagrangian
`V`, for every continuous path, and proves the properties that follow from its formula or from
Tau Ceti's index of paths of unitary frames.

## Main definitions

* `SymplecticGeometry.LagrangianGrassmannian.pathMaslovIndex γ V : ℝ`: move `V` to `{y = 0}` by a
  unitary matrix and the path with it, then take Souriau's spectral formula: the angle swept by
  the Maslov phase `ρ` along the path, divided by `2π`, minus the change of the spectral angle sum
  `Matrix.spectralAngleSum` of the Souriau map between the endpoints.

## Main results

* `pathMaslovIndex_eq_of_unitaryFrame_eq`: the index does not depend on the unitary matrix
  chosen, since the matrices that fix `{y = 0}` are real orthogonal and leave Souriau's formula
  unchanged.
* `pathMaslovIndex_map_unitaryFrame`: on the path framed by a path `δ` of unitary matrices, the
  index relative to `{y = 0}` is Tau Ceti's `Matrix.UnitaryGroup.maslovIndex δ`; every path has
  such a frame (`exists_maslovIndex_eq_pathMaslovIndex`), since `unitaryFrame` is a fibration.
* Homotopy invariance with fixed endpoints (`pathMaslovIndex_eq_of_homotopic`), catenation
  (`pathMaslovIndex_trans`, `pathMaslovIndex_eq_subpath_add`), reversal
  (`pathMaslovIndex_symm`) and constant paths (`pathMaslovIndex_refl`).
* The product property (`pathMaslovIndex_sum`), the zero axiom
  (`pathMaslovIndex_eq_zero_of_finrank_eq`) and localization for paths of graphs
  (`pathMaslovIndex_graph`), transferred from Tau Ceti through frames.
* `pathMaslovIndex_eq_transverseMaslovIndex`: on paths whose ends are transverse to `{y = 0}`, the
  index is Tau Ceti's `TauCeti.TotallyRealPath.transverseMaslovIndex`.
* `pathMaslovIndex_eq_maslovIndex` and `pathMaslovIndex_eq_sub_div_pi`: on a loop, the index
  relative to any Lagrangian is the Maslov index of the loop, `(α 1 - α 0) / π` for
  `det (X + i Y)(t) = e^{i α(t)}`.

The independence of the frame is transferred from Tau Ceti's
`Matrix.UnitaryGroup.maslovIndex_map_mul_left` through a lift to unitary frames. Homotopy
invariance, catenation, reversal and constant paths adapt the proofs of
`Matrix.UnitaryGroup.maslovIndex_eq_of_homotopic`,
`Matrix.UnitaryGroup.maslovIndex_trans`, `Matrix.UnitaryGroup.maslovIndex_symm` and
`Matrix.UnitaryGroup.maslovIndex_refl`, read on `ℒ ι` instead of on frames.

## References

* [J. Robbin, D. Salamon, *The Maslov index for paths*][RobbinSalamon1993], §2 (Theorem 2.3 and
  Remark 2.6).
* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.3.
-/

public section

namespace SymplecticGeometry

open Matrix TauCeti
open scoped unitInterval

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

local notation "ℒ" ι => LagrangianGrassmannian (stdForm ι)

namespace LagrangianGrassmannian

/-! ### Souriau's formula on the Lagrangian Grassmannian -/

/-- Souriau's formula `θ / (2π) - (s(W(Λ₁)) - s(W(Λ₀)))` for a path `η` from `Λ₀` to `Λ₁`, where
`θ` is the angle swept by its Maslov phase, `W` the Souriau map and `s` the spectral angle sum.
It is the index relative to `{y = 0}` (`pathMaslovIndex_horizontal`). -/
private noncomputable def souriauIndex {Λ Λ' : ℒ ι} (η : Path Λ Λ') : ℝ :=
  Circle.angleChange (η.map continuous_maslovPhase) / (2 * Real.pi) -
    (spectralAngleSum (souriau Λ' : Matrix ι ι ℂ) - spectralAngleSum (souriau Λ : Matrix ι ι ℂ))

private theorem souriauIndex_congr {Λ₀ Λ₁ Λ₀' Λ₁' : ℒ ι} (η : Path Λ₀ Λ₁) (η' : Path Λ₀' Λ₁')
    (h : ∀ t, η t = η' t) : souriauIndex η = souriauIndex η' := by
  obtain rfl : Λ₀ = Λ₀' := by simpa using h 0
  obtain rfl : Λ₁ = Λ₁' := by simpa using h 1
  obtain rfl : η = η' := Path.ext (funext h)
  rfl

/-- For a path `δ` of unitary frames, Souriau's formula on the path of Lagrangians it frames is
Tau Ceti's index `Matrix.UnitaryGroup.maslovIndex δ`. -/
private theorem souriauIndex_map_unitaryFrame {U U' : unitaryGroup ι ℂ} (δ : Path U U') :
    souriauIndex (δ.map continuous_unitaryFrame) = UnitaryGroup.maslovIndex δ := by
  rw [souriauIndex, UnitaryGroup.maslovIndex_def, souriau_unitaryFrame, souriau_unitaryFrame,
    Circle.angleChange_congr _ (UnitaryGroup.detSouriauPath δ) fun t ↦ by
      simp [maslovPhase_def]]

/-- Souriau's formula is invariant under real orthogonal matrices. -/
private theorem souriauIndex_map_smul_of_mem_realSubgroup {O : unitaryGroup ι ℂ}
    (hO : O ∈ UnitaryGroup.realSubgroup ι) {Λ Λ' : ℒ ι} (η : Path Λ Λ') :
    souriauIndex (η.map (continuous_const_smul O)) = souriauIndex η := by
  obtain ⟨_, δ, hδ⟩ := exists_path_lift_unitaryFrame η (unitaryFrame_surjective Λ).choose_spec
  rw [souriauIndex_congr η (δ.map continuous_unitaryFrame) fun t ↦ (hδ t).symm,
    souriauIndex_map_unitaryFrame, ← UnitaryGroup.maslovIndex_map_mul_left O
      (mul_eq_one_comm.1 (UnitaryGroup.mem_realSubgroup_iff_transpose_mul_self_eq_one.1 hO)) δ,
    ← souriauIndex_map_unitaryFrame]
  exact souriauIndex_congr _ _ fun t ↦ by simp [unitaryFrame_mul, hδ]

/-! ### The definition -/

/-- The **Maslov index** `μ(γ, V)` of a path `γ` of Lagrangian subspaces relative to a Lagrangian
`V`, in the sense of Robbin and Salamon. Choose a unitary matrix `U` with `U • {y = 0} = V` and
move the path by `U⁻¹`, to the path `γ'` from `Λ₀` to `Λ₁`; then `μ(γ, V)` is Souriau's formula
`θ / (2π) - (s(W(Λ₁)) - s(W(Λ₀)))`, where `θ` is the angle swept by the Maslov phase
`t ↦ ρ(γ' t)`, `W` is the Souriau map and `s` the spectral angle sum
`Matrix.spectralAngleSum`. It does not depend on the choice of `U`
(`pathMaslovIndex_eq_of_unitaryFrame_eq`). -/
noncomputable def pathMaslovIndex {Λ Λ' : ℒ ι} (γ : Path Λ Λ') (V : ℒ ι) : ℝ :=
  souriauIndex (γ.map (continuous_const_smul (unitaryFrame_surjective V).choose⁻¹))

theorem pathMaslovIndex_def {Λ Λ' : ℒ ι} (γ : Path Λ Λ') (V : ℒ ι) :
    pathMaslovIndex γ V =
      Circle.angleChange ((γ.map (continuous_const_smul (unitaryFrame_surjective V).choose⁻¹)).map
          continuous_maslovPhase) / (2 * Real.pi) -
        (spectralAngleSum (souriau ((unitaryFrame_surjective V).choose⁻¹ • Λ') : Matrix ι ι ℂ) -
          spectralAngleSum (souriau ((unitaryFrame_surjective V).choose⁻¹ • Λ) : Matrix ι ι ℂ)) :=
  (rfl)

private theorem pathMaslovIndex_eq_souriauIndex {Λ Λ' : ℒ ι} (γ : Path Λ Λ') {V : ℒ ι}
    {U : unitaryGroup ι ℂ} (hU : unitaryFrame U = V) :
    pathMaslovIndex γ V = souriauIndex (γ.map (continuous_const_smul U⁻¹)) := by
  obtain ⟨U₀, hU₀⟩ : ∃ U₀, U₀ = (unitaryFrame_surjective V).choose := ⟨_, rfl⟩
  have hO : U₀⁻¹ * U ∈ UnitaryGroup.realSubgroup ι := unitaryFrame_eq_unitaryFrame_iff.1 <| by
    rw [hU₀, (unitaryFrame_surjective V).choose_spec, hU]
  calc pathMaslovIndex γ V = souriauIndex (γ.map (continuous_const_smul U₀⁻¹)) :=
        souriauIndex_congr _ _ fun t ↦ by simp [hU₀]
    _ = souriauIndex ((γ.map (continuous_const_smul U₀⁻¹)).map
          (continuous_const_smul (U₀⁻¹ * U)⁻¹)) :=
        (souriauIndex_map_smul_of_mem_realSubgroup (inv_mem hO) _).symm
    _ = souriauIndex (γ.map (continuous_const_smul U⁻¹)) :=
        souriauIndex_congr _ _ fun t ↦ by simp [smul_smul]

/-- **Independence of the frame.** The Maslov index relative to `V` is Souriau's formula for the
path moved by `U⁻¹`, for any unitary matrix `U` with `U • {y = 0} = V`. -/
theorem pathMaslovIndex_eq_of_unitaryFrame_eq {Λ Λ' : ℒ ι} (γ : Path Λ Λ') {V : ℒ ι}
    {U : unitaryGroup ι ℂ} (hU : unitaryFrame U = V) :
    pathMaslovIndex γ V =
      Circle.angleChange ((γ.map (continuous_const_smul U⁻¹)).map continuous_maslovPhase) /
          (2 * Real.pi) -
        (spectralAngleSum (souriau (U⁻¹ • Λ') : Matrix ι ι ℂ) -
          spectralAngleSum (souriau (U⁻¹ • Λ) : Matrix ι ι ℂ)) := by
  rw [pathMaslovIndex_eq_souriauIndex γ hU, souriauIndex]

private theorem pathMaslovIndex_horizontal_eq_souriauIndex {Λ Λ' : ℒ ι} (γ : Path Λ Λ') :
    pathMaslovIndex γ (horizontal ι) = souriauIndex γ :=
  (pathMaslovIndex_eq_souriauIndex γ unitaryFrame_one).trans
    (souriauIndex_congr _ _ fun t ↦ by simp)

/-- The Maslov index relative to the horizontal Lagrangian `{y = 0}` is Souriau's formula for the
path itself. -/
theorem pathMaslovIndex_horizontal {Λ Λ' : ℒ ι} (γ : Path Λ Λ') :
    pathMaslovIndex γ (horizontal ι) =
      Circle.angleChange (γ.map continuous_maslovPhase) / (2 * Real.pi) -
        (spectralAngleSum (souriau Λ' : Matrix ι ι ℂ) -
          spectralAngleSum (souriau Λ : Matrix ι ι ℂ)) := by
  rw [pathMaslovIndex_horizontal_eq_souriauIndex, souriauIndex]

/-- Moving the reference Lagrangian `U • {y = 0}` to `{y = 0}`: the index relative to
`unitaryFrame U` is the index of the path moved by `U⁻¹` relative to `{y = 0}`. -/
theorem pathMaslovIndex_unitaryFrame {Λ Λ' : ℒ ι} (γ : Path Λ Λ') (U : unitaryGroup ι ℂ) :
    pathMaslovIndex γ (unitaryFrame U) =
      pathMaslovIndex (γ.map (continuous_const_smul U⁻¹)) (horizontal ι) := by
  rw [pathMaslovIndex_eq_souriauIndex γ rfl, pathMaslovIndex_horizontal_eq_souriauIndex]

/-- Two paths of Lagrangians with the same values have the same index. -/
theorem pathMaslovIndex_congr {Λ₀ Λ₁ Λ₀' Λ₁' : ℒ ι} (γ : Path Λ₀ Λ₁) (γ' : Path Λ₀' Λ₁')
    (h : ∀ t, γ t = γ' t) (V : ℒ ι) : pathMaslovIndex γ V = pathMaslovIndex γ' V :=
  souriauIndex_congr _ _ fun t ↦ by simp [h]

/-! ### The bridge to Tau Ceti's index of paths of unitary frames -/

/-- **The bridge to Tau Ceti.** The index, relative to `{y = 0}`, of the path of Lagrangians framed
by a path `δ` of unitary matrices is Tau Ceti's Souriau index `Matrix.UnitaryGroup.maslovIndex δ`
of `δ`, relative to `ℝⁿ ⊆ ℂⁿ`. -/
theorem pathMaslovIndex_map_unitaryFrame {U U' : unitaryGroup ι ℂ} (δ : Path U U') :
    pathMaslovIndex (δ.map continuous_unitaryFrame) (horizontal ι) =
      UnitaryGroup.maslovIndex δ := by
  rw [pathMaslovIndex_horizontal_eq_souriauIndex, souriauIndex_map_unitaryFrame]

/-- If `δ` is a path of unitary frames of `γ`, so that `unitaryFrame (δ t) = γ t`, then the index of
`γ` relative to `unitaryFrame W` is Tau Ceti's index of the path of frames `t ↦ W⁻¹ δ t`. -/
theorem pathMaslovIndex_unitaryFrame_eq_maslovIndex {Λ Λ' : ℒ ι} (γ : Path Λ Λ')
    {U U' : unitaryGroup ι ℂ} (δ : Path U U') (hδ : ∀ t, unitaryFrame (δ t) = γ t)
    (W : unitaryGroup ι ℂ) :
    pathMaslovIndex γ (unitaryFrame W) =
      UnitaryGroup.maslovIndex (δ.map (continuous_const_mul W⁻¹)) := by
  rw [pathMaslovIndex_eq_souriauIndex γ rfl, ← souriauIndex_map_unitaryFrame]
  exact souriauIndex_congr _ _ fun t ↦ by simp [unitaryFrame_mul, hδ]

/-- If `δ` is a path of unitary frames of `γ`, the index of `γ` relative to `{y = 0}` is Tau Ceti's
index of `δ`. -/
theorem pathMaslovIndex_horizontal_eq_maslovIndex {Λ Λ' : ℒ ι} (γ : Path Λ Λ')
    {U U' : unitaryGroup ι ℂ} (δ : Path U U') (hδ : ∀ t, unitaryFrame (δ t) = γ t) :
    pathMaslovIndex γ (horizontal ι) = UnitaryGroup.maslovIndex δ := by
  rw [← pathMaslovIndex_map_unitaryFrame]
  exact pathMaslovIndex_congr _ _ (fun t ↦ (hδ t).symm) _

/-- Every path of Lagrangians lifts to a path `δ` of unitary frames, and its index relative to
`{y = 0}` is Tau Ceti's index of `δ`. -/
theorem exists_maslovIndex_eq_pathMaslovIndex {Λ Λ' : ℒ ι} (γ : Path Λ Λ') :
    ∃ (U U' : unitaryGroup ι ℂ) (δ : Path U U'), (∀ t, unitaryFrame (δ t) = γ t) ∧
      UnitaryGroup.maslovIndex δ = pathMaslovIndex γ (horizontal ι) := by
  obtain ⟨U, hU⟩ := unitaryFrame_surjective Λ
  obtain ⟨U', δ, hδ⟩ := exists_path_lift_unitaryFrame γ hU
  exact ⟨U, U', δ, hδ, (pathMaslovIndex_horizontal_eq_maslovIndex γ δ hδ).symm⟩

/-! ### Properties read off the formula -/

/-- **Homotopy invariance.** A homotopy of paths that keeps both ends fixed does not change the
index, whatever the reference Lagrangian. -/
theorem pathMaslovIndex_eq_of_homotopic {Λ Λ' : ℒ ι} {γ₀ γ₁ : Path Λ Λ'} (h : γ₀.Homotopic γ₁)
    (V : ℒ ι) : pathMaslovIndex γ₀ V = pathMaslovIndex γ₁ V := by
  rw [pathMaslovIndex_def, pathMaslovIndex_def, Circle.angleChange_eq_of_homotopic
    (homotopic_map_maslovPhase (h.map ⟨_, continuous_const_smul _⟩))]

/-- **Catenation.** The index is additive under concatenation of paths. -/
@[simp]
theorem pathMaslovIndex_trans {Λ₀ Λ₁ Λ₂ : ℒ ι} (γ₁ : Path Λ₀ Λ₁) (γ₂ : Path Λ₁ Λ₂) (V : ℒ ι) :
    pathMaslovIndex (γ₁.trans γ₂) V = pathMaslovIndex γ₁ V + pathMaslovIndex γ₂ V := by
  simp only [pathMaslovIndex, souriauIndex, Path.map_trans, Circle.angleChange_trans]
  ring

/-- **Reversal.** Reversing a path negates its index. -/
@[simp]
theorem pathMaslovIndex_symm {Λ Λ' : ℒ ι} (γ : Path Λ Λ') (V : ℒ ι) :
    pathMaslovIndex γ.symm V = -pathMaslovIndex γ V := by
  simp only [pathMaslovIndex, souriauIndex, ← Path.map_symm, Circle.angleChange_symm]
  ring

/-- A constant path has index zero. -/
@[simp]
theorem pathMaslovIndex_refl (Λ V : ℒ ι) : pathMaslovIndex (Path.refl Λ) V = 0 := by
  rw [pathMaslovIndex, souriauIndex, Circle.angleChange_congr _
    (Path.refl (maslovPhase ((unitaryFrame_surjective V).choose⁻¹ • Λ))) fun t ↦ by simp,
    Circle.angleChange_refl]
  simp

/-- **Catenation at a point.** Splitting a path at a time `c` splits its index. -/
theorem pathMaslovIndex_eq_subpath_add {Λ Λ' : ℒ ι} (γ : Path Λ Λ') (c : I) (V : ℒ ι) :
    pathMaslovIndex γ V =
      pathMaslovIndex (γ.subpath 0 c) V + pathMaslovIndex (γ.subpath c 1) V := by
  rw [← pathMaslovIndex_trans, pathMaslovIndex_eq_of_homotopic
    (Path.Homotopic.subpath_trans_subpath γ 0 c 1), Path.subpath_zero_one]
  exact pathMaslovIndex_congr _ _ (fun t ↦ by simp) V

/-- **Loops.** On a loop, the index relative to any Lagrangian is the Maslov index of the
loop. -/
theorem pathMaslovIndex_eq_maslovIndex {Λ : ℒ ι} (γ : Path Λ Λ) (V : ℒ ι) :
    pathMaslovIndex γ V = maslovIndex γ := by
  obtain ⟨W, rfl⟩ := unitaryFrame_surjective V
  rw [pathMaslovIndex_eq_souriauIndex γ rfl, souriauIndex, sub_self, sub_zero,
    Circle.angleChange_eq_degree_mul, maslovIndex_def,
    Circle.degree_congr _ ((Path.refl (UnitaryGroup.detCircle W⁻¹ ^ 2)).mul
      (γ.map continuous_maslovPhase)) fun t ↦ by
      rw [Path.map_coe, Function.comp_apply, Path.map_coe, Function.comp_apply,
        maslovPhase_unitary_smul, Path.mul_apply, Path.refl_apply,
        Path.map_coe, Function.comp_apply],
    Circle.degree_mul, Circle.degree_refl, zero_add]
  field_simp

/-- **Loops, through frames.** If `δ` is a path of unitary frames of a loop `γ` and
`det (δ t) = e^{i α(t)}` with `α` continuous, then the index of `γ` relative to any Lagrangian is
`(α 1 - α 0) / π`. -/
theorem pathMaslovIndex_eq_sub_div_pi {Λ : ℒ ι} (γ : Path Λ Λ) (V : ℒ ι)
    {U U' : unitaryGroup ι ℂ} (δ : Path U U') (hδ : ∀ t, unitaryFrame (δ t) = γ t) {α : I → ℝ}
    (hα : Continuous α) (h : ∀ t, (δ t : Matrix ι ι ℂ).det = Complex.exp (α t * Complex.I)) :
    pathMaslovIndex γ V = (α 1 - α 0) / Real.pi := by
  rw [pathMaslovIndex_eq_maslovIndex, maslovIndex_eq_sub_div_pi γ δ hδ hα h]

/-! ### Properties transferred from Tau Ceti -/

/-- **The direct-sum property.** The index of the direct sum `t ↦ γ t ⊕ γ' t` of two paths,
relative to the direct sum `V ⊕ V'`, is the sum of their indices. -/
theorem pathMaslovIndex_sum {Λ₀ Λ₁ : ℒ ι} {Λ₀' Λ₁' : ℒ κ} (γ : Path Λ₀ Λ₁) (γ' : Path Λ₀' Λ₁')
    (V : ℒ ι) (V' : ℒ κ) :
    pathMaslovIndex ((γ.prod γ').map continuous_sum) (sum (V, V')) =
      pathMaslovIndex γ V + pathMaslovIndex γ' V' := by
  obtain ⟨W, rfl⟩ := unitaryFrame_surjective V
  obtain ⟨W', rfl⟩ := unitaryFrame_surjective V'
  obtain ⟨_, δ, hδ⟩ := exists_path_lift_unitaryFrame γ (unitaryFrame_surjective _).choose_spec
  obtain ⟨_, δ', hδ'⟩ := exists_path_lift_unitaryFrame γ' (unitaryFrame_surjective _).choose_spec
  rw [pathMaslovIndex_unitaryFrame_eq_maslovIndex γ δ hδ,
    pathMaslovIndex_unitaryFrame_eq_maslovIndex γ' δ' hδ', sum_unitaryFrame,
    pathMaslovIndex_unitaryFrame_eq_maslovIndex _ ((δ.prod δ').map UnitaryGroup.continuous_sum)
      (fun t ↦ by simp [← sum_unitaryFrame, hδ, hδ']),
    ← UnitaryGroup.maslovIndex_sum]
  exact UnitaryGroup.maslovIndex_eq_of_souriau_eq _ _ fun t ↦ by
    rw [Path.map_coe, Function.comp_apply, Path.map_coe, Function.comp_apply, ← map_inv, ← map_mul]
    simp

/-- **The zero axiom.** If the intersections `γ t ∩ V` all have the same dimension, the index of
`γ` relative to `V` is zero. -/
theorem pathMaslovIndex_eq_zero_of_finrank_eq {Λ Λ' : ℒ ι} (γ : Path Λ Λ') (V : ℒ ι) {k : ℕ}
    (h : ∀ t, Module.finrank ℝ
      ↥((γ t : Submodule ℝ (StdSpace ι)) ⊓ (V : Submodule ℝ (StdSpace ι))) = k) :
    pathMaslovIndex γ V = 0 := by
  obtain ⟨W, rfl⟩ := unitaryFrame_surjective V
  obtain ⟨_, δ, hδ⟩ := exists_path_lift_unitaryFrame γ (unitaryFrame_surjective _).choose_spec
  rw [pathMaslovIndex_unitaryFrame_eq_maslovIndex γ δ hδ]
  refine UnitaryGroup.maslovIndex_eq_zero_of_finrank_eq _ (k := k) fun t ↦ ?_
  rw [← finrank_unitaryFrame_inf_horizontal, Path.map_coe, Function.comp_apply,
    unitaryFrame_mul, hδ, ← finrank_inf_unitaryFrame, h]

/-- Let `γ` be a path of Lagrangians that are the graphs `{(x, A t x)}` of real matrices `A t`.
Then `γ` is framed by a path `δ` of unitary matrices whose
Souriau maps `souriau (δ t)` are the Cayley transforms of the `A t`, and the index of `γ`
relative to `{y = 0}` is Tau Ceti's index of `δ`. -/
theorem exists_souriau_eq_cayley_and_pathMaslovIndex_eq_maslovIndex {Λ Λ' : ℒ ι} (γ : Path Λ Λ')
    {A : I → Matrix ι ι ℝ} (hγ : ∀ t, (γ t : Submodule ℝ (StdSpace ι)) = StdSpace.graph (A t)) :
    ∃ (U U' : unitaryGroup ι ℂ) (δ : Path U U'),
      (∀ t, (UnitaryGroup.souriau (δ t) : Matrix ι ι ℂ) = cayley ((A t).map ((↑) : ℝ → ℂ))) ∧
        pathMaslovIndex γ (horizontal ι) = UnitaryGroup.maslovIndex δ := by
  have hAc : Continuous A := continuous_of_coe_eq_graph γ.continuous hγ
  obtain ⟨U, U', δ, hδ⟩ := UnitaryGroup.exists_path_realImage_eq_and_souriau_eq_cayley hAc
    fun t ↦ isHermitian_of_coe_eq_graph (hγ t)
  refine ⟨U, U', δ, fun t ↦ (hδ t).2, pathMaslovIndex_horizontal_eq_maslovIndex γ δ fun t ↦ ?_⟩
  rw [← toSubmodule_inj, coe_unitaryFrame_eq_map, (hδ t).1, hγ,
    ← StdSpace.range_toEuclideanLin_fromRows_one_eq_graph,
    StdSpace.range_toEuclideanLin_fromRows_eq_map_realImage, Matrix.map_ofReal_one]

/-- **Localization.** Let `γ` be a path of Lagrangians that are the graphs `{(x, A t x)}` of real
matrices `A t`; then `t ↦ A t` is continuous and each `A t` is symmetric. The index of `γ`
relative to `{y = 0}` is half the change of the signature of `A`. -/
theorem pathMaslovIndex_graph {Λ Λ' : ℒ ι} (γ : Path Λ Λ') {A : I → Matrix ι ι ℝ}
    (hγ : ∀ t, (γ t : Submodule ℝ (StdSpace ι)) = StdSpace.graph (A t)) :
    pathMaslovIndex γ (horizontal ι) = ((A 1).signature - (A 0).signature : ℝ) / 2 := by
  obtain ⟨_, _, δ, hδ, h⟩ := exists_souriau_eq_cayley_and_pathMaslovIndex_eq_maslovIndex γ hγ
  rw [h]
  exact UnitaryGroup.maslovIndex_eq_signature_sub_of_souriau_eq_cayley δ
    (continuous_of_coe_eq_graph γ.continuous hγ) (fun t ↦ isHermitian_of_coe_eq_graph (hγ t)) hδ

/-- **Comparison with Tau Ceti's transverse index.** Let `δ` be a path of unitary frames whose
Lagrangians `δ t ℝⁿ ⊆ ℂⁿ` begin and end at chart subspaces `{S y + i y}` of symmetric matrices
`S₀`, `S₁`, which are transverse to `ℝⁿ`. Then the index, relative to `{y = 0}`, of the path of
Lagrangians framed by `δ` is Tau Ceti's index
`TauCeti.TotallyRealPath.transverseMaslovIndex` of `t ↦ δ t ℝⁿ`. -/
theorem pathMaslovIndex_eq_transverseMaslovIndex {U U' : unitaryGroup ι ℂ} (δ : Path U U')
    {S₀ S₁ : Matrix ι ι ℝ} (hS₀ : S₀.IsSymm) (hS₁ : S₁.IsSymm)
    (h₀ : UnitaryGroup.realImagePath δ 0 = S₀.lagrangianChart)
    (h₁ : UnitaryGroup.realImagePath δ 1 = S₁.lagrangianChart) :
    pathMaslovIndex (δ.map continuous_unitaryFrame) (horizontal ι) =
      (UnitaryGroup.realImagePath δ).transverseMaslovIndex hS₀ hS₁ h₀ h₁ := by
  have hS := isSymm_segment hS₀ hS₁
  let S (t : I) : selfAdjoint (Matrix ι ι ℝ) :=
    ⟨Path.segment S₀ S₁ t, isHermitian_iff_isSymm.2 (hS t)⟩
  -- The path of chart points `{(S t y, y)}` along the segment from `S₀` to `S₁`, and a path of
  -- unitary frames of it.
  let P : Path (graphY (S 0)) (graphY (S 1)) :=
    ⟨⟨fun t ↦ graphY (S t), continuous_graphY.comp
      ((Path.segment S₀ S₁).continuous.subtype_mk _)⟩, rfl, rfl⟩
  obtain ⟨_, δ', hδ'⟩ := exists_path_lift_unitaryFrame P (unitaryFrame_surjective _).choose_spec
  have hδ'S (t : I) : (δ' t : Matrix ι ι ℂ).realImage = (Path.segment S₀ S₁ t).lagrangianChart := by
    have h := congrArg toSubmodule (hδ' t)
    simp only [P, Path.coe_mk_mk] at h
    rw [coe_unitaryFrame_eq_map, coe_graphY_eq_map] at h
    exact Submodule.map_injective_of_injective (StdSpace.complexEuclideanEquiv ι).injective h
  have hP : TotallyRealPath.ofLagrangianChart (Path.segment S₀ S₁) hS =
      UnitaryGroup.realImagePath δ' :=
    TotallyRealPath.ext fun t ↦ by
      rw [TotallyRealPath.ofLagrangianChart_apply, UnitaryGroup.realImagePath_apply, hδ'S]
  have hzero : UnitaryGroup.maslovIndex δ' = 0 :=
    UnitaryGroup.maslovIndex_eq_zero_of_finrank_eq δ' (k := 0) fun t ↦ by
      rw [hδ'S, lagrangianChart_inf_realSubspace, finrank_bot]
  rw [pathMaslovIndex_map_unitaryFrame, TotallyRealPath.transverseMaslovIndex_eq_relativeMaslovIndex
    _ _ hS, TotallyRealPath.relativeMaslovIndex_congr_right hP,
    UnitaryGroup.relativeMaslovIndex_realImagePath, hzero, sub_zero]

end LagrangianGrassmannian

end SymplecticGeometry

end
