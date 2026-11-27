/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.LinearAlgebra.Symplectic.Lagrangian.Maslov.Crossing.Form
public import SymplecticGeometry.LinearAlgebra.Symplectic.Lagrangian.Maslov.Path.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Matrix.Normed
public import SymplecticGeometry.Analysis.Matrix.UnitaryGroup.Basic
import SymplecticGeometry.Data.Matrix.Basis
import SymplecticGeometry.LinearAlgebra.Matrix.Realify
import TauCeti.Analysis.Matrix.ContDiff
import TauCeti.Analysis.SpecialFunctions.Trigonometric.UnitInterval
import SymplecticGeometry.Topology.Grassmannian.Lagrangian.Graph
import SymplecticGeometry.LinearAlgebra.Matrix.UnitaryGroup.Projective
import SymplecticGeometry.Analysis.Calculus.Deriv.Matrix

/-!
# Regular pieces of paths of Lagrangian subspaces

Three kinds of paths in the Lagrangian Grassmannian `ℒ ι` of `(StdSpace ι, ω₀)`, each with an
explicit frame whose derivative is known at every time, and with its crossings with a reference
Lagrangian and their crossing forms. They are the pieces out of which regular representatives of
paths are built.

## Main definitions

* The rotation `SymplecticGeometry.LagrangianGrassmannian.rotationPath Λ ε`, the path
  `s ↦ rotate (ε s) Λ` of rotations of `Λ` (defined in
  `Topology/Grassmannian/Lagrangian/Quotient.lean`), gets the frame
  `s ↦ rotationFrame Z (ε s) = e^{ε s J₀} Z` for a frame `Z` of `Λ` (`range_rotationFrame`).
* `SymplecticGeometry.LagrangianGrassmannian.coordinateRotate i θ Λ`: the image of `Λ` under the
  unitary matrix `Matrix.UnitaryGroup.detSection ι i (Circle.exp θ) = diag(1, …, e^{iθ}, …, 1)`,
  which turns the `i`-th coordinate plane; `coordinateHalfTurn i` is the loop
  `s ↦ coordinateRotate i (π s) {x = 0}`, with frame `s ↦ coordinateRotationFrame i (π s)`.

## Main results

* `lagrangianCrossingForm_smul_J_mul_apply`: the crossing form of a rotation is `u ↦ ε |Z u|²`,
  definite when `ε ≠ 0`; `eventually_rotationPath_inf_eq_bot`: for every small nonzero `ε`, the
  rotation `rotationPath Λ ε` meets a given Lagrangian `V` at most at `s = 0`.
* `exists_chartPath`: two Lagrangians transverse to `{y = 0}` are joined by a path in the chart
  `{x = S y}` of symmetric matrices `S`, with a smooth frame, that never meets `{y = 0}`.
* `coordinateHalfTurn_inf_horizontal_ne_bot_iff`: the coordinate half-turn meets `{y = 0}` only at
  `s = 1 / 2`, in a line (`finrank_comap_horizontal_coordinateRotationFrame_pi_div_two`), where its
  crossing form `u ↦ π uᵢ²` is positive definite
  (`posDef_lagrangianCrossingForm_coordinateRotationFrame_pi_div_two`); and
  `pathMaslovIndex_coordinateHalfTurn`: its index is `1`, relative to every Lagrangian.

## Implementation notes

The isolation of the crossing of a rotation is
`SymplecticGeometry.LagrangianGrassmannian.eventually_nhdsNE_not_crossing_of_regular`, applied to
the family of rotations `θ ↦ e^{θ J₀} Λ` on `ℝ` at `θ = 0`, which covers both signs of the
angle at once. The index of the coordinate half-turn comes from the
loop formula `pathMaslovIndex_eq_sub_div_pi`, with the unitary frames
`diag(1, …, e^{iπs}, …, 1) e^{iπ/2}`.

## References

* [J. Robbin, D. Salamon, *The Maslov index for paths*][RobbinSalamon1993], §2.
* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.3.
-/

public section

open Matrix Matrix.UnitaryGroup TauCeti Set Filter Topology
open scoped unitInterval

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace SymplecticGeometry

local notation "ℒ" ι => LagrangianGrassmannian (stdForm ι)

/-! ### The crossing form of a rotation -/

/-- The crossing form of a frame `Z` with derivative `ε J Z`, the derivative of the rotation
`s ↦ e^{ε s J} Z` at `s = 0`, is `u ↦ ε |Z u|²`, relative to any subspace. -/
theorem lagrangianCrossingForm_smul_J_mul_apply (Z : Matrix (ι ⊕ ι) ι ℝ) (ε : ℝ)
    (V : Submodule ℝ (StdSpace ι)) (u : V.comap (toEuclideanLin Z)) :
    lagrangianCrossingForm Z (ε • (J ι ℝ * Z)) V u =
      ε * ‖toEuclideanLin Z (u : EuclideanSpace ℝ ι)‖ ^ 2 := by
  have h := stdForm_apply_stdComplexStructure (toEuclideanLin Z (u : EuclideanSpace ℝ ι))
    (toEuclideanLin Z u)
  have hJ := LinearMap.congr_fun (stdComplexStructure_eq_toEuclideanLin_J (ι := ι))
    (toEuclideanLin Z (u : EuclideanSpace ℝ ι))
  -- `hJ` is about the linear map `(stdComplexStructure ι).toLinearMap`; `show` restates it for
  -- the coercion of `stdComplexStructure ι` itself, which `h` uses.
  rw [show stdComplexStructure ι (toEuclideanLin Z (u : EuclideanSpace ℝ ι)) =
    toEuclideanLin (J ι ℝ) (toEuclideanLin Z (u : EuclideanSpace ℝ ι)) from hJ,
    real_inner_self_eq_norm_sq] at h
  simp [toLpLin_mul_same, h]

/-- The crossing form of `Z` with derivative `ε J Z` has no nonzero isotropic vector when `Z` is
injective and `ε ≠ 0`, so it is nondegenerate (`QuadraticMap.Anisotropic.nondegenerate`). -/
theorem anisotropic_lagrangianCrossingForm_smul_J_mul {Z : Matrix (ι ⊕ ι) ι ℝ}
    (hZ : Function.Injective (toEuclideanLin Z)) {ε : ℝ} (hε : ε ≠ 0)
    (V : Submodule ℝ (StdSpace ι)) :
    (lagrangianCrossingForm Z (ε • (J ι ℝ * Z)) V).Anisotropic := by
  intro u hu
  rw [lagrangianCrossingForm_smul_J_mul_apply, mul_eq_zero, pow_eq_zero_iff two_ne_zero,
    norm_eq_zero, ← map_zero (toEuclideanLin Z)] at hu
  exact Subtype.ext (hZ (hu.resolve_left hε))

/-- For `ε > 0` and an injective `Z`, the crossing form of `Z` with derivative `ε J Z` is positive
definite. -/
theorem posDef_lagrangianCrossingForm_smul_J_mul {Z : Matrix (ι ⊕ ι) ι ℝ}
    (hZ : Function.Injective (toEuclideanLin Z)) {ε : ℝ} (hε : 0 < ε)
    (V : Submodule ℝ (StdSpace ι)) :
    (lagrangianCrossingForm Z (ε • (J ι ℝ * Z)) V).PosDef := fun u hu ↦
  lt_of_le_of_ne (by rw [lagrangianCrossingForm_smul_J_mul_apply]; positivity)
    fun h ↦ hu (anisotropic_lagrangianCrossingForm_smul_J_mul hZ hε.ne' V u h.symm)

/-! ### Frames of rotations -/

/-- The frame `e^{θ J₀} Z = (cos θ • 1 + sin θ • J) Z` of the rotated Lagrangian `rotate θ Λ`,
for a frame `Z` of `Λ` (`range_rotationFrame`). -/
noncomputable def rotationFrame (Z : Matrix (ι ⊕ ι) ι ℝ) (θ : ℝ) : Matrix (ι ⊕ ι) ι ℝ :=
  (Real.cos θ • (1 : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) + Real.sin θ • J ι ℝ) * Z

theorem rotationFrame_def (Z : Matrix (ι ⊕ ι) ι ℝ) (θ : ℝ) :
    rotationFrame Z θ = (Real.cos θ • (1 : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) + Real.sin θ • J ι ℝ) * Z :=
  (rfl)

@[simp]
theorem rotationFrame_zero (Z : Matrix (ι ⊕ ι) ι ℝ) : rotationFrame Z 0 = Z := by
  simp [rotationFrame_def]

/-- The frame of a rotation turns at unit speed: its derivative is `J (rotationFrame Z θ)`. -/
theorem hasDerivAt_rotationFrame (Z : Matrix (ι ⊕ ι) ι ℝ) (θ : ℝ) :
    HasDerivAt (rotationFrame Z) (J ι ℝ * rotationFrame Z θ) θ := by
  have hR : HasDerivAt (fun θ ↦ Real.cos θ • (1 : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) +
      Real.sin θ • J ι ℝ) (-Real.sin θ • 1 + Real.cos θ • J ι ℝ) θ :=
    hasDerivAt_matrix.2 fun p q ↦ by
      simpa using ((Real.hasDerivAt_cos θ).mul_const ((1 : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) p q)).fun_add
        ((Real.hasDerivAt_sin θ).mul_const (J ι ℝ p q))
  rw [show rotationFrame Z = _ from funext (rotationFrame_def Z)]
  convert hR.matrix_mul_const Z using 1
  rw [← Matrix.mul_assoc, Matrix.mul_add, Matrix.mul_smul,
    Matrix.mul_smul, Matrix.mul_one, J_squared, smul_neg, neg_smul, add_comm]

/-- **Chain rule** for the frame of a rotation: if `f` has derivative `f'` at `s`, then
`s ↦ rotationFrame Z (f s)` has derivative `f' • J (rotationFrame Z (f s))` there. -/
theorem hasDerivAt_rotationFrame_comp (Z : Matrix (ι ⊕ ι) ι ℝ) {f : ℝ → ℝ} {f' s : ℝ}
    (hf : HasDerivAt f f' s) :
    HasDerivAt (fun s ↦ rotationFrame Z (f s)) (f' • (J ι ℝ * rotationFrame Z (f s))) s :=
  hasDerivAt_matrix.2 fun p q ↦ by
    have h := (hasDerivAt_matrix.1 (hasDerivAt_rotationFrame Z (f s)) p q).comp s hf
    rw [Matrix.smul_apply, smul_eq_mul, mul_comm]
    exact h

open scoped ContDiff Matrix.Norms.Elementwise in
/-- The frame of a rotation is smooth in the angle, for the entrywise norm on matrices. -/
theorem contDiff_rotationFrame (Z : Matrix (ι ⊕ ι) ι ℝ) : ContDiff ℝ ∞ (rotationFrame Z) := by
  rw [show rotationFrame Z = _ from funext (rotationFrame_def Z)]
  exact ((Real.contDiff_cos.smul contDiff_const).add
    (Real.contDiff_sin.smul contDiff_const)).matrix_mul contDiff_const

/-! ### Frames of coordinate rotations -/

/-- The frame `fromRows (-sin θ Eᵢᵢ) (1 + (cos θ - 1) Eᵢᵢ)` of `coordinateRotate i θ {x = 0}`
(`range_coordinateRotationFrame`), where `Eᵢᵢ = Matrix.single i i 1`. -/
noncomputable def coordinateRotationFrame (i : ι) (θ : ℝ) : Matrix (ι ⊕ ι) ι ℝ :=
  fromRows (-single i i (Real.sin θ)) (1 + single i i (Real.cos θ - 1))

omit [Fintype ι] in
theorem coordinateRotationFrame_def (i : ι) (θ : ℝ) :
    coordinateRotationFrame i θ =
      fromRows (-single i i (Real.sin θ)) (1 + single i i (Real.cos θ - 1)) :=
  (rfl)

omit [Fintype ι] in
/-- **Chain rule** for the frame of a coordinate rotation: if `f` has derivative `f'` at `s`,
then `s ↦ coordinateRotationFrame i (f s)` has derivative
`f' • fromRows (-cos (f s) Eᵢᵢ) (-sin (f s) Eᵢᵢ)` there. -/
theorem hasDerivAt_coordinateRotationFrame_comp [Finite ι] (i : ι) {f : ℝ → ℝ} {f' s : ℝ}
    (hf : HasDerivAt f f' s) :
    HasDerivAt (fun s ↦ coordinateRotationFrame i (f s))
      (f' • fromRows (-single i i (Real.cos (f s))) (-single i i (Real.sin (f s)))) s := by
  refine hasDerivAt_matrix.2 fun p q ↦ ?_
  rcases p with p | p <;> by_cases h : i = p ∧ i = q
  · obtain ⟨rfl, rfl⟩ := h
    simpa [coordinateRotationFrame_def, mul_comm f'] using hf.sin.fun_neg
  · simpa [coordinateRotationFrame_def, single_apply, h] using hasDerivAt_const s (0 : ℝ)
  · obtain ⟨rfl, rfl⟩ := h
    simpa [coordinateRotationFrame_def, mul_comm f'] using (hf.cos.sub_const 1).const_add 1
  · simpa [coordinateRotationFrame_def, single_apply, h] using
      hasDerivAt_const s ((1 : Matrix ι ι ℝ) p q)

omit [Fintype ι] in
open scoped ContDiff Matrix.Norms.Elementwise in
/-- The frame of a coordinate rotation is smooth in the angle, for the entrywise norm on
matrices. -/
theorem contDiff_coordinateRotationFrame [Fintype ι] (i : ι) :
    ContDiff ℝ ∞ (coordinateRotationFrame (ι := ι) i) := by
  refine contDiff_pi' fun p ↦ contDiff_pi' fun q ↦ ?_
  rcases p with p | p <;>
    simp only [coordinateRotationFrame_def, fromRows_apply_inl, fromRows_apply_inr,
      Matrix.neg_apply, Matrix.add_apply, Matrix.single_apply] <;> split_ifs <;> fun_prop

/-- The crossing form of `coordinateRotationFrame i θ` with derivative
`c • fromRows (-cos θ Eᵢᵢ) (-sin θ Eᵢᵢ)`, relative to any subspace, is `u ↦ c uᵢ²`. -/
theorem lagrangianCrossingForm_coordinateRotationFrame_apply (i : ι) (θ c : ℝ)
    (V : Submodule ℝ (StdSpace ι))
    (u : V.comap (toEuclideanLin (coordinateRotationFrame i θ))) :
    lagrangianCrossingForm (coordinateRotationFrame i θ)
        (c • fromRows (-single i i (Real.cos θ)) (-single i i (Real.sin θ))) V u =
      c * (u : EuclideanSpace ℝ ι) i ^ 2 := by
  simp only [lagrangianCrossingForm_apply, stdForm_apply, StdSpace.x_apply, StdSpace.y_apply]
  simp only [coordinateRotationFrame_def, toLpLin_apply, fromRows_mulVec, neg_mulVec, single_mulVec,
    add_mulVec, one_mulVec, Sum.elim_inl, Pi.neg_apply, Function.update_apply, Pi.zero_apply,
    map_smul, LinearMap.smul_apply, PiLp.smul_apply, Sum.elim_inr, smul_eq_mul, mul_neg, mul_ite,
    mul_zero, neg_mul, ite_mul, zero_mul, Pi.add_apply, sub_neg_eq_add]
  rw [Finset.sum_eq_single i (fun j _ hj ↦ by simp [hj]) (by simp)]
  simp only [ite_true]
  linear_combination c * (u : EuclideanSpace ℝ ι) i ^ 2 * Real.sin_sq_add_cos_sq θ

namespace LagrangianGrassmannian

/-! ### Rotation paths -/

/-- If the columns of `Z` span `Λ`, those of `rotationFrame Z θ` span `rotate θ Λ`. So the
rotation `rotationPath Λ ε` has the frame `s ↦ rotationFrame Z (ε * s)`, whose crossing forms are
`u ↦ ε |Z u|²` (`lagrangianCrossingForm_smul_J_mul_apply`). -/
theorem range_rotationFrame {Λ : ℒ ι} {Z : Matrix (ι ⊕ ι) ι ℝ}
    (hZ : LinearMap.range (toEuclideanLin Z) = Λ) (θ : ℝ) :
    LinearMap.range (toEuclideanLin (rotationFrame Z θ)) = rotate θ Λ := by
  rw [rotate_def, unitary_smul_def, coe_smul_of_coe_eq _ hZ.symm, GLSymplectic.coe_ofUnitary,
    coe_scalarHom_eq_smul_one, coe_circleEquivUnitary, realify_smul_one,
    RCLike.re_to_complex, RCLike.im_to_complex,
    Circle.coe_exp, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, rotationFrame_def]

/-- Rotating a Lagrangian `Λ` by a small nonzero angle makes it transverse to any given
Lagrangian `V`: the crossing form of the rotation is definite, so its crossing at `0` is
isolated. -/
theorem eventually_rotate_inf_eq_bot (Λ V : ℒ ι) :
    ∀ᶠ θ in 𝓝[≠] (0 : ℝ), (rotate θ Λ : Submodule ℝ (StdSpace ι)) ⊓ V = ⊥ := by
  obtain ⟨Z, hZ⟩ : ∃ Z : Matrix (ι ⊕ ι) ι ℝ, LinearMap.range (toEuclideanLin Z) = Λ := by
    obtain ⟨U, rfl⟩ := unitaryFrame_surjective Λ
    exact ⟨_, (coe_unitaryFrame U).symm⟩
  -- The rotation `θ ↦ e^{θ J₀} Λ` has a regular crossing at `θ = 0`.
  have h0 : rotationFrame Z 0 = Z := by simp
  have hd := hasDerivAt_rotationFrame Z 0
  rw [h0] at hd
  refine eventually_nhdsNE_not_crossing_of_regular V (Λ := fun θ ↦ rotate θ Λ)
    (Eventually.of_forall fun θ ↦ range_rotationFrame hZ θ) hd ?_
  rw [h0]
  simpa using (anisotropic_lagrangianCrossingForm_smul_J_mul
    (injective_toEuclideanLin_of_range_eq hZ) one_ne_zero V).nondegenerate

/-- **The rotation off a Lagrangian has no crossing but its first point.** For every nonzero
angle `ε` small enough, the rotation `rotationPath Λ ε` meets a given Lagrangian `V` nontrivially
at most at `s = 0`. -/
theorem eventually_rotationPath_inf_eq_bot (Λ V : ℒ ι) :
    ∀ᶠ ε in 𝓝[≠] (0 : ℝ), ∀ t : I, t ≠ 0 →
      (rotationPath Λ ε t : Submodule ℝ (StdSpace ι)) ⊓ V = ⊥ := by
  obtain ⟨δ, hδ, h⟩ := Metric.eventually_nhds_iff.1
    (eventually_nhdsWithin_iff.1 (eventually_rotate_inf_eq_bot Λ V))
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Metric.ball_mem_nhds 0 hδ)] with
    ε hε hεδ t ht
  have ht0 : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1 fun h ↦ ht (Subtype.ext h.symm)
  rw [rotationPath_apply]
  refine h ?_ (mul_ne_zero hε ht0.ne')
  rw [Metric.mem_ball, Real.dist_0_eq_abs] at hεδ
  rw [Real.dist_0_eq_abs, abs_mul, abs_of_pos ht0]
  exact (mul_le_of_le_one_right (abs_nonneg ε) t.property.2).trans_lt hεδ

/-! ### Chart segments -/

open scoped ContDiff Matrix.Norms.Elementwise in
/-- **Chart segments.** Between two Lagrangians transverse to `{y = 0}` there is a path that never
meets `{y = 0}` and has a smooth frame `Z`, with derivative `Z' s` at every `s`: the segment
`s ↦ {x = S s y}` between the symmetric matrices of the two ends, with frame
`fromRows (S s) 1`. Smoothness is stated for the entrywise norm on matrices. -/
theorem exists_chartPath {Λ Λ' : ℒ ι}
    (hΛ : IsCompl (Λ : Submodule ℝ (StdSpace ι)) (horizontal ι))
    (hΛ' : IsCompl (Λ' : Submodule ℝ (StdSpace ι)) (horizontal ι)) :
    ∃ (γ : Path Λ Λ') (Z Z' : ℝ → Matrix (ι ⊕ ι) ι ℝ), ContDiff ℝ ∞ Z ∧
      (∀ s, HasDerivAt Z (Z' s) s) ∧
      (∀ t : I, LinearMap.range (toEuclideanLin (Z t)) = γ t) ∧
      ∀ t, (γ t : Submodule ℝ (StdSpace ι)) ⊓ horizontal ι = ⊥ := by
  obtain ⟨S₀, hS₀, h₀⟩ := isCompl_horizontal_iff.1 hΛ
  obtain ⟨S₁, hS₁, h₁⟩ := isCompl_horizontal_iff.1 hΛ'
  let S (s : ℝ) : selfAdjoint (Matrix ι ι ℝ) :=
    ⟨S₀ + s • (S₁ - S₀), isHermitian_iff_isSymm.2 (hS₀.add ((hS₁.sub hS₀).smul s))⟩
  have hS (s : ℝ) : (S s : Matrix ι ι ℝ) = S₀ + s • (S₁ - S₀) := rfl
  have hcS : Continuous S := Continuous.subtype_mk (by fun_prop) _
  -- The frame is affine in `s`.
  have hZ : (fun s ↦ fromRows (S s : Matrix ι ι ℝ) 1) =
      fun s : ℝ ↦ fromRows S₀ 1 + s • fromRows (S₁ - S₀) (0 : Matrix ι ι ℝ) := by
    funext s
    rw [hS]
    ext (p | p) q <;> simp
  refine ⟨⟨⟨fun t ↦ graphY (S t), continuous_graphY.comp (hcS.comp continuous_subtypeVal)⟩,
    toSubmodule_injective ?_, toSubmodule_injective ?_⟩, fun s ↦ fromRows (S s) 1,
    fun _ ↦ fromRows (S₁ - S₀) (0 : Matrix ι ι ℝ), ?_, fun s ↦ ?_, fun t ↦ ?_, fun t ↦ ?_⟩
  · simp [hS, h₀]
  · simp [hS, h₁]
  · rw [hZ]
    fun_prop
  · refine hasDerivAt_matrix.2 fun p q ↦ ?_
    rcases p with p | p
    · simpa [hS] using (((hasDerivAt_id s).mul_const ((S₁ - S₀) p q)).const_add (S₀ p q))
    · simpa using hasDerivAt_const s ((1 : Matrix ι ι ℝ) p q)
  · rw [Path.coe_mk_mk, coe_graphY]
    exact StdSpace.range_toEuclideanLin_fromRows_one_eq_graphY (S t : Matrix ι ι ℝ)
  · rw [Path.coe_mk_mk, coe_graphY, coe_horizontal]
    exact (StdSpace.isCompl_graphY_ker_y _).inf_eq_bot

/-! ### The coordinate half-turn -/

/-- The rotation of a Lagrangian `Λ` by the diagonal unitary matrix
`detSection ι i (Circle.exp θ) = diag(1, …, e^{iθ}, …, 1)`, which turns the `i`-th coordinate
plane `(xᵢ, yᵢ)` by the angle `θ` and fixes the others. -/
noncomputable def coordinateRotate (i : ι) (θ : ℝ) (Λ : ℒ ι) : ℒ ι :=
  detSection ι i (Circle.exp θ) • Λ

theorem coordinateRotate_def (i : ι) (θ : ℝ) (Λ : ℒ ι) :
    coordinateRotate i θ Λ = detSection ι i (Circle.exp θ) • Λ :=
  (rfl)

@[simp]
theorem coordinateRotate_zero (i : ι) (Λ : ℒ ι) : coordinateRotate i 0 Λ = Λ := by
  rw [coordinateRotate_def, Circle.exp_zero, map_one, one_smul]

/-- Turning the `i`-th coordinate plane by `φ` and then by `θ` is turning it by `θ + φ`. -/
theorem coordinateRotate_coordinateRotate (i : ι) (θ φ : ℝ) (Λ : ℒ ι) :
    coordinateRotate i θ (coordinateRotate i φ Λ) = coordinateRotate i (θ + φ) Λ := by
  rw [coordinateRotate_def, coordinateRotate_def, coordinateRotate_def, smul_smul,
    Circle.exp_add, map_mul]

theorem continuous_coordinateRotate (i : ι) (Λ : ℒ ι) :
    Continuous fun θ : ℝ ↦ coordinateRotate i θ Λ :=
  ((continuous_detSection i).comp Circle.exp.continuous).smul continuous_const

/-- The columns of `coordinateRotationFrame i θ` span `coordinateRotate i θ {x = 0}`. -/
theorem range_coordinateRotationFrame (i : ι) (θ : ℝ) :
    LinearMap.range (toEuclideanLin (coordinateRotationFrame i θ)) =
      coordinateRotate i θ (vertical ι) := by
  have hV : (vertical ι : Submodule ℝ (StdSpace ι)) =
      LinearMap.range (toEuclideanLin (fromRows (0 : Matrix ι ι ℝ) 1)) := by
    rw [StdSpace.range_toEuclideanLin_fromRows_one_eq_graphY, StdSpace.graphY_zero, coe_vertical]
  rw [coordinateRotate_def, unitary_smul_def, coe_smul_of_coe_eq _ hV, GLSymplectic.coe_ofUnitary,
    coe_detSection]
  congr 2
  set D := diagonal fun j ↦ ((Pi.mulSingle i (Circle.exp θ) : ι → Circle) j : ℂ) with hD
  have hR : D.realify = fromBlocks (D.map RCLike.re) (-D.map RCLike.im) (D.map RCLike.im)
      (D.map RCLike.re) := by
    ext (p | p) (q | q) <;> simp
  rw [hR, fromBlocks_mul_fromRows, Matrix.mul_zero, Matrix.mul_one, zero_add,
    Matrix.mul_zero, Matrix.mul_one, zero_add, coordinateRotationFrame_def]
  congr 1 <;> ext p q <;> by_cases hpq : p = q <;> by_cases hp : p = i <;> subst_vars <;>
    simp [diagonal_apply_ne, Circle.coe_exp, Complex.exp_mul_I, Complex.sin_ofReal_re,
      Complex.cos_ofReal_re, Ne.symm, *]

/-- A half-turn of one coordinate plane maps the vertical Lagrangian `{x = 0}` to itself. -/
theorem coordinateRotate_pi_vertical (i : ι) :
    coordinateRotate i Real.pi (vertical ι) = vertical ι := by
  have hY : IsUnit (1 + single i i (Real.cos Real.pi - 1)) := by
    rw [isUnit_one_add_single_iff, add_sub_cancel, Real.cos_pi]
    exact isUnit_one.neg
  rw [← toSubmodule_inj, ← range_coordinateRotationFrame, coordinateRotationFrame_def,
    StdSpace.range_toEuclideanLin_fromRows_eq_graphY hY, Real.sin_pi, single_zero, neg_zero,
    Matrix.zero_mul, StdSpace.graphY_zero, coe_vertical]

/-- The **coordinate half-turn** `s ↦ diag(1, …, e^{iπs}, …, 1) {x = 0}`, `s ∈ [0, 1]`, which turns
the `i`-th coordinate plane by the angle `π`: a loop at the vertical Lagrangian `{x = 0}` with
the frame `s ↦ coordinateRotationFrame i (π s)` (`range_coordinateRotationFrame`). -/
noncomputable def coordinateHalfTurn (i : ι) : Path (vertical ι) (vertical ι) where
  toFun t := coordinateRotate i (Real.pi * t) (vertical ι)
  continuous_toFun :=
    (continuous_coordinateRotate i _).comp (continuous_const.mul continuous_subtypeVal)
  source' := by simp
  target' := by simpa using coordinateRotate_pi_vertical i

@[simp]
theorem coordinateHalfTurn_apply (i : ι) (t : I) :
    coordinateHalfTurn i t = coordinateRotate i (Real.pi * t) (vertical ι) :=
  (rfl)

/-- The coordinate half-turn meets the horizontal Lagrangian `{y = 0}` only at `s = 1 / 2`. -/
theorem coordinateHalfTurn_inf_horizontal_ne_bot_iff (i : ι) (t : I) :
    (coordinateHalfTurn i t : Submodule ℝ (StdSpace ι)) ⊓ horizontal ι ≠ ⊥ ↔ (t : ℝ) = 1 / 2 := by
  have hL := (coordinateHalfTurn i t).isLagrangian
  rw [coordinateHalfTurn_apply, ← range_coordinateRotationFrame, coordinateRotationFrame_def]
    at hL ⊢
  rw [coe_horizontal, Ne, ← disjoint_iff,
    StdSpace.disjoint_range_toEuclideanLin_fromRows_ker_y_iff_of_isLagrangian hL,
    isUnit_one_add_single_iff, add_sub_cancel, isUnit_iff_ne_zero, not_not]
  constructor
  · intro h
    have ht : t = ⟨1 / 2, by norm_num, by norm_num⟩ :=
      TauCeti.cos_pi_mul_strictAnti.injective <|
        h.trans (mul_one_div Real.pi 2 ▸ Real.cos_pi_div_two).symm
    rw [ht]
  · intro h
    rw [h, mul_one_div, Real.cos_pi_div_two]

/-- At its crossing `s = 1 / 2`, the coordinate half-turn meets `{y = 0}` in the line of `eᵢ`: in
the coordinates of the frame `coordinateRotationFrame i (π / 2)`, the vectors `u` with
`Z u ∈ {y = 0}` are the multiples of `eᵢ`. -/
theorem comap_horizontal_coordinateRotationFrame_pi_div_two (i : ι) :
    (horizontal ι : Submodule ℝ (StdSpace ι)).comap
        (toEuclideanLin (coordinateRotationFrame i (Real.pi / 2))) =
      ℝ ∙ EuclideanSpace.single i (1 : ℝ) := by
  ext v
  rw [Submodule.mem_comap, mem_toSubmodule, mem_horizontal_iff, coordinateRotationFrame_def,
    StdSpace.y_toEuclideanLin_fromRows, Submodule.mem_span_singleton]
  constructor
  · intro hv
    refine ⟨v i, PiLp.ext fun j ↦ ?_⟩
    have := congrFun hv j
    by_cases hj : j = i
    · simp [hj]
    · simpa [add_mulVec, single_mulVec, hj, eq_comm] using this
  · rintro ⟨a, rfl⟩
    ext j
    by_cases hj : j = i <;> simp [hj, add_mulVec, single_mulVec, Real.cos_pi_div_two]

/-- The crossing form of the coordinate half-turn at `s = 1 / 2` lives on a line: in the frame
`coordinateRotationFrame i (π / 2)`, the vectors `u` with `Z u ∈ {y = 0}` form a line. -/
theorem finrank_comap_horizontal_coordinateRotationFrame_pi_div_two (i : ι) :
    Module.finrank ℝ ((horizontal ι : Submodule ℝ (StdSpace ι)).comap
      (toEuclideanLin (coordinateRotationFrame i (Real.pi / 2)))) = 1 := by
  rw [comap_horizontal_coordinateRotationFrame_pi_div_two, finrank_span_singleton]
  simp

/-- At its crossing `s = 1 / 2` with `{y = 0}`, the crossing form of the coordinate half-turn,
whose frame `s ↦ coordinateRotationFrame i (π s)` has derivative
`π • fromRows (-cos (π s) Eᵢᵢ) (-sin (π s) Eᵢᵢ)`, is positive definite: it is `u ↦ π uᵢ²` on the
line of `eᵢ`. -/
theorem posDef_lagrangianCrossingForm_coordinateRotationFrame_pi_div_two (i : ι) :
    (lagrangianCrossingForm (coordinateRotationFrame i (Real.pi / 2))
      (Real.pi • fromRows (-single i i (Real.cos (Real.pi / 2)))
        (-single i i (Real.sin (Real.pi / 2)))) (horizontal ι)).PosDef := by
  rintro ⟨u, hu⟩ hu0
  rw [lagrangianCrossingForm_coordinateRotationFrame_apply]
  rw [comap_horizontal_coordinateRotationFrame_pi_div_two, Submodule.mem_span_singleton] at hu
  obtain ⟨a, rfl⟩ := hu
  have ha : a ≠ 0 := by
    rintro rfl
    exact hu0 (Subtype.ext (zero_smul ℝ _))
  have := Real.pi_pos
  simpa using mul_pos this (pow_pos (abs_pos.2 ha) 2 |>.trans_eq (sq_abs a))

/-- **The coordinate half-turn has index `1`**, relative to any Lagrangian. -/
theorem pathMaslovIndex_coordinateHalfTurn (i : ι) (V : ℒ ι) :
    pathMaslovIndex (coordinateHalfTurn i) V = 1 := by
  let E : unitaryGroup ι ℂ := scalarHom ι ℂ (circleEquivUnitary (Circle.exp (Real.pi / 2)))
  let g (t : I) : unitaryGroup ι ℂ := detSection ι i (Circle.exp (Real.pi * t)) * E
  have hg : Continuous g :=
    (((continuous_detSection i).comp Circle.exp.continuous).comp
      (continuous_const.mul continuous_subtypeVal)).mul
      continuous_const
  have hE : unitaryFrame E = vertical ι := by
    rw [unitaryFrame_def, ← rotate_pi_div_two_horizontal, rotate_def]
  have hδ (t : I) : unitaryFrame (g t) = coordinateHalfTurn i t := by
    rw [unitaryFrame_mul, hE, coordinateHalfTurn_apply, coordinateRotate_def]
  have hdet (t : I) : ((g t : unitaryGroup ι ℂ) : Matrix ι ι ℂ).det =
      Complex.exp ((Real.pi * t + Fintype.card ι * (Real.pi / 2) : ℝ) * Complex.I) := by
    rw [Submonoid.coe_mul, det_mul, ← coe_detCircle, detCircle_detSection]
    simp only [E, coe_scalarHom_eq_smul_one, coe_circleEquivUnitary, det_smul, det_one, mul_one,
      Circle.coe_exp]
    rw [← Complex.exp_natCast_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [pathMaslovIndex_eq_sub_div_pi _ V ⟨⟨g, hg⟩, rfl, rfl⟩ hδ (by fun_prop) hdet]
  field_simp
  simp

end LagrangianGrassmannian

end SymplecticGeometry
