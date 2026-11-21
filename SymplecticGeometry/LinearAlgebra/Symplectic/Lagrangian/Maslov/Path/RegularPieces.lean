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
public import SymplecticGeometry.LinearAlgebra.Matrix.Basis
public import SymplecticGeometry.LinearAlgebra.Matrix.Realify
public import TauCeti.LinearAlgebra.Matrix.UnitaryGroup.Basic

/-!
# Regular pieces of paths of Lagrangian subspaces

Three kinds of paths in the Lagrangian Grassmannian `ℒ ι` of `(StdSpace ι, ω₀)`, each with an
explicit frame whose derivative is known at every time, and with its crossings with a reference
Lagrangian and their crossing forms. They are the pieces out of which regular representatives of
paths are built.

## Main definitions

* `SymplecticGeometry.LagrangianGrassmannian.rotate θ Λ`: the image of `Λ` under the scalar
  unitary matrix `e^{iθ}`, that is, under `e^{θ J₀}`, with `rotate_rotate` for composition;
  `rotationPath Λ ε` is the path `s ↦ rotate (ε s) Λ`, with frame
  `s ↦ rotationFrame Z (ε s) = e^{ε s J₀} Z` for a frame `Z` of `Λ`.
* `SymplecticGeometry.coordinateUnitary i θ`: the unitary matrix `diag(1, …, e^{iθ}, …, 1)`;
  `SymplecticGeometry.LagrangianGrassmannian.coordinateRotate i θ Λ`: the image of `Λ` under it,
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
`SymplecticGeometry.LagrangianGrassmannian.eventually_not_crossing_of_regular`, applied to the
rotation through the angle `2 (t - 1 / 2)` at its interior crossing `t = 1 / 2`, so that one
application covers both signs of the angle. The index of the coordinate half-turn comes from the
loop formula `pathMaslovIndex_eq_sub_div_pi`, with the unitary frames
`diag(1, …, e^{iπs}, …, 1) e^{iπ/2}`.

## References

* [J. Robbin, D. Salamon, *The Maslov index for paths*][RobbinSalamon1993], §2.
* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.3.
-/

public section

open Matrix TauCeti Set Filter Topology
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

namespace LagrangianGrassmannian

/-! ### Rotations -/

/-- The rotation of a Lagrangian `Λ` by the scalar unitary matrix `e^{iθ} 1`, that is, by
`e^{θ J₀}`. -/
noncomputable def rotate (θ : ℝ) (Λ : ℒ ι) : ℒ ι :=
  (circleEquivUnitary (Circle.exp θ) • (1 : unitaryGroup ι ℂ)) • Λ

theorem rotate_def (θ : ℝ) (Λ : ℒ ι) :
    rotate θ Λ = (circleEquivUnitary (Circle.exp θ) • (1 : unitaryGroup ι ℂ)) • Λ :=
  (rfl)

@[simp]
theorem rotate_zero (Λ : ℒ ι) : rotate 0 Λ = Λ := by
  have h : circleEquivUnitary (Circle.exp 0) • (1 : unitaryGroup ι ℂ) = 1 :=
    Subtype.ext (by simp [Unitary.coe_smul])
  rw [rotate_def, h, one_smul]

/-- Rotating by `φ` and then by `θ` is rotating by `θ + φ`. -/
theorem rotate_rotate (θ φ : ℝ) (Λ : ℒ ι) : rotate θ (rotate φ Λ) = rotate (θ + φ) Λ := by
  rw [rotate_def, rotate_def, rotate_def, smul_smul]
  congr 1
  refine Subtype.ext ?_
  simp only [Submonoid.coe_mul, Unitary.coe_smul, OneMemClass.coe_one, Submonoid.smul_def,
    coe_circleEquivUnitary, Circle.exp_add, Circle.coe_mul, smul_mul_smul_comm, mul_one]

theorem continuous_rotate (Λ : ℒ ι) : Continuous fun θ : ℝ ↦ rotate θ Λ := by
  have h : Continuous fun θ : ℝ ↦ circleEquivUnitary (Circle.exp θ) • (1 : unitaryGroup ι ℂ) :=
    Continuous.subtype_mk (by fun_prop) _
  exact h.smul continuous_const

end LagrangianGrassmannian

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
  have hR : HasDerivWithinAt (fun θ ↦ Real.cos θ • (1 : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) +
      Real.sin θ • J ι ℝ) (-Real.sin θ • 1 + Real.cos θ • J ι ℝ) univ θ :=
    hasDerivWithinAt_matrix.2 fun p q ↦ by
      simpa using ((Real.hasDerivAt_cos θ).mul_const ((1 : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) p q)).fun_add
        ((Real.hasDerivAt_sin θ).mul_const (J ι ℝ p q))
  have h := hR.matrix_mul (hasDerivWithinAt_matrix_const Z univ θ)
  replace h : HasDerivAt _ _ θ :=
    hasDerivWithinAt_matrix_univ.1 h
  rw [show rotationFrame Z = _ from funext (rotationFrame_def Z)]
  convert h using 1
  rw [Matrix.mul_zero, add_zero, ← Matrix.mul_assoc, Matrix.mul_add, Matrix.mul_smul,
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

/-! ### Frames of coordinate rotations -/

/-- The diagonal unitary matrix `diag(1, …, e^{iθ}, …, 1)`, with `e^{iθ}` at the place `i`. It
turns the `i`-th coordinate plane `(xᵢ, yᵢ)` of `StdSpace ι` by the angle `θ`. -/
noncomputable def coordinateUnitary (i : ι) (θ : ℝ) : unitaryGroup ι ℂ :=
  ⟨diagonal (Function.update 1 i (Circle.exp θ : ℂ)),
    diagonal_update_one_mem_unitary_iff.2 (Circle.exp θ).coe_mem_unitary⟩

theorem coe_coordinateUnitary (i : ι) (θ : ℝ) :
    (coordinateUnitary i θ : Matrix ι ι ℂ) = diagonal (Function.update 1 i (Circle.exp θ : ℂ)) :=
  (rfl)

@[simp]
theorem coordinateUnitary_zero (i : ι) : coordinateUnitary i 0 = 1 :=
  Subtype.ext <| by simp [coe_coordinateUnitary]

theorem coordinateUnitary_add (i : ι) (θ φ : ℝ) :
    coordinateUnitary i (θ + φ) = coordinateUnitary i θ * coordinateUnitary i φ := by
  refine Subtype.ext ?_
  rw [Submonoid.coe_mul, coe_coordinateUnitary, coe_coordinateUnitary, coe_coordinateUnitary,
    diagonal_mul_diagonal]
  congr 1
  ext j
  by_cases hj : j = i <;> simp [hj, Circle.exp_add]

theorem continuous_coordinateUnitary (i : ι) : Continuous (coordinateUnitary i) :=
  continuous_induced_rng.2 <| by
    simpa only [Function.comp_def, coe_coordinateUnitary] using
      Continuous.matrix_diagonal (continuous_const.update i (by fun_prop))

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

/-- If the columns of `Z` span `Λ`, those of `rotationFrame Z θ` span `rotate θ Λ`. -/
theorem range_rotationFrame {Λ : ℒ ι} {Z : Matrix (ι ⊕ ι) ι ℝ}
    (hZ : LinearMap.range (toEuclideanLin Z) = Λ) (θ : ℝ) :
    LinearMap.range (toEuclideanLin (rotationFrame Z θ)) = rotate θ Λ := by
  rw [rotate_def, unitary_smul_def, coe_smul_of_coe_eq _ hZ.symm, GLSymplectic.coe_ofUnitary,
    Unitary.coe_smul, OneMemClass.coe_one, Submonoid.smul_def, coe_circleEquivUnitary,
    realify_smul_one, Circle.coe_exp, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    rotationFrame_def]

/-- The **rotation** `s ↦ e^{ε s J₀} Λ`, `s ∈ [0, 1]`, of a Lagrangian `Λ` through the angle `ε`.
For a frame `Z` of `Λ` it has the frame `s ↦ rotationFrame Z (ε * s)` (`range_rotationFrame`),
whose crossing forms are `u ↦ ε |Z u|²` (`lagrangianCrossingForm_smul_J_mul_apply`). -/
noncomputable def rotationPath (Λ : ℒ ι) (ε : ℝ) : Path Λ (rotate ε Λ) where
  toFun t := rotate (ε * t) Λ
  continuous_toFun := (continuous_rotate Λ).comp (continuous_const.mul continuous_subtypeVal)
  source' := by simp
  target' := by simp

@[simp]
theorem rotationPath_apply (Λ : ℒ ι) (ε : ℝ) (t : I) : rotationPath Λ ε t = rotate (ε * t) Λ :=
  (rfl)

/-- Rotating a Lagrangian `Λ` by a small nonzero angle makes it transverse to any given
Lagrangian `V`: the crossing form of the rotation is definite, so its crossing at `0` is
isolated. -/
theorem eventually_rotate_inf_eq_bot (Λ V : ℒ ι) :
    ∀ᶠ θ in 𝓝[≠] (0 : ℝ), (rotate θ Λ : Submodule ℝ (StdSpace ι)) ⊓ V = ⊥ := by
  obtain ⟨Z, hZ⟩ : ∃ Z : Matrix (ι ⊕ ι) ι ℝ, LinearMap.range (toEuclideanLin Z) = Λ := by
    obtain ⟨U, rfl⟩ := unitaryFrame_surjective Λ
    exact ⟨_, (coe_unitaryFrame U).symm⟩
  -- The rotation through the angle `2 (t - 1 / 2)`, `t ∈ [0, 1]`, has a regular crossing at
  -- `t = 1 / 2`.
  obtain ⟨h, hh⟩ : ∃ h : I, (h : ℝ) = 1 / 2 := ⟨⟨1 / 2, by norm_num, by norm_num⟩, rfl⟩
  have hd : HasDerivAt (fun r ↦ rotationFrame Z (2 * (r - 1 / 2))) ((2 : ℝ) • (J ι ℝ * Z))
      (h : ℝ) := by
    convert hasDerivAt_rotationFrame_comp Z (((hasDerivAt_id (h : ℝ)).sub_const (1 / 2)).const_mul
      (2 : ℝ)) using 2 <;> simp [hh]
  have hreg : (lagrangianCrossingForm (rotationFrame Z (2 * ((h : ℝ) - 1 / 2)))
      ((2 : ℝ) • (J ι ℝ * Z)) V).Nondegenerate := by
    rw [show rotationFrame Z (2 * ((h : ℝ) - 1 / 2)) = Z by simp [hh]]
    exact (anisotropic_lagrangianCrossingForm_smul_J_mul
      (injective_toEuclideanLin_of_range_eq hZ) two_ne_zero V).nondegenerate
  have key := eventually_not_crossing_of_regular
    (fun t : I ↦ rotate (2 * ((t : ℝ) - 1 / 2)) Λ) V
    (Z := fun r ↦ rotationFrame Z (2 * (r - 1 / 2))) (t₀ := h)
    (fun t ↦ range_rotationFrame hZ (2 * ((t : ℝ) - 1 / 2)))
    hd.matrix_hasDerivWithinAt hreg
  -- Read near `t = 1 / 2` through `θ ↦ θ / 2 + 1 / 2`.
  obtain ⟨f, hfc, hf⟩ : ∃ f : ℝ → I, Continuous f ∧
      ∀ {θ : ℝ}, θ ∈ Ioo (-1 : ℝ) 1 → (f θ : ℝ) = θ / 2 + 1 / 2 :=
    ⟨fun θ ↦ projIcc 0 1 zero_le_one (θ / 2 + 1 / 2), continuous_projIcc.comp (by fun_prop),
      fun hθ ↦ by dsimp only; rw [projIcc_of_mem _ ⟨by linarith [hθ.1], by linarith [hθ.2]⟩]⟩
  have hI : Ioo (-1 : ℝ) 1 ∈ 𝓝[≠] (0 : ℝ) :=
    nhdsWithin_le_nhds (Ioo_mem_nhds (by norm_num) (by norm_num))
  have htend : Tendsto f (𝓝[≠] 0) (𝓝[≠] h) := by
    refine tendsto_nhdsWithin_iff.2 ⟨tendsto_nhdsWithin_of_tendsto_nhds ?_, ?_⟩
    · convert hfc.tendsto 0 using 2
      exact Subtype.ext (by rw [hf (by norm_num), hh]; norm_num)
    · filter_upwards [hI, self_mem_nhdsWithin] with θ hθ hθ0 hfθ
      have := congrArg Subtype.val hfθ
      rw [hf hθ] at this
      rw [hh] at this
      exact hθ0 (mem_singleton_iff.2 (by linarith))
  filter_upwards [htend.eventually key, hI] with θ hθ hθI
  simpa only [hf hθI, show 2 * (θ / 2 + 1 / 2 - 1 / 2) = θ by ring] using hθ

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

/-- A quarter turn takes the horizontal Lagrangian `{y = 0}` to the vertical one `{x = 0}`. -/
theorem rotate_pi_div_two_horizontal : rotate (Real.pi / 2) (horizontal ι) = vertical ι := by
  rw [← symJ_smul_horizontal, rotate_def, unitary_smul_def]
  congr 1
  refine Subtype.ext (Units.ext ?_)
  rw [GLSymplectic.coe_ofUnitary, GLSymplectic.coe_symJ, ← realify_I_smul_one, Unitary.coe_smul,
    OneMemClass.coe_one, Submonoid.smul_def, coe_circleEquivUnitary]
  simp [Circle.coe_exp, Complex.exp_mul_I]

/-- The rotation of a Lagrangian `Λ` by the diagonal unitary matrix
`coordinateUnitary i θ = diag(1, …, e^{iθ}, …, 1)`, which turns the `i`-th coordinate plane
`(xᵢ, yᵢ)` by the angle `θ` and fixes the others. -/
noncomputable def coordinateRotate (i : ι) (θ : ℝ) (Λ : ℒ ι) : ℒ ι :=
  coordinateUnitary i θ • Λ

theorem coordinateRotate_def (i : ι) (θ : ℝ) (Λ : ℒ ι) :
    coordinateRotate i θ Λ = coordinateUnitary i θ • Λ :=
  (rfl)

@[simp]
theorem coordinateRotate_zero (i : ι) (Λ : ℒ ι) : coordinateRotate i 0 Λ = Λ := by
  rw [coordinateRotate_def, coordinateUnitary_zero, one_smul]

/-- Turning the `i`-th coordinate plane by `φ` and then by `θ` is turning it by `θ + φ`. -/
theorem coordinateRotate_coordinateRotate (i : ι) (θ φ : ℝ) (Λ : ℒ ι) :
    coordinateRotate i θ (coordinateRotate i φ Λ) = coordinateRotate i (θ + φ) Λ := by
  rw [coordinateRotate_def, coordinateRotate_def, coordinateRotate_def, smul_smul,
    coordinateUnitary_add]

theorem continuous_coordinateRotate (i : ι) (Λ : ℒ ι) :
    Continuous fun θ : ℝ ↦ coordinateRotate i θ Λ :=
  (continuous_coordinateUnitary i).smul continuous_const

/-- The columns of `coordinateRotationFrame i θ` span `coordinateRotate i θ {x = 0}`. -/
theorem range_coordinateRotationFrame (i : ι) (θ : ℝ) :
    LinearMap.range (toEuclideanLin (coordinateRotationFrame i θ)) =
      coordinateRotate i θ (vertical ι) := by
  have hV : (vertical ι : Submodule ℝ (StdSpace ι)) =
      LinearMap.range (toEuclideanLin (fromRows (0 : Matrix ι ι ℝ) 1)) := by
    rw [StdSpace.range_toEuclideanLin_fromRows_one_eq_graphY, StdSpace.graphY_zero, coe_vertical]
  rw [coordinateRotate_def, unitary_smul_def, coe_smul_of_coe_eq _ hV, GLSymplectic.coe_ofUnitary,
    coe_coordinateUnitary]
  congr 2
  set D := diagonal (Function.update (1 : ι → ℂ) i (Circle.exp θ : ℂ)) with hD
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
    have hπ := Real.pi_pos
    have := Real.injOn_cos ⟨by have := t.property.1; positivity, by nlinarith [t.property.2]⟩
      ⟨by positivity, by linarith⟩ (h.trans Real.cos_pi_div_two.symm)
    field_simp at this
    linarith
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
  let E : unitaryGroup ι ℂ := circleEquivUnitary (Circle.exp (Real.pi / 2)) • 1
  let g (t : I) : unitaryGroup ι ℂ := coordinateUnitary i (Real.pi * t) * E
  have hg : Continuous g :=
    ((continuous_coordinateUnitary i).comp (continuous_const.mul continuous_subtypeVal)).mul
      continuous_const
  have hE : unitaryFrame E = vertical ι := by
    rw [unitaryFrame_def, ← rotate_pi_div_two_horizontal, rotate_def]
  have hδ (t : I) : unitaryFrame (g t) = coordinateHalfTurn i t := by
    rw [unitaryFrame_mul, hE, coordinateHalfTurn_apply, coordinateRotate_def]
  have hdet (t : I) : ((g t : unitaryGroup ι ℂ) : Matrix ι ι ℂ).det =
      Complex.exp ((Real.pi * t + Fintype.card ι * (Real.pi / 2) : ℝ) * Complex.I) := by
    simp only [g, E, Submonoid.coe_mul, coe_coordinateUnitary, Unitary.coe_smul,
      OneMemClass.coe_one, Submonoid.smul_def, coe_circleEquivUnitary, det_mul, det_diagonal,
      det_smul, det_one, mul_one, Finset.prod_update_of_mem (Finset.mem_univ i), Pi.one_apply,
      Finset.prod_const_one, Circle.coe_exp]
    rw [← Complex.exp_natCast_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [pathMaslovIndex_eq_sub_div_pi _ V ⟨⟨g, hg⟩, rfl, rfl⟩ hδ (by fun_prop) hdet]
  field_simp
  simp

end LagrangianGrassmannian

end SymplecticGeometry
