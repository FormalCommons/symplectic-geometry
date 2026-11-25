/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import SymplecticGeometry.Geometry.Manifold.Projectivization.FubiniStudy.Kahler
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Sqrt
import TauCeti.Analysis.Matrix.OrthogonalRows
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import SymplecticGeometry.Geometry.Manifold.Diffeomorph.RestrictScalars
import SymplecticGeometry.Analysis.Complex.Euclidean.Space

/-!
# Darboux charts of the Fubini–Study form

For `j : Fin (n + 1)`, this file builds a Darboux chart of the Fubini–Study form
`SymplecticGeometry.fubiniStudyForm n` of `ℂPⁿ = ℙ ℂ (Fin (n + 1) → ℂ)` on the affine open
`Projectivization.affineOpen j`, with values in the open unit ball of the standard model
`StdSpace (Fin n)`, and deduces one on the complement of every hyperplane. Write `|v|² = ∑ᵢ ‖vᵢ‖²`
and `ζ̌ = (complexToRealEuclidean (Fin n))⁻¹ ζ ∈ ℂⁿ` for `ζ : StdSpace (Fin n)`.

* `SymplecticGeometry.fubiniStudyDarbouxChart n j` is the partial diffeomorphism
  `[v] ↦ (|v_j| / |v|) (v_{j.succAbove k} / v_j)_k` (`fubiniStudyDarbouxChart_mk`), read in
  `StdSpace (Fin n)` through `complexToRealEuclidean`, from `affineOpen j`
  (`fubiniStudyDarbouxChart_source`) onto the unit ball (`fubiniStudyDarbouxChart_target`). It is
  the affine chart `Projectivization.affineChart j` followed by Mathlib's map
  `OpenPartialHomeomorph.univUnitBall`, `x ↦ x / √(1 + ‖x‖²)`, from a real inner product space onto
  its unit ball, which is smooth with a smooth inverse there. Its inverse sends `ζ` in the ball to
  `[Fin.insertNth j √(1 - ‖ζ‖²) ζ̌]` (`fubiniStudyDarbouxChart_symm_apply`).
* `SymplecticGeometry.eval₂_fubiniStudyForm_eq_stdForm_mvfderiv_darbouxChart`: the chart pulls the
  standard form `stdForm (Fin n)` back to the Fubini–Study form on its source. On the ball, the
  inverse chart is the projection `Projectivization.mkNonzero ℂ n` after the lift
  `ζ ↦ z = Fin.insertNth j √(1 - ‖ζ‖²) ζ̌`, along which `ω_FS` pulls back to the form
  `ρ = fubiniStudyLift n`. The lift lands in the unit sphere, its derivative is orthogonal to `z`
  and has a real `j`-th entry, so `ρ` reduces on it to `ω₀`, which forgets the `j`-th entry.
* `SymplecticGeometry.exists_darbouxChart_compl_hyperplane`: for a nonzero linear form `ℓ` on
  `ℂⁿ⁺¹`, there is a chart of the same kind from the complement `{x | ℓ x.rep ≠ 0}` of the
  hyperplane `ℓ = 0` onto the unit ball. A unitary matrix whose first row is proportional to the
  coefficients of `ℓ` (from Tau Ceti's `Matrix.exists_mul_conjTranspose_eq_one_and_submatrix_eq`)
  moves the hyperplane to `{z₀ = 0}` and preserves `ω_FS` (`mpullback_unitary_fubiniStudyForm`),
  so the chart is the Darboux chart of `0` after its action.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  Example 4.3.3, p. 168, and Exercise 4.3.4, p. 169.
-/

public section

open Function Metric Matrix TauCeti Projectivization OpenPartialHomeomorph
open scoped Manifold ContDiff InnerProductSpace LinearAlgebra.Projectivization Topology

namespace Metric

/-- A point `x` of the open unit ball has `0 < 1 - ‖x‖²`. -/
theorem one_sub_norm_sq_pos_of_mem_ball {E : Type*} [SeminormedAddGroup E] {x : E}
    (hx : x ∈ ball (0 : E) 1) : 0 < 1 - ‖x‖ ^ 2 := by
  nlinarith [norm_nonneg x, mem_ball_zero_iff.1 hx]

end Metric

namespace SymplecticGeometry

variable (n : ℕ)

/-- The Darboux chart of the Fubini–Study form on the affine open `affineOpen j` of `ℂPⁿ`: the
partial diffeomorphism `[v] ↦ (|v_j| / |v|) (v_{j.succAbove k} / v_j)_k`, read in `StdSpace (Fin n)`
through `complexToRealEuclidean`, onto the open unit ball, with inverse
`ζ ↦ [Fin.insertNth j √(1 - ‖ζ‖²) ζ̌]` (`fubiniStudyDarbouxChart_mk`,
`fubiniStudyDarbouxChart_symm_apply`). It pulls `stdForm (Fin n)` back to `fubiniStudyForm n`
(`eval₂_fubiniStudyForm_eq_stdForm_mvfderiv_darbouxChart`). -/
noncomputable def fubiniStudyDarbouxChart (j : Fin (n + 1)) :
    PartialDiffeomorph 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, StdSpace (Fin n)) (ℙ ℂ (Fin (n + 1) → ℂ))
      (StdSpace (Fin n)) ∞ where
  toFun x := univUnitBall (complexToRealEuclidean (Fin n) (affineChart j x))
  invFun ζ := (affineChart j).symm ((complexToRealEuclidean (Fin n)).symm (univUnitBall.symm ζ))
  source := affineOpen j
  target := ball 0 1
  map_source' _ _ := univUnitBall.map_source (Set.mem_univ _)
  map_target' _ _ := affineChart_source (K := ℂ) j ▸ (affineChart j).map_target (by simp)
  left_inv' x hx := by
    rw [univUnitBall.left_inv (Set.mem_univ _), ContinuousLinearEquiv.symm_apply_apply,
      (affineChart j).left_inv (by rwa [affineChart_source])]
  right_inv' ζ hζ := by
    rw [(affineChart j).right_inv (by simp), ContinuousLinearEquiv.apply_symm_apply,
      univUnitBall.right_inv hζ]
  open_source := isOpen_affineOpen j
  open_target := isOpen_ball
  contMDiffOn_toFun :=
    ((contDiff_univUnitBall.comp (complexToRealEuclidean (Fin n)).contDiff).contMDiff
      |>.comp_contMDiffOn ((contMDiffOn_affineChart (𝕜 := ℂ) (n := n) j ∞).restrictScalars' ℝ) :)
  contMDiffOn_invFun :=
    (contMDiff_affineChart_symm_restrictScalars j ∞).comp_contMDiffOn
      (((complexToRealEuclidean (Fin n)).symm.contDiff.comp_contDiffOn
        (contDiffOn_univUnitBall_symm (n := ⊤))).contMDiffOn)

variable {n}

/-- The source of the Darboux chart of `j` is the affine open of `j`. -/
@[simp]
theorem fubiniStudyDarbouxChart_source (j : Fin (n + 1)) :
    (fubiniStudyDarbouxChart n j).source = affineOpen j :=
  (rfl)

/-- The target of a Darboux chart is the open unit ball. -/
@[simp]
theorem fubiniStudyDarbouxChart_target (j : Fin (n + 1)) :
    (fubiniStudyDarbouxChart n j).target = ball 0 1 :=
  (rfl)

/-- The Darboux chart of `j` is the affine chart of `j` followed by `x ↦ x / √(1 + ‖x‖²)`. -/
theorem fubiniStudyDarbouxChart_apply (j : Fin (n + 1)) (x : ℙ ℂ (Fin (n + 1) → ℂ)) :
    fubiniStudyDarbouxChart n j x =
      univUnitBall (complexToRealEuclidean (Fin n) (affineChart j x)) :=
  (rfl)

/-- The inverse of the Darboux chart of `j` is `y ↦ y / √(1 - ‖y‖²)` followed by the inverse of the
affine chart of `j`. -/
theorem fubiniStudyDarbouxChart_symm_apply_eq_affineChart_symm (j : Fin (n + 1))
    (ζ : StdSpace (Fin n)) :
    (fubiniStudyDarbouxChart n j).symm ζ =
      (affineChart j).symm ((complexToRealEuclidean (Fin n)).symm (univUnitBall.symm ζ)) :=
  (rfl)

/-- The Darboux chart of `j` in homogeneous coordinates:
`[v] ↦ (|v_j| / |v|) (v_{j.succAbove k} / v_j)_k`, with `|v| = ‖complexToRealEuclidean _ v‖`.
Off the source, where `v j = 0`, both sides are `0`. -/
theorem fubiniStudyDarbouxChart_mk (j : Fin (n + 1)) (v : Fin (n + 1) → ℂ) (hv : v ≠ 0) :
    fubiniStudyDarbouxChart n j (mk ℂ v hv) =
      (‖v j‖ / ‖complexToRealEuclidean (Fin (n + 1)) v‖) •
        complexToRealEuclidean (Fin n) (fun k ↦ v (j.succAbove k) / v j) := by
  rw [fubiniStudyDarbouxChart_apply, affineChart_mk, univUnitBall_apply]
  by_cases hj : v j = 0
  · simp [hj, ← Pi.zero_def]
  congr 1
  have hv' : 0 < ‖complexToRealEuclidean (Fin (n + 1)) v‖ := norm_pos_iff.2 (by simpa using hv)
  have hj' : 0 < ‖v j‖ := norm_pos_iff.2 hj
  rw [← inv_div, _root_.inv_inj, ← Real.sqrt_sq (div_pos hv' hj').le, div_pow,
    norm_sq_complexToRealEuclidean, norm_sq_complexToRealEuclidean, Fin.sum_univ_succAbove _ j]
  congr 1
  simp only [norm_div, div_pow, ← Finset.sum_div]
  field_simp

/-- For every `ζ : StdSpace (Fin n)`, the vector `Fin.insertNth j √(1 - ‖ζ‖²) ζ̌ ∈ ℂⁿ⁺¹` is
nonzero: if `ζ̌ = 0`, its `j`-th entry is `1`. -/
theorem insertNth_sqrt_one_sub_norm_sq_ne_zero (j : Fin (n + 1)) (ζ : StdSpace (Fin n)) :
    Fin.insertNth (α := fun _ ↦ ℂ) j (√(1 - ‖ζ‖ ^ 2) : ℂ)
      ((complexToRealEuclidean (Fin n)).symm ζ) ≠ 0 := fun h ↦ by
  have h₁ := congrFun h j
  have h₂ : (complexToRealEuclidean (Fin n)).symm ζ = 0 := funext fun k ↦ by
    simpa using congrFun h (j.succAbove k)
  simp only [Fin.insertNth_apply_same, Pi.zero_apply, Complex.ofReal_eq_zero,
    Real.sqrt_eq_zero', sub_nonpos] at h₁
  simp only [map_eq_zero_iff _ (complexToRealEuclidean (Fin n)).symm.injective] at h₂
  simp only [h₂, norm_zero] at h₁
  norm_num at h₁

/-- The inverse of the Darboux chart of `j` sends `ζ` in the unit ball to
`[Fin.insertNth j √(1 - ‖ζ‖²) ζ̌]`, with `ζ̌ = (complexToRealEuclidean _)⁻¹ ζ`. -/
theorem fubiniStudyDarbouxChart_symm_apply (j : Fin (n + 1)) {ζ : StdSpace (Fin n)}
    (hζ : ζ ∈ ball (0 : StdSpace (Fin n)) 1) :
    (fubiniStudyDarbouxChart n j).symm ζ =
      mk ℂ (Fin.insertNth (α := fun _ ↦ ℂ) j (√(1 - ‖ζ‖ ^ 2) : ℂ)
        ((complexToRealEuclidean (Fin n)).symm ζ))
        (insertNth_sqrt_one_sub_norm_sq_ne_zero j ζ) := by
  have h₁ : 0 < √(1 - ‖ζ‖ ^ 2) := Real.sqrt_pos.2 (one_sub_norm_sq_pos_of_mem_ball hζ)
  rw [fubiniStudyDarbouxChart_symm_apply_eq_affineChart_symm, affineChart_symm_apply, mk_eq_mk_iff']
  refine ⟨((√(1 - ‖ζ‖ ^ 2))⁻¹ : ℝ), funext fun i ↦ ?_⟩
  rcases Fin.eq_self_or_eq_succAbove j i with rfl | ⟨k, rfl⟩
  · simp [h₁.ne']
  · simp [univUnitBall_symm_apply, Complex.ofReal_inv]

/-- The lift `ζ ↦ Fin.insertNth j √(1 - ‖ζ‖²) ζ̌` of the inverse chart to `ℂⁿ⁺¹ ∖ 0`. -/
private noncomputable def darbouxLift (j : Fin (n + 1)) (ζ : StdSpace (Fin n)) :
    puncturedSpace (Fin (n + 1) → ℂ) :=
  ⟨Fin.insertNth (α := fun _ ↦ ℂ) j (√(1 - ‖ζ‖ ^ 2) : ℂ) ((complexToRealEuclidean (Fin n)).symm ζ),
    mem_puncturedSpace.2 (insertNth_sqrt_one_sub_norm_sq_ne_zero j ζ)⟩

/-- The lift `darbouxLift j ζ` is the vector `Fin.insertNth j √(1 - ‖ζ‖²) ζ̌`. -/
private theorem coe_darbouxLift (j : Fin (n + 1)) (ζ : StdSpace (Fin n)) :
    (darbouxLift j ζ : Fin (n + 1) → ℂ) =
      Fin.insertNth (α := fun _ ↦ ℂ) j (√(1 - ‖ζ‖ ^ 2) : ℂ)
        ((complexToRealEuclidean (Fin n)).symm ζ) :=
  rfl

/-- The derivative of `darbouxLift j` at `ζ`. -/
private noncomputable def darbouxLiftDeriv (j : Fin (n + 1)) (ζ : StdSpace (Fin n)) :
    StdSpace (Fin n) →L[ℝ] Fin (n + 1) → ℂ :=
  ContinuousLinearMap.pi (Fin.insertNth (α := fun _ ↦ StdSpace (Fin n) →L[ℝ] ℂ) j
    (Complex.ofRealCLM.comp (-(√(1 - ‖ζ‖ ^ 2))⁻¹ • innerSL ℝ ζ))
    fun k ↦ (ContinuousLinearMap.proj k).comp
      ((complexToRealEuclidean (Fin n)).symm : StdSpace (Fin n) →L[ℝ] Fin n → ℂ))

/-- The derivative of the lift sends `a` to `Fin.insertNth j (-⟪ζ, a⟫ / √(1 - ‖ζ‖²)) ǎ`. -/
private theorem darbouxLiftDeriv_apply (j : Fin (n + 1)) (ζ a : StdSpace (Fin n)) :
    darbouxLiftDeriv j ζ a =
      Fin.insertNth (α := fun _ ↦ ℂ) j ((-(⟪ζ, a⟫_ℝ / √(1 - ‖ζ‖ ^ 2)) : ℝ) : ℂ)
        ((complexToRealEuclidean (Fin n)).symm a) := by
  funext i
  rcases Fin.eq_self_or_eq_succAbove j i with rfl | ⟨k, rfl⟩
  · simp [darbouxLiftDeriv, div_eq_inv_mul]
  · simp [darbouxLiftDeriv]

/-- On the unit ball, the lift has derivative `darbouxLiftDeriv j ζ`. -/
private theorem hasFDerivAt_darbouxLift (j : Fin (n + 1)) {ζ : StdSpace (Fin n)}
    (hζ : ζ ∈ ball (0 : StdSpace (Fin n)) 1) :
    HasFDerivAt (fun ζ ↦ (darbouxLift j ζ : Fin (n + 1) → ℂ)) (darbouxLiftDeriv j ζ) ζ := by
  have hpos := one_sub_norm_sq_pos_of_mem_ball hζ
  refine hasFDerivAt_pi'' fun i ↦ ?_
  rw [darbouxLiftDeriv, ContinuousLinearMap.proj_pi]
  rcases Fin.eq_self_or_eq_succAbove j i with rfl | ⟨k, rfl⟩
  · simp only [coe_darbouxLift, Fin.insertNth_apply_same]
    have h := (((hasFDerivAt_id ζ).norm_sq.const_sub 1).sqrt hpos.ne')
    refine Complex.ofRealCLM.hasFDerivAt.comp ζ (h.congr_fderiv ?_)
    ext a
    simp only [smul_apply, neg_apply,
      ContinuousLinearMap.comp_apply, innerSL_apply_apply, id_eq, ContinuousLinearMap.coe_id',
      smul_eq_mul, nsmul_eq_mul]
    field_simp
    ring
  · simp only [coe_darbouxLift, Fin.insertNth_apply_succAbove]
    exact ((ContinuousLinearMap.proj k).comp
      ((complexToRealEuclidean (Fin n)).symm : StdSpace (Fin n) →L[ℝ] Fin n → ℂ)).hasFDerivAt

/-- The derivative of the lift, as a map into `ℂⁿ⁺¹ ∖ 0`, at a point of the unit ball. -/
private theorem mfderiv_darbouxLift (j : Fin (n + 1)) {ζ : StdSpace (Fin n)}
    (hζ : ζ ∈ ball (0 : StdSpace (Fin n)) 1) (a : TangentSpace 𝓘(ℝ, StdSpace (Fin n)) ζ) :
    mfderiv 𝓘(ℝ, StdSpace (Fin n)) 𝓘(ℝ, Fin (n + 1) → ℂ) (darbouxLift j) ζ a =
      Fin.insertNth (α := fun _ ↦ ℂ) j
        ((-(⟪ζ, (a : StdSpace (Fin n))⟫_ℝ / √(1 - ‖ζ‖ ^ 2)) : ℝ) : ℂ)
        ((complexToRealEuclidean (Fin n)).symm (a : StdSpace (Fin n))) := by
  have h : HasMFDerivAt 𝓘(ℝ, StdSpace (Fin n)) 𝓘(ℝ, Fin (n + 1) → ℂ)
      (Subtype.val ∘ darbouxLift j) ζ (darbouxLiftDeriv j ζ) :=
    (hasFDerivAt_darbouxLift j hζ).hasMFDerivAt
  rw [← TauCeti.Manifold.mfderiv_subtype_val_comp_apply, h.mfderiv]
  -- `a` is read as a vector of `StdSpace (Fin n)`, its tangent space.
  exact darbouxLiftDeriv_apply j ζ a

/-- Near a point of the unit ball, the inverse chart is the projection after the lift. -/
private theorem eventuallyEq_fubiniStudyDarbouxChart_symm (j : Fin (n + 1)) {ζ : StdSpace (Fin n)}
    (hζ : ζ ∈ ball (0 : StdSpace (Fin n)) 1) :
    ⇑(fubiniStudyDarbouxChart n j).symm =ᶠ[𝓝 ζ] mkNonzero ℂ n ∘ darbouxLift j := by
  filter_upwards [isOpen_ball.mem_nhds hζ] with ξ hξ
  rw [fubiniStudyDarbouxChart_symm_apply j hξ, Function.comp_apply, mkNonzero_apply]
  simp only [coe_darbouxLift]

/-- The inverse chart pulls the Fubini–Study form back to `stdForm (Fin n)` on the unit ball. -/
private theorem eval₂_fubiniStudyForm_mfderiv_darbouxChart_symm (j : Fin (n + 1))
    {ζ : StdSpace (Fin n)} (hζ : ζ ∈ ball (0 : StdSpace (Fin n)) 1)
    (a b : TangentSpace 𝓘(ℝ, StdSpace (Fin n)) ζ) :
    (fubiniStudyForm n).eval₂ ((fubiniStudyDarbouxChart n j).symm ζ)
        (mfderiv 𝓘(ℝ, StdSpace (Fin n)) 𝓘(ℝ, Fin n → ℂ) (fubiniStudyDarbouxChart n j).symm ζ a)
        (mfderiv 𝓘(ℝ, StdSpace (Fin n)) 𝓘(ℝ, Fin n → ℂ) (fubiniStudyDarbouxChart n j).symm ζ b) =
      stdForm (Fin n) (a : StdSpace (Fin n)) (b : StdSpace (Fin n)) := by
  have hpos := one_sub_norm_sq_pos_of_mem_ball hζ
  have hE := eventuallyEq_fubiniStudyDarbouxChart_symm j hζ
  have hD : MDifferentiableAt 𝓘(ℝ, StdSpace (Fin n)) 𝓘(ℝ, Fin (n + 1) → ℂ) (darbouxLift j) ζ :=
    TauCeti.Manifold.mdifferentiableAt_subtype_val_comp_iff.1
      (hasFDerivAt_darbouxLift j hζ).hasMFDerivAt.mdifferentiableAt
  have hM := (contMDiff_mkNonzero ℂ n 1 (darbouxLift j ζ)).mdifferentiableAt one_ne_zero
  have hψ : mfderiv 𝓘(ℝ, StdSpace (Fin n)) 𝓘(ℝ, Fin n → ℂ) (fubiniStudyDarbouxChart n j).symm ζ =
      (mfderiv 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin n → ℂ) (mkNonzero ℂ n) (darbouxLift j ζ)).comp
        (mfderiv 𝓘(ℝ, StdSpace (Fin n)) 𝓘(ℝ, Fin (n + 1) → ℂ) (darbouxLift j) ζ) :=
    (hM.hasMFDerivAt.comp ζ hD.hasMFDerivAt).congr_of_eventuallyEq_abuse hE |>.mfderiv
  rw [hE.self_of_nhds, hψ, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    Function.comp_apply, eval₂_fubiniStudyForm_mfderiv_mkNonzero, fubiniStudyLift_apply,
    mfderiv_darbouxLift j hζ, mfderiv_darbouxLift j hζ]
  have hz : ∑ i, ‖(darbouxLift j ζ : Fin (n + 1) → ℂ) i‖ ^ 2 = 1 := by
    rw [← re_star_dotProduct_self, coe_darbouxLift, Fin.star_insertNth,
      insertNth_dotProduct_insertNth,
      Complex.add_re, ← inner_complexToRealEuclidean, ContinuousLinearEquiv.apply_symm_apply,
      real_inner_self_eq_norm_sq, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
      Complex.ofReal_re, Real.mul_self_sqrt hpos.le]
    ring
  have hre (c : StdSpace (Fin n)) : (star (darbouxLift j ζ : Fin (n + 1) → ℂ) ⬝ᵥ
      Fin.insertNth (α := fun _ ↦ ℂ) j ((-(⟪ζ, c⟫_ℝ / √(1 - ‖ζ‖ ^ 2)) : ℝ) : ℂ)
        ((complexToRealEuclidean (Fin n)).symm c)).re = 0 := by
    rw [coe_darbouxLift, Fin.star_insertNth, insertNth_dotProduct_insertNth, Complex.add_re,
      ← inner_complexToRealEuclidean, ContinuousLinearEquiv.apply_symm_apply,
      ContinuousLinearEquiv.apply_symm_apply, Complex.star_def, Complex.conj_ofReal,
      ← Complex.ofReal_mul, Complex.ofReal_re]
    field_simp
    ring
  rw [hz, hre a, hre b, stdComplexPiSymplecticForm_apply_eq_im, Fin.star_insertNth,
    insertNth_dotProduct_insertNth, Complex.add_im, Complex.star_def, Complex.conj_ofReal,
    ← Complex.ofReal_mul, Complex.ofReal_im, ← stdComplexPiSymplecticForm_apply_eq_im,
    ← stdForm_complexToRealEuclidean, (complexToRealEuclidean (Fin n)).apply_symm_apply a,
    (complexToRealEuclidean (Fin n)).apply_symm_apply b]
  simp

/-- **Darboux charts of the Fubini–Study form.** The Darboux chart `ψ` of `j` pulls the standard
form back to the Fubini–Study form: at every point `x` of its source `affineOpen j`,
`ω_FS(v, w) = ω₀(dψ_x v, dψ_x w)` for all tangent vectors `v`, `w`. With
`fubiniStudyDarbouxChart_target`, this makes `ψ` a symplectomorphism from `(affineOpen j, ω_FS)`
onto the open unit ball of `(StdSpace (Fin n), stdForm (Fin n))`. -/
theorem eval₂_fubiniStudyForm_eq_stdForm_mvfderiv_darbouxChart (j : Fin (n + 1))
    {x : ℙ ℂ (Fin (n + 1) → ℂ)} (hx : x ∈ (fubiniStudyDarbouxChart n j).source)
    (v w : TangentSpace 𝓘(ℝ, Fin n → ℂ) x) :
    (fubiniStudyForm n).eval₂ x v w =
      stdForm (Fin n) (mvfderiv 𝓘(ℝ, Fin n → ℂ) (fubiniStudyDarbouxChart n j) x v)
        (mvfderiv 𝓘(ℝ, Fin n → ℂ) (fubiniStudyDarbouxChart n j) x w) := by
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have hinv : (fubiniStudyDarbouxChart n j).symm (fubiniStudyDarbouxChart n j x) = x :=
    (fubiniStudyDarbouxChart n j).left_inv hx
  rw [mvfderiv_apply_eq_mfderiv_apply, mvfderiv_apply_eq_mfderiv_apply,
    ← eval₂_fubiniStudyForm_mfderiv_darbouxChart_symm j
      ((fubiniStudyDarbouxChart n j).map_source hx),
    hinv]
  -- The derivative of the inverse chart at `ψ x` undoes that of `ψ` at `x`.
  exact congrArg₂ ((fubiniStudyForm n).eval₂ x)
    ((fubiniStudyDarbouxChart n j).mfderiv_symm_apply_mfderiv_apply hn hx v).symm
    ((fubiniStudyDarbouxChart n j).mfderiv_symm_apply_mfderiv_apply hn hx w).symm

/-- The Darboux chart of `j` after the action of a unitary matrix, taken as a diffeomorphism `D`
of the underlying real manifold, still pulls the standard form back to the Fubini–Study form,
since that action preserves it. -/
private theorem eval₂_fubiniStudyForm_eq_stdForm_mvfderiv_unitary_trans_darbouxChart
    (W : unitaryGroup (Fin (n + 1)) ℂ)
    {D : ℙ ℂ (Fin (n + 1) → ℂ) ≃ₘ^∞⟮𝓘(ℝ, Fin n → ℂ), 𝓘(ℝ, Fin n → ℂ)⟯ ℙ ℂ (Fin (n + 1) → ℂ)}
    (hD : ⇑D = mapDiffeomorph (UnitaryGroup.toLinearEquiv W) ∞) (j : Fin (n + 1))
    {x : ℙ ℂ (Fin (n + 1) → ℂ)}
    (hx : x ∈ (D.toPartialDiffeomorph.trans (fubiniStudyDarbouxChart n j)).source)
    (v w : TangentSpace 𝓘(ℝ, Fin n → ℂ) x) :
    (fubiniStudyForm n).eval₂ x v w =
      stdForm (Fin n)
        (mvfderiv 𝓘(ℝ, Fin n → ℂ)
          (D.toPartialDiffeomorph.trans (fubiniStudyDarbouxChart n j)) x v)
        (mvfderiv 𝓘(ℝ, Fin n → ℂ)
          (D.toPartialDiffeomorph.trans (fubiniStudyDarbouxChart n j)) x w) := by
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have hx' : D x ∈ (fubiniStudyDarbouxChart n j).source := by simpa using hx
  have hc : ⇑(D.toPartialDiffeomorph.trans (fubiniStudyDarbouxChart n j)) =
      fubiniStudyDarbouxChart n j ∘ D := by
    funext z
    simp
  have hψ := (fubiniStudyDarbouxChart n j).mdifferentiableAt hn hx'
  rw [hc, mvfderiv_comp_apply x hψ (D.mdifferentiable hn x),
    mvfderiv_comp_apply x hψ (D.mdifferentiable hn x),
    ← eval₂_fubiniStudyForm_eq_stdForm_mvfderiv_darbouxChart j hx', hD,
    ← SmoothForm.eval₂_mpullback _ (hD ▸ D.contMDiff),
    mpullback_unitary_fubiniStudyForm]

/-- **Darboux charts on the complement of a hyperplane.** For a nonzero linear form `ℓ` on `ℂⁿ⁺¹`,
there is a partial diffeomorphism `ψ` from the complement `{x | ℓ x.rep ≠ 0}` of the hyperplane
`ℓ = 0` in `ℂPⁿ` onto the open unit ball of `StdSpace (Fin n)` that pulls the standard form back to
the Fubini–Study form. A point `[v]` lies in its source exactly when `ℓ v ≠ 0`. -/
theorem exists_darbouxChart_compl_hyperplane (ℓ : Module.Dual ℂ (Fin (n + 1) → ℂ)) (hℓ : ℓ ≠ 0) :
    ∃ ψ : PartialDiffeomorph 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, StdSpace (Fin n)) (ℙ ℂ (Fin (n + 1) → ℂ))
        (StdSpace (Fin n)) ∞,
      ψ.source = {x | ℓ x.rep ≠ 0} ∧ ψ.target = ball 0 1 ∧
      (∀ (v : Fin (n + 1) → ℂ) (hv : v ≠ 0), mk ℂ v hv ∈ ψ.source ↔ ℓ v ≠ 0) ∧
      ∀ x ∈ ψ.source, ∀ v w : TangentSpace 𝓘(ℝ, Fin n → ℂ) x,
        (fubiniStudyForm n).eval₂ x v w =
          stdForm (Fin n) (mvfderiv 𝓘(ℝ, Fin n → ℂ) ψ x v) (mvfderiv 𝓘(ℝ, Fin n → ℂ) ψ x w) := by
  -- The coefficients `a` of `ℓ`, so that `ℓ v = ∑ᵢ vᵢ aᵢ`.
  set a : Fin (n + 1) → ℂ := fun i ↦ ℓ fun k ↦ if i = k then 1 else 0
  have hℓa (v : Fin (n + 1) → ℂ) : ℓ v = ∑ i, v i * a i := by
    rw [LinearMap.pi_apply_eq_sum_univ ℓ v]
    simp [a]
  have ha : a ≠ 0 := fun h ↦ hℓ (LinearMap.ext fun v ↦ by simp [hℓa, h])
  -- The unit vector `u = a / |a|` is the first row of a unitary matrix `W`.
  set c : ℂ := (‖WithLp.toLp 2 a‖ : ℂ)⁻¹
  have hu : ∑ i, c * a i * star (c * a i) = 1 := by
    have h := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (c • WithLp.toLp 2 a)
    have h1 : ‖c • WithLp.toLp 2 a‖ = 1 := norm_smul_inv_norm (by simpa using ha)
    rw [h1, EuclideanSpace.inner_eq_star_dotProduct] at h
    simpa [dotProduct, mul_comm] using h
  obtain ⟨Q, hQ, hQu⟩ := exists_mul_conjTranspose_eq_one_and_submatrix_eq
    (of fun (_ : Fin 1) i ↦ c * a i) (e := fun _ ↦ 0) (fun _ _ _ ↦ Subsingleton.elim _ _)
    (by ext i k; obtain rfl := Subsingleton.elim i k; simpa [Matrix.mul_apply] using hu)
  set W : unitaryGroup (Fin (n + 1)) ℂ := ⟨Q, mem_unitaryGroup_iff.2 hQ⟩
  have hW (v : Fin (n + 1) → ℂ) :
      ((W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) *ᵥ v) 0 = c * ℓ v := by
    have hQ0 (i : Fin (n + 1)) : Q 0 i = c * a i := congrFun₂ hQu 0 i
    simp only [mulVec, dotProduct, W, hQ0, hℓa, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  -- The action `D` of `W` sends the complement of the hyperplane `ℓ = 0` to the affine open of `0`.
  set D := (mapDiffeomorph (UnitaryGroup.toLinearEquiv W) ∞).restrictScalars' ℝ
  have hDmk (v : Fin (n + 1) → ℂ) (hv : v ≠ 0) : D (mk ℂ v hv) ∈ affineOpen 0 ↔ ℓ v ≠ 0 := by
    rw [Diffeomorph.coe_restrictScalars', coe_mapDiffeomorph, map_mk, mk_mem_affineOpen_iff]
    simp [UnitaryGroup.toLinearEquiv, hW, c, ha]
  refine ⟨D.toPartialDiffeomorph.trans (fubiniStudyDarbouxChart n 0), ?_,
    by simp [fubiniStudyDarbouxChart_target],
    fun v hv ↦ by simpa [fubiniStudyDarbouxChart_source] using hDmk v hv,
    fun x hx v w ↦ eval₂_fubiniStudyForm_eq_stdForm_mvfderiv_unitary_trans_darbouxChart W
      (Diffeomorph.coe_restrictScalars' ℝ _) 0 hx v w⟩
  ext x
  induction x using ind with
  | h v hv =>
    simpa [fubiniStudyDarbouxChart_source, ← mem_linearProjectionDomain_iff] using hDmk v hv

end SymplecticGeometry

end
