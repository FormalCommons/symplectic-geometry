/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Blowup.Model
public import Mathlib.Topology.Algebra.Projectivization

/-!
# The blowup of `ℂ²` as the incidence set of a pencil of lines

The model blowup `BlowupModel 1` of `ℂ²` at `0` consists of the pairs `(ℓ, z)` with `z` on the
line `ℓ`. Near an exceptional curve of a blown-up pencil, one meets it in another guise: as the
pairs `(z, [s : t])` with `s z₀ + t z₁ = 0`. Since, for `(s, t) ≠ 0`, the solutions `z` of this
equation are exactly the multiples of `(t, -s)`, the two descriptions agree through the line map
`[s : t] ↦ [t : -s]`. This file makes that precise over a ball.

## Main definitions and results

* `SymplecticGeometry.BlowupModel.perpLine ℓ`: the image of `ℓ ∈ ℙ ℂ ℂ²` under the linear
  automorphism `(s, t) ↦ (t, -s)` (`SymplecticGeometry.BlowupModel.perpLinearMap`), through
  `Projectivization.map`; it is a continuous involution (`perpLine_perpLine`,
  `continuous_perpLine`).
* `SymplecticGeometry.BlowupModel.mem_span_perp_iff`: for `w ≠ 0`, a vector `z` is a multiple of
  `(w₁, -w₀)` exactly when `w₀ z₀ + w₁ z₁ = 0`; hence `mem_submodule_perpLine_iff`.
* `SymplecticGeometry.BlowupModel.pencilIncidence`: the pairs `(z, ℓ)` with `s z₀ + t z₁ = 0` for
  a representative `(s, t)` of `ℓ`, and `mk_mem_pencilIncidence_iff`: for any representative.
* `SymplecticGeometry.BlowupModel.pencilNbhd r`: its part over the ball of radius `r` in the
  Euclidean norm that `openNbhd` uses.
* `SymplecticGeometry.BlowupModel.pencilNbhdHomeomorph r`: the homeomorphism
  `pencilNbhd r ≃ₜ openNbhd 1 r`, `(z, ℓ) ↦ (perpLine ℓ, z)`, with
  `blowdown_pencilNbhdHomeomorph_apply`, `pr_pencilNbhdHomeomorph_apply` and the inverse's
  `pencilNbhdHomeomorph_symm_apply`; and
  `SymplecticGeometry.BlowupModel.image_pencilNbhdHomeomorph_setOf_fst_eq_zero`: it maps the
  points with `z = 0` onto the exceptional divisor.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §7.1.
-/

public section

open Set Projectivization TauCeti
open scoped LinearAlgebra.Projectivization

namespace SymplecticGeometry

namespace BlowupModel

/-! ### The line map `[s : t] ↦ [t : -s]` -/

/-- The linear map `(s, t) ↦ (t, -s)` of `ℂ²`. -/
def perpLinearMap : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ) where
  toFun w := ![w 1, -w 0]
  map_add' v w := by ext i; fin_cases i <;> simp [add_comm]
  map_smul' a w := by ext i; fin_cases i <;> simp

@[simp]
theorem perpLinearMap_apply_zero (w : Fin 2 → ℂ) : perpLinearMap w 0 = w 1 :=
  (rfl)

@[simp]
theorem perpLinearMap_apply_one (w : Fin 2 → ℂ) : perpLinearMap w 1 = -w 0 :=
  (rfl)

@[simp]
theorem perpLinearMap_perpLinearMap (w : Fin 2 → ℂ) : perpLinearMap (perpLinearMap w) = -w := by
  ext i; fin_cases i <;> simp

theorem perpLinearMap_injective : Function.Injective perpLinearMap := fun v w h ↦ by
  simpa using congrArg perpLinearMap h

@[simp]
theorem perpLinearMap_eq_zero_iff {w : Fin 2 → ℂ} : perpLinearMap w = 0 ↔ w = 0 :=
  (injective_iff_map_eq_zero' _).1 perpLinearMap_injective w

theorem continuous_perpLinearMap : Continuous perpLinearMap :=
  LinearMap.continuous_of_finiteDimensional _

/-- The line map `[s : t] ↦ [t : -s]` of `ℙ ℂ ℂ²`, induced by `perpLinearMap`. -/
noncomputable def perpLine (ℓ : ℙ ℂ (Fin 2 → ℂ)) : ℙ ℂ (Fin 2 → ℂ) :=
  map perpLinearMap perpLinearMap_injective ℓ

@[simp]
theorem perpLine_mk (w : Fin 2 → ℂ) (hw : w ≠ 0) :
    perpLine (mk ℂ w hw) = mk ℂ (perpLinearMap w) (perpLinearMap_eq_zero_iff.not.2 hw) :=
  map_mk _ _ _ _

@[simp]
theorem perpLine_perpLine (ℓ : ℙ ℂ (Fin 2 → ℂ)) : perpLine (perpLine ℓ) = ℓ := by
  induction ℓ using ind with
  | h w hw =>
    rw [perpLine_mk, perpLine_mk, mk_eq_mk_iff']
    exact ⟨-1, by simp⟩

theorem perpLine_involutive : Function.Involutive perpLine :=
  perpLine_perpLine

theorem continuous_perpLine : Continuous perpLine :=
  continuous_map perpLinearMap_injective continuous_perpLinearMap

/-- For `w ≠ 0`, the vectors `z` with `w₀ z₀ + w₁ z₁ = 0` are the multiples of `(w₁, -w₀)`. -/
theorem mem_span_perp_iff {w : Fin 2 → ℂ} (hw : w ≠ 0) (z : Fin 2 → ℂ) :
    z ∈ ℂ ∙ perpLinearMap w ↔ w 0 * z 0 + w 1 * z 1 = 0 := by
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, rfl⟩
    simp only [Pi.smul_apply, perpLinearMap_apply_zero, perpLinearMap_apply_one, smul_eq_mul]
    ring
  · intro h
    have hw' : w 0 ≠ 0 ∨ w 1 ≠ 0 := by
      by_contra! h'
      exact hw (funext fun i ↦ by fin_cases i <;> simp [h'])
    rcases hw' with h0 | h1
    · refine ⟨-z 1 / w 0, funext fun i ↦ ?_⟩
      fin_cases i
      · simp only [Fin.zero_eta, Fin.isValue, Pi.smul_apply, perpLinearMap_apply_zero,
          smul_eq_mul]
        field_simp
        linear_combination -h
      · simp only [Fin.mk_one, Fin.isValue, Pi.smul_apply, perpLinearMap_apply_one, smul_eq_mul]
        field_simp
    · refine ⟨z 0 / w 1, funext fun i ↦ ?_⟩
      fin_cases i
      · simp only [Fin.zero_eta, Fin.isValue, Pi.smul_apply, perpLinearMap_apply_zero,
          smul_eq_mul]
        field_simp
      · simp only [Fin.mk_one, Fin.isValue, Pi.smul_apply, perpLinearMap_apply_one, smul_eq_mul]
        field_simp
        linear_combination -h

/-- A vector `z` lies on the line `perpLine (mk ℂ w hw)` exactly when `w₀ z₀ + w₁ z₁ = 0`. -/
theorem mem_submodule_perpLine_mk_iff {w : Fin 2 → ℂ} (hw : w ≠ 0) (z : Fin 2 → ℂ) :
    z ∈ (perpLine (mk ℂ w hw)).submodule ↔ w 0 * z 0 + w 1 * z 1 = 0 := by
  rw [perpLine_mk, submodule_mk, mem_span_perp_iff hw]

/-- A vector `z` lies on the line `perpLine ℓ` exactly when `s z₀ + t z₁ = 0` for the
representative `(s, t)` of `ℓ`. -/
theorem mem_submodule_perpLine_iff (ℓ : ℙ ℂ (Fin 2 → ℂ)) (z : Fin 2 → ℂ) :
    z ∈ (perpLine ℓ).submodule ↔ ℓ.rep 0 * z 0 + ℓ.rep 1 * z 1 = 0 := by
  conv_lhs => rw [← mk_rep ℓ]
  exact mem_submodule_perpLine_mk_iff ℓ.rep_ne_zero z

/-! ### The incidence set of the pencil -/

/-- The incidence set of the pencil of lines of `ℂ²` through `0`: the pairs `(z, ℓ)` with
`s z₀ + t z₁ = 0` for the representative `(s, t)` of `ℓ` (equivalently, for every representative,
`mk_mem_pencilIncidence_iff`). -/
def pencilIncidence : Set ((Fin 2 → ℂ) × ℙ ℂ (Fin 2 → ℂ)) :=
  {p | p.2.rep 0 * p.1 0 + p.2.rep 1 * p.1 1 = 0}

theorem mem_pencilIncidence_iff {p : (Fin 2 → ℂ) × ℙ ℂ (Fin 2 → ℂ)} :
    p ∈ pencilIncidence ↔ p.2.rep 0 * p.1 0 + p.2.rep 1 * p.1 1 = 0 :=
  Iff.rfl

/-- `(z, ℓ)` lies in the incidence set exactly when `z` lies on the line `perpLine ℓ`. -/
theorem mem_pencilIncidence_iff_mem_submodule {p : (Fin 2 → ℂ) × ℙ ℂ (Fin 2 → ℂ)} :
    p ∈ pencilIncidence ↔ p.1 ∈ (perpLine p.2).submodule :=
  (mem_submodule_perpLine_iff p.2 p.1).symm

@[simp]
theorem mk_mem_pencilIncidence_iff {z w : Fin 2 → ℂ} (hw : w ≠ 0) :
    (z, mk ℂ w hw) ∈ pencilIncidence ↔ w 0 * z 0 + w 1 * z 1 = 0 := by
  rw [mem_pencilIncidence_iff_mem_submodule, mem_submodule_perpLine_mk_iff]

theorem isClosed_pencilIncidence : IsClosed pencilIncidence := by
  have h : pencilIncidence = (fun p ↦ (perpLine p.2, p.1)) ⁻¹' blowupModel 1 := by
    ext p
    rw [mem_preimage, mem_blowupModel_iff]
    exact mem_pencilIncidence_iff_mem_submodule
  rw [h]
  exact (isClosed_blowupModel 1).preimage
    ((continuous_perpLine.comp continuous_snd).prodMk continuous_fst)

/-- The part of `pencilIncidence` over the ball of radius `r` of `ℂ²`, in the Euclidean norm
that `openNbhd` uses. -/
def pencilNbhd (r : ℝ) : Set ((Fin 2 → ℂ) × ℙ ℂ (Fin 2 → ℂ)) :=
  pencilIncidence ∩ {p | ‖complexToRealEuclidean (Fin 2) p.1‖ < r}

theorem mem_pencilNbhd_iff {r : ℝ} {p : (Fin 2 → ℂ) × ℙ ℂ (Fin 2 → ℂ)} :
    p ∈ pencilNbhd r ↔ p ∈ pencilIncidence ∧ ‖complexToRealEuclidean (Fin 2) p.1‖ < r :=
  Iff.rfl

@[simp]
theorem mk_mem_pencilNbhd_iff {r : ℝ} {z w : Fin 2 → ℂ} (hw : w ≠ 0) :
    (z, mk ℂ w hw) ∈ pencilNbhd r ↔
      w 0 * z 0 + w 1 * z 1 = 0 ∧ ‖complexToRealEuclidean (Fin 2) z‖ < r := by
  rw [mem_pencilNbhd_iff, mk_mem_pencilIncidence_iff]


/-! ### The homeomorphism with `openNbhd 1 r` -/

/-- The homeomorphism from the incidence set of the pencil over the ball of radius `r` onto the
neighbourhood `openNbhd 1 r` of the exceptional divisor of the model blowup of `ℂ²`: it sends
`(z, ℓ)` to the point with blowdown `z` on the line `perpLine ℓ`, and its inverse sends a point
`p` to `(p.blowdown, perpLine p.pr)`. -/
noncomputable def pencilNbhdHomeomorph (r : ℝ) : pencilNbhd r ≃ₜ openNbhd 1 r where
  toFun p := ⟨⟨(perpLine p.val.2, p.val.1),
      mem_blowupModel_iff.2 <|
        mem_pencilIncidence_iff_mem_submodule.1 (mem_pencilNbhd_iff.1 p.property).1⟩,
    mem_openNbhd_iff.2 (by rw [blowdown_mk]; exact (mem_pencilNbhd_iff.1 p.property).2)⟩
  invFun p := ⟨(p.val.blowdown, perpLine p.val.pr),
    mem_pencilNbhd_iff.2 ⟨mem_pencilIncidence_iff_mem_submodule.2 (by
      simpa only [perpLine_perpLine] using p.val.blowdown_mem_submodule),
      mem_openNbhd_iff.1 p.property⟩⟩
  left_inv p := Subtype.ext (Prod.ext (blowdown_mk _ _ _) (by simp))
  right_inv p := Subtype.ext (ext (by simp) (blowdown_mk _ _ _))
  continuous_toFun := by
    refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
    exact (continuous_perpLine.comp (continuous_snd.comp continuous_subtypeVal)).prodMk
      (continuous_fst.comp continuous_subtypeVal)
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ _
    exact ((continuous_blowdown.comp continuous_subtypeVal).prodMk
      (continuous_perpLine.comp (continuous_pr.comp continuous_subtypeVal)))

variable {r : ℝ}

@[simp]
theorem blowdown_pencilNbhdHomeomorph_apply (p : pencilNbhd r) :
    (pencilNbhdHomeomorph r p).val.blowdown = p.val.1 :=
  blowdown_mk _ _ _

@[simp]
theorem pr_pencilNbhdHomeomorph_apply (p : pencilNbhd r) :
    (pencilNbhdHomeomorph r p).val.pr = perpLine p.val.2 :=
  pr_mk _ _ _

@[simp]
theorem pencilNbhdHomeomorph_symm_apply (p : openNbhd 1 r) :
    ((pencilNbhdHomeomorph r).symm p).val = (p.val.blowdown, perpLine p.val.pr) :=
  (rfl)

/-- The homeomorphism `pencilNbhdHomeomorph r` maps the points of `pencilNbhd r` over `z = 0`
exactly onto the exceptional divisor. -/
theorem image_pencilNbhdHomeomorph_setOf_fst_eq_zero :
    pencilNbhdHomeomorph r '' {p | p.val.1 = 0} = Subtype.val ⁻¹' exceptionalDivisor 1 := by
  ext p
  rw [(pencilNbhdHomeomorph r).image_eq_preimage_symm]
  simp

end BlowupModel

end SymplecticGeometry

end
