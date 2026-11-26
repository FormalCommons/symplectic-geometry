/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Blowup.Model
public import SymplecticGeometry.LinearAlgebra.Projectivization.Perp

/-!
# The blowup of `ℂ²` as the incidence set of a pencil of lines

The model blowup `BlowupModel 1` of `ℂ²` at `0` consists of the pairs `(ℓ, z)` with `z` on the
line `ℓ`. Near an exceptional curve of a blown-up pencil, one meets it in another guise: as the
pairs `(z, [s : t])` with `s z₀ + t z₁ = 0`. Since, for `(s, t) ≠ 0`, the solutions `z` of this
equation are exactly the multiples of `(t, -s)`, the two descriptions agree through the line map
`[s : t] ↦ [t : -s]` (`SymplecticGeometry.perpLine`, with
`SymplecticGeometry.mem_submodule_perpLine_iff`). This file makes that precise over a ball.

## Main definitions and results

* `SymplecticGeometry.BlowupModel.pencilIncidence`: the pairs `(z, ℓ)` with `s z₀ + t z₁ = 0` for
  a representative `(s, t)` of `ℓ`, and `mk_mem_pencilIncidence_iff`: for any representative.
* `SymplecticGeometry.BlowupModel.pencilNbhd r`: its part over the ball of radius `r` in the
  Euclidean norm that `openNbhd` uses.
* `SymplecticGeometry.BlowupModel.pencilNbhdHomeomorph r`: the homeomorphism
  `pencilNbhd r ≃ₜ openNbhd 1 r`, `(z, ℓ) ↦ (perpLine ℓ, z)`, with
  `blowdown_pencilNbhdHomeomorph_apply`, `pr_pencilNbhdHomeomorph_apply` and the inverse's
  `coe_pencilNbhdHomeomorph_symm_apply`; and
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
    p ∈ pencilIncidence ↔ p.1 ∈ (perpLine p.2).submodule := by
  rw [mem_submodule_perpLine_iff, Matrix.vec2_dotProduct, mem_pencilIncidence_iff]

@[simp]
theorem mk_mem_pencilIncidence_iff {z w : Fin 2 → ℂ} (hw : w ≠ 0) :
    (z, mk ℂ w hw) ∈ pencilIncidence ↔ w 0 * z 0 + w 1 * z 1 = 0 := by
  rw [mem_pencilIncidence_iff_mem_submodule, mem_submodule_perpLine_mk_iff,
    Matrix.vec2_dotProduct]

theorem isClosed_pencilIncidence : IsClosed pencilIncidence := by
  have h : pencilIncidence = (fun p ↦ (perpLine p.2, p.1)) ⁻¹' blowupModel 1 := by
    ext p
    rw [mem_preimage, mem_blowupModel_iff]
    exact mem_pencilIncidence_iff_mem_submodule
  rw [h]
  exact (isClosed_blowupModel 1).preimage (by fun_prop)

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
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

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
theorem coe_pencilNbhdHomeomorph_symm_apply (p : openNbhd 1 r) :
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
