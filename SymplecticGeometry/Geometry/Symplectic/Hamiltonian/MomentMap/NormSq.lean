/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.LinearAlgebra.BilinearForm.Dual.Form
public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap.NormSq
import SymplecticGeometry.LinearAlgebra.BilinearForm.CauchySchwarz

/-!
# The dual of a moment map and its norm square

Let `𝔤` be a finite-dimensional real vector space, usually the Lie algebra `GroupLieAlgebra I G`
of a Lie group `G`, and fix a nondegenerate bilinear form `B` on `𝔤`. A map `μ : M → 𝔤*`, such as
a moment map, then has a dual `μ♯ : M → 𝔤`, characterized by
`B (μ♯ x) ξ = μ x ξ` for all `ξ`, so `μ♯ x = K (μ x)` for the
inverse `K = (B.toDual hB).symm` of `ξ ↦ B ξ`. The norm square of `μ` is Tau Ceti's
`TauCeti.momentNormSq μ K`, `x ↦ μ x (K (μ x)) = B (μ♯ x) (μ♯ x)`
(`SymplecticGeometry.momentNormSq_toDual_symm_eq_apply_momentSharp`, from Tau Ceti's
`TauCeti.momentNormSq_toDual_symm`). Tau Ceti also proves that, for a moment map `μ`, it is
smooth, and computes its derivative and gradient
(`TauCeti.SmoothTwoForm.IsMomentMap.contMDiff_momentNormSq`,
`TauCeti.SmoothTwoForm.IsMomentMap.mvfderiv_momentNormSq`,
`TauCeti.SmoothTwoForm.IsMomentMap.mgradient_momentNormSq`); and that it is `G`-invariant when
`μ` is equivariant for the dual of a representation `ρ` and `K` intertwines that dual with `ρ`
(`TauCeti.momentNormSq_smul`). This file adds the results that use the form `B`, and the
behaviour of `μ♯` and of the norm square under `μ ↦ -μ`. None of them uses a Lie bracket on `𝔤`.
Usually `B` is an `Ad`-invariant inner product, such as the one that
`TauCeti.Lie.exists_isSymm_posDef_continuousBilinearMap_adjoint_invariant`
gives on a compact group; the definitions take any nondegenerate `B`, and each result assumes
only what it uses. Nothing here uses a symplectic form.

## Main definitions

* `SymplecticGeometry.momentSharp B hB μ x`: the vector of `𝔤` dual to `μ x` under `B`.

## Main results

* `SymplecticGeometry.momentNormSq_toDual_symm_eq_apply_momentSharp`: the norm square at `x` is
  `B (μ♯ x) (μ♯ x)`.
* `SymplecticGeometry.momentNormSq_toDual_symm_eq_dualForm`: the norm square is the value of
  Tau Ceti's form `LinearMap.BilinForm.dualForm` on `𝔤*` at `(μ x, μ x)`.
* `SymplecticGeometry.momentNormSq_nonneg`, `SymplecticGeometry.momentNormSq_eq_zero_iff`: for a
  nonnegative, respectively anisotropic, `B`, the norm square is nonnegative, and it
  vanishes exactly where `μ` does; `SymplecticGeometry.bddBelow_range_momentNormSq_comp` bounds
  it below along any family of points.
* `SymplecticGeometry.abs_apply_le_sqrt_momentNormSq_mul_sqrt`: the Cauchy–Schwarz inequality
  `|μ x ξ| ≤ √(‖μ x‖²) √(B ξ ξ)` for a symmetric nonnegative `B`.
* `SymplecticGeometry.momentSharp_neg`, `SymplecticGeometry.momentNormSq_neg`: replacing `μ`
  by `-μ`, as the sign convention of an equivariant moment map may require, negates `μ♯` and
  leaves the norm square unchanged; `SymplecticGeometry.momentNormSq_neg'` states the latter as
  an equality of functions.

## References

* [V. Georgoulas, J. W. Robbin and D. A. Salamon, *The Moment-Weight Inequality and the
  Hilbert–Mumford Criterion*][GeorgoulasRobbinSalamon2021], §2.
* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §5.7.
-/

public section

noncomputable section

open TauCeti

namespace SymplecticGeometry

section MomentSharp

variable {M 𝔤 : Type*} [AddCommGroup 𝔤] [Module ℝ 𝔤] [FiniteDimensional ℝ 𝔤]
  {B : LinearMap.BilinForm ℝ 𝔤} {hB : B.Nondegenerate} {μ : M → Module.Dual ℝ 𝔤} {x : M}

variable (B hB μ) in
/-- The vector `μ♯ x` of `𝔤` dual to `μ x` under the nondegenerate bilinear form `B`: the unique
vector with `B (μ♯ x) ξ = μ x ξ` for every `ξ`. -/
def momentSharp (x : M) : 𝔤 :=
  (B.toDual hB).symm (μ x)

theorem momentSharp_def : momentSharp B hB μ x = (B.toDual hB).symm (μ x) :=
  (rfl)

/-- The defining property of `μ♯ x`: pairing it with `ξ` under `B` gives `μ x ξ`. -/
@[simp]
theorem apply_momentSharp (ξ : 𝔤) : B (momentSharp B hB μ x) ξ = μ x ξ := by
  rw [momentSharp_def, LinearMap.BilinForm.apply_toDual_symm_apply]

/-- `μ♯ x` is the only vector `v` with `B v ξ = μ x ξ` for every `ξ`. -/
theorem momentSharp_eq_iff {v : 𝔤} :
    momentSharp B hB μ x = v ↔ ∀ ξ, B v ξ = μ x ξ := by
  rw [momentSharp_def, LinearEquiv.symm_apply_eq, eq_comm, LinearMap.ext_iff]
  simp only [LinearMap.BilinForm.toDual_def]

@[simp]
theorem momentSharp_eq_zero_iff : momentSharp B hB μ x = 0 ↔ μ x = 0 := by
  rw [momentSharp_def, LinearEquiv.map_eq_zero_iff]

/-- The dual vector of `-μ` is the negative of that of `μ`. -/
@[simp]
theorem momentSharp_neg : momentSharp B hB (fun x ↦ -μ x) x = -momentSharp B hB μ x := by
  simp [momentSharp_def]

/-- The norm square of `μ x` for the inverse of `ξ ↦ B ξ` is `B (μ♯ x) (μ♯ x)`. -/
theorem momentNormSq_toDual_symm_eq_apply_momentSharp :
    momentNormSq μ (B.toDual hB).symm x = B (momentSharp B hB μ x) (momentSharp B hB μ x) := by
  rw [momentNormSq_toDual_symm, momentSharp_def]

/-- The norm square of `μ x` for the inverse of `ξ ↦ B ξ` is the value at `μ x` of the form
`B.dualForm hB` that `B` induces on `𝔤*`. -/
theorem momentNormSq_toDual_symm_eq_dualForm :
    momentNormSq μ (B.toDual hB).symm x = B.dualForm hB (μ x) (μ x) := by
  rw [momentNormSq_apply, LinearEquiv.coe_coe, LinearMap.BilinForm.dualForm_apply_eq]

/-- For a nonnegative form `B`, the norm square of `μ x` is nonnegative. -/
theorem momentNormSq_nonneg (hpos : B.IsNonneg) :
    0 ≤ momentNormSq μ (B.toDual hB).symm x := by
  rw [momentNormSq_toDual_symm]
  exact hpos.nonneg _

/-- For a nonnegative form `B`, the norm square of `μ` along any family `f : ι → M` of points is
bounded below by `0`. -/
theorem bddBelow_range_momentNormSq_comp {ι : Type*} (hpos : B.IsNonneg) (f : ι → M) :
    BddBelow (Set.range fun i ↦ momentNormSq μ (B.toDual hB).symm (f i)) :=
  ⟨0, by
    rintro _ ⟨i, rfl⟩
    exact momentNormSq_nonneg hpos⟩

/-- For an anisotropic form `B`, such as a positive definite one, the norm square of `μ x`
vanishes exactly when `μ x` does. -/
theorem momentNormSq_eq_zero_iff (hB' : B.toQuadraticMap.Anisotropic) :
    momentNormSq μ (B.toDual hB).symm x = 0 ↔ μ x = 0 := by
  rw [momentNormSq_toDual_symm]
  exact ⟨fun h ↦ by simpa using hB' _ h, fun h ↦ by simp [h]⟩

/-- **The Cauchy–Schwarz inequality** for the moment map: for a symmetric nonnegative form `B`,
`|μ x ξ| ≤ √(‖μ x‖²) * √(B ξ ξ)`, where `‖μ x‖² = momentNormSq μ (B.toDual hB).symm x`. -/
theorem abs_apply_le_sqrt_momentNormSq_mul_sqrt (hBs : B.IsSymm) (hpos : B.IsNonneg) (ξ : 𝔤) :
    |μ x ξ| ≤ √(momentNormSq μ (B.toDual hB).symm x) * √(B ξ ξ) := by
  rw [← LinearMap.BilinForm.apply_toDual_symm_apply (hB := hB) (μ x) ξ, momentNormSq_toDual_symm]
  exact B.abs_apply_le_sqrt_mul_sqrt hBs hpos _ _

end MomentSharp

section Neg

variable {M 𝔤 : Type*} [AddCommGroup 𝔤] [Module ℝ 𝔤] {μ : M → Module.Dual ℝ 𝔤}
  {K : Module.Dual ℝ 𝔤 →ₗ[ℝ] 𝔤} {x : M}

/-- The norm square of `-μ` is that of `μ`, for any linear map `K : 𝔤* → 𝔤`. -/
theorem momentNormSq_neg : momentNormSq (fun x ↦ -μ x) K x = momentNormSq μ K x := by
  simp

/-- The norm square of `-μ` is that of `μ`, as functions on `M`. -/
theorem momentNormSq_neg' : momentNormSq (fun x ↦ -μ x) K = momentNormSq μ K :=
  funext fun _ ↦ momentNormSq_neg

end Neg

end SymplecticGeometry

end
