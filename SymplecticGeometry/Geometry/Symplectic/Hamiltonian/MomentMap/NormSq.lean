/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.Structures
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import TauCeti.Geometry.Lie.Adjoint.Representation.Coadjoint.Basic
public import TauCeti.LinearAlgebra.BilinearForm.Dual.Form
public import TauCeti.RepresentationTheory.InvariantForm
public import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
import SymplecticGeometry.Geometry.Manifold.ContMDiff.Dual
import SymplecticGeometry.Topology.Algebra.Module.BilinearForm
import TauCeti.Geometry.Manifold.MFDeriv.ContinuousLinearMap
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# The dual of a moment map and its norm square

Write `𝔤 = GroupLieAlgebra I G` for the Lie algebra of a Lie group `G`, and fix a nondegenerate
bilinear form `B` on `𝔤`. A map `μ : M → 𝔤*`, such as a moment map, then has a dual
`μ♯ : M → 𝔤`, characterized by `B (μ♯ x) ξ = μ x ξ` for all `ξ`, and a norm square
`‖μ x‖² = B (μ♯ x) (μ♯ x)`. Usually `B` is an `Ad`-invariant inner product, such as the one
that `TauCeti.Lie.exists_isSymm_posDef_continuousBilinearMap_adjoint_invariant` gives on a
compact group; the definitions take any nondegenerate `B`, and each result assumes only what it
uses. Nothing here uses a symplectic form: the results hold for any map `μ` with the stated
equivariance or smoothness.

## Main definitions

* `SymplecticGeometry.momentSharp B hB μ x`: the vector of `𝔤` dual to `μ x` under `B`.
* `SymplecticGeometry.momentNormSq B hB μ x`: the norm square of `μ x`, for Tau Ceti's form
  `LinearMap.BilinForm.dualForm` on `𝔤*`; it equals `B (μ♯ x) (μ♯ x)`.

## Main results

* `SymplecticGeometry.momentNormSq_nonneg`, `SymplecticGeometry.momentNormSq_eq_zero_iff`: for a
  nonnegative, respectively anisotropic, `B`, the norm square is nonnegative, and it
  vanishes exactly where `μ` does.
* `SymplecticGeometry.abs_apply_le_sqrt_momentNormSq_mul_sqrt`: the Cauchy–Schwarz inequality
  `|μ x ξ| ≤ √(‖μ x‖²) √(B ξ ξ)` for a symmetric nonnegative `B`.
* `SymplecticGeometry.momentSharp_neg`, `SymplecticGeometry.momentNormSq_neg`: replacing `μ`
  by `-μ`, as the sign convention of an equivariant moment map may require, negates `μ♯` and
  leaves the norm square unchanged; `SymplecticGeometry.momentNormSq_neg'` states the latter as
  an equality of functions.
* `SymplecticGeometry.momentSharp_smul`, `SymplecticGeometry.momentNormSq_smul`: for an
  `Ad`-invariant `B` and a coadjoint-equivariant `μ`, `μ♯` is equivariant and the norm square
  is `G`-invariant.
* `SymplecticGeometry.contMDiff_momentNormSq`: if each component `x ↦ μ x ξ` is `C^n`, so is the
  norm square.
* `SymplecticGeometry.mvfderiv_momentNormSq`: for a symmetric `B` and differentiable components,
  the derivative of the norm square at `x` is twice that of `y ↦ μ y (μ♯ x)`.

## References

* [V. Georgoulas, J. W. Robbin and D. A. Salamon, *The Moment-Weight Inequality and the
  Hilbert–Mumford Criterion*][GeorgoulasRobbinSalamon2021], §2.
* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §5.7.
-/

public section

noncomputable section

open Manifold TauCeti
open scoped Manifold ContDiff

namespace SymplecticGeometry

section MomentSharp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} {M : Type*}
  {B : LinearMap.BilinForm ℝ (GroupLieAlgebra I G)} {hB : B.Nondegenerate}
  {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)} {x : M}

variable (B hB μ) in
/-- The vector `μ♯ x` of the Lie algebra dual to `μ x` under the nondegenerate bilinear form `B`:
the unique vector with `B (μ♯ x) ξ = μ x ξ` for every `ξ`. -/
def momentSharp (x : M) : GroupLieAlgebra I G :=
  (B.toDual hB).symm (μ x)

theorem momentSharp_def : momentSharp B hB μ x = (B.toDual hB).symm (μ x) :=
  (rfl)

/-- The defining property of `μ♯ x`: pairing it with `ξ` under `B` gives `μ x ξ`. -/
@[simp]
theorem apply_momentSharp (ξ : GroupLieAlgebra I G) : B (momentSharp B hB μ x) ξ = μ x ξ := by
  rw [momentSharp_def, LinearMap.BilinForm.apply_toDual_symm_apply]

/-- `μ♯ x` is the only vector `v` with `B v ξ = μ x ξ` for every `ξ`. -/
theorem momentSharp_eq_iff {v : GroupLieAlgebra I G} :
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

variable (B hB μ) in
/-- The norm square `‖μ x‖² = B^∨ (μ x) (μ x)` of the moment map, for the form
`B^∨ = B.dualForm hB` on the dual of the Lie algebra that the nondegenerate form `B` induces.
It is `B (μ♯ x) (μ♯ x)` (`momentNormSq_eq_momentSharp`). -/
def momentNormSq (x : M) : ℝ :=
  B.dualForm hB (μ x) (μ x)

theorem momentNormSq_def : momentNormSq B hB μ x = B.dualForm hB (μ x) (μ x) :=
  (rfl)

/-- The norm square of `μ x` is `B (μ♯ x) (μ♯ x)`. -/
theorem momentNormSq_eq_momentSharp :
    momentNormSq B hB μ x = B (momentSharp B hB μ x) (momentSharp B hB μ x) := by
  rw [momentNormSq_def, LinearMap.BilinForm.dualForm_apply, momentSharp_def]

/-- The norm square of `μ x` is `μ x` evaluated at `μ♯ x`. -/
theorem momentNormSq_eq_apply_momentSharp :
    momentNormSq B hB μ x = μ x (momentSharp B hB μ x) := by
  rw [momentNormSq_def, LinearMap.BilinForm.dualForm_apply_eq, momentSharp_def]

/-- The norm square of `-μ` is that of `μ`. -/
@[simp]
theorem momentNormSq_neg : momentNormSq B hB (fun x ↦ -μ x) x = momentNormSq B hB μ x := by
  simp [momentNormSq_eq_momentSharp, momentSharp_neg]

/-- The norm square of `-μ` is that of `μ`, as functions on `M`. -/
theorem momentNormSq_neg' : momentNormSq B hB (fun x ↦ -μ x) = momentNormSq B hB μ :=
  funext fun _ ↦ momentNormSq_neg

/-- For a nonnegative form `B`, the norm square of `μ x` is nonnegative. -/
theorem momentNormSq_nonneg (hpos : B.IsNonneg) : 0 ≤ momentNormSq B hB μ x := by
  rw [momentNormSq_eq_momentSharp]
  exact hpos.nonneg _

/-- For an anisotropic form `B`, such as a positive definite one, the norm square of `μ x`
vanishes exactly when `μ x` does. -/
theorem momentNormSq_eq_zero_iff (hB' : B.toQuadraticMap.Anisotropic) :
    momentNormSq B hB μ x = 0 ↔ μ x = 0 := by
  rw [momentNormSq_eq_momentSharp, ← momentSharp_eq_zero_iff (hB := hB)]
  exact ⟨hB' _, fun h ↦ by simp [h]⟩

/-- **The Cauchy–Schwarz inequality** for the moment map: for a symmetric nonnegative form `B`,
`|μ x ξ| ≤ √(‖μ x‖²) * √(B ξ ξ)`, where `‖μ x‖²` is `momentNormSq B hB μ x`. -/
theorem abs_apply_le_sqrt_momentNormSq_mul_sqrt (hBs : B.IsSymm) (hpos : B.IsNonneg)
    (ξ : GroupLieAlgebra I G) :
    |μ x ξ| ≤ √(momentNormSq B hB μ x) * √(B ξ ξ) := by
  rw [← apply_momentSharp (hB := hB), momentNormSq_eq_momentSharp,
    ← Real.sqrt_mul (hpos.nonneg _)]
  exact Real.abs_le_sqrt
    (B.apply_sq_le_of_symm hpos.nonneg (LinearMap.BilinForm.isSymm_iff.1 hBs) _ _)

/-- For a coadjoint-equivariant `μ` and an `Ad`-invariant form `B`, the dual vector is
`Ad`-equivariant: `μ♯ (g • x) = Ad_g (μ♯ x)`. -/
theorem momentSharp_smul [LieGroup I 1 G] [MulAction G M]
    (hBG : Representation.IsInvariantForm (Lie.adjointRepresentation ℝ I G) B)
    (hμ : ∀ (g : G) (x : M), μ (g • x) = Lie.coadjointRepresentation ℝ I G g (μ x))
    (g : G) (x : M) :
    momentSharp B hB μ (g • x) = Lie.adjointContinuousLinearMap g (momentSharp B hB μ x) := by
  refine momentSharp_eq_iff.2 fun ξ ↦ ?_
  rw [← Lie.adjointRepresentation_apply (𝕜 := ℝ), hBG.apply_left, apply_momentSharp, hμ,
    Lie.coadjointRepresentation_apply, Lie.adjointRepresentation_apply]

/-- For a coadjoint-equivariant `μ` and an `Ad`-invariant form `B`, the norm square of the moment
map is invariant under `G`. -/
theorem momentNormSq_smul [LieGroup I 1 G] [MulAction G M]
    (hBG : Representation.IsInvariantForm (Lie.adjointRepresentation ℝ I G) B)
    (hμ : ∀ (g : G) (x : M), μ (g • x) = Lie.coadjointRepresentation ℝ I G g (μ x))
    (g : G) (x : M) : momentNormSq B hB μ (g • x) = momentNormSq B hB μ x := by
  rw [momentNormSq_eq_momentSharp, momentSharp_smul hBG hμ,
    ← Lie.adjointRepresentation_apply (𝕜 := ℝ), Representation.isInvariantForm_iff.1 hBG,
    momentNormSq_eq_momentSharp]

/-- The norm square through continuous linear maps: write `L y` for the linear form `μ y` on the
model space `E`, read as a continuous linear map, and `Φ` for the continuous inverse
`B.toContinuousBilinearMap.inverse` of `B.toDual hB`. Then the norm square at `y` is
`L y (Φ (L y))`. -/
theorem momentNormSq_eq_clm_apply :
    momentNormSq B hB μ = fun y ↦ (LinearMap.toContinuousLinearMap (μ y) : E →L[ℝ] ℝ)
      ((B.toContinuousBilinearMap.inverse : (E →L[ℝ] ℝ) →L[ℝ] E)
        (LinearMap.toContinuousLinearMap (μ y))) :=
  funext fun y ↦ by
    rw [LinearMap.BilinForm.toContinuousBilinearMap_inverse_apply hB,
      momentNormSq_eq_apply_momentSharp, momentSharp_def, LinearMap.coe_toContinuousLinearMap]
    -- The `show` reads `μ y` as a linear form on the model space `E`, the type that
    -- `LinearMap.toContinuousLinearMap` takes here.
    exact (congrFun (LinearMap.coe_toContinuousLinearMap' (show E →ₗ[ℝ] ℝ from μ y)) _).symm

/-- If every component `x ↦ μ x ξ` of the moment map is `C^n`, so is its norm square. -/
theorem contMDiff_momentNormSq [TopologicalSpace M] [ChartedSpace H' M] {n : WithTop ℕ∞}
    (hμ : ∀ ξ, ContMDiff I' 𝓘(ℝ) n fun x ↦ μ x ξ) : ContMDiff I' 𝓘(ℝ) n (momentNormSq B hB μ) := by
  have hL := contMDiff_toContinuousLinearMap_of_contMDiff_apply (E := E) hμ
  rw [momentNormSq_eq_clm_apply]
  exact hL.clm_apply ((ContinuousLinearMap.contMDiff _).comp hL)

/-- For a symmetric form `B`, if each component `y ↦ μ y ξ` of `μ` is differentiable at `x`, the
derivative of the norm square at `x` is twice that of the component `y ↦ μ y (μ♯ x)`. -/
theorem mvfderiv_momentNormSq [TopologicalSpace M] [ChartedSpace H' M] (hBs : B.IsSymm)
    (hμ : ∀ ξ, MDifferentiableAt I' 𝓘(ℝ) (fun y ↦ μ y ξ) x) :
    mvfderiv I' (momentNormSq B hB μ) x =
      (2 : ℝ) • mvfderiv I' (fun y ↦ μ y (momentSharp B hB μ x)) x := by
  -- Read `μ` as a family `L` of continuous linear forms, and `μ♯` as `Φ ∘ L` for the continuous
  -- inverse `Φ` of `B.toDual hB`; the norm square is then
  -- `y ↦ L y (Φ (L y))` (`momentNormSq_eq_clm_apply`).
  set L : M → E →L[ℝ] ℝ := fun y ↦ LinearMap.toContinuousLinearMap (μ y)
  have hL : MDifferentiableAt I' 𝓘(ℝ, E →L[ℝ] ℝ) L x := mdifferentiableAt_clm_apply.2 hμ
  -- The Lie algebra carries no normed instances, so `Φ` is taken on the model space `E`.
  set Φ : (E →L[ℝ] ℝ) →L[ℝ] E := B.toContinuousBilinearMap.inverse
  have hΦ (f : E →L[ℝ] ℝ) : Φ f = (B.toDual hB).symm (f : E →ₗ[ℝ] ℝ) :=
    LinearMap.BilinForm.toContinuousBilinearMap_inverse_apply hB _
  have hLx (y : M) : (L y : E →ₗ[ℝ] ℝ) = μ y := LinearMap.coe_toContinuousLinearMap _
  have h₁ : Φ (L x) = momentSharp B hB μ x := by rw [hΦ, hLx, momentSharp_def]
  -- For symmetric `B`, `μ x (Φ f) = B (μ♯ x) (Φ f) = B (Φ f) (μ♯ x) = f (μ♯ x)`.
  have h₂ (f : E →L[ℝ] ℝ) : L x (Φ f) = f (momentSharp B hB μ x) := by
    have h (g : Module.Dual ℝ (GroupLieAlgebra I G)) :
        μ x ((B.toDual hB).symm g) = g (momentSharp B hB μ x) := by
      rw [← apply_momentSharp, hBs.eq, LinearMap.BilinForm.apply_toDual_symm_apply]
    rw [hΦ]
    exact (congrFun (LinearMap.coe_toContinuousLinearMap' (show E →ₗ[ℝ] ℝ from μ x)) _).trans
      (h (f : E →ₗ[ℝ] ℝ))
  -- `momentNormSq_eq_clm_apply` with `L` and `Φ` folded, checked by definitional equality;
  -- rewriting with the theorem itself leaves terms that the rewrites below do not match.
  have hN : momentNormSq B hB μ = fun y ↦ L y (Φ (L y)) := momentNormSq_eq_clm_apply
  ext v
  have h₃ : mvfderiv I' L x v (momentSharp B hB μ x) =
      mvfderiv I' (fun y ↦ μ y (momentSharp B hB μ x)) x v :=
    mvfderiv_toContinuousLinearMap_apply (E := E) hμ v _
  have hΦL := Φ.mvfderiv_comp_apply hL v
  rw [Function.comp_def] at hΦL
  rw [hN,
    mvfderiv_clm_apply (p := fun y ↦ Φ (L y)) hL (Φ.mdifferentiableAt.comp x hL) v, hΦL, h₁, h₂, h₃,
    smul_apply, two_smul]

end MomentSharp

end SymplecticGeometry

end
