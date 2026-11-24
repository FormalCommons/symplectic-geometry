/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.Structures
public import TauCeti.Geometry.Lie.Adjoint.Representation.Coadjoint.Basic
public import TauCeti.RepresentationTheory.InvariantForm

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
* `SymplecticGeometry.momentNormSq B hB μ x`: the norm square `B (μ♯ x) (μ♯ x)` of `μ x`.

## Main results

* `SymplecticGeometry.momentNormSq_nonneg`, `SymplecticGeometry.momentNormSq_eq_zero_iff`: for a
  nonnegative, respectively anisotropic, `B`, the norm square is nonnegative, and it
  vanishes exactly where `μ` does.
* `SymplecticGeometry.momentSharp_neg`, `SymplecticGeometry.momentNormSq_neg`: replacing `μ`
  by `-μ`, as the sign convention of an equivariant moment map may require, negates `μ♯` and
  leaves the norm square unchanged.
* `SymplecticGeometry.momentSharp_smul`, `SymplecticGeometry.momentNormSq_smul`: for an
  `Ad`-invariant `B` and a coadjoint-equivariant `μ`, `μ♯` is equivariant and the norm square
  is `G`-invariant.
* `SymplecticGeometry.contMDiff_momentNormSq`: if each component `x ↦ μ x ξ` is `C^n`, so is the
  norm square.

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
/-- The norm square `‖μ x‖² = B (μ♯ x) (μ♯ x)` of the moment map, for the form on the dual of
the Lie algebra that the nondegenerate form `B` induces. -/
def momentNormSq (x : M) : ℝ :=
  B (momentSharp B hB μ x) (momentSharp B hB μ x)

theorem momentNormSq_def :
    momentNormSq B hB μ x = B (momentSharp B hB μ x) (momentSharp B hB μ x) :=
  (rfl)

/-- The norm square of `μ x` is `μ x` evaluated at `μ♯ x`. -/
theorem momentNormSq_eq_apply_momentSharp :
    momentNormSq B hB μ x = μ x (momentSharp B hB μ x) := by
  rw [momentNormSq_def, apply_momentSharp]

/-- The norm square of `-μ` is that of `μ`. -/
@[simp]
theorem momentNormSq_neg : momentNormSq B hB (fun x ↦ -μ x) x = momentNormSq B hB μ x := by
  simp [momentNormSq_def, momentSharp_neg]

/-- For a nonnegative form `B`, the norm square of `μ x` is nonnegative. -/
theorem momentNormSq_nonneg (hpos : B.IsNonneg) : 0 ≤ momentNormSq B hB μ x :=
  hpos.nonneg _

/-- For an anisotropic form `B`, such as a positive definite one, the norm square of `μ x`
vanishes exactly when `μ x` does. -/
theorem momentNormSq_eq_zero_iff (hB' : B.toQuadraticMap.Anisotropic) :
    momentNormSq B hB μ x = 0 ↔ μ x = 0 := by
  rw [← momentSharp_eq_zero_iff (hB := hB)]
  exact ⟨hB' _, fun h ↦ by simp [momentNormSq_def, h]⟩

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
  rw [momentNormSq_def, momentSharp_smul hBG hμ, ← Lie.adjointRepresentation_apply (𝕜 := ℝ),
    Representation.isInvariantForm_iff.1 hBG, momentNormSq_def]

/-- In a basis `b` of the Lie algebra, the norm square of `μ x` is
`∑ i, μ x (b i) * μ x (B♯ (b.coord i))`, with `B♯` the inverse of `B.toDual hB`. -/
private theorem momentNormSq_eq_sum {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℝ (GroupLieAlgebra I G)) :
    momentNormSq B hB μ x = ∑ i, μ x (b i) * μ x ((B.toDual hB).symm (b.coord i)) := by
  rw [momentNormSq_eq_apply_momentSharp, momentSharp_def]
  conv_lhs => arg 2; rw [← b.sum_dual_apply_smul_coord (μ x)]
  simp only [map_sum, map_smul, smul_eq_mul]

/-- If every component `x ↦ μ x ξ` of the moment map is `C^n`, so is its norm square. -/
theorem contMDiff_momentNormSq [TopologicalSpace M] [ChartedSpace H' M] {n : WithTop ℕ∞}
    (hμ : ∀ ξ, ContMDiff I' 𝓘(ℝ) n fun x ↦ μ x ξ) : ContMDiff I' 𝓘(ℝ) n (momentNormSq B hB μ) := by
  let b := Module.finBasis ℝ (GroupLieAlgebra I G)
  simp_rw [funext fun x ↦ momentNormSq_eq_sum (hB := hB) (μ := μ) (x := x) b]
  exact ContMDiff.sum fun i _ ↦ (hμ _).mul (hμ _)

end MomentSharp

end SymplecticGeometry

end
