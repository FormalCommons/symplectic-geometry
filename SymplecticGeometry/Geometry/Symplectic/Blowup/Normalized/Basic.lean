/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Complex.Blowup.Basic
public import SymplecticGeometry.Geometry.Symplectic.IsotopyExtension.Ball.Complex
public import SymplecticGeometry.LinearAlgebra.Symplectic.Standard.Basic
public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure
public import TauCeti.Geometry.Symplectic.Manifold.JHolomorphic
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm

/-!
# Normalized ball embeddings and their blowup charts

Let `M` be a manifold modelled on `E := Fin (n + 1) → ℂ`, with a symplectic form `σ` and an
almost complex structure `J`. A map `ψ₀ : StdSpace (Fin (n + 1)) → M` *normalizes* `(σ, J)` at
`p₀` on the ball of radius `δ` when `J` is compatible with `σ`, `ψ₀` is a symplectic embedding of
the closed ball `B(δ)` sending `0` to `p₀`, and the differential of `ψ₀` is complex linear from
the standard structure `J₀` of `StdSpace` to `J` on the open ball (McDuff–Salamon, Definition
7.1.17).

Such a `ψ₀` gives a chart of `M` at `p₀` with values in `E`: the inverse of
`ψ₀ ∘ complexToRealEuclidean (Fin (n + 1))` on the image of the open ball. It sends `p₀` to `0`,
so it is a `BlowupChart M p₀` of *Complex blowup*; it lies in the smooth maximal atlas of `M`, and
it is pseudoholomorphic from `J` to the complex structure of `E`. These are the two hypotheses
under which `Blowup.almostComplexStructure` puts an almost complex structure on the blowup
`Blowup c` of `M` at `p₀` along the chart.

## Main definitions

* `SymplecticGeometry.IsNormalizedAt σ J p₀ δ ψ₀`: `ψ₀` normalizes `(σ, J)` at `p₀` on the ball
  of radius `δ`.
* `SymplecticGeometry.IsNormalizedAt.blowupChart hN`: the blowup chart at `p₀` given by the
  inverse of `ψ₀`, read on `Fin (n + 1) → ℂ`.

## Main results

* `SymplecticGeometry.IsNormalizedAt.isPseudoholomorphicOn_comp_complexToRealEuclidean`: read on
  `Fin (n + 1) → ℂ`, a normalization is pseudoholomorphic on the preimage of the open ball, from
  the complex structure of `Fin (n + 1) → ℂ` to `J`.
* `SymplecticGeometry.IsNormalizedAt.blowupChart_mem_maximalAtlas`: the blowup chart is in the
  smooth maximal atlas of `M`.
* `SymplecticGeometry.IsNormalizedAt.blowupChart_isHolomorphic`: the blowup chart is
  pseudoholomorphic on its source from `J` to the complex structure of `Fin (n + 1) → ℂ`.

## Implementation notes

The symplectic form is called `σ`, since `ω` is a token once the scope `ContDiff` is open. The
definition asks for `0 < δ`, without which the open ball is empty and `ψ₀` gives no chart at
`p₀`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §7.1.
-/

public section

noncomputable section

open Set Metric
open scoped ContDiff Manifold

namespace SymplecticGeometry

open TauCeti TauCeti.SmoothAlmostComplexStructure

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Fin (n + 1) → ℂ) M]
  [IsManifold 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ M]

/-- `ψ₀` normalizes the symplectic form `σ` and the almost complex structure `J` at `p₀` on the
ball of radius `δ > 0`: `J` is compatible with `σ`, `ψ₀` is a symplectic embedding of the closed
ball `B(δ)` with `ψ₀ 0 = p₀`, and `ψ₀` is pseudoholomorphic on the open ball from the constant
standard complex structure `J₀` of `StdSpace` to `J`. -/
def IsNormalizedAt (σ : SmoothTwoForm 𝓘(ℝ, Fin (n + 1) → ℂ) M)
    (J : SmoothAlmostComplexStructure 𝓘(ℝ, Fin (n + 1) → ℂ) M) (p₀ : M) (δ : ℝ)
    (ψ₀ : StdSpace (Fin (n + 1)) → M) : Prop :=
  σ.Compatible J ∧ 0 < δ ∧ IsSymplecticBallEmbedding σ δ ψ₀ ∧ ψ₀ 0 = p₀ ∧
    IsPseudoholomorphicOn (stdComplexStructure (Fin (n + 1))).constSmooth J ψ₀ (ball 0 δ)

variable {σ : SmoothTwoForm 𝓘(ℝ, Fin (n + 1) → ℂ) M}
  {J : SmoothAlmostComplexStructure 𝓘(ℝ, Fin (n + 1) → ℂ) M} {p₀ : M} {δ : ℝ}
  {ψ₀ : StdSpace (Fin (n + 1)) → M}

theorem isNormalizedAt_def :
    IsNormalizedAt σ J p₀ δ ψ₀ ↔
      σ.Compatible J ∧ 0 < δ ∧ IsSymplecticBallEmbedding σ δ ψ₀ ∧ ψ₀ 0 = p₀ ∧
        IsPseudoholomorphicOn (stdComplexStructure (Fin (n + 1))).constSmooth J ψ₀
          (ball 0 δ) :=
  Iff.rfl

namespace IsNormalizedAt

variable (hN : IsNormalizedAt σ J p₀ δ ψ₀)
include hN

/-- The almost complex structure of a normalization is compatible with the symplectic form. -/
theorem compatible : σ.Compatible J := hN.1

/-- The radius of a normalization is positive. -/
theorem pos : 0 < δ := hN.2.1

/-- A normalization is a symplectic embedding of the closed ball of radius `δ`. -/
theorem isSymplecticBallEmbedding : IsSymplecticBallEmbedding σ δ ψ₀ := hN.2.2.1

/-- A normalization at `p₀` sends the origin to `p₀`. -/
theorem map_zero : ψ₀ 0 = p₀ := hN.2.2.2.1

/-- A normalization is pseudoholomorphic on the open ball of radius `δ`, from the constant
standard complex structure `J₀` to `J`. -/
theorem isPseudoholomorphicOn :
    IsPseudoholomorphicOn (stdComplexStructure (Fin (n + 1))).constSmooth J ψ₀ (ball 0 δ) :=
  hN.2.2.2.2

/-- On the open ball, the differential of a normalization sends the standard complex
structure `J₀` to `J`. -/
theorem mfderiv_comp_stdComplexStructure {z : StdSpace (Fin (n + 1))} (hz : z ∈ ball 0 δ)
    (v : StdSpace (Fin (n + 1))) :
    mfderiv 𝓘(ℝ, StdSpace (Fin (n + 1))) 𝓘(ℝ, Fin (n + 1) → ℂ) ψ₀ z
        (stdComplexStructure (Fin (n + 1)) v) =
      J (ψ₀ z) (mfderiv 𝓘(ℝ, StdSpace (Fin (n + 1))) 𝓘(ℝ, Fin (n + 1) → ℂ) ψ₀ z v) := by
  rw [← AlmostComplexStructure.constSmooth_apply _ z v]
  exact ((hN.isPseudoholomorphicOn.isPseudoholomorphicWithinAt hz).isPseudoholomorphicAt_of_mem_nhds
    (isOpen_ball.mem_nhds hz)).mfderiv_apply_commute v

/-- Read on `Fin (n + 1) → ℂ`, a normalization is pseudoholomorphic on the preimage of the open
ball: `ψ₀ ∘ complexToRealEuclidean (Fin (n + 1))` is pseudoholomorphic there from the complex
structure of `Fin (n + 1) → ℂ` to `J`. -/
theorem isPseudoholomorphicOn_comp_complexToRealEuclidean :
    IsPseudoholomorphicOn (ofComplexManifold (Fin (n + 1) → ℂ) (Fin (n + 1) → ℂ)) J
      (ψ₀ ∘ complexToRealEuclidean (Fin (n + 1)))
      (complexToRealEuclidean (Fin (n + 1)) ⁻¹' ball 0 δ) :=
  hN.isPseudoholomorphicOn.comp
    ((isPseudoholomorphic_complexToRealEuclidean _).isPseudoholomorphicOn _) (mapsTo_preimage _ _)

/-- The blowup chart of a normalization `ψ₀` at `p₀`: the inverse of
`ψ₀ ∘ complexToRealEuclidean (Fin (n + 1))`, from the image under `ψ₀` of the open ball of
radius `δ` onto the preimage of that ball in `Fin (n + 1) → ℂ`. -/
def blowupChart : BlowupChart (n := n) M p₀ where
  toOpenPartialHomeomorph :=
    hN.isSymplecticBallEmbedding.complexPartialDiffeomorph.toOpenPartialHomeomorph.symm
  mem_source := by
    rw [OpenPartialHomeomorph.symm_source, PartialDiffeomorph.toOpenPartialHomeomorph_target,
      IsSymplecticBallEmbedding.complexPartialDiffeomorph_target]
    exact ⟨0, mem_ball_self hN.pos, hN.map_zero⟩
  map_center := by
    have hp := congrFun hN.isSymplecticBallEmbedding.coe_complexPartialDiffeomorph 0
    rw [Function.comp_apply, _root_.map_zero, hN.map_zero,
      ← PartialDiffeomorph.toFun'_toOpenPartialHomeomorph] at hp
    exact (congrArg _ hp.symm).trans (OpenPartialHomeomorph.left_inv _
      (by simpa using hN.pos))

/-- The underlying open partial homeomorphism of the blowup chart is the inverse of
`ψ₀ ∘ complexToRealEuclidean (Fin (n + 1))` on the open ball. -/
theorem blowupChart_toOpenPartialHomeomorph :
    hN.blowupChart.toOpenPartialHomeomorph =
      hN.isSymplecticBallEmbedding.complexPartialDiffeomorph.toOpenPartialHomeomorph.symm :=
  (rfl)

/-- The source of the blowup chart is the image under `ψ₀` of the open ball of radius `δ`. -/
@[simp]
theorem blowupChart_source : hN.blowupChart.source = ψ₀ '' ball 0 δ := by
  simp [blowupChart_toOpenPartialHomeomorph]

/-- The target of the blowup chart is the preimage in `Fin (n + 1) → ℂ` of the open ball of
radius `δ`. -/
@[simp]
theorem blowupChart_target :
    hN.blowupChart.target = complexToRealEuclidean (Fin (n + 1)) ⁻¹' ball 0 δ := by
  simp [blowupChart_toOpenPartialHomeomorph]

/-- The inverse of the blowup chart is `ψ₀ ∘ complexToRealEuclidean (Fin (n + 1))`. -/
@[simp]
theorem coe_blowupChart_symm :
    ⇑hN.blowupChart.symm = ψ₀ ∘ complexToRealEuclidean (Fin (n + 1)) := by
  simp [blowupChart_toOpenPartialHomeomorph]

/-- The blowup chart of a normalization is in the smooth maximal atlas of `M`. -/
theorem blowupChart_mem_maximalAtlas :
    hN.blowupChart.toOpenPartialHomeomorph ∈
      IsManifold.maximalAtlas 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ M := by
  rw [IsManifold.mem_maximalAtlas_iff_contMDiffOn, blowupChart_toOpenPartialHomeomorph]
  exact ⟨hN.isSymplecticBallEmbedding.complexPartialDiffeomorph.symm.contMDiffOn_toFun,
    hN.isSymplecticBallEmbedding.complexPartialDiffeomorph.symm.contMDiffOn_invFun⟩

/-- The blowup chart of a normalization is pseudoholomorphic on its source, from `J` to the
complex structure of `Fin (n + 1) → ℂ`. -/
theorem blowupChart_isHolomorphic :
    IsPseudoholomorphicOn J (ofComplexManifold (Fin (n + 1) → ℂ) (Fin (n + 1) → ℂ))
      hN.blowupChart hN.blowupChart.source := by
  set Φ := hN.isSymplecticBallEmbedding.complexPartialDiffeomorph
  have hΦ : Φ.toOpenPartialHomeomorph.MDifferentiable 𝓘(ℝ, Fin (n + 1) → ℂ)
      𝓘(ℝ, Fin (n + 1) → ℂ) :=
    ⟨Φ.mdifferentiableOn (by simp), Φ.symm.mdifferentiableOn (by simp)⟩
  rw [isPseudoholomorphicOn_iff]
  intro y hy
  rw [blowupChart_source, ← hN.isSymplecticBallEmbedding.complexPartialDiffeomorph_target,
    ← PartialDiffeomorph.toOpenPartialHomeomorph_target] at hy
  refine IsPseudoholomorphicAt.isPseudoholomorphicWithinAt ?_
  rw [blowupChart_toOpenPartialHomeomorph]
  refine hΦ.isPseudoholomorphicAt_symm hy ?_
  have hw := Φ.toOpenPartialHomeomorph.map_target hy
  rw [PartialDiffeomorph.toOpenPartialHomeomorph_source,
    hN.isSymplecticBallEmbedding.complexPartialDiffeomorph_source] at hw
  rw [PartialDiffeomorph.toFun'_toOpenPartialHomeomorph,
    hN.isSymplecticBallEmbedding.coe_complexPartialDiffeomorph]
  exact (hN.isPseudoholomorphicOn_comp_complexToRealEuclidean.isPseudoholomorphicWithinAt hw
    ).isPseudoholomorphicAt_of_mem_nhds
    ((isOpen_ball.preimage (complexToRealEuclidean _).continuous).mem_nhds hw)

end IsNormalizedAt

end SymplecticGeometry

end
