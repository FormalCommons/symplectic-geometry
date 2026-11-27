/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Complex.Blowup.Basic
public import SymplecticGeometry.Geometry.Symplectic.Blowup.Model
public import SymplecticGeometry.Geometry.Symplectic.IsotopyExtension.Ball.Complex
public import SymplecticGeometry.LinearAlgebra.Symplectic.Standard.Basic
public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure
public import TauCeti.Geometry.Symplectic.Manifold.JHolomorphic
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Injective
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import TauCeti.Geometry.Manifold.LocalDiffeomorph.RestrictScalars

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

A normalized ball embedding (McDuff–Salamon, Definition 7.1.20) is a symplectic embedding `ψ` of
a closed ball `B(r)` that agrees with `ψ₀` on a smaller ball `B(ε)`, with a weight `l` such
that `l + ε < r`. It lifts to the blowup: the lift `ψ̃` of the neighbourhood `openNbhd n r` of the
exceptional divisor of the model is the inclusion of the model piece over `B(ε)`, where `ψ = ψ₀`,
and `inl ∘ ψ ∘ π` off the divisor, the two agreeing where both are defined. It is injective and a
local diffeomorphism at every point, so an open embedding and a partial diffeomorphism, and it
lies over `ψ`.

## Main definitions

* `SymplecticGeometry.IsNormalizedAt σ J p₀ δ ψ₀`: `ψ₀` normalizes `(σ, J)` at `p₀` on the ball
  of radius `δ`.
* `SymplecticGeometry.IsNormalizedAt.blowupChart hN`: the blowup chart at `p₀` given by the
  inverse of `ψ₀`, read on `Fin (n + 1) → ℂ`.
* `SymplecticGeometry.IsNormalizedBallEmbedding hN ψ r l ε`: `ψ` is a normalized ball embedding
  of radius `r`, weight `l` and width `ε` for the normalization `hN`.
* `SymplecticGeometry.IsNormalizedBallEmbedding.ballLift hψ`: the lift `ψ̃` of `ψ`, from
  `openNbhd n r` to the blowup, and `IsNormalizedBallEmbedding.ballLiftPartialDiffeomorph hψ`,
  the same map as a partial diffeomorphism of the model blowup with source `openNbhd n r`.

## Main results

* `SymplecticGeometry.IsNormalizedAt.isPseudoholomorphicOn_comp_complexToRealEuclidean`: read on
  `Fin (n + 1) → ℂ`, a normalization is pseudoholomorphic on the preimage of the open ball, from
  the complex structure of `Fin (n + 1) → ℂ` to `J`.
* `SymplecticGeometry.IsNormalizedAt.blowupChart_mem_maximalAtlas`: the blowup chart is in the
  smooth maximal atlas of `M`.
* `SymplecticGeometry.IsNormalizedAt.blowupChart_isHolomorphic`: the blowup chart is
  pseudoholomorphic on its source from `J` to the complex structure of `Fin (n + 1) → ℂ`.
* `SymplecticGeometry.IsNormalizedBallEmbedding.ballLift_of_mem_openNbhd`,
  `SymplecticGeometry.IsNormalizedBallEmbedding.ballLift_of_blowdown_ne_zero`: the two
  descriptions of the lift.
* `SymplecticGeometry.IsNormalizedBallEmbedding.blowdown_ballLift`: the lift lies over `ψ`.
* `SymplecticGeometry.IsNormalizedBallEmbedding.isOpenEmbedding_ballLift`: the lift is an open
  embedding.

## Implementation notes

The symplectic form is called `σ`, since `ω` is a token once the scope `ContDiff` is open. The
definition asks for `0 < δ`, without which the open ball is empty and `ψ₀` gives no chart at
`p₀`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §7.1.
-/

public section

noncomputable section

open Set Metric Topology
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

/-- The blowup chart of a normalization is in the smooth maximal atlas of `M`, as an instance,
so that the blowup along it is a smooth manifold. -/
instance fact_blowupChart_mem_maximalAtlas :
    Fact (hN.blowupChart.toOpenPartialHomeomorph ∈
      IsManifold.maximalAtlas 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ M) :=
  ⟨hN.blowupChart_mem_maximalAtlas⟩

end IsNormalizedAt

/-! ### Normalized ball embeddings and their lifts -/

/-- `ψ` is a normalized ball embedding of radius `r`, weight `l` and width `ε` for the
normalization `hN : IsNormalizedAt σ J p₀ δ ψ₀`: a symplectic embedding of the closed ball `B(r)`
with `0 < l`, `0 < ε < 1`, `l + ε < r` and `ε < δ`, which agrees with `ψ₀` on the closed ball
`B(ε)` (McDuff–Salamon, Definition 7.1.20). -/
def IsNormalizedBallEmbedding (_hN : IsNormalizedAt σ J p₀ δ ψ₀)
    (ψ : StdSpace (Fin (n + 1)) → M) (r l ε : ℝ) : Prop :=
  IsSymplecticBallEmbedding σ r ψ ∧ 0 < l ∧ 0 < ε ∧ ε < 1 ∧ l + ε < r ∧ ε < δ ∧
    EqOn ψ ψ₀ (closedBall 0 ε)

variable {hN : IsNormalizedAt σ J p₀ δ ψ₀} {ψ : StdSpace (Fin (n + 1)) → M} {r l ε : ℝ}

theorem isNormalizedBallEmbedding_def :
    IsNormalizedBallEmbedding hN ψ r l ε ↔
      IsSymplecticBallEmbedding σ r ψ ∧ 0 < l ∧ 0 < ε ∧ ε < 1 ∧ l + ε < r ∧ ε < δ ∧
        EqOn ψ ψ₀ (closedBall 0 ε) :=
  Iff.rfl

namespace IsNormalizedBallEmbedding

open BlowupModel

open GluedAlong (inl inr)

open Blowup (gluingHomeomorph)

variable (hψ : IsNormalizedBallEmbedding hN ψ r l ε)
include hψ

/-- A normalized ball embedding of radius `r` is a symplectic embedding of the closed ball
`B(r)`. -/
theorem isSymplecticBallEmbedding : IsSymplecticBallEmbedding σ r ψ := hψ.1

/-- The weight of a normalized ball embedding is positive. -/
theorem weight_pos : 0 < l := hψ.2.1

/-- The width of a normalized ball embedding is positive. -/
theorem width_pos : 0 < ε := hψ.2.2.1

/-- The width of a normalized ball embedding is less than `1`. -/
theorem width_lt_one : ε < 1 := hψ.2.2.2.1

/-- The weight and the width of a normalized ball embedding add up to less than its radius. -/
theorem weight_add_width_lt : l + ε < r := hψ.2.2.2.2.1

/-- The width of a normalized ball embedding is less than the radius `δ` of the
normalization. -/
theorem width_lt : ε < δ := hψ.2.2.2.2.2.1

/-- A normalized ball embedding agrees with the normalization on the closed ball of radius its
width. -/
theorem eqOn : EqOn ψ ψ₀ (closedBall 0 ε) := hψ.2.2.2.2.2.2

/-- The width of a normalized ball embedding is less than its radius. -/
theorem width_lt_radius : ε < r := by
  linarith [hψ.weight_pos, hψ.weight_add_width_lt]

/-- A normalized ball embedding for a normalization at `p₀` sends the origin to `p₀`. -/
theorem map_zero : ψ 0 = p₀ :=
  (hψ.eqOn (mem_closedBall_self hψ.width_pos.le)).trans hN.map_zero

/-- A normalized ball embedding of radius `r` sends no nonzero point of the closed ball `B(r)`
to `p₀`. -/
theorem apply_ne_center {z : StdSpace (Fin (n + 1))} (hz : z ∈ closedBall 0 r) (hz0 : z ≠ 0) :
    ψ z ≠ p₀ := fun h ↦
  hz0 <| hψ.isSymplecticBallEmbedding.injOn hz
    (mem_closedBall_self (hψ.width_pos.trans hψ.width_lt_radius).le)
    (h.trans hψ.map_zero.symm)

/-- On the preimage of the open ball of radius `ε`, the blowup chart inverts
`ψ ∘ complexToRealEuclidean (Fin (n + 1))`. -/
theorem blowupChart_apply {w : Fin (n + 1) → ℂ}
    (hw : ‖complexToRealEuclidean (Fin (n + 1)) w‖ < ε) :
    hN.blowupChart (ψ (complexToRealEuclidean (Fin (n + 1)) w)) = w := by
  have hwt : w ∈ hN.blowupChart.target := by
    rw [hN.blowupChart_target, mem_preimage, mem_ball_zero_iff]
    exact hw.trans hψ.width_lt
  rw [hψ.eqOn (mem_closedBall_zero_iff.2 hw.le), ← Function.comp_apply (f := ψ₀),
    ← hN.coe_blowupChart_symm]
  exact hN.blowupChart.right_inv hwt

/-- On the preimage of the open ball of radius `ε`, `ψ ∘ complexToRealEuclidean (Fin (n + 1))`
takes values in the source of the blowup chart. -/
theorem apply_mem_blowupChart_source {w : Fin (n + 1) → ℂ}
    (hw : ‖complexToRealEuclidean (Fin (n + 1)) w‖ < ε) :
    ψ (complexToRealEuclidean (Fin (n + 1)) w) ∈ hN.blowupChart.source := by
  rw [hN.blowupChart_source, hψ.eqOn (mem_closedBall_zero_iff.2 hw.le)]
  exact mem_image_of_mem _ (mem_ball_zero_iff.2 (hw.trans hψ.width_lt))

/-- A point of `openNbhd n ε` lies over the target of the blowup chart. -/
theorem mem_modelOpens {y : BlowupModel n} (hy : y ∈ openNbhd n ε) :
    y ∈ Blowup.modelOpens hN.blowupChart := by
  rw [Blowup.mem_modelOpens, hN.blowupChart_target, mem_preimage, mem_ball_zero_iff]
  exact (mem_openNbhd_iff.1 hy).trans hψ.width_lt

/-- `ψ ∘ π` sends a point of `openNbhd n r` off the exceptional divisor to a point other than
`p₀`. -/
theorem apply_blowdown_mem_puncturedOpens {y : BlowupModel n} (hy : y ∈ openNbhd n r)
    (hy0 : y.blowdown ≠ 0) :
    ψ (complexToRealEuclidean (Fin (n + 1)) y.blowdown) ∈
      Blowup.puncturedOpens hN.blowupChart := by
  rw [Blowup.mem_puncturedOpens]
  refine hψ.apply_ne_center (mem_closedBall_zero_iff.2 (mem_openNbhd_iff.1 hy).le) ?_
  rwa [Ne, map_eq_zero_iff _ (complexToRealEuclidean (Fin (n + 1))).injective]

private theorem blowdown_ne_zero_of_notMem {y : BlowupModel n} (hy : y ∉ openNbhd n ε) :
    y.blowdown ≠ 0 := fun h ↦
  hy (exceptionalDivisor_subset_openNbhd hψ.width_pos (mem_exceptionalDivisor_iff.2 h))

open scoped Classical in
/-- The lift `ψ̃` of a normalized ball embedding, from the neighbourhood `openNbhd n r` of the
exceptional divisor of the model to the blowup `Blowup hN.blowupChart`: on `openNbhd n ε` it is
the inclusion `inr` of the model piece, and elsewhere it is `inl ∘ ψ ∘ π`, for the blowdown `π`
read on `StdSpace` through `complexToRealEuclidean`. The two descriptions agree off the divisor
(`ballLift_of_blowdown_ne_zero`), since `ψ = ψ₀` on `B(ε)`. -/
def ballLift (y : openNbhd n r) : Blowup hN.blowupChart :=
  if h : (y : BlowupModel n) ∈ openNbhd n ε then
    inr (gluingHomeomorph hN.blowupChart) ⟨y, hψ.mem_modelOpens h⟩
  else
    inl (gluingHomeomorph hN.blowupChart)
      ⟨ψ (complexToRealEuclidean (Fin (n + 1)) (y : BlowupModel n).blowdown),
        hψ.apply_blowdown_mem_puncturedOpens y.property (hψ.blowdown_ne_zero_of_notMem h)⟩

/-- On `openNbhd n ε`, the lift is the inclusion of the model piece. -/
theorem ballLift_of_mem_openNbhd (y : openNbhd n r) (hy : (y : BlowupModel n) ∈ openNbhd n ε) :
    hψ.ballLift y = inr (gluingHomeomorph hN.blowupChart) ⟨y, hψ.mem_modelOpens hy⟩ :=
  dite_eq_left hy

/-- Off the exceptional divisor, the lift is `inl ∘ ψ ∘ π`. -/
theorem ballLift_of_blowdown_ne_zero (y : openNbhd n r) (hy : (y : BlowupModel n).blowdown ≠ 0) :
    hψ.ballLift y = inl (gluingHomeomorph hN.blowupChart)
      ⟨ψ (complexToRealEuclidean (Fin (n + 1)) (y : BlowupModel n).blowdown),
        hψ.apply_blowdown_mem_puncturedOpens y.property hy⟩ := by
  by_cases h : (y : BlowupModel n) ∈ openNbhd n ε
  · rw [hψ.ballLift_of_mem_openNbhd y h, Blowup.inr_eq_inl_iff]
    have hc := hψ.blowupChart_apply (mem_openNbhd_iff.1 h)
    exact ⟨hψ.apply_mem_blowupChart_source (mem_openNbhd_iff.1 h), hc⟩
  · exact dite_eq_right h

/-- The lift lies over `ψ`: the blowdown of `ψ̃ y` is `ψ` of the blowdown of `y`. -/
@[simp]
theorem blowdown_ballLift (y : openNbhd n r) :
    Blowup.blowdown hN.blowupChart (hψ.ballLift y) =
      ψ (complexToRealEuclidean (Fin (n + 1)) (y : BlowupModel n).blowdown) := by
  by_cases h : (y : BlowupModel n) ∈ openNbhd n ε
  · rw [hψ.ballLift_of_mem_openNbhd y h, Blowup.blowdown_inr, hN.coe_blowupChart_symm,
      Function.comp_apply, hψ.eqOn (mem_closedBall_zero_iff.2 (mem_openNbhd_iff.1 h).le)]
  · rw [hψ.ballLift_of_blowdown_ne_zero y (hψ.blowdown_ne_zero_of_notMem h), Blowup.blowdown_inl]

/-- The lift of a normalized ball embedding is injective. -/
theorem injective_ballLift : Function.Injective hψ.ballLift := by
  intro y y' h
  have hb : (y : BlowupModel n).blowdown = (y' : BlowupModel n).blowdown := by
    have := congrArg (Blowup.blowdown hN.blowupChart) h
    rw [hψ.blowdown_ballLift, hψ.blowdown_ballLift] at this
    exact (complexToRealEuclidean (Fin (n + 1))).injective <|
      hψ.isSymplecticBallEmbedding.injOn
        (mem_closedBall_zero_iff.2 (mem_openNbhd_iff.1 y.property).le)
        (mem_closedBall_zero_iff.2 (mem_openNbhd_iff.1 y'.property).le) this
  by_cases h0 : (y : BlowupModel n).blowdown = 0
  · have hy : (y : BlowupModel n) ∈ openNbhd n ε := by
      by_contra hy
      exact hψ.blowdown_ne_zero_of_notMem hy h0
    have hy' : (y' : BlowupModel n) ∈ openNbhd n ε := by
      by_contra hy'
      exact hψ.blowdown_ne_zero_of_notMem hy' (hb ▸ h0)
    rw [hψ.ballLift_of_mem_openNbhd y hy, hψ.ballLift_of_mem_openNbhd y' hy'] at h
    have h2 := GluedAlong.inr_injective (gluingHomeomorph hN.blowupChart) h
    rw [Subtype.mk.injEq] at h2
    exact Subtype.ext h2
  · exact Subtype.ext (eq_of_blowdown_eq h0 hb)

/-! #### The lift as a partial diffeomorphism -/

open scoped TauCeti.ComplexManifold

open scoped Classical in
/-- The lift, extended to the whole model by an arbitrary value off `openNbhd n r`. -/
private def ballLiftExt (y : BlowupModel n) : Blowup hN.blowupChart :=
  if h : y ∈ openNbhd n r then hψ.ballLift ⟨y, h⟩ else Classical.arbitrary _

private theorem ballLiftExt_of_mem {y : BlowupModel n} (h : y ∈ openNbhd n r) :
    hψ.ballLiftExt y = hψ.ballLift ⟨y, h⟩ :=
  dite_eq_left h

/-- Near a point of `openNbhd n ε`, the lift is `inr` composed with the inclusion. -/
private theorem isLocalDiffeomorphAt_ballLiftExt_of_mem {y : BlowupModel n}
    (hy : y ∈ openNbhd n ε) :
    IsLocalDiffeomorphAt 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ hψ.ballLiftExt y := by
  classical
  let g : BlowupModel n → Blowup.modelOpens hN.blowupChart := fun y' ↦
    if h : y' ∈ openNbhd n ε then ⟨y', hψ.mem_modelOpens h⟩ else ⟨y, hψ.mem_modelOpens hy⟩
  have hev : ∀ᶠ y' in 𝓝 y, y' ∈ openNbhd n ε := (isOpen_openNbhd ε).mem_nhds hy
  have hg : IsLocalDiffeomorphAt 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ g y := by
    rw [← isLocalDiffeomorphAt_subtypeVal_comp_iff]
    refine ((Diffeomorph.refl 𝓘(ℝ, Fin (n + 1) → ℂ) (BlowupModel n) ∞).isLocalDiffeomorph
      y).congr_of_eventuallyEq ?_
    filter_upwards [hev] with y' hy'
    simp only [g, dite_eq_left hy', Function.comp_apply, Diffeomorph.coe_refl, id]
  refine (IsLocalDiffeomorphAt.comp (hf := hg)
    (hg := Blowup.isLocalDiffeomorph_inr_real _ (g y))).congr_of_eventuallyEq ?_
  filter_upwards [hev] with y' hy'
  rw [hψ.ballLiftExt_of_mem (openNbhd_mono hψ.width_lt_radius.le hy'),
    hψ.ballLift_of_mem_openNbhd _ hy', Function.comp_apply]
  simp only [g, dite_eq_left hy']

/-- Near a point of `openNbhd n r` off the exceptional divisor, the lift is `inl ∘ ψ ∘ π`. -/
private theorem isLocalDiffeomorphAt_ballLiftExt_of_blowdown_ne_zero {y : BlowupModel n}
    (hy : y ∈ openNbhd n r) (hy0 : y.blowdown ≠ 0) :
    IsLocalDiffeomorphAt 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ hψ.ballLiftExt y := by
  classical
  set e := complexToRealEuclidean (Fin (n + 1))
  let U : Set (BlowupModel n) := openNbhd n r ∩ {y' | y'.blowdown ≠ 0}
  have hU : IsOpen U := (isOpen_openNbhd r).inter (isOpen_ne_fun continuous_blowdown
    continuous_const)
  have hev : ∀ᶠ y' in 𝓝 y, y' ∈ U := hU.mem_nhds ⟨hy, hy0⟩
  let g : BlowupModel n → Blowup.puncturedOpens hN.blowupChart := fun y' ↦
    if h : y' ∈ U then ⟨ψ (e y'.blowdown), hψ.apply_blowdown_mem_puncturedOpens h.1 h.2⟩
    else ⟨ψ (e y.blowdown), hψ.apply_blowdown_mem_puncturedOpens hy hy0⟩
  have hφ : IsLocalDiffeomorphAt 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) ∞
      (ψ ∘ e ∘ BlowupModel.blowdown) y := by
    have hb := ((BlowupModel.isLocalDiffeomorphAt_blowdown hy0).restrictScalars ℝ).of_le
      (m := ∞) le_top
    have hΦ := hψ.isSymplecticBallEmbedding.complexPartialDiffeomorph.isLocalDiffeomorphAt
      (hx := by simpa [e] using hy)
    rw [IsSymplecticBallEmbedding.coe_complexPartialDiffeomorph] at hΦ
    exact IsLocalDiffeomorphAt.comp (hf := hb) (hg := hΦ)
  have hg : IsLocalDiffeomorphAt 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ g y := by
    rw [← isLocalDiffeomorphAt_subtypeVal_comp_iff]
    refine hφ.congr_of_eventuallyEq ?_
    filter_upwards [hev] with y' hy'
    simp only [g, dite_eq_left hy', Function.comp_apply]
  refine (IsLocalDiffeomorphAt.comp (hf := hg)
    (hg := Blowup.isLocalDiffeomorph_inl_real _ (g y))).congr_of_eventuallyEq ?_
  filter_upwards [hev] with y' hy'
  rw [hψ.ballLiftExt_of_mem hy'.1, hψ.ballLift_of_blowdown_ne_zero _ hy'.2, Function.comp_apply]
  simp only [g, dite_eq_left hy']
  rfl

private theorem isLocalDiffeomorphOn_ballLiftExt :
    IsLocalDiffeomorphOn 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ hψ.ballLiftExt
      (openNbhd n r) := fun y ↦ by
  by_cases h : (y : BlowupModel n) ∈ openNbhd n ε
  · exact hψ.isLocalDiffeomorphAt_ballLiftExt_of_mem h
  · exact hψ.isLocalDiffeomorphAt_ballLiftExt_of_blowdown_ne_zero y.property
      (hψ.blowdown_ne_zero_of_notMem h)

private theorem injOn_ballLiftExt : InjOn hψ.ballLiftExt (openNbhd n r) := fun y hy y' hy' h ↦ by
  rw [hψ.ballLiftExt_of_mem hy, hψ.ballLiftExt_of_mem hy'] at h
  exact congrArg Subtype.val (hψ.injective_ballLift h)

/-- The lift `ψ̃` of a normalized ball embedding as a smooth partial diffeomorphism from the
model blowup to `Blowup hN.blowupChart`, with source `openNbhd n r` and target the range of
`ballLift`, which it agrees with on `openNbhd n r` (`ballLiftPartialDiffeomorph_apply`). -/
def ballLiftPartialDiffeomorph :
    PartialDiffeomorph 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) (BlowupModel n)
      (Blowup hN.blowupChart) ∞ :=
  hψ.isLocalDiffeomorphOn_ballLiftExt.partialDiffeomorphOfInjOn (isOpen_openNbhd r)
    hψ.injOn_ballLiftExt

@[simp]
theorem ballLiftPartialDiffeomorph_source :
    hψ.ballLiftPartialDiffeomorph.source = openNbhd n r :=
  IsLocalDiffeomorphOn.partialDiffeomorphOfInjOn_source ..

/-- On `openNbhd n r`, the partial diffeomorphism is the lift. -/
@[simp]
theorem ballLiftPartialDiffeomorph_apply (y : openNbhd n r) :
    hψ.ballLiftPartialDiffeomorph y = hψ.ballLift y := by
  rw [ballLiftPartialDiffeomorph, IsLocalDiffeomorphOn.coe_partialDiffeomorphOfInjOn,
    hψ.ballLiftExt_of_mem y.property]

@[simp]
theorem ballLiftPartialDiffeomorph_target :
    hψ.ballLiftPartialDiffeomorph.target = range hψ.ballLift := by
  rw [ballLiftPartialDiffeomorph, IsLocalDiffeomorphOn.partialDiffeomorphOfInjOn_target,
    ← Set.range_domRestrict]
  exact congrArg range (funext fun y ↦ hψ.ballLiftExt_of_mem y.property)

/-- The lift of a normalized ball embedding is an open embedding of `openNbhd n r` into the
blowup. -/
theorem isOpenEmbedding_ballLift : IsOpenEmbedding hψ.ballLift := by
  have h := hψ.ballLiftPartialDiffeomorph.toOpenPartialHomeomorph.isOpenEmbedding_restrict
  have hs : hψ.ballLiftPartialDiffeomorph.toOpenPartialHomeomorph.source = openNbhd n r :=
    hψ.ballLiftPartialDiffeomorph_source
  rw [hs] at h
  convert h using 1
  ext y
  exact (hψ.ballLiftPartialDiffeomorph_apply y).symm

end IsNormalizedBallEmbedding

end SymplecticGeometry

end
