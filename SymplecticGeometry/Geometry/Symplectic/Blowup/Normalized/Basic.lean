/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Complex.Blowup.AlmostComplex
public import SymplecticGeometry.Geometry.Manifold.Complex.Blowup.Basic
public import SymplecticGeometry.Geometry.Symplectic.Blowup.Model
public import SymplecticGeometry.Geometry.Symplectic.Blowup.Profile
public import SymplecticGeometry.Geometry.Symplectic.IsotopyExtension.Ball.Complex
public import SymplecticGeometry.LinearAlgebra.Symplectic.Standard.Basic
public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure
public import TauCeti.Geometry.Symplectic.Manifold.JHolomorphic
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import SymplecticGeometry.Geometry.Symplectic.Manifold.AlmostComplex.Chart
import SymplecticGeometry.Geometry.Symplectic.Manifold.AlmostComplex.Pseudoholomorphic
import SymplecticGeometry.Geometry.Symplectic.Manifold.Darboux
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Injective
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import TauCeti.Geometry.Manifold.LocalDiffeomorph.RestrictScalars
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Opens
import SymplecticGeometry.Geometry.Symplectic.Manifold.Opens
import SymplecticGeometry.Geometry.Symplectic.Manifold.SymplecticMap
import TauCeti.Geometry.Manifold.DifferentialForm.Opens.PartialDiffeomorph

/-!
# Normalized ball embeddings, their blowup charts and the forms of the blowup

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

The lift carries the forms of the model to the blowup. For a profile `h` of the blowup of weight
`l` with collar `ε`, the form `ω̃_{ψ,l,ε}` of the blowup is the push-forward by `ψ̃` of the form
`ω̃_{l,ε} = profileForm n l ε h` on the image of `ψ̃`, and the pull-back of `σ` by the blowdown
off the image under `ψ̃` of `closedNbhd n (l + ε)`. On the overlap `ω̃_{l,ε}` is the pull-back of
`ω₀` by the blowdown of the model, and `ψ` pulls `σ` back to `ω₀`, so the two descriptions
agree. On the image of `closedNbhd n ε` the form is the push-forward of `ω̃_l = blowupForm n l`
(McDuff–Salamon, Theorem 7.1.21 (i)). If moreover `ψ` is pseudoholomorphic from `J₀` to `J`
at every point of the closed ball `B(l + ε)`, the form is compatible with the almost complex blowup
`J̃ = Blowup.almostComplexStructure` of `J` (Theorem 7.1.21 (iv)): on the image of `L(l + ε)`
the lift is `J̃`-holomorphic, and elsewhere the form and `J̃` are the pull-backs of `σ` and `J` by
the blowdown.

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
* `SymplecticGeometry.IsNormalizedBallEmbedding.normalizedBlowupForm hψ h`: the form `ω̃_{ψ,l,ε}`
  of the blowup, for a profile `h` that defaults to `blowupProfile l ε`.

## Main results

* `SymplecticGeometry.IsNormalizedAt.isPseudoholomorphicOn_comp_complexToRealEuclidean`: read on
  `Fin (n + 1) → ℂ`, a normalization is pseudoholomorphic on the preimage of the open ball, from
  the complex structure of `Fin (n + 1) → ℂ` to `J`.
* `SymplecticGeometry.IsNormalizedAt.blowupChart_mem_maximalAtlas`: the blowup chart is in the
  smooth maximal atlas of `M`.
* `SymplecticGeometry.IsNormalizedAt.blowupChart_isHolomorphic`: the blowup chart is
  pseudoholomorphic on its source from `J` to the complex structure of `Fin (n + 1) → ℂ`.
* `SymplecticGeometry.exists_isNormalizedAt`: on a Hausdorff σ-compact manifold, a symplectic
  form is normalized at every point, for some compatible `J`, radius and map. The map is the
  inverse of a Darboux chart onto `StdSpace (Fin (n + 1))`
  (`TauCeti.SmoothTwoForm.IsSymplectic.exists_darbouxChart_stdForm`), restricted to a closed ball
  in its target; `J` is a compatible structure that the derivative of the chart carries to `J₀`
  on the image of that ball
  (`TauCeti.SmoothTwoForm.IsNondegenerate.exists_compatible_mfderiv_apply_eq`, which rests on Tau
  Ceti's `TauCeti.SmoothTwoForm.Compatible.exists_compatible_eqOn`). This is McDuff–Salamon,
  Remark 7.1.18 (i).
* `SymplecticGeometry.IsNormalizedBallEmbedding.ballLift_of_mem_openNbhd`,
  `SymplecticGeometry.IsNormalizedBallEmbedding.ballLift_of_blowdown_ne_zero`: the two
  descriptions of the lift.
* `SymplecticGeometry.IsNormalizedBallEmbedding.blowdown_ballLift`: the lift lies over `ψ`.
* `SymplecticGeometry.IsNormalizedBallEmbedding.isOpenEmbedding_ballLift`: the lift is an open
  embedding.
* `SymplecticGeometry.IsNormalizedBallEmbedding.isLocalDiffeomorph_ballLift`,
  `SymplecticGeometry.IsNormalizedBallEmbedding.contMDiff_ballLift`: on `openNbhdOpens n r`, the
  lift is a local diffeomorphism, and so smooth.
* `SymplecticGeometry.IsNormalizedBallEmbedding.normalizedBlowupForm_eq_on_ballLift`,
  `SymplecticGeometry.IsNormalizedBallEmbedding.normalizedBlowupForm_eq_on_compl`: the two
  descriptions of `ω̃_{ψ,l,ε}`; by
  `SymplecticGeometry.IsNormalizedBallEmbedding.eq_normalizedBlowupForm`, they determine it.
* `SymplecticGeometry.IsNormalizedBallEmbedding.normalizedBlowupForm_eq_blowupForm_on`: near the
  exceptional divisor, the lift pulls `ω̃_{ψ,l,ε}` back to `ω̃_l`.
* `SymplecticGeometry.IsNormalizedBallEmbedding.isSymplectic_normalizedBlowupForm`: for symplectic
  `σ`, the form `ω̃_{ψ,l,ε}` is symplectic.
* `SymplecticGeometry.IsNormalizedBallEmbedding.exists_mextDeriv_eq_normalizedBlowupForm_sub`:
  the forms of two profiles of the same weight and collar differ by `d β`, for a one-form `β`
  that vanishes off the image of `closedNbhd n (l + ε)`. It is the push-forward of the primitive
  on the model, `BlowupModel.exists_mextDeriv_eq_profileForm_sub`, glued with `0` as
  `ω̃_{ψ,l,ε}` is glued with the pull-back of `σ`; Moser's argument for two profiles uses it.
* `SymplecticGeometry.IsNormalizedBallEmbedding.isPseudoholomorphicAt_ballLiftPartialDiffeomorph`:
  the lift is pseudoholomorphic, from the complex structure of the model to `J̃`, at each point of
  `openNbhd n r` over which `ψ` is pseudoholomorphic from `J₀` to `J`.
* `SymplecticGeometry.IsNormalizedBallEmbedding.compatible_normalizedBlowupForm`: if `ψ` is
  pseudoholomorphic from `J₀` to `J` on `B(l + ε)`, the form `ω̃_{ψ,l,ε}` is compatible with `J̃`.

## Implementation notes

The symplectic form is called `σ`, since `ω` is a token once the scope `ContDiff` is open. The
definition asks for `0 < δ`, without which the open ball is empty and `ψ₀` gives no chart at
`p₀`.

The form `ω̃_{ψ,l,ε}` is glued by `SmoothForm.exists_forall_eq_and_mpullback_subtype_val_eq`, which
glues a form on the blowup, here the pull-back of `σ` by the blowdown, with a form on an open
subset, here the image of the lift; the forms are compared through Tau Ceti's
`SmoothForm.mpullback_toDiffeomorphSourceTarget_eq_iff`. The image of `closedNbhd n (l + ε)` is
compact, so closed since `M`, and hence the blowup, is Hausdorff. If `h` is not a profile of the
blowup, `normalizedBlowupForm hψ h` is the pull-back of `σ` by the blowdown.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §7.1,
  Definition 7.1.17, Remark 7.1.18 and Theorem 7.1.21.
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
  rw [blowupChart_source] at hy
  have hw : Φ.symm y ∈ complexToRealEuclidean (Fin (n + 1)) ⁻¹' ball 0 δ :=
    mem_ball_zero_iff.2 (hN.isSymplecticBallEmbedding.norm_complexPartialDiffeomorph_symm_lt hy)
  rw [← hN.isSymplecticBallEmbedding.complexPartialDiffeomorph_target,
    ← PartialDiffeomorph.toOpenPartialHomeomorph_target] at hy
  refine IsPseudoholomorphicAt.isPseudoholomorphicWithinAt ?_
  rw [blowupChart_toOpenPartialHomeomorph]
  refine hΦ.isPseudoholomorphicAt_symm hy ?_
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

/-- **Every symplectic manifold is normalized at every point.** Let `σ` be a symplectic form on
a Hausdorff σ-compact manifold `M` modelled on `Fin (n + 1) → ℂ`. At every point `p₀` there are
an almost complex structure `J` compatible with `σ`, a radius `δ > 0` and a map `ψ₀` that
normalizes `(σ, J)` at `p₀` on the ball of radius `δ`. The form `σ` itself is not changed. -/
theorem exists_isNormalizedAt [T2Space M] [SigmaCompactSpace M] (hσ : σ.IsSymplectic) (p₀ : M) :
    ∃ (J : SmoothAlmostComplexStructure 𝓘(ℝ, Fin (n + 1) → ℂ) M) (δ : ℝ)
      (ψ₀ : StdSpace (Fin (n + 1)) → M), IsNormalizedAt σ J p₀ δ ψ₀ := by
  have hE : Module.finrank ℝ (Fin (n + 1) → ℂ) = 2 * Fintype.card (Fin (n + 1)) := by
    simp [Module.finrank_pi_fintype, mul_comm]
  -- A Darboux chart `χ` onto `StdSpace (Fin (n + 1))` centred at `p₀`, and a closed ball `B(δ)`
  -- inside its target. The inverse of `χ` is a symplectic embedding of `B(δ)`.
  obtain ⟨χ, hp, -, hp0, hχ⟩ := hσ.exists_darbouxChart_stdForm hE (s := univ) Filter.univ_mem
  obtain ⟨ε, hε, hεt⟩ := isOpen_iff.1 χ.open_target 0 (hp0 ▸ χ.map_source hp)
  have hδt : closedBall (0 : StdSpace (Fin (n + 1))) (ε / 2) ⊆ χ.target :=
    (closedBall_subset_ball (by linarith)).trans hεt
  have hψ : IsSymplecticBallEmbedding σ (ε / 2) χ.symm := (isSymplecticBallEmbedding_def _ _ _).2
    ⟨⟨χ.target, χ.open_target, hδt, χ.symm.contMDiffOn⟩, χ.symm.injOn.mono hδt,
      fun z hz ↦ SmoothTwoForm.mpullback_symm_apply_eq_constSmooth hχ
        (hδt (ball_subset_closedBall hz))⟩
  -- A compatible `J` that `dχ` carries to `J₀` on the image of `B(δ)`.
  obtain ⟨J, hJ, hJχ⟩ := hσ.isNondegenerate.exists_compatible_mfderiv_apply_eq hχ
    stdForm_compatible (hψ.isCompact_image_closedBall le_rfl).isClosed
    (by rintro _ ⟨z, hz, rfl⟩; exact χ.map_target (hδt hz))
  refine ⟨J, ε / 2, χ.symm, hJ, by positivity, hψ, by rw [← hp0]; exact χ.left_inv hp,
    isPseudoholomorphicOn_iff.2 fun z hz ↦ ?_⟩
  have hzt := hδt (ball_subset_closedBall hz)
  refine ((χ.toOpenPartialHomeomorph_mdifferentiable (by simp)).isPseudoholomorphicAt_symm hzt
    (isPseudoholomorphicAt_iff_mfderiv.2 ⟨χ.mdifferentiableAt (by simp) (χ.map_target hzt),
      fun w ↦ (hJχ _ ⟨z, ball_subset_closedBall hz, rfl⟩ w).trans
        (AlmostComplexStructure.constSmooth_apply _ _ _).symm⟩)).isPseudoholomorphicWithinAt

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

/-- A normalized ball embedding of width `ε` is pseudoholomorphic, from the constant standard
complex structure `J₀` to `J`, at every point of the open ball `B°(ε)`. -/
theorem isPseudoholomorphicAt {z : StdSpace (Fin (n + 1))} (hz : z ∈ ball 0 ε) :
    IsPseudoholomorphicAt (stdComplexStructure (Fin (n + 1))).constSmooth J ψ z := by
  have hzδ : z ∈ ball 0 δ := ball_subset_ball hψ.width_lt.le hz
  refine ((hN.isPseudoholomorphicOn.isPseudoholomorphicWithinAt
    hzδ).isPseudoholomorphicAt_of_mem_nhds (isOpen_ball.mem_nhds hzδ)).congr_of_eventuallyEq ?_
  filter_upwards [isOpen_ball.mem_nhds hz] with w hw
  exact hψ.eqOn (ball_subset_closedBall hw)

/-- The width of a normalized ball embedding is less than its radius. -/
theorem width_lt_radius : ε < r := by
  linarith [hψ.weight_pos, hψ.weight_add_width_lt]

/-- A normalized ball embedding of width `ε` stays normalized, with the same radius, for any
positive width `ε' ≤ ε` and any positive weight `l'` with `l' + ε' < r`. -/
theorem of_width_le {l' ε' : ℝ} (hl' : 0 < l') (hε' : 0 < ε') (hε'ε : ε' ≤ ε)
    (hr : l' + ε' < r) : IsNormalizedBallEmbedding hN ψ r l' ε' :=
  isNormalizedBallEmbedding_def.2 ⟨hψ.isSymplecticBallEmbedding, hl', hε',
    hε'ε.trans_lt hψ.width_lt_one, hr, hε'ε.trans_lt hψ.width_lt,
    hψ.eqOn.mono (closedBall_subset_closedBall hε'ε)⟩

/-- A normalized ball embedding for a normalization at `p₀` sends the origin to `p₀`. -/
theorem map_zero : ψ 0 = p₀ :=
  (hψ.eqOn (mem_closedBall_self hψ.width_pos.le)).trans hN.map_zero

/-- A normalized ball embedding of radius `r` sends no nonzero point of the closed ball `B(r)`
to `p₀`. -/
theorem apply_ne_center {z : StdSpace (Fin (n + 1))} (hz : z ∈ closedBall 0 r) (hz0 : z ≠ 0) :
    ψ z ≠ p₀ :=
  hψ.map_zero ▸ hψ.isSymplecticBallEmbedding.apply_ne_apply_zero hz hz0

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

/-- The exceptional divisor of the blowup lies in the image under the lift of `openNbhd n ε`. -/
theorem exceptionalDivisor_subset_image_openNbhd :
    Blowup.exceptionalDivisor hN.blowupChart ⊆
      hψ.ballLiftPartialDiffeomorph '' openNbhd n ε := by
  intro z hz
  obtain ⟨y, hy0, rfl⟩ := (Blowup.mem_exceptionalDivisor_iff _).1 hz
  have hy : (y : BlowupModel n) ∈ openNbhd n ε :=
    exceptionalDivisor_subset_openNbhd hψ.width_pos (mem_exceptionalDivisor_iff.2 hy0)
  refine ⟨y, hy, ?_⟩
  rw [hψ.ballLiftPartialDiffeomorph_apply ⟨y, openNbhd_mono hψ.width_lt_radius.le hy⟩,
    hψ.ballLift_of_mem_openNbhd _ hy]

/-- The exceptional divisor of the blowup lies in the image of the lift. -/
theorem exceptionalDivisor_subset_ballLiftPartialDiffeomorph_target :
    Blowup.exceptionalDivisor hN.blowupChart ⊆ hψ.ballLiftPartialDiffeomorph.target := by
  refine hψ.exceptionalDivisor_subset_image_openNbhd.trans ?_
  rintro _ ⟨y, hy, rfl⟩
  exact hψ.ballLiftPartialDiffeomorph.map_source (by
    rw [ballLiftPartialDiffeomorph_source]; exact openNbhd_mono hψ.width_lt_radius.le hy)

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

/-- The lift of a normalized ball embedding, read on the open subset `openNbhdOpens n r` of the
model blowup, is a local diffeomorphism into the blowup. -/
theorem isLocalDiffeomorph_ballLift :
    IsLocalDiffeomorph 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) ∞
      fun y : openNbhdOpens n r ↦ hψ.ballLift ⟨y, mem_openNbhdOpens_iff.1 y.property⟩ := by
  intro y
  have hΦ : IsLocalDiffeomorphAt 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) ∞
      hψ.ballLiftPartialDiffeomorph y :=
    hψ.ballLiftPartialDiffeomorph.isLocalDiffeomorphAt (hx := by
      rw [ballLiftPartialDiffeomorph_source]; exact mem_openNbhdOpens_iff.1 y.property)
  refine (IsLocalDiffeomorphAt.comp (hf := isLocalDiffeomorph_subtype_val y) (hg := hΦ))
    |>.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x ↦ ?_)
  exact (hψ.ballLiftPartialDiffeomorph_apply ⟨x, mem_openNbhdOpens_iff.1 x.property⟩).symm

/-- The lift of a normalized ball embedding, read on the open subset `openNbhdOpens n r` of the
model blowup, is smooth. -/
theorem contMDiff_ballLift :
    ContMDiff 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) ∞
      fun y : openNbhdOpens n r ↦ hψ.ballLift ⟨y, mem_openNbhdOpens_iff.1 y.property⟩ :=
  hψ.isLocalDiffeomorph_ballLift.contMDiff

/-! #### The forms `ω̃_{ψ,l,ε}` -/

open TopologicalSpace

attribute [local instance high] IsManifold.instOfNatWithTopENat_1

/-- The closed neighbourhood `closedNbhd n a` of the divisor lies in the source `openNbhd n r` of
the lift for `a < r`. -/
private theorem closedNbhd_subset_source {a : ℝ} (ha : a < r) :
    closedNbhd n a ⊆ hψ.ballLiftPartialDiffeomorph.source :=
  hψ.ballLiftPartialDiffeomorph_source ▸ closedNbhd_subset_openNbhd ha

/-- The source `openNbhd n r` of the lift, as an open subset of the model. -/
private abbrev sourceOpens : Opens (BlowupModel n) :=
  ⟨hψ.ballLiftPartialDiffeomorph.source, hψ.ballLiftPartialDiffeomorph.open_source⟩

/-- The image of the lift, as an open subset of the blowup. -/
private abbrev targetOpens : Opens (Blowup hN.blowupChart) :=
  ⟨hψ.ballLiftPartialDiffeomorph.target, hψ.ballLiftPartialDiffeomorph.open_target⟩

/-- The lift pulls back the pull-back of `σ` by the blowdown of `Blowup hN.blowupChart` to the
pull-back of `ω₀` by the blowdown of the model, on the source of the lift, read as a
diffeomorphism onto its image. This holds since the lift lies over `ψ`, and `ψ` pulls `σ` back to
`ω₀` on the ball `B(r)`. -/
private theorem mpullback_toDiffeomorphSourceTarget_blowdown :
    SmoothForm.mpullback hψ.ballLiftPartialDiffeomorph.toDiffeomorphSourceTarget
        hψ.ballLiftPartialDiffeomorph.toDiffeomorphSourceTarget.contMDiff
        (SmoothForm.mpullback (Subtype.val : hψ.targetOpens → Blowup hN.blowupChart)
            contMDiff_subtypeVal
          (SmoothForm.mpullback (Blowup.blowdown hN.blowupChart)
            (Blowup.contMDiff_blowdown_real _) σ)) =
      SmoothForm.mpullback (Subtype.val : hψ.sourceOpens → BlowupModel n) contMDiff_subtypeVal
        (SmoothForm.mpullback blowdown ((contMDiff_blowdown ∞).restrictScalars' ℝ) (ω₀E n)) := by
  set Φ := hψ.ballLiftPartialDiffeomorph
  set Ψ := hψ.isSymplecticBallEmbedding.complexPartialDiffeomorph
  refine (SmoothForm.mpullback_toDiffeomorphSourceTarget_eq_iff Φ).2 fun y hΦy ↦ ?_
  have hy : y ∈ openNbhd n r := by rwa [ballLiftPartialDiffeomorph_source] at hΦy
  have hg : (y : BlowupModel n).blowdown ∈ Ψ.source := by
    rw [hψ.isSymplecticBallEmbedding.mem_complexPartialDiffeomorph_source_iff]
    exact mem_openNbhd_iff.1 hy
  have hfun : Blowup.blowdown hN.blowupChart ∘ Φ =ᶠ[𝓝 y] Ψ ∘ blowdown :=
    Filter.eventuallyEq_of_mem ((isOpen_openNbhd r).mem_nhds hy) fun y' hy' ↦ by
      simp only [Function.comp_apply, Ψ, IsSymplecticBallEmbedding.coe_complexPartialDiffeomorph]
      rw [show Φ y' = hψ.ballLift ⟨y', hy'⟩ from hψ.ballLiftPartialDiffeomorph_apply ⟨y', hy'⟩,
        blowdown_ballLift]
  have hΦ := Φ.mdifferentiableAt (by simp) hΦy
  have hΨ := Ψ.mdifferentiableAt (by simp) hg
  simp only [SmoothForm.coe_mpullback]
  rw [← mpullback_comp_at hΦ ((Blowup.contMDiff_blowdown_real _).mdifferentiableAt (by simp)),
    hfun.mpullback_eq,
    mpullback_comp_at (((contMDiff_blowdown ∞).restrictScalars' ℝ).mdifferentiableAt (by simp)) hΨ]
  exact mpullback_apply_congr ((ω₀E_def n ▸
    hψ.isSymplecticBallEmbedding.isSymplecticMapOn_complexPartialDiffeomorph).mpullback_apply hg)

variable [T2Space M]

/-- The complement of the image under the lift of `L(l + ε) = closedNbhd n (l + ε)`, an open
subset of the blowup. -/
private def outerOpens : Opens (Blowup hN.blowupChart) :=
  ⟨(hψ.ballLiftPartialDiffeomorph '' closedNbhd n (l + ε))ᶜ,
    ((isCompact_closedNbhd _).image_of_continuousOn
      (hψ.ballLiftPartialDiffeomorph.contMDiffOn.continuousOn.mono
        (hψ.closedNbhd_subset_source hψ.weight_add_width_lt))).isClosed.isOpen_compl⟩

/-- The complement of the image of `closedNbhd n (l + ε)` under the lift and the image of the lift
cover the blowup. -/
private theorem outerOpens_union_targetOpens :
    (hψ.outerOpens : Set (Blowup hN.blowupChart)) ∪ hψ.targetOpens = univ := by
  refine eq_univ_of_forall fun x ↦ ?_
  by_contra hx
  simp only [mem_union, not_or, SetLike.mem_coe, outerOpens, Opens.mem_mk, mem_compl_iff,
    not_not] at hx
  obtain ⟨y, hy, rfl⟩ := hx.1
  exact hx.2 (hψ.ballLiftPartialDiffeomorph.map_source
    (hψ.closedNbhd_subset_source hψ.weight_add_width_lt hy))

omit [T2Space M] in
/-- The lift maps the inverse of its restriction to its source and image, at a point `x` of the
image, back to `x`. -/
private theorem ballLiftPartialDiffeomorph_toDiffeomorphSourceTarget_symm (x : hψ.targetOpens) :
    hψ.ballLiftPartialDiffeomorph
      (hψ.ballLiftPartialDiffeomorph.toDiffeomorphSourceTarget.symm x) = x := by
  rw [PartialDiffeomorph.toDiffeomorphSourceTarget_symm_apply_coe]
  exact hψ.ballLiftPartialDiffeomorph.right_inv x.property

/-- The pull-back of `σ` by the blowdown, off the image of `closedNbhd n (l + ε)`, and the
push-forward of `ω̃_{l,ε}` by the lift, on its image, glue to a two-form on the blowup. -/
private theorem exists_normalizedBlowupForm {h : ℝ → ℝ} (hh : IsBlowupProfile l ε h) :
    ∃ τ : SmoothTwoForm 𝓘(ℝ, Fin (n + 1) → ℂ) (Blowup hN.blowupChart),
      (∀ x ∈ (hψ.outerOpens : Set (Blowup hN.blowupChart)), τ.val x =
        (SmoothForm.mpullback (Blowup.blowdown hN.blowupChart)
          (Blowup.contMDiff_blowdown_real _) σ).val x) ∧
      SmoothForm.mpullback (Subtype.val : hψ.targetOpens → Blowup hN.blowupChart)
          contMDiff_subtypeVal τ =
        SmoothForm.mpullback hψ.ballLiftPartialDiffeomorph.toDiffeomorphSourceTarget.symm
          hψ.ballLiftPartialDiffeomorph.toDiffeomorphSourceTarget.symm.contMDiff
          (SmoothForm.mpullback (Subtype.val : hψ.sourceOpens → BlowupModel n) contMDiff_subtypeVal
            (profileForm n l ε h)) := by
  set Φ := hψ.ballLiftPartialDiffeomorph
  set D := Φ.toDiffeomorphSourceTarget
  refine SmoothForm.exists_forall_eq_and_mpullback_subtype_val_eq hψ.outerOpens.isOpen
    hψ.outerOpens_union_targetOpens _ _ fun x hx ↦ ?_
  · have hD := hψ.mpullback_toDiffeomorphSourceTarget_blowdown
    set η := SmoothForm.mpullback (Blowup.blowdown hN.blowupChart)
      (Blowup.contMDiff_blowdown_real _) σ
    rw [← SmoothForm.coe_mpullback_subtype_val_apply η x, ← SmoothForm.mpullback_symm_mpullback D
      (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal η), hD]
    simp only [SmoothForm.coe_mpullback]
    ext v
    simp only [TauCeti.mpullback_apply, mpullback_subtype_val_apply]
    congr 1
    rw [← SmoothForm.coe_mpullback]
    exact profileForm_eq_on_compl n hh _ fun hK ↦
      hx ⟨_, hK, hψ.ballLiftPartialDiffeomorph_toDiffeomorphSourceTarget_symm x⟩

open scoped Classical in
/-- **The form `ω̃_{ψ,l,ε}` of the blowup** (McDuff–Salamon, §7.1), for a profile `h` of the
blowup of weight `l` with collar `ε`, by default `blowupProfile l ε`: the two-form on
`Blowup hN.blowupChart` that the lift `ψ̃` pulls back to `ω̃_{l,ε} = profileForm n l ε h` on
`openNbhd n r` (`normalizedBlowupForm_eq_on_ballLift`), and that is the pull-back of `σ` by the
blowdown off the image under `ψ̃` of `L(l + ε) = closedNbhd n (l + ε)`
(`normalizedBlowupForm_eq_on_compl`). The two agree where both apply, since `ω̃_{l,ε}` is the
pull-back of `ω₀` off `L(l + ε)` and `ψ` pulls `σ` back to `ω₀`, and the two open sets cover the
blowup; `eq_normalizedBlowupForm` says that these properties determine the form. If `h` is not a
profile of the blowup, the form is the pull-back of `σ` by the blowdown. -/
def normalizedBlowupForm (h : ℝ → ℝ := blowupProfile l ε) :
    SmoothTwoForm 𝓘(ℝ, Fin (n + 1) → ℂ) (Blowup hN.blowupChart) :=
  if hh : IsBlowupProfile l ε h then (hψ.exists_normalizedBlowupForm hh).choose
  else SmoothForm.mpullback (Blowup.blowdown hN.blowupChart) (Blowup.contMDiff_blowdown_real _) σ

omit [T2Space M] in
/-- A two-form on the blowup that the lift pulls back to `ω̃_{l,ε}` on `openNbhd n r` restricts,
on the image of the lift, to the push-forward of `ω̃_{l,ε}`. -/
private theorem mpullback_subtypeVal_eq_of_eq_on_ballLift {h : ℝ → ℝ}
    {α : SmoothTwoForm 𝓘(ℝ, Fin (n + 1) → ℂ) (Blowup hN.blowupChart)}
    (hα : ∀ y ∈ openNbhd n r, TauCeti.mpullback 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ)
      hψ.ballLiftPartialDiffeomorph α.val y = (profileForm n l ε h).val y) :
    SmoothForm.mpullback (Subtype.val : hψ.targetOpens → Blowup hN.blowupChart)
        contMDiff_subtypeVal α =
      SmoothForm.mpullback hψ.ballLiftPartialDiffeomorph.toDiffeomorphSourceTarget.symm
        hψ.ballLiftPartialDiffeomorph.toDiffeomorphSourceTarget.symm.contMDiff
        (SmoothForm.mpullback (Subtype.val : hψ.sourceOpens → BlowupModel n) contMDiff_subtypeVal
          (profileForm n l ε h)) := by
  rw [← (SmoothForm.mpullback_toDiffeomorphSourceTarget_eq_iff _).2 fun y hy ↦
    hα y (by rwa [ballLiftPartialDiffeomorph_source] at hy), SmoothForm.mpullback_symm_mpullback]

/-- The two properties that define `ω̃_{ψ,l,ε}`, for a profile of the blowup. -/
private theorem normalizedBlowupForm_choose_spec {h : ℝ → ℝ} (hh : IsBlowupProfile l ε h) :
    (∀ x ∈ (hψ.outerOpens : Set (Blowup hN.blowupChart)), (hψ.normalizedBlowupForm h).val x =
        (SmoothForm.mpullback (Blowup.blowdown hN.blowupChart)
          (Blowup.contMDiff_blowdown_real _) σ).val x) ∧
      SmoothForm.mpullback (Subtype.val : hψ.targetOpens → Blowup hN.blowupChart)
          contMDiff_subtypeVal
          (hψ.normalizedBlowupForm h) =
        SmoothForm.mpullback hψ.ballLiftPartialDiffeomorph.toDiffeomorphSourceTarget.symm
          hψ.ballLiftPartialDiffeomorph.toDiffeomorphSourceTarget.symm.contMDiff
          (SmoothForm.mpullback (Subtype.val : hψ.sourceOpens → BlowupModel n) contMDiff_subtypeVal
            (profileForm n l ε h)) := by
  rw [normalizedBlowupForm, dite_eq_left hh]
  exact (hψ.exists_normalizedBlowupForm hh).choose_spec

/-- The lift `ψ̃` pulls `ω̃_{ψ,l,ε}` back to `ω̃_{l,ε} = profileForm n l ε h` on `openNbhd n r`. -/
theorem normalizedBlowupForm_eq_on_ballLift {h : ℝ → ℝ} (hh : IsBlowupProfile l ε h) :
    ∀ y ∈ openNbhd n r, TauCeti.mpullback 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ)
      hψ.ballLiftPartialDiffeomorph (hψ.normalizedBlowupForm h).val y =
        (profileForm n l ε h).val y := by
  intro y hy
  refine (SmoothForm.mpullback_toDiffeomorphSourceTarget_eq_iff _).1 ?_ y
    (by rwa [ballLiftPartialDiffeomorph_source])
  rw [(hψ.normalizedBlowupForm_choose_spec hh).2, SmoothForm.mpullback_mpullback_symm]

/-- Unless `h` is a profile of the blowup of weight `l` with collar `ε`, the form
`hψ.normalizedBlowupForm h` is the pull-back of `σ` by the blowdown. -/
theorem normalizedBlowupForm_of_not {h : ℝ → ℝ} (hh : ¬IsBlowupProfile l ε h) :
    hψ.normalizedBlowupForm h =
      SmoothForm.mpullback (Blowup.blowdown hN.blowupChart)
        (Blowup.contMDiff_blowdown_real _) σ := by
  rw [normalizedBlowupForm, dite_eq_right hh]

/-- Off the image under the lift `ψ̃` of `L(l + ε) = closedNbhd n (l + ε)`, the form
`hψ.normalizedBlowupForm h` is the pull-back of `σ` by the blowdown. -/
theorem normalizedBlowupForm_eq_on_compl {h : ℝ → ℝ} :
    ∀ x ∉ hψ.ballLiftPartialDiffeomorph '' closedNbhd n (l + ε),
      (hψ.normalizedBlowupForm h).val x =
        (SmoothForm.mpullback (Blowup.blowdown hN.blowupChart)
          (Blowup.contMDiff_blowdown_real _) σ).val x := fun x hx ↦ by
  by_cases hh : IsBlowupProfile l ε h
  · exact (hψ.normalizedBlowupForm_choose_spec hh).1 x hx
  · rw [hψ.normalizedBlowupForm_of_not hh]

/-- **Uniqueness of `ω̃_{ψ,l,ε}`.** A two-form on the blowup that the lift `ψ̃` pulls back to
`ω̃_{l,ε}` on `openNbhd n r`, and that is the pull-back of `σ` by the blowdown off the image under
`ψ̃` of `L(l + ε)`, is `ω̃_{ψ,l,ε}`. -/
theorem eq_normalizedBlowupForm {h : ℝ → ℝ} (hh : IsBlowupProfile l ε h)
    {α : SmoothTwoForm 𝓘(ℝ, Fin (n + 1) → ℂ) (Blowup hN.blowupChart)}
    (hα : ∀ y ∈ openNbhd n r, TauCeti.mpullback 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ)
      hψ.ballLiftPartialDiffeomorph α.val y = (profileForm n l ε h).val y)
    (hα' : ∀ x ∉ hψ.ballLiftPartialDiffeomorph '' closedNbhd n (l + ε),
      α.val x = (SmoothForm.mpullback (Blowup.blowdown hN.blowupChart)
        (Blowup.contMDiff_blowdown_real _) σ).val x) :
    α = hψ.normalizedBlowupForm h := by
  refine Subtype.ext (funext fun x ↦ ?_)
  by_cases hx : x ∈ hψ.ballLiftPartialDiffeomorph.target
  · have h₁ := hψ.mpullback_subtypeVal_eq_of_eq_on_ballLift hα
    rw [← hψ.mpullback_subtypeVal_eq_of_eq_on_ballLift
      (hψ.normalizedBlowupForm_eq_on_ballLift hh)] at h₁
    have h₂ := congrArg (fun β : SmoothTwoForm 𝓘(ℝ, Fin (n + 1) → ℂ) hψ.targetOpens ↦ β.val ⟨x,
        hx⟩) h₁
    exact (SmoothForm.coe_mpullback_subtype_val_apply α ⟨x, hx⟩).symm.trans
      (h₂.trans (SmoothForm.coe_mpullback_subtype_val_apply _ ⟨x, hx⟩))
  · have hK : x ∉ hψ.ballLiftPartialDiffeomorph '' closedNbhd n (l + ε) := fun ⟨y, hy, hyx⟩ ↦
      hx (hyx ▸ hψ.ballLiftPartialDiffeomorph.map_source
        (hψ.closedNbhd_subset_source hψ.weight_add_width_lt hy))
    exact (hα' x hK).trans (hψ.normalizedBlowupForm_eq_on_compl x hK).symm

/-- On `L(ε) = closedNbhd n ε`, the lift `ψ̃` pulls `ω̃_{ψ,l,ε}` back to the form
`ω̃_l = blowupForm n l` of the model (McDuff–Salamon, Theorem 7.1.21 (i)). -/
theorem normalizedBlowupForm_eq_blowupForm_on {h : ℝ → ℝ} (hh : IsBlowupProfile l ε h) :
    ∀ y ∈ closedNbhd n ε, TauCeti.mpullback 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ)
      hψ.ballLiftPartialDiffeomorph (hψ.normalizedBlowupForm h).val y =
        (blowupForm n l).val y := fun y hy ↦ by
  rw [hψ.normalizedBlowupForm_eq_on_ballLift hh y (by
      simpa using hψ.closedNbhd_subset_source hψ.width_lt_radius hy),
    profileForm_eq_blowupForm_on n y hy]

/-- For a symplectic form `σ` and a profile `h` of the blowup, `ω̃_{ψ,l,ε}` is symplectic: on the
image of the lift it is the push-forward of the Kähler form `ω̃_{l,ε}`, and off the image of
`L(l + ε)` and the exceptional divisor it is the pull-back of `σ` by the blowdown, a local
diffeomorphism there. -/
theorem isSymplectic_normalizedBlowupForm {h : ℝ → ℝ} (hh : IsBlowupProfile l ε h)
    (hσ : σ.IsSymplectic) : (hψ.normalizedBlowupForm h).IsSymplectic := by
  set Φ := hψ.ballLiftPartialDiffeomorph
  set D := Φ.toDiffeomorphSourceTarget
  set W := hψ.outerOpens ⊓ Blowup.offDivisorOpens hN.blowupChart
  have hcover : IsOpenCover ![(⟨Φ.target, Φ.open_target⟩ : Opens (Blowup hN.blowupChart)), W] := by
    refine IsOpenCover.mk (eq_top_iff.2 fun z _ ↦ Opens.mem_iSup.2 ?_)
    by_cases hz : z ∈ Φ.target
    · exact ⟨0, hz⟩
    · refine ⟨1, ⟨fun ⟨y, hy, hyz⟩ ↦ hz (hyz ▸ Φ.map_source
        (hψ.closedNbhd_subset_source hψ.weight_add_width_lt hy)), ?_⟩⟩
      exact (Blowup.mem_offDivisorOpens _).2 fun hZ ↦
        hz (hψ.exceptionalDivisor_subset_ballLiftPartialDiffeomorph_target hZ)
  refine (SmoothTwoForm.isSymplectic_iff_forall_mpullback_subtype_val hcover).2 ?_
  refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
  -- `![U, W] 0` is `U` only by unfolding `Matrix.vecCons`. The form's type depends on it, so
  -- `simp only [Matrix.cons_val_zero]` cannot rewrite it, and `change` states the goal on `U`.
  · change SmoothTwoForm.IsSymplectic (SmoothForm.mpullback
      (Subtype.val : hψ.targetOpens → Blowup hN.blowupChart) contMDiff_subtypeVal _)
    rw [(hψ.normalizedBlowupForm_choose_spec hh).2]
    exact (D.symm.isLocalDiffeomorph.isSymplectic_mpullback_iff D.symm.surjective).2
      (((isKahler_profileForm n hh).isSymplectic).mpullback_subtype_val _)
  · -- As above, `change` states the goal on `![U, W] 1 = W`.
    change SmoothTwoForm.IsSymplectic (SmoothForm.mpullback
      (Subtype.val : W → Blowup hN.blowupChart) contMDiff_subtypeVal _)
    have hW : SmoothForm.mpullback (Subtype.val : W → Blowup hN.blowupChart) contMDiff_subtypeVal
        (hψ.normalizedBlowupForm h) =
          SmoothForm.mpullback (Blowup.blowdown hN.blowupChart ∘ Subtype.val)
            ((Blowup.contMDiff_blowdown_real _).comp contMDiff_subtypeVal) σ := by
      rw [← SmoothForm.mpullback_mpullback (Subtype.val : W → Blowup hN.blowupChart)
        (Blowup.blowdown hN.blowupChart) contMDiff_subtypeVal (Blowup.contMDiff_blowdown_real _)]
      refine Subtype.ext (funext fun x ↦ ?_)
      exact (SmoothForm.coe_mpullback_subtype_val_apply (hψ.normalizedBlowupForm h) x).trans
        (((hψ.normalizedBlowupForm_choose_spec hh).1 x x.property.1).trans
          (SmoothForm.coe_mpullback_subtype_val_apply (SmoothForm.mpullback
            (Blowup.blowdown hN.blowupChart) (Blowup.contMDiff_blowdown_real _) σ) x).symm)
    have hloc : IsLocalDiffeomorph 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) ∞
        (Blowup.blowdown hN.blowupChart ∘ (Subtype.val : W → Blowup hN.blowupChart)) := fun x ↦
      IsLocalDiffeomorphAt.comp (hf := isLocalDiffeomorph_subtype_val x)
        (hg := Blowup.isLocalDiffeomorphAt_blowdown_real _
          ((Blowup.mem_offDivisorOpens _).1 x.property.2))
    rw [hW]
    exact ⟨hσ.isClosed.mpullback _ _,
      hσ.isNondegenerate.isNondegenerate_mpullback_of_isLocalDiffeomorph hloc⟩

/-- **A primitive of the difference of two forms `ω̃_{ψ,l,ε}`, supported in the lifted ball.** For
two profiles `h₀ h₁` of the blowup of weight `l` with collar `ε`, the difference
`hψ.normalizedBlowupForm h₁ - hψ.normalizedBlowupForm h₀` is `d β` for a one-form `β` on the
blowup that vanishes off the image under the lift `ψ̃` of the compact set
`L(l + ε) = closedNbhd n (l + ε)`. Such a `β` is the push-forward by `ψ̃` of the primitive on the
model of `exists_mextDeriv_eq_profileForm_sub`, extended by zero. -/
theorem exists_mextDeriv_eq_normalizedBlowupForm_sub {h₀ h₁ : ℝ → ℝ}
    (hh₀ : IsBlowupProfile l ε h₀) (hh₁ : IsBlowupProfile l ε h₁) :
    ∃ β : SmoothForm 𝓘(ℝ, Fin (n + 1) → ℂ) (Blowup hN.blowupChart) ℝ 1,
      mextDeriv β.val = (hψ.normalizedBlowupForm h₁ - hψ.normalizedBlowupForm h₀).val ∧
      ∀ x ∉ hψ.ballLiftPartialDiffeomorph '' closedNbhd n (l + ε), β.val x = 0 := by
  set Φ := hψ.ballLiftPartialDiffeomorph
  set D := Φ.toDiffeomorphSourceTarget
  have hK := hψ.closedNbhd_subset_source hψ.weight_add_width_lt
  obtain ⟨α, hα, hα0⟩ := exists_mextDeriv_eq_profileForm_sub n hh₀ hh₁
  -- The push-forward of `α` vanishes at the points of the image of the lift off `Φ '' L(l + ε)`.
  obtain ⟨β, hβW, hβT⟩ := SmoothForm.exists_forall_eq_and_mpullback_subtype_val_eq
    hψ.outerOpens.isOpen hψ.outerOpens_union_targetOpens 0
    (SmoothForm.mpullback D.symm D.symm.contMDiff
      (SmoothForm.mpullback (Subtype.val : hψ.sourceOpens → BlowupModel n) contMDiff_subtypeVal α))
    fun x hx ↦ by
      have h0 : α.val (D.symm x) = 0 := hα0 _ fun hK ↦
        hx ⟨_, hK, hψ.ballLiftPartialDiffeomorph_toDiffeomorphSourceTarget_symm x⟩
      simp only [SmoothForm.coe_mpullback]
      exact TauCeti.mpullback_apply_eq_zero (TauCeti.mpullback_apply_eq_zero h0)
  have hβ0 : ∀ x ∉ Φ '' closedNbhd n (l + ε), β.val x = 0 := fun x hx ↦ by
    simpa using hβW x hx
  -- The lift pulls `β` back to `α`.
  have hΦβ : ∀ y ∈ Φ.source, TauCeti.mpullback 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ)
      Φ β.val y = α.val y :=
    (SmoothForm.mpullback_toDiffeomorphSourceTarget_eq_iff Φ).1
      (by rw [hβT, SmoothForm.mpullback_mpullback_symm])
  refine ⟨β, funext fun x ↦ ?_, hβ0⟩
  by_cases hx : x ∈ Φ '' closedNbhd n (l + ε)
  · obtain ⟨y, hy, rfl⟩ := hx
    have hyS := hK hy
    have hyr : y ∈ openNbhd n r := by rwa [ballLiftPartialDiffeomorph_source] at hyS
    rw [(Φ.isLocalDiffeomorphAt _ _ _ hyS).mextDeriv_apply_eq_iff (by simp)
        ((β.contMDiff _).of_le (by simp)),
      mextDeriv_congr_of_eventuallyEq (Filter.eventually_of_mem (Φ.open_source.mem_nhds hyS) hΦβ),
      hα, Submodule.coe_sub, Submodule.coe_sub, mpullback_sub, Pi.sub_apply, Pi.sub_apply,
      hψ.normalizedBlowupForm_eq_on_ballLift hh₁ y hyr,
      hψ.normalizedBlowupForm_eq_on_ballLift hh₀ y hyr]
  · have hβx : ∀ᶠ z in 𝓝 x, β.val z = (0 : RoughForm 𝓘(ℝ, Fin (n + 1) → ℂ) _ ℝ 1) z :=
      Filter.eventually_of_mem (hψ.outerOpens.isOpen.mem_nhds hx) hβ0
    rw [mextDeriv_congr_of_eventuallyEq hβx, mextDeriv_zero, Submodule.coe_sub, Pi.sub_apply,
      hψ.normalizedBlowupForm_eq_on_compl x hx, hψ.normalizedBlowupForm_eq_on_compl x hx,
      sub_self, Pi.zero_apply]

/-! #### Compatibility with the almost complex blowup -/

omit [T2Space M] in
/-- The lift `ψ̃` is pseudoholomorphic at a point `y` of `openNbhd n r`, from the complex structure
of the model blowup to the almost complex blowup `J̃` of `J`, if `ψ` is pseudoholomorphic from
`J₀` to `J` at the image of `y` under the blowdown, read in `StdSpace`. On `openNbhd n ε` this
holds since `lift` inverts `ψ̃` there; off the exceptional divisor, since the blowdown of the
blowup is `J̃`-holomorphic with injective differential and `ψ̃` lies over `ψ`. -/
theorem isPseudoholomorphicAt_ballLiftPartialDiffeomorph {y : BlowupModel n}
    (hy : y ∈ openNbhd n r)
    (hJψ : IsPseudoholomorphicAt (stdComplexStructure (Fin (n + 1))).constSmooth J ψ
      (complexToRealEuclidean (Fin (n + 1)) y.blowdown)) :
    IsPseudoholomorphicAt (ofComplexManifold (Fin (n + 1) → ℂ) (BlowupModel n))
      (Blowup.almostComplexStructure hN.blowupChart J hN.blowupChart_isHolomorphic)
      hψ.ballLiftPartialDiffeomorph y := by
  set Φ := hψ.ballLiftPartialDiffeomorph
  have hΦy : y ∈ Φ.source := by rwa [ballLiftPartialDiffeomorph_source]
  have hΦ : MDifferentiableAt 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) Φ y :=
    Φ.mdifferentiableAt (by simp) hΦy
  have hΦapp (y' : BlowupModel n) (hy' : y' ∈ openNbhd n r) : Φ y' = hψ.ballLift ⟨y', hy'⟩ :=
    hψ.ballLiftPartialDiffeomorph_apply ⟨y', hy'⟩
  by_cases hyε : y ∈ openNbhd n ε
  · -- Near `y`, `lift ∘ ψ̃` is the identity.
    have hz : Φ y ∈ range (inr (gluingHomeomorph hN.blowupChart)) :=
      ⟨_, ((hΦapp y hy).trans (hψ.ballLift_of_mem_openNbhd ⟨y, hy⟩ hyε)).symm⟩
    have hl := Blowup.isLocalDiffeomorphAt_lift hN.blowupChart hz
    refine IsPseudoholomorphicAt.of_comp (v := Blowup.lift hN.blowupChart) ?_
      (Blowup.isPseudoholomorphicAt_lift _ J _ hz) (hl.isInvertible_mfderiv (by simp)).injective
      hΦ
    refine (isPseudoholomorphicAt_id _ y).congr_of_eventuallyEq ?_
    filter_upwards [(isOpen_openNbhd ε).mem_nhds hyε] with y' hy'
    rw [Function.comp_apply, hΦapp y' (openNbhd_mono hψ.width_lt_radius.le hy'),
      hψ.ballLift_of_mem_openNbhd _ hy', Blowup.lift_inr, id]
  · -- Off the divisor, the blowdown of the blowup composed with `ψ̃` is `ψ ∘ π`.
    set e := complexToRealEuclidean (Fin (n + 1))
    have hy0 := hψ.blowdown_ne_zero_of_notMem hyε
    have hz : Φ y ∉ Blowup.exceptionalDivisor hN.blowupChart := by
      rw [hΦapp y hy, hψ.ballLift_of_blowdown_ne_zero _ hy0]
      exact Blowup.inl_notMem_exceptionalDivisor _ _
    have hπ := Blowup.isLocalDiffeomorphAt_blowdown_real hN.blowupChart hz
    have hb : IsPseudoholomorphicAt (ofComplexManifold (Fin (n + 1) → ℂ) (BlowupModel n))
        (ofComplexManifold (Fin (n + 1) → ℂ) (Fin (n + 1) → ℂ)) blowdown y :=
      (isPseudoholomorphic_ofComplexManifold_iff.2
        ((contMDiff_blowdown ∞).mdifferentiable (by simp))).isPseudoholomorphicAt y
    have heb : IsPseudoholomorphicAt (ofComplexManifold (Fin (n + 1) → ℂ) (BlowupModel n))
        (stdComplexStructure (Fin (n + 1))).constSmooth (e ∘ blowdown) y :=
      ((isPseudoholomorphic_complexToRealEuclidean (Fin (n + 1))).isPseudoholomorphicAt
        y.blowdown).comp hb
    refine IsPseudoholomorphicAt.of_comp (v := Blowup.blowdown hN.blowupChart) ?_
      (Blowup.isPseudoholomorphicAt_blowdown _ J _ hz)
      (hπ.isInvertible_mfderiv (by simp)).injective hΦ
    refine (IsPseudoholomorphicAt.comp (u := e ∘ blowdown) (v := ψ) hJψ
      heb).congr_of_eventuallyEq ?_
    filter_upwards [(isOpen_openNbhd r).mem_nhds hy] with y' hy'
    rw [Function.comp_apply, hΦapp y' hy', blowdown_ballLift]
    rfl

/-- **Compatibility of `ω̃_{ψ,l,ε}`** (McDuff–Salamon, Theorem 7.1.21 (iv)). If `ψ` is
pseudoholomorphic from `J₀` to `J` at every point of the closed ball `B(l + ε)`, then for a
profile `h` of the blowup the form `ω̃_{ψ,l,ε}` is compatible with the almost complex blowup `J̃`
of `J`. On the image of `L(l + ε)` the lift `ψ̃` is pseudoholomorphic and pulls the form back to
the Kähler form `ω̃_{l,ε}`; elsewhere the form is the pull-back of `σ` by the blowdown, which
intertwines `J̃` with `J` and has injective differential there. -/
theorem compatible_normalizedBlowupForm {h : ℝ → ℝ} (hh : IsBlowupProfile l ε h)
    (hJψ : ∀ z ∈ closedBall (0 : StdSpace (Fin (n + 1))) (l + ε),
      IsPseudoholomorphicAt (stdComplexStructure (Fin (n + 1))).constSmooth J ψ z) :
    (hψ.normalizedBlowupForm h).Compatible
      (Blowup.almostComplexStructure hN.blowupChart J hN.blowupChart_isHolomorphic) := by
  set Φ := hψ.ballLiftPartialDiffeomorph
  set J' := Blowup.almostComplexStructure hN.blowupChart J hN.blowupChart_isHolomorphic
  set τ := hψ.normalizedBlowupForm h
  have hK := (isKahler_profileForm n hh).compatible
  suffices H : ∀ x, (∀ v w, τ.eval₂ x (J' x v) (J' x w) = τ.eval₂ x v w) ∧
      ∀ v, v ≠ 0 → 0 < τ.eval₂ x v (J' x v) from
    ⟨SmoothTwoForm.invariant_iff.2 fun x ↦ (H x).1, SmoothTwoForm.tames_iff.2 fun x ↦ (H x).2⟩
  intro x
  by_cases hx : x ∈ Φ '' closedNbhd n (l + ε)
  · obtain ⟨y, hy, rfl⟩ := hx
    have hyr : y ∈ openNbhd n r := closedNbhd_subset_openNbhd hψ.weight_add_width_lt hy
    have hΦy : y ∈ Φ.source := by rwa [ballLiftPartialDiffeomorph_source]
    have hhol := hψ.isPseudoholomorphicAt_ballLiftPartialDiffeomorph hyr
      (hJψ _ (mem_closedBall_zero_iff.2 (mem_closedNbhd_iff.1 hy)))
    have hsurj := (Φ.isInvertible_mfderiv (by simp) hΦy).surjective
    have heval (a b : TangentSpace 𝓘(ℝ, Fin (n + 1) → ℂ) y) :
        τ.eval₂ (Φ y) (mfderiv 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) Φ y a)
            (mfderiv 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) Φ y b) =
          (profileForm n l ε h).eval₂ y a b := by
      rw [SmoothBundleForm.eval₂_apply, SmoothBundleForm.eval₂_apply,
        ← hψ.normalizedBlowupForm_eq_on_ballLift hh y hyr, TauCeti.mpullback_apply_pair]
    refine ⟨fun v w ↦ ?_, fun v hv ↦ ?_⟩
    · obtain ⟨a, rfl⟩ := hsurj v
      obtain ⟨b, rfl⟩ := hsurj w
      rw [← hhol.mfderiv_apply_commute, ← hhol.mfderiv_apply_commute, heval, heval,
        hK.invariant.apply]
    · obtain ⟨a, rfl⟩ := hsurj v
      rw [← hhol.mfderiv_apply_commute, heval]
      exact SmoothTwoForm.tames_iff.1 hK.tames y a fun ha ↦ hv (by rw [ha, _root_.map_zero])
  · have hZ : x ∉ Blowup.exceptionalDivisor hN.blowupChart := fun hZ ↦ by
      obtain ⟨y, hy, rfl⟩ := hψ.exceptionalDivisor_subset_image_openNbhd hZ
      exact hx ⟨y, closedNbhd_mono (le_add_of_nonneg_left hψ.weight_pos.le)
        (openNbhd_subset_closedNbhd ε hy), rfl⟩
    have hπ := Blowup.isLocalDiffeomorphAt_blowdown_real hN.blowupChart hZ
    have hv := Blowup.isPseudoholomorphicAt_blowdown hN.blowupChart J
      hN.blowupChart_isHolomorphic hZ
    have heval (a b : TangentSpace 𝓘(ℝ, Fin (n + 1) → ℂ) x) : τ.eval₂ x a b =
        (SmoothForm.mpullback (Blowup.blowdown hN.blowupChart)
          (Blowup.contMDiff_blowdown_real _) σ).eval₂ x a b := by
      rw [SmoothBundleForm.eval₂_apply, SmoothBundleForm.eval₂_apply,
        hψ.normalizedBlowupForm_eq_on_compl x hx]
    refine ⟨fun v w ↦ ?_, fun v hv0 ↦ ?_⟩
    · rw [heval, heval]
      exact hN.compatible.invariant.eval₂_mpullback hv _ v w
    · rw [heval]
      exact hN.compatible.tames.eval₂_mpullback_pos hv _
        ((map_ne_zero_iff _ (hπ.isInvertible_mfderiv (by simp)).injective).2 hv0)

end IsNormalizedBallEmbedding

end SymplecticGeometry

end
