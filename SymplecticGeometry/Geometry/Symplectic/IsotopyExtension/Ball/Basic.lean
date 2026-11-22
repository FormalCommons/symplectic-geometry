/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Real
public import SymplecticGeometry.LinearAlgebra.Symplectic.Standard.Basic
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm
import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.Neighborhood
import SymplecticGeometry.Geometry.Symplectic.Manifold.TwoForm
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Calculus.DifferentialForm.Poincare
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.ModelSpace
import TauCeti.Geometry.Symplectic.Manifold.RelativeMoser

/-!
# Symplectic embeddings of closed balls

Let `B(r)` be the closed ball `Metric.closedBall 0 r` of `StdSpace (Fin n)`, with the standard
symplectic form `ω₀ = (stdForm (Fin n)).constSmooth`. A map `j : StdSpace (Fin n) → M` into a
manifold with a two-form `σ` is a symplectic embedding of `B(r)`
(`SymplecticGeometry.IsSymplecticBallEmbedding σ r j`) when it is smooth on an open
neighbourhood of `B(r)`, injective on `B(r)`, and pulls `σ` back to `ω₀` at every point of the
open ball. Only the values of `j` near `B(r)` matter. For `r = 0` the last condition is empty, so
an embedding of `B(0)` is a point with a smooth germ. A smooth family of such embeddings over
`[0, 1]` is `SymplecticGeometry.IsSymplecticBallFamily σ r e`.

The main result enlarges a symplectic ball
(`SymplecticGeometry.IsSymplecticBallEmbedding.exists_lt_isSymplecticBallEmbedding_eqOn`): if `σ`
is closed and `0 < r₀`, a symplectic embedding `j` of `B(r₀)` agrees on `B(r₀)` with a symplectic
embedding of a strictly larger ball. This is the first half of McDuff–Salamon, Theorem 3.3.1. The
proof follows theirs. On a ball `B` about `B(r₀)` where `j` is smooth, the form `j^* σ - ω₀` is
closed and vanishes on `B(r₀)`. Its radial primitive `β₀` (Tau Ceti's `TauCeti.poincareHomotopy`
with centre `0`) vanishes on `B(r₀)` as well, since every segment from `0` to a point of `B(r₀)`
stays in `B(r₀)`. A bump function equal to `1` near `B(r₀)` and supported in `B` turns `β₀` into a
one-form `β` on all of `StdSpace (Fin n)`, and `ω₀ + dβ` agrees with `j^* σ` near `B(r₀)`. Tau
Ceti's relative Moser theorem
(`TauCeti.SmoothTwoForm.exists_diffeomorph_fix_eventually_mpullback_eq_of_mextDeriv_eq_sub`, with
the primitive `β` and the compact set `B(r₀)`) gives a diffeomorphism `Φ` fixing `B(r₀)` and
pulling `ω₀ + dβ` back to `ω₀` near `B(r₀)`. Then `j ∘ Φ` pulls `σ` back to `ω₀` near `B(r₀)`, and
it is injective on `B(r₀)`, where it is `j`. Such a map is an immersion along `B(r₀)`
(`TauCeti.SmoothTwoForm.injective_mfderiv_of_mpullback_apply_eq`), so an embedding of a
neighbourhood of `B(r₀)` (`TauCeti.exists_isOpen_isSmoothEmbedding_of_injOn`), which contains a
larger closed ball (`SymplecticGeometry.exists_lt_isSymplecticBallEmbedding_of_injOn`).

## Main definitions

* `SymplecticGeometry.IsSymplecticBallEmbedding σ r j`: `j` is a symplectic embedding of `B(r)`.
* `SymplecticGeometry.IsSymplecticBallFamily σ r e`: `e` is a smooth family over `[0, 1]` of
  symplectic embeddings of `B(r)`.

## Main results

* `SymplecticGeometry.IsSymplecticBallEmbedding.mpullback_eq_of_mem_closedBall`: for `0 < r`, a
  symplectic embedding of `B(r)` pulls `σ` back to `ω₀` on all of `B(r)`.
* `SymplecticGeometry.IsSymplecticBallEmbedding.injective_mfderiv`: for `0 < r`, it is an
  immersion along `B(r)`.
* `SymplecticGeometry.isSymplecticBallEmbedding_id`,
  `SymplecticGeometry.isSymplecticBallFamily_const`,
  `SymplecticGeometry.IsSymplecticBallFamily.of_path`: the identity, constant families, and paths
  of centres as families of embeddings of `B(0)`.
* `SymplecticGeometry.exists_lt_isSymplecticBallEmbedding_of_injOn`: a map that pulls `σ` back to
  `ω₀` on a neighbourhood of `B(r₀)` and is injective on `B(r₀)` is a symplectic embedding of a
  larger ball.
* `SymplecticGeometry.IsSymplecticBallEmbedding.exists_lt_isSymplecticBallEmbedding_eqOn`: a
  symplectic embedding of a closed ball of positive radius extends to a larger ball.

## Implementation notes

The form on `M` is called `σ`, since `ω` is a token once the scope `ContDiff` is open. Along
`B(r₀)` the segment from `ω₀` to `ω₀ + dβ` is constantly `ω₀`; this is shown as in Tau Ceti's
private `bilinFormAt_add_smul_sub_of_eq` of `Geometry/Symplectic/Manifold/RelativeMoser.lean`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Theorem 3.3.1.
-/

public section

noncomputable section

open Set Function Filter Metric
open scoped ContDiff Manifold Topology

namespace SymplecticGeometry

open TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {n : ℕ} {σ : SmoothTwoForm I M}

/-- `j` is a symplectic embedding of the closed ball `B(r)`: smooth on an open
neighbourhood of `B(r)`, injective on it, and pulling `σ` back to `ω₀` on the open ball. -/
def IsSymplecticBallEmbedding (σ : SmoothTwoForm I M) (r : ℝ) (j : StdSpace (Fin n) → M) :
    Prop :=
  (∃ U, IsOpen U ∧ closedBall 0 r ⊆ U ∧ ContMDiffOn 𝓘(ℝ, StdSpace (Fin n)) I ∞ j U) ∧
    InjOn j (closedBall 0 r) ∧
    ∀ z ∈ ball 0 r,
      mpullback 𝓘(ℝ, StdSpace (Fin n)) I j σ.val z = (stdForm (Fin n)).constSmooth.val z

theorem isSymplecticBallEmbedding_def (σ : SmoothTwoForm I M) (r : ℝ)
    (j : StdSpace (Fin n) → M) :
    IsSymplecticBallEmbedding σ r j ↔
      (∃ U, IsOpen U ∧ closedBall 0 r ⊆ U ∧ ContMDiffOn 𝓘(ℝ, StdSpace (Fin n)) I ∞ j U) ∧
        InjOn j (closedBall 0 r) ∧
        ∀ z ∈ ball 0 r,
          mpullback 𝓘(ℝ, StdSpace (Fin n)) I j σ.val z = (stdForm (Fin n)).constSmooth.val z :=
  Iff.rfl

/-- A smooth family of symplectic embeddings of `B(r)`, jointly smooth near `[0, 1] × B(r)`. -/
def IsSymplecticBallFamily (σ : SmoothTwoForm I M) (r : ℝ)
    (e : unitInterval × StdSpace (Fin n) → M) : Prop :=
  (∃ U, IsOpen U ∧ closedBall 0 r ⊆ U ∧
    ContMDiffOn ((𝓡∂ 1).prod 𝓘(ℝ, StdSpace (Fin n))) I ∞ e (univ ×ˢ U)) ∧
    ∀ t, IsSymplecticBallEmbedding σ r (fun z ↦ e (t, z))

theorem isSymplecticBallFamily_def (σ : SmoothTwoForm I M) (r : ℝ)
    (e : unitInterval × StdSpace (Fin n) → M) :
    IsSymplecticBallFamily σ r e ↔
      (∃ U, IsOpen U ∧ closedBall 0 r ⊆ U ∧
        ContMDiffOn ((𝓡∂ 1).prod 𝓘(ℝ, StdSpace (Fin n))) I ∞ e (univ ×ˢ U)) ∧
        ∀ t, IsSymplecticBallEmbedding σ r (fun z ↦ e (t, z)) :=
  Iff.rfl

namespace IsSymplecticBallEmbedding

variable {r r' : ℝ} {j : StdSpace (Fin n) → M}

/-- A symplectic embedding of `B(r)` restricts to a symplectic embedding of any smaller ball. -/
theorem mono (hj : IsSymplecticBallEmbedding σ r j) (h : r' ≤ r) :
    IsSymplecticBallEmbedding σ r' j := by
  obtain ⟨⟨U, hUo, hU, hjU⟩, hinj, hpull⟩ := hj
  exact ⟨⟨U, hUo, (closedBall_subset_closedBall h).trans hU, hjU⟩,
    hinj.mono (closedBall_subset_closedBall h), fun z hz ↦ hpull z (ball_subset_ball h hz)⟩

/-- For `0 < r`, a symplectic embedding of `B(r)` pulls `σ` back to `ω₀` on all of `B(r)`, by
continuity. -/
theorem mpullback_eq_of_mem_closedBall (hj : IsSymplecticBallEmbedding σ r j) (hr : 0 < r)
    {z : StdSpace (Fin n)} (hz : z ∈ closedBall 0 r) :
    mpullback 𝓘(ℝ, StdSpace (Fin n)) I j σ.val z = (stdForm (Fin n)).constSmooth.val z := by
  obtain ⟨⟨U, hUo, hU, hjU⟩, -, hpull⟩ := hj
  have hω₀ :=
    (isSmoothForm_modelSpace_iff.1 (stdForm (Fin n)).constSmooth.isSmoothForm).continuous
  exact EqOn.of_subset_closure (fun z hz ↦ hpull z hz)
    ((σ.contDiffOn_mpullback hUo hjU).continuousOn.mono hU) hω₀.continuousOn
    ball_subset_closedBall (closure_ball 0 hr.ne').ge hz

/-- For `0 < r`, a symplectic embedding of `B(r)` is an immersion along `B(r)`. -/
theorem injective_mfderiv (hj : IsSymplecticBallEmbedding σ r j) (hr : 0 < r)
    {z : StdSpace (Fin n)} (hz : z ∈ closedBall 0 r) :
    Injective (mfderiv 𝓘(ℝ, StdSpace (Fin n)) I j z) :=
  SmoothTwoForm.injective_mfderiv_of_mpullback_apply_eq
    ((SymplecticForm.isNondegenerate_constSmooth _).nondegenerate_bilinFormAt z)
    (hj.mpullback_eq_of_mem_closedBall hr hz)

end IsSymplecticBallEmbedding

/-- The identity is a symplectic embedding of every ball into `StdSpace (Fin n)` with `ω₀`. -/
theorem isSymplecticBallEmbedding_id (r : ℝ) :
    IsSymplecticBallEmbedding (stdForm (Fin n)).constSmooth r id :=
  ⟨⟨univ, isOpen_univ, subset_univ _, contMDiffOn_id⟩, injOn_id _,
    fun z _ ↦ by rw [mpullback_id]⟩

/-- The constant family at a symplectic embedding of `B(r)`. -/
theorem isSymplecticBallFamily_const {r : ℝ} {j : StdSpace (Fin n) → M}
    (hj : IsSymplecticBallEmbedding σ r j) : IsSymplecticBallFamily σ r (fun p ↦ j p.2) := by
  obtain ⟨⟨U, hUo, hU, hjU⟩, -⟩ := id hj
  exact ⟨⟨U, hUo, hU, hjU.comp contMDiffOn_snd fun _ hp ↦ hp.2⟩, fun _ ↦ hj⟩

/-- A smooth path of centres `c` is a family of symplectic embeddings of `B(0)`. -/
theorem IsSymplecticBallFamily.of_path {c : unitInterval → M} (hc : ContMDiff (𝓡∂ 1) I ∞ c) :
    IsSymplecticBallFamily σ 0 (fun p : unitInterval × StdSpace (Fin n) ↦ c p.1) := by
  refine ⟨⟨univ, isOpen_univ, subset_univ _, (hc.comp contMDiff_fst).contMDiffOn⟩, fun t ↦
    ⟨⟨univ, isOpen_univ, subset_univ _, (contMDiff_const (c := c t)).contMDiffOn⟩, ?_, by simp⟩⟩
  rw [closedBall_zero]
  exact injOn_singleton _ _

/-- A map that is smooth on an open `W ⊇ B(r₀)`, injective on `B(r₀)`, and pulls `σ` back to `ω₀`
on `W` is a symplectic embedding of a closed ball `B(r)` of radius `r > r₀`. -/
theorem exists_lt_isSymplecticBallEmbedding_of_injOn [FiniteDimensional ℝ E] [I.Boundaryless]
    [T2Space M] {r₀ : ℝ} {j : StdSpace (Fin n) → M} {W : Set (StdSpace (Fin n))} (hW : IsOpen W)
    (hKW : closedBall 0 r₀ ⊆ W) (hjW : ContMDiffOn 𝓘(ℝ, StdSpace (Fin n)) I ∞ j W)
    (hinj : InjOn j (closedBall 0 r₀))
    (hpull : ∀ z ∈ W,
      mpullback 𝓘(ℝ, StdSpace (Fin n)) I j σ.val z = (stdForm (Fin n)).constSmooth.val z) :
    ∃ r, r₀ < r ∧ IsSymplecticBallEmbedding σ r j := by
  rcases lt_or_ge r₀ 0 with hr₀ | hr₀
  · have h : closedBall (0 : StdSpace (Fin n)) (r₀ / 2) = ∅ := closedBall_eq_empty.2 (by linarith)
    exact ⟨r₀ / 2, by linarith, ⟨W, hW, by simp [h], hjW⟩, by simp [h],
      fun z hz ↦ absurd (ball_subset_closedBall hz) (by simp [h])⟩
  have hK : IsCompact (closedBall (0 : StdSpace (Fin n)) r₀) := isCompact_closedBall 0 r₀
  -- `j` is an immersion along `B(r₀)`, so an embedding of an open `V ⊇ B(r₀)`.
  obtain ⟨V, hKV, hVW, hV⟩ := exists_isOpen_isSmoothEmbedding_of_injOn hW hjW hK hKW hinj
    fun z hz ↦ SmoothTwoForm.injective_mfderiv_of_mpullback_apply_eq
      ((SymplecticForm.isNondegenerate_constSmooth _).nondegenerate_bilinFormAt z)
      (hpull z (hKW hz))
  have hVinj : InjOn j V := fun x hx y hy h ↦
    congrArg Subtype.val (hV.isEmbedding.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) h)
  -- `V` contains a closed ball larger than `B(r₀)`.
  obtain ⟨ε, hε, hεV⟩ := hK.exists_thickening_subset_open V.isOpen hKV
  rw [thickening_closedBall hε hr₀] at hεV
  have hsub : closedBall (0 : StdSpace (Fin n)) (ε / 2 + r₀) ⊆ V :=
    (closedBall_subset_ball (by linarith)).trans hεV
  exact ⟨ε / 2 + r₀, by linarith, ⟨V, V.isOpen, hsub, hjW.mono hVW⟩, hVinj.mono hsub,
    fun z hz ↦ hpull z (hVW (hsub (ball_subset_closedBall hz)))⟩

/-- The first step of enlarging a symplectic ball: a one-form `β` on `StdSpace (Fin n)` that
vanishes on `B(r₀)` and such that `ω₀ + dβ` is `j^* σ` on an open `O ⊇ B(r₀)` where `j` is
smooth. It is the radial primitive of `j^* σ - ω₀`, cut off away from `B(r₀)`. -/
private theorem IsSymplecticBallEmbedding.exists_smoothForm_add_mextDeriv_eq_mpullback
    [FiniteDimensional ℝ E] (hσ : σ.IsClosed) {r₀ : ℝ} (hr₀ : 0 < r₀)
    {j : StdSpace (Fin n) → M} (hj : IsSymplecticBallEmbedding σ r₀ j) :
    ∃ β : SmoothForm 𝓘(ℝ, StdSpace (Fin n)) (StdSpace (Fin n)) ℝ 1,
      (∀ z ∈ closedBall 0 r₀, β.val z = 0) ∧
      ∃ O, IsOpen O ∧ closedBall 0 r₀ ⊆ O ∧ ContMDiffOn 𝓘(ℝ, StdSpace (Fin n)) I ∞ j O ∧
        ∀ z ∈ O, ((stdForm (Fin n)).constSmooth + mextDerivₗ 𝓘(ℝ, StdSpace (Fin n)) 1 β).val z =
          mpullback 𝓘(ℝ, StdSpace (Fin n)) I j σ.val z := by
  set K := closedBall (0 : StdSpace (Fin n)) r₀
  set ω₀ := (stdForm (Fin n)).constSmooth
  obtain ⟨⟨U, hUo, hKU, hjU⟩, -⟩ := id hj
  -- A ball `ball 0 (δ + r₀)` on which `j` is smooth.
  obtain ⟨δ, hδ, hδU⟩ := (isCompact_closedBall 0 r₀).exists_thickening_subset_open hUo hKU
  rw [thickening_closedBall hδ hr₀.le] at hδU
  -- The flat closed form `j^* σ - ω₀` on that ball, vanishing on `K`.
  set γ : StdSpace (Fin n) → StdSpace (Fin n) [⋀^Fin 2]→L[ℝ] ℝ :=
    mpullback 𝓘(ℝ, StdSpace (Fin n)) I j σ.val
  set γ₀ : StdSpace (Fin n) → StdSpace (Fin n) [⋀^Fin 2]→L[ℝ] ℝ := ω₀.val
  have hγ₀c : ContDiff ℝ ∞ γ₀ := isSmoothForm_modelSpace_iff.1 ω₀.isSmoothForm
  have hγc : ContDiffOn ℝ ∞ γ U := σ.contDiffOn_mpullback hUo hjU
  have hηc : ContDiffOn ℝ (⊤ : ℕ∞) (γ - γ₀) (ball 0 (δ + r₀)) :=
    (hγc.mono hδU).sub hγ₀c.contDiffOn
  have hηd (z : StdSpace (Fin n)) (hz : z ∈ ball 0 (δ + r₀)) : extDeriv (γ - γ₀) z = 0 := by
    have hzU : U ∈ 𝓝 z := hUo.mem_nhds (hδU hz)
    have h₁ : extDeriv γ z = 0 :=
      SmoothForm.IsClosed.extDeriv_mpullback_eq_zero hσ
        (((hjU z (hδU hz)).contMDiffAt hzU).of_le (by simp))
    have h₀ : extDeriv γ₀ z = 0 := by
      simpa [mpullback_id] using SmoothForm.IsClosed.extDeriv_mpullback_eq_zero
        (SymplecticForm.isClosed_constSmooth (stdForm (Fin n))) (contMDiffAt_id (x := z))
    rw [extDeriv_sub ((hγc.differentiableOn (by simp)).differentiableAt hzU)
      (hγ₀c.differentiable (by simp)).differentiableAt, h₁, h₀, sub_zero]
  have hηK (z : StdSpace (Fin n)) (hz : z ∈ K) : (γ - γ₀) z = 0 :=
    sub_eq_zero.2 (hj.mpullback_eq_of_mem_closedBall hr₀ hz)
  -- Its radial primitive `β₀` on the ball vanishes on `K`.
  have hs : StarConvex ℝ 0 (ball (0 : StdSpace (Fin n)) (δ + r₀)) :=
    (convex_ball 0 _).starConvex (mem_ball_self (by positivity))
  set β₀ := poincareHomotopy (0 : StdSpace (Fin n)) (γ - γ₀) with hβ₀
  have hβ₀c : ContDiffOn ℝ (⊤ : ℕ∞) β₀ (ball 0 (δ + r₀)) :=
    hs.contDiffOn_poincareHomotopy isOpen_ball hηc
  have hβ₀K (z : StdSpace (Fin n)) (hz : z ∈ K) : β₀ z = 0 := by
    rw [hβ₀, poincareHomotopy_congr (ω₂ := 0) fun y hy ↦ hηK y
      ((convex_closedBall 0 r₀).segment_subset (mem_closedBall_self hr₀.le) hz hy),
      poincareHomotopy_zero, Pi.zero_apply]
  -- Cut `β₀` off by a bump function equal to `1` on `ball 0 (r₀ + δ / 3)`.
  let χ : ContDiffBump (0 : StdSpace (Fin n)) :=
    ⟨r₀ + δ / 3, r₀ + 2 * δ / 3, by positivity, by linarith⟩
  set β : StdSpace (Fin n) → StdSpace (Fin n) [⋀^Fin 1]→L[ℝ] ℝ := fun z ↦ χ z • β₀ z with hβ
  have hβc : ContDiff ℝ ∞ β :=
    hβ₀c.contDiff_smul_of_tsupport_subset isOpen_ball χ.contDiff.contDiffOn (by
      rw [χ.tsupport_eq]
      exact closedBall_subset_ball (by simp [χ]; linarith))
  have hβK (z : StdSpace (Fin n)) (hz : z ∈ K) : β z = 0 := by simp [hβ, hβ₀K z hz]
  let βs : SmoothForm 𝓘(ℝ, StdSpace (Fin n)) (StdSpace (Fin n)) ℝ 1 :=
    ⟨β, (isSmoothForm_modelSpace_iff.2 hβc).mem_smoothBundleForms⟩
  refine ⟨βs, hβK, ball 0 (r₀ + δ / 3), isOpen_ball, closedBall_subset_ball (by linarith),
    hjU.mono ((ball_subset_ball (by linarith)).trans hδU), fun z hz ↦ ?_⟩
  -- Near `z`, `β = β₀`, whose exterior derivative is `j^* σ - ω₀`.
  have hββ₀ : β =ᶠ[𝓝 z] β₀ := by
    filter_upwards [isOpen_ball.mem_nhds hz] with y hy
    simp [hβ, χ.one_of_mem_closedBall (ball_subset_closedBall hy)]
  have hd : mextDeriv βs.val z = extDeriv β₀ z := by
    rw [mextDeriv_eq_extDeriv, ← extDerivWithin_univ, ← extDerivWithin_univ]
    exact hββ₀.extDerivWithin_eq_nhds
  have hzρ : z ∈ ball (0 : StdSpace (Fin n)) (δ + r₀) := ball_subset_ball (by linarith) hz
  rw [AddMemClass.coe_add, Pi.add_apply, mextDerivₗ_apply, hd,
    hs.extDeriv_poincareHomotopy isOpen_ball (hηc.of_le (by simp)) hηd hzρ, Pi.sub_apply]
  exact add_sub_cancel _ _

/-- **Enlarging a symplectic ball.** For a closed two-form `σ` and `0 < r₀`, a symplectic
embedding `j` of `B(r₀)` agrees on `B(r₀)` with a symplectic embedding of a closed ball `B(r)`
whose radius `r` exceeds `r₀`. -/
theorem IsSymplecticBallEmbedding.exists_lt_isSymplecticBallEmbedding_eqOn [FiniteDimensional ℝ E]
    [I.Boundaryless] [T2Space M] (hσ : σ.IsClosed) {r₀ : ℝ} (hr₀ : 0 < r₀)
    {j : StdSpace (Fin n) → M} (hj : IsSymplecticBallEmbedding σ r₀ j) :
    ∃ r, r₀ < r ∧ ∃ j', IsSymplecticBallEmbedding σ r j' ∧ EqOn j' j (closedBall 0 r₀) := by
  set K := closedBall (0 : StdSpace (Fin n)) r₀
  set ω₀ := (stdForm (Fin n)).constSmooth
  obtain ⟨β, hβK, O, hOo, hKO, hjO, hO⟩ := hj.exists_smoothForm_add_mextDeriv_eq_mpullback hσ hr₀
  set σ₁ := ω₀ + mextDerivₗ 𝓘(ℝ, StdSpace (Fin n)) 1 β with hσ₁
  have hσ₁K (z : StdSpace (Fin n)) (hz : z ∈ K) : (σ₁ - ω₀).val z = 0 := by
    rw [AddSubgroupClass.coe_sub, Pi.sub_apply, hO z (hKO hz),
      sub_eq_zero.2 (hj.mpullback_eq_of_mem_closedBall hr₀ hz)]
  -- Along `K` the segment from `ω₀` to `σ₁` is constantly `ω₀`, so it stays nondegenerate.
  have hnd (z : StdSpace (Fin n)) (hz : z ∈ K) (s : ℝ) (_ : s ∈ Icc (0 : ℝ) 1) :
      ((ω₀ + s • (σ₁ - ω₀)).bilinFormAt z).Nondegenerate := by
    have h : (ω₀ + s • (σ₁ - ω₀)).bilinFormAt z = ω₀.bilinFormAt z := by
      ext v w
      simp only [SmoothForm.bilinFormAt_apply, SmoothBundleForm.eval₂_apply,
        SmoothForm.add_toRoughForm, Pi.add_apply, SetLike.val_smul, Pi.smul_apply, hσ₁K z hz,
        smul_zero, add_zero]
    rw [h]
    exact (SymplecticForm.isNondegenerate_constSmooth _).nondegenerate_bilinFormAt z
  -- Relative Moser: `Φ` fixes `K` and pulls `σ₁` back to `ω₀` on an open `N ⊇ K`.
  obtain ⟨Φ, hΦK, -, hΦ, -⟩ :=
    SmoothTwoForm.exists_diffeomorph_fix_eventually_mpullback_eq_of_mextDeriv_eq_sub
      (SymplecticForm.isClosed_constSmooth _) (β := β)
      (by rw [hσ₁, add_sub_cancel_left, mextDerivₗ_apply]) (isCompact_closedBall 0 r₀)
      hβK hnd
  obtain ⟨N, hNo, hKN, hN⟩ := eventually_nhdsSet_iff_exists.1 hΦ
  -- So `j ∘ Φ` pulls `σ` back to `ω₀` on the open `Φ ⁻¹' O ∩ N ⊇ K`.
  have hpull (z : StdSpace (Fin n)) (hz : z ∈ Φ ⁻¹' O ∩ N) :
      mpullback 𝓘(ℝ, StdSpace (Fin n)) I (j ∘ Φ) σ.val z = ω₀.val z := by
    obtain ⟨hzO, hzN⟩ := hz
    rw [mpullback_comp_at (Φ.contMDiff.mdifferentiable (by simp) z)
      (((hjO _ hzO).contMDiffAt (hOo.mem_nhds hzO)).mdifferentiableAt (by simp)), ← hN z hzN,
      SmoothForm.coe_mpullback]
    ext v
    conv_rhs => rw [mpullback_apply, hO _ hzO]
    rw [mpullback_apply]
  have hKW : K ⊆ Φ ⁻¹' O ∩ N := fun z hz ↦ ⟨by rw [mem_preimage, hΦK z hz]; exact hKO hz, hKN hz⟩
  obtain ⟨r, hr, hjΦ⟩ := exists_lt_isSymplecticBallEmbedding_of_injOn
    ((Φ.continuous.isOpen_preimage _ hOo).inter hNo) hKW
    (hjO.comp Φ.contMDiff.contMDiffOn fun z hz ↦ hz.1)
    (fun x hx y hy h ↦ hj.2.1 hx hy (by simpa [hΦK x hx, hΦK y hy] using h)) hpull
  exact ⟨r, hr, j ∘ Φ, hjΦ, fun z hz ↦ by simp [hΦK z hz]⟩

end SymplecticGeometry

end
