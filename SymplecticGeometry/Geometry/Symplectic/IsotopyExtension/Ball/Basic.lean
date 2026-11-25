/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Real
public import SymplecticGeometry.LinearAlgebra.Symplectic.Standard.Basic
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm
import SymplecticGeometry.Analysis.Calculus.DifferentialForm.Poincare
import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.Neighborhood
import SymplecticGeometry.Geometry.Symplectic.Manifold.Family
import SymplecticGeometry.Geometry.Symplectic.Manifold.TwoForm
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.ModelSpace
import TauCeti.Geometry.Symplectic.Manifold.RelativeMoser
import TauCeti.Topology.MetricSpace.SeparatedBalls

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
closed and vanishes on `B(r₀)`. So it has a primitive `β` near `B(r₀)`, defined on all of
`StdSpace (Fin n)` and vanishing on `B(r₀)`
(`StarConvex.exists_contDiff_eqOn_zero_eventually_extDeriv_eq`, a cut-off radial primitive), and
`ω₀ + dβ` agrees with `j^* σ` near `B(r₀)`. Tau Ceti's relative Moser theorem
(`TauCeti.SmoothTwoForm.exists_diffeomorph_fix_eventually_mpullback_eq_of_mextDeriv_eq_sub`, with
the primitive `β` and the compact set `B(r₀)`) gives a diffeomorphism `Φ` fixing `B(r₀)` and
pulling `ω₀ + dβ` back to `ω₀` near `B(r₀)`. Then `j ∘ Φ` pulls `σ` back to `ω₀` near `B(r₀)`, and
it is injective on `B(r₀)`, where it is `j`. Such a map is an immersion along `B(r₀)`
(`TauCeti.SmoothTwoForm.injective_mfderiv_of_mpullback_apply_eq`), so an embedding of a
neighbourhood of `B(r₀)` (`TauCeti.exists_isOpen_forall_isSmoothEmbedding_of_injOn`, for a
constant family), which contains a larger closed ball
(`SymplecticGeometry.exists_lt_isSymplecticBallEmbedding_of_injOn`).

## Main definitions

* `SymplecticGeometry.IsSymplecticBallEmbedding σ r j`: `j` is a symplectic embedding of `B(r)`.
* `SymplecticGeometry.IsSymplecticBallFamily σ r e`: `e` is a smooth family over `[0, 1]` of
  symplectic embeddings of `B(r)`.

## Main results

* `SymplecticGeometry.IsSymplecticBallEmbedding.exists_contMDiffOn`, `.injOn`, `.mpullback_eq`,
  `SymplecticGeometry.IsSymplecticBallFamily.exists_contMDiffOn`,
  `.isSymplecticBallEmbedding`: the components of the two definitions.
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
* `SymplecticGeometry.exists_lt_isSymplecticBallFamily_of_injOn`: the same for a family over
  `[0, 1]`, with one larger ball for all times.
* `SymplecticGeometry.IsSymplecticBallEmbedding.exists_lt_isSymplecticBallEmbedding_eqOn`: a
  symplectic embedding of a closed ball of positive radius extends to a larger ball.

## Implementation notes

The form on `M` is called `σ`, since `ω` is a token once the scope `ContDiff` is open.

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

/-- A symplectic embedding of `B(r)` is smooth on an open neighbourhood of `B(r)`. -/
theorem exists_contMDiffOn (hj : IsSymplecticBallEmbedding σ r j) :
    ∃ U, IsOpen U ∧ closedBall 0 r ⊆ U ∧ ContMDiffOn 𝓘(ℝ, StdSpace (Fin n)) I ∞ j U :=
  hj.1

/-- A symplectic embedding of `B(r)` is injective on `B(r)`. -/
theorem injOn (hj : IsSymplecticBallEmbedding σ r j) : InjOn j (closedBall 0 r) :=
  hj.2.1

/-- A symplectic embedding of `B(r)` pulls `σ` back to `ω₀` on the open ball. -/
theorem mpullback_eq (hj : IsSymplecticBallEmbedding σ r j) {z : StdSpace (Fin n)}
    (hz : z ∈ ball 0 r) :
    mpullback 𝓘(ℝ, StdSpace (Fin n)) I j σ.val z = (stdForm (Fin n)).constSmooth.val z :=
  hj.2.2 z hz

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
  obtain ⟨U, hUo, hU, hjU⟩ := hj.exists_contMDiffOn
  have hω₀ :=
    (isSmoothForm_modelSpace_iff.1 (stdForm (Fin n)).constSmooth.isSmoothForm).continuous
  exact EqOn.of_subset_closure (fun y hy ↦ hj.mpullback_eq (z := y) hy)
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

namespace IsSymplecticBallFamily

variable {r : ℝ} {e : unitInterval × StdSpace (Fin n) → M}

/-- A smooth family of symplectic embeddings of `B(r)` is jointly smooth on `[0, 1] × U` for an
open neighbourhood `U` of `B(r)`. -/
theorem exists_contMDiffOn (he : IsSymplecticBallFamily σ r e) :
    ∃ U, IsOpen U ∧ closedBall 0 r ⊆ U ∧
      ContMDiffOn ((𝓡∂ 1).prod 𝓘(ℝ, StdSpace (Fin n))) I ∞ e (univ ×ˢ U) :=
  he.1

/-- Each slice of a smooth family of symplectic embeddings of `B(r)` is a symplectic embedding
of `B(r)`. -/
theorem isSymplecticBallEmbedding (he : IsSymplecticBallFamily σ r e) (t : unitInterval) :
    IsSymplecticBallEmbedding σ r (fun z ↦ e (t, z)) :=
  he.2 t

end IsSymplecticBallFamily

/-- The identity is a symplectic embedding of every ball into `StdSpace (Fin n)` with `ω₀`. -/
theorem isSymplecticBallEmbedding_id (r : ℝ) :
    IsSymplecticBallEmbedding (stdForm (Fin n)).constSmooth r id :=
  ⟨⟨univ, isOpen_univ, subset_univ _, contMDiffOn_id⟩, injOn_id _,
    fun z _ ↦ by rw [mpullback_id]⟩

/-- The constant family at a symplectic embedding of `B(r)`. -/
theorem isSymplecticBallFamily_const {r : ℝ} {j : StdSpace (Fin n) → M}
    (hj : IsSymplecticBallEmbedding σ r j) : IsSymplecticBallFamily σ r (fun p ↦ j p.2) := by
  obtain ⟨U, hUo, hU, hjU⟩ := hj.exists_contMDiffOn
  exact ⟨⟨U, hUo, hU, hjU.comp contMDiffOn_snd fun _ hp ↦ hp.2⟩, fun _ ↦ hj⟩

/-- A smooth path of centres `c` is a family of symplectic embeddings of `B(0)`. -/
theorem IsSymplecticBallFamily.of_path {c : unitInterval → M} (hc : ContMDiff (𝓡∂ 1) I ∞ c) :
    IsSymplecticBallFamily σ 0 (fun p : unitInterval × StdSpace (Fin n) ↦ c p.1) := by
  refine ⟨⟨univ, isOpen_univ, subset_univ _, (hc.comp contMDiff_fst).contMDiffOn⟩, fun t ↦
    ⟨⟨univ, isOpen_univ, subset_univ _, (contMDiff_const (c := c t)).contMDiffOn⟩, ?_, by simp⟩⟩
  rw [closedBall_zero]
  exact injOn_singleton _ _

/-- A family that is jointly smooth on `[0, 1] × W` for an open `W ⊇ B(r₀)`, whose slices are
injective on `B(r₀)` and pull `σ` back to `ω₀` on `W`, is a smooth family of symplectic embeddings
of a closed ball `B(r)` of radius `r > r₀`. -/
theorem exists_lt_isSymplecticBallFamily_of_injOn [FiniteDimensional ℝ E] [I.Boundaryless]
    [T2Space M] {r₀ : ℝ} {e : unitInterval × StdSpace (Fin n) → M} {W : Set (StdSpace (Fin n))}
    (hW : IsOpen W) (hKW : closedBall 0 r₀ ⊆ W)
    (heW : ContMDiffOn ((𝓡∂ 1).prod 𝓘(ℝ, StdSpace (Fin n))) I ∞ e (univ ×ˢ W))
    (hinj : ∀ t, InjOn (fun z ↦ e (t, z)) (closedBall 0 r₀))
    (hpull : ∀ t, ∀ z ∈ W, mpullback 𝓘(ℝ, StdSpace (Fin n)) I (fun z ↦ e (t, z)) σ.val z =
      (stdForm (Fin n)).constSmooth.val z) :
    ∃ r, r₀ < r ∧ IsSymplecticBallFamily σ r e := by
  have hslice (t : unitInterval) : ContMDiffOn 𝓘(ℝ, StdSpace (Fin n)) I ∞ (fun z ↦ e (t, z)) W :=
    heW.comp (contMDiffOn_const.prodMk contMDiffOn_id) fun z hz ↦ ⟨mem_univ _, hz⟩
  have hK : IsCompact (closedBall (0 : StdSpace (Fin n)) r₀) := isCompact_closedBall 0 r₀
  -- Every slice is an immersion along `B(r₀)`, so an embedding of one open `V ⊇ B(r₀)`.
  obtain ⟨V, hKV, hVW, hV⟩ := exists_isOpen_forall_isSmoothEmbedding_of_injOn hW heW hK hKW hinj
    fun t z hz ↦ SmoothTwoForm.injective_mfderiv_of_mpullback_apply_eq
      ((SymplecticForm.isNondegenerate_constSmooth _).nondegenerate_bilinFormAt z)
      (hpull t z (hKW hz))
  have hVinj (t : unitInterval) : InjOn (fun z ↦ e (t, z)) V := fun x hx y hy h ↦
    congrArg Subtype.val ((hV t).isEmbedding.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) h)
  -- `V` contains a closed ball larger than `B(r₀)`.
  obtain ⟨r, hr, hsub⟩ := V.isOpen.exists_gt_closedBall_subset hKV
  exact ⟨r, hr, ⟨V, V.isOpen, hsub, heW.mono (prod_mono subset_rfl hVW)⟩,
    fun t ↦ ⟨⟨V, V.isOpen, hsub, (hslice t).mono hVW⟩, (hVinj t).mono hsub,
      fun z hz ↦ hpull t z (hVW (hsub (ball_subset_closedBall hz)))⟩⟩

/-- A map that is smooth on an open `W ⊇ B(r₀)`, injective on `B(r₀)`, and pulls `σ` back to `ω₀`
on `W` is a symplectic embedding of a closed ball `B(r)` of radius `r > r₀`. -/
theorem exists_lt_isSymplecticBallEmbedding_of_injOn [FiniteDimensional ℝ E] [I.Boundaryless]
    [T2Space M] {r₀ : ℝ} {j : StdSpace (Fin n) → M} {W : Set (StdSpace (Fin n))} (hW : IsOpen W)
    (hKW : closedBall 0 r₀ ⊆ W) (hjW : ContMDiffOn 𝓘(ℝ, StdSpace (Fin n)) I ∞ j W)
    (hinj : InjOn j (closedBall 0 r₀))
    (hpull : ∀ z ∈ W,
      mpullback 𝓘(ℝ, StdSpace (Fin n)) I j σ.val z = (stdForm (Fin n)).constSmooth.val z) :
    ∃ r, r₀ < r ∧ IsSymplecticBallEmbedding σ r j := by
  obtain ⟨r, hr, he⟩ := exists_lt_isSymplecticBallFamily_of_injOn (e := fun p ↦ j p.2) hW hKW
    (hjW.comp contMDiffOn_snd fun _ hp ↦ hp.2) (fun _ ↦ hinj) fun _ ↦ hpull
  exact ⟨r, hr, he.isSymplecticBallEmbedding 0⟩

/-- The first step of enlarging a symplectic ball: a one-form `β` on `StdSpace (Fin n)` that
vanishes on `B(r₀)` and such that `ω₀ + dβ` is `j^* σ` on an open `O ⊇ B(r₀)` where `j` is
smooth. It is a primitive of `j^* σ - ω₀` near `B(r₀)` that vanishes on `B(r₀)`. -/
private theorem IsSymplecticBallEmbedding.exists_smoothForm_add_mextDeriv_eq_mpullback
    [FiniteDimensional ℝ E] (hσ : σ.IsClosed) {r₀ : ℝ} (hr₀ : 0 < r₀)
    {j : StdSpace (Fin n) → M} (hj : IsSymplecticBallEmbedding σ r₀ j) :
    ∃ β : SmoothForm 𝓘(ℝ, StdSpace (Fin n)) (StdSpace (Fin n)) ℝ 1,
      (∀ z ∈ closedBall 0 r₀, β.val z = 0) ∧
      ∃ O, IsOpen O ∧ closedBall 0 r₀ ⊆ O ∧ ContMDiffOn 𝓘(ℝ, StdSpace (Fin n)) I ∞ j O ∧
        ∀ z ∈ O, ((stdForm (Fin n)).constSmooth + mextDerivₗ 𝓘(ℝ, StdSpace (Fin n)) 1 β).val z =
          mpullback 𝓘(ℝ, StdSpace (Fin n)) I j σ.val z := by
  set ω₀ := (stdForm (Fin n)).constSmooth
  obtain ⟨U, hUo, hKU, hjU⟩ := hj.exists_contMDiffOn
  -- A ball `ball 0 r`, `r > r₀`, on which `j` is smooth.
  obtain ⟨r, hr, hrU⟩ := hUo.exists_gt_closedBall_subset hKU
  replace hrU := ball_subset_closedBall.trans hrU
  -- The flat closed form `j^* σ - ω₀` on that ball, vanishing on `B(r₀)`.
  set γ : StdSpace (Fin n) → StdSpace (Fin n) [⋀^Fin 2]→L[ℝ] ℝ :=
    mpullback 𝓘(ℝ, StdSpace (Fin n)) I j σ.val
  set γ₀ : StdSpace (Fin n) → StdSpace (Fin n) [⋀^Fin 2]→L[ℝ] ℝ := ω₀.val
  have hγ₀c : ContDiff ℝ ∞ γ₀ := isSmoothForm_modelSpace_iff.1 ω₀.isSmoothForm
  have hγc : ContDiffOn ℝ ∞ γ U := σ.contDiffOn_mpullback hUo hjU
  have hηd (z : StdSpace (Fin n)) (hz : z ∈ ball 0 r) : extDeriv (γ - γ₀) z = 0 := by
    have hzU : U ∈ 𝓝 z := hUo.mem_nhds (hrU hz)
    have h₁ : extDeriv γ z = 0 :=
      SmoothForm.IsClosed.extDeriv_mpullback_eq_zero hσ
        (((hjU z (hrU hz)).contMDiffAt hzU).of_le (by simp))
    have h₀ : extDeriv γ₀ z = 0 := by
      simpa [mpullback_id] using SmoothForm.IsClosed.extDeriv_mpullback_eq_zero
        (SymplecticForm.isClosed_constSmooth (stdForm (Fin n))) (contMDiffAt_id (x := z))
    rw [extDeriv_sub ((hγc.differentiableOn (by simp)).differentiableAt hzU)
      (hγ₀c.differentiable (by simp)).differentiableAt, h₁, h₀, sub_zero]
  -- Its cut-off radial primitive.
  obtain ⟨β, hβc, hβK, hβd⟩ :=
    ((convex_ball (0 : StdSpace (Fin n)) _).starConvex (mem_ball_self (hr₀.trans hr))
      ).exists_contDiff_eqOn_zero_eventually_extDeriv_eq isOpen_ball
      (isCompact_closedBall 0 r₀) (closedBall_subset_ball (by linarith))
      ((convex_closedBall 0 r₀).starConvex (mem_closedBall_self hr₀.le)) (r := ⊤) le_top
      ((hγc.mono hrU).sub hγ₀c.contDiffOn) hηd
      fun z hz ↦ sub_eq_zero.2 (hj.mpullback_eq_of_mem_closedBall hr₀ hz)
  obtain ⟨O, hOo, hKO, hO⟩ := eventually_nhdsSet_iff_exists.1 hβd
  let βs : SmoothForm 𝓘(ℝ, StdSpace (Fin n)) (StdSpace (Fin n)) ℝ 1 :=
    ⟨β, (isSmoothForm_modelSpace_iff.2 hβc).mem_smoothBundleForms⟩
  refine ⟨βs, hβK, O ∩ ball 0 r, hOo.inter isOpen_ball,
    subset_inter hKO (closedBall_subset_ball (by linarith)), hjU.mono fun z hz ↦ hrU hz.2,
    fun z hz ↦ ?_⟩
  rw [AddMemClass.coe_add, Pi.add_apply, mextDerivₗ_apply, mextDeriv_eq_extDeriv, hO z hz.1]
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
      ((ω₀ + s • (σ₁ - ω₀)).bilinFormAt z).Nondegenerate :=
    SmoothTwoForm.nondegenerate_bilinFormAt_add_smul_sub_of_eq (hσ₁K z hz)
      ((SymplecticForm.isNondegenerate_constSmooth _).nondegenerate_bilinFormAt z) s
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
    (fun x hx y hy h ↦ hj.injOn hx hy (by simpa [hΦK x hx, hΦK y hy] using h)) hpull
  exact ⟨r, hr, j ∘ Φ, hjΦ, fun z hz ↦ by simp [hΦK z hz]⟩

end SymplecticGeometry

end
