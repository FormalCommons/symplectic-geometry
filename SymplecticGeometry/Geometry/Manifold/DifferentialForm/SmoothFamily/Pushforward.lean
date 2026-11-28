/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.SmoothFamily.Basic
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Opens
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.UnitInterval

/-!
# Push-forward of a smooth family of forms along a family of open embeddings

`SymplecticGeometry.IsSmoothFamily.exists_isSmoothFamily_mpullback_eq` pushes a smooth family
`α t` of forms forward, extended by zero, along a jointly smooth `e : unitInterval × N → M` whose
slices `e (t, ·)` are injective local diffeomorphisms of boundaryless manifolds into a Hausdorff
`M`, when every `α t` vanishes off one compact set `C ⊆ unitInterval × N`. The push-forwards
`A t` form a smooth family.

Its smoothness step holds over any Hausdorff parameter manifold `P`, with no boundary condition:
`SymplecticGeometry.IsSmoothFamily.of_mpullback_family_of_eq_zero` shows that a family `A t` on
`M` is smooth when `(t, y) ↦ (t, e (t, y))` is a local diffeomorphism, the pullbacks
`e (t, ·)^* (A t)` form a smooth family, and each `A t` vanishes off the image of the slice of a
compact set `C ⊆ P × N`.

## Implementation notes

For one `t`, the push-forward is
`IsLocalDiffeomorph.exists_smoothForm_mpullback_eq_of_injective`. The smoothness criterion
follows the proof of
`SymplecticGeometry.IsNormalizedBallEmbedding.isSmoothFamily_of_eq_on_ballLift`: at a point
`(t, e (t, y))` the family is smooth by
`SymplecticGeometry.IsSmoothFamily.contMDiffAt_of_mpullback_family`, and any other point lies off
the image of `C` under `(t, y) ↦ (t, e (t, y))`, which is compact and hence closed, and off which
every `A t` vanishes. Over the unit interval, the map `(t, y) ↦ (t, e (t, y))` is a local
diffeomorphism when its slices are (`ContMDiff.isLocalDiffeomorph_prodMk_unitInterval`).
-/

public section

open Set Function
open scoped Manifold ContDiff

namespace SymplecticGeometry.IsSmoothFamily

open TauCeti

section Criterion

variable {E H N E' H' M EP HP P F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace N] [ChartedSpace H N]
  [IsManifold I 1 N] [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' 1 M]
  [T2Space M] [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
  {J : ModelWithCorners ℝ EP HP} [TopologicalSpace P] [ChartedSpace HP P] [IsManifold J 1 P]
  [T2Space P] [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

/-- **Smoothness of a family pushed forward along a family of open embeddings.** Let
`e : P × N → M` be smooth, with `M` and `P` Hausdorff and `(t, y) ↦ (t, e (t, y))` a local
diffeomorphism, and let `C ⊆ P × N` be compact. A family `A` of forms on `M` whose pullbacks
`e (t, ·)^* (A t)` form a smooth family, and with `A t` vanishing off the image under `e (t, ·)`
of the slice `{y | (t, y) ∈ C}` for every `t`, is smooth. -/
theorem of_mpullback_family_of_eq_zero {e : P × N → M} (he : ContMDiff (J.prod I) I' ∞ e)
    (hΦ : IsLocalDiffeomorph (J.prod I) (J.prod I') ∞ fun q ↦ (q.1, e q))
    {A : P → SmoothForm I' M F k}
    (hA : IsSmoothFamily J fun t ↦ SmoothForm.mpullback (fun y ↦ e (t, y))
      (he.comp (contMDiff_const.prodMk contMDiff_id)) (A t))
    {C : Set (P × N)} (hC : IsCompact C)
    (hA0 : ∀ t, ∀ x ∉ (fun y ↦ e (t, y)) '' {y | (t, y) ∈ C}, (A t).val x = 0) :
    IsSmoothFamily J A := by
  rw [isSmoothFamily_iff_contMDiff]
  rintro ⟨t₀, x₀⟩
  by_cases hx₀ : x₀ ∈ range fun y ↦ e (t₀, y)
  · -- On the image of `e (t₀, ·)`, through the local diffeomorphism `(t, y) ↦ (t, e (t, y))`.
    obtain ⟨y₀, rfl⟩ := hx₀
    exact contMDiffAt_of_mpullback_family he (hΦ (t₀, y₀)) hA
  · -- Off it, every `A t` vanishes near `(t₀, x₀)`, since the image of `C` is closed.
    have hK : IsClosed ((fun q ↦ (q.1, e q)) '' C) :=
      (hC.image (continuous_fst.prodMk he.continuous)).isClosed
    have hnot : (t₀, x₀) ∉ (fun q ↦ (q.1, e q)) '' C := by
      rintro ⟨⟨t, y⟩, -, hq⟩
      obtain ⟨rfl, rfl⟩ := Prod.ext_iff.1 hq
      exact hx₀ ⟨y, rfl⟩
    refine contMDiffAt_sliceSection_of_eventually_eq_zero ?_
    filter_upwards [hK.isOpen_compl.mem_nhds hnot] with ⟨t, x⟩ hq
    refine hA0 t x ?_
    rintro ⟨y, hy, rfl⟩
    exact hq ⟨(t, y), hy, rfl⟩

end Criterion

variable {E H N E' H' M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace N] [ChartedSpace H N]
  [IsManifold I ∞ N] [BoundarylessManifold I N] [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace M] [ChartedSpace H' M]
  [IsManifold I' ∞ M] [BoundarylessManifold I' M] [T2Space M] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {k : ℕ}

/-- **Push-forward of a smooth family along a family of open embeddings, extended by zero.** Let
`N` and `M` be boundaryless, `M` Hausdorff, and `e : unitInterval × N → M` jointly smooth with
every slice `e (t, ·)` an injective local diffeomorphism. Let `α` be a smooth family of forms on
`N` that vanish off a compact set `C ⊆ unitInterval × N`: `(α t) y = 0` when `(t, y) ∉ C`. Then
there is a smooth family `A` of forms on `M` with `e (t, ·)^* (A t) = α t` for every `t`, and
with `A t` vanishing off the image under `e (t, ·)` of the slice `{y | (t, y) ∈ C}`. -/
theorem exists_isSmoothFamily_mpullback_eq {e : unitInterval × N → M}
    (he : ContMDiff ((𝓡∂ 1).prod I) I' ∞ e)
    (hd : ∀ t, IsLocalDiffeomorph I I' ∞ fun y ↦ e (t, y))
    (hinj : ∀ t, Injective fun y ↦ e (t, y))
    {α : unitInterval → SmoothForm I N F k} (hα : IsSmoothFamily (𝓡∂ 1) α)
    {C : Set (unitInterval × N)} (hC : IsCompact C)
    (hαC : ∀ t y, (t, y) ∉ C → (α t).val y = 0) :
    ∃ A : unitInterval → SmoothForm I' M F k, IsSmoothFamily (𝓡∂ 1) A ∧
      (∀ t, SmoothForm.mpullback (fun y ↦ e (t, y)) (hd t).contMDiff (A t) = α t) ∧
      ∀ t, ∀ x ∉ (fun y ↦ e (t, y)) '' {y | (t, y) ∈ C}, (A t).val x = 0 := by
  have hslice (t : unitInterval) : IsCompact {y | (t, y) ∈ C} :=
    (isInducing_prodMkRight t).isCompact_preimage (isClosedMap_prodMk_left t).isClosed_range hC
  choose A hA hA0 using fun t ↦ (hd t).exists_smoothForm_mpullback_eq_of_injective (hinj t)
    (α t) (hslice t) (hαC t)
  refine ⟨A, of_mpullback_family_of_eq_zero he (he.isLocalDiffeomorph_prodMk_unitInterval hd)
    ?_ hC hA0, hA, hA0⟩
  convert hα using 2 with t
  exact hA t

end SymplecticGeometry.IsSmoothFamily

end
