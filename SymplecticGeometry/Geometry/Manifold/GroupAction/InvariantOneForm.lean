/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Lie.Adjoint.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Invariant
public import SymplecticGeometry.Geometry.Manifold.GroupAction.BoundarylessModel
public import SymplecticGeometry.Geometry.Manifold.GroupAction.Circle
public import SymplecticGeometry.Geometry.Manifold.Riemannian.OneForm.Flat

/-!
# An invariant one-form dual to a fundamental vector field

Let a compact commutative Lie group `G` act smoothly on a σ-compact Hausdorff boundaryless manifold
`M`, and let `X` be the fundamental vector field of an element `ξ` of the Lie algebra of `G`. This
file shows that some smooth one-form `β` on `M` is invariant under every `g • ·`, satisfies
`β(X) ≥ 0`, and vanishes on `X` exactly at the zeros of `X`.

The form is the flat `β = g(X, ·)` (`TauCeti.SmoothForm.flat`) for a Riemannian metric `g` that
`G` preserves, which exists by Tau Ceti's `TauCeti.of_forall_riemannianBundle_inner_mfderiv`
(Haar averaging of any metric). Then `β(X) = g(X, X)`, which is nonnegative and vanishes exactly
where `X` does. Invariance of `β` comes from that of `g` and of `X`
(`TauCeti.SmoothForm.mpullback_flat`): the differential of `a • ·` carries `X` at `x` to the
fundamental vector field of `Ad_a ξ` at `a • x` (`TauCeti.mfderiv_smul_fundamentalVectorField`),
and `Ad_a` is the identity because `G` is commutative
(`TauCeti.Lie.adjointContinuousLinearMap_eq_id`).

Tau Ceti's invariant metrics are stated for a boundaryless model `I`. For a boundaryless manifold
whose model may have boundary, the form is built as above on the copy
`TauCeti.BoundarylessModel I M` with charts in `E`, which carries the action
(`SymplecticGeometry/Geometry/Manifold/GroupAction/BoundarylessModel.lean`), and pulled back
along the identity diffeomorphism `TauCeti.BoundarylessModel.interiorDiffeomorph`. Since that map
is equivariant, its differential carries the fundamental vector field of `ξ` on `M` to the one on
the copy (`TauCeti.mfderiv_fundamentalVectorField_of_map_smul`), and is injective.

For a smooth circle action and the period-one generator, the zeros of `X` are the fixed points
(`SymplecticGeometry.mem_fixedPoints_circle_iff_fundamentalVectorField_eq_zero`), so `β(X)`
vanishes exactly on the fixed points. This is the one-form away from the fixed points used in
the localization argument of Berline–Getzler–Vergne.

## Main results

* `SymplecticGeometry.exists_invariant_smoothForm_apply_fundamentalVectorField_nonneg`: for a
  compact commutative Lie group, an invariant one-form `β` with `β(X) ≥ 0`, and `β(X) = 0` exactly
  where `X = 0`.
* `SymplecticGeometry.exists_invariant_smoothForm_apply_circle_nonneg`: for a circle action and
  `X` the fundamental vector field of `circlePeriodOneGenerator`, an invariant one-form `β` with
  `β(X) ≥ 0`, and `β(X) = 0` exactly on the fixed points.

## References

* N. Berline, E. Getzler and M. Vergne, *Heat Kernels and Dirac Operators*, Grundlehren 298,
  Springer, 1992, §7.2 (the invariant one-form of the localization formula).
* G. E. Bredon, *Introduction to Compact Transformation Groups*, Academic Press (1972),
  Chapter VI (invariant Riemannian metrics).
-/

public section

noncomputable section

open Bundle Manifold TauCeti
open scoped ContDiff Manifold

namespace SymplecticGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [SigmaCompactSpace M]

section CommGroup

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {G : Type*} [Group G] [IsMulCommutative G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [ChartedSpace H' G] [LieGroup J ∞ G] [MulAction G M]
  [ContMDiffSMul J I ∞ G M]

/-- The case of a boundaryless model, where Tau Ceti gives an invariant metric directly. -/
private theorem exists_invariant_smoothForm_apply_fundamentalVectorField_nonneg_of_boundaryless
    [I.Boundaryless] (ξ : GroupLieAlgebra J G) :
    ∃ β : SmoothForm I M ℝ 1,
      (∀ g : G, SmoothForm.mpullback (g • ·)
        (ContMDiffSMul.contMDiff_const_smul (I := J) (I' := I) g) β = β) ∧
      ∀ x : M, 0 ≤ β.val x ![fundamentalVectorField I ξ x] ∧
        (β.val x ![fundamentalVectorField I ξ x] = 0 ↔ fundamentalVectorField I ξ x = 0) := by
  refine of_forall_riemannianBundle_inner_mfderiv (I := I) (M := M) J G fun hg ↦ ?_
  set X : (x : M) → TangentSpace I x := fundamentalVectorField I ξ
  have hX : ContMDiff I I.tangent ∞ (fun x ↦ (⟨x, X x⟩ : TangentBundle I M)) :=
    contMDiff_fundamentalVectorField (by rw [ENat.coe_top_add_one]) ξ
  -- The differential of `a • ·` carries `X` to itself, since `Ad_a = id`.
  have hXa (a : G) (x : M) : mfderiv I I (a • ·) x (X x) = X (a • x) := by
    rw [mfderiv_smul_fundamentalVectorField, Lie.adjointContinuousLinearMap_eq_id,
      ContinuousLinearMap.id_apply]
  refine ⟨SmoothForm.flat X hX, fun a ↦ SmoothForm.mpullback_flat _ (hg a) (hXa a), fun x ↦ ?_⟩
  rw [SmoothForm.flat_apply_self]
  exact ⟨sq_nonneg _, by simp⟩

attribute [local instance] BoundarylessModel.interiorChartedSpace in
/-- For a smooth action of a compact commutative Lie group `G` on a σ-compact Hausdorff
boundaryless manifold `M` with a finite-dimensional model, and `ξ` in the Lie algebra of `G` with
fundamental vector field `X`, there is a smooth one-form `β` on `M`, invariant under every
`g • ·`, such that `β(X) ≥ 0` at every point, with equality exactly where `X` vanishes. -/
theorem exists_invariant_smoothForm_apply_fundamentalVectorField_nonneg
    [BoundarylessManifold I M] (ξ : GroupLieAlgebra J G) :
    ∃ β : SmoothForm I M ℝ 1,
      (∀ g : G, SmoothForm.mpullback (g • ·)
        (ContMDiffSMul.contMDiff_const_smul (I := J) (I' := I) g) β = β) ∧
      ∀ x : M, 0 ≤ β.val x ![fundamentalVectorField I ξ x] ∧
        (β.val x ![fundamentalVectorField I ξ x] = 0 ↔ fundamentalVectorField I ξ x = 0) := by
  have : SigmaCompactSpace (BoundarylessModel I M) := inferInstanceAs (SigmaCompactSpace M)
  obtain ⟨β, hinv, hβ⟩ :=
    exists_invariant_smoothForm_apply_fundamentalVectorField_nonneg_of_boundaryless
      (I := 𝓘(ℝ, E)) (M := BoundarylessModel I M) ξ
  let Φ := BoundarylessModel.interiorDiffeomorph I (M := M) ∞
  have hΦd (x : M) : MDifferentiableAt I 𝓘(ℝ, E) Φ x := Φ.mdifferentiable (by simp) x
  -- The differential of `Φ` carries the fundamental vector field on `M` to the one on the copy.
  have hX (x : M) : mfderiv I 𝓘(ℝ, E) Φ x (fundamentalVectorField I ξ x) =
      fundamentalVectorField 𝓘(ℝ, E) ξ (Φ x) :=
    mfderiv_fundamentalVectorField_of_map_smul (hΦd x)
      ((ContMDiffSMul.contMDiff_smul_const (I := J) (I' := I) (n := ∞) x).mdifferentiableAt
        (by simp))
      (fun g ↦ BoundarylessModel.interiorDiffeomorph_smul I ∞ g x) ξ
  refine ⟨SmoothForm.mpullback Φ Φ.contMDiff β, fun g ↦ ?_, fun x ↦ ?_⟩
  · have hg := ContMDiffSMul.contMDiff_const_smul (I := J) (I' := 𝓘(ℝ, E)) (n := ∞)
      (M := BoundarylessModel I M) g
    rw [SmoothForm.mpullback_mpullback_of_comp_eq _ _ Φ.contMDiff hg
      (funext fun y ↦ BoundarylessModel.interiorDiffeomorph_smul I ∞ g y), hinv g]
  · rw [SmoothForm.mpullback_apply_one, hX]
    refine ⟨(hβ (Φ x)).1, (hβ (Φ x)).2.trans ?_⟩
    rw [← hX]
    exact map_eq_zero_iff _ (Φ.isInvertible_mfderiv (x := x) (by simp)).injective

end CommGroup

section Circle

variable [BoundarylessManifold I M] [MulAction Circle M] [ContMDiffSMul (𝓡 1) I ∞ Circle M]

/-- For a smooth circle action on a σ-compact Hausdorff boundaryless manifold `M` with a
finite-dimensional model, and `X` the fundamental vector field of `circlePeriodOneGenerator`,
there is a smooth one-form `β` on `M`, invariant under every `g • ·`, such that `β(X) ≥ 0` at
every point, with equality exactly at the fixed points of the action. -/
theorem exists_invariant_smoothForm_apply_circle_nonneg :
    ∃ β : SmoothForm I M ℝ 1,
      (∀ g : Circle, SmoothForm.mpullback (g • ·)
        (ContMDiffSMul.contMDiff_const_smul (I := 𝓡 1) (I' := I) g) β = β) ∧
      ∀ x : M, 0 ≤ β.val x ![fundamentalVectorField I circlePeriodOneGenerator x] ∧
        (β.val x ![fundamentalVectorField I circlePeriodOneGenerator x] = 0 ↔
          x ∈ MulAction.fixedPoints Circle M) := by
  obtain ⟨β, hinv, hβ⟩ :=
    exists_invariant_smoothForm_apply_fundamentalVectorField_nonneg (I := I) (M := M)
      circlePeriodOneGenerator
  refine ⟨β, hinv, fun x ↦ ⟨(hβ x).1, ?_⟩⟩
  rw [(hβ x).2, mem_fixedPoints_circle_iff_fundamentalVectorField_eq_zero (I' := I)]

end Circle

end SymplecticGeometry

end
