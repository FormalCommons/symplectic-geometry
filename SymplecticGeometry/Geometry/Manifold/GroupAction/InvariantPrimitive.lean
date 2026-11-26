/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Average
public import TauCeti.RepresentationTheory.Compact.Haar
public import SymplecticGeometry.Geometry.Manifold.GroupAction.BoundarylessModel
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Pullback.Smooth
import SymplecticGeometry.Geometry.Manifold.GroupAction.Opens

/-!
# Invariant primitives of invariant exact forms

Let a group `G`, which is a compact smooth manifold, act smoothly on a boundaryless smooth
manifold `M`. If a smooth form `α` on `M` is invariant under every element of `G` and is exact,
`α = d β`, then it has an invariant primitive: the average of `β` over `G`. Indeed, averaging
commutes with `d` (`TauCeti.SmoothForm.mextDerivₗ_measureAverage`), so `d (avg β) = avg α`, and
for a right-invariant probability measure the average of an invariant form is the form itself
(`TauCeti.SmoothForm.measureAverage_eq_self_iff`), while every average is invariant
(`TauCeti.SmoothForm.mpullback_smul_measureAverage`). For a compact topological group the
normalized Haar measure `TauCeti.haarProb` is such a measure.

Tau Ceti's average of forms asks the model of `M` to have no boundary, so the averaging lemma
keeps `[I.Boundaryless]`. The existence of an invariant primitive asks only that `M` itself be
boundaryless, `[BoundarylessManifold I M]`: the forms are carried to the copy
`TauCeti.BoundarylessModel I M` with charts in the model vector space, along the inverse of the
identity diffeomorphism `TauCeti.BoundarylessModel.interiorDiffeomorph`, which is equivariant
(`SymplecticGeometry/Geometry/Manifold/GroupAction/BoundarylessModel.lean`); the primitive is
averaged there and the average pulled back, and pullback commutes with `d`
(`TauCeti.SmoothForm.mextDerivₗ_mpullback`). The transport follows
`SymplecticGeometry.exists_invariant_smoothForm_apply_fundamentalVectorField_nonneg`.

These invariant primitives are what make a Moser isotopy between invariant forms equivariant.

## Main results

* `TauCeti.SmoothForm.mextDerivₗ_measureAverage_of_invariant`: for a right-invariant probability
  measure, the average of a primitive of an invariant form is again a primitive of it.
* `TauCeti.SmoothForm.exists_invariant_primitive`: for a compact group acting smoothly on a
  boundaryless manifold, an invariant exact form has an invariant primitive.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017]
* G. E. Bredon, *Introduction to Compact Transformation Groups*, Academic Press (1972),
  Chapter VI, for averaging over smooth compact transformation groups.
-/

public section

open MeasureTheory
open scoped Manifold ContDiff

namespace TauCeti.SmoothForm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {G : Type*} [Group G] [MulAction G M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {k : ℕ}
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] (J : ModelWithCorners ℝ E' H')
  [TopologicalSpace G] [ChartedSpace H' G] [IsManifold J ∞ G] [ContMDiffSMul J I ∞ G M]
  [CompactSpace G] [T2Space G]

/-- **Averaging a primitive of an invariant form.** For a right-invariant probability measure `μ`
on `G`, if `d β = α` and `α` is invariant under every element of `G`, then the average of `β`
against `μ` is again a primitive of `α`, `d (avg β) = α`. The average is invariant by
`TauCeti.SmoothForm.mpullback_smul_measureAverage`. The model `I` has no boundary, since Tau
Ceti's average `TauCeti.SmoothForm.measureAverage` is defined only for such a model. -/
theorem mextDerivₗ_measureAverage_of_invariant [I.Boundaryless] [MeasurableSpace G]
    [OpensMeasurableSpace G] [MeasurableMul G] (μ : Measure G) [IsProbabilityMeasure μ]
    [μ.IsMulRightInvariant] {α : SmoothForm I M F (k + 1)} {β : SmoothForm I M F k}
    (hβ : mextDerivₗ I k β = α)
    (hα : ∀ a : G, mpullback (fun x : M ↦ a • x)
      (ContMDiffSMul.contMDiff_const_smul (I := J) (I' := I) a) α = α) :
    mextDerivₗ I k (measureAverage J μ β) = α := by
  rw [mextDerivₗ_measureAverage, hβ,
    (measureAverage_eq_self_iff J μ α).2 fun a ↦ (mpullback_eq_iff _).1 (hα a)]

include J in
attribute [local instance] BoundarylessModel.interiorChartedSpace in
/-- **Invariant primitives.** For a compact Hausdorff topological group `G`, which is a smooth
manifold acting smoothly on a boundaryless manifold `M`, a smooth form `α` on `M` that is exact,
`α = d β`, and invariant under every element of `G` has a primitive `γ`, `d γ = α`, that is
invariant under every element of `G`. -/
theorem exists_invariant_primitive [BoundarylessManifold I M] [IsTopologicalGroup G]
    {α : SmoothForm I M F (k + 1)} {β : SmoothForm I M F k} (hβ : mextDerivₗ I k β = α)
    (hα : ∀ a : G, TauCeti.mpullback (F := F) I I (a • ·) α.val = α.val) :
    ∃ γ : SmoothForm I M F k, mextDerivₗ I k γ = α ∧
      ∀ a : G, TauCeti.mpullback (F := F) I I (a • ·) γ.val = γ.val := by
  borelize G
  -- Carry `α` and `β` to the copy of `M` with charts in `E`, average `β` there, and pull the
  -- average back.
  let Φ := BoundarylessModel.interiorDiffeomorph I (M := M) ∞
  have : ContMDiffConstSMul I ∞ G M := ContMDiffSMul.contMDiffConstSMul J
  have : ContMDiffConstSMul 𝓘(ℝ, E) ∞ G (BoundarylessModel I M) :=
    ContMDiffSMul.contMDiffConstSMul J
  let α' := mpullback Φ.symm Φ.symm.contMDiff α
  let β' := mpullback Φ.symm Φ.symm.contMDiff β
  have hβ' : mextDerivₗ 𝓘(ℝ, E) k β' = α' := by
    rw [mextDerivₗ_mpullback, hβ]
  -- The inverse of `Φ` is equivariant, so `α'` is invariant.
  have hα' (a : G) : mpullback (fun x : BoundarylessModel I M ↦ a • x)
      (contMDiff_const_smul a) α' = α' :=
    mpullback_smul_mpullback Φ.symm.contMDiff
      (BoundarylessModel.interiorDiffeomorph_symm_smul I ∞ a) ((mpullback_eq_iff _).2 (hα a))
  let γ' := measureAverage J (haarProb G) β'
  refine ⟨mpullback Φ Φ.contMDiff γ', ?_, fun a ↦ ?_⟩
  · rw [mextDerivₗ_mpullback, mextDerivₗ_measureAverage_of_invariant J (haarProb G) hβ' hα',
      mpullback_mpullback_symm]
  · -- The map `Φ` is equivariant, and the average is invariant.
    exact (mpullback_eq_iff _).1 (mpullback_smul_mpullback Φ.contMDiff
      (BoundarylessModel.interiorDiffeomorph_smul I ∞ a)
      ((mpullback_eq_iff _).2 (mpullback_smul_measureAverage J (haarProb G) β' a)))

end TauCeti.SmoothForm

end
