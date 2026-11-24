/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Average
public import TauCeti.RepresentationTheory.Compact.Haar

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

These invariant primitives are what make a Moser isotopy between invariant forms equivariant.

## Main results

* `TauCeti.SmoothForm.mextDerivₗ_measureAverage_of_invariant`: for a right-invariant probability
  measure, the average of a primitive of an invariant form is again a primitive of it.
* `TauCeti.SmoothForm.exists_invariant_primitive`: for a compact group acting smoothly, an
  invariant exact form has an invariant primitive.

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
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
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
`TauCeti.SmoothForm.mpullback_smul_measureAverage`. -/
theorem mextDerivₗ_measureAverage_of_invariant [MeasurableSpace G] [OpensMeasurableSpace G]
    [MeasurableMul G] (μ : Measure G) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    {α : SmoothForm I M F (k + 1)} {β : SmoothForm I M F k} (hβ : mextDerivₗ I k β = α)
    (hα : ∀ a : G, TauCeti.mpullback (F := F) I I (a • ·) α.val = α.val) :
    mextDerivₗ I k (measureAverage J μ β) = α := by
  rw [mextDerivₗ_measureAverage, hβ, (measureAverage_eq_self_iff J μ α).2 hα]

include J in
/-- **Invariant primitives.** For a compact Hausdorff topological group `G`, which is a smooth
manifold acting smoothly on a boundaryless manifold `M`, a smooth form `α` on `M` that is exact,
`α = d β`, and invariant under every element of `G` has a primitive `γ`, `d γ = α`, that is
invariant under every element of `G`. -/
theorem exists_invariant_primitive [IsTopologicalGroup G] {α : SmoothForm I M F (k + 1)}
    {β : SmoothForm I M F k} (hβ : mextDerivₗ I k β = α)
    (hα : ∀ a : G, TauCeti.mpullback (F := F) I I (a • ·) α.val = α.val) :
    ∃ γ : SmoothForm I M F k, mextDerivₗ I k γ = α ∧
      ∀ a : G, TauCeti.mpullback (F := F) I I (a • ·) γ.val = γ.val := by
  borelize G
  exact ⟨measureAverage J (haarProb G) β,
    mextDerivₗ_measureAverage_of_invariant J (haarProb G) hβ hα,
    mpullback_smul_measureAverage J (haarProb G) β⟩

end TauCeti.SmoothForm

end
