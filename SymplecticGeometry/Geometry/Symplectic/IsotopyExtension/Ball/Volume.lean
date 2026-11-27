/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.IsotopyExtension.Ball.Basic
public import SymplecticGeometry.Geometry.Symplectic.Manifold.LiouvilleMeasure

/-!
# The volume of a symplectic ball

A symplectic embedding `j` of the closed ball `B(r)` of `StdSpace (Fin n)` into a manifold `M`
with a two-form `σ`, whose model has dimension `2 * n`, preserves volume on the open ball: it
sends each subset `s` of `ball 0 r` onto a set whose Liouville measure for `σ` is the Lebesgue
measure of `s` (`SymplecticGeometry.IsSymplecticBallEmbedding.liouvilleMeasure_image`). The proof
applies `TauCeti.SmoothTwoForm.IsSymplecticMapOn.liouvilleMeasure_image` to the partial
diffeomorphism `SymplecticGeometry.IsSymplecticBallEmbedding.toPartialDiffeomorph`, and uses
that the Liouville measure of the standard form `ω₀` is Lebesgue measure
(`SymplecticGeometry.liouvilleMeasure_constSmooth_stdForm`).

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §7.1.
-/

public section

noncomputable section

open Set Metric MeasureTheory Module
open scoped ContDiff Manifold

namespace SymplecticGeometry

open TauCeti

namespace IsSymplecticBallEmbedding

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [MeasurableSpace M] [BorelSpace M] [LindelofSpace M]
  {n : ℕ} [Fact (finrank ℝ E = 2 * n)] {σ : SmoothTwoForm I M} {r : ℝ}
  {j : StdSpace (Fin n) → M}

/-- **The volume of a symplectic ball.** A symplectic embedding `j` of `B(r)` into a manifold
whose model has dimension `2 * n` sends each subset `s` of the open ball `ball 0 r` onto a set
whose Liouville measure for `σ` is the Lebesgue measure of `s`. -/
theorem liouvilleMeasure_image (hj : IsSymplecticBallEmbedding σ r j)
    {s : Set (StdSpace (Fin n))} (hs : s ⊆ ball 0 r) :
    σ.liouvilleMeasure n (j '' s) = volume s := by
  have hdim : finrank ℝ (StdSpace (Fin n)) = finrank ℝ E := by
    rw [finrank_stdSpace, Fintype.card_fin, Fact.out (p := finrank ℝ E = 2 * n)]
  have : Fact (finrank ℝ (StdSpace (Fin n)) = 2 * n) := ⟨hdim.trans Fact.out⟩
  have hΦ : SmoothTwoForm.IsSymplecticMapOn (stdForm (Fin n)).constSmooth σ
      (hj.toPartialDiffeomorph hdim) (hj.toPartialDiffeomorph hdim).source := by
    rw [hj.coe_toPartialDiffeomorph, hj.toPartialDiffeomorph_source]
    exact hj.isSymplecticMapOn
  have h := hΦ.liouvilleMeasure_image (n := n) (hs.trans (hj.toPartialDiffeomorph_source hdim).ge)
  rwa [hj.coe_toPartialDiffeomorph, liouvilleMeasure_constSmooth_stdForm] at h

end IsSymplecticBallEmbedding

end SymplecticGeometry

end
