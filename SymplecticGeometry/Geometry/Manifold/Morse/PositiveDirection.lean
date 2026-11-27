/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Strong
public import TauCeti.Geometry.Manifold.Morse.Hessian
import SymplecticGeometry.Geometry.Manifold.ContMDiffMap.Chart.Jet
import SymplecticGeometry.Geometry.Manifold.Morse.CriticalPoints
import SymplecticGeometry.Geometry.Manifold.Morse.Hessian
import TauCeti.Geometry.Manifold.ExtChartAt

/-!
# Positive Hessian directions in the strong Whitney topology

Let `f : M → ℝ` be a `C^n` function, `n ≥ 2`, on a boundaryless finite-dimensional manifold, and
`A ⊆ M` a closed set such that at every critical point of `f` in `A` the critical Hessian is
positive on some tangent vector. Then the same holds for every `g` in some strong Whitney ball
`c.ball f` of order two (`TauCeti.exists_strongCkControl_criticalHessian_pos`). For a
nondegenerate critical point this says that its Morse index is less than the dimension, by
`TauCeti.manifoldMorseIndex_eq_finrank_iff`, so a perturbation that is small in the strong `C²`
sense creates no local maximum in `A`.

The criterion is read in coordinates: in any chart of the maximal atlas, a critical point has a
positive Hessian direction exactly when the Hessian of the coordinate expression has one
(`TauCeti.exists_criticalHessian_pos_iff_of_mem_maximalAtlas`, proved in
`SymplecticGeometry.Geometry.Manifold.Morse.Hessian`). So on the chart target the first two
coordinate derivatives of `f` lie, at the points of `A`, in the open set of pairs whose first
member is nonzero or whose second member is positive on some vector.

## Implementation notes

The proof follows Tau Ceti's `TauCeti.exists_strongCkControl_isManifoldStronglyPseudoconvexAt`:
a locally finite cover of `M` by compact sets in chart targets, on each of which compactness gives
a tolerance keeping the coordinate jets in an open set. Here the jets of orders one and two are
tested together, and only on the part of each compact set that lies over `A`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Theorem 7.3.1.
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  §2, for the Hessian at a critical point and its index.
* M. Hirsch, *Differential Topology*, Graduate Texts in Mathematics 33, Springer, 1976,
  Chapter 2, §1, for the strong topology.
-/

public section

open Set Topology ContMDiffMap
open scoped Manifold ContDiff

universe u

namespace TauCeti

variable {E H : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M]

variable {n : WithTop ℕ∞} [IsManifold I n M]

/-- The pairs of first and second derivatives of real functions on `E` at a point where the
function is either not critical or has a positive Hessian direction. -/
private def PosDirJets (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Set ((E [×1]→L[ℝ] ℝ) × (E [×2]→L[ℝ] ℝ)) :=
  {p | p.1 ≠ 0 ∨ ∃ w : E, 0 < p.2 ![w, w]}

private theorem isOpen_posDirJets : IsOpen (PosDirJets E) := by
  rw [PosDirJets, ofPred_or, ofPred_exists]
  refine ((isOpen_compl_singleton (x := (0 : E [×1]→L[ℝ] ℝ))).preimage
    (continuous_fst (X := E [×1]→L[ℝ] ℝ) (Y := E [×2]→L[ℝ] ℝ))).union ?_
  exact isOpen_iUnion fun w ↦ isOpen_lt continuous_const
    ((continuous_eval_const ![w, w]).comp continuous_snd)

/-- The test of `PosDirJets` on the first two chart derivatives of `g` at a point of a chart
target is the conclusion of the theorem at the corresponding point of `M`. -/
private theorem mem_posDirJets_iff (hn : 2 ≤ n) (g : C^n⟮I, M; 𝓘(ℝ), ℝ⟯) (a : M)
    (z : (extChartAt I a).target) :
    (chartIteratedFDeriv g a 1 ((by norm_num : ((1 : ℕ) : WithTop ℕ∞) ≤ 2).trans hn) z,
        chartIteratedFDeriv g a 2 hn z) ∈ PosDirJets E ↔
      ((extChartAt I a).symm z ∈ criticalPoints I g →
        ∃ v, 0 < criticalHessian I g ((extChartAt I a).symm z) v v) := by
  set x := (extChartAt I a).symm z
  have hz : (z : E) ∈ (extChartAt I a).target := z.property
  have hxs : x ∈ (chartAt H a).source := extChartAt_symm_mem_chart_source hz
  have hzx : (chartAt H a).extend I x = z := by
    rw [← extChartAt.eq_1]; exact (extChartAt I a).right_inv hz
  have hcrit := extChartAt_symm_mem_criticalPoints_iff
    ((by norm_num : ((1 : ℕ) : WithTop ℕ∞) ≤ 2).trans hn) g a z
  have hhess : x ∈ criticalPoints I g → ((∃ v, 0 < criticalHessian I g x v v) ↔
      ∃ w : E, 0 < chartIteratedFDeriv g a 2 hn z ![w, w]) := fun hx ↦ by
    rw [exists_criticalHessian_pos_iff_of_mem_maximalAtlas
      (IsManifold.maximalAtlas_subset_of_le hn (IsManifold.chart_mem_maximalAtlas a)) hxs
      ((g.contMDiff.of_le hn).contMDiffAt) hx, hzx, ← extChartAt.eq_1]
    simp only [chartIteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
  simp only [PosDirJets, mem_ofPred_eq, ne_eq, ← imp_iff_not_or, ← hcrit]
  exact imp_congr_right fun hx ↦ (hhess hx).symm

variable [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M]

/-- Let `f` be a `C^n` function, `n ≥ 2`, on a boundaryless finite-dimensional manifold, and `A` a
closed set such that at every critical point of `f` in `A` the critical Hessian is positive on
some tangent vector. Then there is a strong Whitney control of order two such that every `g` in
its ball around `f` has the same property: at every critical point of `g` in `A` the critical
Hessian of `g` is positive on some tangent vector. -/
theorem exists_strongCkControl_criticalHessian_pos (hn : 2 ≤ n) (f : C^n⟮I, M; 𝓘(ℝ), ℝ⟯)
    {A : Set M} (hA : IsClosed A)
    (hfA : ∀ x ∈ A, x ∈ criticalPoints I f → ∃ v, 0 < criticalHessian I f x v v) :
    ∃ c : StrongCkControl I M n, c.order = 2 ∧ ∀ g ∈ c.ball f, ∀ x ∈ A,
      x ∈ criticalPoints I g → ∃ v, 0 < criticalHessian I g x v v := by
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have h1 : ((1 : ℕ) : WithTop ℕ∞) ≤ n := (by norm_num : ((1 : ℕ) : WithTop ℕ∞) ≤ 2).trans hn
  obtain ⟨α, a, K, hlf, hcover⟩ := exists_locallyFinite_compact_extChartAt_cover (I := I) (M := M)
  -- The part of the `i`th compact set lying over `A`, and the jet map tested on it.
  let S (i : α) : Set (extChartAt I (a i)).target :=
    (K i : Set _) ∩ {z | (extChartAt I (a i)).symm z ∈ A}
  have hS (i : α) : IsCompact (S i) :=
    (K i).isCompact.inter_right (hA.preimage
      ((continuousOn_extChartAt_symm (a i)).domRestrict))
  let J (g : C^n⟮I, M; 𝓘(ℝ), ℝ⟯) (i : α) (z : (extChartAt I (a i)).target) :=
    (chartIteratedFDeriv g (a i) 1 h1 z, chartIteratedFDeriv g (a i) 2 hn z)
  have hJ (i : α) : Continuous (J f i) :=
    (chartIteratedFDeriv f (a i) 1 h1).continuous.prodMk
      (chartIteratedFDeriv f (a i) 2 hn).continuous
  have hmaps (i : α) : MapsTo (J f i) (S i) (PosDirJets E) :=
    fun z hz ↦ (mem_posDirJets_iff hn f (a i) z).mpr (hfA _ hz.2)
  -- Compactness gives a tolerance on each member keeping the jets in the open set.
  have htol (i : α) : ∃ ε, 0 < ε ∧ Metric.thickening ε (J f i '' S i) ⊆ PosDirJets E :=
    ((hS i).image (hJ i)).exists_thickening_subset_open isOpen_posDirJets
      (hmaps i).image_subset
  choose ε hε hsub using htol
  let c : StrongCkControl I M n :=
    { ι := α, center := a, compact := K, order := 2, order_le := hn,
      tolerance := ε, tolerance_pos := hε, locallyFinite := hlf }
  refine ⟨c, rfl, fun g hg x hxA hx ↦ ?_⟩
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover.symm ▸ mem_univ x)
  obtain ⟨_, ⟨z, hzK, rfl⟩, rfl⟩ := hi
  have hgi := StrongCkControl.mem_ball_iff_forall_norm_sub_lt.mp hg i
  have hjet : J g i z ∈ PosDirJets E := by
    refine hsub i (Metric.mem_thickening_iff.mpr ⟨J f i z, mem_image_of_mem _ ⟨hzK, hxA⟩, ?_⟩)
    rw [Prod.dist_eq, max_lt_iff, dist_eq_norm, dist_eq_norm]
    exact ⟨hgi 1 (by norm_num) z hzK, hgi 2 le_rfl z hzK⟩
  exact (mem_posDirJets_iff hn g (a i) z).mp hjet hx

end TauCeti

end
