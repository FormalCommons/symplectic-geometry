/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Morrey
import SymplecticGeometry.Analysis.Calculus.IteratedFDeriv.ClosedGraph
import SymplecticGeometry.Geometry.Manifold.VectorBundle.FiniteBundleAtlas.Basic
import TauCeti.Topology.MetricSpace.Pseudo.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.CriticalEmbedding
import all TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Morrey

/-!
# Bounds of the `Cʲ` chart readings of Sobolev sections on compact sets

Let `M` be a manifold modelled on a real inner product space `E` of finite dimension `d`, `V → M`
a vector bundle with finite-dimensional fibre and `A` a finite bundle atlas. For `p ≥ 1` and
`d ≤ k`, every element of `W^{k,p}(V)` has a continuous representative
(`TauCeti.SobolevSection.HasContinuousRepresentatives.of_finrank_le`), so Tau Ceti's API for
`TauCeti.SobolevSection.toSection` applies to it. When `d + j ≤ k`, the chart readings of the
representative `toSection w` are `Cʲ` on the chart images
(`TauCeti.SobolevSection.contDiffOn_coord_toSection_of_finrank_add_le`). This file bounds their
derivatives of order at most `j` on a compact subset of a chart image by a constant multiple of
the Sobolev norm of `w` (`TauCeti.SobolevSection.exists_norm_iteratedFDeriv_coord_toSection_le`),
and states the bound for a `Cᵏ` section and its Sobolev norm
(`TauCeti.SobolevSection.exists_norm_iteratedFDeriv_coord_le_norm_ofContMDiffSection`). On a
surface with `p = 2` this bounds the `Cʲ` chart norms by the `W^{j+2,2}` norm. So convergence in
`W^{k,p}(V)` makes the derivatives of order `j` of the chart readings converge locally uniformly
on the chart images
(`TauCeti.SobolevSection.tendstoLocallyUniformlyOn_iteratedFDeriv_coord_toSection`).

The representatives come from Tau Ceti's critical embedding
`TauCeti.SobolevSection.exists_continuous_contDiffOn_coord_ae_eq_of_finrank_le`, after lowering
the exponent to `1`; Tau Ceti states no constructor of
`TauCeti.SobolevSection.HasContinuousRepresentatives` for this case, and its proof here reads the
definition through `import all`. The values are bounded on compact sets by Tau Ceti's
`TauCeti.SobolevSection.exists_norm_coord_toSection_le`, and the derivatives by the closed graph
theorem, as `SymplecticGeometry.exists_forall_norm_iteratedFDeriv_le` shows for any linear
family of `Cʲ` functions whose values are bounded on compact sets.

## Main results

* `TauCeti.SobolevSection.HasContinuousRepresentatives.of_finrank_le`: continuous
  representatives in `W^{k,p}(V)` for `d ≤ k`.
* `TauCeti.SobolevSection.contDiffOn_coord_toSection_of_finrank_add_le`: for `d + j ≤ k`, the
  continuous representatives of `W^{k,p}(V)` have `Cʲ` chart readings.
* `TauCeti.SobolevSection.exists_norm_iteratedFDeriv_coord_toSection_le`: the bound for elements
  of `W^{k,p}(V)`.
* `TauCeti.SobolevSection.exists_norm_iteratedFDeriv_coord_le_norm_ofContMDiffSection`: the bound
  for `Cᵏ` sections.
* `TauCeti.SobolevSection.tendstoLocallyUniformlyOn_iteratedFDeriv_coord_toSection`: convergence
  in `W^{k,p}(V)` gives locally uniform convergence of the order-`j` derivatives of the chart
  readings.

## References

* [D. McDuff, D. Salamon, *J-holomorphic curves and symplectic topology*][McDuffSalamon2012],
  Appendix B.1 (the Sobolev embedding theorem).
-/

public section

open Bundle MeasureTheory Module Set
open scoped Manifold ContDiff ENNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) 1 M] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V]
  [VectorBundle ℝ F V] {A : FiniteBundleAtlas E M F V} {p : ℝ≥0∞} [Fact (1 ≤ p)] {k : ℕ}

namespace SobolevSection

/-- **Continuous representatives in the critical case.** If `M` has dimension `d ≤ k`, then for
every `p ≥ 1` every element of `W^{k,p}(V)` has a continuous representative. -/
theorem HasContinuousRepresentatives.of_finrank_le (hk : finrank ℝ E ≤ k) :
    HasContinuousRepresentatives A volume p k := fun w ↦ by
  have hp : (1 : ℝ≥0∞) ≤ p := Fact.out
  obtain ⟨t, ht, htw⟩ := exists_continuous_contDiffOn_coord_ae_eq_of_finrank_le hk 0
    (A.sectionChartData.ofExponentLEL volume k hp w)
  exact ⟨t, ht, fun i ↦ (chartValueL_ofExponentLEL_ae_eq hp w i).symm.trans (htw i).2⟩

/-- If `M` has dimension `d` and `d + j ≤ k`, then the chart readings of the continuous
representative of an element of `W^{k,p}(V)` are `Cʲ` on the chart images. -/
theorem contDiffOn_coord_toSection_of_finrank_add_le {j : ℕ} (hk : finrank ℝ E + j ≤ k)
    (w : SobolevSection A volume p k) (i : Fin A.n) :
    ContDiffOn ℝ j (A.coord i (toSection w)) (A.image i) := by
  have hp : (1 : ℝ≥0∞) ≤ p := Fact.out
  obtain ⟨l, rfl⟩ : ∃ l, k = l + j := ⟨k - j, by omega⟩
  obtain ⟨t, ht, htw⟩ := exists_continuous_contDiffOn_coord_ae_eq_of_finrank_le (by omega) j
    (A.sectionChartData.ofExponentLEL volume (l + j) hp w)
  rw [← eq_toSection ht fun i ↦ (chartValueL_ofExponentLEL_ae_eq hp w i).symm.trans (htw i).2]
  exact (htw i).1

/-- **Bounds of the `Cʲ` chart readings of Sobolev sections.** Let `M` have dimension `d` and
`d + j ≤ k`. For every chart `i` and every compact subset `K` of its image, there is a constant
`C` such that for every element `w` of `W^{k,p}(V)` the derivatives of order at most `j` of the
chart reading of the continuous representative of `w` are bounded on `K` by `C ‖w‖`. -/
theorem exists_norm_iteratedFDeriv_coord_toSection_le {j : ℕ} (hk : finrank ℝ E + j ≤ k)
    (i : Fin A.n) {K : Set E} (hK : IsCompact K) (hKi : K ⊆ A.image i) :
    ∃ C, ∀ w : SobolevSection A volume p k, ∀ y ∈ K, ∀ m ≤ j,
      ‖iteratedFDeriv ℝ m (A.coord i (toSection w)) y‖ ≤ C * ‖w‖ := by
  have h := HasContinuousRepresentatives.of_finrank_le (A := A) (p := p) (by omega : _ ≤ k)
  exact SymplecticGeometry.exists_forall_norm_iteratedFDeriv_le (A.image i).isOpen
    (fun w ↦ contDiffOn_coord_toSection_of_finrank_add_le hk w i)
    (fun w v y hy ↦ by rw [toSection_add h]; exact A.coord_add i _ _ hy)
    (fun c w y hy ↦ by rw [toSection_smul h]; exact A.coord_smul i _ _ hy)
    (fun _ hLi hL ↦ let ⟨C, hC⟩ := exists_norm_coord_toSection_le h i hL hLi; ⟨C, hC⟩) hK hKi

/-- **Bounds of the `Cʲ` chart readings of smooth sections by their Sobolev norm.** Let `M` have
dimension `d` and `d + j ≤ k`. For every chart `i` and every compact subset `K` of its image,
there is a constant `C` such that for every `Cᵏ` section `s` of `V` the derivatives of order at
most `j` of the chart reading `A.coord i s` are bounded on `K` by `C` times the `W^{k,p}` norm of
`s`. -/
theorem exists_norm_iteratedFDeriv_coord_le_norm_ofContMDiffSection [IsManifold 𝓘(ℝ, E) k M]
    [ContMDiffVectorBundle k F V 𝓘(ℝ, E)] {j : ℕ} (hk : finrank ℝ E + j ≤ k) (i : Fin A.n)
    {K : Set E} (hK : IsCompact K) (hKi : K ⊆ A.image i) :
    ∃ C, ∀ s : Cₛ^k⟮𝓘(ℝ, E); F, V⟯, ∀ y ∈ K, ∀ m ≤ j,
      ‖iteratedFDeriv ℝ m (A.coord i s) y‖ ≤ C * ‖ofContMDiffSection A volume p k s‖ := by
  obtain ⟨C, hC⟩ := exists_norm_iteratedFDeriv_coord_toSection_le (p := p) hk i hK hKi
  refine ⟨C, fun s y hy m hm ↦ ?_⟩
  simpa only [toSection_ofContMDiffSection] using hC (ofContMDiffSection A volume p k s) y hy m hm

/-- **Sobolev convergence gives locally uniform convergence of the `Cʲ` chart readings.** Let `M`
have dimension `d` and `d + j ≤ k`. If `w q` tends to `w₀` in `W^{k,p}(V)` along `l`, then on
the image of every chart `i` the derivatives of order `j` of the chart readings of the continuous
representatives of `w q` tend locally uniformly to those of `w₀`. -/
theorem tendstoLocallyUniformlyOn_iteratedFDeriv_coord_toSection {j : ℕ}
    (hk : finrank ℝ E + j ≤ k) (i : Fin A.n) {ι : Type*} {l : Filter ι}
    {w : ι → SobolevSection A volume p k} {w₀ : SobolevSection A volume p k}
    (hw : Filter.Tendsto w l (nhds w₀)) :
    TendstoLocallyUniformlyOn (fun q ↦ iteratedFDeriv ℝ j (A.coord i (toSection (w q))))
      (iteratedFDeriv ℝ j (A.coord i (toSection w₀))) l (A.image i) := by
  have hrep := HasContinuousRepresentatives.of_finrank_le (A := A) (p := p) (by omega : _ ≤ k)
  have hd (v : SobolevSection A volume p k) :=
    contDiffOn_coord_toSection_of_finrank_add_le hk v i
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact (A.image i).isOpen]
  intro K hKi hK
  obtain ⟨C, hC⟩ := exists_norm_iteratedFDeriv_coord_toSection_le (p := p) hk i hK hKi
  refine tendstoUniformlyOn_of_dist_le (u := fun q ↦ C * ‖w q - w₀‖) ?_ ?_
  · simpa using (tendsto_iff_norm_sub_tendsto_zero.1 hw).const_mul C
  · refine Filter.Eventually.of_forall fun q y hy ↦ ?_
    rw [dist_eq_norm, ← A.iteratedFDeriv_coord_sub i (hd _) (hd _) (hKi hy),
      ← toSection_sub hrep]
    exact hC _ y hy j le_rfl

end SobolevSection

end TauCeti

end
