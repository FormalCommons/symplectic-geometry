/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Basic
import TauCeti.MeasureTheory.Function.LocalRepresentative
import SymplecticGeometry.Geometry.Manifold.VectorBundle.FiniteBundleAtlas.Basic

/-!
# Smooth representatives of Sobolev sections from local ones

Let `A` be a finite bundle atlas of a vector bundle `V → M` and `w` a Sobolev section of `V`
(`TauCeti.SobolevSection`). If, near every point of every chart image, the chart data of `w` agree
almost everywhere with a function that is `Cⁿ` there, then `w` is represented by a `Cⁿ` section of
`V`: a section whose chart readings agree almost everywhere with the chart data of `w`
(`TauCeti.SobolevSection.exists_contMDiff_ae_eq_coord_of_locally`). This is how a local regularity
statement for the chart data of a solution of an elliptic equation becomes a global one.

The local representatives in one chart agree on overlaps, since continuous functions that agree
almost everywhere on an open set agree there, so they glue to one on the chart image
(`TauCeti.exists_contDiffOn_ae_eq_of_locally`). These glue across charts into a continuous section
(`TauCeti.FiniteBundleAtlas.exists_continuous_coord_eqOn_of_ae_eq`), which is `Cⁿ` since its chart
readings are (`TauCeti.FiniteBundleAtlas.contMDiff_of_contDiffOn_coord`). The gluing adapts the
proof of Tau Ceti's
`TauCeti.SobolevSection.exists_continuous_contDiffOn_coord_ae_eq_of_forall_zeroAtInfty`, which
glues chartwise representatives of Sobolev data in the same way.

## Main results

* `TauCeti.SobolevSection.exists_contMDiff_ae_eq_coord_of_locally`: a Sobolev section whose chart
  data have local `Cⁿ` representatives is represented by a `Cⁿ` section.
-/

public section

open Bundle MeasureTheory Set Filter Topology
open scoped Manifold ContDiff ENNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) 1 M] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V]
  [VectorBundle ℝ F V] {A : FiniteBundleAtlas E M F V} {μ : Measure E} [μ.IsAddHaarMeasure]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {k : ℕ} {n : WithTop ℕ∞} [IsManifold 𝓘(ℝ, E) n M]
  [ContMDiffVectorBundle n F V 𝓘(ℝ, E)]

namespace SobolevSection

/-- **Smooth representatives from local ones.** Let `w` be a Sobolev section of `V`. If near every
point of the image of every chart `i` the chart-`i` data of `w` agree almost everywhere with a
function that is `Cⁿ` near that point, then there is a `Cⁿ` section `t` of `V` whose reading in
every chart `i` agrees almost everywhere on the chart image with the chart-`i` data of `w`. -/
theorem exists_contMDiff_ae_eq_coord_of_locally {w : SobolevSection A μ p k}
    (h : ∀ i, ∀ y ∈ A.image i, ∃ U ∈ 𝓝 y, ∃ f : E → F, ContDiffOn ℝ n f U ∧
      A.sectionChartData.chartValueL μ p k i w =ᵐ[μ.restrict U] f) :
    ∃ t : ∀ x, V x, ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, F)) n (fun x ↦ TotalSpace.mk' F x (t x)) ∧
      ∀ i, A.sectionChartData.chartValueL μ p k i w =ᵐ[μ.restrict (A.image i)] A.coord i t := by
  choose g hg hgw using fun i ↦ exists_contDiffOn_ae_eq_of_locally (h i)
  obtain ⟨s, hs⟩ := SobolevSection.exists_section_ae_eq_coord _ _ _ _ w
  obtain ⟨t, -, ht⟩ := FiniteBundleAtlas.exists_continuous_coord_eqOn_of_ae_eq (μ := μ)
    (fun i ↦ (hg i).continuousOn) fun i ↦ (hs i).symm.trans (hgw i)
  refine ⟨t, A.contMDiff_of_contDiffOn_coord fun i ↦ (hg i).congr (ht i), fun i ↦ ?_⟩
  filter_upwards [hgw i, ae_restrict_mem (A.image i).isOpen.measurableSet] with y h2 hy
  rw [h2, ht i hy]

end SobolevSection

end TauCeti

end
