/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Morrey
import SymplecticGeometry.Analysis.Calculus.IteratedFDeriv.ClosedGraph
import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.CriticalEmbedding
import TauCeti.MeasureTheory.Measure.OpenPos

/-!
# Bounds of the `Cʲ` chart readings of Sobolev sections on compact sets

Let `M` be a manifold modelled on a real inner product space `E` of finite dimension `d`, `V → M`
a vector bundle with finite-dimensional fibre and `A` a finite bundle atlas. For `p ≥ 1`, every
element `w` of `W^{d+j,p}(V)` has a continuous representative `TauCeti.SobolevSection.toSection w`
whose chart readings are `Cʲ` on the chart images. This file bounds their derivatives of order at
most `j` on a compact subset of a chart image by a constant multiple of the Sobolev norm of `w`
(`TauCeti.SobolevSection.exists_norm_iteratedFDeriv_coord_toSection_le`), and states the bound for
a `C^{d+j}` section and its Sobolev norm
(`TauCeti.SobolevSection.exists_norm_iteratedFDeriv_coord_le_norm_ofContMDiffSection`). On a
surface with `p = 2` this bounds the `Cʲ` chart norms by the `W^{j+2,2}` norm.

The representatives come from Tau Ceti's critical embedding
`TauCeti.SobolevSection.exists_continuous_contDiffOn_coord_ae_eq_of_finrank_le`, after lowering
the exponent to `1`. Their values are bounded on compact sets by the closed graph theorem, in a
proof adapted from Tau Ceti's `TauCeti.SobolevSection.exists_norm_coord_toSection_le`, which
assumes `TauCeti.SobolevSection.HasContinuousRepresentatives`, a hypothesis that Tau Ceti does
not derive in the critical case `p = 1`. The derivatives are then bounded by the closed graph
theorem again, as `SymplecticGeometry.exists_forall_norm_iteratedFDeriv_le` shows for any linear
family of `Cʲ` functions whose values are bounded on compact sets.

## Main results

* `TauCeti.SobolevSection.contDiffOn_coord_toSection_of_finrank_add`,
  `TauCeti.SobolevSection.toSection_add_of_finrank_add`: the continuous representatives of
  `W^{d+j,p}(V)` have `Cʲ` chart readings and depend linearly on the element.
* `TauCeti.SobolevSection.exists_norm_coord_toSection_le_of_finrank_add`: the bound of the values.
* `TauCeti.SobolevSection.exists_norm_iteratedFDeriv_coord_toSection_le`: the bound for elements
  of `W^{d+j,p}(V)`.
* `TauCeti.SobolevSection.exists_norm_iteratedFDeriv_coord_le_norm_ofContMDiffSection`: the bound
  for `C^{d+j}` sections.

## References

* [D. McDuff, D. Salamon, *J-holomorphic curves and symplectic topology*][McDuffSalamon2012],
  Appendix B.1 (the Sobolev embedding theorem).
-/

public section

open Bundle Filter MeasureTheory Module Set Topology TauCeti.MeasureTheory
open scoped Manifold ContDiff ENNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) 1 M] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V]
  [VectorBundle ℝ F V] {A : FiniteBundleAtlas E M F V} {p : ℝ≥0∞} [Fact (1 ≤ p)]

namespace SobolevSection

/-- An element of `W^{d+j,p}(V)` is represented by a continuous section whose chart readings are
`Cʲ` on the chart images, and its continuous representative `toSection w` is that section. -/
private theorem toSection_spec (j : ℕ) (w : SobolevSection A volume p (finrank ℝ E + j)) :
    Continuous (fun x ↦ TotalSpace.mk' F x (toSection w x)) ∧
      ∀ i, ContDiffOn ℝ j (A.coord i (toSection w)) (A.image i) ∧
        A.sectionChartData.chartValueL volume p (finrank ℝ E + j) i w
          =ᵐ[volume.restrict (A.image i)] A.coord i (toSection w) := by
  have hp : (1 : ℝ≥0∞) ≤ p := Fact.out
  obtain ⟨t, ht, htw⟩ := exists_continuous_contDiffOn_coord_ae_eq_of_finrank_le le_rfl j
    (A.sectionChartData.ofExponentLEL volume (finrank ℝ E + j) hp w)
  have hae (i : Fin A.n) : A.sectionChartData.chartValueL volume p (finrank ℝ E + j) i w
      =ᵐ[volume.restrict (A.image i)] A.coord i t :=
    (chartValueL_ofExponentLEL_ae_eq hp w i).symm.trans (htw i).2
  rw [← eq_toSection ht hae]
  exact ⟨ht, fun i ↦ ⟨(htw i).1, hae i⟩⟩

/-- The continuous representative of an element of `W^{d+j,p}(V)` is a continuous section. -/
theorem continuous_toSection_of_finrank_add (j : ℕ)
    (w : SobolevSection A volume p (finrank ℝ E + j)) :
    Continuous fun x ↦ TotalSpace.mk' F x (toSection w x) :=
  (toSection_spec j w).1

/-- The chart readings of the continuous representative of an element of `W^{d+j,p}(V)` are `Cʲ`
on the chart images. -/
theorem contDiffOn_coord_toSection_of_finrank_add (j : ℕ)
    (w : SobolevSection A volume p (finrank ℝ E + j)) (i : Fin A.n) :
    ContDiffOn ℝ j (A.coord i (toSection w)) (A.image i) :=
  ((toSection_spec j w).2 i).1

/-- The chart data of an element of `W^{d+j,p}(V)` are the chart readings of its continuous
representative, almost everywhere. -/
theorem chartValueL_ae_eq_coord_toSection_of_finrank_add (j : ℕ)
    (w : SobolevSection A volume p (finrank ℝ E + j)) (i : Fin A.n) :
    A.sectionChartData.chartValueL volume p (finrank ℝ E + j) i w
      =ᵐ[volume.restrict (A.image i)] A.coord i (toSection w) :=
  ((toSection_spec j w).2 i).2

/-- Taking continuous representatives of elements of `W^{d+j,p}(V)` is additive. -/
theorem toSection_add_of_finrank_add (j : ℕ)
    (w v : SobolevSection A volume p (finrank ℝ E + j)) :
    toSection (w + v) = toSection w + toSection v := by
  refine (eq_toSection ?_ fun i ↦ ?_).symm
  · exact contMDiff_zero_iff.1 (ContMDiff.add_section (I := 𝓘(ℝ, E))
      (contMDiff_zero_iff.2 (continuous_toSection_of_finrank_add j w))
      (contMDiff_zero_iff.2 (continuous_toSection_of_finrank_add j v)))
  · have hw := (A.ae_eq_sectionChartData_coord_iff volume).2
      (chartValueL_ae_eq_coord_toSection_of_finrank_add j w i)
    have hv := (A.ae_eq_sectionChartData_coord_iff volume).2
      (chartValueL_ae_eq_coord_toSection_of_finrank_add j v i)
    exact (A.ae_eq_sectionChartData_coord_iff volume).1
      (SectionChartData.chartValueL_add_ae_coord hw hv)

/-- Taking continuous representatives of elements of `W^{d+j,p}(V)` commutes with real scalar
multiplication. -/
theorem toSection_smul_of_finrank_add (j : ℕ) (c : ℝ)
    (w : SobolevSection A volume p (finrank ℝ E + j)) :
    toSection (c • w) = c • toSection w := by
  refine (eq_toSection ?_ fun i ↦ ?_).symm
  · exact contMDiff_zero_iff.1 (ContMDiff.const_smul_section (I := 𝓘(ℝ, E)) (a := c)
      (contMDiff_zero_iff.2 (continuous_toSection_of_finrank_add j w)))
  · have hw := (A.ae_eq_sectionChartData_coord_iff volume).2
      (chartValueL_ae_eq_coord_toSection_of_finrank_add j w i)
    exact (A.ae_eq_sectionChartData_coord_iff volume).1
      (SectionChartData.chartValueL_smul_ae_coord c hw)

/-- **The sup bound for `W^{d+j,p}(V)`.** On a compact subset `K` of the image of chart `i`, the
chart reading of the continuous representative of an element `w` of `W^{d+j,p}(V)` is bounded by
`C ‖w‖`, the constant `C` depending on `K` but not on `w`. -/
theorem exists_norm_coord_toSection_le_of_finrank_add (j : ℕ) (i : Fin A.n) {K : Set E}
    (hK : IsCompact K) (hKi : K ⊆ A.image i) :
    ∃ C, ∀ w : SobolevSection A volume p (finrank ℝ E + j), ∀ y ∈ K,
      ‖A.coord i (toSection w) y‖ ≤ C * ‖w‖ := by
  obtain ⟨U, hU, hKU, hUi, hUc⟩ :=
    exists_open_between_and_isCompact_closure hK (A.image i).isOpen hKi
  have : CompactSpace (closure U) := isCompact_iff_compactSpace.1 hUc
  refine Exists.imp (fun C hC w y hy ↦ hC w y (subset_closure (hKU hy)))
    (SymplecticGeometry.exists_norm_le_of_tendstoUniformly (L := closure U)
    (fun w : SobolevSection A volume p (finrank ℝ E + j) ↦ A.coord i (toSection w))
    (fun w ↦ (contDiffOn_coord_toSection_of_finrank_add j w i).continuousOn.mono hUi)
    (fun w v y hy ↦ by rw [toSection_add_of_finrank_add]; exact A.coord_add i _ _ (hUi hy))
    (fun c w y hy ↦ by rw [toSection_smul_of_finrank_add]; exact A.coord_smul i _ _ (hUi hy))
    fun u w φ hu hφ ↦ ?_)
  intro y
  -- Along a subsequence the chart data converge almost everywhere.
  have hval : Tendsto (fun n ↦ A.sectionChartData.chartValueL volume p (finrank ℝ E + j) i (u n))
      atTop (𝓝 (A.sectionChartData.chartValueL volume p (finrank ℝ E + j) i w)) :=
    ((A.sectionChartData.chartValueL volume p _ i).continuous.comp
      continuous_subtypeVal).continuousAt.tendsto.comp hu
  obtain ⟨ns, hns_mono, hns⟩ := (tendstoInMeasure_of_tendsto_Lp hval).exists_seq_tendsto_ae
  have hae : ∀ᵐ y ∂volume.restrict (A.image i), Tendsto
      (fun n ↦ A.coord i (toSection (u (ns n))) y) atTop (𝓝 (A.coord i (toSection w) y)) := by
    filter_upwards [hns,
      ae_all_iff.2 fun n ↦ chartValueL_ae_eq_coord_toSection_of_finrank_add j (u (ns n)) i,
      chartValueL_ae_eq_coord_toSection_of_finrank_add j w i] with y hy hn h₀
    simpa only [hn, h₀] using hy
  -- The uniform limit `φ` agrees with the chart reading of the representative of the limit almost
  -- everywhere on `U`, hence on its closure.
  -- `Set.domRestrict` is the composition with the coercion, which `exact` unfolds.
  have hφc : Continuous φ := hφ.continuous (Frequently.of_forall fun n ↦ by
    exact ((contDiffOn_coord_toSection_of_finrank_add j (u n) i).continuousOn.mono
      hUi).domRestrict)
  have heq := hU.ext_closure_of_ae_eq (μ := volume) hφc
    ((contDiffOn_coord_toSection_of_finrank_add j w i).continuousOn.mono hUi).domRestrict (by
      filter_upwards [(ae_restrict_iff' (A.image i).isOpen.measurableSet).1 hae] with y hy hyU
      exact tendsto_nhds_unique ((hφ.tendsto_at _).comp hns_mono.tendsto_atTop)
        (hy (hUi (subset_closure hyU))))
  exact congrFun heq y

/-- **Bounds of the `Cʲ` chart readings of Sobolev sections.** Let `M` have dimension `d`. For
every chart `i`, every compact subset `K` of its image and every `j`, there is a constant `C` such
that for every element `w` of `W^{d+j,p}(V)` the derivatives of order at most `j` of the chart
reading of the continuous representative of `w` are bounded on `K` by `C ‖w‖`. -/
theorem exists_norm_iteratedFDeriv_coord_toSection_le (i : Fin A.n) {K : Set E}
    (hK : IsCompact K) (hKi : K ⊆ A.image i) (j : ℕ) :
    ∃ C, ∀ w : SobolevSection A volume p (finrank ℝ E + j), ∀ y ∈ K, ∀ m ≤ j,
      ‖iteratedFDeriv ℝ m (A.coord i (toSection w)) y‖ ≤ C * ‖w‖ :=
  SymplecticGeometry.exists_forall_norm_iteratedFDeriv_le (A.image i).isOpen
    (fun w ↦ contDiffOn_coord_toSection_of_finrank_add j w i)
    (fun w v y hy ↦ by rw [toSection_add_of_finrank_add]; exact A.coord_add i _ _ hy)
    (fun c w y hy ↦ by rw [toSection_smul_of_finrank_add]; exact A.coord_smul i _ _ hy)
    (fun _ hLi hL ↦ exists_norm_coord_toSection_le_of_finrank_add j i hL hLi) hK hKi

/-- **Bounds of the `Cʲ` chart readings of smooth sections by their Sobolev norm.** Let `M` have
dimension `d`. For every chart `i`, every compact subset `K` of its image and every `j`, there is a
constant `C` such that for every `C^{d+j}` section `s` of `V` the derivatives of order at most `j`
of the chart reading `A.coord i s` are bounded on `K` by `C` times the `W^{d+j,p}` norm of `s`. -/
theorem exists_norm_iteratedFDeriv_coord_le_norm_ofContMDiffSection (i : Fin A.n) {K : Set E}
    (hK : IsCompact K) (hKi : K ⊆ A.image i) (j : ℕ) [IsManifold 𝓘(ℝ, E) (finrank ℝ E + j : ℕ) M]
    [ContMDiffVectorBundle (finrank ℝ E + j : ℕ) F V 𝓘(ℝ, E)] :
    ∃ C, ∀ s : Cₛ^(finrank ℝ E + j : ℕ)⟮𝓘(ℝ, E); F, V⟯, ∀ y ∈ K, ∀ m ≤ j,
      ‖iteratedFDeriv ℝ m (A.coord i s) y‖ ≤
        C * ‖ofContMDiffSection A volume p (finrank ℝ E + j) s‖ := by
  obtain ⟨C, hC⟩ := exists_norm_iteratedFDeriv_coord_toSection_le (p := p) i hK hKi j
  refine ⟨C, fun s y hy m hm ↦ ?_⟩
  have := hC (ofContMDiffSection A volume p _ s) y hy m hm
  rwa [toSection_ofContMDiffSection] at this

end SobolevSection

end TauCeti

end
