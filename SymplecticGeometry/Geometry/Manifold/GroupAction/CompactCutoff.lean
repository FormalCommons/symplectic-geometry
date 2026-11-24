/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiff.ParametricIntegral
public import TauCeti.Geometry.Manifold.PartitionOfUnity.Compact
public import TauCeti.RepresentationTheory.Compact.Haar

/-!
# Invariant cutoffs around compact sets

Let a compact Lie group `G` act smoothly on a boundaryless Hausdorff manifold `M` with a
finite-dimensional model. A compact set `K` inside a `G`-invariant open set `U` has a smooth
`G`-invariant cutoff: a function equal to `1` on a `G`-invariant open neighbourhood of `K`, with
compact topological support inside `U`.

It is the Haar average `ρ(x) = ∫ σ(a • x) da` of a cutoff `σ` around the compact saturation
`G • K` (Tau Ceti's `IsCompact.exists_contMDiff_one_nhds_tsupport_subset`). It is smooth by
differentiation under the integral over the compact group (`ContMDiff.parametric_integral`), and
invariant by the invariance of Haar measure.

## Main results

* `SymplecticGeometry.exists_invariant_contMDiff_eq_one_of_isCompact`: the invariant cutoff.

## References

* G. E. Bredon, *Introduction to Compact Transformation Groups*, Academic Press (1972),
  Chapter VI (averaging over a compact group).
-/

public section

noncomputable section

open Function MeasureTheory Set TauCeti Topology
open scoped ContDiff Manifold

namespace SymplecticGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] (J : ModelWithCorners ℝ E' H')
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [ChartedSpace H' G] [IsManifold J ∞ G] [MulAction G M] [ContMDiffSMul J I ∞ G M]

include J in
/-- **A smooth invariant cutoff around a compact set.** For a compact Lie group `G` acting
smoothly, a compact set `K` inside a `G`-invariant open set `U` has a smooth `G`-invariant
function `ρ` that is `1` on a `G`-invariant open neighbourhood `W` of `K`, and whose topological
support is compact and contained in `U`. -/
theorem exists_invariant_contMDiff_eq_one_of_isCompact {K U : Set M} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) (hUinv : ∀ (g : G) (x : M), x ∈ U → g • x ∈ U) :
    ∃ (ρ : M → ℝ) (W : Set M), ContMDiff I 𝓘(ℝ) ∞ ρ ∧ (∀ (g : G) (x : M), ρ (g • x) = ρ x) ∧
      IsOpen W ∧ K ⊆ W ∧ (∀ (g : G) (x : M), x ∈ W → g • x ∈ W) ∧ (∀ x ∈ W, ρ x = 1) ∧
      HasCompactSupport ρ ∧ tsupport ρ ⊆ U := by
  have hsmul : Continuous (fun p : G × M ↦ p.1 • p.2) :=
    (contMDiff_smul (I := J) (I' := I) (n := ∞)).continuous
  -- The saturation `G • K` is compact and lies in `U`.
  set C := (fun p : G × M ↦ p.1 • p.2) '' (univ ×ˢ K)
  have hC : IsCompact C := (isCompact_univ.prod hK).image hsmul
  have hCU : C ⊆ U := by
    rintro _ ⟨⟨a, y⟩, ⟨-, hy⟩, rfl⟩
    exact hUinv a y (hKU hy)
  obtain ⟨σ, hσ, hσ1, hσc, hσU, -⟩ := hC.exists_contMDiff_one_nhds_tsupport_subset I hU hCU
  -- The open set where `σ = 1` contains `C`; `W` is the set of points whose orbit lies in it.
  set V := interior {x | σ x = 1}
  have hCV : C ⊆ V := subset_interior_iff_mem_nhdsSet.2 hσ1
  set W := {x : M | ∀ a : G, a • x ∈ V}
  have hW : IsOpen W := by
    have hcl : IsClosed {p : G × M | p.1 • p.2 ∈ Vᶜ} :=
      isOpen_interior.isClosed_compl.preimage hsmul
    have : Wᶜ = Prod.snd '' {p : G × M | p.1 • p.2 ∈ Vᶜ} := by
      ext x
      simp [W]
    rw [← isClosed_compl_iff, this]
    exact isClosedMap_snd_of_compactSpace _ hcl
  have hKW : K ⊆ W := fun y hy a ↦ hCV ⟨(a, y), ⟨mem_univ _, hy⟩, rfl⟩
  have hWinv (g : G) (x : M) (hx : x ∈ W) : g • x ∈ W := fun a ↦ by
    rw [smul_smul]
    exact hx (a * g)
  -- The saturation `D` of `tsupport σ` is compact and lies in `U`.
  set D := (fun p : G × M ↦ p.1 • p.2) '' (univ ×ˢ tsupport σ)
  have hD : IsCompact D := (isCompact_univ.prod hσc).image hsmul
  have hDU : D ⊆ U := by
    rintro _ ⟨⟨a, y⟩, ⟨-, hy⟩, rfl⟩
    exact hUinv a y (hσU hy)
  borelize G
  set ρ : M → ℝ := fun x ↦ ∫ a, σ (a • x) ∂haarProb G
  have hρD (x : M) (hx : x ∉ D) : ρ x = 0 := by
    have : ∀ a : G, σ (a • x) = 0 := fun a ↦ image_eq_zero_of_notMem_tsupport fun ha ↦ hx
      ⟨(a⁻¹, a • x), ⟨mem_univ _, ha⟩, by simp [smul_smul]⟩
    simp [ρ, this]
  have hρsupp : tsupport ρ ⊆ D :=
    closure_minimal (support_subset_iff'.2 hρD) hD.isClosed
  refine ⟨ρ, W, ?_, fun g x ↦ ?_, hW, hKW, hWinv, fun x hx ↦ ?_, HasCompactSupport.intro hD hρD,
    hρsupp.trans hDU⟩
  · exact ContMDiff.parametric_integral (J := J)
      (hσ.comp ((contMDiff_smul (I := J) (I' := I)).comp (contMDiff_snd.prodMk contMDiff_fst)))
  · simp only [ρ, smul_smul]
    exact integral_mul_right_eq_self (fun a ↦ σ (a • x)) g
  · have : ∀ a : G, σ (a • x) = 1 := fun a ↦ interior_subset (hx a)
    simp [ρ, this]

end SymplecticGeometry

end
