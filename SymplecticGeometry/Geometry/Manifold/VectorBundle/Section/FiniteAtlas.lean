/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.FiniteAtlas
import TauCeti.Geometry.Manifold.VectorBundle.Section.Seminorm
import TauCeti.Geometry.Manifold.VectorBundle.Section.Topology

/-!
# Convergence in the frame topology from finite-atlas seminorms

Let `(e', U', c, K)` be a finite chart-frame atlas of a `C^n` vector bundle `V`, in the sense of
Tau Ceti's `ContMDiffSection.finiteAtlasSeminorm`, whose compact pieces `K i` have relative
interiors covering `M`. This file shows that if the finite-atlas `C^m` seminorms of `s p - s₀`
tend to zero for every order `m ≤ n`, then `s p` tends to `s₀` in the frame topology
`ContMDiffSection.frameTopology` of every frame system, covering `M` or not:
`ContMDiffSection.tendsto_frameTopology_of_tendsto_finiteAtlasSeminorm`. It is a converse of Tau
Ceti's `ContMDiffSection.tendsto_chartIteratedFDeriv_of_tendsto_finiteAtlasSeminorm`.

Each seminorm of the frame topology is bounded by a multiple of a finite-atlas seminorm, by Tau
Ceti's `ContMDiffSection.exists_chartCkSeminorm_le_finiteAtlasSeminorm`, and
`ContMDiffSection.tendsto_frameTopology_iff` concludes.

## References

* [M. Hirsch, *Differential Topology*][Hirsch1976], Chapter 2, §1
-/

public section

open Bundle Filter Set Topology TopologicalSpace
open scoped Manifold ContDiff

namespace ContMDiffSection

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]
  {n : ℕ∞ω} [ContMDiffVectorBundle n F V I] [IsManifold I n M]
  {ι' : Type*} [Fintype ι'] (e' : ι' → Trivialization F (π F V))
  [∀ i, MemTrivializationAtlas (e' i)] (U' : ι' → Opens M)
  (hU' : ∀ i, (U' i : Set M) ⊆ (e' i).baseSet) {c : ∀ i, U' i}
  {K : ∀ i, Compacts (extChartAt I (c i)).target}

/-- Let `(e', U', c, K)` be a finite chart-frame atlas whose compact pieces have relative
interiors covering `M`. If, for every order `m ≤ n`, the finite-atlas `C^m` seminorms of
`s p - s₀` tend to zero along `l`, then `s p` tends to `s₀` along `l` in the frame topology of
every frame system `(e, U)`, covering `M` or not. -/
theorem tendsto_frameTopology_of_tendsto_finiteAtlasSeminorm
    (hK : ∀ y : M, ∃ i, ∃ hyU : y ∈ U' i,
      ∃ hy : (⟨y, hyU⟩ : U' i) ∈ (extChartAt I (c i)).source,
        (⟨extChartAt I (c i) ⟨y, hyU⟩, (extChartAt I (c i)).map_source hy⟩ :
          (extChartAt I (c i)).target) ∈ interior (K i : Set (extChartAt I (c i)).target))
    {ι : Type*} (e : ι → Trivialization F (π F V)) [∀ i, MemTrivializationAtlas (e i)]
    (U : ι → Opens M) (hU : ∀ i, (U i : Set M) ⊆ (e i).baseSet)
    {P : Type*} {l : Filter P} {s : P → Cₛ^n⟮I; F, V⟯} {s₀ : Cₛ^n⟮I; F, V⟯}
    (hs : ∀ (m : ℕ) (hm : (m : ℕ∞ω) ≤ n),
      Tendsto (fun p ↦ finiteAtlasSeminorm e' U' hU' c K m hm (s p - s₀)) l (𝓝 0)) :
    letI := frameTopology (I := I) (n := n) e U hU
    Tendsto s l (𝓝 s₀) := by
  refine (tendsto_frameTopology_iff (I := I) e U hU).mpr fun i x L m hm ↦ ?_
  obtain ⟨C, -, hC⟩ := exists_chartCkSeminorm_le_finiteAtlasSeminorm e' U' hU' hK (e i) (hU i)
    x L m hm
  refine squeeze_zero (fun p ↦ apply_nonneg _ _) (fun p ↦
    ((e i).chartDerivativeSeminorm_le_chartCkSeminorm (hU i) x L le_rfl hm _).trans (hC _)) ?_
  simpa using (hs m hm).const_mul C

end ContMDiffSection

end
