/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.FiniteBundleAtlas.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Section.FrameCover
import SymplecticGeometry.Geometry.Manifold.VectorBundle.Section.FiniteAtlas
import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Evaluation
import TauCeti.Geometry.Manifold.ExtChartAt
import TauCeti.Geometry.Manifold.VectorBundle.Section.FiniteAtlas
import TauCeti.Topology.UniformSpace.LocallyUniformConvergence

/-!
# Finite bundle atlases and the frame topology on sections

Let `V` be a `Cⁿ` vector bundle over a manifold `M` modelled on a locally compact normed space
`E`, and let `A` be a finite bundle atlas of `V` (`TauCeti.FiniteBundleAtlas`). This file shows
that convergence of `Cⁿ` sections in the frame topology `ContMDiffSection.frameTopology` of any
covering frame system gives, for each chart `i` of `A` and each order `j ≤ n`, uniform
convergence of the `j`-th derivatives of the chart readings `A.coord i` on the chart image
`A.image i`:
`TauCeti.FiniteBundleAtlas.tendstoUniformlyOn_iteratedFDeriv_coord_of_tendsto`.
Conversely, locally uniform convergence of these derivatives on every chart image gives
convergence in the frame topology of every frame system, covering `M` or not:
`TauCeti.FiniteBundleAtlas.tendsto_frameTopology_of_tendstoLocallyUniformlyOn`. For a covering
frame system the two give an equivalence:
`TauCeti.FiniteBundleAtlas.tendsto_frameTopology_iff_tendstoLocallyUniformlyOn`.

On the way it relates the chart readings `A.coord i` to the frame coordinates
`Bundle.Trivialization.frameCoordinates` of the bundle chart `A.triv i`, read through the charts
at `A.center i`, and their derivatives:
`TauCeti.FiniteBundleAtlas.coord_eqOn_frameCoordinates`,
`TauCeti.FiniteBundleAtlas.iteratedFDerivWithin_frameCoordinates_eq` and, in the form of the chart
derivatives of Tau Ceti's seminorms,
`TauCeti.FiniteBundleAtlas.chartIteratedFDeriv_frameCoordinates_eq`.

The proof reads the sections in the frame of the bundle chart `A.triv i` over its base set, whose
frame coordinates depend continuously on the section by Tau Ceti's
`ContMDiffSection.continuous_frameCoordinates_of_cover`, and then uses the uniform convergence of
coordinate derivatives on compact subsets of a chart target,
`ContMDiffMap.tendstoUniformlyOn_iteratedFDerivWithin_extChartAt`, on the compact chart image of
the closure of the chart domain. No `CompactSpace M` instance is assumed, since a finite bundle
atlas already makes `M` compact (`TauCeti.FiniteBundleAtlas.compactSpace`).

For the converse, compact neighbourhoods inside the chart images, finitely many by compactness of
`M`, form a finite chart-frame atlas in the sense of Tau Ceti's
`ContMDiffSection.finiteAtlasSeminorm`, built on the bundle charts `A.triv i` over their base
sets. Its seminorms of `s p - s₀` tend to zero by the hypothesis, and
`ContMDiffSection.tendsto_frameTopology_of_tendsto_finiteAtlasSeminorm` concludes. The relative
interiors of the compact pieces are found as in the proof of Tau Ceti's
`TauCeti.exists_compacts_extChartAt_target_of_precompact`.

## References

* [M. Hirsch, *Differential Topology*][Hirsch1976], Chapter 2, §1
-/

public section

open Bundle Filter Set Topology TopologicalSpace
open scoped Manifold ContDiff TauCeti.ManifoldWeakWhitney

namespace TauCeti

namespace FiniteBundleAtlas

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]
  {n : ℕ∞ω} [ContMDiffVectorBundle n F V 𝓘(𝕜, E)]

/-- On the target of the chart at `A.center i` of an open set `U'` inside the base set of the
bundle chart `A.triv i`, the frame coordinates of a `Cⁿ` section `t` in `A.triv i`, read through
the charts, are the chart reading `A.coord i t`. -/
theorem coord_eqOn_frameCoordinates (A : FiniteBundleAtlas E M F V) (i : Fin A.n) {U' : Opens M}
    (hU' : (U' : Set M) ⊆ (A.triv i).baseSet) (hx : A.center i ∈ U')
    (t : Cₛ^n⟮𝓘(𝕜, E); F, V⟯) :
    EqOn (extChartAt 𝓘(𝕜, F) (0 : F) ∘ (A.triv i).frameCoordinates (n := n) hU' t ∘
        (extChartAt 𝓘(𝕜, E) (⟨A.center i, hx⟩ : U')).symm)
      (A.coord i t) (extChartAt 𝓘(𝕜, E) (⟨A.center i, hx⟩ : U')).target := fun z hz ↦ by
  have hz' := Opens.coe_extChartAt_symm_apply U' ⟨A.center i, hx⟩ hz
  simp only [extChartAt_coe_symm, modelWithCornersSelf_coe_symm, Function.comp_id] at hz'
  simp only [Bundle.Trivialization.frameCoordinates_apply, A.coord_def, Function.comp_apply,
    extChartAt_coe_symm, modelWithCornersSelf_coe_symm, Function.comp_id]
  exact congrArg (fun y ↦ (A.triv i ⟨y, t y⟩).2) hz'

/-- On the target of the chart at `A.center i` of an open set `U'` inside the base set of the
bundle chart `A.triv i`, the `m`-th derivative within that target of the frame coordinates of a
`Cⁿ` section `t` in `A.triv i`, read through the charts, is the `m`-th derivative of the chart
reading `A.coord i t`. -/
theorem iteratedFDerivWithin_frameCoordinates_eq (A : FiniteBundleAtlas E M F V) (i : Fin A.n)
    {U' : Opens M} (hU' : (U' : Set M) ⊆ (A.triv i).baseSet) (hx : A.center i ∈ U')
    (t : Cₛ^n⟮𝓘(𝕜, E); F, V⟯) (m : ℕ) {w : E}
    (hw : w ∈ (extChartAt 𝓘(𝕜, E) (⟨A.center i, hx⟩ : U')).target) :
    iteratedFDerivWithin 𝕜 m (extChartAt 𝓘(𝕜, F) (0 : F) ∘
        (A.triv i).frameCoordinates (n := n) hU' t ∘
          (extChartAt 𝓘(𝕜, E) (⟨A.center i, hx⟩ : U')).symm)
      (extChartAt 𝓘(𝕜, E) (⟨A.center i, hx⟩ : U')).target w =
      iteratedFDeriv 𝕜 m (A.coord i t) w := by
  rw [← iteratedFDerivWithin_of_isOpen m (isOpen_extChartAt_target _) hw]
  exact iteratedFDerivWithin_congr (A.coord_eqOn_frameCoordinates i hU' hx t) hw m

/-- On the target of the chart at `A.center i` of an open set `U'` inside the base set of the
bundle chart `A.triv i`, the chart derivative of order `m ≤ n` of the frame coordinates of a `Cⁿ`
section `t` in `A.triv i` (`ContMDiffMap.chartIteratedFDeriv`) is the `m`-th derivative of the
chart reading `A.coord i t`. -/
theorem chartIteratedFDeriv_frameCoordinates_eq (A : FiniteBundleAtlas E M F V) (i : Fin A.n)
    {U' : Opens M} (hU' : (U' : Set M) ⊆ (A.triv i).baseSet) (hx : A.center i ∈ U')
    (t : Cₛ^n⟮𝓘(𝕜, E); F, V⟯) [IsManifold 𝓘(𝕜, E) n M] {m : ℕ} (hm : (m : ℕ∞ω) ≤ n)
    (z : (extChartAt 𝓘(𝕜, E) (⟨A.center i, hx⟩ : U')).target) :
    ContMDiffMap.chartIteratedFDeriv ((A.triv i).frameCoordinates hU' t) ⟨A.center i, hx⟩ m hm z =
      iteratedFDeriv 𝕜 m (A.coord i t) z := by
  have h := A.iteratedFDerivWithin_frameCoordinates_eq i hU' hx t m z.property
  rw [extChartAt_model_space_eq_id, PartialEquiv.refl_coe, Function.id_comp] at h
  rw [ContMDiffMap.chartIteratedFDeriv_self_target_apply, h]

variable [LocallyCompactSpace E] [IsManifold 𝓘(𝕜, E) n M]
  {ι : Type*} {e : ι → Trivialization F (π F V)} [∀ i, MemTrivializationAtlas (e i)]
  {U : ι → Opens M} {hU : ∀ i, (U i : Set M) ⊆ (e i).baseSet}

/-- If `Cⁿ` sections `s p` tend to `s₀` along `l` in the frame topology of a frame system covering
`M`, then in every chart `i` of a finite bundle atlas `A` and for every order `j ≤ n`, the `j`-th
derivatives of the chart readings `A.coord i (s p)` tend to that of `A.coord i s₀` uniformly on
the chart image `A.image i`. -/
theorem tendstoUniformlyOn_iteratedFDeriv_coord_of_tendsto (hcover : ∀ x, ∃ i, x ∈ U i)
    {P : Type*} {l : Filter P} {s : P → Cₛ^n⟮𝓘(𝕜, E); F, V⟯} {s₀ : Cₛ^n⟮𝓘(𝕜, E); F, V⟯}
    (hs : letI := ContMDiffSection.frameTopology (I := 𝓘(𝕜, E)) (n := n) e U hU
      Tendsto s l (𝓝 s₀))
    (A : FiniteBundleAtlas E M F V) (i : Fin A.n) {j : ℕ} (hj : j ≤ n) :
    TendstoUniformlyOn (fun p ↦ iteratedFDeriv 𝕜 j (A.coord i (s p)))
      (iteratedFDeriv 𝕜 j (A.coord i s₀)) l (A.image i) := by
  let := ContMDiffSection.frameTopology (I := 𝓘(𝕜, E)) (n := n) e U hU
  -- The frame of the bundle chart `A.triv i` over its whole base set.
  let U' : Opens M := ⟨(A.triv i).baseSet, (A.triv i).open_baseSet⟩
  let x : U' := ⟨A.center i, mem_baseSet_trivializationAt F V (A.center i)⟩
  let φ := extChartAt 𝓘(𝕜, E) x
  have hT := ((ContMDiffSection.continuous_frameCoordinates_of_cover e U hU hcover (A.triv i) U'
    subset_rfl).tendsto s₀).comp hs
  -- The chart image of the closure of the chart domain is a compact subset of `φ.target`.
  have hCc := A.isCompact_chart_image_closure_dom i
  have hCt : A.chart i '' closure (A.dom i) ⊆ φ.target := by
    rw [Opens.extChartAt_target_eq]
    simpa [x, U'] using A.chart_image_closure_dom_subset i
  -- On `φ.target`, the frame coordinates read through `φ` are the chart readings of `A`.
  have hread (t : Cₛ^n⟮𝓘(𝕜, E); F, V⟯) {w : E} (hw : w ∈ φ.target) :=
    A.iteratedFDerivWithin_frameCoordinates_eq i (subset_rfl : (U' : Set M) ⊆ _) x.property t j hw
  let f₀ := (A.triv i).frameCoordinates (I := 𝓘(𝕜, E)) (n := n)
    (subset_rfl : (U' : Set M) ⊆ _) s₀
  have hu := ContMDiffMap.tendstoUniformlyOn_iteratedFDerivWithin_extChartAt (J := 𝓘(𝕜, F))
    (y := (0 : F)) (f₀ := f₀) hCc hCt (fun _ _ ↦ by simp) hj
  have hsub := A.image_subset_chart_image_closure_dom i
  have hlim := (hu.comp_tendsto hT).mono hsub
  exact (hlim.congr (Eventually.of_forall fun p w hw ↦ hread (s p) (hCt (hsub hw)))).congr_right
    fun w hw ↦ hread s₀ (hCt (hsub hw))

/-- If, in every chart `i` of a finite bundle atlas `A` and for every order `j ≤ n`, the `j`-th
derivatives of the chart readings `A.coord i (s p)` of `Cⁿ` sections tend to that of
`A.coord i s₀` locally uniformly on the chart image `A.image i`, then `s p` tends to `s₀` along `l`
in the frame topology of every frame system `(e, U)`, covering `M` or not. -/
theorem tendsto_frameTopology_of_tendstoLocallyUniformlyOn (A : FiniteBundleAtlas E M F V)
    {P : Type*} {l : Filter P} {s : P → Cₛ^n⟮𝓘(𝕜, E); F, V⟯} {s₀ : Cₛ^n⟮𝓘(𝕜, E); F, V⟯}
    (hs : ∀ (i : Fin A.n) (j : ℕ), (j : ℕ∞ω) ≤ n →
      TendstoLocallyUniformlyOn (fun p ↦ iteratedFDeriv 𝕜 j (A.coord i (s p)))
        (iteratedFDeriv 𝕜 j (A.coord i s₀)) l (A.image i)) :
    letI := ContMDiffSection.frameTopology (I := 𝓘(𝕜, E)) (n := n) e U hU
    Tendsto s l (𝓝 s₀) := by
  let := ContMDiffSection.frameTopology (I := 𝓘(𝕜, E)) (n := n) e U hU
  -- Every point has a compact neighbourhood, read in some chart of `A`, inside its chart image.
  have hpiece (y : M) : ∃ i : Fin A.n, ∃ b : Set E, IsCompact b ∧ b ⊆ A.image i ∧
      y ∈ A.dom i ∧ A.chart i y ∈ interior b := by
    obtain ⟨i, hi⟩ := A.exists_mem_dom y
    obtain ⟨b, hb, hyb, hbi⟩ := exists_compact_subset (A.image i).isOpen
      (A.mem_image.mpr ⟨y, hi, rfl⟩)
    exact ⟨i, b, hb, hbi, hi, hyb⟩
  choose σ b hb hbσ hdom hint using hpiece
  have := A.compactSpace
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover
    (fun y ↦ A.dom (σ y) ∩ A.chart (σ y) ⁻¹' interior (b y))
    (fun y ↦ A.isOpen_dom_inter_preimage _ isOpen_interior)
    (fun y _ ↦ mem_iUnion.mpr ⟨y, hdom y, hint y⟩)
  -- The finite chart-frame atlas: the bundle charts of `A` over their base sets, read in the
  -- charts at the centres of `A`, with the compact pieces `b y` for `y ∈ T`.
  let e' : T → Trivialization F (π F V) := fun y ↦ A.triv (σ y)
  let U' : T → Opens M := fun y ↦ ⟨(e' y).baseSet, (e' y).open_baseSet⟩
  have hU' (y : T) : (U' y : Set M) ⊆ (e' y).baseSet := subset_rfl
  let c : ∀ y, U' y := fun y ↦ ⟨A.center (σ y), mem_baseSet_trivializationAt F V _⟩
  have hbt (y : T) : b y ⊆ (extChartAt 𝓘(𝕜, E) (c y)).target := by
    rw [Opens.extChartAt_target_eq]
    simpa [c, U', e'] using (hbσ y).trans (A.image_subset_target_inter_preimage_baseSet _)
  let K : ∀ y, Compacts (extChartAt 𝓘(𝕜, E) (c y)).target := fun y ↦
    ⟨Subtype.val ⁻¹' b y, by
      rw [Subtype.isCompact_iff, Subtype.image_preimage_coe, inter_eq_right.mpr (hbt y)]
      exact hb y⟩
  have hK (x : M) : ∃ y, ∃ hxU : x ∈ U' y,
      ∃ hx : (⟨x, hxU⟩ : U' y) ∈ (extChartAt 𝓘(𝕜, E) (c y)).source,
        (⟨extChartAt 𝓘(𝕜, E) (c y) ⟨x, hxU⟩, (extChartAt 𝓘(𝕜, E) (c y)).map_source hx⟩ :
          (extChartAt 𝓘(𝕜, E) (c y)).target) ∈
          interior (K y : Set (extChartAt 𝓘(𝕜, E) (c y)).target) := by
    obtain ⟨y, hyT, hxy⟩ := mem_iUnion₂.mp (hT (mem_univ x))
    have hxU : x ∈ U' ⟨y, hyT⟩ := A.dom_subset_baseSet _ hxy.1
    have hxs : (⟨x, hxU⟩ : U' ⟨y, hyT⟩) ∈ (extChartAt 𝓘(𝕜, E) (c ⟨y, hyT⟩)).source := by
      rw [Opens.extChartAt_source_eq]
      simpa [c] using A.dom_subset_chart_source _ hxy.1
    refine ⟨⟨y, hyT⟩, hxU, hxs, interior_maximal (preimage_mono interior_subset)
      (isOpen_interior.preimage continuous_subtypeVal) ?_⟩
    simp only [mem_preimage, Opens.extChartAt_apply]
    simpa [c] using hxy.2
  -- The finite-atlas seminorms of `s p - s₀` tend to zero.
  refine ContMDiffSection.tendsto_frameTopology_of_tendsto_finiteAtlasSeminorm e' U' hU' hK e U hU
    fun m hm ↦ tendsto_order.mpr ⟨fun r hr ↦ Eventually.of_forall fun p ↦
      hr.trans_le (apply_nonneg _ _), fun ε hε ↦ ?_⟩
  have hu (y : T) (m' : ℕ) (hm' : m' ∈ Finset.range (m + 1)) : ∀ᶠ p in l, ∀ z ∈ b y,
      dist (iteratedFDeriv 𝕜 m' (A.coord (σ y) s₀) z)
        (iteratedFDeriv 𝕜 m' (A.coord (σ y) (s p)) z) < ε := by
    have hm'm : (m' : ℕ∞ω) ≤ n :=
      (Nat.cast_le.mpr (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm'))).trans hm
    exact Metric.tendstoUniformlyOn_iff.mp ((tendstoLocallyUniformlyOn_iff_forall_isCompact
      (A.image _).isOpen).mp (hs _ m' hm'm) _ (hbσ y) (hb y)) ε hε
  filter_upwards [eventually_all.mpr fun y ↦ (eventually_all_finset _).mpr (hu y)] with p hp
  refine (ContMDiffSection.finiteAtlasSeminorm_lt_iff e' U' hU' c K m hm _ hε).mpr
    fun y m' hm' z hz ↦ ?_
  rw [map_sub, ContMDiffMap.chartIteratedFDeriv_sub, ContinuousMap.sub_apply,
    A.chartIteratedFDeriv_frameCoordinates_eq, A.chartIteratedFDeriv_frameCoordinates_eq,
    ← dist_eq_norm, dist_comm]
  exact hp y m' (Finset.mem_range.mpr (Nat.lt_succ_of_le hm')) z hz

/-- For a frame system `(e, U)` covering `M` and a finite bundle atlas `A`, `Cⁿ` sections `s p`
tend to `s₀` along `l` in the frame topology if and only if, in every chart `i` of `A` and for
every order `j ≤ n`, the `j`-th derivatives of the chart readings `A.coord i (s p)` tend to that
of `A.coord i s₀` locally uniformly on the chart image `A.image i`. -/
theorem tendsto_frameTopology_iff_tendstoLocallyUniformlyOn (hcover : ∀ x, ∃ i, x ∈ U i)
    (A : FiniteBundleAtlas E M F V)
    {P : Type*} {l : Filter P} {s : P → Cₛ^n⟮𝓘(𝕜, E); F, V⟯} {s₀ : Cₛ^n⟮𝓘(𝕜, E); F, V⟯} :
    letI := ContMDiffSection.frameTopology (I := 𝓘(𝕜, E)) (n := n) e U hU
    Tendsto s l (𝓝 s₀) ↔ ∀ (i : Fin A.n) (j : ℕ), (j : ℕ∞ω) ≤ n →
      TendstoLocallyUniformlyOn (fun p ↦ iteratedFDeriv 𝕜 j (A.coord i (s p)))
        (iteratedFDeriv 𝕜 j (A.coord i s₀)) l (A.image i) :=
  ⟨fun h i _ hj ↦
    (tendstoUniformlyOn_iteratedFDeriv_coord_of_tendsto hcover h A i hj).tendstoLocallyUniformlyOn,
    tendsto_frameTopology_of_tendstoLocallyUniformlyOn A⟩

end FiniteBundleAtlas

end TauCeti

end
