/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Flow
public import TauCeti.Geometry.Manifold.SmoothIsotopy.Diffeotopy
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import TauCeti.Geometry.Manifold.ContMDiffMap.Basic
import TauCeti.Geometry.Manifold.SmoothEmbedding.Diffeomorph
import SymplecticGeometry.Geometry.Manifold.Flow.BandCrossing
import SymplecticGeometry.Geometry.Manifold.SmoothIsotopy.Basic
import SymplecticGeometry.Geometry.Manifold.VectorField.ModelChart
import SymplecticGeometry.Topology.Order.Sublevel

/-!
# Band cores, and pushing a band without critical points down

Let `f` be a smooth real function on a boundaryless finite-dimensional manifold `M`, and let the
band `f⁻¹[a, b]` be compact and free of critical points of `f`. For every open set `U` containing
the sublevel `{f ≤ a}`, there is a smooth diffeotopy of `M` that does not move a neighbourhood of
`{f ≤ a}` and whose final diffeomorphism carries `{f ≤ b}` into `U`
(`TauCeti.exists_diffeotopy_mapsTo_of_sublevel_subset`).

The flows of `TauCeti.exists_flow_apply_eq_sub` and `TauCeti.exists_diffeomorph_sublevel` move
points of `{f ≤ a}` too. Here the descending field is multiplied by a smooth function of `f` that
vanishes on `{f ≤ a + ε / 3}` and is `1` on `{f ≥ a + 2 ε / 3}`, where `ε ≤ b - a` and
`{f ≤ a + ε} ⊆ U` (`exists_pos_sublevel_subset_of_isCompact_preimage_Icc`), and the cut-off field
is run for the time `b - a` by `TauCeti.compactlySupportedFlowDiffeotopy`. On the band
`f⁻¹[a + 2 ε / 3, b]` the cut-off field descends at unit speed, so every orbit starting in
`{f ≤ b}` leaves it downwards within the time `b - a`
(`IsMIntegralCurve.apply_lt_of_mvfderiv_apply_le_neg`).
The descending field is `TauCeti.exists_vectorField_mvfderiv_eq_neg_one_of_boundaryless`.

A band core `SymplecticGeometry.BandCore I g a₀ a b` of `g : M → ℝ` is a finite family of pairwise
disjoint cubes of positive codimension, each the image of the cube `closedBall 0 1 ×ˢ {0}` of
`(Fin m → ℝ) × (Fin (finrank ℝ E - m) → ℝ)` under a smooth open embedding, above the level `a₀`
and with boundary sphere below the level `a`, together with a compression: every open set
containing `{g ≤ a}` and the cubes receives `{g ≤ b}` at the end of a smooth isotopy of the
identity that fixes a neighbourhood of `{g ≤ a}`. A band without critical points has the band
core without cubes (`SymplecticGeometry.BandCore.ofNoCriticalPoint`), whose compression is
`TauCeti.Diffeotopy.smoothIsotopy` of the diffeotopy above.

## Main declarations

* `TauCeti.exists_diffeotopy_mapsTo_of_sublevel_subset`: the diffeotopy fixed near `{f ≤ a}`
  carrying `{f ≤ b}` into a given open neighbourhood of `{f ≤ a}`.
* `SymplecticGeometry.BandCore`: band cores; `SymplecticGeometry.BandCore.cubes`, the union of
  the cubes, compact (`isCompact_cubes`) and above `a₀` (`cubes_subset`).
* `SymplecticGeometry.BandCore.ofNoCriticalPoint`: the band core without cubes.
* `SymplecticGeometry.BandCore.ofDiffeomorph`: the pullback of a band core along a
  diffeomorphism, whose cubes are the old ones moved back (`cubes_ofDiffeomorph`); it may change
  the model but not its vector space.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorem 3.1.
* [Y. Eliashberg and N. Mishachev, *Introduction to the h-Principle*][EliashbergMishachev2002]
-/

public section

open Function Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [I.Boundaryless]
  [IsManifold I ∞ M] {f : M → ℝ} {a b : ℝ}

/-- **Pushing a band without critical points down, fixing a neighbourhood of the sublevel below
it.** Let `f` be smooth, let the band `f⁻¹[a, b]` be compact and contain no critical point of `f`,
and let `U` be an open set containing the sublevel `{f ≤ a}`. Then there is a smooth diffeotopy
`Φ` of `M` that fixes every point of some neighbourhood of `{f ≤ a}` at all times, and whose
final diffeomorphism carries `{f ≤ b}` into `U`. -/
theorem exists_diffeotopy_mapsTo_of_sublevel_subset (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hcompact : IsCompact (f ⁻¹' Icc a b))
    (hreg : ∀ x, a ≤ f x → f x ≤ b → mfderiv I 𝓘(ℝ) f x ≠ 0)
    {U : Set M} (hU : IsOpen U) (hsub : {x | f x ≤ a} ⊆ U) :
    ∃ Φ : Diffeotopy I ∞ M, (∃ V ∈ 𝓝ˢ {x | f x ≤ a}, ∀ t, ∀ x ∈ V, Φ (t, x) = x) ∧
      MapsTo Φ.final {x | f x ≤ b} U := by
  rcases le_or_gt b a with hba | hab
  · -- Without a band, the identity diffeotopy does.
    refine ⟨Diffeotopy.refl I ∞ M, ⟨univ, Filter.univ_mem, fun t x _ ↦ Diffeotopy.refl_apply _⟩,
      fun x hx ↦ ?_⟩
    rw [Diffeotopy.final_apply, Diffeotopy.refl_apply]
    exact hsub ((show f x ≤ b from hx).trans hba)
  have : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
  -- `ε ≤ b - a`, so that the level `a + 2 ε / 3` is in the band.
  obtain ⟨ε, hε, hεb, hεU⟩ :=
    exists_pos_sublevel_subset_of_isCompact_preimage_Icc hf.continuous hab hcompact
      (hU.mem_nhdsSet.2 hsub)
  -- The cutoff `ρ ∘ f` vanishes below `c = a + ε / 3` and is `1` above `d = a + 2 ε / 3`.
  set c := a + ε / 3 with hc
  set d := a + 2 * ε / 3 with hd
  have hcd : c < d := by linarith
  set ρ : ℝ → ℝ := fun s ↦ Real.smoothTransition ((s - c) / (d - c))
  have hρC : ContMDiff I 𝓘(ℝ) ∞ (ρ ∘ f) :=
    (Real.smoothTransition.contDiff.comp
      ((contDiff_id.sub contDiff_const).div_const _)).contMDiff.comp hf
  have hρ0 : ∀ s, s ≤ c → ρ s = 0 := fun s hs ↦
    Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith)
      (by linarith))
  have hρ1 : ∀ s, d ≤ s → ρ s = 1 := fun s hs ↦
    Real.smoothTransition.one_of_one_le ((one_le_div (by linarith)).2 (by linarith))
  obtain ⟨X, hX, -, ⟨W, -, hKW, hXW⟩, C, hC, hXC⟩ :=
    exists_vectorField_mvfderiv_eq_neg_one_of_boundaryless hf hcompact
      fun x hx ↦ hreg x hx.1 hx.2
  -- The cut-off field `Y = (ρ ∘ f) • X`.
  set Y : (x : M) → TangentSpace I x := fun x ↦ ρ (f x) • X x with hY
  have hYC : ContMDiff I I.tangent ∞ (fun x ↦ (⟨x, Y x⟩ : TangentBundle I M)) :=
    hρC.smul_section hX
  have hYzero : ∀ x ∉ C, Y x = 0 := fun x hx ↦ by simp [hY, hXC x hx]
  have hdY : ∀ x, mvfderiv I f x (Y x) = ρ (f x) * mvfderiv I f x (X x) := fun x ↦
    (map_smul (mvfderiv I f x) (ρ (f x)) (X x)).trans (smul_eq_mul _ _)
  have hYW : ∀ x ∈ W ∩ {x | d ≤ f x}, mvfderiv I f x (Y x) = -1 := fun x hx ↦ by
    rw [hdY, hρ1 _ hx.2, hXW x hx.1, one_mul]
  have hY1 : ContMDiff I I.tangent 1 (fun x ↦ (⟨x, Y x⟩ : TangentBundle I M)) :=
    hYC.of_le (by simp)
  have hcomplete := isCompleteVectorField_of_isCompact_of_eq_zero_off hY1 hC hYzero
  refine ⟨compactlySupportedFlowDiffeotopy (n := ⊤) (by simp) hYC hC hYzero (b - a),
    ⟨{x | f x < c}, (isOpen_lt hf.continuous continuous_const).mem_nhdsSet.2
      fun x hx ↦ (show f x ≤ a from hx).trans_lt (by linarith), fun t x hx ↦ ?_⟩,
    fun x hx ↦ ?_⟩
  · refine compactlySupportedFlowDiffeotopy_apply_of_eq_zero _ hYC hC hYzero _ ?_ t
    simp [hY, hρ0 _ (show f x < c from hx).le]
  -- A point of `{f ≤ b}` whose orbit stayed in the band `f⁻¹[d, b]` would descend at unit
  -- speed for the time `b - a`, ending below `a`.
  rw [Diffeotopy.final_apply, compactlySupportedFlowDiffeotopy_apply, Set.Icc.coe_one, mul_one,
    ← globalFlow_apply hY1 hcomplete]
  have hx0 : f (globalFlow Y hY1 hcomplete 0 x) ≤ b := by
    rw [Flow.map_zero_apply]
    exact hx
  refine hεU (show f (globalFlow Y hY1 hcomplete (b - a) x) ≤ a + ε from
    (((isMIntegralCurve_globalFlow hY1 hcomplete x).apply_lt_of_mvfderiv_apply_le_neg
      (fun _ ↦ hf.mdifferentiableAt (by simp)) (by linarith : d ≤ b)
      (fun u hdu hub ↦ (hYW _ ⟨hKW ⟨by linarith, hub⟩, hdu⟩).le) (ε := 1) hx0
      (by linarith) (by linarith)).trans_le (by linarith)).le)

end TauCeti

namespace SymplecticGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- A **band core** of `g : M → ℝ` for the levels `a₀`, `a`, `b`: finitely many pairwise
disjoint cubes of positive codimension, lying above the level `a₀` with their boundary spheres
below the level `a`, such that every open set containing `{g ≤ a}` and the cubes receives
`{g ≤ b}` at the end of a smooth isotopy from the identity that fixes a neighbourhood of
`{g ≤ a}`.

The cube `i` has dimension `m = dim i`. It is the image of `closedBall 0 1 ×ˢ {0}` under a smooth
open embedding `chart i` of the whole of `(Fin m → ℝ) × (Fin (finrank ℝ E - m) → ℝ)` (with sup
norms) into `M`, and its boundary sphere is the image of `sphere 0 1 ×ˢ {0}`. -/
structure BandCore (g : M → ℝ) (a₀ a b : ℝ) where
  /-- The index type of the cubes. -/
  ι : Type
  /-- There are finitely many cubes. -/
  [fintype : Fintype ι]
  /-- The dimension of each cube. -/
  dim : ι → ℕ
  /-- Each cube has positive codimension. -/
  dim_lt (i : ι) : dim i < Module.finrank ℝ E
  /-- The coordinates around each cube. -/
  chart (i : ι) : (Fin (dim i) → ℝ) × (Fin (Module.finrank ℝ E - dim i) → ℝ) → M
  /-- Each chart is a smooth embedding. -/
  isSmoothEmbedding_chart (i : ι) : Manifold.IsSmoothEmbedding
    𝓘(ℝ, (Fin (dim i) → ℝ) × (Fin (Module.finrank ℝ E - dim i) → ℝ)) I ∞ (chart i)
  /-- Each chart has open range. -/
  isOpen_range_chart (i : ι) : IsOpen (range (chart i))
  /-- Each cube lies above the level `a₀`. -/
  mapsTo_cube (i : ι) : MapsTo (chart i) (Metric.closedBall 0 1 ×ˢ {0}) {x | a₀ < g x}
  /-- The boundary sphere of each cube lies below the level `a`. -/
  mapsTo_sphere (i : ι) : MapsTo (chart i) (Metric.sphere 0 1 ×ˢ {0}) {x | g x < a}
  /-- Distinct cubes are disjoint. -/
  pairwise_disjoint : Pairwise fun i j ↦
    Disjoint (chart i '' Metric.closedBall 0 1 ×ˢ {0}) (chart j '' Metric.closedBall 0 1 ×ˢ {0})
  /-- Every open set containing `{g ≤ a}` and the cubes receives `{g ≤ b}` at the end of a
  smooth isotopy from the identity that fixes a neighbourhood of `{g ≤ a}`. -/
  exists_compression (U : Set M) (hU : IsOpen U)
      (hsub : {x | g x ≤ a} ∪ ⋃ i, chart i '' Metric.closedBall 0 1 ×ˢ {0} ⊆ U) :
    ∃ (f : C^∞⟮I, M; I, M⟯) (F : TauCeti.SmoothIsotopy ContMDiffMap.id f),
      (∃ V ∈ 𝓝ˢ {x | g x ≤ a}, ∀ t, ∀ x ∈ V, F (t, x) = x) ∧ MapsTo f {x | g x ≤ b} U

namespace BandCore

attribute [instance] BandCore.fintype

variable {I} {g : M → ℝ} {a₀ a b : ℝ}

/-- The union of the cubes of a band core. -/
def cubes (c : BandCore I g a₀ a b) : Set M :=
  ⋃ i, c.chart i '' Metric.closedBall 0 1 ×ˢ {0}

/-- The cubes of a band core are the images of the unit cube under its charts. -/
theorem cubes_def (c : BandCore I g a₀ a b) :
    c.cubes = ⋃ i, c.chart i '' Metric.closedBall 0 1 ×ˢ {0} := (rfl)

/-- Each cube of a band core lies in its cubes. -/
theorem image_chart_subset_cubes (c : BandCore I g a₀ a b) (i : c.ι) :
    c.chart i '' Metric.closedBall 0 1 ×ˢ {0} ⊆ c.cubes := by
  rw [cubes_def]
  exact subset_iUnion (fun j ↦ c.chart j '' Metric.closedBall 0 1 ×ˢ {0}) i

/-- Every open set containing `{g ≤ a}` and the cubes of a band core receives `{g ≤ b}` at the
end of a smooth isotopy from the identity that fixes a neighbourhood of `{g ≤ a}`. -/
theorem exists_compression_of_subset (c : BandCore I g a₀ a b) {U : Set M} (hU : IsOpen U)
    (hsub : {x | g x ≤ a} ∪ c.cubes ⊆ U) :
    ∃ (f : C^∞⟮I, M; I, M⟯) (F : TauCeti.SmoothIsotopy ContMDiffMap.id f),
      (∃ V ∈ 𝓝ˢ {x | g x ≤ a}, ∀ t, ∀ x ∈ V, F (t, x) = x) ∧ MapsTo f {x | g x ≤ b} U :=
  c.exists_compression U hU (by rwa [← cubes_def])

/-- A point lies in the cubes when some chart sends a point of the unit cube to it. -/
theorem mem_cubes_iff (c : BandCore I g a₀ a b) {x : M} :
    x ∈ c.cubes ↔ ∃ i, ∃ v ∈ Metric.closedBall 0 1 ×ˢ {0}, c.chart i v = x := by
  simp only [cubes_def, mem_iUnion, mem_image]

/-- The cubes of a band core form a compact set. -/
theorem isCompact_cubes (c : BandCore I g a₀ a b) : IsCompact c.cubes :=
  isCompact_iUnion fun i ↦ ((isCompact_closedBall 0 1).prod isCompact_singleton).image
    (c.isSmoothEmbedding_chart i).contMDiff.continuous

/-- The cubes of a band core lie above the level `a₀`. -/
theorem cubes_subset (c : BandCore I g a₀ a b) : c.cubes ⊆ {x | a₀ < g x} :=
  iUnion_subset fun i ↦ (c.mapsTo_cube i).image_subset

section ofDiffeomorph

variable [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E H'} [J.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] {g : N → ℝ}

/-- The **pullback of a band core along a diffeomorphism** `Φ : M ≃ₘ^∞⟮I, J⟯ N` between
boundaryless manifolds whose models share the vector space `E`: a band core of `g : N → ℝ` gives
the band core of `g ∘ Φ` with the same cubes moved by `Φ.symm`. Its charts are `Φ.symm ∘ chart i`,
and its compression for an open `U ⊆ M` is the compression `F` of `c` for `Φ '' U` conjugated by
`Φ`, the isotopy `(t, x) ↦ Φ.symm (F (t, Φ x))`. -/
@[expose] noncomputable def ofDiffeomorph (Φ : M ≃ₘ^∞⟮I, J⟯ N) (c : BandCore J g a₀ a b) :
    BandCore I (g ∘ Φ) a₀ a b where
  ι := c.ι
  dim := c.dim
  dim_lt := c.dim_lt
  chart i := Φ.symm ∘ c.chart i
  -- A tactic proof, so that the exposed body may use the privately imported lemma.
  isSmoothEmbedding_chart i := by
    exact Φ.symm.isSmoothEmbedding_comp (by simp) (c.isSmoothEmbedding_chart i)
  isOpen_range_chart i := by
    rw [range_comp, ← Diffeomorph.coe_toHomeomorph]
    exact Φ.symm.toHomeomorph.isOpenMap _ (c.isOpen_range_chart i)
  mapsTo_cube i v hv := by simpa using c.mapsTo_cube i hv
  mapsTo_sphere i v hv := by simpa using c.mapsTo_sphere i hv
  pairwise_disjoint i j hij := by
    simp only [image_comp]
    exact (disjoint_image_iff Φ.symm.injective).2 (c.pairwise_disjoint hij)
  exists_compression U hU hsub := by
    have hΦ : Manifold.IsSmoothEmbedding I J ∞ Φ :=
      Φ.isSmoothEmbedding_comp (f := id) (by simp) Manifold.IsSmoothEmbedding.id
    have hΦs : Manifold.IsSmoothEmbedding J I ∞ Φ.symm :=
      Φ.symm.isSmoothEmbedding_comp (f := id) (by simp) Manifold.IsSmoothEmbedding.id
    have hsub' : {y | g y ≤ a} ∪ ⋃ i, c.chart i '' Metric.closedBall 0 1 ×ˢ {0} ⊆ Φ '' U := by
      rw [Φ.image_eq_preimage_symm]
      rintro y (hy | hy)
      · exact hsub (Or.inl (by simpa using hy))
      · refine hsub (Or.inr ?_)
        obtain ⟨i, hi⟩ := mem_iUnion.1 hy
        exact mem_iUnion.2 ⟨i, by rw [image_comp]; exact mem_image_of_mem _ hi⟩
    have hU' : IsOpen (Φ '' U) := by
      rw [← Diffeomorph.coe_toHomeomorph]
      exact Φ.toHomeomorph.isOpenMap _ hU
    obtain ⟨f, F, ⟨V, hV, hFV⟩, hf⟩ := c.exists_compression _ hU' hsub'
    -- The compression of `c` for `Φ '' U`, conjugated by `Φ`.
    let g₀ : C^∞⟮I, M; J, N⟯ := ⟨Φ, Φ.contMDiff⟩
    let g₁ : C^∞⟮I, M; J, N⟯ := ⟨f ∘ Φ, f.contMDiff.comp Φ.contMDiff⟩
    let f' : C^∞⟮I, M; I, M⟯ :=
      ⟨Φ.symm ∘ f ∘ Φ, Φ.symm.contMDiff.comp (f.contMDiff.comp Φ.contMDiff)⟩
    have hg₀ (y : M) : g₀ y = (ContMDiffMap.id : C^∞⟮J, N; J, N⟯) (Φ y) := by
      simp [g₀, ContMDiffMap.id]
    have hg₁ (y : M) : g₁ y = f (Φ y) := by simp [g₁]
    have hid (x : M) : (ContMDiffMap.id : C^∞⟮I, M; I, M⟯) x = Φ.symm (g₀ x) := by
      simp [g₀, ContMDiffMap.id]
    have hf' (x : M) : f' x = Φ.symm (g₁ x) := by simp [f', g₁]
    refine ⟨f', (F.precompSmoothEmbedding Φ hΦ (by simp) g₀ g₁ hg₀ hg₁).postcompSmoothEmbedding
      Φ.symm hΦs (by simp) ContMDiffMap.id f' hid hf',
      ⟨Φ ⁻¹' V, ?_, fun t x hx ↦ ?_⟩, fun x hx ↦ ?_⟩
    · exact Φ.continuous.tendsto_nhdsSet (fun x hx ↦ hx) hV
    · rw [TauCeti.SmoothIsotopy.postcompSmoothEmbedding_apply,
        TauCeti.SmoothIsotopy.precompSmoothEmbedding_apply, hFV t _ hx, Φ.symm_apply_apply]
    · obtain ⟨y, hy, hxy⟩ := hf (show g (Φ x) ≤ b from hx)
      simpa [f', ← hxy] using hy

/-- The cubes of `c.ofDiffeomorph Φ` are indexed by those of `c`. -/
theorem ofDiffeomorph_ι (Φ : M ≃ₘ^∞⟮I, J⟯ N) (c : BandCore J g a₀ a b) :
    (c.ofDiffeomorph Φ).ι = c.ι := (rfl)

/-- The cubes of `c.ofDiffeomorph Φ` have the dimensions of those of `c`. -/
@[simp]
theorem ofDiffeomorph_dim (Φ : M ≃ₘ^∞⟮I, J⟯ N) (c : BandCore J g a₀ a b) (i : c.ι) :
    (c.ofDiffeomorph Φ).dim i = c.dim i := (rfl)

/-- The charts of `c.ofDiffeomorph Φ` are those of `c` followed by `Φ.symm`. -/
@[simp]
theorem ofDiffeomorph_chart (Φ : M ≃ₘ^∞⟮I, J⟯ N) (c : BandCore J g a₀ a b) (i : c.ι) :
    (c.ofDiffeomorph Φ).chart i = Φ.symm ∘ c.chart i := (rfl)

/-- The cubes of the pullback of a band core along `Φ` are the cubes of the band core moved by
`Φ.symm`. -/
@[simp]
theorem cubes_ofDiffeomorph (Φ : M ≃ₘ^∞⟮I, J⟯ N) (c : BandCore J g a₀ a b) :
    (c.ofDiffeomorph Φ).cubes = Φ.symm '' c.cubes := by
  rw [cubes_def, cubes_def, image_iUnion]
  exact iUnion_congr fun i ↦ image_comp Φ.symm (c.chart i) _

end ofDiffeomorph

variable [FiniteDimensional ℝ E] [T2Space M] [I.Boundaryless] [IsManifold I ∞ M]

/-- The band core without cubes of a smooth `g` whose band `g⁻¹[a, b]` is compact and contains
no critical point of `g`, for any level `a₀`. Its compression is the smooth isotopy of the
identity along the diffeotopy of `TauCeti.exists_diffeotopy_mapsTo_of_sublevel_subset`. -/
noncomputable def ofNoCriticalPoint (hg : ContMDiff I 𝓘(ℝ) ∞ g)
    (hcompact : IsCompact (g ⁻¹' Icc a b))
    (hreg : ∀ x, a ≤ g x → g x ≤ b → mfderiv I 𝓘(ℝ) g x ≠ 0) (a₀ : ℝ) :
    BandCore I g a₀ a b where
  ι := Empty
  dim := Empty.elim
  dim_lt i := i.elim
  chart i := i.elim
  isSmoothEmbedding_chart i := i.elim
  isOpen_range_chart i := i.elim
  mapsTo_cube i := i.elim
  mapsTo_sphere i := i.elim
  pairwise_disjoint i := i.elim
  exists_compression U hU hsub := by
    obtain ⟨Φ, ⟨V, hV, hΦV⟩, hΦ⟩ := TauCeti.exists_diffeotopy_mapsTo_of_sublevel_subset hg
      hcompact hreg hU (subset_union_left.trans hsub)
    refine ⟨_, Φ.smoothIsotopy ContMDiffMap.id Manifold.IsSmoothEmbedding.id,
      ⟨V, hV, fun t x hx ↦ ?_⟩, fun x hx ↦ ?_⟩
    · exact (Φ.smoothIsotopy_apply _ _ (t, x)).trans (hΦV t x hx)
    · simpa using hΦ hx

/-- The band core `ofNoCriticalPoint` has no cubes. -/
@[simp]
theorem cubes_ofNoCriticalPoint (hg : ContMDiff I 𝓘(ℝ) ∞ g)
    (hcompact : IsCompact (g ⁻¹' Icc a b))
    (hreg : ∀ x, a ≤ g x → g x ≤ b → mfderiv I 𝓘(ℝ) g x ≠ 0) (a₀ : ℝ) :
    (ofNoCriticalPoint hg hcompact hreg a₀).cubes = ∅ := by
  simp [cubes_def, ofNoCriticalPoint]

end BandCore

end SymplecticGeometry

end
