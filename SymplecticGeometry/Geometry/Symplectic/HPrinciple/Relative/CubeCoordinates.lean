/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Topology.MetricSpace.Thickening
public import SymplecticGeometry.Geometry.Manifold.Morse.Core.Basic
public import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.Injective
public import SymplecticGeometry.Geometry.Symplectic.HPrinciple.FormalPrimitive
import TauCeti.Geometry.Manifold.Immersion.LocalDiffeomorph
import TauCeti.Geometry.Manifold.ContMDiff.Prod

/-!
# The charts of a band core as coordinates, and the relative set of a cube

Let `c` be a band core (`Morse/Core/Basic.lean`) of a manifold `M` modelled on a
finite-dimensional space `E`. The chart of its cube `i` is a smooth embedding of the normed
space `(Fin m → ℝ) × (Fin (finrank ℝ E - m) → ℝ)`, with `m = c.dim i`, whose dimension is that of
`E`. So it is a local diffeomorphism (`BandCore.isLocalDiffeomorph_chart`, from Tau Ceti's
`Manifold.IsImmersion.isLocalDiffeomorph`), and, being injective, the inverse of a partial
diffeomorphism `BandCore.chartPartialDiffeomorph c i` from `M` to that space, with source the
range of the chart and target the whole space. It is the symm of
`IsLocalDiffeomorph.partialDiffeomorphOfInjective` (`LocalDiffeomorph/Injective.lean`).

For an open `N` containing the sublevel `{g ≤ a}`, `BandCore.exists_relativeSet` gives the set of
core points of a cube over which the relative holonomic approximation of a stage of the
h-principle is asked to change nothing. With `Y` the points of `closedBall 0 2` that the chart
sends into `{g ≤ a}`, it is the set `B` of `u` with `‖u‖ ≤ 1 + η` and `(u, 0)` within `η` of `Y`,
for a margin `0 < η < 1`. It contains the boundary sphere of the cube, since the chart sends
that sphere below `a`; its points `(u, 0)` lie in the preimage of `N`; and a point within
`δ ≤ η / 2` of the cube whose first coordinate is not in `B` is farther than `η / 2` from `Y`, so
the chart sends it above `a`. The set `Y` is described by closed thickenings rather than by
distances, so that a cube of dimension `0`, whose sphere is empty, and for which `Y` may be
empty, needs no separate case.

The forms of a stage are read in the chart of a cube by pullback along it, and give the cube a
formal datum: the reading of the one-form, with the formal primitive (`FormalPrimitive.lean`) of
the reading of the difference of the two-forms. It is holonomic at the points that the chart sends
to where the forms are related, and smooth for smooth families.

## Main declarations

* `SymplecticGeometry.BandCore.isLocalDiffeomorph_chart`: the charts are local diffeomorphisms.
* `SymplecticGeometry.BandCore.chartPartialDiffeomorph`: the inverse of a chart, as a partial
  diffeomorphism, with `chartPartialDiffeomorph_symm_apply`, `chartPartialDiffeomorph_source`,
  `chartPartialDiffeomorph_target` and `chartPartialDiffeomorph_apply_chart`.
* `SymplecticGeometry.BandCore.exists_relativeSet`: the relative set of a cube and its margin.
* `SymplecticGeometry.BandCore.fderiv_mpullback_chart_eq_formalPrimitive`: the formal datum of a
  cube, read in its chart, is holonomic where the forms are related.
* `SymplecticGeometry.BandCore.contDiff_mpullback_chart`,
  `SymplecticGeometry.BandCore.contDiff_formalPrimitive_mpullback_chart`: for smooth families of
  forms, it is smooth in the parameter and the point together.

## References

* [Y. Eliashberg and N. Mishachev, *Introduction to the h-principle*][EliashbergMishachev2002],
  §10.2.
-/

public section

open Function Metric Set
open scoped ContDiff Manifold

namespace SymplecticGeometry

namespace BandCore

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {g : M → ℝ} {a₀ a b : ℝ}

section Chart

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M]

/-- Each chart of a band core is a smooth local diffeomorphism: it is a smooth embedding of a
space of dimension `c.dim i + (finrank ℝ E - c.dim i) = finrank ℝ E`. -/
theorem isLocalDiffeomorph_chart (c : BandCore I g a₀ a b) (i : c.ι) :
    IsLocalDiffeomorph 𝓘(ℝ, (Fin (c.dim i) → ℝ) × (Fin (Module.finrank ℝ E - c.dim i) → ℝ)) I ∞
      (c.chart i) :=
  (c.isSmoothEmbedding_chart i).isImmersion.isLocalDiffeomorph
    (by simp [Module.finrank_prod, Nat.add_sub_cancel' (c.dim_lt i).le]) (by simp)

/-- The inverse of the chart of the cube `i` of a band core, as a partial diffeomorphism from `M`
to the chart's domain `(Fin (c.dim i) → ℝ) × (Fin (finrank ℝ E - c.dim i) → ℝ)`. Its source is
the range of the chart (`chartPartialDiffeomorph_source`), its target is the whole domain
(`chartPartialDiffeomorph_target`), and its inverse is the chart
(`chartPartialDiffeomorph_symm_apply`). -/
noncomputable def chartPartialDiffeomorph (c : BandCore I g a₀ a b) (i : c.ι) :
    PartialDiffeomorph I 𝓘(ℝ, (Fin (c.dim i) → ℝ) × (Fin (Module.finrank ℝ E - c.dim i) → ℝ))
      M ((Fin (c.dim i) → ℝ) × (Fin (Module.finrank ℝ E - c.dim i) → ℝ)) ∞ :=
  (IsLocalDiffeomorph.partialDiffeomorphOfInjective (c.isLocalDiffeomorph_chart i)
    (c.isSmoothEmbedding_chart i).isEmbedding.injective).symm

theorem chartPartialDiffeomorph_def (c : BandCore I g a₀ a b) (i : c.ι) :
    c.chartPartialDiffeomorph i =
      (IsLocalDiffeomorph.partialDiffeomorphOfInjective (c.isLocalDiffeomorph_chart i)
        (c.isSmoothEmbedding_chart i).isEmbedding.injective).symm :=
  (rfl)

/-- The inverse of `chartPartialDiffeomorph c i` is the chart `c.chart i`. (`simp` rewrites the
left side to the inverse of the underlying partial equivalence, for which
`chartPartialDiffeomorph_toPartialEquiv_symm_apply` is the `simp` lemma.) -/
theorem chartPartialDiffeomorph_symm_apply (c : BandCore I g a₀ a b) (i : c.ι) :
    ⇑(c.chartPartialDiffeomorph i).symm = c.chart i := by
  rw [chartPartialDiffeomorph_def]
  exact IsLocalDiffeomorph.coe_partialDiffeomorphOfInjective (c.isLocalDiffeomorph_chart i) _

/-- The inverse of the partial equivalence underlying `chartPartialDiffeomorph c i` sends `v` to
`c.chart i v`. -/
@[simp]
theorem chartPartialDiffeomorph_toPartialEquiv_symm_apply (c : BandCore I g a₀ a b) (i : c.ι)
    (v : (Fin (c.dim i) → ℝ) × (Fin (Module.finrank ℝ E - c.dim i) → ℝ)) :
    (c.chartPartialDiffeomorph i).toPartialEquiv.symm v = c.chart i v := by
  simpa using congrFun (c.chartPartialDiffeomorph_symm_apply i) v

/-- The source of `chartPartialDiffeomorph c i` is the range of the chart. -/
@[simp]
theorem chartPartialDiffeomorph_source (c : BandCore I g a₀ a b) (i : c.ι) :
    (c.chartPartialDiffeomorph i).source = range (c.chart i) := by
  rw [chartPartialDiffeomorph_def, PartialDiffeomorph.symm_toPartialEquiv, PartialEquiv.symm_source]
  exact IsLocalDiffeomorph.partialDiffeomorphOfInjective_target (c.isLocalDiffeomorph_chart i) _

/-- The target of `chartPartialDiffeomorph c i` is the whole domain of the chart. -/
@[simp]
theorem chartPartialDiffeomorph_target (c : BandCore I g a₀ a b) (i : c.ι) :
    (c.chartPartialDiffeomorph i).target = univ := by
  rw [chartPartialDiffeomorph_def, PartialDiffeomorph.symm_toPartialEquiv, PartialEquiv.symm_target]
  exact IsLocalDiffeomorph.partialDiffeomorphOfInjective_source (c.isLocalDiffeomorph_chart i) _

/-- `chartPartialDiffeomorph c i` sends `c.chart i v` back to `v`. -/
@[simp]
theorem chartPartialDiffeomorph_apply_chart (c : BandCore I g a₀ a b) (i : c.ι)
    (v : (Fin (c.dim i) → ℝ) × (Fin (Module.finrank ℝ E - c.dim i) → ℝ)) :
    c.chartPartialDiffeomorph i (c.chart i v) = v := by
  rw [chartPartialDiffeomorph_def]
  exact IsLocalDiffeomorph.partialDiffeomorphOfInjective_symm_apply_apply
    (c.isLocalDiffeomorph_chart i) _ v

end Chart

/-- **The relative set of a cube and its margin.** Let `g` be continuous and `N` an open set
containing `{g ≤ a}`, and let `Y` be the set of points of `closedBall 0 2` that the chart of the
cube `i` sends into `{g ≤ a}`. There is `0 < η < 1` such that the compact set `B` of `u` with
`‖u‖ ≤ 1 + η` and `(u, 0) ∈ cthickening η Y`
1. contains the unit sphere;
2. satisfies `B ×ˢ {0} ⊆ (c.chart i) ⁻¹' N`;
3. for every `0 < δ ≤ η / 2`, every point `p` of `thickening δ (closedBall 0 1 ×ˢ {0})` with
   `p.1 ∉ B` lies outside `cthickening (η / 2) Y`, and the chart sends it above `a`. -/
theorem exists_relativeSet (c : BandCore I g a₀ a b) (hg : Continuous g) {N : Set M}
    (hN : IsOpen N) (haN : {x | g x ≤ a} ⊆ N) (i : c.ι) :
    ∃ η : ℝ, 0 < η ∧ η < 1 ∧ ∃ B : Set (Fin (c.dim i) → ℝ),
      B = {u | ‖u‖ ≤ 1 + η ∧
        (u, 0) ∈ cthickening η (c.chart i ⁻¹' {x | g x ≤ a} ∩ closedBall 0 2)} ∧
      IsCompact B ∧ sphere 0 1 ⊆ B ∧ B ×ˢ {0} ⊆ c.chart i ⁻¹' N ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ η / 2 → ∀ p ∈ thickening δ (closedBall 0 1 ×ˢ {0}), p.1 ∉ B →
        p ∉ cthickening (η / 2) (c.chart i ⁻¹' {x | g x ≤ a} ∩ closedBall 0 2) ∧
          a < g (c.chart i p) := by
  set Y := c.chart i ⁻¹' {x | g x ≤ a} ∩ closedBall 0 2
  have hchart := (c.isSmoothEmbedding_chart i).contMDiff.continuous
  have hYc : IsCompact Y :=
    (isCompact_closedBall _ _).inter_left (isClosed_le (hg.comp hchart) continuous_const)
  obtain ⟨δ₀, hδ₀, hδ₀N⟩ := hYc.exists_cthickening_subset_open (hN.preimage hchart)
    (inter_subset_left.trans (preimage_mono haN))
  set η := min δ₀ (1 / 2)
  have hη0 : 0 < η := lt_min hδ₀ (by norm_num)
  have hη1 : η ≤ 1 / 2 := min_le_right _ _
  refine ⟨η, hη0, by linarith, _, rfl, ?_, ?_, ?_, ?_⟩
  · have hB : IsClosed {u : Fin (c.dim i) → ℝ | ‖u‖ ≤ 1 + η ∧ (u, 0) ∈ cthickening η Y} :=
      (isClosed_le continuous_norm continuous_const).inter
        (isClosed_cthickening.preimage (by fun_prop :
          Continuous fun u : Fin (c.dim i) → ℝ ↦ (u, (0 : Fin (Module.finrank ℝ E - c.dim i) → ℝ))))
    exact (isCompact_closedBall (0 : Fin (c.dim i) → ℝ) (1 + η)).of_isClosed_subset hB
      fun u hu ↦ mem_closedBall_zero_iff.2 hu.1
  · intro u hu
    have hu1 : ‖u‖ = 1 := mem_sphere_zero_iff_norm.1 hu
    refine ⟨by linarith, self_subset_cthickening _ ⟨?_, ?_⟩⟩
    · have h : g (c.chart i (u, 0)) < a := c.mapsTo_sphere i (mk_mem_prod hu (mem_singleton 0))
      exact h.le
    · simp [Prod.norm_def, hu1]
  · rintro ⟨u, v⟩ ⟨hu, hv⟩
    obtain rfl : v = 0 := hv
    exact hδ₀N (cthickening_mono (min_le_left _ _) _ hu.2)
  · intro δ hδ hδη p hp hpB
    obtain ⟨q, ⟨hq1, hq2⟩, hpq⟩ := mem_thickening_iff.1 hp
    rw [mem_singleton_iff] at hq2
    have hpq' : ‖p.1 - q.1‖ < δ ∧ ‖p.2‖ < δ := by
      rw [dist_eq_norm, Prod.norm_def, max_lt_iff] at hpq
      simpa [hq2] using hpq
    have hq1' : ‖q.1‖ ≤ 1 := mem_closedBall_zero_iff.1 hq1
    have hp1 : ‖p.1‖ ≤ 1 + η := by
      have := norm_le_norm_add_norm_sub' p.1 q.1
      linarith [hpq'.1]
    have hpY : p ∉ cthickening (η / 2) Y := by
      intro hpY
      refine hpB ⟨hp1, cthickening_mono (le_of_eq (add_halves η)) _ ?_⟩
      refine cthickening_cthickening_subset (half_pos hη0).le (half_pos hη0).le _
        (mem_cthickening_of_dist_le _ p _ _ hpY ?_)
      rw [dist_eq_norm, Prod.norm_def]
      simpa using hpq'.2.le.trans hδη
    refine ⟨hpY, lt_of_not_ge fun hga ↦ hpY (self_subset_cthickening _ ⟨hga, ?_⟩)⟩
    rw [mem_closedBall_zero_iff, Prod.norm_def, max_le_iff]
    constructor <;> linarith [hpq'.2]

section Readings

/-! ### The formal datum of a cube read in its chart

Forms on `M` are read on the domain of the chart `φ := c.chart i` of cube `i` by the pullback
`φ^*` (`TauCeti.SmoothForm.mpullback`). For two-forms `σ l`, `α l` and one-forms `β l` on `M`,
the formal datum of the cube is the map `f (l, x) := (φ^* (β l)).val x` and its formal primitive
`G (l, x) := formalPrimitive (φ^* (σ l - α l)).val (φ^* (β l)).val x` (`FormalPrimitive.lean`).
The datum is holonomic, `fderiv ℝ (f (l, ·)) x = G (l, x)`, wherever
`σ l = α l + d (β l)` at `c.chart i x`, and `f` and `G` are smooth for smooth families of forms:
these are the hypotheses that the holonomic approximation theorem for families,
`SymplecticGeometry.exists_holonomic_approximation_family`, asks of a formal datum.
-/

open TauCeti

variable [IsManifold I ∞ M] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {L : Type*}
  {σ α : L → SmoothForm I M F 2} {β : L → SmoothForm I M F 1}

/-- **The formal datum of a cube is holonomic where the forms are related.** Let
`σ l = α l + d (β l)` on a set `N` for every parameter `l`, and on all of `M` for the parameters
`l ∈ P₀`. Then the formal primitive of the reading of `σ l - α l` in the chart of cube `i`, with
zeroth-order part the reading of `β l`, is the derivative of that reading at every `(l, x)` with
`c.chart i x ∈ N` or `l ∈ P₀`. -/
theorem fderiv_mpullback_chart_eq_formalPrimitive (c : BandCore I g a₀ a b) (i : c.ι)
    {N : Set M} (hN : ∀ l, ∀ x ∈ N, (σ l).val x = (α l + mextDerivₗ I 1 (β l)).val x)
    {P₀ : Set L} (hP₀ : ∀ l ∈ P₀, ∀ x, (σ l).val x = (α l + mextDerivₗ I 1 (β l)).val x) :
    ∀ p ∈ (univ : Set L) ×ˢ (c.chart i ⁻¹' N) ∪ P₀ ×ˢ univ,
      fderiv ℝ (SmoothForm.mpullback (c.chart i)
          (c.isSmoothEmbedding_chart i).contMDiff (β p.1)).val p.2 =
        formalPrimitive (SmoothForm.mpullback (c.chart i)
          (c.isSmoothEmbedding_chart i).contMDiff (σ p.1 - α p.1)).val
          (SmoothForm.mpullback (c.chart i)
            (c.isSmoothEmbedding_chart i).contMDiff (β p.1)).val p.2 := by
  rintro ⟨l, x⟩ hp
  refine (formalPrimitive_mpullback_eq_fderiv (c.isSmoothEmbedding_chart i).contMDiff ?_).symm
  rcases hp with ⟨-, hx⟩ | ⟨hl, -⟩
  · exact hN l _ hx
  · exact hP₀ l hl _

variable [NormedAddCommGroup L] [NormedSpace ℝ L]

/-- **The reading of a smooth family of forms is smooth.** For a smooth family `β` of `k`-forms on
`M` over a normed space `L`, the value `(mpullback (c.chart i) (β l)).val x` of its reading in the
chart of cube `i` is smooth in `(l, x)`. -/
theorem contDiff_mpullback_chart (c : BandCore I g a₀ a b) (i : c.ι) {k : ℕ}
    {β : L → SmoothForm I M F k} (hβ : IsSmoothFamily 𝓘(ℝ, L) β) :
    ContDiff
      (F := ((Fin (c.dim i) → ℝ) × (Fin (Module.finrank ℝ E - c.dim i) → ℝ)) [⋀^Fin k]→L[ℝ] F) ℝ ∞
      fun p : L × (Fin (c.dim i) → ℝ) × (Fin (Module.finrank ℝ E - c.dim i) → ℝ) ↦
        (SmoothForm.mpullback (c.chart i) (c.isSmoothEmbedding_chart i).contMDiff
          (β p.1)).val p.2 :=
  contMDiff_iff_contDiff.mp (contMDiff_prod_modelWithCornersSelf_iff.mp
    (hβ.mpullback _ (c.isSmoothEmbedding_chart i).contMDiff).contMDiff_val)

/-- **The formal primitive of the reading of smooth families is smooth.** For smooth families
`σ`, `α` of two-forms and `β` of one-forms on `M` over a normed space `L`, the formal primitive of
the reading of `σ l - α l` in the chart of cube `i`, with zeroth-order part the reading of `β l`,
is smooth in `(l, x)`. -/
theorem contDiff_formalPrimitive_mpullback_chart (c : BandCore I g a₀ a b) (i : c.ι)
    (hσ : IsSmoothFamily 𝓘(ℝ, L) σ) (hα : IsSmoothFamily 𝓘(ℝ, L) α)
    (hβ : IsSmoothFamily 𝓘(ℝ, L) β) :
    ContDiff ℝ ∞ fun p : L × (Fin (c.dim i) → ℝ) × (Fin (Module.finrank ℝ E - c.dim i) → ℝ) ↦
      formalPrimitive (SmoothForm.mpullback (c.chart i)
          (c.isSmoothEmbedding_chart i).contMDiff (σ p.1 - α p.1)).val
        (SmoothForm.mpullback (c.chart i)
          (c.isSmoothEmbedding_chart i).contMDiff (β p.1)).val p.2 :=
  contMDiff_iff_contDiff.mp (contMDiff_prod_modelWithCornersSelf_iff.mp
    (contMDiff_formalPrimitive ((hσ.sub hα).mpullback _ (c.isSmoothEmbedding_chart i).contMDiff)
      (hβ.mpullback _ (c.isSmoothEmbedding_chart i).contMDiff)))

end Readings

end BandCore

end SymplecticGeometry

end
