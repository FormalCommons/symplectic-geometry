/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.FiniteBundleAtlas.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Section.FrameCover
import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Evaluation
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

On the way it relates the chart readings `A.coord i` to the frame coordinates
`Bundle.Trivialization.frameCoordinates` of the bundle chart `A.triv i`, read through the charts
at `A.center i`: `TauCeti.FiniteBundleAtlas.coord_eqOn_frameCoordinates`.

The proof reads the sections in the frame of the bundle chart `A.triv i` over its base set, whose
frame coordinates depend continuously on the section by Tau Ceti's
`ContMDiffSection.continuous_frameCoordinates_of_cover`, and then uses the uniform convergence of
coordinate derivatives on compact subsets of a chart target,
`ContMDiffMap.tendstoUniformlyOn_iteratedFDerivWithin_extChartAt`, on the compact chart image of
the closure of the chart domain. No `CompactSpace M` instance is assumed, since a finite bundle
atlas already makes `M` compact (`TauCeti.FiniteBundleAtlas.compactSpace`).

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
  have hφ : IsOpen φ.target := isOpen_extChartAt_target x
  -- On `φ.target`, the frame coordinates read through `φ` are the chart readings of `A`.
  have hread (t : Cₛ^n⟮𝓘(𝕜, E); F, V⟯) {w : E} (hw : w ∈ φ.target) :
      iteratedFDerivWithin 𝕜 j (extChartAt 𝓘(𝕜, F) (0 : F) ∘
        (A.triv i).frameCoordinates (I := 𝓘(𝕜, E)) (n := n) (subset_rfl : (U' : Set M) ⊆ _) t ∘
          φ.symm) φ.target w = iteratedFDeriv 𝕜 j (A.coord i t) w := by
    rw [← iteratedFDerivWithin_of_isOpen j hφ hw]
    exact iteratedFDerivWithin_congr (A.coord_eqOn_frameCoordinates i subset_rfl x.property t) hw j
  let f₀ := (A.triv i).frameCoordinates (I := 𝓘(𝕜, E)) (n := n)
    (subset_rfl : (U' : Set M) ⊆ _) s₀
  have hu := ContMDiffMap.tendstoUniformlyOn_iteratedFDerivWithin_extChartAt (J := 𝓘(𝕜, F))
    (y := (0 : F)) (f₀ := f₀) hCc hCt (fun _ _ ↦ by simp) hj
  have hsub := A.image_subset_chart_image_closure_dom i
  have hlim := (hu.comp_tendsto hT).mono hsub
  exact (hlim.congr (Eventually.of_forall fun p w hw ↦ hread (s p) (hCt (hsub hw)))).congr_right
    fun w hw ↦ hread s₀ (hCt (hsub hw))

end FiniteBundleAtlas

end TauCeti

end
