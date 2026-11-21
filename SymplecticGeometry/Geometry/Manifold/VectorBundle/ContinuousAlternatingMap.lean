/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.ContinuousAlternatingMap
public import TauCeti.Analysis.Calculus.ContDiff.ContinuousAlternatingMap

/-!
# Precomposition in bundles of continuous alternating maps

For vector bundles `V₁`, `V₂` and `W` over `M` and a `C^n` section `L` of the bundle of
continuous linear maps `V₂ x →L V₁ x`, the map `α ↦ α ∘ L` from the total space of the bundle of
continuous alternating maps `V₁ x [⋀^ι]→L W x` to that of `V₂ x [⋀^ι]→L W x` is `C^n`
(`contMDiff_compContinuousLinearMap_totalSpace`). It holds for any arity `ι` and any coefficient
bundle `W`, and asks no regularity of the bundles themselves.

The proof reads the map in the fibre coordinates of the trivializations at a point, where it is
Tau Ceti's `ContinuousAlternatingMap.compContinuousLinearMapCLM`, a `C^n` map of the model spaces.
-/

public section

open Bundle
open scoped Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {EB HB M : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  [TopologicalSpace HB] {I : ModelWithCorners 𝕜 EB HB}
  [TopologicalSpace M] [ChartedSpace HB M]
  {F₁ F₂ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  {V₁ V₂ : M → Type*} [∀ x, AddCommGroup (V₁ x)] [∀ x, Module 𝕜 (V₁ x)]
  [∀ x, TopologicalSpace (V₁ x)] [∀ x, IsTopologicalAddGroup (V₁ x)]
  [∀ x, ContinuousSMul 𝕜 (V₁ x)] [TopologicalSpace (TotalSpace F₁ V₁)]
  [FiberBundle F₁ V₁] [VectorBundle 𝕜 F₁ V₁]
  [∀ x, AddCommGroup (V₂ x)] [∀ x, Module 𝕜 (V₂ x)]
  [∀ x, TopologicalSpace (V₂ x)] [TopologicalSpace (TotalSpace F₂ V₂)]
  [FiberBundle F₂ V₂] [VectorBundle 𝕜 F₂ V₂]
  {ι G : Type*} [Fintype ι] [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {W : M → Type*} [∀ x, AddCommGroup (W x)] [∀ x, Module 𝕜 (W x)]
  [∀ x, TopologicalSpace (W x)] [∀ x, IsTopologicalAddGroup (W x)]
  [∀ x, ContinuousSMul 𝕜 (W x)] [TopologicalSpace (TotalSpace G W)]
  [FiberBundle G W] [VectorBundle 𝕜 G W] {n : ℕ∞}

/-- Composing alternating maps on the fibres of `V₁` with a `C^n` family of linear maps
`L x : V₂ x → V₁ x` is a `C^n` map between the total spaces of the bundles of alternating maps
on `V₁` and on `V₂`. -/
theorem contMDiff_compContinuousLinearMap_totalSpace (L : ∀ x, V₂ x →L[𝕜] V₁ x)
    (hL : ContMDiff I (I.prod 𝓘(𝕜, F₂ →L[𝕜] F₁)) n
      (fun x ↦ TotalSpace.mk' (F₂ →L[𝕜] F₁) (E := fun x ↦ V₂ x →L[𝕜] V₁ x) x (L x))) :
    ContMDiff (I.prod 𝓘(𝕜, F₁ [⋀^ι]→L[𝕜] G)) (I.prod 𝓘(𝕜, F₂ [⋀^ι]→L[𝕜] G)) n
      (fun p : TotalSpace (F₁ [⋀^ι]→L[𝕜] G) (fun x ↦ V₁ x [⋀^ι]→L[𝕜] W x) ↦
        TotalSpace.mk' (F₂ [⋀^ι]→L[𝕜] G) (E := fun x ↦ V₂ x [⋀^ι]→L[𝕜] W x) p.proj
          (p.snd.compContinuousLinearMap (L p.proj))) := by
  intro p₀
  rw [contMDiffAt_continuousAlternatingMap_bundle]
  refine ⟨(contMDiff_proj _).contMDiffAt, ?_⟩
  have hp := (contMDiffAt_continuousAlternatingMap_bundle (IB := I) (ι := ι)
    (F₁ := F₁) (F₂ := G) (E₁ := V₁) (E₂ := W) (n := n) id (x₀ := p₀)).1 contMDiffAt_id
  have hl := ((contMDiffAt_hom_bundle _).1 (hL p₀.proj)).2.comp p₀
    (contMDiff_proj _).contMDiffAt
  have hc := ((ContinuousAlternatingMap.contDiff_compContinuousLinearMapCLM (𝕜 := 𝕜)
    (E := F₂) (F := F₁) (G := G) (ι := ι) n).contMDiff.contMDiffAt.comp p₀ hl).clm_apply hp.2
  refine hc.congr_of_eventuallyEq ?_
  have hmem : (trivializationAt F₁ V₁ p₀.proj).baseSet ∈ nhds p₀.proj :=
    (trivializationAt F₁ V₁ p₀.proj).open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt F₁ V₁ p₀.proj)
  filter_upwards [hp.1.continuousAt.preimage_mem_nhds hmem] with p hp
  ext v
  simp only [ContinuousAlternatingMap.inCoordinates, ContinuousLinearMap.inCoordinates,
    Function.comp_apply, ContinuousAlternatingMap.compContinuousLinearMapCLM_apply,
    ContinuousLinearMap.compContinuousAlternatingMap_coe,
    ContinuousAlternatingMap.compContinuousLinearMap_apply]
  congr 2
  ext i
  simp only [Function.comp_apply, ContinuousLinearMap.coe_comp]
  exact (Trivialization.symmL_continuousLinearMapAt _ hp _).symm

end
