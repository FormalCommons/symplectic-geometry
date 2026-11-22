/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Smooth

/-!
# Smooth bundle-valued differential forms: evaluation at a point

This file is a part of Tau Ceti's `TauCeti/Geometry/Manifold/DifferentialForm/Smooth.lean`,
copied from Tau Ceti's main branch at commit `464618e8a5496d16e0fe55cd34168d1c98276327`, which
the pinned version of Tau Ceti does not have yet. It contains one declaration,
`TauCeti.SmoothBundleForm.contMDiffAt_eval₂`: evaluating a smooth bundle-valued two-form on two
tangent fields along a map, both `C^n` at a point, is `C^n` at that point. The pinned version
has the global version `TauCeti.SmoothBundleForm.contMDiff_eval₂` only. It is used by
`SymplecticGeometry/Geometry/Symplectic/Manifold/Energy/Surface.lean`.

Changes from Tau Ceti's text:
* the variables are only those the declaration needs;
* in the proof, `simp only [eval₂, SmoothBundleForm.toContMDiffSection_apply]` is replaced by
  `simp only [eval₂_apply, SmoothBundleForm.toContMDiffSection_apply]`, since the body of
  `TauCeti.SmoothBundleForm.eval₂` is not visible outside its file; the pinned lemma
  `TauCeti.SmoothBundleForm.eval₂_apply` states it.
-/

public section

noncomputable section

open Bundle
open scoped ContDiff Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]

namespace SmoothBundleForm

variable {I : ModelWithCorners ℝ E H} [IsManifold I 1 M]

section Evaluation

variable {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]

/-- Evaluating a smooth bundle-valued two-form on two tangent fields along a map, both `C^n` at
`y₀`, is `C^n` at `y₀`. -/
theorem contMDiffAt_eval₂ {n : WithTop ℕ∞} [ENat.LEInfty n]
    (φ : SmoothBundleForm I F V 2) {b : N → M}
    {U W : ∀ y : N, TangentSpace I (b y)} {y₀ : N}
    (hU : ContMDiffAt I' I.tangent n
      (fun y ↦ TotalSpace.mk' E (b y) (U y)) y₀)
    (hW : ContMDiffAt I' I.tangent n
      (fun y ↦ TotalSpace.mk' E (b y) (W y)) y₀) :
    ContMDiffAt I' (I.prod 𝓘(ℝ, F)) n
      (fun y ↦ TotalSpace.mk' F (b y) (φ.eval₂ (b y) (U y) (W y))) y₀ := by
  have hb : ContMDiffAt I' I n b y₀ := (contMDiff_proj (TangentSpace I)).contMDiffAt.comp y₀ hU
  have hφ := ((φ.toContMDiffSection.contMDiff.of_le ENat.LEInfty.out) (b y₀)).comp y₀ hb
  have hφ' : ContMDiffAt I' (I.prod 𝓘(ℝ, E [⋀^Fin 2]→L[ℝ] F)) n
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin 2]→L[ℝ] F)
        (E := fun x ↦ TangentSpace I x [⋀^Fin 2]→L[ℝ] V x) (b y)
        (φ.toContMDiffSection (b y))) y₀ := by
    convert hφ using 1
    funext y
    rfl
  have happly := ContMDiffAt.continuousAlternatingMap_bundle_apply
    (b := b) (v := fun i ↦ ![U, W] i) hφ'
    (fun i ↦ by
      fin_cases i
      · exact hU
      · exact hW)
  convert happly using 1
  funext y
  congr 1
  simp only [eval₂_apply, SmoothBundleForm.toContMDiffSection_apply]
  congr 1
  funext i
  fin_cases i <;> rfl

end Evaluation

end SmoothBundleForm

end TauCeti

end
