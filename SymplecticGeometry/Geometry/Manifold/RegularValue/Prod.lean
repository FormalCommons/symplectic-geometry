/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.RegularValue
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-!
# Regular points of a product of maps

The product `Prod.map f g` of two maps is regular at `(x, y)` when `f` is regular at `x` and `g`
is regular at `y`, since its differential is the product of theirs. So a map
`s ↦ (f i (s i), f j (s j))` on a product of normed spaces is regular where `f i` and `f j` are.

## Main results

* `TauCeti.IsRegularPoint.prodMap`: a product of regular points is a regular point.
* `TauCeti.isRegularPoint_apply_prodMk_apply`: for `i ≠ j`, the map
  `s ↦ (f i (s i), f j (s j))` is regular at `s` when `f i` and `f j` are regular at `s i`
  and `s j`.
-/

public section

open Function
open scoped Manifold

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners 𝕜 F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  {G' : Type*} [TopologicalSpace G'] {J' : ModelWithCorners 𝕜 F' G'}
  {N' : Type*} [TopologicalSpace N'] [ChartedSpace G' N']

/-- If `f` is differentiable and regular at `x` and `g` is differentiable and regular at `y`,
then `Prod.map f g` is regular at `(x, y)`. -/
theorem IsRegularPoint.prodMap {f : M → N} {g : M' → N'} {x : M} {y : M'}
    (hf : IsRegularPoint I J f x) (hg : IsRegularPoint I' J' g y)
    (hfd : MDifferentiableAt I J f x) (hgd : MDifferentiableAt I' J' g y) :
    IsRegularPoint (I.prod I') (J.prod J') (Prod.map f g) (x, y) := by
  rw [isRegularPoint_iff, mfderiv_prodMap (p := (x, y)) hfd hgd]
  exact (isRegularPoint_iff.1 hf).prodMap (isRegularPoint_iff.1 hg)

/-- For `i ≠ j`, the map `s ↦ (f i (s i), f j (s j))` on a product of normed spaces is regular
at `s` when `f i` is differentiable and regular at `s i` and `f j` at `s j`. -/
theorem isRegularPoint_apply_prodMk_apply {ι : Type*} [Fintype ι]
    {V : ι → Type*} [∀ k, NormedAddCommGroup (V k)] [∀ k, NormedSpace 𝕜 (V k)]
    {f : ∀ k, V k → M} {i j : ι} (hij : i ≠ j) {s : ∀ k, V k}
    (hi : IsRegularPoint 𝓘(𝕜, V i) I (f i) (s i)) (hj : IsRegularPoint 𝓘(𝕜, V j) I (f j) (s j))
    (hdi : MDifferentiableAt 𝓘(𝕜, V i) I (f i) (s i))
    (hdj : MDifferentiableAt 𝓘(𝕜, V j) I (f j) (s j)) :
    IsRegularPoint 𝓘(𝕜, ∀ k, V k) (I.prod I) (fun s ↦ (f i (s i), f j (s j))) s := by
  classical
  -- The coordinates `i` and `j`, as a surjective linear map.
  let π : (∀ k, V k) →L[𝕜] V i × V j :=
    (ContinuousLinearMap.proj i).prod (ContinuousLinearMap.proj j)
  have hπ : IsRegularPoint 𝓘(𝕜, ∀ k, V k) (𝓘(𝕜, V i).prod 𝓘(𝕜, V j)) π s := by
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod, isRegularPoint_iff_surjective_fderiv,
      ContinuousLinearMap.fderiv]
    rintro ⟨a, b⟩
    exact ⟨update (update 0 i a) j b, by simp [π, update_of_ne hij]⟩
  have hprod := hi.prodMap hj hdi hdj
  rw [show (s i, s j) = π s by simp [π]] at hprod
  exact hprod.comp hπ

end TauCeti

end
