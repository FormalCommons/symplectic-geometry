/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Hom
public import TauCeti.Geometry.Manifold.VectorBundle.Trivial
import TauCeti.Geometry.Manifold.Diffeomorph.Basic

/-!
# Fibrewise linear maps as sections of hom bundles

Let `Φ x : V₁ x ≃L V₂ x` be fibrewise equivalences of vector bundles whose map of total spaces is
`C^n`, with `V₁` of finite rank. Then the fibrewise inverses `(Φ x)⁻¹` form a `C^n` section of the
bundle of continuous linear maps `V₂ x →L V₁ x` (`contMDiff_hom_bundle_symm`). The forward maps
`Φ x` form a `C^n` section by Tau Ceti's `TauCeti.contMDiff_hom_bundle_iff`, and inversion
preserves smoothness by Tau Ceti's `ContMDiff.clm_bundle_inverse`. As in
`TauCeti.contMDiff_bundle_symm`, only the source bundle `V₁` needs finite rank.

A map `g` out of the total space of the trivial bundle with fibre `W` over `M` is `C^n` (at a
point, within a set, on a set) exactly when `(x, v) ↦ g ⟨x, v⟩` is, as a map on `M × W`
(`Bundle.Trivial.contMDiff_comp_mk_iff` and its `At`, `WithinAt` and `On` forms). These are
Mathlib's `Diffeomorph.contMDiff_comp_diffeomorph_iff` and its variants, applied to the inverse of
Tau Ceti's `Bundle.Trivial.diffeomorphProd`, with the composite written out.

For a family `Φ x : W →L V x` out of a fixed space `W` of finite dimension, the file also reads
the smoothness of `Φ` as a section of the hom bundle from the trivial bundle with fibre `W` on the
product `M × W` (`contMDiffAt_hom_trivial_iff`, and `contMDiffOn_hom_trivial_iff` over an open
set), through
`TauCeti.contMDiffAt_hom_bundle_iff` and `Bundle.Trivial.contMDiffAt_comp_mk_iff` above.
-/

public section

open Bundle
open scoped Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {EB HB M : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  [TopologicalSpace HB] {I : ModelWithCorners 𝕜 EB HB}
  [TopologicalSpace M] [ChartedSpace HB M]
  {F₁ F₂ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
  [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  {V₁ V₂ : M → Type*} [∀ x, AddCommGroup (V₁ x)] [∀ x, Module 𝕜 (V₁ x)]
  [∀ x, TopologicalSpace (V₁ x)] [∀ x, IsTopologicalAddGroup (V₁ x)]
  [∀ x, ContinuousSMul 𝕜 (V₁ x)] [TopologicalSpace (TotalSpace F₁ V₁)]
  [FiberBundle F₁ V₁] [VectorBundle 𝕜 F₁ V₁]
  [∀ x, AddCommGroup (V₂ x)] [∀ x, Module 𝕜 (V₂ x)]
  [∀ x, TopologicalSpace (V₂ x)] [∀ x, IsTopologicalAddGroup (V₂ x)]
  [∀ x, ContinuousSMul 𝕜 (V₂ x)] [TopologicalSpace (TotalSpace F₂ V₂)]
  [FiberBundle F₂ V₂] [VectorBundle 𝕜 F₂ V₂] {n : WithTop ℕ∞}

namespace SymplecticGeometry

/-- The fibrewise inverses of fibrewise equivalences `Φ x : V₁ x ≃L V₂ x` whose map of total
spaces is `C^n` form a `C^n` section of the bundle of continuous linear maps `V₂ x →L V₁ x`, when
`V₁` has finite rank. -/
theorem contMDiff_hom_bundle_symm (Φ : ∀ x, V₁ x ≃L[𝕜] V₂ x)
    (hΦ : ContMDiff (I.prod 𝓘(𝕜, F₁)) (I.prod 𝓘(𝕜, F₂)) n
      (fun p : TotalSpace F₁ V₁ ↦ TotalSpace.mk' F₂ p.proj (Φ p.proj p.snd))) :
    ContMDiff I (I.prod 𝓘(𝕜, F₂ →L[𝕜] F₁)) n
      (fun x ↦ TotalSpace.mk' (F₂ →L[𝕜] F₁) (E := fun x ↦ V₂ x →L[𝕜] V₁ x) x
        ((Φ x).symm : V₂ x →L[𝕜] V₁ x)) := by
  have := FiniteDimensional.completeSpace 𝕜 F₁
  simpa only [ContinuousLinearMap.inverse_equiv] using
    ((TauCeti.contMDiff_hom_bundle_iff fun x ↦ (Φ x : V₁ x →L[𝕜] V₂ x)).2 hΦ).clm_bundle_inverse
      fun _ ↦ ContinuousLinearMap.isInvertible_equiv

end SymplecticGeometry

section Trivial

omit [FiniteDimensional 𝕜 F₁]

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace 𝕜 W] [FiniteDimensional 𝕜 W]

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 W] in
/-- A map `g` out of the total space of the trivial bundle with fibre `W` is `C^n` within
`(fun p ↦ (p.proj, p.snd)) ⁻¹' s` at `⟨x, v⟩` exactly when `(y, w) ↦ g ⟨y, w⟩`, as a map on
`M × W`, is `C^n` within `s` at `(x, v)`. -/
theorem Bundle.Trivial.contMDiffWithinAt_comp_mk_iff {EN HN N : Type*} [NormedAddCommGroup EN]
    [NormedSpace 𝕜 EN] [TopologicalSpace HN] {J : ModelWithCorners 𝕜 EN HN} [TopologicalSpace N]
    [ChartedSpace HN N] {g : TotalSpace W (Trivial M W) → N} {s : Set (M × W)} {x : M} {v : W} :
    ContMDiffWithinAt (I.prod 𝓘(𝕜, W)) J n (fun p : M × W ↦ g ⟨p.1, p.2⟩) s (x, v) ↔
      ContMDiffWithinAt (I.prod 𝓘(𝕜, W)) J n g
        ((fun p : TotalSpace W (Trivial M W) ↦ (p.proj, p.snd)) ⁻¹' s) ⟨x, v⟩ := by
  simpa only [Function.comp_def, diffeomorphProd_symm_apply, Diffeomorph.symm_symm,
    funext (diffeomorphProd_apply I M W n)] using
    (diffeomorphProd I M W n).symm.contMDiffWithinAt_comp_diffeomorph_iff le_rfl

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 W] in
/-- A map `g` out of the total space of the trivial bundle with fibre `W` is `C^n` at `⟨x, v⟩`
exactly when `(y, w) ↦ g ⟨y, w⟩`, as a map on `M × W`, is `C^n` at `(x, v)`. -/
theorem Bundle.Trivial.contMDiffAt_comp_mk_iff {EN HN N : Type*} [NormedAddCommGroup EN]
    [NormedSpace 𝕜 EN] [TopologicalSpace HN] {J : ModelWithCorners 𝕜 EN HN} [TopologicalSpace N]
    [ChartedSpace HN N] {g : TotalSpace W (Trivial M W) → N} {x : M} {v : W} :
    ContMDiffAt (I.prod 𝓘(𝕜, W)) J n (fun p : M × W ↦ g ⟨p.1, p.2⟩) (x, v) ↔
      ContMDiffAt (I.prod 𝓘(𝕜, W)) J n g ⟨x, v⟩ := by
  simpa only [Function.comp_def, diffeomorphProd_symm_apply] using
    (diffeomorphProd I M W n).symm.contMDiffAt_comp_diffeomorph_iff le_rfl

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 W] in
/-- A map `g` out of the total space of the trivial bundle with fibre `W` is `C^n` on
`(fun p ↦ (p.proj, p.snd)) ⁻¹' s` exactly when `(y, w) ↦ g ⟨y, w⟩`, as a map on `M × W`, is
`C^n` on `s`. -/
theorem Bundle.Trivial.contMDiffOn_comp_mk_iff {EN HN N : Type*} [NormedAddCommGroup EN]
    [NormedSpace 𝕜 EN] [TopologicalSpace HN] {J : ModelWithCorners 𝕜 EN HN} [TopologicalSpace N]
    [ChartedSpace HN N] {g : TotalSpace W (Trivial M W) → N} {s : Set (M × W)} :
    ContMDiffOn (I.prod 𝓘(𝕜, W)) J n (fun p : M × W ↦ g ⟨p.1, p.2⟩) s ↔
      ContMDiffOn (I.prod 𝓘(𝕜, W)) J n g
        ((fun p : TotalSpace W (Trivial M W) ↦ (p.proj, p.snd)) ⁻¹' s) :=
  ⟨fun h p hp ↦ contMDiffWithinAt_comp_mk_iff.1 (h (p.proj, p.snd) hp),
    fun h q hq ↦ contMDiffWithinAt_comp_mk_iff.2 (h ⟨q.1, q.2⟩ hq)⟩

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 W] in
/-- A map `g` out of the total space of the trivial bundle with fibre `W` is `C^n` exactly when
`(y, w) ↦ g ⟨y, w⟩`, as a map on `M × W`, is `C^n`. -/
theorem Bundle.Trivial.contMDiff_comp_mk_iff {EN HN N : Type*} [NormedAddCommGroup EN]
    [NormedSpace 𝕜 EN] [TopologicalSpace HN] {J : ModelWithCorners 𝕜 EN HN} [TopologicalSpace N]
    [ChartedSpace HN N] {g : TotalSpace W (Trivial M W) → N} :
    ContMDiff (I.prod 𝓘(𝕜, W)) J n (fun p : M × W ↦ g ⟨p.1, p.2⟩) ↔
      ContMDiff (I.prod 𝓘(𝕜, W)) J n g := by
  simpa only [Function.comp_def, diffeomorphProd_symm_apply] using
    (diffeomorphProd I M W n).symm.contMDiff_comp_diffeomorph_iff le_rfl

namespace SymplecticGeometry

/-- A family of continuous linear maps `Φ x : W →L V₂ x` from a fixed space `W` of finite
dimension is a `C^n` section at `x` of the bundle of continuous linear maps from the trivial bundle
with fibre `W` to `V₂` exactly when `(y, v) ↦ Φ y v`, as a map from `M × W` to the total space of
`V₂`, is `C^n` at `(x, v)` for every `v`. -/
theorem contMDiffAt_hom_trivial_iff (Φ : ∀ x, W →L[𝕜] V₂ x) (x : M) :
    ContMDiffAt I (I.prod 𝓘(𝕜, W →L[𝕜] F₂)) n
        (fun y ↦ TotalSpace.mk' (W →L[𝕜] F₂) (E := fun y ↦ Trivial M W y →L[𝕜] V₂ y) y
          (Φ y : W →L[𝕜] V₂ y)) x ↔
      ∀ v : W, ContMDiffAt (I.prod 𝓘(𝕜, W)) (I.prod 𝓘(𝕜, F₂)) n
        (fun p : M × W ↦ TotalSpace.mk' F₂ p.1 (Φ p.1 p.2)) (x, v) := by
  rw [TauCeti.contMDiffAt_hom_bundle_iff]
  exact forall_congr' fun v ↦ Trivial.contMDiffAt_comp_mk_iff.symm

/-- A family of continuous linear maps `Φ x : W →L V₂ x` from a fixed space `W` of finite
dimension is a `C^n` section on an open set `U` of the bundle of continuous linear maps from the
trivial bundle with fibre `W` to `V₂` exactly when `(y, v) ↦ Φ y v`, as a map from `M × W` to the
total space of `V₂`, is `C^n` on `U ×ˢ univ`. -/
theorem contMDiffOn_hom_trivial_iff (Φ : ∀ x, W →L[𝕜] V₂ x) {U : Set M} (hU : IsOpen U) :
    ContMDiffOn I (I.prod 𝓘(𝕜, W →L[𝕜] F₂)) n
        (fun y ↦ TotalSpace.mk' (W →L[𝕜] F₂) (E := fun y ↦ Trivial M W y →L[𝕜] V₂ y) y
          (Φ y : W →L[𝕜] V₂ y)) U ↔
      ContMDiffOn (I.prod 𝓘(𝕜, W)) (I.prod 𝓘(𝕜, F₂)) n
        (fun p : M × W ↦ TotalSpace.mk' F₂ p.1 (Φ p.1 p.2)) (U ×ˢ Set.univ) := by
  refine ⟨fun h p hp ↦ ?_, fun h x hx ↦ ?_⟩
  · exact ((contMDiffAt_hom_trivial_iff Φ p.1).1 (h.contMDiffAt (hU.mem_nhds hp.1))
      p.2).contMDiffWithinAt
  · exact ((contMDiffAt_hom_trivial_iff Φ x).2 fun v ↦
      h.contMDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨hx, Set.mem_univ v⟩)).contMDiffWithinAt

end SymplecticGeometry

end Trivial

end
