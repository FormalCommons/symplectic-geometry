/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.CriticalPoints
public import TauCeti.Geometry.Manifold.RegularValue
import SymplecticGeometry.Geometry.Manifold.Diffeomorph.RestrictScalars
import TauCeti.Geometry.Manifold.Morse.ScalarComposition
import TauCeti.Geometry.Manifold.RegularValue.Open

/-!
# The critical set of a map between manifolds

The critical set `criticalSet I I' f` of a map `f : M → N` between manifolds over a nontrivially
normed field is the set of points at which `f` is not a regular point in the sense of Tau Ceti's
`TauCeti.IsRegularPoint`, that is, at which the manifold derivative of `f` is not surjective.
Tau Ceti's own `criticalPoints` is the corresponding notion for real-valued functions only, and
`SymplecticGeometry.criticalSet_eq_criticalPoints` identifies the two for maps into `ℝ`.

## Main results

* `SymplecticGeometry.mem_criticalSet_iff` and `SymplecticGeometry.compl_criticalSet`: the
  critical set is the complement of the regular points.
* `TauCeti.IsRegularValue.notMem_criticalSet` and
  `TauCeti.IsRegularValue.apply_ne_of_mem_criticalSet`: no point of the critical set lies over a
  regular value, one direction of Tau Ceti's `TauCeti.isRegularValue_iff_notMem_image`.
* `SymplecticGeometry.isClosed_criticalSet`: the critical set of a `C¹` map into a
  finite-dimensional manifold is closed, by Tau Ceti's `TauCeti.isOpen_setOf_isRegularPoint`.
* `Diffeomorph.comp_isRegularPoint_iff`, `Diffeomorph.comp_isRegularValue_iff` and
  `Diffeomorph.criticalSet_comp`: postcomposing with a diffeomorphism changes neither the regular
  points, nor the regular values (moved by the diffeomorphism), nor the critical set. This is the
  counterpart, for the target, of Tau Ceti's `Diffeomorph.isRegularPoint_comp_iff`.
* `Diffeomorph.comp_isRegularPoint_iff_restrictScalars'`,
  `Diffeomorph.comp_isRegularValue_iff_restrictScalars'` and
  `Diffeomorph.criticalSet_comp_restrictScalars'`: the same for a diffeomorphism over a larger
  field, such as a biholomorphism, seen over the smaller field by `Diffeomorph.restrictScalars'`.
* `SymplecticGeometry.criticalSet_eq_criticalPoints`: for a real-valued function the critical
  set is Tau Ceti's `TauCeti.criticalPoints`, by
  `TauCeti.isRegularPoint_iff_notMem_criticalPoints`.
* `TauCeti.IsRegularValue.scalar_comp`: postcomposing a real-valued function with an injective
  `φ : ℝ → ℝ` whose derivative does not vanish at its values moves its regular values by `φ`,
  since it keeps its critical points (`TauCeti.mem_criticalPoints_scalar_comp_iff`).
-/

public section

open TauCeti
open scoped Manifold

namespace SymplecticGeometry

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] (I' : ModelWithCorners 𝕜 E' H')
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]

/-- The critical set of a map `f : M → N` between manifolds: the points at which the manifold
derivative of `f` is not surjective, the complement of the regular points of Tau Ceti's
`IsRegularPoint`. -/
def criticalSet (f : M → N) : Set M :=
  {x | ¬ IsRegularPoint I I' f x}

theorem criticalSet_def (f : M → N) : criticalSet I I' f = {x | ¬ IsRegularPoint I I' f x} :=
  (rfl)

variable {I I'}

@[simp]
theorem mem_criticalSet_iff {f : M → N} {x : M} :
    x ∈ criticalSet I I' f ↔ ¬ IsRegularPoint I I' f x := by
  rw [criticalSet_def, Set.mem_ofPred_eq]

/-- The complement of the critical set is the set of regular points. -/
theorem compl_criticalSet (f : M → N) :
    (criticalSet I I' f)ᶜ = {x | IsRegularPoint I I' f x} := by
  ext x
  simp

/-- A point of the fibre of `f` over a regular value is not in the critical set of `f`. -/
theorem _root_.TauCeti.IsRegularValue.notMem_criticalSet {f : M → N} {x : M} {y : N}
    (hy : IsRegularValue I I' f y) (hx : f x = y) : x ∉ criticalSet I I' f :=
  fun hc ↦ mem_criticalSet_iff.1 hc (hy.isRegularPoint hx)

/-- A critical point of `f` is never mapped to a regular value of `f`. -/
theorem _root_.TauCeti.IsRegularValue.apply_ne_of_mem_criticalSet {f : M → N} {x : M} {y : N}
    (hy : IsRegularValue I I' f y) (hx : x ∈ criticalSet I I' f) : f x ≠ y :=
  fun h ↦ hy.notMem_criticalSet h hx

/-- The critical set of a `C¹` map into a finite-dimensional manifold is closed. -/
theorem isClosed_criticalSet [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E'] [IsManifold I 1 M]
    [IsManifold I' 1 N] {f : M → N} {n : WithTop ℕ∞} (hf : ContMDiff I I' n f) (hn : 1 ≤ n) :
    IsClosed (criticalSet I I' f) := by
  rw [← isOpen_compl_iff, compl_criticalSet]
  exact isOpen_setOf_isRegularPoint hf hn

/-- Postcomposing a map with a `C^n` diffeomorphism (`n ≠ 0`) preserves regular points. -/
theorem _root_.Diffeomorph.comp_isRegularPoint_iff {n : WithTop ℕ∞}
    {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] {H'' : Type*} [TopologicalSpace H'']
    {I'' : ModelWithCorners 𝕜 E'' H''} {N' : Type*} [TopologicalSpace N'] [ChartedSpace H'' N']
    (Φ : N ≃ₘ^n⟮I', I''⟯ N') (hn : n ≠ 0) {f : M → N} {x : M} :
    IsRegularPoint I I'' (Φ ∘ f) x ↔ IsRegularPoint I I' f x := by
  refine ⟨fun h ↦ ?_, fun h ↦ ((Φ.isLocalDiffeomorph _).isRegularPoint hn).comp h⟩
  have := ((Φ.symm.isLocalDiffeomorph _).isRegularPoint hn).comp h
  rwa [← Function.comp_assoc, ← Diffeomorph.coe_trans, Diffeomorph.self_trans_symm,
    Diffeomorph.coe_refl, Function.id_comp] at this

/-- Postcomposing a map with a `C^n` diffeomorphism `Φ` (`n ≠ 0`) preserves regular values:
`Φ y` is a regular value of `Φ ∘ f` exactly when `y` is one of `f`. -/
theorem _root_.Diffeomorph.comp_isRegularValue_iff {n : WithTop ℕ∞}
    {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] {H'' : Type*} [TopologicalSpace H'']
    {I'' : ModelWithCorners 𝕜 E'' H''} {N' : Type*} [TopologicalSpace N'] [ChartedSpace H'' N']
    (Φ : N ≃ₘ^n⟮I', I''⟯ N') (hn : n ≠ 0) {f : M → N} {y : N} :
    IsRegularValue I I'' (Φ ∘ f) (Φ y) ↔ IsRegularValue I I' f y := by
  simp only [isRegularValue_iff, Function.comp_apply, EmbeddingLike.apply_eq_iff_eq,
    Φ.comp_isRegularPoint_iff hn]

/-- Postcomposing a map with a `C^n` diffeomorphism (`n ≠ 0`) does not change its critical set. -/
theorem _root_.Diffeomorph.criticalSet_comp {n : WithTop ℕ∞}
    {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] {H'' : Type*} [TopologicalSpace H'']
    {I'' : ModelWithCorners 𝕜 E'' H''} {N' : Type*} [TopologicalSpace N'] [ChartedSpace H'' N']
    (Φ : N ≃ₘ^n⟮I', I''⟯ N') (hn : n ≠ 0) (f : M → N) :
    criticalSet I I'' (Φ ∘ f) = criticalSet I I' f := by
  ext x
  simp [Φ.comp_isRegularPoint_iff hn]

section RestrictScalars

variable {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace 𝕜' F] [IsScalarTower 𝕜 𝕜' F]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F'] [NormedSpace 𝕜' F']
  [IsScalarTower 𝕜 𝕜' F'] {P : Type*} [TopologicalSpace P] [ChartedSpace F P]
  {P' : Type*} [TopologicalSpace P'] [ChartedSpace F' P'] {n : WithTop ℕ∞}

/-- Postcomposing a map with a `C^n` diffeomorphism over a larger field `𝕜'` (`n ≠ 0`), such as a
biholomorphism, does not change its regular points over `𝕜`. -/
theorem _root_.Diffeomorph.comp_isRegularPoint_iff_restrictScalars'
    (Ψ : P ≃ₘ^n⟮𝓘(𝕜', F), 𝓘(𝕜', F')⟯ P') (hn : n ≠ 0) {f : M → P} {x : M} :
    IsRegularPoint I 𝓘(𝕜, F') (Ψ ∘ f) x ↔ IsRegularPoint I 𝓘(𝕜, F) f x := by
  rw [← Diffeomorph.coe_restrictScalars' 𝕜 Ψ, Diffeomorph.comp_isRegularPoint_iff _ hn]

/-- Postcomposing a map with a `C^n` diffeomorphism `Ψ` over a larger field `𝕜'` (`n ≠ 0`), such
as a biholomorphism, moves its regular values over `𝕜` by `Ψ`: `Ψ y` is a regular value of `Ψ ∘ f`
exactly when `y` is one of `f`. -/
theorem _root_.Diffeomorph.comp_isRegularValue_iff_restrictScalars'
    (Ψ : P ≃ₘ^n⟮𝓘(𝕜', F), 𝓘(𝕜', F')⟯ P') (hn : n ≠ 0) {f : M → P} {y : P} :
    IsRegularValue I 𝓘(𝕜, F') (Ψ ∘ f) (Ψ y) ↔ IsRegularValue I 𝓘(𝕜, F) f y := by
  rw [← Diffeomorph.coe_restrictScalars' 𝕜 Ψ, Diffeomorph.comp_isRegularValue_iff _ hn]

/-- Postcomposing a map with a `C^n` diffeomorphism over a larger field `𝕜'` (`n ≠ 0`), such as a
biholomorphism, does not change its critical set over `𝕜`. -/
theorem _root_.Diffeomorph.criticalSet_comp_restrictScalars'
    (Ψ : P ≃ₘ^n⟮𝓘(𝕜', F), 𝓘(𝕜', F')⟯ P') (hn : n ≠ 0) (f : M → P) :
    criticalSet I 𝓘(𝕜, F') (Ψ ∘ f) = criticalSet I 𝓘(𝕜, F) f := by
  rw [← Diffeomorph.coe_restrictScalars' 𝕜 Ψ, Diffeomorph.criticalSet_comp _ hn]

end RestrictScalars

/-- For a real-valued function, the critical set is Tau Ceti's `criticalPoints`, the set of points
where the manifold derivative vanishes. -/
theorem criticalSet_eq_criticalPoints {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] (f : M → ℝ) :
    criticalSet I 𝓘(ℝ) f = criticalPoints I f := by
  ext x
  rw [mem_criticalSet_iff, isRegularPoint_iff_notMem_criticalPoints, not_not]

/-- Post-composing with an injective `φ : ℝ → ℝ` whose derivative does not vanish at the values of
a differentiable `f` keeps regular values: if `c` is a regular value of `f`, then `φ c` is one of
`φ ∘ f`. -/
theorem _root_.TauCeti.IsRegularValue.scalar_comp {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*}
    [TopologicalSpace M] [ChartedSpace H M] {f : M → ℝ} {φ : ℝ → ℝ}
    (hf : MDifferentiable I 𝓘(ℝ) f) (hinj : Function.Injective φ) (hφ : ∀ x, deriv φ (f x) ≠ 0)
    {c : ℝ} (hc : IsRegularValue I 𝓘(ℝ) f c) : IsRegularValue I 𝓘(ℝ) (φ ∘ f) (φ c) := by
  rw [isRegularValue_iff_notMem_image_criticalPoints] at hc ⊢
  rintro ⟨x, hx, hxc⟩
  rw [mem_criticalPoints_scalar_comp_iff (hf x) (hφ x)] at hx
  exact hc ⟨x, hx, hinj hxc⟩

end SymplecticGeometry

end
