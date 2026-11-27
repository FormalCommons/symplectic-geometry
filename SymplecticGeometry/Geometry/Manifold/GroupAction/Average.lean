/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SMul
public import TauCeti.RepresentationTheory.Compact.Haar
public import TauCeti.MeasureTheory.Integral.ContinuousMap
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import SymplecticGeometry.Geometry.Manifold.ContMDiff.ParametricIntegral

/-!
# Averaging a function over the orbits of a compact group

Let a compact topological group `G` act on a type `M`, and let `f : M → F` take values in a real
normed space. Its *orbit average* is `x ↦ ∫ a, f (a • x) ∂haarProb G`, the mean of `f` over the
orbit of `x` for the normalized Haar measure `TauCeti.haarProb G`.

## Main definitions and results

* `SymplecticGeometry.orbitAverage`: the orbit average of a function.
* `SymplecticGeometry.orbitAverage_smul`: the orbit average is `G`-invariant.
* `SymplecticGeometry.orbitAverage_eq_self`: a `G`-invariant function is its own orbit average.
* `SymplecticGeometry.orbitAverage_const`, `SymplecticGeometry.orbitAverage_orbitAverage`: the
  orbit average of a constant, and of an orbit average.
* `SymplecticGeometry.orbitAverage_eq_of_eqOn`,
  `SymplecticGeometry.orbitAverage_eq_zero_of_notMem`: the orbit average keeps the value
  that `f` takes on a `G`-invariant set.
* `SymplecticGeometry.orbitAverage_mem_Icc`: the orbit average of a function with values in
  `[0, 1]` has values in `[0, 1]`.
* `Continuous.orbitAverage`: for a continuous action, the orbit average of a continuous function
  is continuous.
* `ContMDiff.orbitAverage`: for a Lie group acting in a `C^n` way on a boundaryless manifold, the
  orbit average of a `C^n` function is `C^n`. This is differentiation under the integral over the
  compact group (`ContMDiff.parametric_integral_of_boundarylessManifold`).

Tau Ceti averages functions on the group itself (`TauCeti.haarAverage`), Riemannian metrics and
differential forms; this file does the same for functions on a `G`-space.

## References

* G. E. Bredon, *Introduction to Compact Transformation Groups*, Academic Press (1972),
  Chapter VI (averaging over a compact group).
-/

public section

noncomputable section

open Function MeasureTheory Set TauCeti
open scoped ContDiff Manifold

namespace SymplecticGeometry

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G]
  {M : Type*} [MulAction G M] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The orbit average of `f : M → F` under an action of a compact group `G`: the function
`x ↦ ∫ a, f (a • x) ∂haarProb G`, the mean of `f` over the orbit of `x` for the normalized Haar
measure. -/
def orbitAverage (f : M → F) : M → F :=
  fun x ↦ ∫ a, f (a • x) ∂haarProb G

theorem orbitAverage_def (f : M → F) (x : M) :
    orbitAverage G f x = ∫ a, f (a • x) ∂haarProb G := (rfl)

variable {G}

/-- The orbit average is `G`-invariant. -/
@[simp]
theorem orbitAverage_smul (f : M → F) (g : G) (x : M) :
    orbitAverage G f (g • x) = orbitAverage G f x := by
  simp only [orbitAverage_def, smul_smul]
  exact integral_mul_right_eq_self (fun a ↦ f (a • x)) g

/-- If `f` is constant, equal to `c`, on a `G`-invariant set `s`, then so is its orbit
average. -/
theorem orbitAverage_eq_of_eqOn [CompleteSpace F] {f : M → F} {s : Set M} {c : F}
    (hs : ∀ (g : G), ∀ x ∈ s, g • x ∈ s) (hf : EqOn f (fun _ ↦ c) s) :
    EqOn (orbitAverage G f) (fun _ ↦ c) s := fun x hx ↦ by
  simp [orbitAverage_def, hf (hs _ x hx)]

/-- A `G`-invariant function is its own orbit average. -/
theorem orbitAverage_eq_self [CompleteSpace F] {f : M → F}
    (hf : ∀ (g : G) (x : M), f (g • x) = f x) :
    orbitAverage G f = f :=
  funext fun x ↦ by simp [orbitAverage_def, hf]

/-- The orbit average of a constant function is that constant. -/
@[simp]
theorem orbitAverage_const [CompleteSpace F] (c : F) :
    orbitAverage G (fun _ : M ↦ c) = fun _ ↦ c :=
  orbitAverage_eq_self fun _ _ ↦ rfl

/-- Averaging over the orbits twice is the same as averaging once. -/
@[simp]
theorem orbitAverage_orbitAverage [CompleteSpace F] (f : M → F) :
    orbitAverage G (orbitAverage G f) = orbitAverage G f :=
  orbitAverage_eq_self (orbitAverage_smul f)

/-- If `f` vanishes outside a `G`-invariant set `s`, then so does its orbit average. -/
theorem orbitAverage_eq_zero_of_notMem {f : M → F} {s : Set M}
    (hs : ∀ (g : G), ∀ x ∈ s, g • x ∈ s) (hf : ∀ x ∉ s, f x = 0) {x : M} (hx : x ∉ s) :
    orbitAverage G f x = 0 := by
  have (a : G) : f (a • x) = 0 := hf _ fun h ↦ hx (by simpa using hs a⁻¹ _ h)
  simp [orbitAverage_def, this]

/-- The orbit average of a function with values in `[0, 1]` has values in `[0, 1]`. -/
theorem orbitAverage_mem_Icc {f : M → ℝ} (hf : ∀ x, f x ∈ Icc 0 1) (x : M) :
    orbitAverage G f x ∈ Icc 0 1 := by
  rw [orbitAverage_def]
  refine ⟨integral_nonneg fun a ↦ (hf _).1, ?_⟩
  calc ∫ a, f (a • x) ∂haarProb G ≤ ∫ _a, (1 : ℝ) ∂haarProb G :=
        integral_mono_of_nonneg (.of_forall fun a ↦ (hf _).1) (integrable_const 1)
          (.of_forall fun a ↦ (hf _).2)
    _ = 1 := by simp

/-- For a continuous action of a compact group, the orbit average of a continuous function is
continuous. -/
theorem _root_.Continuous.orbitAverage [TopologicalSpace M] [ContinuousSMul G M] {f : M → F}
    (hf : Continuous f) : Continuous (orbitAverage G f) := by
  -- `x ↦ (a ↦ f (a • x))` is continuous into `C(G, F)` with the uniform norm, and integration
  -- over the compact group is continuous for that norm.
  let φ : C(M × G, F) := ⟨fun p ↦ f (p.2 • p.1), hf.comp (continuous_smul.comp continuous_swap)⟩
  exact continuous_integral_continuousMap.comp φ.curry.continuous

end SymplecticGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] (J : ModelWithCorners ℝ E' H')
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [ChartedSpace H' G] [MulAction G M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ∞}
  [IsManifold I n M] [IsManifold J n G] [ContMDiffSMul J I (n : ℕ∞ω) G M]

include J in
/-- **Smoothness of the orbit average.** If a compact Lie group `G` acts on a boundaryless
manifold `M` by a `C^n` map `G × M → M`, then the orbit average of a `C^n` function `f : M → F`
is `C^n`. -/
theorem ContMDiff.orbitAverage [BoundarylessManifold I M] {f : M → F}
    (hf : ContMDiff I 𝓘(ℝ, F) n f) :
    ContMDiff I 𝓘(ℝ, F) n (SymplecticGeometry.orbitAverage G f) := by
  rw [show SymplecticGeometry.orbitAverage G f = _ from
    funext (SymplecticGeometry.orbitAverage_def G f)]
  exact ContMDiff.parametric_integral_of_boundarylessManifold (J := J)
    (hf.comp ((contMDiff_smul (I := J) (I' := I)).comp (contMDiff_snd.prodMk contMDiff_fst)))

end
