/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import TauCeti.Analysis.Calculus.ContDiffZPow

/-!
# Integral powers of a `C^n` function on a manifold

Mathlib has `ContMDiffWithinAt.pow` for natural powers and `ContMDiffWithinAt.inv₀` for the inverse
of a nonvanishing function, and Tau Ceti has `ContDiffAt.zpow` for integral powers on normed
spaces. This file gives the manifold version of the latter: for a function `f` from a manifold to
a normed division algebra `𝕜'` over `𝕜`, the function `fun x ↦ f x ^ m`, `m : ℤ`, is `C^n` where
`f` is, at points where `f` does not vanish or for `0 ≤ m`.

## Main results

* `ContMDiffWithinAt.zpow`, `ContMDiffAt.zpow`, `ContMDiffOn.zpow`, `ContMDiff.zpow`, with the
  side conditions of Tau Ceti's `ContDiffWithinAt.zpow` family, from which each is obtained by
  composition.
-/

public section

open scoped Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {𝕜' : Type*} [NormedDivisionRing 𝕜'] [NormedAlgebra 𝕜 𝕜']
  {f : M → 𝕜'} {s : Set M} {x : M} {m : ℤ} {n : WithTop ℕ∞}

/-- An integral power of a `C^n` function is `C^n` within a set at a point where the function does
not vanish, and also, whatever the value there, for a nonnegative exponent. -/
theorem ContMDiffWithinAt.zpow (hf : ContMDiffWithinAt I 𝓘(𝕜, 𝕜') n f s x)
    (h : f x ≠ 0 ∨ 0 ≤ m) : ContMDiffWithinAt I 𝓘(𝕜, 𝕜') n (fun y ↦ f y ^ m) s x :=
  (contDiffAt_id.zpow h).contMDiffAt.comp_contMDiffWithinAt x hf

/-- An integral power of a `C^n` function is `C^n` at a point where the function does not vanish,
and also, whatever the value there, for a nonnegative exponent. -/
theorem ContMDiffAt.zpow (hf : ContMDiffAt I 𝓘(𝕜, 𝕜') n f x) (h : f x ≠ 0 ∨ 0 ≤ m) :
    ContMDiffAt I 𝓘(𝕜, 𝕜') n (fun y ↦ f y ^ m) x :=
  ContMDiffWithinAt.zpow hf h

/-- An integral power of a `C^n` function is `C^n` on a set where the function does not vanish,
and also, whatever its values there, for a nonnegative exponent. -/
theorem ContMDiffOn.zpow (hf : ContMDiffOn I 𝓘(𝕜, 𝕜') n f s)
    (h : (∀ y ∈ s, f y ≠ 0) ∨ 0 ≤ m) : ContMDiffOn I 𝓘(𝕜, 𝕜') n (fun y ↦ f y ^ m) s :=
  fun y hy ↦ (hf y hy).zpow (h.imp_left fun h ↦ h y hy)

/-- An integral power of a `C^n` function is `C^n` if the function does not vanish, and also,
whatever its values, for a nonnegative exponent. -/
theorem ContMDiff.zpow (hf : ContMDiff I 𝓘(𝕜, 𝕜') n f) (h : (∀ y, f y ≠ 0) ∨ 0 ≤ m) :
    ContMDiff I 𝓘(𝕜, 𝕜') n (fun y ↦ f y ^ m) :=
  fun y ↦ (hf y).zpow (h.imp_left fun h ↦ h y)

end
