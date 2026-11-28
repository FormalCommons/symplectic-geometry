/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import TauCeti.Topology.Algebra.Module.FiniteDimension

/-!
# Maps with a `C^n` left inverse

* `ContDiffAt.of_local_left_inverse`: over `𝕂 = ℝ` or `ℂ`, with `G` complete, let `f : G → F`
  be `C^n` at `g a`, `n ≠ 0`, with derivative there a continuous linear equivalence, let
  `g : F → G` be continuous at `a`, and let `f (g y) = y` for `y` near `a`. Then `g` is `C^n`
  at `a`. This is the `C^n` counterpart of Mathlib's `HasStrictFDerivAt.of_local_left_inverse`.
* `ContDiffAt.of_local_left_inverse_of_finrank_eq`: the same conclusion when `G` is
  finite-dimensional, `F` has the same dimension, and `g` is differentiable at `a`; the
  derivative of `f` is then invertible, and need not be assumed so.

For the first, Mathlib's `ContDiffAt.to_localInverse` makes the local inverse of `f` at `g a`
a `C^n` map at `f (g a) = a`, and `Filter.eventuallyEq_of_left_inv_of_right_inv` shows that it
agrees with `g` near `a`. For the second, the chain rule shows that `f'(g a) ∘ g'(a)` is the
identity, so `f'(g a)` is onto, hence invertible in equal finite dimension by Tau Ceti's
`ContinuousLinearMap.isInvertible_iff_surjective_of_finrank_eq`.

In the second statement, differentiability of `g` at `a` cannot be weakened to continuity: the
real cube root is a continuous right inverse of the smooth map `x ↦ x ^ 3` that is not
differentiable at `0`.
-/

public section

open Filter Topology

namespace ContDiffAt

variable {𝕂 : Type*} [RCLike 𝕂]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕂 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕂 G]

/-- **A map with a `C^n` left inverse is `C^n`.** Let `G` be complete, let `f : G → F` be `C^n`
at `g a`, `n ≠ 0`, with derivative there a continuous linear equivalence `f'`, let `g : F → G`
be continuous at `a`, and let `f (g y) = y` for all `y` near `a`. Then `g` is `C^n` at `a`.
This is the `C^n` counterpart of `HasStrictFDerivAt.of_local_left_inverse`. -/
theorem of_local_left_inverse [CompleteSpace G] {f : G → F} {g : F → G} {a : F}
    {n : WithTop ℕ∞} {f' : G ≃L[𝕂] F} (hf : ContDiffAt 𝕂 n f (g a))
    (hf' : HasFDerivAt f (f' : G →L[𝕂] F) (g a)) (hg : ContinuousAt g a)
    (hfg : ∀ᶠ y in 𝓝 a, f (g y) = y) (hn : n ≠ 0) : ContDiffAt 𝕂 n g a := by
  have h := hf.to_localInverse hf' hn
  rw [hfg.self_of_nhds] at h
  exact h.congr_of_eventuallyEq (eventuallyEq_of_left_inv_of_right_inv
    (hf.hasStrictFDerivAt hf' hn).eventually_left_inverse hfg hg).symm

/-- **A map with a `C^n` left inverse is `C^n`, in equal finite dimension.** Let `G` be
finite-dimensional over `𝕂` and `F` of the same dimension, let `g : F → G` be differentiable at
`a`, and let `f : G → F` be `C^n` at `g a`, `n ≠ 0`, with `f (g y) = y` for all `y` near `a`.
Then `g` is `C^n` at `a`. -/
theorem of_local_left_inverse_of_finrank_eq [FiniteDimensional 𝕂 G] {f : G → F} {g : F → G}
    {a : F} {n : WithTop ℕ∞} (hf : ContDiffAt 𝕂 n f (g a)) (hg : DifferentiableAt 𝕂 g a)
    (hfg : ∀ᶠ y in 𝓝 a, f (g y) = y) (hn : n ≠ 0)
    (hdim : Module.finrank 𝕂 F = Module.finrank 𝕂 G) :
    ContDiffAt 𝕂 n g a := by
  set f' := fderiv 𝕂 f (g a)
  have hf' : HasFDerivAt f f' (g a) := (hf.differentiableAt hn).hasFDerivAt
  have hcomp : f'.comp (fderiv 𝕂 g a) = ContinuousLinearMap.id 𝕂 F :=
    (hf'.comp a hg.hasFDerivAt).unique ((hasFDerivAt_id a).congr_of_eventuallyEq hfg)
  have hsurj : Function.Surjective f' := fun y ↦
    ⟨fderiv 𝕂 g a y, by simpa using congrArg (· y) hcomp⟩
  have : FiniteDimensional 𝕂 F := Module.Finite.of_surjective (f' : G →ₗ[𝕂] F) hsurj
  have : CompleteSpace G := FiniteDimensional.completeSpace 𝕂 G
  obtain ⟨L, hL⟩ := (f'.isInvertible_iff_surjective_of_finrank_eq hdim.symm).2 hsurj
  rw [← hL] at hf'
  exact of_local_left_inverse hf hf' hg.continuousAt hfg hn

end ContDiffAt

end
