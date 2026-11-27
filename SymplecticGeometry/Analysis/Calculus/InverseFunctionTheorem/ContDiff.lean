/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Maps with a `C^n` left inverse between spaces of equal finite dimension

* `ContDiffAt.of_local_left_inverse`: let `G` be finite-dimensional over `𝕂 = ℝ` or `ℂ` and `F`
  of the same dimension, let `g : F → G` be differentiable at `a`, and let `f : G → F` be `C^n`
  at `g a`, `n ≠ 0`, with `f (g y) = y` for `y` near `a`. Then `g` is `C^n` at `a`.

By the chain rule `f'(g a) ∘ g'(a)` is the identity, so `f'(g a)` is onto, hence invertible
since the dimensions agree. The inverse function theorem then gives a local homeomorphism `T`
that is `f` near `g a`, and `T.symm` is `C^n` at `a` by Mathlib's
`OpenPartialHomeomorph.contDiffAt_symm`, applied as in the proof of Mathlib's
`ContDiffAt.to_localInverse`. Since `g` is continuous at `a`, `T.symm` undoes `f` at `g y` for
`y` near `a`, so `g y = T.symm (f (g y)) = T.symm y` there. The assumption that `g` be
differentiable at `a` cannot be weakened to continuity: the real cube root is a continuous right
inverse of the smooth map `x ↦ x ^ 3` that is not differentiable at `0`.

The statement is the `C^n` counterpart of Mathlib's `HasStrictFDerivAt.of_local_left_inverse`,
which assumes the derivative of `f` invertible and concludes strict differentiability of `g`.
-/

public section

open Filter Topology

namespace ContDiffAt

variable {𝕂 : Type*} [RCLike 𝕂]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕂 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕂 G] [FiniteDimensional 𝕂 G]

/-- **A map with a `C^n` left inverse is `C^n`, in equal finite dimension.** Let `G` be
finite-dimensional over `𝕂` and `F` of the same dimension, let `g : F → G` be differentiable at
`a`, and let `f : G → F` be `C^n` at `g a`, `n ≠ 0`, with `f (g y) = y` for all `y` near `a`.
Then `g` is `C^n` at `a`. -/
theorem of_local_left_inverse {f : G → F} {g : F → G} {a : F} {n : WithTop ℕ∞}
    (hf : ContDiffAt 𝕂 n f (g a)) (hg : DifferentiableAt 𝕂 g a)
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
  have hinj : Function.Injective f' :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim.symm).2 hsurj
  have : CompleteSpace F := FiniteDimensional.completeSpace 𝕂 F
  have : CompleteSpace G := FiniteDimensional.completeSpace 𝕂 G
  have he : HasFDerivAt f (ContinuousLinearEquiv.ofBijective f' (LinearMap.ker_eq_bot.2 hinj)
      (LinearMap.range_eq_top.2 hsurj) : G →L[𝕂] F) (g a) := by
    rwa [ContinuousLinearEquiv.coe_ofBijective]
  have hs := hf.hasStrictFDerivAt he hn
  set T := hs.toOpenPartialHomeomorph f
  have hT : ∀ᶠ x in 𝓝 (g a), T.symm (f x) = x := by
    simpa [T] using T.eventually_left_inverse hs.mem_toOpenPartialHomeomorph_source
  have hga : T.symm a = g a := by simpa [hfg.self_of_nhds] using hT.self_of_nhds
  have ha : a ∈ T.target := by
    simpa [T, hfg.self_of_nhds] using hs.image_mem_toOpenPartialHomeomorph_target
  have hinv : ContDiffAt 𝕂 n T.symm a :=
    T.contDiffAt_symm ha (by simpa [T, hga] using he) (by simpa [T, hga] using hf)
  refine hinv.congr_of_eventuallyEq ?_
  filter_upwards [hfg, hg.continuousAt.eventually hT] with y hy hy'
  rw [← hy', hy]

end ContDiffAt

end
