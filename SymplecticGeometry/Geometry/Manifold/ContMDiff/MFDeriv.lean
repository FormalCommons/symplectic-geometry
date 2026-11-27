/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import TauCeti.Geometry.Manifold.ContMDiff.MFDeriv

/-!
# The derivative in the first factor of a jointly smooth function

For a function `g : E → P → F`, with `E` and `F` normed spaces and `P` a manifold, that is
jointly `C^m` near a point of `E × P`, the derivative in the first variable,
`(x, p) ↦ fderiv 𝕜 (g · p) x`, is jointly `C^n` when `n + 1 ≤ m`.

## Main results

* `ContMDiffAt.fderiv_left`: the counterpart, for the first factor, of Tau Ceti's
  `ContMDiffAt.fderiv_right`, which differentiates in the second factor of `P × E`.

The proof swaps the two factors and applies `ContMDiffAt.fderiv_right`, as the proof of Tau
Ceti's `ContMDiffAt.deriv_uncurry` does for a scalar parameter.
-/

public section

open scoped ContDiff Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {H : Type*} [TopologicalSpace H] {J : ModelWithCorners 𝕜 G H}
  {P : Type*} [TopologicalSpace P] [ChartedSpace H P] [IsManifold J 1 P]
  {g : E → P → F} {m n : ℕ∞ω} {z : E × P}

/-- The derivative in the first, vector-space, variable of a function on `E × P` that is jointly
`C^m` at a point is jointly `C^n` there when `n + 1 ≤ m`. No finite-dimensionality or
completeness is required. -/
theorem ContMDiffAt.fderiv_left
    (hg : ContMDiffAt (𝓘(𝕜, E).prod J) 𝓘(𝕜, F) m (Function.uncurry g) z)
    (hnm : n + 1 ≤ m) :
    ContMDiffAt (𝓘(𝕜, E).prod J) 𝓘(𝕜, E →L[𝕜] F) n
      (fun q : E × P ↦ fderiv 𝕜 (fun x ↦ g x q.2) q.1) z := by
  have hswap : ContMDiffAt (J.prod 𝓘(𝕜, E)) 𝓘(𝕜, F) m
      (Function.uncurry fun (p : P) (x : E) ↦ g x p) (z.2, z.1) :=
    hg.comp (z.2, z.1) (contMDiffAt_snd.prodMk contMDiffAt_fst)
  exact (hswap.fderiv_right hnm).comp z (contMDiffAt_snd.prodMk contMDiffAt_fst)

end
