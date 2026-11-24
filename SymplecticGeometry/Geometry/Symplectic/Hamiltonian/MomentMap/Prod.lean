/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.MFDeriv.Prod
public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap

/-!
# The differential of a product moment map

For moment maps `μ` of an infinitesimal action on `(M, σ)` and `ν` of one on `(N, τ)`, Tau Ceti
shows that `(x, y) ↦ μ x + ν y` is a moment map of the diagonal action on `M × N`
(`TauCeti.SmoothTwoForm.IsMomentMap.prod`). This file computes its differential:

* `TauCeti.SmoothTwoForm.IsMomentMap.differential_prod_apply`: at `p`, the differential of
  `(x, y) ↦ μ x + ν y` sends `v` to `dμ(v.1) + dν(v.2)`.

The statement takes any moment map of any infinitesimal action on the product with this map as
its moment map, since the differential depends only on the map; `h.prod h'` is one of them.

## References

* [A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, Berlin, 2001][CannasdaSilva2001Lectures], Lecture 22.
-/

public section

open scoped Manifold ContDiff

namespace TauCeti

namespace SmoothTwoForm

namespace IsMomentMap

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {F H' N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H']
  {J : ModelWithCorners ℝ F H'} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
  {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
  {σ : SmoothTwoForm I M} {a : InfinitesimalAction 𝔤 I M} {μ : M → Module.Dual ℝ 𝔤}
  {τ : SmoothTwoForm J N} {b : InfinitesimalAction 𝔤 J N} {ν : N → Module.Dual ℝ 𝔤}

/-- **The differential of a product moment map.** If `μ` is a moment map on `M`, `ν` one on `N`,
and `(x, y) ↦ μ x + ν y` a moment map on `M × N`, then the differential of the latter at `p` sends
`v` to `dμ(v.1) + dν(v.2)`. -/
theorem differential_prod_apply (h : σ.IsMomentMap a μ) (h' : τ.IsMomentMap b ν)
    {c : InfinitesimalAction 𝔤 (I.prod J) (M × N)}
    (hp : (σ.prod τ).IsMomentMap c fun p ↦ μ p.1 + ν p.2) (p : M × N)
    (v : TangentSpace (I.prod J) p) :
    hp.differential p v = h.differential p.1 v.1 + h'.differential p.2 v.2 := by
  ext Z
  rw [LinearMap.add_apply, hp.differential_apply, h.differential_apply p.1 v.1 Z,
    h'.differential_apply p.2 v.2 Z, ← mvfderiv_comp_fst_add_comp_snd_apply
      (h.mdifferentiableAt Z p.1) (h'.mdifferentiableAt Z p.2) v]
  simp only [LinearMap.add_apply, Pi.add_def, Function.comp_def]

end IsMomentMap

end SmoothTwoForm

end TauCeti

end
