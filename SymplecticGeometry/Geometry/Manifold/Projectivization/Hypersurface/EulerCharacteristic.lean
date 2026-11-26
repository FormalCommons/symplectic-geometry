/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Projectivization.Hypersurface.Degree
public import TauCeti.Geometry.Manifold.Complex.FiniteCWType

import SymplecticGeometry.Geometry.Manifold.Complex.EulerCharacteristic
import SymplecticGeometry.Geometry.Manifold.Projectivization.Hypersurface.Line

/-!
# The Euler characteristic of a smooth projective hypersurface

Let `X ⊆ ℂℙⁿ⁺¹` be a smooth projective hypersurface of degree `d`, with inclusion `ι`, and let `h`
be the hyperplane class of `ℂℙⁿ⁺¹`. This file computes the Euler characteristic of `X`.

As a compact complex manifold, `X` has finite CW type (Tau Ceti's
`TauCeti.ComplexManifold.finiteCWType`), so its Euler characteristic `TauCeti.eulerChar X` is
defined. For `n ≠ 0` it is the top Chern number `⟨c_n(TX), [X]⟩`, as for every compact complex
manifold (`SymplecticGeometry.evalFundamentalClass_chernClass_eq_eulerChar`). The top Chern class
is `(∑_{j ≤ n} (n + 2).choose (n - j) (-d) ^ j) (ι^* h) ^ n`
(`SymplecticGeometry.SmoothProjectiveHypersurface.chernClass_tangentSpace`), and
`⟨(ι^* h) ^ n, [X]⟩ = d`
(`SymplecticGeometry.SmoothProjectiveHypersurface.evalFundamentalClass_hyperplaneClass_pow`), so
`χ(X) = d ∑_{j ≤ n} (n + 2).choose (n - j) (-d) ^ j`. For `n = 0` this is `χ(X) = d`, the number
of points of `X` (`SymplecticGeometry.SmoothProjectiveHypersurface.eulerChar_eq_of_dim_zero`).

## Main results

The following are in the namespace `SymplecticGeometry.SmoothProjectiveHypersurface`.

* `instFiniteCWType`: a smooth projective hypersurface has finite CW type.
* `eulerChar_eq_evalFundamentalClass_chernClass`: `χ(X) = ⟨c_n(TX), [X]⟩` for `n ≠ 0`, written
  for a hypersurface of dimension `n + 1`, the fundamental class being that of the complex
  orientation.
* `eulerChar_eq`: `χ(X) = d ∑_{j ≤ n} (n + 2).choose (n - j) (-d) ^ j`, for every `n`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Examples 4.4.3 and 4.4.4 and Exercise 4.4.6.
* [P. Griffiths and J. Harris, *Principles of Algebraic Geometry*][GriffithsHarris1978],
  Chapter 1, §1.
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §11 and §14.
-/

public section

open Module SymplecticGeometry.Bundle TauCeti
open scoped Manifold ContDiff TauCeti.ComplexManifold

namespace SymplecticGeometry

namespace SmoothProjectiveHypersurface

variable {n d : ℕ}

/-- A smooth projective hypersurface has finite CW type, as every compact complex manifold
does. -/
instance instFiniteCWType (X : SmoothProjectiveHypersurface n d) : FiniteCWType X :=
  ComplexManifold.finiteCWType X 𝓘(ℂ, Fin n → ℂ) (n := ω) (by simp)

/-- **The Euler characteristic of a hypersurface as a Chern number.** For a smooth hypersurface
`X ⊆ ℂℙⁿ⁺²` of dimension `n + 1`, oriented by its complex structure
(`complexManifoldHomologicalOrientation`), the Euler characteristic of `X` is its top Chern class
`c_{n+1}(TX)` evaluated on the fundamental class of `X`.

Milestone: *Chern classes of projective hypersurfaces*. -/
theorem eulerChar_eq_evalFundamentalClass_chernClass (X : SmoothProjectiveHypersurface (n + 1) d) :
    eulerChar X =
      complexManifoldEvalFundamentalClass (Fin (n + 1) → ℂ) X (Module.finrank_fin_fun ℂ)
        (chernClass (Fin (n + 1) → ℂ)
          (TangentSpace 𝓘(ℂ, Fin (n + 1) → ℂ) : X → Type) (n + 1)) :=
  (evalFundamentalClass_chernClass_eq_eulerChar (Module.finrank_fin_fun ℂ)).symm

/-- **The Euler characteristic of a hypersurface.** A smooth hypersurface `X ⊆ ℂℙⁿ⁺¹` of degree
`d` has Euler characteristic `d ∑_{j ≤ n} (n + 2).choose (n - j) (-d) ^ j`. -/
theorem eulerChar_eq (X : SmoothProjectiveHypersurface n d) :
    eulerChar X =
      d * ∑ j ∈ Finset.range (n + 1), ((n + 2).choose (n - j) : ℤ) * (-(d : ℤ)) ^ j := by
  cases n with
  | zero => simpa using X.eulerChar_eq_of_dim_zero
  | succ n =>
    rw [eulerChar_eq_evalFundamentalClass_chernClass, chernClass_tangentSpace, map_zsmul,
      evalFundamentalClass_hyperplaneClass_pow, smul_eq_mul, mul_comm]

end SmoothProjectiveHypersurface

end SymplecticGeometry

end
