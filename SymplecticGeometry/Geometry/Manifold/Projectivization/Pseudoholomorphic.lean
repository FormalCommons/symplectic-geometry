/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure
public import SymplecticGeometry.Geometry.Manifold.Projectivization.Hopf

/-!
# The projection onto complex projective space is pseudoholomorphic

Write `J` for the complex structure `TauCeti.SmoothAlmostComplexStructure.ofComplexManifold` of a
complex manifold. This file shows that the projection
`Projectivization.mkNonzero ℂ n : ℂⁿ⁺¹ ∖ 0 → ℙ ℂ (Fin (n + 1) → ℂ)` respects `J`, and so do the
maps of `ℂPⁿ` induced by linear actions on `ℂⁿ⁺¹`.

* `Projectivization.isPseudoholomorphic_mkNonzero`: the projection is pseudoholomorphic, since it
  is holomorphic (`Projectivization.contMDiff_mkNonzero_self`) and a map of complex manifolds is
  pseudoholomorphic exactly when it is holomorphic
  (`TauCeti.SmoothAlmostComplexStructure.isPseudoholomorphic_ofComplexManifold_iff`).
* `Projectivization.mfderiv_mkNonzero_I_smul`: its real derivative carries multiplication by `i`
  on `ℂⁿ⁺¹` to `J` on `ℂPⁿ`, as the real derivative of every holomorphic map does
  (`MDifferentiableAt.mfderiv_ofComplexManifold_apply`).
* `Projectivization.isPseudoholomorphic_smul`: a group acting `ℂ`-linearly on `ℂⁿ⁺¹` acts on
  `ℂPⁿ` by pseudoholomorphic maps, since Tau Ceti's `Projectivization.instContMDiffConstSMul`
  says that it acts by holomorphic ones.

## References

* [P. Griffiths, J. Harris, *Principles of Algebraic Geometry*][GriffithsHarris1978], Chapter 0,
  §1.
-/

public section

open TauCeti
open scoped Manifold LinearAlgebra.Projectivization

namespace Projectivization

variable {n : ℕ}

open SmoothAlmostComplexStructure

variable (n) in
/-- The projection `ℂⁿ⁺¹ ∖ 0 → ℂPⁿ` is pseudoholomorphic for the complex structures of the two
complex manifolds. -/
theorem isPseudoholomorphic_mkNonzero :
    IsPseudoholomorphic (ofComplexManifold (Fin (n + 1) → ℂ) (puncturedSpace (Fin (n + 1) → ℂ)))
      (ofComplexManifold (Fin n → ℂ) (ℙ ℂ (Fin (n + 1) → ℂ))) (mkNonzero ℂ n) :=
  isPseudoholomorphic_ofComplexManifold_iff.2
    ((contMDiff_mkNonzero_self 1).mdifferentiable one_ne_zero)

/-- The real derivative of the projection `ℂⁿ⁺¹ ∖ 0 → ℂPⁿ` carries multiplication by `i` to the
complex structure of `ℂPⁿ`. -/
theorem mfderiv_mkNonzero_I_smul (z : puncturedSpace (Fin (n + 1) → ℂ))
    (v : Fin (n + 1) → ℂ) :
    mfderiv 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin n → ℂ) (mkNonzero ℂ n) z (Complex.I • v) =
      ofComplexManifold (Fin n → ℂ) (ℙ ℂ (Fin (n + 1) → ℂ)) (mkNonzero ℂ n z)
        (mfderiv 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin n → ℂ) (mkNonzero ℂ n) z v) := by
  simpa [ofComplexManifold_apply] using
    ((contMDiff_mkNonzero_self 1).mdifferentiableAt (x := z)
      one_ne_zero).mfderiv_ofComplexManifold_apply v

/-- Every element of a group acting `ℂ`-linearly on `ℂⁿ⁺¹` acts on `ℂPⁿ` by a pseudoholomorphic
map, since it acts by a holomorphic map (`Projectivization.instContMDiffConstSMul`). -/
theorem isPseudoholomorphic_smul {G : Type*} [Group G] [DistribMulAction G (Fin (n + 1) → ℂ)]
    [SMulCommClass G ℂ (Fin (n + 1) → ℂ)] (g : G) :
    IsPseudoholomorphic (ofComplexManifold (Fin n → ℂ) (ℙ ℂ (Fin (n + 1) → ℂ)))
      (ofComplexManifold (Fin n → ℂ) (ℙ ℂ (Fin (n + 1) → ℂ)))
      fun x : ℙ ℂ (Fin (n + 1) → ℂ) ↦ g • x :=
  isPseudoholomorphic_ofComplexManifold_iff.2
    ((contMDiff_const_smul (I := 𝓘(ℂ, Fin n → ℂ)) (n := 1) g).mdifferentiable one_ne_zero)

end Projectivization

end
