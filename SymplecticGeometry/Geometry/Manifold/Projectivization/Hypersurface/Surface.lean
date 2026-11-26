/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Signature
public import SymplecticGeometry.AlgebraicTopology.Cohomology.Cap.RationalCoefficients
public import TauCeti.AlgebraicTopology.Cohomology.Cap.Kronecker

import SymplecticGeometry.AlgebraicTopology.Cohomology.Empty
import SymplecticGeometry.Geometry.Manifold.Projectivization.Hypersurface.BettiNumber
public import SymplecticGeometry.Geometry.Manifold.Projectivization.Hypersurface.EulerCharacteristic
public import SymplecticGeometry.Geometry.Manifold.Projectivization.Hypersurface.ChernClass
import SymplecticGeometry.Geometry.Manifold.Projectivization.Hypersurface.Degree
import TauCeti.LinearAlgebra.QuadraticForm.Signature

/-!
# Smooth surfaces in `ℂℙ³`

Let `X ⊆ ℂℙ³` be a smooth surface of degree `d`, with inclusion `ι`, and let `h` be the
hyperplane class. This file specializes the general results on hypersurfaces to `X`.

* Its Chern classes are `c₁(TX) = (4 - d) ι^* h` and `c₂(TX) = (d² - 4d + 6) (ι^* h)²`
  (`SmoothProjectiveHypersurface.chernClass_tangentSpace`), and its Euler characteristic is
  `χ(X) = d³ - 4d² + 6d` (`SmoothProjectiveHypersurface.eulerChar_eq`).
* For `d ≠ 0` its second Betti number is `b₂ = χ(X) - 2 = d³ - 4d² + 6d - 2`
  (`SmoothProjectiveHypersurface.bettiNumber_middle`; the Lefschetz theorem makes `b₀ = b₄ = 1`
  and `b₁ = b₃ = 0`).
* The intersection form of `X` is the cup pairing `(α, β) ↦ ⟨α ⌣ β, [X]⟩` on `H²(X; ℚ)`
  (`TauCeti.HomologicalOrientation.intersectionForm`, for the complex orientation), `b⁺`, `b⁻`
  are the indices of inertia `sigPos` and `sigNeg` of its quadratic form, and the signature is
  `σ = b⁺ - b⁻` (`TauCeti.HomologicalOrientation.signature`). The library does not prove
  Hirzebruch's signature theorem `3σ = ⟨c₁² - 2c₂, [X]⟩`; `signature_surface` takes it as a
  hypothesis, and derives `3σ = (4 - d²) d` from the Chern numbers `⟨c₁², [X]⟩ = (4 - d)² d` and
  `⟨c₂, [X]⟩ = (d² - 4d + 6) d`. By Poincaré duality the intersection form is nondegenerate, so
  `b⁺ + b⁻ = b₂`
  (`TauCeti.HomologicalOrientation.sigPos_add_sigNeg_intersectionQuadraticForm`), which gives
  `b⁺` and `b⁻`.

The formulas for `b₂`, `b⁺` and `b⁻` fail for `d = 0`, where `X` is empty.

## Main results

The following are in the namespace `SymplecticGeometry.SmoothProjectiveHypersurface`.

* `chernClass_one_tangentSpace_surface`, `chernClass_two_tangentSpace_surface`: `c₁` and `c₂`.
* `eulerChar_surface`: `χ(X) = d³ - 4d² + 6d`.
* `bettiNumber_two_surface`: `b₂ = d³ - 4d² + 6d - 2` for `d ≠ 0`; `bettiNumber_two_fermat_zero`
  shows that `d ≠ 0` is needed.
* `evalFundamentalClass_integralCup_chernClass_one_surface`,
  `evalFundamentalClass_chernClass_two_surface`: the Chern numbers `⟨c₁ ⌣ c₁, [X]⟩` and
  `⟨c₂, [X]⟩`.
* `signature_surface`: given the signature theorem, and for `d ≠ 0`, `3σ = (4 - d²) d`,
  `3b⁺ = d³ - 6d² + 11d - 3` and `3b⁻ = 2d³ - 6d² + 7d - 3`; `sigPos_fermat_zero` shows that
  the last two need `d ≠ 0`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Example 4.4.3 and Exercise 4.4.6.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.3.
-/

public section

open CategoryTheory MonoidalCategory Module SymplecticGeometry.Bundle TauCeti
open scoped Manifold TauCeti.ComplexManifold

namespace SymplecticGeometry

namespace SmoothProjectiveHypersurface

variable {d : ℕ} (X : SmoothProjectiveHypersurface 2 d)

/-- **The first Chern class of a surface in `ℂℙ³`.** A smooth surface `X ⊆ ℂℙ³` of degree `d`
has `c₁(TX) = (4 - d) ι^* h`.

Milestone: *Chern classes of projective hypersurfaces*. -/
theorem chernClass_one_tangentSpace_surface :
    chernClass (Fin 2 → ℂ)
        (TangentSpace 𝓘(ℂ, Fin 2 → ℂ) : X → Type) 1 =
      (4 - d : ℤ) • X.hyperplaneClass := by
  rw [chernClass_one_tangentSpace]
  norm_num

/-- **The second Chern class of a surface in `ℂℙ³`.** A smooth surface `X ⊆ ℂℙ³` of degree `d`
has `c₂(TX) = (d² - 4d + 6) (ι^* h)²`, where `(ι^* h)²` is read in `H⁴(X; ℤ)`.

Milestone: *Chern classes of projective hypersurfaces*. -/
theorem chernClass_two_tangentSpace_surface :
    chernClass (Fin 2 → ℂ)
        (TangentSpace 𝓘(ℂ, Fin 2 → ℂ) : X → Type) 2 =
      ((d : ℤ) ^ 2 - 4 * d + 6) •
        ((TopCat.of X).evenIntegralCohomologyOf 1 X.hyperplaneClass ^ 2) 2 := by
  rw [chernClass_tangentSpace]
  congr 1
  simp [Finset.sum_range_succ, Nat.choose]
  ring

/-- **The Euler characteristic of a surface in `ℂℙ³`.** A smooth surface `X ⊆ ℂℙ³` of degree `d`
has `χ(X) = d³ - 4d² + 6d`.

Milestone: *Chern classes of projective hypersurfaces*. -/
theorem eulerChar_surface : eulerChar X = (d : ℤ) ^ 3 - 4 * d ^ 2 + 6 * d := by
  rw [eulerChar_eq]
  simp [Finset.sum_range_succ, Nat.choose]
  ring

/-- **The second Betti number of a surface in `ℂℙ³`.** For `d ≠ 0`, a smooth surface `X ⊆ ℂℙ³` of
degree `d` has `b₂ = d³ - 4d² + 6d - 2`.

Milestone: *Chern classes of projective hypersurfaces*. -/
theorem bettiNumber_two_surface (hd : d ≠ 0) :
    (bettiNumber ℚ X 2 : ℤ) = (d : ℤ) ^ 3 - 4 * d ^ 2 + 6 * d - 2 := by
  have h := X.bettiNumber_middle hd
  rw [X.eulerChar_surface] at h
  norm_num at h
  linarith

/-- `bettiNumber_two_surface` needs `d ≠ 0`: the Fermat surface of degree `0` is empty, so its
second Betti number is `0`, while `d³ - 4d² + 6d - 2 = -2` for `d = 0`. -/
theorem bettiNumber_two_fermat_zero : bettiNumber ℚ (fermat 2 0) 2 = 0 :=
  bettiNumber_eq_zero_of_isEmpty ℚ _ 2

/-- On a surface in `ℂℙ³`, `⟨c₁ ⌣ c₁, [X]⟩ = (4 - d)² d`. -/
theorem evalFundamentalClass_integralCup_chernClass_one_surface :
    complexManifoldEvalFundamentalClass (Fin 2 → ℂ) X (Module.finrank_fin_fun ℂ)
      ((TopCat.of X).integralCup (2 * 1) (2 * 1) (2 * (1 + 1)) rfl
        (chernClass (Fin 2 → ℂ)
          (TangentSpace 𝓘(ℂ, Fin 2 → ℂ) : X → Type) 1)
        (chernClass (Fin 2 → ℂ)
          (TangentSpace 𝓘(ℂ, Fin 2 → ℂ) : X → Type) 1)) =
      (4 - d : ℤ) ^ 2 * d := by
  rw [chernClass_one_tangentSpace_surface, TopCat.integralCup_zsmul_left, map_zsmul,
    map_zsmul, map_zsmul]
  have h := (TopCat.of X).evenIntegralCohomologyOf_pow_succ_apply X.hyperplaneClass 1
  rw [pow_one, DirectSum.of_eq_same] at h
  rw [← h, evalFundamentalClass_hyperplaneClass_pow (n := 1), smul_eq_mul, smul_eq_mul]
  ring

/-- On a surface in `ℂℙ³`, `⟨c₂, [X]⟩ = (d² - 4d + 6) d`. -/
theorem evalFundamentalClass_chernClass_two_surface :
    complexManifoldEvalFundamentalClass (Fin 2 → ℂ) X (Module.finrank_fin_fun ℂ)
      (chernClass (Fin 2 → ℂ)
        (TangentSpace 𝓘(ℂ, Fin 2 → ℂ) : X → Type) 2) =
      ((d : ℤ) ^ 2 - 4 * d + 6) * d := by
  rw [chernClass_two_tangentSpace_surface, map_zsmul,
    evalFundamentalClass_hyperplaneClass_pow (n := 1), smul_eq_mul]

/-- **The signature of a surface in `ℂℙ³`.** Let `X ⊆ ℂℙ³` be a smooth surface of degree `d`,
oriented by its complex structure, `σ` its signature
(`TauCeti.HomologicalOrientation.signature`, in degree `2`), and `b⁺`, `b⁻` the positive and
negative indices of inertia of the quadratic form of its intersection form on `H²(X; ℚ)`
(`TauCeti.HomologicalOrientation.intersectionQuadraticForm`), so that `σ = b⁺ - b⁻`. Assume the
signature theorem `3σ = ⟨c₁ ⌣ c₁, [X]⟩ - 2 ⟨c₂, [X]⟩`, which the library does not prove, and
`d ≠ 0`. Then `3σ = (4 - d²) d`, `3b⁺ = d³ - 6d² + 11d - 3` and `3b⁻ = 2d³ - 6d² + 7d - 3`.
Only the formulas for `b⁺` and `b⁻` use `d ≠ 0` (see `sigPos_fermat_zero`); the one for `σ`
follows from the signature theorem in every degree.

Milestone: *Chern classes of projective hypersurfaces*. -/
theorem signature_surface (hd : d ≠ 0)
    (hsignature : 3 * (complexManifoldHomologicalOrientation (Fin 2 → ℂ) X
        (Module.finrank_fin_fun ℂ)).signature
        (finrank_real_of_finrank_complex_eq_add_one (Module.finrank_fin_fun ℂ))
        (show 2 + 2 = 2 * 1 + 1 + 1 from rfl) =
      complexManifoldEvalFundamentalClass (Fin 2 → ℂ) X (Module.finrank_fin_fun ℂ)
        ((TopCat.of X).integralCup (2 * 1) (2 * 1) (2 * (1 + 1)) rfl
          (chernClass (Fin 2 → ℂ)
            (TangentSpace 𝓘(ℂ, Fin 2 → ℂ) : X → Type) 1)
          (chernClass (Fin 2 → ℂ)
            (TangentSpace 𝓘(ℂ, Fin 2 → ℂ) : X → Type) 1)) -
        2 * complexManifoldEvalFundamentalClass (Fin 2 → ℂ) X
          (Module.finrank_fin_fun ℂ) (chernClass (Fin 2 → ℂ)
            (TangentSpace 𝓘(ℂ, Fin 2 → ℂ) : X → Type) 2)) :
    3 * (complexManifoldHomologicalOrientation (Fin 2 → ℂ) X (Module.finrank_fin_fun ℂ)).signature
        (finrank_real_of_finrank_complex_eq_add_one (Module.finrank_fin_fun ℂ))
        (show 2 + 2 = 2 * 1 + 1 + 1 from rfl) =
        (4 - (d : ℤ) ^ 2) * d ∧
      3 * (sigPos
          ((complexManifoldHomologicalOrientation (Fin 2 → ℂ) X
            (Module.finrank_fin_fun ℂ)).intersectionQuadraticForm
            (finrank_real_of_finrank_complex_eq_add_one (Module.finrank_fin_fun ℂ))
            (show 2 + 2 = 2 * 1 + 1 + 1 from rfl)) : ℤ) =
        (d : ℤ) ^ 3 - 6 * d ^ 2 + 11 * d - 3 ∧
      3 * (sigNeg
          ((complexManifoldHomologicalOrientation (Fin 2 → ℂ) X
            (Module.finrank_fin_fun ℂ)).intersectionQuadraticForm
            (finrank_real_of_finrank_complex_eq_add_one (Module.finrank_fin_fun ℂ))
            (show 2 + 2 = 2 * 1 + 1 + 1 from rfl)) : ℤ) =
        2 * (d : ℤ) ^ 3 - 6 * d ^ 2 + 7 * d - 3 := by
  rw [evalFundamentalClass_integralCup_chernClass_one_surface,
    evalFundamentalClass_chernClass_two_surface, HomologicalOrientation.signature_def,
    QuadraticForm.signature_def] at hsignature
  rw [HomologicalOrientation.signature_def, QuadraticForm.signature_def]
  have hb := congrArg (Nat.cast : ℕ → ℤ) <|
    (complexManifoldHomologicalOrientation (Fin 2 → ℂ) X (Module.finrank_fin_fun ℂ))
      |>.sigPos_add_sigNeg_intersectionQuadraticForm
        (finrank_real_of_finrank_complex_eq_add_one (Module.finrank_fin_fun ℂ))
        (show 2 + 2 = 2 * 1 + 1 + 1 from rfl)
        even_two
  push_cast at hb
  rw [X.bettiNumber_two_surface hd] at hb
  exact ⟨by rw [hsignature]; ring, by linarith, by linarith⟩

/-- `signature_surface` needs `d ≠ 0` for `b⁺` and `b⁻`: the Fermat surface of degree `0` is
empty, so every quadratic form on its `H²(X; ℚ)` has `b⁺ = 0`, while
`(d³ - 6d² + 11d - 3) / 3 = -1` for `d = 0`. -/
theorem sigPos_fermat_zero
    (q : QuadraticForm ℚ
      ((TopCat.of (fermat 2 0)).singularCohomology (𝟙_ (ModuleCat.{0} ℚ)) ℚ (𝟙_ _) 2)) :
    sigPos q = 0 :=
  QuadraticForm.sigPos_eq_zero_of_finrank_eq_zero q finrank_zero_of_subsingleton

end SmoothProjectiveHypersurface

end SymplecticGeometry

end
