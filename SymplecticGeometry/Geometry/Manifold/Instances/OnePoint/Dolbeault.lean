/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.DegreeOne
public import TauCeti.Geometry.Manifold.DifferentialForm.Dolbeault.ProjectiveLine.Cohomology
public import TauCeti.Geometry.Manifold.Instances.OnePoint.Projectivization
public import TauCeti.Geometry.Manifold.VectorBundle.CauchyRiemann.Trivial.Basic
import SymplecticGeometry.Geometry.Manifold.Instances.OnePoint

/-!
# `∂bar` on functions of the Riemann sphere

Mathlib's identification `OnePoint.equivProjectivization` of the Riemann sphere `OnePoint ℂ` with
`ℂP¹ = ℙ ℂ (Fin 2 → ℂ)` is a biholomorphism. This file states that in terms of Tau Ceti's almost
complex structures of complex manifolds, and uses it to carry Tau Ceti's solution of `∂bar f = β`
on `ℂP¹` to the Riemann sphere.

## Main declarations

* `OnePoint.isPseudoholomorphic_equivProjectivization` and
  `OnePoint.isPseudoholomorphic_equivProjectivization_symm`: the identification and its inverse
  are pseudoholomorphic for the structures `ofComplexManifold` on both sides.
* `OnePoint.exists_contMDiff_dbarFunction_eq`: for the standard complex structure of the Riemann
  sphere, every smooth `(0,1)`-form `β` with values in a complex Banach space is `∂bar f` of a
  smooth function `f`. The form is pulled back to `ℂP¹`, solved there with
  `TauCeti.SmoothForm.IsOfType.exists_delBar_eq_projectivization`, and the solution is pulled
  back to the sphere, using that pullback along a pseudoholomorphic map commutes with `∂bar`
  (`TauCeti.SmoothAlmostComplexStructure.mpullback_delBar`).

## References

* [D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*,
  2nd ed.][McDuffSalamon2012], Appendix C (real Cauchy–Riemann operators on Riemann surfaces).
* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §13 (the Dolbeault lemma).
-/

public section

open TauCeti TauCeti.SmoothAlmostComplexStructure
open scoped Manifold ContDiff TauCeti.ComplexManifold LinearAlgebra.Projectivization

namespace OnePoint

/-- Mathlib's identification of the Riemann sphere with `ℂP¹`, `t ↦ [t : 1]` and `∞ ↦ [1 : 0]`,
is pseudoholomorphic for the almost complex structures of the two complex manifolds. -/
theorem isPseudoholomorphic_equivProjectivization :
    IsPseudoholomorphic (ofComplexManifold ℂ (OnePoint ℂ))
      (ofComplexManifold (Fin 1 → ℂ) (ℙ ℂ (Fin 2 → ℂ))) (equivProjectivization ℂ) :=
  isPseudoholomorphic_ofComplexManifold_iff.2
    (contMDiff_equivProjectivization.mdifferentiable (by simp))

/-- The inverse of Mathlib's identification of the Riemann sphere with `ℂP¹` is pseudoholomorphic
for the almost complex structures of the two complex manifolds. -/
theorem isPseudoholomorphic_equivProjectivization_symm :
    IsPseudoholomorphic (ofComplexManifold (Fin 1 → ℂ) (ℙ ℂ (Fin 2 → ℂ)))
      (ofComplexManifold ℂ (OnePoint ℂ)) (equivProjectivization ℂ).symm :=
  isPseudoholomorphic_ofComplexManifold_iff.2
    (contMDiff_equivProjectivization_symm.mdifferentiable (by simp))

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- **`∂bar` is onto on smooth functions of the Riemann sphere.** For the standard complex
structure of `OnePoint ℂ` and a complex Banach space `F`, every smooth section `β` of the bundle
`x ↦ (T_x → F)` that is a `(0,1)`-form at every point is `∂bar f` of a smooth function
`f : OnePoint ℂ → F`. -/
-- Inside `namespace OnePoint` the notation `∞` also names the point at infinity, so the
-- smoothness exponent `∞` is written as the cast of `⊤ : ℕ∞`.
theorem exists_contMDiff_dbarFunction_eq
    (β : ContMDiffSection 𝓘(ℝ, ℂ) (ℂ →L[ℝ] F) ((⊤ : ℕ∞) : ℕ∞ω)
      (fun x : OnePoint ℂ ↦ TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] F))
    (hβ : ∀ x, (ofComplexManifold ℂ (OnePoint ℂ)).IsZeroOneForm
      (V := Bundle.Trivial (OnePoint ℂ) F) (β x)) :
    ∃ f : OnePoint ℂ → F, ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, F) ((⊤ : ℕ∞) : ℕ∞ω) f ∧
      ∀ x, (ofComplexManifold ℂ (OnePoint ℂ)).dbarFunction f x = β x := by
  have hφ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin 1 → ℂ) ((⊤ : ℕ∞) : ℕ∞ω)
      (equivProjectivization ℂ) :=
    contMDiff_equivProjectivization_real.of_le le_top
  have hψ : ContMDiff 𝓘(ℝ, Fin 1 → ℂ) 𝓘(ℝ, ℂ) ((⊤ : ℕ∞) : ℕ∞ω)
      (equivProjectivization ℂ).symm :=
    contMDiff_equivProjectivization_symm_real.of_le le_top
  set α := SmoothForm.degreeOneEquiv.symm β
  have hαβ (x : OnePoint ℂ) (v : TangentSpace 𝓘(ℝ, ℂ) x) : α.val x ![v] = β x v := by
    rw [← SmoothForm.degreeOneEquiv_apply_apply_vec, LinearEquiv.apply_symm_apply]
  have hα : α.IsOfType (ofComplexManifold ℂ (OnePoint ℂ)) 0 1 :=
    SmoothForm.isOfType_zero_one_iff.2 fun x v ↦ by
      rw [hαβ, hαβ, isZeroOneForm_iff.1 (hβ x) v]
      exact (_root_.neg_smul Complex.I (β x v)).symm
  obtain ⟨g, hg⟩ := (hα.mpullback hψ isPseudoholomorphic_equivProjectivization_symm)
    |>.exists_delBar_eq_projectivization
  set f := SmoothForm.mpullback (equivProjectivization ℂ) hφ g
  have hf : (ofComplexManifold ℂ (OnePoint ℂ)).delBar f = α := by
    rw [← mpullback_delBar _ hφ isPseudoholomorphic_equivProjectivization, hg,
      SmoothForm.mpullback_mpullback_of_comp_eq hφ hψ contMDiff_id contMDiff_id
        (funext (equivProjectivization ℂ).symm_apply_apply)]
    simp
  refine ⟨fun y ↦ f.val y 0, SmoothForm.contMDiff_apply_zero f,
    fun x ↦ ContinuousLinearMap.ext fun v ↦ ?_⟩
  rw [← delBar_apply_apply_eq_dbarFunction, hf, hαβ]

end OnePoint

end
