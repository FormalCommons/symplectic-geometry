/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Hodge.Conjugation
public import TauCeti.Geometry.Manifold.DeRham.ComplexCoefficients

/-!
# Complex conjugation on complex de Rham cohomology

Complex de Rham cohomology `TauCeti.complexDeRhamCohomology I M k` is the complexification of
real de Rham cohomology (`TauCeti.complexDeRhamCohomology.complexificationEquiv`). This file
equips it with its complex conjugation, as a Hodge conjugation in Tau Ceti's sense: the
conjugate-linear involution that fixes the classes of real forms.

## Main definitions

* `TauCeti.complexDeRhamCohomology.conj`: complex conjugation on `H^k_dR(M; ℂ)`, Tau Ceti's
  `LinearEquiv.conjugationOfComplexification` of `complexificationEquiv`: the transport of the
  tensor conjugation `TauCeti.tmulConj` along it.

## Main results

* `TauCeti.complexDeRhamCohomology.conj_complexificationEquiv`: under `complexificationEquiv`,
  `conj` is the conjugation of the scalar factor.
* `TauCeti.complexDeRhamCohomology.conj_mk`: `conj` sends the class of a closed complex form to
  the class of the form with conjugated coefficients.
* `TauCeti.complexDeRhamCohomology.conj_ofReal`: `conj` fixes the classes of real forms.

## References

* [P. Griffiths, J. Harris, *Principles of Algebraic Geometry*][GriffithsHarris1978],
  Chapter 0, §7.
-/

public section

noncomputable section

open scoped ContDiff Manifold TensorProduct

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 2 M]

namespace complexClosedForms

/-- The closed complex form with complex-conjugated coefficients. -/
def conj {k : ℕ} (φ : complexClosedForms I M k) : complexClosedForms I M k :=
  ⟨SmoothForm.mapCoeff (Complex.conjCLE : ℂ →L[ℝ] ℂ) φ.val, by
    rw [mem_complexClosedForms, SmoothForm.mextDerivₗ_mapCoeff,
      (mem_complexClosedForms I φ.val).1 φ.property, map_zero]⟩

/-- The underlying form of the conjugate of a closed complex form. -/
@[simp]
theorem coe_conj {k : ℕ} (φ : complexClosedForms I M k) :
    (conj I φ).val = SmoothForm.mapCoeff (Complex.conjCLE : ℂ →L[ℝ] ℂ) φ.val :=
  (rfl)

/-- Conjugating the coefficients twice gives back the closed form. -/
@[simp]
theorem conj_conj {k : ℕ} (φ : complexClosedForms I M k) : conj I (conj I φ) = φ := by
  refine Subtype.ext <| Subtype.ext <| funext fun x ↦ ?_
  ext v
  simp [RoughForm.mapCoeff_apply]

/-- The real part of the conjugate of a closed complex form is its real part. -/
@[simp]
theorem re_conj {k : ℕ} (φ : complexClosedForms I M k) : re I (conj I φ) = re I φ := by
  refine Subtype.ext <| Subtype.ext <| funext fun x ↦ ?_
  ext v
  simp [RoughForm.mapCoeff_apply]

/-- The imaginary part of the conjugate of a closed complex form is minus its imaginary part. -/
@[simp]
theorem im_conj {k : ℕ} (φ : complexClosedForms I M k) : im I (conj I φ) = -im I φ := by
  refine Subtype.ext <| Subtype.ext <| funext fun x ↦ ?_
  ext v
  simp [RoughForm.mapCoeff_apply]

/-- The conjugate of a closed complex form `α + i β`, with `α` and `β` its real and imaginary
parts, is `α + (-i) β`. -/
theorem conj_eq_ofReal_re_add_neg_I_smul_ofReal_im {k : ℕ} (φ : complexClosedForms I M k) :
    conj I φ =
      closedForms.ofReal I (re I φ) + (-Complex.I) • closedForms.ofReal I (im I φ) := by
  refine Subtype.ext <| Subtype.ext <| funext fun x ↦ ?_
  ext v
  apply Complex.ext <;> simp [RoughForm.mapCoeff_apply]

end complexClosedForms

namespace complexDeRhamCohomology

variable {I} in
/-- Complex conjugation on complex de Rham cohomology: the conjugation of the complexification
`ℂ ⊗[ℝ] H^k_dR(M; ℝ)`, transported along `complexificationEquiv`
(`LinearEquiv.conjugationOfComplexification`). It sends the class of a closed
complex form to the class of its complex conjugate (`conj_mk`). -/
def conj (k : ℕ) : Hodge.Conjugation (complexDeRhamCohomology I M k) where
  toEquiv := .ofInvolutive _
    (complexificationEquiv I k).conjugationOfComplexification_involutive
  involutive := (complexificationEquiv I k).conjugationOfComplexification_involutive

/-- Under `complexificationEquiv`, conjugation on complex de Rham cohomology is the conjugation of
the scalar factor of `ℂ ⊗[ℝ] H^k_dR(M; ℝ)`. -/
@[simp]
theorem conj_complexificationEquiv (k : ℕ) (u : ℂ ⊗[ℝ] deRhamCohomology I M k) :
    (conj k).toEquiv (complexificationEquiv I k u) =
      complexificationEquiv I k (tmulConj _ u) := by
  simp [conj]

/-- Conjugation on complex de Rham cohomology fixes the classes of real forms. -/
@[simp]
theorem conj_ofReal (k : ℕ) (a : deRhamCohomology I M k) :
    (conj k).toEquiv (ofReal I k a) = ofReal I k a := by
  simpa using conj_complexificationEquiv I k (1 ⊗ₜ a)

/-- Conjugation on complex de Rham cohomology sends the class of a closed complex form to the
class of the form with complex-conjugated coefficients. -/
@[simp]
theorem conj_mk (k : ℕ) (φ : complexClosedForms I M k) :
    (conj k).toEquiv (mk I k φ) = mk I k (complexClosedForms.conj I φ) := by
  rw [← (complexificationEquiv I k).apply_symm_apply (mk I k φ), conj_complexificationEquiv,
    complexClosedForms.conj_eq_ofReal_re_add_neg_I_smul_ofReal_im]
  simp [complexificationEquiv_symm_mk, ofReal_mk]

end complexDeRhamCohomology

end TauCeti

end
