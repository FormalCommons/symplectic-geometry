/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Distribution.LinearEquiv
public import TauCeti.Analysis.Distribution.SmulLeft
public import TauCeti.Analysis.Distribution.TestFunction.LineDeriv

/-!
# Transport of distributions, line derivatives and multiplication by smooth functions

Tau Ceti's `Distribution.transportCLM e h` moves a distribution `T` on an open set `V ⊆ E` to an
open set `Ω' ⊆ E'` along a continuous linear equivalence `e : E' ≃L[ℝ] E`, by
`φ ↦ T (φ ∘ e⁻¹)`. This file shows that it commutes with the operations of differential
operators:

* `ContinuousLinearEquiv.transportTestFunction_lineDerivOp`: transporting a test function along
  `e` turns the derivative along `v` into the derivative along `e v`;
* `Distribution.lineDerivOp_transportCLM`, `Distribution.iteratedLineDerivOp_transportCLM`: the
  derivative of the transport along `v` is the transport of the derivative along `e v`, and
  likewise for iterated derivatives along `m`, which become derivatives along `e ∘ m`;
* `Distribution.smulLeftCLM_transportCLM`: the product of the transport with a smooth function `g`
  is the transport of the product with `g ∘ e⁻¹`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, §6.1 (pullback of
  distributions by diffeomorphisms; here the diffeomorphism is linear).
-/

public section

open Set TopologicalSpace
open scoped Distributions LineDeriv ContDiff

variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E']
  [NormedSpace ℝ E']

namespace ContinuousLinearEquiv

variable {V : Opens E} {Ω : Opens E'} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Transporting a test function along `e` turns its derivative along `v` into the derivative of
the transported test function along `e v`. -/
theorem transportTestFunction_lineDerivOp (e : E ≃L[ℝ] E') (h : MapsTo e V Ω) (φ : 𝓓(V, F))
    (v : E) : e.transportTestFunction h (∂_{v} φ) = ∂_{e v} (e.transportTestFunction h φ) := by
  ext y
  simp only [TestFunction.lineDerivOp_apply_eq_fderiv, transportTestFunction_apply,
    fderiv_transportTestFunction]
  simp

end ContinuousLinearEquiv

namespace Distribution

variable {V : Opens E} {Ω' : Opens E'} {F : Type*} [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]

/-- The derivative along `v` of the transport of `T` along `e` is the transport of the derivative
of `T` along `e v`. -/
theorem lineDerivOp_transportCLM (e : E' ≃L[ℝ] E) (h : MapsTo e Ω' V) (T : 𝓓'(V, F)) (v : E') :
    ∂_{v} (transportCLM e h T) = transportCLM e h (∂_{e v} T) := by
  ext φ
  simp only [lineDerivOp_apply_apply, transportCLM_apply, map_neg,
    ContinuousLinearEquiv.transportTestFunction_lineDerivOp]

/-- The iterated derivative along `m` of the transport of `T` along `e` is the transport of the
iterated derivative of `T` along `e ∘ m`. -/
theorem iteratedLineDerivOp_transportCLM (e : E' ≃L[ℝ] E) (h : MapsTo e Ω' V) (T : 𝓓'(V, F))
    {k : ℕ} (m : Fin k → E') : ∂^{m} (transportCLM e h T) = transportCLM e h (∂^{e ∘ m} T) := by
  induction k generalizing T with
  | zero => rfl
  | succ k ih =>
    rw [LineDeriv.iteratedLineDerivOp_succ_right, LineDeriv.iteratedLineDerivOp_succ_right,
      lineDerivOp_transportCLM, ih]
    rfl

variable {n : ℕ∞} {g : E' → ℝ}

/-- The product of the transport of `T` along `e` with a `C^n` function `g` is the transport of
the product of `T` with `g ∘ e⁻¹`. -/
theorem smulLeftCLM_transportCLM (e : E' ≃L[ℝ] E) (h : MapsTo e Ω' V) (hg : ContDiff ℝ n g)
    (T : 𝓓'^{n}(V, F)) :
    smulLeftCLM hg (transportCLM e h T) =
      transportCLM e h (smulLeftCLM (hg.comp e.symm.contDiff) T) := by
  ext φ
  simp only [smulLeftCLM_apply, transportCLM_apply]
  congr 1
  ext x
  simp

end Distribution

end
