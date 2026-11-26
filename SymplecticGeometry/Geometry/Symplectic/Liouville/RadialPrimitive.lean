/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.Liouville.Radial.Basic
import Mathlib.Tactic.FinCases

/-!
# Homogeneity of the radial primitive

For a symplectic form `B` on a finite-dimensional real vector space `V`, Tau Ceti's radial
primitive `TauCeti.SymplecticForm.radialPrimitive B` is the one-form `x ↦ B(x, ·) / 2`, whose
exterior derivative is the constant form `B`. Its coefficients are linear in `x`, so it is
homogeneous of degree two under dilations:

* `TauCeti.SymplecticForm.mpullback_const_smul_radialPrimitive`: the pull-back of the radial
  primitive along `x ↦ a • x` is `a ^ 2` times the radial primitive.

The statement concerns only Tau Ceti's notions, so it is stated in Tau Ceti's namespace and could
sit next to `TauCeti.SymplecticForm.radialPrimitive_apply` in Tau Ceti's
`TauCeti/Geometry/Symplectic/Liouville/Radial/Basic.lean`.
-/

public section

open scoped Manifold

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  (B : SymplecticForm V)

/-- **The radial primitive is homogeneous of degree two**: its pull-back along the dilation
`x ↦ a • x` is `a ^ 2` times itself. -/
@[simp]
theorem mpullback_const_smul_radialPrimitive (a : ℝ) :
    mpullback 𝓘(ℝ, V) 𝓘(ℝ, V) (a • ·) B.radialPrimitive.val = a ^ 2 • B.radialPrimitive.val := by
  funext x
  ext v
  obtain ⟨w, rfl⟩ : ∃ w, v = ![w] := ⟨v 0, by funext i; fin_cases i; rfl⟩
  -- `w` is a tangent vector at `x` and its image one at `a • x`; both sides are read in `V`.
  have hm : @Eq V (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, V) (a • ·) x w) (a • w) :=
    congrArg (· w) ((hasFDerivAt_id x).const_smul a).hasMFDerivAt.mfderiv
  rw [mpullback_apply_one, radialPrimitive_apply, Pi.smul_apply,
    ContinuousAlternatingMap.smul_apply, radialPrimitive_apply, hm]
  simp only [map_smul, smul_eq_mul]
  have key (u : V) : 2⁻¹ * (a • B.toBilinForm x) (a • u) = a ^ 2 * (2⁻¹ * B.toBilinForm x u) := by
    simp only [LinearMap.smul_apply, map_smul, smul_eq_mul]
    ring
  -- The goal is `key w`, with `w` typed as a tangent vector at `x` rather than in `V`, which
  -- blocks `rw [LinearMap.smul_apply]` on it directly.
  exact key w

end TauCeti.SymplecticForm

end
