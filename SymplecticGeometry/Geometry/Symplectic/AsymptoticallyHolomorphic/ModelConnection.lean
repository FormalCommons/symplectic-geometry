/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.LinearAlgebra.Symplectic.Standard.Basic
public import TauCeti.Geometry.Symplectic.Liouville.Radial.Basic
import SymplecticGeometry.Analysis.Calculus.DifferentialForm.Poincare
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.ExtDeriv
import TauCeti.Geometry.Manifold.DifferentialForm.Regularity

/-!
# The model connection form on `StdSpace ι`

On `StdSpace ι`, with its standard symplectic form `ω₀ = stdForm ι`, this file fixes the
one-form `A₀` with linear coefficients whose exterior derivative is the constant two-form
`-2π ω₀`, and shows that every one-form with that exterior derivative on an open star-convex
set agrees there with `A₀` up to the differential of a function. With the library's
normalization of the curvature of a connection form, `hα.curvature = -(2 * π) • ω`
(`Geometry/Symplectic/AsymptoticallyHolomorphic/Power/Connection.lean`), this says that over a
Darboux ball a local section of the circle bundle can be rotated so that its connection form
becomes `A₀`.

* `SymplecticGeometry.stdConnectionForm ι`: the smooth one-form `A₀(x)(v) = -π ω₀(x, v)`, that
  is `-2π` times Tau Ceti's radial primitive `TauCeti.SymplecticForm.radialPrimitive` of `ω₀`.
* `SymplecticGeometry.mextDeriv_stdConnectionForm`: `dA₀ = -2π ω₀`, from Tau Ceti's
  `TauCeti.SymplecticForm.mextDeriv_radialPrimitive`.
* `TauCeti.SymplecticForm.mpullback_const_smul_radialPrimitive`: the radial primitive is
  homogeneous of degree two, its pull-back along `x ↦ a • x` being `a ^ 2` times itself.
* `SymplecticGeometry.exists_contDiffOn_add_mextDeriv_eq_stdConnectionForm`: if a one-form `β`
  on `StdSpace ι` is `Cʳ` (`r ≥ 1`) on an open star-convex set `s` and `dβ = -2π ω₀` on `s`,
  there is a function `θ`, `Cʳ⁺¹` on `s`, with `β + dθ = A₀` on `s`. The closed form `A₀ - β`
  is exact by the Poincaré lemma in degree one,
  `StarConvex.exists_contDiffOn_forall_fderiv_apply_eq_of_extDeriv_eq_zero`. Here `β` is a rough
  form, as pull-backs along charts are.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.7
  (connection forms on circle bundles and their curvature) and §7.4.
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 17 (the Poincaré lemma).
-/

public section

noncomputable section

open TauCeti
open scoped ContDiff Manifold

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  (B : SymplecticForm V)

/-- **The radial primitive is homogeneous of degree two**: its pull-back along the dilation
`x ↦ a • x` is `a ^ 2` times itself. -/
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

namespace SymplecticGeometry

variable (ι : Type*) [Fintype ι]

/-- The model connection form `A₀` on `StdSpace ι`: the smooth one-form with linear coefficients
`A₀(x)(v) = -π ω₀(x, v)`, which is `-2π` times the radial primitive of `ω₀`. Its exterior
derivative is `-2π ω₀` (`SymplecticGeometry.mextDeriv_stdConnectionForm`). -/
def stdConnectionForm : SmoothForm 𝓘(ℝ, StdSpace ι) (StdSpace ι) ℝ 1 :=
  -(2 * Real.pi) • (stdForm ι).radialPrimitive

theorem stdConnectionForm_def :
    stdConnectionForm ι = -(2 * Real.pi) • (stdForm ι).radialPrimitive :=
  (rfl)

variable {ι}

/-- `A₀(x)(v) = -π ω₀(x, v)`. -/
@[simp]
theorem stdConnectionForm_apply (x : StdSpace ι) (v : TangentSpace 𝓘(ℝ, StdSpace ι) x) :
    (stdConnectionForm ι).val x ![v] = -Real.pi * stdForm ι x v := by
  rw [stdConnectionForm_def, SetLike.val_smul, Pi.smul_apply,
    ContinuousAlternatingMap.smul_apply, SymplecticForm.radialPrimitive_apply, smul_eq_mul]
  ring

/-- **The exterior derivative of the model connection form**: `dA₀ = -2π ω₀`, the constant
two-form. -/
@[simp]
theorem mextDeriv_stdConnectionForm :
    mextDeriv (stdConnectionForm ι).val = (-(2 * Real.pi) • (stdForm ι).constSmooth).val := by
  rw [stdConnectionForm_def, SetLike.val_smul, mextDeriv_smul,
    SymplecticForm.mextDeriv_radialPrimitive, SetLike.val_smul]

/-- **Gauge to the model connection form.** Let `β` be a one-form on `StdSpace ι` that is `Cʳ`,
`r ≥ 1`, on an open set `s`, star-convex with respect to some point, with `dβ = -2π ω₀` on `s`.
Then there is a function `θ`, `Cʳ⁺¹` on `s`, with `β + dθ = A₀` on `s`, where `A₀` is
`SymplecticGeometry.stdConnectionForm ι`. -/
theorem exists_contDiffOn_add_mextDeriv_eq_stdConnectionForm
    {β : RoughForm 𝓘(ℝ, StdSpace ι) (StdSpace ι) ℝ 1} {s : Set (StdSpace ι)} {x₀ : StdSpace ι}
    (hs : StarConvex ℝ x₀ s) (hso : IsOpen s) {r : ℕ∞} (hr : 1 ≤ r)
    (hβ : ContDiffOn ℝ (E := StdSpace ι) (F := StdSpace ι [⋀^Fin 1]→L[ℝ] ℝ) r β s)
    (hdβ : ∀ x ∈ s, mextDeriv β x = (-(2 * Real.pi) • (stdForm ι).constSmooth).val x) :
    ∃ θ : StdSpace ι → ℝ, ContDiffOn ℝ (r + 1) θ s ∧
      ∀ x ∈ s, β x + mextDeriv (RoughForm.ofFunction 𝓘(ℝ, StdSpace ι) θ) x =
        (stdConnectionForm ι).val x := by
  have hr' : (r : WithTop ℕ∞) ≠ 0 := (lt_of_lt_of_le zero_lt_one (by exact_mod_cast hr)).ne'
  -- `A₀` and `β` as plain maps into alternating maps, for the calculus of `extDeriv`.
  let A : StdSpace ι → StdSpace ι [⋀^Fin 1]→L[ℝ] ℝ := (stdConnectionForm ι).val
  let B : StdSpace ι → StdSpace ι [⋀^Fin 1]→L[ℝ] ℝ := β
  have hA : ContDiff ℝ ∞ A :=
    isSmoothForm_modelSpace_iff.mp (stdConnectionForm ι).isSmoothForm
  obtain ⟨θ, hθ, hθw⟩ := hs.exists_contDiffOn_forall_fderiv_apply_eq_of_extDeriv_eq_zero hso hr
    (w := A - B) (hA.contDiffOn.of_le (by exact_mod_cast le_top) |>.sub hβ) fun x hx ↦ by
      have hβx : DifferentiableAt ℝ B x :=
        (hβ.differentiableOn hr' x hx).differentiableAt (hso.mem_nhds hx)
      rw [extDeriv_sub (hA.differentiable (by simp) x) hβx, ← mextDeriv_eq_extDeriv,
        ← mextDeriv_eq_extDeriv, hdβ x hx, mextDeriv_stdConnectionForm]
      -- The two sides are typed with `Fin 2` and `Fin (1 + 1)`, which blocks `rw [sub_self]`.
      exact sub_self _
  refine ⟨θ, hθ, fun x hx ↦ ?_⟩
  ext v
  rw [ContinuousAlternatingMap.add_apply, mextDeriv_ofFunction_modelSpace_apply, hθw x hx v,
    Pi.sub_apply]
  -- `v` lives in `TangentSpace 𝓘(ℝ, StdSpace ι) x` while `A x - B x` takes vectors of
  -- `StdSpace ι`, which blocks `rw [ContinuousAlternatingMap.sub_apply]`.
  exact add_sub_cancel _ _

end SymplecticGeometry

end
