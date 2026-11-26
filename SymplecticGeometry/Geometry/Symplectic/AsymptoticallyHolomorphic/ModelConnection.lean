/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
public import SymplecticGeometry.LinearAlgebra.Symplectic.Standard.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.ExtDeriv
public import TauCeti.Geometry.Symplectic.Liouville.Linear
import SymplecticGeometry.LinearAlgebra.Symplectic.Basic
import TauCeti.Analysis.Calculus.DifferentialForm.Gradient

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

* `SymplecticGeometry.stdConnectionForm ι`: the radial one-form
  `A₀(x)(v) = -π ω₀(x, v)`, Tau Ceti's `ContinuousLinearMap.liouvilleFormCLM` of the continuous
  bilinear form `-2π ω₀`.
* `SymplecticGeometry.extDeriv_stdConnectionForm_apply`: `dA₀(v₀, v₁) = -2π ω₀(v₀, v₁)` at every
  point, from Tau Ceti's `ContinuousLinearMap.extDeriv_liouvilleFormCLM_apply_of_skew`.
* `SymplecticGeometry.exists_contDiffOn_add_mextDeriv_eq_stdConnectionForm`: if a one-form `β`
  on `StdSpace ι` is `Cʳ` (`r ≥ 1`) on an open star-convex set `s` and `dβ = -2π ω₀` on `s`,
  there is a function `θ`, `Cʳ⁺¹` on `s`, with `β + dθ = A₀` on `s`. The closed form `A₀ - β` is
  exact by Tau Ceti's Poincaré lemma for covector fields,
  `StarConvex.exists_contDiffOn_forall_hasFDerivAt_of_extDeriv_eq_zero`. Here `β` is a rough
  form, as pull-backs along charts are; `exists_contDiffOn_fderiv_apply_eq_stdConnectionForm_sub`
  is the same statement for a map `StdSpace ι → StdSpace ι [⋀^Fin 1]→L[ℝ] ℝ`, with `dθ = A₀ - β`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.7
  (connection forms on circle bundles and their curvature).
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 17 (the Poincaré lemma).
-/

public section

noncomputable section

open ContinuousAlternatingMap TauCeti
open scoped ContDiff Manifold

namespace SymplecticGeometry

variable (ι : Type*) [Fintype ι]

/-- The model connection form `A₀` on `StdSpace ι`: the one-form with linear coefficients
`A₀(x)(v) = -π ω₀(x, v)`, whose exterior derivative is `-2π ω₀`
(`SymplecticGeometry.extDeriv_stdConnectionForm_apply`). It is the radial primitive
`ContinuousLinearMap.liouvilleFormCLM` of the continuous bilinear form `-2π ω₀`. -/
def stdConnectionForm : StdSpace ι →L[ℝ] StdSpace ι [⋀^Fin 1]→L[ℝ] ℝ :=
  ContinuousLinearMap.liouvilleFormCLM
    (-(2 * Real.pi) • (stdForm ι).toBilinForm.toContinuousBilinearMap)

theorem stdConnectionForm_def :
    stdConnectionForm ι = ContinuousLinearMap.liouvilleFormCLM
      (-(2 * Real.pi) • (stdForm ι).toBilinForm.toContinuousBilinearMap) :=
  (rfl)

variable {ι}

/-- `A₀(x)(v) = -π ω₀(x, v)`. -/
@[simp]
theorem stdConnectionForm_apply (x : StdSpace ι) (v : Fin 1 → StdSpace ι) :
    stdConnectionForm ι x v = -Real.pi * stdForm ι x (v 0) := by
  rw [stdConnectionForm_def, ContinuousLinearMap.liouvilleFormCLM_apply]
  simp only [_root_.smul_apply, LinearMap.toContinuousBilinearMap_apply, smul_eq_mul]
  rw [SymplecticForm.toBilinForm_apply]
  ring

/-- **The exterior derivative of the model connection form**: `dA₀ = -2π ω₀`, the constant
two-form, at every point. -/
theorem extDeriv_stdConnectionForm_apply (x : StdSpace ι) (v : Fin 2 → StdSpace ι) :
    extDeriv (stdConnectionForm ι) x v = -(2 * Real.pi) * stdForm ι (v 0) (v 1) := by
  rw [stdConnectionForm_def, ContinuousLinearMap.extDeriv_liouvilleFormCLM_apply_of_skew _
    two_ne_zero (fun v w ↦ by
      simp only [_root_.smul_apply, LinearMap.toContinuousBilinearMap_apply,
        smul_eq_mul, ← mul_neg]
      exact congrArg _ ((stdForm ι).neg_eq w v).symm)]
  simp only [_root_.smul_apply, LinearMap.toContinuousBilinearMap_apply,
    smul_eq_mul]

/-- The model connection form is a smooth one-form on `StdSpace ι`. -/
theorem contDiff_stdConnectionForm {n : WithTop ℕ∞} :
    ContDiff ℝ n (stdConnectionForm ι : StdSpace ι → StdSpace ι [⋀^Fin 1]→L[ℝ] ℝ) :=
  (stdConnectionForm ι).contDiff

/-- **Gauge to the model connection form, flat version.** Let `b` be a one-form on `StdSpace ι`,
`Cʳ` (`r ≥ 1`) on an open set `s` that is star-convex with respect to some point, with
`db = -2π ω₀` on `s`. Then there is a function `θ`, `Cʳ⁺¹` on `s`, with `dθ = A₀ - b` on `s`,
where `A₀` is `SymplecticGeometry.stdConnectionForm ι`. -/
theorem exists_contDiffOn_fderiv_apply_eq_stdConnectionForm_sub
    {b : StdSpace ι → StdSpace ι [⋀^Fin 1]→L[ℝ] ℝ} {s : Set (StdSpace ι)} {x₀ : StdSpace ι}
    (hs : StarConvex ℝ x₀ s) (hso : IsOpen s) {r : ℕ∞} (hr : 1 ≤ r) (hb : ContDiffOn ℝ r b s)
    (hdb : ∀ x ∈ s, ∀ v : Fin 2 → StdSpace ι,
      extDeriv b x v = -(2 * Real.pi) * stdForm ι (v 0) (v 1)) :
    ∃ θ : StdSpace ι → ℝ, ContDiffOn ℝ (r + 1) θ s ∧
      ∀ x ∈ s, ∀ v : Fin 1 → StdSpace ι,
        fderiv ℝ θ x (v 0) = stdConnectionForm ι x v - b x v := by
  have hr' : (r : WithTop ℕ∞) ≠ 0 := (lt_of_lt_of_le zero_lt_one (by exact_mod_cast hr)).ne'
  -- `A₀ - b` is the one-form of a covector field `L`, which is closed.
  set e := ofSubsingletonLIE (𝕜 := ℝ) (E := StdSpace ι) (F := ℝ) (0 : Fin 1)
  set L : StdSpace ι → StdSpace ι →L[ℝ] ℝ := fun y ↦ e.symm ((⇑(stdConnectionForm ι) - b) y)
  have heL : (fun y ↦ e (L y)) = ⇑(stdConnectionForm ι) - b :=
    funext fun y ↦ e.apply_symm_apply _
  have hL : ContDiffOn ℝ r L s :=
    e.symm.contDiff.comp_contDiffOn ((contDiff_stdConnectionForm (ι := ι)).contDiffOn.sub hb)
  have hdL : ∀ c ∈ s, extDeriv (fun y ↦ e (L y)) c = 0 := by
    intro c hc
    have hbc : DifferentiableAt ℝ b c :=
      (hb.differentiableOn hr' c hc).differentiableAt (hso.mem_nhds hc)
    rw [heL, extDeriv_sub (stdConnectionForm ι).differentiableAt hbc]
    ext v
    rw [ContinuousAlternatingMap.sub_apply, extDeriv_stdConnectionForm_apply, hdb c hc v,
      sub_self]
    simp
  obtain ⟨θ, hθ, hθL⟩ :=
    hs.exists_contDiffOn_forall_hasFDerivAt_of_extDeriv_eq_zero hso hr hL hdL
  refine ⟨θ, hθ, fun x hx v ↦ ?_⟩
  have hv := DFunLike.congr_fun (congrFun heL x) v
  rw [← (hθL x hx).fderiv] at hv
  simpa [e] using hv

/-- **Gauge to the model connection form.** Let `β` be a one-form on `StdSpace ι` that is `Cʳ`,
`r ≥ 1`, on an open set `s`, star-convex with respect to some point, with `dβ = -2π ω₀` on `s`.
Then there is a function `θ`, `Cʳ⁺¹` on `s`, with `β + dθ = A₀` on `s`, where `A₀` is
`SymplecticGeometry.stdConnectionForm ι`. -/
theorem exists_contDiffOn_add_mextDeriv_eq_stdConnectionForm
    {β : RoughForm 𝓘(ℝ, StdSpace ι) (StdSpace ι) ℝ 1} {s : Set (StdSpace ι)} {x₀ : StdSpace ι}
    (hs : StarConvex ℝ x₀ s) (hso : IsOpen s) {r : ℕ∞} (hr : 1 ≤ r)
    (hβ : ContDiffOn ℝ (E := StdSpace ι) (F := StdSpace ι [⋀^Fin 1]→L[ℝ] ℝ) r β s)
    (hdβ : ∀ x ∈ s, ∀ v : Fin 2 → StdSpace ι,
      mextDeriv β x v = -(2 * Real.pi) * stdForm ι (v 0) (v 1)) :
    ∃ θ : StdSpace ι → ℝ, ContDiffOn ℝ (r + 1) θ s ∧
      ∀ x ∈ s, β x + mextDeriv (RoughForm.ofFunction 𝓘(ℝ, StdSpace ι) θ) x =
        stdConnectionForm ι x := by
  obtain ⟨θ, hθ, hθβ⟩ := exists_contDiffOn_fderiv_apply_eq_stdConnectionForm_sub hs hso hr hβ
    fun x hx v ↦ (DFunLike.congr_fun (mextDeriv_eq_extDeriv β x) v).symm.trans (hdβ x hx v)
  refine ⟨θ, hθ, fun x hx ↦ ?_⟩
  ext v
  refine (ContinuousAlternatingMap.add_apply _ _ v).trans ?_
  have hv0 : v = ![v 0] := funext fun i ↦ by rw [Subsingleton.elim i 0, Matrix.cons_val_zero]
  rw [hv0, mextDeriv_ofFunction_apply, mfderiv_eq_fderiv, ← hv0]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearEquiv.coe_coe,
    NormedSpace.fromTangentSpace_apply, NormedSpace.fromTangentSpace_symm_apply, hθβ x hx v]
  exact add_sub_cancel _ _

end SymplecticGeometry

end
