/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Dolbeault.DC
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import TauCeti.Geometry.Symplectic.Manifold.JHolomorphic
public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Leibniz
public import TauCeti.Geometry.Manifold.Complex.DdbarForm.DC
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Smooth
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Wedge.Smooth.FunSMul
public import SymplecticGeometry.Topology.Algebra.Module.Alternating.Basic

/-!
# Real potentials and `∂∂bar`

Let `J` be a smooth almost complex structure on `M` and `f` a smooth real function, seen as a
complex-valued `0`-form through `SmoothForm.mapCoeff Complex.ofRealCLM`. With Tau Ceti's
normalization `dᶜ = i (∂bar - ∂)`, the form `dᶜ f` is real: it is `-df ∘ J`, that is,
`J.covectorComplexStructure (d f)`. Wherever `d = ∂ + ∂bar` on one-forms, in particular when
the Nijenhuis tensor of `J` vanishes or `J` comes from a complex manifold, `ddᶜ = 2i ∂∂bar`
turns this into `(i/2) ∂∂bar f = (1/4) d (J.covectorComplexStructure (d f))`. So the form
`(i/2) ∂∂bar f` of a real potential `f` is the complexification of a real exact two-form.

Write `λ_f = -df ∘ J` and `ω_f = d λ_f`. The map `a ↦ -a ∘ J` is linear over smooth functions,
so the chain rule and the Leibniz rule give `λ_f` and `ω_f` of a composite `g ∘ f` with
`g : ℝ → ℝ`: `λ_{g ∘ f} = g'(f) λ_f` and `ω_{g ∘ f} = g'(f) ω_f + g''(f) df ∧ λ_f`. On a
complex manifold, `ω_f` is twice Tau Ceti's real (1,1)-form `TauCeti.ddbarForm V u`, for the
function `u` underlying `f`.

## Main declarations

In the namespace `TauCeti.SmoothAlmostComplexStructure`:

* `dC_mapCoeff_ofReal`: `dᶜ f = -df ∘ J`, for every almost complex structure.
* `del_delBar_mapCoeff_ofReal_of_mextDerivₗ_eq_del_add_delBar`:
  `(i/2) ∂∂bar f = (1/4) d (J.covectorComplexStructure (d f))` wherever `d = ∂ + ∂bar` on
  one-forms.
* `del_delBar_mapCoeff_ofReal_of_nijenhuis_eq_zero`,
  `del_delBar_mapCoeff_ofReal_ofComplexManifold`: the same when `N_J = 0`, and on a complex
  manifold.
* `covectorComplexStructure_funSMulₗ`: `a ↦ -a ∘ J` commutes with multiplication by smooth
  functions.
* `covectorComplexStructure_mextDerivₗ_ofFunction_comp_of_hasDerivAt`,
  `mextDerivₗ_covectorComplexStructure_mextDerivₗ_ofFunction_comp_of_hasDerivAt`: `λ_{g ∘ f}`
  and `ω_{g ∘ f}`.
* `mpullback_covectorComplexStructure`: `a ↦ -a ∘ J` commutes with pull-back along
  pseudoholomorphic maps, so a potential `f` of `(1/4) d (J* df)` pulls back to the potential
  `f ∘ φ` of the pulled-back form.

The `∂∂bar` identities follow the pattern of Tau Ceti's `Dolbeault/DC.lean`, whose
`mextDerivₗ_dC_of_mextDerivₗ_eq_del_add_delBar` (`ddᶜ = 2i ∂∂bar`) they use, with hypotheses
`d = ∂ + ∂bar` and a corollary for complex manifolds as in `mextDerivₗ_dC_ofComplexManifold`.

In the namespace `TauCeti`:

* `SmoothAlmostComplexStructure.covectorComplexStructure_ofComplexManifold_mextDerivₗ_apply`: on
  a complex manifold, the value of `-df ∘ J` on `v` at `x` is `-df_x(i v)`.
* `coe_mextDerivₗ_covectorComplexStructure_eq_two_smul_ddbarForm`: on a complex manifold,
  `ω_f = 2 • TauCeti.ddbarForm V u`, for the function `u` underlying `f`, from
  `dC_mapCoeff_ofReal` and Tau Ceti's `ddbarForm_apply_eq_inv_two_smul_mextDerivₗ_dC_apply`.

## References

* Daniel Huybrechts, *Complex Geometry: An Introduction*, Sections 1.3 and 3.1.
* [K. Cieliebak, Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  Chapter 2, for the forms `λ_f` and `ω_f` of a composite.
-/

public section

noncomputable section

open scoped Manifold ContDiff

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

namespace SmoothAlmostComplexStructure

variable (J : SmoothAlmostComplexStructure I M)

/-- For a real function `f`, `dᶜ f = -df ∘ J`: the operator `dᶜ = i (∂bar - ∂)` sends the
complexification of `f` to the complexification of the real one-form
`J.covectorComplexStructure (d f)`. No integrability of `J` is needed. -/
theorem dC_mapCoeff_ofReal (f : SmoothForm I M ℝ 0) :
    J.dC (SmoothForm.mapCoeff Complex.ofRealCLM f) =
      SmoothForm.mapCoeff Complex.ofRealCLM (J.covectorComplexStructure (mextDerivₗ I 0 f)) := by
  refine Subtype.ext <| funext fun x ↦ ?_
  refine sub_eq_zero.1 <| (ContinuousAlternatingMap.eq_zero_iff_forall_apply_fin_one _).2
    fun v ↦ ?_
  rw [ContinuousAlternatingMap.sub_apply, sub_eq_zero, J.dC_apply_apply, ← mextDerivₗ_zero_apply,
    SmoothForm.mextDerivₗ_mapCoeff]
  simp

variable {J}

/-- For a real function `f`, if `d = ∂ + ∂bar` on complex one-forms, then
`(i/2) ∂∂bar f = (1/4) d (J.covectorComplexStructure (d f))`: the left side is the
complexification of the real two-form on the right. -/
theorem del_delBar_mapCoeff_ofReal_of_mextDerivₗ_eq_del_add_delBar
    (hd : ∀ φ : SmoothForm I M ℂ 1, mextDerivₗ I 1 φ = J.del φ + J.delBar φ)
    (f : SmoothForm I M ℝ 0) :
    (Complex.I / 2) • J.del (J.delBar (SmoothForm.mapCoeff Complex.ofRealCLM f)) =
      SmoothForm.mapCoeff Complex.ofRealCLM
        ((4 : ℝ)⁻¹ • mextDerivₗ I 1 (J.covectorComplexStructure (mextDerivₗ I 0 f))) := by
  have h := mextDerivₗ_dC_of_mextDerivₗ_eq_del_add_delBar
    (fun φ ↦ (J.del_add_delBar_eq_mextDerivₗ φ).symm) hd
    (SmoothForm.mapCoeff Complex.ofRealCLM f)
  rw [dC_mapCoeff_ofReal, SmoothForm.mextDerivₗ_mapCoeff] at h
  rw [map_smul, h]
  module

/-- For a real function `f`, if the Nijenhuis tensor of `J` vanishes, then
`(i/2) ∂∂bar f = (1/4) d (J.covectorComplexStructure (d f))`: the left side is the
complexification of the real two-form on the right. -/
theorem del_delBar_mapCoeff_ofReal_of_nijenhuis_eq_zero [FiniteDimensional ℝ E]
    (hJ : J.nijenhuis = 0)
    (f : SmoothForm I M ℝ 0) :
    (Complex.I / 2) • J.del (J.delBar (SmoothForm.mapCoeff Complex.ofRealCLM f)) =
      SmoothForm.mapCoeff Complex.ofRealCLM
        ((4 : ℝ)⁻¹ • mextDerivₗ I 1 (J.covectorComplexStructure (mextDerivₗ I 0 f))) :=
  del_delBar_mapCoeff_ofReal_of_mextDerivₗ_eq_del_add_delBar
    (J.mextDerivₗ_eq_del_add_delBar_of_nijenhuis_eq_zero hJ) f

/-! ### The primitive `-df ∘ J` and its derivative under composition -/

/-- The almost complex structure `a ↦ -a ∘ J` on real one-forms is linear over smooth functions:
it commutes with multiplication by a smooth function `g`. -/
@[simp]
theorem covectorComplexStructure_funSMulₗ (g : C^∞⟮I, M; ℝ⟯) (a : SmoothForm I M ℝ 1) :
    J.covectorComplexStructure (SmoothForm.funSMulₗ g a) =
      SmoothForm.funSMulₗ g (J.covectorComplexStructure a) := by
  refine Subtype.ext <| funext fun x ↦ ContinuousAlternatingMap.ext_fin_one fun v ↦ ?_
  simp [SmoothForm.coe_funSMulₗ]

/-- **The primitive `-dh ∘ J` of a composite.** If `h = g ∘ f` for a smooth real function `f`
and a function `g : ℝ → ℝ` with derivative `g' x` at `f x` for every `x`, then
`-dh ∘ J = g' (-df ∘ J)`. -/
theorem covectorComplexStructure_mextDerivₗ_ofFunction_comp_of_hasDerivAt {g : ℝ → ℝ}
    {f h g' : C^∞⟮I, M; ℝ⟯} (hh : ∀ x, h x = g (f x)) (hg : ∀ x, HasDerivAt g (g' x) (f x)) :
    J.covectorComplexStructure (mextDerivₗ I 0 (SmoothForm.ofFunction h)) =
      SmoothForm.funSMulₗ g'
        (J.covectorComplexStructure (mextDerivₗ I 0 (SmoothForm.ofFunction f))) := by
  rw [SmoothForm.mextDerivₗ_ofFunction_comp_of_hasDerivAt hh hg,
    covectorComplexStructure_funSMulₗ]

/-- **The form `d(-dh ∘ J)` of a composite.** Let `h = g ∘ f` for a smooth real function `f` and
a function `g : ℝ → ℝ` whose derivative at `f x` is `g' (f x)`, and the derivative of `g'` at
`f x` is `g'' (f x)`, for every `x`. If the smooth functions `a` and `b` are `g' ∘ f` and
`g'' ∘ f`, then `d(-dh ∘ J) = a d(-df ∘ J) + b (df ∧ (-df ∘ J))`, the wedge being Tau Ceti's
`SmoothForm.extDerivWedgeₗ f`. -/
theorem mextDerivₗ_covectorComplexStructure_mextDerivₗ_ofFunction_comp_of_hasDerivAt
    {g g' g'' : ℝ → ℝ} {f h a b : C^∞⟮I, M; ℝ⟯} (hh : ∀ x, h x = g (f x))
    (ha : ∀ x, a x = g' (f x)) (hb : ∀ x, b x = g'' (f x))
    (hg : ∀ x, HasDerivAt g (g' (f x)) (f x)) (hg' : ∀ x, HasDerivAt g' (g'' (f x)) (f x)) :
    mextDerivₗ I 1 (J.covectorComplexStructure (mextDerivₗ I 0 (SmoothForm.ofFunction h))) =
      SmoothForm.funSMulₗ a (mextDerivₗ I 1
          (J.covectorComplexStructure (mextDerivₗ I 0 (SmoothForm.ofFunction f)))) +
        SmoothForm.funSMulₗ b (SmoothForm.extDerivWedgeₗ f 1
          (J.covectorComplexStructure (mextDerivₗ I 0 (SmoothForm.ofFunction f)))) := by
  have hda := SmoothForm.mextDerivₗ_ofFunction_comp_of_hasDerivAt (g' := b) ha
    fun x ↦ hb x ▸ hg' x
  rw [covectorComplexStructure_mextDerivₗ_ofFunction_comp_of_hasDerivAt (g' := a) hh
      fun x ↦ ha x ▸ hg x,
    SmoothForm.mextDerivₗ_funSMulₗ, add_comm (SmoothForm.extDerivWedgeₗ _ _ _)]
  congr 1
  -- `d a ∧ λ = (b df) ∧ λ = b (df ∧ λ)`.
  rw [SmoothForm.extDerivWedgeₗ_def, SmoothForm.extDerivWedgeₗ_def, hda,
    SmoothForm.wedge_funSMulₗ_left]
  ext x v
  simp [SmoothForm.coe_funSMulₗ]

section Pullback

variable {E' H' M' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']
  {J' : SmoothAlmostComplexStructure I' M'}

/-- The almost complex structure `a ↦ -a ∘ J` on real one-forms is natural for pseudoholomorphic
maps: if `f` intertwines `J` and `J'`, the pull-back of `J'.covectorComplexStructure a` is
`J.covectorComplexStructure` of the pull-back of `a`. -/
theorem mpullback_covectorComplexStructure {f : M → M'} (hf : ContMDiff I I' ∞ f)
    (hJ : IsPseudoholomorphic J J' f) (a : SmoothForm I' M' ℝ 1) :
    SmoothForm.mpullback f hf (J'.covectorComplexStructure a) =
      J.covectorComplexStructure (SmoothForm.mpullback f hf a) := by
  refine Subtype.ext <| funext fun x ↦ ?_
  refine sub_eq_zero.1 <| (ContinuousAlternatingMap.eq_zero_iff_forall_apply_fin_one _).2
    fun v ↦ ?_
  rw [ContinuousAlternatingMap.sub_apply, sub_eq_zero, SmoothForm.mpullback_apply_one,
    covectorComplexStructure_apply_vec, covectorComplexStructure_apply_vec,
    SmoothForm.mpullback_apply_one, (hJ.isPseudoholomorphicAt x).mfderiv_apply_commute]

end Pullback
end SmoothAlmostComplexStructure

section ComplexManifold

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  {N : Type*} [TopologicalSpace N] [ChartedSpace V N] [IsManifold 𝓘(ℂ, V) ∞ N]

open scoped TauCeti.ComplexManifold
open SmoothAlmostComplexStructure

/-- On a complex manifold, the value of `-df ∘ J` on `v` at `x` is `-df_x(i v)`, for a smooth
real function `f`. -/
theorem SmoothAlmostComplexStructure.covectorComplexStructure_ofComplexManifold_mextDerivₗ_apply
    (f : C^∞⟮𝓘(ℝ, V), N; ℝ⟯) (x : N) (v : V) :
    ((ofComplexManifold V N).covectorComplexStructure
        (mextDerivₗ 𝓘(ℝ, V) 0 (SmoothForm.ofFunction f))).val x ![v] =
      -mvfderiv 𝓘(ℝ, V) f x (Complex.I • v) := by
  refine (covectorComplexStructure_apply_vec _ _ x v).trans ?_
  rw [mextDerivₗ_zero_apply, SmoothForm.ofFunction_apply_zero]
  exact congrArg (fun w ↦ -mvfderiv 𝓘(ℝ, V) f x w) (ofComplexManifold_apply (E := V) x v)

/-- On a complex manifold, for a real function `f`,
`(i/2) ∂∂bar f = (1/4) d (J.covectorComplexStructure (d f))`: the left side is the
complexification of the real two-form on the right. -/
theorem SmoothAlmostComplexStructure.del_delBar_mapCoeff_ofReal_ofComplexManifold
    (f : SmoothForm 𝓘(ℝ, V) N ℝ 0) :
    (Complex.I / 2) • (ofComplexManifold V N).del
        ((ofComplexManifold V N).delBar (SmoothForm.mapCoeff Complex.ofRealCLM f)) =
      SmoothForm.mapCoeff Complex.ofRealCLM ((4 : ℝ)⁻¹ • mextDerivₗ 𝓘(ℝ, V) 1
        ((ofComplexManifold V N).covectorComplexStructure (mextDerivₗ 𝓘(ℝ, V) 0 f))) :=
  del_delBar_mapCoeff_ofReal_of_mextDerivₗ_eq_del_add_delBar
    mextDerivₗ_eq_del_add_delBar_ofComplexManifold f

/-- On a complex manifold, for a real function `u` given by the smooth `0`-form `f`, the
exterior derivative of `-df ∘ J` is twice Tau Ceti's real (1,1)-form `TauCeti.ddbarForm V u`,
that is, `2 i∂∂bar u`. -/
theorem coe_mextDerivₗ_covectorComplexStructure_eq_two_smul_ddbarForm {u : N → ℝ}
    (f : SmoothForm 𝓘(ℝ, V) N ℝ 0) (hf : ∀ y, f.val y 0 = u y) :
    (mextDerivₗ 𝓘(ℝ, V) 1
        ((ofComplexManifold V N).covectorComplexStructure (mextDerivₗ 𝓘(ℝ, V) 0 f))).val =
      (2 : ℝ) • ddbarForm V u := by
  refine funext fun x ↦ ContinuousAlternatingMap.ext_fin_two fun v w ↦ Complex.ofReal_injective ?_
  have key := ddbarForm_apply_eq_inv_two_smul_mextDerivₗ_dC_apply (u := u)
    (SmoothForm.mapCoeff Complex.ofRealCLM f) (fun y ↦ by
      rw [SmoothForm.coe_mapCoeff, RoughForm.mapCoeff_apply, hf, Complex.ofRealCLM_apply])
    x v w
  rw [dC_mapCoeff_ofReal, SmoothForm.mextDerivₗ_mapCoeff, SmoothForm.coe_mapCoeff,
    RoughForm.mapCoeff_apply] at key
  rw [Pi.smul_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul, Complex.ofReal_mul, key]
  simp

end ComplexManifold

end TauCeti

end
