/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Closed
public import TauCeti.Geometry.Manifold.DifferentialForm.Dolbeault.DC
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import TauCeti.Geometry.Symplectic.Manifold.JHolomorphic
public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Leibniz
public import TauCeti.Geometry.Manifold.Complex.DdbarForm.DC
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.AlmostComplexType
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.DegreeOne
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Smooth
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Wedge.Smooth.FunSMul
import SymplecticGeometry.Topology.Algebra.Module.Alternating.Basic

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
* `potentialForm`: the real two-form `J.potentialForm f = (1/4) d (J.covectorComplexStructure
  (d f))` of a potential `f`, closed and `ℝ`-linear in `f`.
* `del_delBar_mapCoeff_ofReal_of_mextDerivₗ_eq_del_add_delBar`:
  `(i/2) ∂∂bar f` is the complexification of `J.potentialForm f` wherever `d = ∂ + ∂bar` on
  one-forms.
* `del_delBar_mapCoeff_ofReal_of_nijenhuis_eq_zero`,
  `del_delBar_mapCoeff_ofReal_ofComplexManifold`: the same when `N_J = 0`, and on a complex
  manifold.
* `covectorComplexStructure_funSMulₗ`: `a ↦ -a ∘ J` commutes with multiplication by smooth
  functions, the degree-one case of the library's
  `ContMDiffSection.realAlternatingDerivation_funSMulₗ`.
* `covectorComplexStructure_mextDerivₗ_ofFunction_comp_of_hasDerivAt`,
  `mextDerivₗ_covectorComplexStructure_mextDerivₗ_ofFunction_comp_of_hasDerivAt`: `λ_{g ∘ f}`
  and `ω_{g ∘ f}`.
* `mpullback_covectorComplexStructure`: `a ↦ -a ∘ J` commutes with pull-back along
  pseudoholomorphic maps, so that (`mpullback_potentialForm`) the pull-back of
  `J'.potentialForm f` along a pseudoholomorphic `φ` is `J.potentialForm (f ∘ φ)`.

The `∂∂bar` identities follow the pattern of Tau Ceti's `Dolbeault/DC.lean`, whose
`mextDerivₗ_dC_of_mextDerivₗ_eq_del_add_delBar` (`ddᶜ = 2i ∂∂bar`) they use, with hypotheses
`d = ∂ + ∂bar` and a corollary for complex manifolds as in `mextDerivₗ_dC_ofComplexManifold`.

In the namespace `TauCeti`:

* `SmoothAlmostComplexStructure.covectorComplexStructure_ofComplexManifold_mextDerivₗ_apply`: on
  a complex manifold, the value of `-df ∘ J` on `v` at `x` is `-df_x(i v)`.
* `coe_mextDerivₗ_covectorComplexStructure_eq_two_smul_ddbarForm`: on a complex manifold,
  `ω_f = 2 • TauCeti.ddbarForm V u`, for the function `u` underlying `f`, from
  `dC_mapCoeff_ofReal` and Tau Ceti's `ddbarForm_apply_eq_inv_two_smul_mextDerivₗ_dC_apply`;
  hence `SmoothAlmostComplexStructure.coe_potentialForm_eq_inv_two_smul_ddbarForm`: the form of a
  potential `u` is `(1/2) • TauCeti.ddbarForm V u`.

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
  refine SmoothBundleForm.ext_fin_one fun x v ↦ ?_
  rw [J.dC_apply_apply, ← mextDerivₗ_zero_apply, SmoothForm.mextDerivₗ_mapCoeff]
  simp

/-- The form `(1/4) d (J* d f)` of a real potential `f`, where `J*` is the almost complex
structure `a ↦ -a ∘ J` on real one-forms. Wherever `d = ∂ + ∂bar` on one-forms, its
complexification is `(i/2) ∂∂bar f`
(`del_delBar_mapCoeff_ofReal_of_mextDerivₗ_eq_del_add_delBar`). It is `ℝ`-linear in `f`. -/
noncomputable def potentialForm : SmoothForm I M ℝ 0 →ₗ[ℝ] SmoothForm I M ℝ 2 :=
  (4 : ℝ)⁻¹ • (mextDerivₗ I 1 ∘ₗ J.covectorComplexStructure.toLinearMap ∘ₗ mextDerivₗ I 0)

theorem potentialForm_def (f : SmoothForm I M ℝ 0) :
    J.potentialForm f =
      (4 : ℝ)⁻¹ • mextDerivₗ I 1 (J.covectorComplexStructure (mextDerivₗ I 0 f)) :=
  (rfl)

/-- The form of a potential is closed. -/
theorem isClosed_potentialForm (f : SmoothForm I M ℝ 0) : (J.potentialForm f).IsClosed := by
  rw [potentialForm_def]
  exact (SmoothForm.isClosed_mextDerivₗ _).smul _

variable {J}

/-- For a real function `f`, if `d = ∂ + ∂bar` on complex one-forms, then
`(i/2) ∂∂bar f = (1/4) d (J.covectorComplexStructure (d f))`: the left side is the
complexification of the real two-form `J.potentialForm f`. -/
theorem del_delBar_mapCoeff_ofReal_of_mextDerivₗ_eq_del_add_delBar
    (hd : ∀ φ : SmoothForm I M ℂ 1, mextDerivₗ I 1 φ = J.del φ + J.delBar φ)
    (f : SmoothForm I M ℝ 0) :
    (Complex.I / 2) • J.del (J.delBar (SmoothForm.mapCoeff Complex.ofRealCLM f)) =
      SmoothForm.mapCoeff Complex.ofRealCLM (J.potentialForm f) := by
  have h := mextDerivₗ_dC_of_mextDerivₗ_eq_del_add_delBar
    (fun φ ↦ (J.del_add_delBar_eq_mextDerivₗ φ).symm) hd
    (SmoothForm.mapCoeff Complex.ofRealCLM f)
  rw [dC_mapCoeff_ofReal, SmoothForm.mextDerivₗ_mapCoeff] at h
  rw [potentialForm_def, map_smul, h]
  module

/-- For a real function `f`, if the Nijenhuis tensor of `J` vanishes, then
`(i/2) ∂∂bar f = (1/4) d (J.covectorComplexStructure (d f))`: the left side is the
complexification of the real two-form `J.potentialForm f`. -/
theorem del_delBar_mapCoeff_ofReal_of_nijenhuis_eq_zero [FiniteDimensional ℝ E]
    (hJ : J.nijenhuis = 0)
    (f : SmoothForm I M ℝ 0) :
    (Complex.I / 2) • J.del (J.delBar (SmoothForm.mapCoeff Complex.ofRealCLM f)) =
      SmoothForm.mapCoeff Complex.ofRealCLM (J.potentialForm f) :=
  del_delBar_mapCoeff_ofReal_of_mextDerivₗ_eq_del_add_delBar
    (J.mextDerivₗ_eq_del_add_delBar_of_nijenhuis_eq_zero hJ) f

/-! ### The primitive `-df ∘ J` and its derivative under composition -/

/-- The almost complex structure `a ↦ -a ∘ J` on real one-forms is linear over smooth functions:
it commutes with multiplication by a smooth function `g`. -/
@[simp]
theorem covectorComplexStructure_funSMulₗ (g : C^∞⟮I, M; ℝ⟯) (a : SmoothForm I M ℝ 1) :
    J.covectorComplexStructure (SmoothForm.funSMulₗ g a) =
      SmoothForm.funSMulₗ g (J.covectorComplexStructure a) := by
  rw [covectorComplexStructure_apply, covectorComplexStructure_apply,
    ContMDiffSection.realAlternatingDerivation_funSMulₗ, map_neg]

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
  refine SmoothBundleForm.ext_fin_one fun x v ↦ ?_
  rw [SmoothForm.mpullback_apply_one,
    covectorComplexStructure_apply_vec, covectorComplexStructure_apply_vec,
    SmoothForm.mpullback_apply_one, (hJ.isPseudoholomorphicAt x).mfderiv_apply_commute]

/-- The form of a potential is natural for pseudoholomorphic maps: if `f` intertwines `J` and
`J'`, the pull-back of `J'.potentialForm φ` is `J.potentialForm` of the pulled-back potential
`φ ∘ f`. -/
theorem mpullback_potentialForm {f : M → M'} (hf : ContMDiff I I' ∞ f)
    (hJ : IsPseudoholomorphic J J' f) (φ : SmoothForm I' M' ℝ 0) :
    SmoothForm.mpullback f hf (J'.potentialForm φ) =
      J.potentialForm (SmoothForm.mpullback f hf φ) := by
  rw [potentialForm_def, potentialForm_def, SmoothForm.mpullback_smul,
    ← SmoothForm.mextDerivₗ_mpullback, mpullback_covectorComplexStructure hf hJ,
    ← SmoothForm.mextDerivₗ_mpullback]

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
    (f : C^∞⟮𝓘(ℝ, V), N; ℝ⟯) (x : N) (v : TangentSpace 𝓘(ℝ, V) x) :
    ((ofComplexManifold V N).covectorComplexStructure
        (mextDerivₗ 𝓘(ℝ, V) 0 (SmoothForm.ofFunction f))).val x ![v] =
      -mvfderiv 𝓘(ℝ, V) f x (Complex.I • (show V from v)) := by
  refine (covectorComplexStructure_apply_vec _ _ x v).trans ?_
  rw [mextDerivₗ_zero_apply, SmoothForm.ofFunction_apply_zero]
  exact congrArg (fun w ↦ -mvfderiv 𝓘(ℝ, V) f x w) (ofComplexManifold_apply (E := V) x v)

/-- On a complex manifold, for a real function `f`,
`(i/2) ∂∂bar f = (1/4) d (J.covectorComplexStructure (d f))`: the left side is the
complexification of the real two-form `potentialForm f`. -/
theorem SmoothAlmostComplexStructure.del_delBar_mapCoeff_ofReal_ofComplexManifold
    (f : SmoothForm 𝓘(ℝ, V) N ℝ 0) :
    (Complex.I / 2) • (ofComplexManifold V N).del
        ((ofComplexManifold V N).delBar (SmoothForm.mapCoeff Complex.ofRealCLM f)) =
      SmoothForm.mapCoeff Complex.ofRealCLM ((ofComplexManifold V N).potentialForm f) :=
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

/-- On a complex manifold, the form of a real potential `u`, given by the smooth `0`-form `f`,
is half of Tau Ceti's real (1,1)-form `TauCeti.ddbarForm V u`, that is, `(i/2) ∂∂bar u`. -/
theorem SmoothAlmostComplexStructure.coe_potentialForm_eq_inv_two_smul_ddbarForm
    {u : N → ℝ} (f : SmoothForm 𝓘(ℝ, V) N ℝ 0) (hf : ∀ y, f.val y 0 = u y) :
    ((ofComplexManifold V N).potentialForm f).val = (2 : ℝ)⁻¹ • ddbarForm V u := by
  rw [potentialForm_def, SmoothForm.smul_toRoughForm,
    coe_mextDerivₗ_covectorComplexStructure_eq_two_smul_ddbarForm f hf, smul_smul]
  norm_num

end ComplexManifold

end TauCeti

end
