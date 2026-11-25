/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Dolbeault.DC
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import TauCeti.Geometry.Symplectic.Manifold.JHolomorphic

/-!
# Real potentials and `∂∂bar`

Let `J` be a smooth almost complex structure on `M` and `f` a smooth real function, seen as a
complex-valued `0`-form through `SmoothForm.mapCoeff Complex.ofRealCLM`. With Tau Ceti's
normalization `dᶜ = i (∂bar - ∂)`, the form `dᶜ f` is real: it is `-df ∘ J`, that is,
`J.covectorComplexStructure (d f)`. Wherever `d = ∂ + ∂bar` on one-forms, in particular when
the Nijenhuis tensor of `J` vanishes or `J` comes from a complex manifold, `ddᶜ = 2i ∂∂bar`
turns this into `(i/2) ∂∂bar f = (1/4) d (J.covectorComplexStructure (d f))`. So the form
`(i/2) ∂∂bar f` of a real potential `f` is the complexification of a real exact two-form.

## Main declarations

In the namespace `TauCeti.SmoothAlmostComplexStructure`:

* `dC_mapCoeff_ofReal`: `dᶜ f = -df ∘ J`, for every almost complex structure.
* `del_delBar_mapCoeff_ofReal_of_mextDerivₗ_eq_del_add_delBar`:
  `(i/2) ∂∂bar f = (1/4) d (J.covectorComplexStructure (d f))` wherever `d = ∂ + ∂bar` on
  one-forms.
* `del_delBar_mapCoeff_ofReal_of_nijenhuis_eq_zero`,
  `del_delBar_mapCoeff_ofReal_ofComplexManifold`: the same when `N_J = 0`, and on a complex
  manifold.
* `mpullback_covectorComplexStructure`: `a ↦ -a ∘ J` commutes with pull-back along
  pseudoholomorphic maps, so a potential `f` of `(1/4) d (J* df)` pulls back to the potential
  `f ∘ φ` of the pulled-back form.

These follow the pattern of Tau Ceti's `Dolbeault/DC.lean`, whose
`mextDerivₗ_dC_of_mextDerivₗ_eq_del_add_delBar` (`ddᶜ = 2i ∂∂bar`) they use, with hypotheses
`d = ∂ + ∂bar` and a corollary for complex manifolds as in `mextDerivₗ_dC_ofComplexManifold`.

## References

* Daniel Huybrechts, *Complex Geometry: An Introduction*, Sections 1.3 and 3.1.
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

end ComplexManifold

end TauCeti

end
