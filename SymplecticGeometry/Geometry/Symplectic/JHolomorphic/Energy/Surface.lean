/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Smooth
public import SymplecticGeometry.Geometry.Symplectic.JHolomorphic.Energy.Density

/-!
# The energy form of a map from an almost complex surface

Let `(C, j)` be an almost complex surface, and let `M` be a manifold with a two-form `ω` (`form`
in the code) and an almost complex structure `J`. The energy form of a map `u : C → M` is the
rough two-form on `C` whose value at `c` is the energy density `ε_{du_c}` of the derivative of `u`
at `c` (`TauCeti.SmoothTwoForm.energyForm`, with the densities of
`SymplecticGeometry.Geometry.Symplectic.JHolomorphic.Energy.Density`). The energy of `u` will be
the integral of this top form over `C`; it involves no area form on `C`.

## Main results

* `TauCeti.SmoothTwoForm.isSmoothForm_energyForm`: for a `C¹` map `u`, the energy form is a
  continuous form (`IsSmoothForm I' 0`).

The proof reads the form on the frame fields of a tangent trivialization of `C`, as Tau Ceti's
`TauCeti.isSmoothForm_iff_forall_contMDiffAt_trivializationAt_apply` allows. By the four-term
formula `TauCeti.SmoothTwoForm.energyDensity_apply`, each value is a combination of values of `ω`
along `u` on tangent fields built from the frame fields by applying `j`, the tangent map of `u`
(continuous for a `C¹` map, Mathlib's `ContMDiff.contMDiff_tangentMap`) and `J`, and such values are
continuous at a point by `TauCeti.SmoothForm.contMDiffAt_apply`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §4.5,
  equation (4.5.4).
* [C. Wendl, *Lectures on Holomorphic Curves in Symplectic and Contact Geometry*][Wendl2010],
  Definition 2.18.
-/

public section

open Bundle
open scoped Manifold ContDiff

noncomputable section

namespace TauCeti

namespace SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' H' C : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace C]
  [ChartedSpace H' C] [IsManifold I' ∞ C]

variable (form : SmoothTwoForm I M) (J : SmoothAlmostComplexStructure I M)
  (j : SmoothAlmostComplexStructure I' C)

/-- The energy form of a map `u : C → M` from the almost complex surface `(C, j)`: the rough
two-form on `C` whose value at `c` is the energy density `ε_{du_c}` (`energyDensity`) of the
derivative `du_c : T_c C → T_{u c} M`. It is defined for every `form` and `J`, and involves no
area form on `C`. -/
def energyForm (u : C → M) : RoughForm I' C ℝ 2 :=
  fun c ↦ form.energyDensity J j (mfderiv I' I u c).toLinearMap

/-- The value of the energy form at `c` is the energy density of `du_c`. -/
theorem energyForm_apply (u : C → M) (c : C) :
    form.energyForm J j u c = form.energyDensity J j (mfderiv I' I u c).toLinearMap :=
  (rfl)

/-- The energy form of a constant map vanishes. -/
@[simp]
theorem energyForm_const (x : M) : form.energyForm J j (fun _ : C ↦ x) = 0 := by
  ext c v
  simp [energyForm_apply]

/-- The energy form of a `C¹` map `u : C → M` is a continuous form on `C`. -/
theorem isSmoothForm_energyForm {u : C → M} (hu : ContMDiff I' I 1 u) :
    IsSmoothForm I' 0 (form.energyForm J j u) := by
  rw [isSmoothForm_iff_forall_contMDiffAt_trivializationAt_apply]
  intro c₀ v
  set e := trivializationAt E' (TangentSpace I') c₀
  have hc₀ : c₀ ∈ e.baseSet := mem_baseSet_trivializationAt E' (TangentSpace I') c₀
  have hu₀ : ContMDiffAt I' I 0 u c₀ := (hu c₀).of_le zero_le_one
  -- the frame fields of the trivialization, and their images under `j`
  have hW (i : Fin 2) : ContMDiffAt I' I'.tangent 0
      (fun y ↦ TotalSpace.mk' E' y (e.symmL ℝ y (v i))) c₀ :=
    (e.contMDiffAt_symmL hc₀).clm_bundle_apply
      (by rw [contMDiffAt_section_iff]; exact contMDiffAt_const)
  have hjW (i : Fin 2) : ContMDiffAt I' I'.tangent 0
      (fun y ↦ TotalSpace.mk' E' y (j y (e.symmL ℝ y (v i)))) c₀ :=
    ((j.toEndomorphism.contMDiff c₀).of_le (by simp)).clm_bundle_apply (hW i)
  -- pushing a continuous field forward by `du`, and then applying `J`
  have hdu {X : (y : C) → TangentSpace I' y}
      (hX : ContMDiffAt I' I'.tangent 0 (fun y ↦ TotalSpace.mk' E' y (X y)) c₀) :
      ContMDiffAt I' I.tangent 0
        (fun y ↦ TotalSpace.mk' E (u y) (mfderiv I' I u y (X y))) c₀ :=
    (hu.contMDiff_tangentMap (by simp) _).comp c₀ hX
  have hJ {X : (y : C) → TangentSpace I (u y)}
      (hX : ContMDiffAt I' I.tangent 0 (fun y ↦ TotalSpace.mk' E (u y) (X y)) c₀) :
      ContMDiffAt I' I.tangent 0 (fun y ↦ TotalSpace.mk' E (u y) (J (u y) (X y))) c₀ :=
    (((J.toEndomorphism.contMDiff (u c₀)).of_le (by simp)).comp c₀ hu₀).clm_bundle_apply hX
  -- evaluating `form` along `u` on two continuous fields
  have hev {X Y : (y : C) → TangentSpace I (u y)}
      (hX : ContMDiffAt I' I.tangent 0 (fun y ↦ TotalSpace.mk' E (u y) (X y)) c₀)
      (hY : ContMDiffAt I' I.tangent 0 (fun y ↦ TotalSpace.mk' E (u y) (Y y)) c₀) :
      ContMDiffAt I' 𝓘(ℝ, ℝ) 0 (fun y ↦ form.val (u y) ![X y, Y y]) c₀ := by
    simpa only [SmoothBundleForm.eval₂_apply] using form.contMDiffAt_apply hX hY
  have hfr (y : C) : e.symmL ℝ y ∘ v = ![e.symmL ℝ y (v 0), e.symmL ℝ y (v 1)] := by
    ext i; fin_cases i <;> simp
  refine ((contMDiffAt_const (c := (4⁻¹ : ℝ))).mul ((((hev (hdu (hjW 0)) (hJ (hdu (hW 1)))).add
    (hev (hdu (hW 1)) (hJ (hdu (hjW 0))))).sub (hev (hdu (hW 0)) (hJ (hdu (hjW 1))))).sub
    (hev (hdu (hjW 1)) (hJ (hdu (hW 0)))))).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun y ↦ ?_)
  simp only [Pi.add_apply, Pi.mul_apply]
  rw [energyForm_apply, hfr, energyDensity_apply]
  simp only [ContinuousLinearMap.coe_coe]

end SmoothTwoForm

end TauCeti

end
