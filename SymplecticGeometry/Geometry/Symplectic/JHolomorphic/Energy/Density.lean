/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.LinearAlgebra.Complex.EnergyDensity
public import SymplecticGeometry.LinearAlgebra.Complex.StdComplexLine
public import TauCeti.Geometry.Symplectic.Manifold.Energy
public import TauCeti.Topology.Algebra.Module.FiniteDimension

/-!
# Energy densities of maps from almost complex surfaces

Let `(C, j)` be an almost complex surface and `M` a manifold with a two-form `ω` (`form` in the
code) and an almost complex structure `J`. For a linear map `L : T_c C → T_x M`, the integrand of
the energy of a map `u : C → M` at `c` is, when `L = du_c`, the top form on `T_c C`

`ε_L (v, w) = ¼ (b (j v, w) + b (w, j v) - b (v, j w) - b (j w, v))`,
`b (v, w) = ω_x (L v, J_x (L w))`

(`TauCeti.SmoothTwoForm.energyDensity`). It is alternating for every `ω` and `J`, and on a frame
`(e, j e)` it takes the value `½ (ω (L e, J L e) + ω (L j e, J L j e))`, half of Tau Ceti's
`stdComplexLineEnergyDensity` of `(a, s) ↦ L (a e + s j e)`. For an area form `dvol` on `C`, the
squared norm `|L|²` of `L` for the metrics `dvol (·, j ·)` and `ω (·, J ·)`
(`TauCeti.SmoothTwoForm.normSq`) satisfies `|L|² dvol = 2 ε_L` wherever `dvol` does not vanish, so
`½ |du|² dvol` is `ε_{du}` and does not depend on `dvol`.

## Main results

* `TauCeti.SmoothTwoForm.energyDensity_apply_complexFrame`: the value on a frame `(e, j e)`, and
  `energyDensity_apply_complexFrame_eq_stdComplexLineEnergyDensity`, its comparison with Tau
  Ceti's density on the standard complex line.
* `TauCeti.SmoothTwoForm.Tames.energyDensity_apply_complexFrame_nonneg` and
  `Tames.energyDensity_apply_complexFrame_eq_zero_iff`: for `ω` taming `J`, the density is
  nonnegative on frames, and zero on `(e, j e)` exactly when `L e = 0` and `L (j e) = 0`.
* `TauCeti.SmoothTwoForm.normSq_eq`: on a plane, `|L|²` may be computed from any nonzero `e`;
  `normSq_smul_eq_two_smul_energyDensity`: `|L|² dvol = 2 ε_L`.
* `TauCeti.SmoothTwoForm.Invariant.energyDensity_eq_two_smul_add`: for `J`-invariant `ω`,
  `ε_L = 2 ε_{∂̄L} + L^* ω_x`, with `∂̄L = ½ (L + J ∘ L ∘ j)` Tau Ceti's `complexAntilinearPart`.

Apart from the comparison with Tau Ceti's density, these are the statements of
`SymplecticGeometry.LinearAlgebra.Complex.EnergyDensity` for
the form `ω_x`, the complex structures `J_x` and `j_c`, and the area form `dvol_c`
(`TauCeti.SmoothTwoForm.toAlternatingMap_energyDensity`, `TauCeti.SmoothTwoForm.normSq_def`);
this file only reads them on tangent spaces. The statements on a plane take only
`Module.finrank ℝ E' = 2`, not an orientation of `C`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §4.5,
  equation (4.5.4).
* [D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*][McDuffSalamon2012],
  §2.2.
* [C. Wendl, *Lectures on Holomorphic Curves in Symplectic and Contact Geometry*][Wendl2010],
  equation (2.6), Definition 2.18 and Proposition 2.19.
-/

public section

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
  (j : SmoothAlmostComplexStructure I' C) {c : C} {x : M}

/-- The energy density `ε_L` of a linear map `L : T_c C → T_x M` from a tangent space of the
surface `(C, j)` to one of `(M, form, J)`: the top form on `T_c C` given by
`ε_L (v, w) = ¼ (b (j v, w) + b (w, j v) - b (v, j w) - b (j w, v))` with
`b (v, w) = form_x (L v, J_x (L w))`, that is `AlternatingMap.energyDensity` for `form_x`, `J_x`
and `j_c`. On a frame `(e, j e)` it is `½ (form (L e, J (L e)) + form (L (j e), J (L (j e))))`
(`energyDensity_apply_complexFrame`). It is defined for every `form` and `J`, and does not
involve an area form on `C`. -/
def energyDensity (L : TangentSpace I' c →ₗ[ℝ] TangentSpace I x) :
    TangentSpace I' c [⋀^Fin 2]→L[ℝ] ℝ :=
  haveI : FiniteDimensional ℝ (TangentSpace I' c) := inferInstanceAs (FiniteDimensional ℝ E')
  AlternatingMap.toContinuousAlternatingMap <| AlternatingMap.energyDensity
    (form.val x).toAlternatingMap
    (J.almostComplexStructureAt x) (j.almostComplexStructureAt c) L

/-- The energy density is the energy density of the linear map `L` for `form_x`, `J_x` and
`j_c`. -/
theorem toAlternatingMap_energyDensity (L : TangentSpace I' c →ₗ[ℝ] TangentSpace I x) :
    (form.energyDensity J j L).toAlternatingMap = AlternatingMap.energyDensity
      (form.val x).toAlternatingMap
      (J.almostComplexStructureAt x) (j.almostComplexStructureAt c) L := by
  have : FiniteDimensional ℝ (TangentSpace I' c) := inferInstanceAs (FiniteDimensional ℝ E')
  ext v
  rw [ContinuousAlternatingMap.coe_toAlternatingMap, energyDensity,
    AlternatingMap.coe_toContinuousAlternatingMap]

/-- The value of the energy density is that of the energy density of the linear map `L` for
`form_x`, `J_x` and `j_c`. -/
theorem energyDensity_apply_eq (L : TangentSpace I' c →ₗ[ℝ] TangentSpace I x)
    (v : Fin 2 → TangentSpace I' c) :
    form.energyDensity J j L v = AlternatingMap.energyDensity (form.val x).toAlternatingMap
      (J.almostComplexStructureAt x) (j.almostComplexStructureAt c) L v := by
  rw [← toAlternatingMap_energyDensity, ContinuousAlternatingMap.coe_toAlternatingMap]

/-- The energy density on a pair of tangent vectors, by its four-term formula. -/
theorem energyDensity_apply (L : TangentSpace I' c →ₗ[ℝ] TangentSpace I x)
    (v w : TangentSpace I' c) :
    form.energyDensity J j L ![v, w] = 4⁻¹ * (form.val x ![L (j c v), J x (L w)] +
      form.val x ![L w, J x (L (j c v))] - form.val x ![L v, J x (L (j c w))] -
      form.val x ![L (j c w), J x (L v)]) := by
  rw [energyDensity_apply_eq, AlternatingMap.energyDensity_apply]
  simp only [ContinuousAlternatingMap.coe_toAlternatingMap,
    SmoothAlmostComplexStructure.almostComplexStructureAt_apply]

/-- On a frame `(e, j e)`, the energy density is
`½ (form (L e, J (L e)) + form (L (j e), J (L (j e))))`. -/
theorem energyDensity_apply_complexFrame (L : TangentSpace I' c →ₗ[ℝ] TangentSpace I x)
    (e : TangentSpace I' c) :
    form.energyDensity J j L ![e, j c e] = 2⁻¹ * (form.val x ![L e, J x (L e)] +
      form.val x ![L (j c e), J x (L (j c e))]) := by
  rw [energyDensity_apply_eq, ← j.almostComplexStructureAt_apply,
    AlternatingMap.energyDensity_apply_complexFrame]
  simp only [ContinuousAlternatingMap.coe_toAlternatingMap,
    SmoothAlmostComplexStructure.almostComplexStructureAt_apply]

/-- The energy density of the zero map vanishes. -/
@[simp]
theorem energyDensity_zero :
    form.energyDensity J j (0 : TangentSpace I' c →ₗ[ℝ] TangentSpace I x) = 0 := by
  refine ContinuousAlternatingMap.toAlternatingMap_injective ?_
  rw [toAlternatingMap_energyDensity, AlternatingMap.energyDensity_zero,
    ContinuousAlternatingMap.toAlternatingMap_zero]

/-- On a frame `(e, j e)`, the energy density is half of Tau Ceti's energy density
`stdComplexLineEnergyDensity` of the map `(a, s) ↦ L (a e + s j e)` from the standard complex
line. -/
theorem energyDensity_apply_complexFrame_eq_stdComplexLineEnergyDensity
    (L : TangentSpace I' c →ₗ[ℝ] TangentSpace I x) (e : TangentSpace I' c) :
    form.energyDensity J j L ![e, j c e] = 2⁻¹ * form.stdComplexLineEnergyDensity J x
      (L ∘ₗ (LinearMap.toSpanSingleton ℝ _ e).coprod (LinearMap.toSpanSingleton ℝ _ (j c e))) := by
  rw [energyDensity_apply_complexFrame, stdComplexLineEnergyDensity_def, LinearMap.comp_apply,
    LinearMap.comp_apply, LinearMap.coprod_toSpanSingleton_apply_stdComplexLineReal,
    LinearMap.coprod_toSpanSingleton_apply_stdComplexLineImag, SmoothBundleForm.eval₂_apply,
    SmoothBundleForm.eval₂_apply]

/-- If `form` tames `J`, then at each `x` the alternating form `form_x` is positive on every pair
`(v, J_x v)` with `v ≠ 0`. -/
theorem Tames.toAlternatingMap_pos {form : SmoothTwoForm I M}
    {J : SmoothAlmostComplexStructure I M} (h : form.Tames J) (x : M) (v : TangentSpace I x)
    (hv : v ≠ 0) : 0 < (form.val x).toAlternatingMap ![v, J.almostComplexStructureAt x v] := by
  simpa only [ContinuousAlternatingMap.coe_toAlternatingMap,
    SmoothAlmostComplexStructure.almostComplexStructureAt_apply, SmoothBundleForm.eval₂_apply]
    using tames_iff.mp h x v hv

/-- If `form` is `J`-invariant, then at each `x` the alternating form `form_x` takes the same
value on `(J_x v, J_x w)` as on `(v, w)`. -/
theorem Invariant.toAlternatingMap_apply_eq {form : SmoothTwoForm I M}
    {J : SmoothAlmostComplexStructure I M} (h : form.Invariant J) (x : M)
    (v w : TangentSpace I x) :
    (form.val x).toAlternatingMap
        ![J.almostComplexStructureAt x v, J.almostComplexStructureAt x w] =
      (form.val x).toAlternatingMap ![v, w] := by
  simpa only [ContinuousAlternatingMap.coe_toAlternatingMap,
    SmoothAlmostComplexStructure.almostComplexStructureAt_apply, SmoothBundleForm.eval₂_apply]
    using invariant_iff.mp h x v w

/-- If `form` tames `J`, the energy density is nonnegative on every frame `(e, j e)`. -/
theorem Tames.energyDensity_apply_complexFrame_nonneg {form : SmoothTwoForm I M}
    {J : SmoothAlmostComplexStructure I M} (h : form.Tames J)
    (L : TangentSpace I' c →ₗ[ℝ] TangentSpace I x) (e : TangentSpace I' c) :
    0 ≤ form.energyDensity J j L ![e, j c e] := by
  rw [energyDensity_apply_eq, ← j.almostComplexStructureAt_apply]
  exact AlternatingMap.energyDensity_apply_complexFrame_nonneg _ (h.toAlternatingMap_pos x) L e

/-- If `form` tames `J`, the energy density vanishes on a frame `(e, j e)` exactly when `L`
vanishes on `e` and `j e`. -/
theorem Tames.energyDensity_apply_complexFrame_eq_zero_iff {form : SmoothTwoForm I M}
    {J : SmoothAlmostComplexStructure I M} (h : form.Tames J)
    (L : TangentSpace I' c →ₗ[ℝ] TangentSpace I x) (e : TangentSpace I' c) :
    form.energyDensity J j L ![e, j c e] = 0 ↔ L e = 0 ∧ L (j c e) = 0 := by
  rw [energyDensity_apply_eq, ← j.almostComplexStructureAt_apply]
  exact AlternatingMap.energyDensity_apply_complexFrame_eq_zero_iff _ (h.toAlternatingMap_pos x) L e

/-- The squared norm `|L|²` of a linear map `L : T_c C → T_x M` for the metric
`dvol (·, j ·)` on the source and the form `form (·, J ·)` on the target:
`AlternatingMap.energyNormSq` for `form_x`, `J_x`, `j_c` and `dvol_c`, that is the value
`(form (L e, J (L e)) + form (L (j e), J (L (j e)))) / dvol (e, j e)` for a nonzero `e` chosen
once, and `0` if the tangent space is zero. On a plane, any nonzero `e` gives the same value
(`normSq_eq`). -/
def normSq (dvol : SmoothTwoForm I' C) (L : TangentSpace I' c →ₗ[ℝ] TangentSpace I x) : ℝ :=
  AlternatingMap.energyNormSq (form.val x).toAlternatingMap (J.almostComplexStructureAt x)
    (j.almostComplexStructureAt c) (dvol.val c).toAlternatingMap L

omit [FiniteDimensional ℝ E'] in
/-- The squared norm by its definition. -/
theorem normSq_def (dvol : SmoothTwoForm I' C) (L : TangentSpace I' c →ₗ[ℝ] TangentSpace I x) :
    form.normSq J j dvol L = AlternatingMap.energyNormSq (form.val x).toAlternatingMap
      (J.almostComplexStructureAt x) (j.almostComplexStructureAt c) (dvol.val c).toAlternatingMap
      L :=
  (rfl)

omit [FiniteDimensional ℝ E'] in
/-- On a surface, the squared norm of `L` is
`(form (L e, J (L e)) + form (L (j e), J (L (j e)))) / dvol (e, j e)` for every nonzero `e`. -/
theorem normSq_eq (h2 : Module.finrank ℝ E' = 2) (dvol : SmoothTwoForm I' C)
    (L : TangentSpace I' c →ₗ[ℝ] TangentSpace I x) {e : TangentSpace I' c} (he : e ≠ 0) :
    form.normSq J j dvol L = (form.val x ![L e, J x (L e)] +
      form.val x ![L (j c e), J x (L (j c e))]) / dvol.val c ![e, j c e] := by
  simp only [normSq_def, ← SmoothAlmostComplexStructure.almostComplexStructureAt_apply]
  exact AlternatingMap.energyNormSq_eq _ _ _ h2 _ L he

/-- On a surface, where the area form `dvol` does not vanish, `|L|² dvol = 2 ε_L` as top
forms. -/
theorem normSq_smul_eq_two_smul_energyDensity (h2 : Module.finrank ℝ E' = 2)
    {dvol : SmoothTwoForm I' C} (hdvol : dvol.val c ≠ 0)
    (L : TangentSpace I' c →ₗ[ℝ] TangentSpace I x) :
    form.normSq J j dvol L • dvol.val c = (2 : ℝ) • form.energyDensity J j L := by
  refine ContinuousAlternatingMap.toAlternatingMap_injective ?_
  rw [ContinuousAlternatingMap.toAlternatingMap_smul,
    ContinuousAlternatingMap.toAlternatingMap_smul,
    toAlternatingMap_energyDensity, normSq_def]
  refine AlternatingMap.energyNormSq_smul_eq_two_smul_energyDensity _ _ _ h2 (fun h ↦ hdvol ?_) L
  exact ContinuousAlternatingMap.toAlternatingMap_injective h

omit [FiniteDimensional ℝ E'] in
/-- If `form` tames `J` and `dvol` tames `j`, the squared norm is nonnegative. -/
theorem normSq_nonneg {form : SmoothTwoForm I M} {J : SmoothAlmostComplexStructure I M}
    (hform : form.Tames J) {dvol : SmoothTwoForm I' C} (hdvol : dvol.Tames j)
    (L : TangentSpace I' c →ₗ[ℝ] TangentSpace I x) : 0 ≤ form.normSq J j dvol L :=
  AlternatingMap.energyNormSq_nonneg (hform.toAlternatingMap_pos x) (hdvol.toAlternatingMap_pos c)
    L

/-- **The pointwise energy identity.** If `form` is `J`-invariant, then on a tangent plane of an
almost complex surface the energy density of `L` is twice that of its complex-antilinear part
`∂̄L = ½ (L + J ∘ L ∘ j)` plus the pullback of `form` by `L`:
`ε_L = 2 ε_{∂̄L} + L^* form`. -/
theorem Invariant.energyDensity_eq_two_smul_add {form : SmoothTwoForm I M}
    {J : SmoothAlmostComplexStructure I M} (hinv : form.Invariant J)
    (h2 : Module.finrank ℝ E' = 2) (L : TangentSpace I' c →L[ℝ] TangentSpace I x) :
    form.energyDensity J j (L : TangentSpace I' c →ₗ[ℝ] TangentSpace I x) =
      (2 : ℝ) • form.energyDensity J j (complexAntilinearPart
        (j.toEndomorphism c : TangentSpace I' c →ₗ[ℝ] TangentSpace I' c)
        (J.toEndomorphism x : TangentSpace I x →ₗ[ℝ] TangentSpace I x) L) +
      (form.val x).compContinuousLinearMap L := by
  refine ContinuousAlternatingMap.toAlternatingMap_injective ?_
  rw [ContinuousAlternatingMap.toAlternatingMap_add,
    ContinuousAlternatingMap.toAlternatingMap_smul,
    toAlternatingMap_energyDensity, toAlternatingMap_energyDensity]
  refine (AlternatingMap.energyDensity_eq_two_smul_add _
    (hinv.toAlternatingMap_apply_eq x) h2
    (L : TangentSpace I' c →ₗ[ℝ] TangentSpace I x)).trans ?_
  rw [SmoothAlmostComplexStructure.almostComplexStructureAt_toLinearMap,
    SmoothAlmostComplexStructure.almostComplexStructureAt_toLinearMap]
  -- The pullbacks `(form x).toAlternatingMap.compLinearMap L` and
  -- `((form x).compContinuousLinearMap L).toAlternatingMap` are the same alternating map, but
  -- their codomains are `ℝ` and `Bundle.Trivial M ℝ x`, so no rewrite applies; `congr 1` closes
  -- both sides by definitional unfolding.
  congr 1

end SmoothTwoForm

end TauCeti
