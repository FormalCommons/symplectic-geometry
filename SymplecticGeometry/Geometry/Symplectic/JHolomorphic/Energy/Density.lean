/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.IsManifold.Basic
public import SymplecticGeometry.Geometry.Symplectic.Manifold.AlmostComplex.TopForm
public import TauCeti.Geometry.Symplectic.Manifold.Energy
public import TauCeti.LinearAlgebra.BilinearMap.Multilinear
public import TauCeti.LinearAlgebra.Complex.LinearPart
public import TauCeti.Topology.Algebra.Module.Alternating.TopDegree
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
  Both sides are top forms on a plane, so it suffices to compare them on one frame `(e, j e)`
  (`TauCeti.SmoothAlmostComplexStructure.topForm_ext`), where it is Tau Ceti's Wirtinger identity
  `TauCeti.SmoothTwoForm.Invariant.stdComplexLineEnergyDensity_sub_two_mul_twoForm`.

The statements on a plane take only `Module.finrank ℝ E' = 2`, not an orientation of `C`; the
comparison of top forms on frames `(e, j e)` is in
`SymplecticGeometry.Geometry.Symplectic.Manifold.AlmostComplex.TopForm`.

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

/-- The map `(a, s) ↦ a • v + s • w` sends `stdComplexLineReal = (1, 0)` to `v`. -/
theorem _root_.LinearMap.coprod_toSpanSingleton_apply_stdComplexLineReal {V : Type*}
    [AddCommGroup V] [Module ℝ V] (v w : V) :
    (LinearMap.toSpanSingleton ℝ V v).coprod (LinearMap.toSpanSingleton ℝ V w)
      stdComplexLineReal = v := by
  simp [stdComplexLineReal_eq]

/-- The map `(a, s) ↦ a • v + s • w` sends `stdComplexLineImag = (0, 1)` to `w`. -/
theorem _root_.LinearMap.coprod_toSpanSingleton_apply_stdComplexLineImag {V : Type*}
    [AddCommGroup V] [Module ℝ V] (v w : V) :
    (LinearMap.toSpanSingleton ℝ V v).coprod (LinearMap.toSpanSingleton ℝ V w)
      stdComplexLineImag = w := by
  simp [stdComplexLineImag_eq]

namespace SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' H' C : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace C]
  [ChartedSpace H' C] [IsManifold I' ∞ C]

variable (form : SmoothTwoForm I M) (J : SmoothAlmostComplexStructure I M)
  (j : SmoothAlmostComplexStructure I' C) {c : C} {x : M}

/-- The bilinear form `(v, w) ↦ ¼ (b (j v) w + b w (j v) - b v (j w) - b (j w) v)` for
`b v w = form (L v) (J (L w))`, whose alternating map is the energy density. -/
private def energyBilin (L : TangentSpace I' c →ₗ[ℝ] TangentSpace I x) :
    TangentSpace I' c →ₗ[ℝ] TangentSpace I' c →ₗ[ℝ] ℝ :=
  let b := (form.bilinFormAt x).compl₁₂ L ((J.toEndomorphism x).toLinearMap ∘ₗ L)
  let jc := (j.toEndomorphism c).toLinearMap
  (4⁻¹ : ℝ) • (b ∘ₗ jc + b.flip ∘ₗ jc - b.compl₂ jc - b.flip.compl₂ jc)

omit [FiniteDimensional ℝ E'] in
private lemma energyBilin_apply (L : TangentSpace I' c →ₗ[ℝ] TangentSpace I x)
    (v w : TangentSpace I' c) :
    energyBilin form J j L v w = 4⁻¹ * (form.val x ![L (j c v), J x (L w)] +
      form.val x ![L w, J x (L (j c v))] - form.val x ![L v, J x (L (j c w))] -
      form.val x ![L (j c w), J x (L v)]) := by
  simp [energyBilin]

omit [FiniteDimensional ℝ E'] in
private lemma isAlt_energyBilin (L : TangentSpace I' c →ₗ[ℝ] TangentSpace I x) :
    (energyBilin form J j L).IsAlt := fun v ↦ by
  rw [energyBilin_apply]
  ring

/-- The energy density `ε_L` of a linear map `L : T_c C → T_x M` from a tangent space of the
surface `(C, j)` to one of `(M, form, J)`: the top form on `T_c C` given by
`ε_L (v, w) = ¼ (b (j v, w) + b (w, j v) - b (v, j w) - b (j w, v))` with
`b (v, w) = form_x (L v, J_x (L w))`. On a frame `(e, j e)` it is
`½ (form (L e, J (L e)) + form (L (j e), J (L (j e))))` (`energyDensity_apply_complexFrame`). It
is defined for every `form` and `J`, and does not involve an area form on `C`. -/
def energyDensity (L : TangentSpace I' c →ₗ[ℝ] TangentSpace I x) :
    TangentSpace I' c [⋀^Fin 2]→L[ℝ] ℝ :=
  haveI : FiniteDimensional ℝ (TangentSpace I' c) := inferInstanceAs (FiniteDimensional ℝ E')
  AlternatingMap.toContinuousAlternatingMap (isAlt_energyBilin form J j L).toAlternatingMap

/-- The energy density on a pair of tangent vectors, by its four-term formula. -/
theorem energyDensity_apply (L : TangentSpace I' c →ₗ[ℝ] TangentSpace I x)
    (v w : TangentSpace I' c) :
    form.energyDensity J j L ![v, w] = 4⁻¹ * (form.val x ![L (j c v), J x (L w)] +
      form.val x ![L w, J x (L (j c v))] - form.val x ![L v, J x (L (j c w))] -
      form.val x ![L (j c w), J x (L v)]) := by
  have : FiniteDimensional ℝ (TangentSpace I' c) := inferInstanceAs (FiniteDimensional ℝ E')
  rw [energyDensity, AlternatingMap.coe_toContinuousAlternatingMap,
    LinearMap.IsAlt.toAlternatingMap_apply, energyBilin_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]

/-- On a frame `(e, j e)`, the energy density is
`½ (form (L e, J (L e)) + form (L (j e), J (L (j e))))`. -/
theorem energyDensity_apply_complexFrame (L : TangentSpace I' c →ₗ[ℝ] TangentSpace I x)
    (e : TangentSpace I' c) :
    form.energyDensity J j L ![e, j c e] = 2⁻¹ * (form.val x ![L e, J x (L e)] +
      form.val x ![L (j c e), J x (L (j c e))]) := by
  rw [energyDensity_apply, j.apply_apply]
  simp only [← SmoothBundleForm.eval₂_apply, map_neg, SmoothBundleForm.eval₂_neg_left,
    SmoothBundleForm.eval₂_neg_right]
  ring

/-- The energy density of the zero map vanishes. -/
@[simp]
theorem energyDensity_zero :
    form.energyDensity J j (0 : TangentSpace I' c →ₗ[ℝ] TangentSpace I x) = 0 := by
  ext v
  have hv : v = ![v 0, v 1] := by
    funext i
    fin_cases i <;> simp
  rw [hv, energyDensity_apply]
  simp

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
/-- If `form` tames `J`, the energy density is nonnegative on every frame `(e, j e)`. -/
theorem Tames.energyDensity_apply_complexFrame_nonneg {form : SmoothTwoForm I M}
    {J : SmoothAlmostComplexStructure I M} (h : form.Tames J)
    (L : TangentSpace I' c →ₗ[ℝ] TangentSpace I x) (e : TangentSpace I' c) :
    0 ≤ form.energyDensity J j L ![e, j c e] := by
  rw [energyDensity_apply_complexFrame_eq_stdComplexLineEnergyDensity]
  exact mul_nonneg (by norm_num) (h.stdComplexLineEnergyDensity_nonneg x _)

/-- If `form` tames `J`, the energy density vanishes on a frame `(e, j e)` exactly when `L`
vanishes on `e` and `j e`. -/
theorem Tames.energyDensity_apply_complexFrame_eq_zero_iff {form : SmoothTwoForm I M}
    {J : SmoothAlmostComplexStructure I M} (h : form.Tames J)
    (L : TangentSpace I' c →ₗ[ℝ] TangentSpace I x) (e : TangentSpace I' c) :
    form.energyDensity J j L ![e, j c e] = 0 ↔ L e = 0 ∧ L (j c e) = 0 := by
  rw [energyDensity_apply_complexFrame_eq_stdComplexLineEnergyDensity, mul_eq_zero,
    or_iff_right (by norm_num), h.stdComplexLineEnergyDensity_eq_zero_iff]
  constructor
  · intro hL
    exact ⟨by simpa using LinearMap.congr_fun hL (1, 0),
      by simpa using LinearMap.congr_fun hL (0, 1)⟩
  · rintro ⟨h₁, h₂⟩
    ext <;> simp [h₁, h₂]

open scoped Classical in
/-- The squared norm `|L|²` of a linear map `L : T_c C → T_x M` for the metric
`dvol (·, j ·)` on the source and the form `form (·, J ·)` on the target: the value
`(form (L e, J (L e)) + form (L (j e), J (L (j e)))) / dvol (e, j e)` for a nonzero `e` chosen
once, and `0` if the tangent space is zero. On a plane, any nonzero `e` gives the same value
(`normSq_eq`). -/
def normSq (dvol : SmoothTwoForm I' C) (L : TangentSpace I' c →ₗ[ℝ] TangentSpace I x) : ℝ :=
  if h : ∃ e : TangentSpace I' c, e ≠ 0 then
    (form.val x ![L h.choose, J x (L h.choose)] +
        form.val x ![L (j c h.choose), J x (L (j c h.choose))]) /
      dvol.val c ![h.choose, j c h.choose]
  else 0

omit [FiniteDimensional ℝ E'] in
open scoped Classical in
/-- The squared norm by its definition. -/
theorem normSq_def (dvol : SmoothTwoForm I' C) (L : TangentSpace I' c →ₗ[ℝ] TangentSpace I x) :
    form.normSq J j dvol L =
      if h : ∃ e : TangentSpace I' c, e ≠ 0 then
        (form.val x ![L h.choose, J x (L h.choose)] +
            form.val x ![L (j c h.choose), J x (L (j c h.choose))]) /
          dvol.val c ![h.choose, j c h.choose]
      else 0 :=
  (rfl)

/-- On a surface, the squared norm of `L` is
`(form (L e, J (L e)) + form (L (j e), J (L (j e)))) / dvol (e, j e)` for every nonzero `e`. -/
theorem normSq_eq (h2 : Module.finrank ℝ E' = 2) (dvol : SmoothTwoForm I' C)
    (L : TangentSpace I' c →ₗ[ℝ] TangentSpace I x) {e : TangentSpace I' c} (he : e ≠ 0) :
    form.normSq J j dvol L = (form.val x ![L e, J x (L e)] +
      form.val x ![L (j c e), J x (L (j c e))]) / dvol.val c ![e, j c e] := by
  have h : ∃ e : TangentSpace I' c, e ≠ 0 := ⟨e, he⟩
  have key (e : TangentSpace I' c) : form.val x ![L e, J x (L e)] +
      form.val x ![L (j c e), J x (L (j c e))] = 2 * form.energyDensity J j L ![e, j c e] := by
    rw [energyDensity_apply_complexFrame]
    ring
  simp only [normSq_def, h, ↓reduceDIte]
  rw [key, key, mul_div_assoc, mul_div_assoc,
    j.topForm_apply_div_apply_eq h2 he h.choose_spec]

/-- On a surface, where the area form `dvol` does not vanish, `|L|² dvol = 2 ε_L` as top
forms. -/
theorem normSq_smul_eq_two_smul_energyDensity (h2 : Module.finrank ℝ E' = 2)
    {dvol : SmoothTwoForm I' C} (hdvol : dvol.val c ≠ 0)
    (L : TangentSpace I' c →ₗ[ℝ] TangentSpace I x) :
    form.normSq J j dvol L • dvol.val c = (2 : ℝ) • form.energyDensity J j L := by
  have : Nontrivial E' := Module.nontrivial_of_finrank_pos (R := ℝ) (h2 ▸ two_pos)
  obtain ⟨e, he⟩ := exists_ne (0 : TangentSpace I' c)
  have hd : dvol.val c ![e, j c e] ≠ 0 := fun hd ↦
    hdvol (j.topForm_ext h2 he (by rw [hd]; rfl))
  refine j.topForm_ext h2 he ?_
  rw [ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul,
    smul_eq_mul, normSq_eq form J j h2 dvol L he, energyDensity_apply_complexFrame]
  field_simp

/-- If `form` tames `J` and `dvol` tames `j`, the squared norm is nonnegative. -/
theorem normSq_nonneg {form : SmoothTwoForm I M} {J : SmoothAlmostComplexStructure I M}
    (hform : form.Tames J) {dvol : SmoothTwoForm I' C} (hdvol : dvol.Tames j)
    (L : TangentSpace I' c →ₗ[ℝ] TangentSpace I x) : 0 ≤ form.normSq J j dvol L := by
  rw [normSq_def]
  split_ifs with h
  · refine div_nonneg ?_ (by simpa using (tames_iff.mp hdvol c _ h.choose_spec).le)
    have := hform.energyDensity_apply_complexFrame_nonneg j L h.choose
    rw [energyDensity_apply_complexFrame] at this
    linarith
  · exact le_rfl

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
  have : Nontrivial E' := Module.nontrivial_of_finrank_pos (R := ℝ) (h2 ▸ two_pos)
  obtain ⟨e, he⟩ := exists_ne (0 : TangentSpace I' c)
  refine j.topForm_ext h2 he ?_
  set A := complexAntilinearPart
    (j.toEndomorphism c : TangentSpace I' c →ₗ[ℝ] TangentSpace I' c)
    (J.toEndomorphism x : TangentSpace I x →ₗ[ℝ] TangentSpace I x) L
  -- `w = L e + J (L (j e))` is twice `∂̄L e`, and `∂̄L (j e) = - J (∂̄L e)`.
  set w := L e + J x (L (j c e))
  have hAe : A e = (2⁻¹ : ℝ) • w := by
    rw [complexAntilinearPart_apply, ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_coe,
      ContinuousLinearMap.coe_coe]
  have hAje : A (j c e) = -J x (A e) := by
    simpa only [SmoothAlmostComplexStructure.almostComplexStructureAt_toLinearMap,
      ContinuousLinearMap.coe_coe] using
      (isComplexAntilinear_complexAntilinearPart (j.almostComplexStructureAt c).square_neg
        (J.almostComplexStructureAt x).square_neg (L : _ →ₗ[ℝ] _)).apply e
  have hJA : form.val x ![A (j c e), J x (A (j c e))] = form.val x ![A e, J x (A e)] := by
    simp only [hAje, map_neg, J.apply_apply, neg_neg]
    rw [← SmoothBundleForm.eval₂_apply, ← SmoothBundleForm.eval₂_apply,
      SmoothBundleForm.eval₂_neg_left,
      SmoothBundleForm.eval₂_swap form x (J x (A e)), neg_neg]
  have hAA : form.val x ![A e, J x (A e)] = 4⁻¹ * form.val x ![w, J x w] := by
    simp only [hAe, map_smul]
    rw [← SmoothBundleForm.eval₂_apply, ← SmoothBundleForm.eval₂_apply,
      SmoothBundleForm.eval₂_smul_left, SmoothBundleForm.eval₂_smul_right, smul_eq_mul,
      smul_eq_mul]
    ring
  have hW := hinv.stdComplexLineEnergyDensity_sub_two_mul_twoForm x
    ((L : TangentSpace I' c →ₗ[ℝ] TangentSpace I x) ∘ₗ
      (LinearMap.toSpanSingleton ℝ _ e).coprod (LinearMap.toSpanSingleton ℝ _ (j c e)))
  rw [LinearMap.comp_apply, LinearMap.comp_apply,
    LinearMap.coprod_toSpanSingleton_apply_stdComplexLineReal,
    LinearMap.coprod_toSpanSingleton_apply_stdComplexLineImag, SmoothBundleForm.eval₂_apply,
    SmoothBundleForm.eval₂_apply] at hW
  simp only [ContinuousLinearMap.coe_coe] at hW
  have hL : ⇑L ∘ ![e, j c e] = ![L e, L (j c e)] := (FinVec.map_eq _ _).symm
  rw [energyDensity_apply_complexFrame_eq_stdComplexLineEnergyDensity,
    ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul,
    energyDensity_apply_complexFrame, hJA, hAA,
    ContinuousAlternatingMap.compContinuousLinearMap_apply, hL]
  linear_combination (2⁻¹ : ℝ) * hW

end SmoothTwoForm

end TauCeti
