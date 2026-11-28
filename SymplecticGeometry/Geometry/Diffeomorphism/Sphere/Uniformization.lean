/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
public import SymplecticGeometry.Geometry.Diffeomorphism.Sphere.ComplexStructure
public import SymplecticGeometry.Geometry.Manifold.Instances.OnePoint.CauchyRiemann.Kernel
public import TauCeti.Geometry.Manifold.Instances.OnePoint.FubiniStudy
import TauCeti.Geometry.Manifold.Algebra.ComplexSmoothFunctions
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Descent
import TauCeti.Topology.VectorBundle.ZeroSection

/-!
# The uniformizing map of a tame almost complex structure on the sphere

Let `J` be a smooth almost complex structure on the Riemann sphere `OnePoint ℂ` tamed by the
Fubini–Study form `OnePoint.fubiniStudyForm`, and let `E_J = twistOneKernel J` be the kernel of
the real Cauchy–Riemann operator `D_J` on the line bundle `𝒪(1)`. Pick nonzero `s, t ∈ E_J`
with `s 0 = 0` and `t ∞ = 0` (`SymplecticGeometry.exists_mem_twistOneKernel_eq_zero`). Every
nonzero element of `E_J` vanishes at a single point
(`SymplecticGeometry.existsUnique_eq_zero_of_mem_twistOneKernel`), so `s` and `t` have no common
zero and do not vanish at `1`. Hence

  `σ(J) x = [s x · t 1 : t x · s 1]`

is a well defined map from the sphere to itself, read through Mathlib's identification
`OnePoint.equivProjectivization` of `OnePoint ℂ` with `ℙ¹(ℂ)`.

## Main definitions and results

* `SymplecticGeometry.vec_ne_zero_of_mem_twistOneKernel`: the vector
  `![s x * t 1, t x * s 1]` is nonzero, for `s, t` as above.
* `SymplecticGeometry.uniformizingMap`: the map `σ(J)`.
* `SymplecticGeometry.uniformizingMap_eq`: `σ(J)` is given by the formula above for every choice
  of `s` and `t`, since the elements of `E_J` vanishing at a point form a complex line
  (`SymplecticGeometry.exists_smul_eq_of_mem_twistOneKernel`).
* `SymplecticGeometry.uniformizingMap_zero`, `SymplecticGeometry.uniformizingMap_one` and
  `SymplecticGeometry.uniformizingMap_infty`: `σ(J)` fixes `0`, `1` and `∞`.
* `SymplecticGeometry.injective_uniformizingMap`: `σ(J)` is injective, since `σ(J) x = σ(J) y`
  gives a nonzero element `t y • s - s y • t` of `E_J` vanishing at `x` and at `y`.
* `SymplecticGeometry.contMDiff_uniformizingMap`: `σ(J)` is smooth. Where `t` does not vanish it
  is the inclusion of `ℂ` applied to a constant multiple of the quotient `s / t` of smooth
  sections of `𝒪(1)` (`OnePoint.contMDiffAt_div_twistCore`), and where `s` does not vanish it is
  the inverse of the inverted chart applied to a constant multiple of `t / s`.
* `SymplecticGeometry.isLocalDiffeomorph_uniformizingMap`: `σ(J)` is a local diffeomorphism.
  In the two local forms above, the quotient has injective derivative
  (`SymplecticGeometry.injective_mfderiv_div_of_mem_twistOneKernel`) and the charts are local
  diffeomorphisms, so Tau Ceti's inverse function theorem
  `TauCeti.isLocalDiffeomorphAt_of_injective_mfderiv` applies at every point.
* `SymplecticGeometry.bijective_uniformizingMap`: `σ(J)` is bijective. Its range is open, as
  that of a local diffeomorphism, closed, as the image of a compact space, and nonempty, so it is
  the whole connected sphere.
* `SymplecticGeometry.isPseudoholomorphic_uniformizingMap`: `σ(J)` is pseudoholomorphic from `J`
  to the complex structure `i` of the sphere, since in the two local forms above the quotient is
  pseudoholomorphic (`SymplecticGeometry.isPseudoholomorphicAt_div_of_mem_twistOneKernel`) and
  the charts are holomorphic.
* `SymplecticGeometry.uniformizingDiffeomorph`: `σ(J)` as an element of `diffPlus`, built by
  Mathlib's `IsLocalDiffeomorph.diffeomorphOfBijective`, with
  `SymplecticGeometry.coe_uniformizingDiffeomorph`, and
  `SymplecticGeometry.pullback_uniformizingDiffeomorph`: `σ(J)^* i = J`, since a diffeomorphism
  pseudoholomorphic from `J` to `i` pulls `i` back to `J`
  (`TauCeti.SmoothAlmostComplexStructure.eq_localPullback_iff_isPseudoholomorphic`). It preserves
  the orientation by `SymplecticGeometry.mem_diffPlus_iff_tames_pullback`, since the
  Fubini–Study form tames `J`. So `uniformizingDiffeomorph` is a section of
  `SymplecticGeometry.complexStructureMap`
  (`SymplecticGeometry.complexStructureMap_uniformizingDiffeomorph`).

## References

* [D. McDuff, D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd
  ed.][McDuffSalamon2012] (Riemann–Roch for real Cauchy–Riemann operators on line bundles over
  the sphere).
-/

public section

open scoped OnePoint SymplecticGeometry Manifold ContDiff Topology TauCeti.ComplexManifold
open TauCeti

namespace SymplecticGeometry

/-- The smooth almost complex structures on the Riemann sphere tamed by the Fubini–Study form. -/
local notation "𝒥" =>
  {J : SmoothAlmostComplexStructure 𝓘(ℝ, ℂ) (OnePoint ℂ) // OnePoint.fubiniStudyForm.Tames J}

section Vector

variable {σ : SmoothTwoForm 𝓘(ℝ, ℂ) (OnePoint ℂ)}
  {J : SmoothAlmostComplexStructure 𝓘(ℝ, ℂ) (OnePoint ℂ)}

/-- Let a two-form `σ` tame both `J` and the standard structure `i`, and let `s, t` be nonzero
elements of `twistOneKernel J` with `s 0 = 0` and `t ∞ = 0`. Then for every point `x`, the
vector `![s x * t 1, t x * s 1]` of `ℂ²` is nonzero. -/
theorem vec_ne_zero_of_mem_twistOneKernel (hJ : σ.Tames J) (hi : σ.Tames 𝒊)
    {s t : OnePoint ℂ → ℂ} (hs : s ∈ twistOneKernel J) (ht : t ∈ twistOneKernel J)
    (hs' : s ≠ 0) (ht' : t ≠ 0) (h₀ : s (0 : ℂ) = 0) (hinf : t ∞ = 0) (x : OnePoint ℂ) :
    ![s x * t (1 : ℂ), t x * s (1 : ℂ)] ≠ 0 := by
  have hs₁ := apply_ne_zero_of_mem_twistOneKernel hJ hi hs hs' h₀ (y := (1 : ℂ)) (by simp)
  have ht₁ := apply_ne_zero_of_mem_twistOneKernel hJ hi ht ht' hinf (y := (1 : ℂ)) (by simp)
  intro hv
  have hx₀ : s x = 0 := by simpa [ht₁] using congrFun hv 0
  have hxinf : t x = 0 := by simpa [hs₁] using congrFun hv 1
  exact OnePoint.coe_ne_infty _ ((eq_of_mem_twistOneKernel_of_eq_zero hJ hi hs hs' h₀ hx₀).trans
    (eq_of_mem_twistOneKernel_of_eq_zero hJ hi ht ht' hxinf hinf))

end Vector

/-- The nonzero element of `twistOneKernel J` vanishing at `x` that `uniformizingMap` uses. -/
private noncomputable def chosenSection (J : 𝒥) (x : OnePoint ℂ) : OnePoint ℂ → ℂ :=
  (exists_mem_twistOneKernel_eq_zero J.property OnePoint.compatible_fubiniStudyForm.tames
    x).choose

private theorem chosenSection_spec (J : 𝒥) (x : OnePoint ℂ) :
    chosenSection J x ∈ twistOneKernel J.val ∧ chosenSection J x ≠ 0 ∧
      chosenSection J x x = 0 :=
  (exists_mem_twistOneKernel_eq_zero J.property OnePoint.compatible_fubiniStudyForm.tames
    x).choose_spec

private theorem chosenSection_vec_ne_zero (J : 𝒥) (x : OnePoint ℂ) :
    ![chosenSection J (0 : ℂ) x * chosenSection J ∞ (1 : ℂ),
      chosenSection J ∞ x * chosenSection J (0 : ℂ) (1 : ℂ)] ≠ 0 :=
  vec_ne_zero_of_mem_twistOneKernel J.property OnePoint.compatible_fubiniStudyForm.tames
    (chosenSection_spec J _).1 (chosenSection_spec J ∞).1 (chosenSection_spec J _).2.1
    (chosenSection_spec J ∞).2.1 (chosenSection_spec J _).2.2 (chosenSection_spec J ∞).2.2 x

/-- **The uniformizing map** `σ(J)` of a structure `J` tamed by the Fubini–Study form: with
`s, t` nonzero elements of `twistOneKernel J` vanishing at `0` and at `∞`, the point `x` goes
to `[s x · t 1 : t x · s 1]`, read through `OnePoint.equivProjectivization`. By
`uniformizingMap_eq`, it does not depend on the choice of `s` and `t`. -/
noncomputable def uniformizingMap (J : 𝒥) (x : OnePoint ℂ) : OnePoint ℂ :=
  (OnePoint.equivProjectivization ℂ).symm <| Projectivization.mk ℂ
    ![chosenSection J (0 : ℂ) x * chosenSection J ∞ (1 : ℂ),
      chosenSection J ∞ x * chosenSection J (0 : ℂ) (1 : ℂ)]
    (chosenSection_vec_ne_zero J x)

/-- **`σ(J)` does not depend on the sections.** For any nonzero `s, t ∈ twistOneKernel J` with
`s 0 = 0` and `t ∞ = 0`, the map `uniformizingMap J` sends `x` to
`[s x · t 1 : t x · s 1]`. -/
theorem uniformizingMap_eq (J : 𝒥) {s t : OnePoint ℂ → ℂ} (hs : s ∈ twistOneKernel J.val)
    (ht : t ∈ twistOneKernel J.val) (hs' : s ≠ 0) (ht' : t ≠ 0) (h₀ : s (0 : ℂ) = 0)
    (hinf : t ∞ = 0) (x : OnePoint ℂ) :
    uniformizingMap J x = (OnePoint.equivProjectivization ℂ).symm (Projectivization.mk ℂ
      ![s x * t (1 : ℂ), t x * s (1 : ℂ)]
      (vec_ne_zero_of_mem_twistOneKernel J.property OnePoint.compatible_fubiniStudyForm.tames
        hs ht hs' ht' h₀ hinf x)) := by
  have hi := OnePoint.compatible_fubiniStudyForm.tames
  obtain ⟨ht₀, ht₀', ht₀0⟩ := chosenSection_spec J (0 : ℂ)
  obtain ⟨htinf, htinf', htinf0⟩ := chosenSection_spec J ∞
  obtain ⟨a, ha⟩ := exists_smul_eq_of_mem_twistOneKernel J.property hi ht₀ hs ht₀' ht₀0 h₀
  obtain ⟨b, hb⟩ :=
    exists_smul_eq_of_mem_twistOneKernel J.property hi htinf ht htinf' htinf0 hinf
  rw [uniformizingMap, Equiv.apply_eq_iff_eq, Projectivization.mk_eq_mk_iff']
  refine ⟨(a * b)⁻¹, ?_⟩
  have hab : a * b ≠ 0 := by
    refine mul_ne_zero (fun h ↦ hs' ?_) (fun h ↦ ht' ?_)
    · rw [← ha, h, zero_smul]
    · rw [← hb, h, zero_smul]
  have ha0 : a ≠ 0 := left_ne_zero_of_mul hab
  have hb0 : b ≠ 0 := right_ne_zero_of_mul hab
  subst ha hb
  ext i
  fin_cases i <;> simp <;> field_simp

/-- `σ(J)` fixes `0`. -/
@[simp]
theorem uniformizingMap_zero (J : 𝒥) : uniformizingMap J (0 : ℂ) = (0 : ℂ) := by
  have h₀ := (chosenSection_spec J (0 : ℂ)).2.2
  have h := chosenSection_vec_ne_zero J (0 : ℂ)
  rw [uniformizingMap, OnePoint.equivProjectivization_symm_apply_mk]
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero, h₀, zero_mul, mul_zero] at h ⊢
  have h₁ : chosenSection J ∞ (0 : ℂ) * chosenSection J (0 : ℂ) (1 : ℂ) ≠ 0 :=
    fun h' ↦ h (by ext i; fin_cases i <;> simp [h'])
  simp [h₁]

/-- `σ(J)` fixes `1`. -/
@[simp]
theorem uniformizingMap_one (J : 𝒥) : uniformizingMap J (1 : ℂ) = (1 : ℂ) := by
  have h := chosenSection_vec_ne_zero J (1 : ℂ)
  rw [uniformizingMap, OnePoint.equivProjectivization_symm_apply_mk]
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
  have h₁ : chosenSection J ∞ (1 : ℂ) * chosenSection J (0 : ℂ) (1 : ℂ) ≠ 0 :=
    fun h' ↦ h (by ext i; fin_cases i <;> simp [h', mul_comm])
  simp only [h₁, ↓reduceIte]
  rw [mul_comm (chosenSection J (0 : ℂ) _), inv_mul_cancel₀ h₁]

/-- `σ(J)` fixes `∞`. -/
@[simp]
theorem uniformizingMap_infty (J : 𝒥) : uniformizingMap J ∞ = (∞ : OnePoint ℂ) := by
  rw [uniformizingMap, OnePoint.equivProjectivization_symm_apply_mk]
  simp [(chosenSection_spec J ∞).2.2]

/-- **`σ(J)` is injective.** If `σ(J) x = σ(J) y`, the element `t y • s - s y • t` of
`twistOneKernel J` is nonzero and vanishes at `x` and at `y`, so `x = y`. -/
theorem injective_uniformizingMap (J : 𝒥) : Function.Injective (uniformizingMap J) := by
  obtain ⟨hs, hs', h₀⟩ := chosenSection_spec J (0 : ℂ)
  obtain ⟨ht, ht', hinf⟩ := chosenSection_spec J ∞
  set s := chosenSection J (0 : ℂ)
  set t := chosenSection J ∞
  have hi := OnePoint.compatible_fubiniStudyForm.tames
  have hs₁ := apply_ne_zero_of_mem_twistOneKernel J.property hi hs hs' h₀ (y := (1 : ℂ)) (by simp)
  have ht₁ := apply_ne_zero_of_mem_twistOneKernel J.property hi ht ht' hinf (y := (1 : ℂ))
    (by simp)
  have ht0 := apply_ne_zero_of_mem_twistOneKernel J.property hi ht ht' hinf (y := (0 : ℂ))
    (by simp)
  have hsinf := apply_ne_zero_of_mem_twistOneKernel J.property hi hs hs' h₀ (y := ∞) (by simp)
  intro x y hxy
  rw [uniformizingMap, uniformizingMap, Equiv.apply_eq_iff_eq,
    Projectivization.mk_eq_mk_iff'] at hxy
  obtain ⟨c, hc⟩ := hxy
  have hx₀ : s x = c * s y := by
    have := congrFun hc 0
    simp only [Pi.smul_apply, Matrix.cons_val_zero, smul_eq_mul] at this
    exact mul_right_cancel₀ ht₁ (by rw [← this]; ring)
  have hxinf : t x = c * t y := by
    have := congrFun hc 1
    simp only [Pi.smul_apply, Matrix.cons_val_one, Matrix.cons_val_zero, smul_eq_mul] at this
    exact mul_right_cancel₀ hs₁ (by rw [← this]; ring)
  -- The section `w = t y • s - s y • t` vanishes at `x` and at `y`.
  set w : OnePoint ℂ → ℂ := t y • s - s y • t
  have hw : w ∈ twistOneKernel J.val :=
    sub_mem (Submodule.smul_mem _ _ hs) (Submodule.smul_mem _ _ ht)
  have hwy : w y = 0 := by simp [w, mul_comm]
  have hwx : w x = 0 := by simp [w, hx₀, hxinf]; ring
  -- It is nonzero: otherwise `s y = t y = 0`, against `vec_ne_zero_of_mem_twistOneKernel`.
  have hw' : w ≠ 0 := by
    intro h
    have e0 := congrFun h (0 : ℂ)
    have einf := congrFun h ∞
    simp only [w, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, h₀, hinf, mul_zero, sub_zero,
      zero_sub, Pi.zero_apply, neg_eq_zero] at e0 einf
    refine vec_ne_zero_of_mem_twistOneKernel J.property hi hs ht hs' ht' h₀ hinf y ?_
    simp [(mul_eq_zero.1 e0).resolve_right ht0, (mul_eq_zero.1 einf).resolve_right hsinf]
  exact eq_of_mem_twistOneKernel_of_eq_zero J.property hi hw hw' hwx hwy

/-- `σ(J)` in terms of the chosen sections, as a value of `OnePoint ℂ`. -/
private theorem uniformizingMap_eq_ite (J : 𝒥) (p : OnePoint ℂ) : uniformizingMap J p =
    if chosenSection J ∞ p * chosenSection J (0 : ℂ) (1 : ℂ) = 0 then (∞ : OnePoint ℂ)
    else (((chosenSection J ∞ p * chosenSection J (0 : ℂ) (1 : ℂ))⁻¹ *
      (chosenSection J (0 : ℂ) p * chosenSection J ∞ (1 : ℂ)) : ℂ) : OnePoint ℂ) := by
  rw [uniformizingMap, OnePoint.equivProjectivization_symm_apply_mk]
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
  -- The two sides differ only in the decidability instances of their conditions.
  congr

open scoped VectorBundle.ComplexToReal in
/-- Near a point where the section `t` vanishing at `∞` does not vanish, `σ(J)` is the inclusion
of `ℂ` applied to `t 1 / s 1` times the quotient `s / t`. -/
private theorem uniformizingMap_eventuallyEq_coe (J : 𝒥) {x : OnePoint ℂ}
    (hx : chosenSection J ∞ x ≠ 0) :
    uniformizingMap J =ᶠ[𝓝 x] (↑) ∘ fun p ↦
      chosenSection J ∞ (1 : ℂ) / chosenSection J (0 : ℂ) (1 : ℂ) *
        (chosenSection J (0 : ℂ) p / chosenSection J ∞ p) := by
  obtain ⟨hs, hs', h₀⟩ := chosenSection_spec J (0 : ℂ)
  have ht := (chosenSection_spec J ∞).1
  have hs₁ := apply_ne_zero_of_mem_twistOneKernel J.property
    OnePoint.compatible_fubiniStudyForm.tames hs hs' h₀ (y := (1 : ℂ)) (by simp)
  have htm := ((mem_twistOneKernel_iff J.val).1 ht).1
  filter_upwards [(htm x).continuousAt.preimage_mem_nhds
    ((TauCeti.isOpen_zeroSectionCompl ℂ _).mem_nhds (mem_zeroSectionCompl.2 hx))] with p hp
  replace hp : chosenSection J ∞ p ≠ 0 := mem_zeroSectionCompl.1 hp
  rw [Function.comp_apply, uniformizingMap_eq_ite, ite_eq_right (mul_ne_zero hp hs₁)]
  congr 1
  field_simp

open scoped VectorBundle.ComplexToReal in
/-- Near a point where the section `s` vanishing at `0` does not vanish, `σ(J)` is the inverse of
the inverted chart applied to `s 1 / t 1` times the quotient `t / s`. -/
private theorem uniformizingMap_eventuallyEq_invChart_symm (J : 𝒥) {x : OnePoint ℂ}
    (hx : chosenSection J (0 : ℂ) x ≠ 0) :
    uniformizingMap J =ᶠ[𝓝 x] OnePoint.invChart.symm ∘ fun p ↦
      chosenSection J (0 : ℂ) (1 : ℂ) / chosenSection J ∞ (1 : ℂ) *
        (chosenSection J ∞ p / chosenSection J (0 : ℂ) p) := by
  obtain ⟨hs, hs', h₀⟩ := chosenSection_spec J (0 : ℂ)
  obtain ⟨ht, ht', hinf⟩ := chosenSection_spec J ∞
  have hi := OnePoint.compatible_fubiniStudyForm.tames
  have hs₁ := apply_ne_zero_of_mem_twistOneKernel J.property hi hs hs' h₀ (y := (1 : ℂ)) (by simp)
  have ht₁ := apply_ne_zero_of_mem_twistOneKernel J.property hi ht ht' hinf (y := (1 : ℂ))
    (by simp)
  have hsm := ((mem_twistOneKernel_iff J.val).1 hs).1
  filter_upwards [(hsm x).continuousAt.preimage_mem_nhds
    ((TauCeti.isOpen_zeroSectionCompl ℂ _).mem_nhds (mem_zeroSectionCompl.2 hx))] with p hp
  replace hp : chosenSection J (0 : ℂ) p ≠ 0 := mem_zeroSectionCompl.1 hp
  rw [Function.comp_apply, uniformizingMap_eq_ite]
  by_cases htp : chosenSection J ∞ p = 0
  · simp [htp]
  · have hne : chosenSection J (0 : ℂ) (1 : ℂ) / chosenSection J ∞ (1 : ℂ) *
        (chosenSection J ∞ p / chosenSection J (0 : ℂ) p) ≠ 0 := by simp [*]
    rw [ite_eq_right (mul_ne_zero htp hs₁), OnePoint.invChart_symm_of_ne_zero hne]
    congr 1
    field_simp

open scoped VectorBundle.ComplexToReal in
/-- A constant multiple of the quotient of two chosen sections is smooth where the denominator
does not vanish. -/
private theorem contMDiffAt_const_mul_div_chosenSection (J : 𝒥) (c : ℂ) {a b : OnePoint ℂ}
    {x : OnePoint ℂ} (hx : chosenSection J b x ≠ 0) :
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞)
      (fun p ↦ c * (chosenSection J a p / chosenSection J b p)) x :=
  contMDiffAt_const.mul (OnePoint.contMDiffAt_div_twistCore 1
    (((mem_twistOneKernel_iff J.val).1 (chosenSection_spec J a).1).1 x)
    (((mem_twistOneKernel_iff J.val).1 (chosenSection_spec J b).1).1 x) hx)

/-- **`σ(J)` is smooth.** The uniformizing map of a structure `J` tamed by the Fubini–Study form
is a smooth map from the sphere to itself, for its structure as a real surface. -/
theorem contMDiff_uniformizingMap (J : 𝒥) :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) (uniformizingMap J) := by
  intro x
  by_cases hx : chosenSection J ∞ x = 0
  · -- Near `x`, where `s` does not vanish, `σ(J)` reads through the inverted chart.
    have hsx : chosenSection J (0 : ℂ) x ≠ 0 := fun h ↦
      chosenSection_vec_ne_zero J x (by simp [h, hx])
    exact (OnePoint.contMDiff_invChart_symm_real.contMDiffAt.comp x
      (contMDiffAt_const_mul_div_chosenSection J _ (a := ∞) hsx)).congr_of_eventuallyEq
      (uniformizingMap_eventuallyEq_invChart_symm J hsx)
  · -- Near `x`, where `t` does not vanish, `σ(J)` reads through the inclusion of `ℂ`.
    exact (OnePoint.contMDiff_coe_real.contMDiffAt.comp x
      (contMDiffAt_const_mul_div_chosenSection J _ (a := (0 : ℂ)) hx)).congr_of_eventuallyEq
      (uniformizingMap_eventuallyEq_coe J hx)

/-- A constant multiple of a quotient of functions, as the quotient of a multiple. -/
private theorem const_mul_div_eq_smul_div (c : ℂ) (u v : OnePoint ℂ → ℂ) :
    (fun p ↦ c * (u p / v p)) = fun p ↦ (c • u) p / v p :=
  funext fun p ↦ by rw [Pi.smul_apply, smul_eq_mul, mul_div_assoc]

/-- For nonzero `u, v` in `twistOneKernel J` with `u y = 0 ≠ v y`, and `c ≠ 0`, the map
`p ↦ c * (u p / v p)` has injective real derivative at every `x` with `v x ≠ 0`. -/
private theorem injective_mfderiv_const_mul_div (J : 𝒥) {u v : OnePoint ℂ → ℂ}
    (hu : u ∈ twistOneKernel J.val) (hv : v ∈ twistOneKernel J.val) (hu₀ : u ≠ 0) {c : ℂ}
    (hc : c ≠ 0) {y : OnePoint ℂ} (huy : u y = 0) (hvy : v y ≠ 0) {x : OnePoint ℂ}
    (hx : v x ≠ 0) :
    Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun p ↦ c * (u p / v p)) x) := by
  rw [const_mul_div_eq_smul_div]
  refine injective_mfderiv_div_of_mem_twistOneKernel J.property
    OnePoint.compatible_fubiniStudyForm.tames (Submodule.smul_mem _ c hu) hv (fun d hd ↦ ?_) hx
  have h := congrFun hd y
  simp only [Pi.smul_apply, smul_eq_mul, huy, mul_zero] at h
  rw [(mul_eq_zero.1 h.symm).resolve_right hvy, zero_smul, smul_eq_zero] at hd
  exact hu₀ (hd.resolve_left hc)

/-- **`σ(J)` is a local diffeomorphism.** The uniformizing map of a structure `J` tamed by the
Fubini–Study form is a smooth local diffeomorphism from the sphere to itself, for its structure
as a real surface. -/
theorem isLocalDiffeomorph_uniformizingMap (J : 𝒥) :
    IsLocalDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) (uniformizingMap J) := by
  obtain ⟨hs, hs', h₀⟩ := chosenSection_spec J (0 : ℂ)
  obtain ⟨ht, ht', hinf⟩ := chosenSection_spec J ∞
  have hi := OnePoint.compatible_fubiniStudyForm.tames
  have hs₁ := apply_ne_zero_of_mem_twistOneKernel J.property hi hs hs' h₀ (y := (1 : ℂ)) (by simp)
  have ht₁ := apply_ne_zero_of_mem_twistOneKernel J.property hi ht ht' hinf (y := (1 : ℂ))
    (by simp)
  have ht0 := apply_ne_zero_of_mem_twistOneKernel J.property hi ht ht' hinf (y := (0 : ℂ))
    (by simp)
  have hsinf := apply_ne_zero_of_mem_twistOneKernel J.property hi hs hs' h₀ (y := ∞) (by simp)
  intro x
  refine isLocalDiffeomorphAt_of_injective_mfderiv (contMDiff_uniformizingMap J).contMDiffOn
    isOpen_univ (Set.mem_univ x) BoundarylessManifold.isInteriorPoint (by simp) ?_ rfl
  by_cases hx : chosenSection J ∞ x = 0
  · -- Near `x`, `σ(J)` is the inverse of the inverted chart after a quotient of sections.
    have hsx : chosenSection J (0 : ℂ) x ≠ 0 := fun h ↦
      chosenSection_vec_ne_zero J x (by simp [h, hx])
    set q := fun p ↦ chosenSection J (0 : ℂ) (1 : ℂ) / chosenSection J ∞ (1 : ℂ) *
      (chosenSection J ∞ p / chosenSection J (0 : ℂ) p)
    -- The inverse of the inverted chart is the inverse of the extended chart at `∞`.
    have hg : IsLocalDiffeomorphAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) OnePoint.invChart.symm (q x) := by
      simpa using isLocalDiffeomorphAt_extChartAt_symm (I := 𝓘(ℝ, ℂ)) (n := (⊤ : ℕ∞))
        (x := (∞ : OnePoint ℂ)) (z := q x) (by simp)
    rw [(uniformizingMap_eventuallyEq_invChart_symm J hsx).mfderiv_eq,
      mfderiv_comp x (hg.mdifferentiableAt (by simp))
        ((contMDiffAt_const_mul_div_chosenSection J _ (a := ∞) hsx).mdifferentiableAt (by simp))]
    exact (hg.isInvertible_mfderiv (by simp)).injective.comp
      (injective_mfderiv_const_mul_div J ht hs ht' (div_ne_zero hs₁ ht₁) hinf hsinf hsx)
  · -- Near `x`, `σ(J)` is the inclusion of `ℂ` after a quotient of sections.
    rw [(uniformizingMap_eventuallyEq_coe J hx).mfderiv_eq,
      mfderiv_comp x (OnePoint.hasMFDerivAt_coe _).mdifferentiableAt
        ((contMDiffAt_const_mul_div_chosenSection J _ (a := (0 : ℂ)) hx).mdifferentiableAt
          (by simp)),
      (OnePoint.hasMFDerivAt_coe _).mfderiv]
    exact injective_mfderiv_const_mul_div J hs ht hs' (div_ne_zero ht₁ hs₁) h₀ ht0 hx

/-- **`σ(J)` is bijective.** It is injective, and its range is open, since `σ(J)` is a local
diffeomorphism, closed, as the image of the compact sphere, and nonempty, so it is the whole
sphere, which is connected. -/
theorem bijective_uniformizingMap (J : 𝒥) : Function.Bijective (uniformizingMap J) :=
  ⟨injective_uniformizingMap J, Set.range_eq_univ.1 <|
    IsClopen.eq_univ ⟨(isCompact_range (contMDiff_uniformizingMap J).continuous).isClosed,
      (isLocalDiffeomorph_uniformizingMap J).isOpen_range⟩ (Set.range_nonempty _)⟩

/-- For `u, v` in `twistOneKernel J` and a constant `c`, the map `p ↦ c * (u p / v p)` is
pseudoholomorphic from `J` to the standard structure of `ℂ` at every `x` with `v x ≠ 0`. -/
private theorem isPseudoholomorphicAt_const_mul_div (J : 𝒥) {u v : OnePoint ℂ → ℂ}
    (hu : u ∈ twistOneKernel J.val) (hv : v ∈ twistOneKernel J.val) (c : ℂ) {x : OnePoint ℂ}
    (hx : v x ≠ 0) :
    IsPseudoholomorphicAt J.val (SmoothAlmostComplexStructure.ofComplexManifold ℂ ℂ)
      (fun p ↦ c * (u p / v p)) x := by
  rw [const_mul_div_eq_smul_div]
  exact isPseudoholomorphicAt_div_of_mem_twistOneKernel (Submodule.smul_mem _ c hu) hv hx

/-- **`σ(J)` is pseudoholomorphic** from `J` to the complex structure `i` of the Riemann sphere:
its derivative intertwines `J` and `i`. -/
theorem isPseudoholomorphic_uniformizingMap (J : 𝒥) :
    IsPseudoholomorphic J.val (SmoothAlmostComplexStructure.ofComplexManifold ℂ (OnePoint ℂ))
      (uniformizingMap J) := by
  have hs := (chosenSection_spec J (0 : ℂ)).1
  have ht := (chosenSection_spec J ∞).1
  refine isPseudoholomorphic_iff.2 fun x ↦ ?_
  by_cases hx : chosenSection J ∞ x = 0
  · -- Near `x`, `σ(J)` is the inverse of the inverted chart after a quotient of sections.
    have hsx : chosenSection J (0 : ℂ) x ≠ 0 := fun h ↦
      chosenSection_vec_ne_zero J x (by simp [h, hx])
    refine IsPseudoholomorphicAt.congr_of_eventuallyEq ?_
      (uniformizingMap_eventuallyEq_invChart_symm J hsx)
    exact (isPseudoholomorphicAt_ofComplexManifold_iff.2
      ((OnePoint.contMDiff_invChart_symm (𝕜 := ℂ)).mdifferentiableAt (by simp))).comp
      (isPseudoholomorphicAt_const_mul_div J ht hs _ hsx)
  · -- Near `x`, `σ(J)` is the inclusion of `ℂ` after a quotient of sections.
    refine IsPseudoholomorphicAt.congr_of_eventuallyEq ?_ (uniformizingMap_eventuallyEq_coe J hx)
    exact (isPseudoholomorphicAt_ofComplexManifold_iff.2
      ((OnePoint.contMDiff_coe (𝕜 := ℂ)).mdifferentiableAt (by simp))).comp
      (isPseudoholomorphicAt_const_mul_div J hs ht _ hx)

/-- `σ(J)` as a diffeomorphism of the sphere, before its membership in `diffPlus` is known. -/
private noncomputable def uniformizingDiffeomorphAux (J : 𝒥) :
    TauCeti.Diff 𝓘(ℝ, ℂ) (OnePoint ℂ) ((⊤ : ℕ∞) : ℕ∞ω) :=
  (isLocalDiffeomorph_uniformizingMap J).diffeomorphOfBijective (bijective_uniformizingMap J)

private theorem pullback_uniformizingDiffeomorphAux (J : 𝒥) :
    (SmoothAlmostComplexStructure.ofComplexManifold ℂ (OnePoint ℂ)).pullback
      (uniformizingDiffeomorphAux J) = J.val := by
  rw [← SmoothAlmostComplexStructure.localPullback_eq_pullback, eq_comm,
    SmoothAlmostComplexStructure.eq_localPullback_iff_isPseudoholomorphic,
    uniformizingDiffeomorphAux, IsLocalDiffeomorph.coe_diffeomorphOfBijective]
  exact isPseudoholomorphic_uniformizingMap J

/-- **The uniformizing diffeomorphism** `σ(J)` of a structure `J` tamed by the Fubini–Study form:
the bijective local diffeomorphism `uniformizingMap J`, as an element of `diffPlus`. It lies in
`diffPlus` because it pulls `i` back to `J` (`pullback_uniformizingDiffeomorph`), which the
Fubini–Study form tames. -/
noncomputable def uniformizingDiffeomorph (J : 𝒥) : diffPlus :=
  ⟨uniformizingDiffeomorphAux J, mem_diffPlus_iff_tames_pullback.2 <| by
    rw [pullback_uniformizingDiffeomorphAux]
    exact J.property⟩

/-- The underlying map of `uniformizingDiffeomorph J` is `uniformizingMap J`. -/
@[simp]
theorem coe_uniformizingDiffeomorph (J : 𝒥) :
    ⇑(uniformizingDiffeomorph J : TauCeti.Diff 𝓘(ℝ, ℂ) (OnePoint ℂ) ((⊤ : ℕ∞) : ℕ∞ω)) =
      uniformizingMap J := by
  rw [uniformizingDiffeomorph, Subgroup.coe_mk, uniformizingDiffeomorphAux,
    IsLocalDiffeomorph.coe_diffeomorphOfBijective]

/-- **`σ(J)` pulls `i` back to `J`**: `σ(J)^* i = J`. -/
@[simp]
theorem pullback_uniformizingDiffeomorph (J : 𝒥) :
    (SmoothAlmostComplexStructure.ofComplexManifold ℂ (OnePoint ℂ)).pullback
      (uniformizingDiffeomorph J) = J.val := by
  rw [uniformizingDiffeomorph, Subgroup.coe_mk, pullback_uniformizingDiffeomorphAux]

/-- `uniformizingDiffeomorph` is a section of `complexStructureMap`, the map `φ ↦ φ^* i` from
`diffPlus` to the structures tamed by the Fubini–Study form. -/
@[simp]
theorem complexStructureMap_uniformizingDiffeomorph (J : 𝒥) :
    complexStructureMap (uniformizingDiffeomorph J) = J :=
  Subtype.ext ((coe_complexStructureMap _).trans (pullback_uniformizingDiffeomorph J))

end SymplecticGeometry

end
