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
import SymplecticGeometry.Geometry.Diffeomorphism.Sphere.Mobius
import SymplecticGeometry.Geometry.Manifold.Instances.OnePoint.RatioMap
import SymplecticGeometry.Geometry.Symplectic.Manifold.AlmostComplex.Pullback
import TauCeti.Geometry.Manifold.Algebra.ComplexSmoothFunctions
import TauCeti.Geometry.Manifold.Instances.OnePoint.Automorphism
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Section.ScalarTopology
import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Descent
import SymplecticGeometry.Topology.FiberBundle.Basic

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
* `SymplecticGeometry.contMDiff_uniformizingMap`: `σ(J)` is smooth. The multiples
  `s' = s · t 1` and `t' = t · s 1` lie in `E_J`, so they are smooth sections of `𝒪(1)` without
  common zero, and `σ(J)` is their map `x ↦ [s' x : t' x]`, which is smooth by
  `OnePoint.contMDiff_equivProjectivization_symm_mk_twistCore`. Near a point where `t'` does not
  vanish, `σ(J)` is the inclusion of `ℂ` applied to `s' / t'`
  (`OnePoint.equivProjectivization_symm_mk_eventuallyEq_coe_div`), and near a point where `s'`
  does not vanish it is the inverse of the inverted chart applied to `t' / s'`
  (`OnePoint.equivProjectivization_symm_mk_eventuallyEq_invChart_symm_div`).
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
* `SymplecticGeometry.eq_uniformizingDiffeomorph_iff`: a diffeomorphism `φ` of the sphere is
  `σ(J)` exactly when `φ^* i = J` and `φ` fixes `0`, `1` and `∞`. Indeed `φ ∘ σ(J)⁻¹` pulls `i`
  back to itself, so it is a Möbius transformation
  (`SymplecticGeometry.pullback_ofComplexManifold_onePoint_eq_self_iff`), and a Möbius
  transformation fixing `0`, `1` and `∞` is the identity (Tau Ceti's
  `Diffeomorph.eq_refl_of_apply_zero_one_infty_eq_self`). Hence
  `SymplecticGeometry.uniformizingDiffeomorph_ofComplexManifold`: `σ(i) = 1`.
* `SymplecticGeometry.exists_continuousAt_mem_twistOneKernel_eq_zero`: near a structure `J₀`, one
  can pick, continuously in `J`, a smooth section of `𝒪(1)` in `E_J` that is nonzero and has
  a zero at a given point `p`. With the family `T_J` of
  `SymplecticGeometry.exists_continuousAt_twistOneKernelFamily` and a basis `a, b` of `E_{J₀}`,
  it is `T_J b (p) • T_J a - T_J a (p) • T_J b`. As `T_J` is injective, it is nonzero once
  `T_J a` and `T_J b` do not both vanish at `p`. This holds at `J₀`, since `a` and `b` are
  not proportional (`SymplecticGeometry.exists_smul_eq_of_mem_twistOneKernel`), and so near
  `J₀`, since evaluation at `p` is continuous on smooth sections.
* `SymplecticGeometry.continuous_uniformizingDiffeomorph`: `J ↦ σ(J)` is continuous from the
  `C^∞` topology of a covering frame system to the weak Whitney topology on `diffPlus`. Near a
  structure `J₀`, take the families `s` and `t` of the previous item for `p = 0` and `p = ∞`.
  By `SymplecticGeometry.uniformizingMap_eq`, `σ(J)` is then the map `[t 1 · s : s 1 · t]` of
  the pair of sections `(t 1 • s, s 1 • t)`, which is continuous at `J₀` since evaluation at `1`
  is continuous. The map from such pairs to smooth maps of the sphere is continuous
  (`OnePoint.continuous_ratioMap`), and the weak Whitney topology on diffeomorphisms is induced
  from that on maps (`Diffeomorph.continuous_weakWhitney_iff`).

## References

* [D. McDuff, D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd
  ed.][McDuffSalamon2012] (Riemann–Roch for real Cauchy–Riemann operators on line bundles over
  the sphere).
* [M. W. Hirsch, *Differential Topology*][Hirsch1976], Chapter 2, §1 (the weak topology on
  spaces of maps).
-/

public section

open scoped OnePoint SymplecticGeometry Manifold ContDiff Topology TauCeti.ComplexManifold
  TauCeti.DiffeomorphWeakWhitney TauCeti.ManifoldWeakWhitney
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

/-- `σ(J)` as the map `x ↦ [s' x : t' x]`, read through `OnePoint.equivProjectivization`, for
the multiples `s' = s · t 1` and `t' = t · s 1` of the chosen sections `s` and `t`. -/
private theorem uniformizingMap_def (J : 𝒥) : uniformizingMap J = fun x ↦
    (OnePoint.equivProjectivization ℂ).symm (Projectivization.mk ℂ
      ![chosenSection J (0 : ℂ) x * chosenSection J ∞ (1 : ℂ),
        chosenSection J ∞ x * chosenSection J (0 : ℂ) (1 : ℂ)] (chosenSection_vec_ne_zero J x)) :=
  (rfl)

/-- A chosen section times a constant lies in `twistOneKernel J`. -/
private theorem chosenSection_mul_const_mem (J : 𝒥) (a : OnePoint ℂ) (c : ℂ) :
    (fun p ↦ chosenSection J a p * c) ∈ twistOneKernel J.val := by
  convert Submodule.smul_mem _ c (chosenSection_spec J a).1 using 1
  funext p
  simp [mul_comm]

/-- **`σ(J)` is smooth.** The uniformizing map of a structure `J` tamed by the Fubini–Study form
is a smooth map from the sphere to itself, for its structure as a real surface. -/
theorem contMDiff_uniformizingMap (J : 𝒥) :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) (uniformizingMap J) := by
  rw [uniformizingMap_def]
  exact OnePoint.contMDiff_equivProjectivization_symm_mk_twistCore
    ((mem_twistOneKernel_iff J.val).1 (chosenSection_mul_const_mem J (0 : ℂ) _)).1
    ((mem_twistOneKernel_iff J.val).1 (chosenSection_mul_const_mem J ∞ _)).1 _

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
  have hu := chosenSection_mul_const_mem J (0 : ℂ) (chosenSection J ∞ (1 : ℂ))
  have hv := chosenSection_mul_const_mem J ∞ (chosenSection J (0 : ℂ) (1 : ℂ))
  have hum := ((mem_twistOneKernel_iff J.val).1 hu).1
  have hvm := ((mem_twistOneKernel_iff J.val).1 hv).1
  intro x
  refine isLocalDiffeomorphAt_of_injective_mfderiv (contMDiff_uniformizingMap J).contMDiffOn
    isOpen_univ (Set.mem_univ x) BoundarylessManifold.isInteriorPoint (by simp) ?_ rfl
  rw [uniformizingMap_def]
  by_cases hx : chosenSection J ∞ x = 0
  · -- Near `x`, `σ(J)` is the inverse of the inverted chart after a quotient of sections.
    have hux : chosenSection J (0 : ℂ) x * chosenSection J ∞ (1 : ℂ) ≠ 0 :=
      mul_ne_zero (fun h ↦ chosenSection_vec_ne_zero J x (by simp [h, hx])) ht₁
    set q := fun p ↦ chosenSection J ∞ p * chosenSection J (0 : ℂ) (1 : ℂ) /
      (chosenSection J (0 : ℂ) p * chosenSection J ∞ (1 : ℂ))
    -- The inverse of the inverted chart is the inverse of the extended chart at `∞`.
    have hg : IsLocalDiffeomorphAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) OnePoint.invChart.symm (q x) := by
      simpa using isLocalDiffeomorphAt_extChartAt_symm (I := 𝓘(ℝ, ℂ)) (n := (⊤ : ℕ∞))
        (x := (∞ : OnePoint ℂ)) (z := q x) (by simp)
    rw [(OnePoint.equivProjectivization_symm_mk_eventuallyEq_invChart_symm_div
        (chosenSection_vec_ne_zero J) (hum x).continuousAt hux).mfderiv_eq,
      mfderiv_comp x (hg.mdifferentiableAt (by simp))
        ((OnePoint.contMDiffAt_div_twistCore 1 (hvm x) (hum x) hux).mdifferentiableAt (by simp))]
    exact (hg.isInvertible_mfderiv (by simp)).injective.comp
      (injective_mfderiv_div_of_mem_twistOneKernel J.property hi hv hu
        (fun c h ↦ by simpa [h₀, ht0, hs₁] using congrFun h (0 : ℂ)) hux)
  · -- Near `x`, `σ(J)` is the inclusion of `ℂ` after a quotient of sections.
    have hvx : chosenSection J ∞ x * chosenSection J (0 : ℂ) (1 : ℂ) ≠ 0 := mul_ne_zero hx hs₁
    rw [(OnePoint.equivProjectivization_symm_mk_eventuallyEq_coe_div
        (chosenSection_vec_ne_zero J) (hvm x).continuousAt hvx).mfderiv_eq,
      mfderiv_comp x (OnePoint.hasMFDerivAt_coe _).mdifferentiableAt
        ((OnePoint.contMDiffAt_div_twistCore 1 (hum x) (hvm x) hvx).mdifferentiableAt (by simp)),
      (OnePoint.hasMFDerivAt_coe _).mfderiv]
    exact injective_mfderiv_div_of_mem_twistOneKernel J.property hi hu hv
      (fun c h ↦ by simpa [hinf, hsinf, ht₁] using congrFun h ∞) hvx

/-- **`σ(J)` is bijective.** It is injective, and its range is open, since `σ(J)` is a local
diffeomorphism, closed, as the image of the compact sphere, and nonempty, so it is the whole
sphere, which is connected. -/
theorem bijective_uniformizingMap (J : 𝒥) : Function.Bijective (uniformizingMap J) :=
  ⟨injective_uniformizingMap J, Set.range_eq_univ.1 <|
    IsClopen.eq_univ ⟨(isCompact_range (contMDiff_uniformizingMap J).continuous).isClosed,
      (isLocalDiffeomorph_uniformizingMap J).isOpen_range⟩ (Set.range_nonempty _)⟩

/-- **`σ(J)` is pseudoholomorphic** from `J` to the complex structure `i` of the Riemann sphere:
its derivative intertwines `J` and `i`. -/
theorem isPseudoholomorphic_uniformizingMap (J : 𝒥) :
    IsPseudoholomorphic J.val (SmoothAlmostComplexStructure.ofComplexManifold ℂ (OnePoint ℂ))
      (uniformizingMap J) := by
  have hi := OnePoint.compatible_fubiniStudyForm.tames
  obtain ⟨hs, hs', h₀⟩ := chosenSection_spec J (0 : ℂ)
  obtain ⟨ht, ht', hinf⟩ := chosenSection_spec J ∞
  have hs₁ := apply_ne_zero_of_mem_twistOneKernel J.property hi hs hs' h₀ (y := (1 : ℂ)) (by simp)
  have ht₁ := apply_ne_zero_of_mem_twistOneKernel J.property hi ht ht' hinf (y := (1 : ℂ))
    (by simp)
  have hu := chosenSection_mul_const_mem J (0 : ℂ) (chosenSection J ∞ (1 : ℂ))
  have hv := chosenSection_mul_const_mem J ∞ (chosenSection J (0 : ℂ) (1 : ℂ))
  rw [uniformizingMap_def]
  refine isPseudoholomorphic_iff.2 fun x ↦ ?_
  by_cases hx : chosenSection J ∞ x = 0
  · -- Near `x`, `σ(J)` is the inverse of the inverted chart after a quotient of sections.
    have hux : chosenSection J (0 : ℂ) x * chosenSection J ∞ (1 : ℂ) ≠ 0 :=
      mul_ne_zero (fun h ↦ chosenSection_vec_ne_zero J x (by simp [h, hx])) ht₁
    refine IsPseudoholomorphicAt.congr_of_eventuallyEq ?_
      (OnePoint.equivProjectivization_symm_mk_eventuallyEq_invChart_symm_div
        (chosenSection_vec_ne_zero J) (((mem_twistOneKernel_iff J.val).1 hu).1 x).continuousAt hux)
    exact (isPseudoholomorphicAt_ofComplexManifold_iff.2
      ((OnePoint.contMDiff_invChart_symm (𝕜 := ℂ)).mdifferentiableAt (by simp))).comp
      (isPseudoholomorphicAt_div_of_mem_twistOneKernel hv hu hux)
  · -- Near `x`, `σ(J)` is the inclusion of `ℂ` after a quotient of sections.
    have hvx : chosenSection J ∞ x * chosenSection J (0 : ℂ) (1 : ℂ) ≠ 0 := mul_ne_zero hx hs₁
    refine IsPseudoholomorphicAt.congr_of_eventuallyEq ?_
      (OnePoint.equivProjectivization_symm_mk_eventuallyEq_coe_div
        (chosenSection_vec_ne_zero J) (((mem_twistOneKernel_iff J.val).1 hv).1 x).continuousAt hvx)
    exact (isPseudoholomorphicAt_ofComplexManifold_iff.2
      ((OnePoint.contMDiff_coe (𝕜 := ℂ)).mdifferentiableAt (by simp))).comp
      (isPseudoholomorphicAt_div_of_mem_twistOneKernel hu hv hvx)

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

/-- **Uniqueness of `σ(J)`.** A diffeomorphism `φ` of the sphere is the uniformizing
diffeomorphism `σ(J)` exactly when it pulls the complex structure `i` back to `J` and fixes `0`,
`1` and `∞`. -/
theorem eq_uniformizingDiffeomorph_iff (J : 𝒥)
    {φ : TauCeti.Diff 𝓘(ℝ, ℂ) (OnePoint ℂ) ((⊤ : ℕ∞) : ℕ∞ω)} :
    φ = uniformizingDiffeomorph J ↔
      (SmoothAlmostComplexStructure.ofComplexManifold ℂ (OnePoint ℂ)).pullback φ = J.val ∧
        φ (0 : ℂ) = (0 : ℂ) ∧ φ (1 : ℂ) = (1 : ℂ) ∧ φ ∞ = (∞ : OnePoint ℂ) := by
  refine ⟨?_, fun ⟨hJ, h0, h1, hinf⟩ ↦ ?_⟩
  · rintro rfl
    simp
  set σ : TauCeti.Diff 𝓘(ℝ, ℂ) (OnePoint ℂ) ((⊤ : ℕ∞) : ℕ∞ω) := ↑(uniformizingDiffeomorph J)
  have hσ : ⇑σ = uniformizingMap J := coe_uniformizingDiffeomorph J
  -- `σ⁻¹` fixes `0`, `1` and `∞`, since `σ` does.
  have hσ0 : σ.symm (0 : ℂ) = (0 : ℂ) := σ.symm_apply_eq.2 (by simp [hσ])
  have hσ1 : σ.symm (1 : ℂ) = (1 : ℂ) := σ.symm_apply_eq.2 (by simp [hσ])
  have hσinf : σ.symm ∞ = (∞ : OnePoint ℂ) := σ.symm_apply_eq.2 (by simp [hσ])
  -- `φ ∘ σ⁻¹` pulls `i` back to itself, so it is a Möbius transformation `g`.
  obtain ⟨g, hg⟩ := (pullback_ofComplexManifold_onePoint_eq_self_iff (φ := σ.symm.trans φ)).1 <| by
    rw [SmoothAlmostComplexStructure.pullback_trans, hJ,
      SmoothAlmostComplexStructure.pullback_symm_eq_iff]
    exact pullback_uniformizingDiffeomorph J
  have hg' (x : OnePoint ℂ) : φ (σ.symm x) = g • x := by
    rw [← mobiusHom_apply, ← hg, Diffeomorph.coe_trans, Function.comp_apply]
  -- As `g` fixes `0`, `1` and `∞`, it acts as the identity.
  have hid :=
    (Diffeomorph.constSmul 𝓘(ℂ) (1 : WithTop ℕ∞) g).eq_refl_of_apply_zero_one_infty_eq_self
      one_ne_zero (by simp [← hg', hσ0, h0]) (by simp [← hg', hσ1, h1])
      (by simp [← hg', hσinf, hinf])
  refine Diffeomorph.ext fun x ↦ ?_
  simpa [← hg'] using congr($hid (σ x))

/-- **`σ(i) = 1`.** The uniformizing diffeomorphism of the complex structure `i` of the Riemann
sphere is the identity. -/
@[simp]
theorem uniformizingDiffeomorph_ofComplexManifold :
    uniformizingDiffeomorph tameOfComplexManifold = 1 := by
  refine Subtype.ext ((eq_uniformizingDiffeomorph_iff _).2 ?_).symm
  simp

/-! ### Kernel elements vanishing at a point, near a given structure -/

section Family

universe u

open Bundle
open OnePoint (twistCore)
open scoped VectorBundle.ComplexToReal

variable {σ : SmoothTwoForm 𝓘(ℝ, ℂ) (OnePoint ℂ)} {ι : Type*}
  (e : ι → Trivialization (ℂ →L[ℝ] ℂ) (π (ℂ →L[ℝ] ℂ) (fun x : OnePoint ℂ ↦
    TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] TangentSpace 𝓘(ℝ, ℂ) x)))
  [∀ i, MemTrivializationAtlas (e i)] (U : ι → TopologicalSpace.Opens (OnePoint ℂ))
  (hU : ∀ i, (U i : Set (OnePoint ℂ)) ⊆ (e i).baseSet)

/-- **Kernel elements vanishing at a point, continuous in the structure.** Let a two-form `σ` on
the sphere tame both `J₀` and the standard structure `i`, and give the structures tamed by `σ`
the subspace topology of `SmoothAlmostComplexStructure.frameTopology e U hU`, for frames whose
domains cover the sphere. For every point `p` of the sphere there is a family `S` of smooth
sections of `𝒪(1)` such that, for `J` near `J₀`, `S J` is a nonzero element of
`twistOneKernel J` vanishing at `p`, and `S` is continuous at `J₀` for
`ContMDiffSection.frameTopology e' U' hU'`, for every frame system `(e', U')` of `𝒪(1)`.

For `p = 0` and `p = ∞` this gives the two sections of the formula of `uniformizingMap_eq`,
chosen continuously in the structure. -/
theorem exists_continuousAt_mem_twistOneKernel_eq_zero (hcover : ∀ x, ∃ i, x ∈ U i)
    {J₀ : SmoothAlmostComplexStructure 𝓘(ℝ, ℂ) (OnePoint ℂ)} (hJ₀ : σ.Tames J₀)
    (hi : σ.Tames 𝒊) (p : OnePoint ℂ) :
    let _ := SmoothAlmostComplexStructure.frameTopology e U hU
    ∃ S : {J // σ.Tames J} →
        Cₛ^((⊤ : ℕ∞) : WithTop ℕ∞)⟮𝓘(ℝ, ℂ); ℂ, (twistCore (𝕜 := ℂ) 1).Fiber⟯,
      (∀ᶠ J in 𝓝 ⟨J₀, hJ₀⟩, ⇑(S J) ∈ twistOneKernel J.val ∧ ⇑(S J) ≠ 0 ∧ S J p = 0) ∧
      ∀ {κ : Type u} (e' : κ → Trivialization ℂ (π ℂ (twistCore (𝕜 := ℂ) 1).Fiber))
        [∀ i, MemTrivializationAtlas (e' i)] (U' : κ → TopologicalSpace.Opens (OnePoint ℂ))
        (hU' : ∀ i, (U' i : Set (OnePoint ℂ)) ⊆ (e' i).baseSet),
        letI := ContMDiffSection.frameTopology (I := 𝓘(ℝ, ℂ)) (n := ((⊤ : ℕ∞) : WithTop ℕ∞))
          e' U' hU'
        ContinuousAt S ⟨J₀, hJ₀⟩ := by
  intro _
  obtain ⟨T, hT, hT₀, hS⟩ :=
    exists_continuousAt_twistOneKernelFamily.{_, u} e U hU hcover hJ₀ hi
  have := finiteDimensional_twistOneKernel hJ₀ hi
  -- A basis `a, b` of the plane `twistOneKernel J₀`.
  let v := Module.finBasisOfFinrankEq ℂ _ (finrank_twistOneKernel hJ₀ hi)
  have hv : LinearIndependent ℂ ![v 0, v 1] := by
    convert v.linearIndependent
    ext i
    fin_cases i <;> rfl
  -- Evaluation at `p` is continuous for the frame at `p` alone, so `J ↦ T J s p` is continuous
  -- at `J₀`.
  let e₁ (_ : PUnit.{u + 1}) := trivializationAt ℂ (twistCore (𝕜 := ℂ) 1).Fiber p
  let U₁ (_ : PUnit.{u + 1}) : TopologicalSpace.Opens (OnePoint ℂ) := ⟨_, (e₁ ⟨⟩).open_baseSet⟩
  have hU₁ : ∀ x, (U₁ x : Set (OnePoint ℂ)) ⊆ (e₁ x).baseSet := fun _ ↦ subset_rfl
  have hev (s : twistOneKernel J₀) : ContinuousAt (fun J ↦ T J s p) ⟨J₀, hJ₀⟩ := by
    obtain ⟨S', hS', hS'c⟩ := hS s
    let := ContMDiffSection.frameTopology (I := 𝓘(ℝ, ℂ)) (n := ((⊤ : ℕ∞) : WithTop ℕ∞))
      e₁ U₁ hU₁
    refine (((ContMDiffSection.continuous_eval_const_of_mem e₁ U₁ hU₁ ⟨⟩
      (mem_baseSet_trivializationAt _ _ p)).continuousAt).comp (hS'c e₁ U₁ hU₁)).congr ?_
    filter_upwards [hS'] with J hJ using congrFun hJ p
  -- At `J₀`, `a` and `b` do not both vanish at `p`, since they are independent.
  have hl₀ : (T ⟨J₀, hJ₀⟩ (v 0) p, T ⟨J₀, hJ₀⟩ (v 1) p) ≠ 0 := by
    rw [hT₀, hT₀]
    refine prodMk_apply_ne_zero_of_mem_twistOneKernel hJ₀ hi (v 0).property (v 1).property ?_ p
    convert hv.map' _ (twistOneKernel J₀).ker_subtype
    ext i
    fin_cases i <;> rfl
  obtain ⟨Sa, hSa, hSac⟩ := hS (v 0)
  obtain ⟨Sb, hSb, hSbc⟩ := hS (v 1)
  let S (J : {J // σ.Tames J}) :
      Cₛ^((⊤ : ℕ∞) : WithTop ℕ∞)⟮𝓘(ℝ, ℂ); ℂ, (twistCore (𝕜 := ℂ) 1).Fiber⟯ :=
    T J (v 1) p • Sa J - T J (v 0) p • Sb J
  refine ⟨S, ?_, fun e' _ U' hU' ↦ ?_⟩
  · filter_upwards [hT, hSa, hSb, ((hev (v 0)).prodMk (hev (v 1))).eventually_ne hl₀]
      with J hJ ha hb hne
    -- The equation is stated for functions to `ℂ`, which is what each fibre of `𝒪(1)` is.
    have hSJ : @Eq (OnePoint ℂ → ℂ) ⇑(S J) (T J (T J (v 1) p • v 0 - T J (v 0) p • v 1)) := by
      simp only [S, ContMDiffSection.coe_sub, ContMDiffSection.coe_smul_of_normedAlgebra, ha,
        hb, map_sub, map_smul]
      -- The two sides differ only in the scalar action: on the fibres of `𝒪(1)`, and on `ℂ`.
      rfl
    refine ⟨?_, fun h ↦ hne ?_, ?_⟩
    · have hm : T J (T J (v 1) p • v 0 - T J (v 0) p • v 1) ∈ twistOneKernel J.val :=
        hJ.2 ▸ LinearMap.mem_range_self _ _
      exact hSJ ▸ hm
    · have h₀ : T J (T J (v 1) p • v 0 - T J (v 0) p • v 1) = T J 0 :=
        (hSJ.symm.trans h).trans (map_zero (T J)).symm
      have h₁ := LinearIndependent.pair_iff.1 hv (T J (v 1) p) (-T J (v 0) p)
        (by rw [neg_smul, ← sub_eq_add_neg]; exact hJ.1 h₀)
      exact Prod.ext (neg_eq_zero.1 h₁.2) h₁.1
    · refine (congrFun hSJ p).trans ?_
      exact (by simp [mul_comm] : T J (T J (v 1) p • v 0 - T J (v 0) p • v 1) p = (0 : ℂ))
  · let _ := ContMDiffSection.frameTopology (I := 𝓘(ℝ, ℂ)) (n := ((⊤ : ℕ∞) : WithTop ℕ∞))
      e' U' hU'
    have hg := ContMDiffSection.isTopologicalAddGroup_frameTopology (I := 𝓘(ℝ, ℂ))
      (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) e' U' hU'
    have := ContMDiffSection.continuousSMul_frameTopology_ofNormedAlgebra (𝕜' := ℂ)
      (I := 𝓘(ℝ, ℂ)) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) e' U' hU'
    -- Instance search does not derive this from `hg` here, so it is given by hand.
    have : ContinuousSub
        Cₛ^((⊤ : ℕ∞) : WithTop ℕ∞)⟮𝓘(ℝ, ℂ); ℂ, (twistCore (𝕜 := ℂ) 1).Fiber⟯ :=
      @IsTopologicalAddGroup.to_continuousSub _ _ _ hg
    exact ((hev (v 1)).smul (hSac e' U' hU')).sub ((hev (v 0)).smul (hSbc e' U' hU'))


/-! ### Continuity of `σ` -/

/-- **`σ` is continuous.** Give the structures tamed by the Fubini–Study form the subspace
topology of `SmoothAlmostComplexStructure.frameTopology e U hU`, for frames whose domains cover
the sphere, and `diffPlus` the weak Whitney topology. Then `J ↦ σ(J)` is continuous. -/
theorem continuous_uniformizingDiffeomorph (hcover : ∀ x, ∃ i, x ∈ U i) :
    letI := SmoothAlmostComplexStructure.frameTopology e U hU
    Continuous uniformizingDiffeomorph := by
  let _ := SmoothAlmostComplexStructure.frameTopology e U hU
  -- The frame system of `𝒪(1)` given by the trivializations at all points.
  let e' := trivializationAt ℂ (twistCore (𝕜 := ℂ) 1).Fiber
  let U' := FiberBundle.baseSetOpensAt ℂ (twistCore (𝕜 := ℂ) 1).Fiber
  have hU' := FiberBundle.baseSetOpensAt_subset_baseSet ℂ (twistCore (𝕜 := ℂ) 1).Fiber
  have hcover' := FiberBundle.exists_mem_baseSetOpensAt ℂ (twistCore (𝕜 := ℂ) 1).Fiber
  let _ := ContMDiffSection.frameTopology (I := 𝓘(ℝ, ℂ)) (n := ((⊤ : ℕ∞) : WithTop ℕ∞))
    e' U' hU'
  have := ContMDiffSection.continuousSMul_frameTopology_ofNormedAlgebra (𝕜' := ℂ)
    (I := 𝓘(ℝ, ℂ)) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) e' U' hU'
  have hev := ContMDiffSection.continuous_eval_const (I := 𝓘(ℝ, ℂ))
    (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) e' U' hU' hcover' (1 : ℂ)
  refine continuous_induced_rng.2 (Diffeomorph.continuous_weakWhitney_iff.2 ?_)
  refine continuous_iff_continuousAt.2 fun J₀ ↦ ?_
  have hi := OnePoint.compatible_fubiniStudyForm.tames
  obtain ⟨s, hs, hsc⟩ :=
    exists_continuousAt_mem_twistOneKernel_eq_zero.{0, _} e U hU hcover J₀.property hi (0 : ℂ)
  obtain ⟨t, ht, htc⟩ :=
    exists_continuousAt_mem_twistOneKernel_eq_zero.{0, _} e U hU hcover J₀.property hi ∞
  -- The pair `(t 1 • s, s 1 • t)` of sections, continuous at `J₀`.
  classical
  let a (J : 𝒥) : ℂ := s J (1 : ℂ)
  let b (J : 𝒥) : ℂ := t J (1 : ℂ)
  let P (J : 𝒥) := (b J • s J, a J • t J)
  -- The sections `s J` and `t J` as functions to `ℂ`, which each fibre of `𝒪(1)` is.
  let s' (J : 𝒥) : OnePoint ℂ → ℂ := s J
  let t' (J : 𝒥) : OnePoint ℂ → ℂ := t J
  have ha : ContinuousAt a J₀ := hev.continuousAt.comp (hsc e' U' hU')
  have hb : ContinuousAt b J₀ := hev.continuousAt.comp (htc e' U' hU')
  have hP : ContinuousAt P J₀ :=
    (hb.smul (hsc e' U' hU')).prodMk (ha.smul (htc e' U' hU'))
  -- On each fibre `ℂ` of `𝒪(1)`, the scalar action of `ℂ` is multiplication.
  have hPx (J : 𝒥) (x : OnePoint ℂ) : (![(P J).1 x, (P J).2 x] : Fin 2 → ℂ) =
      ![s' J x * b J, t' J x * a J] := by
    ext i
    fin_cases i
    · exact mul_comm (b J) (s J x)
    · exact mul_comm (a J) (t J x)
  have hgood : ∀ᶠ J in 𝓝 J₀, ∀ x, (![(P J).1 x, (P J).2 x] : Fin 2 → ℂ) ≠ 0 := by
    filter_upwards [hs, ht] with J hsJ htJ x
    rw [hPx]
    exact vec_ne_zero_of_mem_twistOneKernel J.property hi hsJ.1 htJ.1 hsJ.2.1 htJ.2.1
      hsJ.2.2 htJ.2.2 x
  -- The pair as a point of the domain of `OnePoint.ratioMap`, which it is near `J₀`.
  let Q (J : 𝒥) : {p : Cₛ^((⊤ : ℕ∞) : WithTop ℕ∞)⟮𝓘(ℝ, ℂ); ℂ, (twistCore (𝕜 := ℂ) 1).Fiber⟯ ×
      Cₛ^((⊤ : ℕ∞) : WithTop ℕ∞)⟮𝓘(ℝ, ℂ); ℂ, (twistCore (𝕜 := ℂ) 1).Fiber⟯ //
        ∀ x, (![p.1 x, p.2 x] : Fin 2 → ℂ) ≠ 0} :=
    if h : ∀ x, (![(P J).1 x, (P J).2 x] : Fin 2 → ℂ) ≠ 0 then ⟨P J, h⟩
    else ⟨P J₀, hgood.self_of_nhds⟩
  have hQ : ContinuousAt Q J₀ := by
    refine tendsto_subtype_rng.2 (hP.congr ?_)
    filter_upwards [hgood] with J hJ
    simp [Q, hJ]
  -- Near `J₀`, `σ(J)` is the map `[t 1 · s : s 1 · t]` of the pair, by `uniformizingMap_eq`.
  refine ((OnePoint.continuous_ratioMap e' U' hU' hcover').continuousAt.comp hQ).congr ?_
  filter_upwards [hs, ht, hgood] with J hsJ htJ hJ
  ext x
  rw [Function.comp_apply, Function.comp_apply, Diffeomorph.coe_toContMDiffMap,
    coe_uniformizingDiffeomorph, uniformizingMap_eq J hsJ.1 htJ.1 hsJ.2.1 htJ.2.1 hsJ.2.2 htJ.2.2,
    show Q J = ⟨P J, hJ⟩ by simp [Q, hJ], OnePoint.ratioMap_apply]
  congr 2
  exact hPx J x

end Family

end SymplecticGeometry

end
