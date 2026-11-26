/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import SymplecticGeometry.Geometry.Manifold.Instances.OnePoint.CauchyRiemann.Basic
public import SymplecticGeometry.Topology.VectorBundle.Core.Basic
public import TauCeti.Geometry.Manifold.Instances.OnePoint.LineBundle.Sections
import Mathlib.Geometry.Manifold.PartitionOfUnity
import SymplecticGeometry.Geometry.Manifold.Instances.OnePoint.Dolbeault
import TauCeti.Geometry.Manifold.ContMDiff.RestrictScalars
import TauCeti.Geometry.Manifold.VectorBundle.Scalar

/-!
# The Cauchy–Riemann operator of the standard structure on `𝒪(1)`

Let `D_i = SymplecticGeometry.twistOneDelBar 𝒊` be the real Cauchy–Riemann operator on the line
bundle `𝒪(1) = OnePoint.twistCore 1` over the Riemann sphere for its standard complex structure
`𝒊`. This file identifies the space `twistOneKernel 𝒊` of its smooth zeros with the space
`OnePoint.holomorphicTwistSections 1` of holomorphic sections of `𝒪(1)`, which has complex
dimension two, and shows that `D_i` is onto on smooth `(0,1)`-forms.

## Main results

* `SymplecticGeometry.twistOneDelBar_ofComplexManifold_eq_zero_iff`: at a point where a section
  of `𝒪(1)` is real differentiable, `D_i` vanishes exactly when the section is holomorphic there.
* `SymplecticGeometry.twistOneKernel_ofComplexManifold`: the smooth zeros of `D_i` are the
  holomorphic sections of `𝒪(1)`.
* `SymplecticGeometry.finrank_twistOneKernel_ofComplexManifold`: they form a complex vector space
  of dimension two.
* `OnePoint.contMDiff_div_smul_twistCore_hom`: multiplying a smooth `𝒪(k)`-valued one-form by
  `χ / σ`, for a smooth real function `χ` and a smooth section `σ` of `𝒪(k)` that does not vanish
  on the closed support of `χ`, gives a smooth complex valued one-form.
* `SymplecticGeometry.twistOneDelBar_ofComplexManifold_smul_apply`: `D_i (g σ) = (∂bar g) σ` for a
  holomorphic section `σ` of `𝒪(1)`.
* `SymplecticGeometry.exists_twistOneDelBar_eq`: every smooth `(0,1)`-form with values in `𝒪(1)`
  is `D_i s` for a smooth section `s`.

## Proof

In the frame of the chart at a point `x`, the `(0,1)`-part of the connection for `𝒊` is `∂bar` of
the coordinate of the section (`SymplecticGeometry.twistOneConnection_zeroOnePart_eq`), and
that frame is an isomorphism at `x`. By Tau Ceti's
`TauCeti.SmoothAlmostComplexStructure.dbarFunction_ofComplexManifold_eq_zero_iff`, `∂bar` of the
coordinate vanishes at `x` exactly when the coordinate is holomorphic at `x`, that is, when the
section is holomorphic at `x`. A holomorphic section of `𝒪(1)` is analytic
(`OnePoint.contMDiff_section_twistCore_iff_mdifferentiable`), hence smooth for the underlying real
structure; and Tau Ceti's `OnePoint.finrank_holomorphicTwistSections` gives the dimension.

For surjectivity, take a smooth partition of unity `χ_z + χ_1 = 1` on the sphere with `χ_z` zero
near `0` and `χ_1` zero near `∞`. The holomorphic sections `z` (`OnePoint.identitySection`) and
`1` (`OnePoint.monomialSection 1 0`) of `𝒪(1)` vanish only at `0` and only at `∞`, so
`β_z = (χ_z / z) α` and `β_1 = (χ_1 / 1) α` are smooth complex valued `(0,1)`-forms. The scalar
case `OnePoint.exists_contMDiff_dbarFunction_eq` gives smooth functions `g_z`, `g_1` with
`∂bar g_z = β_z` and `∂bar g_1 = β_1`. Since `D_i` kills holomorphic sections, the complex Leibniz
rule (`TauCeti.IsRealCauchyRiemannOperator.leibniz_complex`) gives
(`SymplecticGeometry.twistOneDelBar_ofComplexManifold_smul_apply`)
`D_i (g_z z + g_1 1) = (∂bar g_z) z + (∂bar g_1) 1 = χ_z α + χ_1 α = α`.

## References

* [D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*][McDuffSalamon2012],
  Appendix C.1.
-/

public section

open Bundle Filter Set TauCeti
open OnePoint (twistCore twistTransition)
open scoped Manifold ContDiff Topology TauCeti.ComplexManifold VectorBundle.ComplexToReal

namespace OnePoint

/-- Let `α` be a smooth one-form on the Riemann sphere with values in `𝒪(k)`, `σ` a smooth section
of `𝒪(k)` and `χ` a smooth real function such that `σ` does not vanish on the closed support of
`χ`. Then the complex valued one-form `(χ / σ) α`, which reads `α x` in `ℂ` through the
identification `VectorBundleCore.fiberEquiv` of the fibre with `ℂ` and is zero off the support
of `χ`, is smooth. -/
-- Inside `namespace OnePoint` the notation `∞` also names the point at infinity, so the
-- smoothness exponent `∞` is written as the cast of `⊤ : ℕ∞`.
theorem contMDiff_div_smul_twistCore_hom {k : ℤ}
    (α : ContMDiffSection 𝓘(ℝ, ℂ) (ℂ →L[ℝ] ℂ) ((⊤ : ℕ∞) : ℕ∞ω)
      (fun x : OnePoint ℂ ↦ TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] (twistCore (𝕜 := ℂ) k).Fiber x))
    {σ : OnePoint ℂ → ℂ}
    (hσ : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ)) ((⊤ : ℕ∞) : ℕ∞ω)
      (fun p ↦ TotalSpace.mk' ℂ (E := (twistCore (𝕜 := ℂ) k).Fiber) p (σ p)))
    {χ : OnePoint ℂ → ℝ} (hχ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) ((⊤ : ℕ∞) : ℕ∞ω) χ)
    (hχσ : ∀ x ∈ tsupport χ, σ x ≠ 0) :
    ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ →L[ℝ] ℂ)) ((⊤ : ℕ∞) : ℕ∞ω)
      (fun x ↦ TotalSpace.mk' (ℂ →L[ℝ] ℂ)
        (E := fun x : OnePoint ℂ ↦ TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] ℂ) x
        (((χ x : ℂ) / σ x) • (((twistCore (𝕜 := ℂ) k).fiberEquiv x :
          (twistCore (𝕜 := ℂ) k).Fiber x →L[ℂ] ℂ).restrictScalars ℝ).comp (α x))) := by
  intro x₀
  by_cases hx₀ : x₀ ∈ tsupport χ
  swap
  · have h0 : χ =ᶠ[𝓝 x₀] 0 := notMem_tsupport_iff_eventuallyEq.1 hx₀
    refine (contMDiff_zeroSection ℝ
      (fun x : OnePoint ℂ ↦ TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] ℂ) x₀).congr_of_eventuallyEq ?_
    filter_upwards [h0] with p hp
    simp [hp, zeroSection]
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  have hα := ((contMDiffAt_hom_bundle _).1 (α.contMDiff x₀)).2
  have hσ' := (contMDiffAt_section_iff x₀).1 (hσ x₀)
  set e := trivializationAt ℂ (twistCore (𝕜 := ℂ) k).Fiber x₀ with he
  have he' : e = (twistCore (𝕜 := ℂ) k).localTriv x₀ := by
    rw [he, VectorBundleCore.trivializationAt, ← VectorBundleCore.localTrivAt_def,
      OnePoint.twistCore_indexAt]
  have hr : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ((⊤ : ℕ∞) : ℕ∞ω) (fun p ↦ χ p • ((e ⟨p, σ p⟩).2)⁻¹) x₀ := by
    have hne : (e ⟨x₀, σ x₀⟩).2 ≠ 0 := by
      rw [he', twistCore_localTriv_apply, twistTransition_self, one_mul]
      exact hχσ x₀ hx₀
    exact (hχ x₀).smul (((contDiffAt_inv ℂ hne).restrict_scalars ℝ).contMDiffAt.comp x₀ hσ')
  refine ((contDiff_smul (𝕜 := ℝ) (𝕜' := ℂ) (F := ℂ →L[ℝ] ℂ)).contMDiff.contMDiffAt.comp x₀
    (hr.prodMk_space hα)).congr_of_eventuallyEq ?_
  have hU : ∀ᶠ p in 𝓝 x₀, p ∈ (chartAt ℂ x₀).source :=
    (chartAt ℂ x₀).open_source.mem_nhds (mem_chart_source ℂ x₀)
  filter_upwards [hU] with p hp
  have hb : p ∈ (trivializationAt ℂ (twistCore (𝕜 := ℂ) k).Fiber x₀).baseSet := by
    rw [← he, he', twistCore_localTriv_baseSet]; exact hp
  -- The transition function does not vanish on the chart; `field_simp` uses this below.
  have ht : twistTransition k p x₀ p ≠ 0 := fun h ↦ by
    have := twistTransition_mul_twistTransition k (mem_chart_source ℂ p) hp
      (mem_chart_source ℂ p) (x := p) (y := x₀) (z := p)
    simp [h] at this
  ext v
  simp only [ContinuousLinearMap.inCoordinates, Function.comp_apply, ContinuousLinearMap.comp_apply,
    smul_apply, ContinuousLinearMap.coe_restrictScalars', ContinuousLinearEquiv.coe_coe]
  generalize Trivialization.symmL ℝ (trivializationAt ℂ (TangentSpace 𝓘(ℝ, ℂ)) x₀) p v = w
  rw [Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) (hb := hb),
    Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) (hb := mem_univ p), ← he, he',
    twistCore_localTriv_apply k x₀ (fun _ ↦ α p w) p,
    twistCore_localTriv_apply k x₀ σ p, VectorBundleCore.fiberEquiv_def]
  -- The fibres of `𝒪(k)` are `ℂ`; `id` reads the values of `α` in `ℂ`.
  change ((χ p : ℂ) / σ p) * (@id ℂ (α p w)) = (χ p • (twistTransition k p x₀ p * σ p)⁻¹) •
    (twistTransition k p x₀ p * (@id ℂ (α p w)))
  generalize @id ℂ (α p w) = a
  rw [Complex.real_smul, smul_eq_mul]
  rcases eq_or_ne (σ p) 0 with h | h
  · simp [h]
  · field_simp

end OnePoint

namespace SymplecticGeometry

/-- At a point where a section `s` of `𝒪(1)` is real differentiable, the Cauchy–Riemann operator
`D_i` of the standard complex structure of the sphere vanishes exactly when `s` is holomorphic
there. -/
theorem twistOneDelBar_ofComplexManifold_eq_zero_iff {s : Π x, (twistCore (𝕜 := ℂ) 1).Fiber x}
    {x : OnePoint ℂ}
    (hs : MDifferentiableAt 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ))
      (fun p ↦ TotalSpace.mk' ℂ (E := (twistCore (𝕜 := ℂ) 1).Fiber) p (s p)) x) :
    twistOneDelBar 𝒊 s x = 0 ↔ MDifferentiableAt 𝓘(ℂ, ℂ) (𝓘(ℂ, ℂ).prod 𝓘(ℂ, ℂ))
      (fun p ↦ TotalSpace.mk' ℂ (E := (twistCore (𝕜 := ℂ) 1).Fiber) p (s p)) x := by
  have hx : x ∈ ((twistCore (𝕜 := ℂ) 1).localTriv x).baseSet := by simp
  have hr := ((twistCore (𝕜 := ℂ) 1).localTriv x).mdifferentiableAt_section_iff 𝓘(ℝ, ℂ) s hx
    |>.1 hs
  rw [((twistCore (𝕜 := ℂ) 1).localTriv x).mdifferentiableAt_section_iff 𝓘(ℂ, ℂ) s hx,
    ← SmoothAlmostComplexStructure.dbarFunction_ofComplexManifold_eq_zero_iff hr,
    twistOneDelBar_def, twistOneConnection_zeroOnePart_eq (mem_chart_source ℂ x) hs]
  -- The frame of the chart at `x` is the identity at `x`.
  refine ⟨fun h ↦ ContinuousLinearMap.ext fun v ↦ ?_,
    fun h ↦ by rw [h, ContinuousLinearMap.comp_zero]⟩
  have h' := congrArg (fun L ↦ L v) h
  simp only [ContinuousLinearMap.comp_apply, zero_apply] at h'
  rw [OnePoint.twistCore_localTriv_symmL_apply (mem_chart_source ℂ x),
    OnePoint.twistTransition_self, one_mul] at h'
  -- The fibre of `𝒪(1)` at `x` is `ℂ`, in which `h'` is stated.
  rw [zero_apply]
  exact h'

/-- **The kernel of `D_i` is `H⁰(𝒪(1))`.** The smooth sections of `𝒪(1)` that the Cauchy–Riemann
operator of the standard complex structure of the sphere sends to zero are exactly the
holomorphic sections. -/
theorem twistOneKernel_ofComplexManifold :
    twistOneKernel 𝒊 = OnePoint.holomorphicTwistSections 1 := by
  ext s
  rw [mem_twistOneKernel_iff, OnePoint.mem_holomorphicTwistSections]
  refine ⟨fun ⟨hs, h0⟩ x ↦ (twistOneDelBar_ofComplexManifold_eq_zero_iff
    (hs.mdifferentiableAt (by simp))).1 (congrFun h0 x), fun h ↦ ?_⟩
  have hc := (OnePoint.contMDiff_section_twistCore_iff_mdifferentiable (m := ∞) 1 (by simp) s).2 h
  have hr : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ)) ∞
      (fun p ↦ TotalSpace.mk' ℂ (E := (twistCore (𝕜 := ℂ) 1).Fiber) p (s p)) := by
    simpa only [ModelWithCorners.restrictScalars_prod, modelWithCornersSelf_restrictScalars] using
      hc.restrictScalars ℝ
  exact ⟨hr, funext fun x ↦
    (twistOneDelBar_ofComplexManifold_eq_zero_iff (hr.mdifferentiableAt (by simp))).2 (h x)⟩

/-- The smooth zeros of the Cauchy–Riemann operator of the standard complex structure on `𝒪(1)`
form a complex vector space of dimension two. -/
theorem finrank_twistOneKernel_ofComplexManifold : Module.finrank ℂ (twistOneKernel 𝒊) = 2 := by
  rw [twistOneKernel_ofComplexManifold]
  exact OnePoint.finrank_holomorphicTwistSections 1


/-- **Leibniz rule for `D_i` against a holomorphic section.** If a section `σ` of `𝒪(1)` is real
differentiable and holomorphic at `x`, and `g : OnePoint ℂ → ℂ` is differentiable at `x`, then
`D_i (g σ) = (∂bar g) σ` at `x`. -/
theorem twistOneDelBar_ofComplexManifold_smul_apply {g : OnePoint ℂ → ℂ}
    {σ : Π x, (twistCore (𝕜 := ℂ) 1).Fiber x} {x : OnePoint ℂ}
    (hg : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) g x)
    (hσ : MDifferentiableAt 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ))
      (fun p ↦ TotalSpace.mk' ℂ (E := (twistCore (𝕜 := ℂ) 1).Fiber) p (σ p)) x)
    (hσℂ : MDifferentiableAt 𝓘(ℂ, ℂ) (𝓘(ℂ, ℂ).prod 𝓘(ℂ, ℂ))
      (fun p ↦ TotalSpace.mk' ℂ (E := (twistCore (𝕜 := ℂ) 1).Fiber) p (σ p)) x)
    (v : TangentSpace 𝓘(ℝ, ℂ) x) :
    twistOneDelBar 𝒊 (g • σ) x v = 𝒊.dbarFunction g x v • σ x := by
  rw [(isRealCauchyRiemannOperator_twistOneDelBar 𝒊).leibniz_complex
      (isComplexLinearOperator_twistOneDelBar 𝒊) hσ hg,
    (twistOneDelBar_ofComplexManifold_eq_zero_iff hσ).2 hσℂ, smul_zero, zero_add,
    SmoothAlmostComplexStructure.zeroOnePart_apply,
    SmoothAlmostComplexStructure.dbarFunction_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.smulRight_apply, smul_assoc, add_smul, smul_assoc]

/-- **`D_i` is onto on smooth `(0,1)`-forms.** Every smooth one-form `α` on the Riemann sphere with
values in `𝒪(1)` that is a `(0,1)`-form for the standard complex structure `𝒊` at every point is
`D_i s` for a smooth section `s` of `𝒪(1)`. -/
theorem exists_twistOneDelBar_eq
    (α : ContMDiffSection 𝓘(ℝ, ℂ) (ℂ →L[ℝ] ℂ) ∞
      (fun x : OnePoint ℂ ↦ TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] (twistCore (𝕜 := ℂ) 1).Fiber x))
    (hα : ∀ x, 𝒊.IsZeroOneForm (α x)) :
    ∃ s : Π x, (twistCore (𝕜 := ℂ) 1).Fiber x,
      ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ)) ∞
        (fun x ↦ TotalSpace.mk' ℂ (E := (twistCore (𝕜 := ℂ) 1).Fiber) x (s x)) ∧
      twistOneDelBar 𝒊 s = α := by
  -- The two holomorphic sections `z` and `1`, vanishing only at `0` and only at `∞`.
  set σ : Bool → OnePoint ℂ → ℂ := fun b ↦ if b then OnePoint.identitySection
    else OnePoint.monomialSection 1 0
  have hσω (b : Bool) : ContMDiff 𝓘(ℂ, ℂ) (𝓘(ℂ, ℂ).prod 𝓘(ℂ, ℂ)) ω
      (fun p ↦ TotalSpace.mk' ℂ (E := (twistCore (𝕜 := ℂ) 1).Fiber) p (σ b p)) := by
    cases b
    · exact_mod_cast OnePoint.contMDiff_monomialSection (𝕜 := ℂ) (k := 1) (j := 0) zero_le_one
    · exact OnePoint.contMDiff_identitySection
  have hσr (b : Bool) : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ)) ∞
      (fun p ↦ TotalSpace.mk' ℂ (E := (twistCore (𝕜 := ℂ) 1).Fiber) p (σ b p)) := by
    simpa only [ModelWithCorners.restrictScalars_prod, modelWithCornersSelf_restrictScalars] using
      ((hσω b).of_le le_top).restrictScalars ℝ
  set U : Bool → Set (OnePoint ℂ) := fun b ↦ {p | σ b p ≠ 0}
  have hUo (b : Bool) : IsOpen (U b) := by
    cases b
    · convert (isClosed_singleton (x := (OnePoint.infty : OnePoint ℂ))).isOpen_compl using 1
      ext p
      induction p using OnePoint.rec <;> simp [U, σ]
    · convert (isClosed_singleton (x := ((0 : ℂ) : OnePoint ℂ))).isOpen_compl using 1
      ext p
      simp [U, σ, OnePoint.identitySection_eq_zero_iff]
  have hUcov : (univ : Set (OnePoint ℂ)) ⊆ ⋃ b, U b := by
    intro p _
    rw [mem_iUnion]
    by_cases hp : p = ((0 : ℂ) : OnePoint ℂ)
    · exact ⟨false, by simp [U, σ, hp]⟩
    · exact ⟨true, by simpa [U, σ, OnePoint.identitySection_eq_zero_iff] using hp⟩
  obtain ⟨f, hf⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, ℂ) isClosed_univ U hUo hUcov
  have hfσ (b : Bool) : ∀ x ∈ tsupport (f b), σ b x ≠ 0 := fun x hx ↦ hf b hx
  -- The two complex valued `(0,1)`-forms `f b • α / σ b`.
  let β (b : Bool) : ContMDiffSection 𝓘(ℝ, ℂ) (ℂ →L[ℝ] ℂ) ∞
      (fun x : OnePoint ℂ ↦ TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] ℂ) :=
    ⟨fun x ↦ ((f b x : ℂ) / σ b x) • (((twistCore (𝕜 := ℂ) 1).fiberEquiv x :
      (twistCore (𝕜 := ℂ) 1).Fiber x →L[ℂ] ℂ).restrictScalars ℝ).comp (α x),
      OnePoint.contMDiff_div_smul_twistCore_hom α (hσr b) (f b).contMDiff (hfσ b)⟩
  -- The fibres of `𝒪(1)` are `ℂ`; `id` reads the value of `α` in `ℂ`.
  have hβ (b : Bool) (x : OnePoint ℂ) (v : TangentSpace 𝓘(ℝ, ℂ) x) :
      β b x v = (f b x : ℂ) / σ b x * (@id ℂ (α x v)) := by
    rw [ContMDiffSection.coeFn_mk, smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_restrictScalars', ContinuousLinearEquiv.coe_coe,
      VectorBundleCore.fiberEquiv_def, smul_eq_mul]
    rfl
  have hβ01 (b : Bool) (x : OnePoint ℂ) :
      𝒊.IsZeroOneForm (V := Bundle.Trivial (OnePoint ℂ) ℂ) (β b x) :=
    SmoothAlmostComplexStructure.isZeroOneForm_iff.2 fun v ↦ by
      change β b x (𝒊 x v) = -(Complex.I * β b x v)
      rw [hβ, hβ, SmoothAlmostComplexStructure.isZeroOneForm_iff.1 (hα x) v]
      change _ * (-(Complex.I * @id ℂ (α x v))) = _
      ring
  choose g hg hdbar using fun b ↦ OnePoint.exists_contMDiff_dbarFunction_eq (β b) (hβ01 b)
  -- The section `g true • z + g false • 1`.
  let σ' (b : Bool) : Π x, (twistCore (𝕜 := ℂ) 1).Fiber x := σ b
  have ht (b : Bool) : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ)) ∞
      (fun x ↦ TotalSpace.mk' ℂ (E := (twistCore (𝕜 := ℂ) 1).Fiber) x ((g b • σ' b) x)) :=
    (hg b).smul_totalSpace (hσr b)
  refine ⟨g true • σ' true + g false • σ' false, (ht true).add_section (ht false),
    funext fun x ↦ ?_⟩
  ext v
  have hsmul (b : Bool) := twistOneDelBar_ofComplexManifold_smul_apply
    ((hg b).mdifferentiableAt (by simp) (x := x)) ((hσr b).mdifferentiableAt (by simp))
    ((hσω b).mdifferentiableAt (by simp)) v
  rw [(isRealCauchyRiemannOperator_twistOneDelBar 𝒊).add ((ht true).mdifferentiableAt (by simp))
    ((ht false).mdifferentiableAt (by simp)), add_apply, hsmul, hsmul, hdbar, hdbar, hβ, hβ]
  -- The fibres of `𝒪(1)` are `ℂ`, on which `ℂ` acts by multiplication.
  change (f true x : ℂ) / σ true x * @id ℂ (α x v) * σ true x +
    (f false x : ℂ) / σ false x * @id ℂ (α x v) * σ false x = @id ℂ (α x v)
  have hcancel (b : Bool) :
      (f b x : ℂ) / σ b x * @id ℂ (α x v) * σ b x = f b x * @id ℂ (α x v) := by
    by_cases hx : σ b x = 0
    · have : f b x = 0 := by
        by_contra h
        exact hfσ b x (subset_tsupport _ h) hx
      simp [hx, this]
    · field_simp
  have hsum := f.sum_eq_one (mem_univ x)
  rw [finsum_eq_sum_of_fintype, Fintype.sum_bool] at hsum
  rw [hcancel, hcancel, ← add_mul, ← Complex.ofReal_add, hsum, Complex.ofReal_one, one_mul]

end SymplecticGeometry

end
