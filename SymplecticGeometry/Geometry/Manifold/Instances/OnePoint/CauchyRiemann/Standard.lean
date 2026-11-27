/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Instances.OnePoint.CauchyRiemann.Sobolev
public import TauCeti.Geometry.Manifold.Instances.OnePoint.LineBundle.Sections
public import Mathlib.Analysis.Normed.Operator.Fredholm.Basic
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Index
import SymplecticGeometry.Geometry.Manifold.Instances.OnePoint.CauchyRiemann.Basic
import Mathlib.Geometry.Manifold.PartitionOfUnity
import SymplecticGeometry.Geometry.Manifold.Instances.OnePoint.Dolbeault
import TauCeti.Geometry.Manifold.ContMDiff.RestrictScalars
import TauCeti.Geometry.Manifold.MFDeriv.RestrictScalars
import TauCeti.Geometry.Manifold.VectorBundle.Scalar
import TauCeti.Geometry.Manifold.VectorBundle.CauchyRiemann.Constructions
import SymplecticGeometry.Geometry.Manifold.Instances.OnePoint.CauchyRiemann.LocalForm
import TauCeti.Analysis.Fredholm.Criteria
import SymplecticGeometry.Geometry.Manifold.VectorBundle.Sobolev.ZeroOneForm
import TauCeti.Geometry.Manifold.Instances.OnePoint.FubiniStudy

/-!
# The Cauchy–Riemann operator of the standard structure on `𝒪(1)`

Let `D_i = SymplecticGeometry.twistOneDelBar 𝒊` be the real Cauchy–Riemann operator on the line
bundle `𝒪(1) = OnePoint.twistCore 1` over the Riemann sphere for its standard complex structure
`𝒊`. This file identifies the space `twistOneKernel 𝒊` of its smooth zeros with the space
`OnePoint.holomorphicTwistSections 1` of holomorphic sections of `𝒪(1)`, which has complex
dimension two, and shows that `D_i` is onto on smooth `(0,1)`-forms. On Sobolev sections, for
every order `k`, the operator `SymplecticGeometry.twistOneDelBarSobolev 𝒊 k` from `W^{k+1,2}` to
`W^{k,2}` is then onto, and Fredholm of real index four.

## Main results

* `SymplecticGeometry.twistOneDelBar_ofComplexManifold_eq_zero_iff`: at a point where a section
  of `𝒪(1)` is real differentiable, `D_i` vanishes exactly when the section is holomorphic there.
* `SymplecticGeometry.twistOneKernel_ofComplexManifold`: the smooth zeros of `D_i` are the
  holomorphic sections of `𝒪(1)`.
* `SymplecticGeometry.finrank_twistOneKernel_ofComplexManifold`: they form a complex vector space
  of dimension two.
* `OnePoint.monomialSection_zero_eq_zero_iff`: the section `1` of `𝒪(k)`, for `k ≠ 0`, vanishes
  only at `∞`.
* `OnePoint.identitySection_ne_zero_or_monomialSection_ne_zero`: the sections `z` and `1` of
  `𝒪(1)` have no common zero.
* `SymplecticGeometry.twistOneDelBar_ofComplexManifold_smul_apply`: `D_i (g σ) = (∂bar g) σ` for a
  holomorphic section `σ` of `𝒪(1)`.
* `SymplecticGeometry.exists_twistOneDelBar_eq`: every smooth `(0,1)`-form with values in `𝒪(1)`
  is `D_i s` for a smooth section `s`.
* `SymplecticGeometry.twistOneDelBarSobolev_ofComplexManifold_surjective`: `D_i` is onto from
  `W^{k+1,2}(𝒪(1))` to the `W^{k,2}` `(0,1)`-forms with values in `𝒪(1)`.
* `SymplecticGeometry.finrank_ker_twistOneDelBarSobolev_ofComplexManifold`: its kernel there has
  real dimension four.
* `SymplecticGeometry.isFredholm_twistOneDelBarSobolev_ofComplexManifold`: it is Fredholm, of real
  index four.

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
`1` (`OnePoint.monomialSection 1 0`) of `𝒪(1)` vanish only at `0` and only at `∞`
(`OnePoint.monomialSection_zero_eq_zero_iff`), so `β_z = (χ_z / z) α` and `β_1 = (χ_1 / 1) α` are
smooth (`OnePoint.contMDiff_div_smul_twistCore_hom`) complex valued `(0,1)`-forms
(`TauCeti.SmoothAlmostComplexStructure.IsZeroOneForm.restrictScalars_comp`). The scalar case
`OnePoint.exists_contMDiff_dbarFunction_eq` gives smooth functions `g_z`, `g_1` with
`∂bar g_z = β_z` and `∂bar g_1 = β_1`. Since `D_i` kills holomorphic sections, the complex Leibniz
rule (`TauCeti.IsRealCauchyRiemannOperator.leibniz_complex`) gives
(`SymplecticGeometry.twistOneDelBar_ofComplexManifold_smul_apply`)
`D_i (g_z z + g_1 1) = (∂bar g_z) z + (∂bar g_1) 1 = χ_z α + χ_1 α = α`.

On Sobolev sections, the Fubini–Study form tames `𝒊` (Tau Ceti's
`OnePoint.compatible_fubiniStudyForm`), so the range of `D_i` is closed
(`SymplecticGeometry.isClosed_range_twistOneDelBarSobolev`). The `(0,1)`-projections of the
Sobolev forms of smooth one-forms `s` are dense among the `(0,1)`-forms
(`TauCeti.dense_zeroOnePartSobolevL_ofContMDiffSection`), and each is the Sobolev form of the
smooth `(0,1)`-form `𝒊.zeroOnePart ∘ s` (`TauCeti.coe_zeroOnePartSobolevL_ofContMDiffSection`),
hence `D_i` of a smooth section by `exists_twistOneDelBar_eq` (compared through
`chartValueL_twistOneDelBarSobolev_ofContMDiffSection_ae_coord`). So the range is everything. The
kernel has the real dimension of `twistOneKernel 𝒊`
(`SymplecticGeometry.finrank_ker_twistOneDelBarSobolev`), which is `2 · 2 = 4`; with the cokernel
zero, the index is four.

## References

* [D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*][McDuffSalamon2012],
  Appendix C.1.
-/

public section

open Bundle Filter MeasureTheory Set TauCeti
open OnePoint (twistCore twistTransition)
open scoped Manifold ContDiff Topology TauCeti.ComplexManifold VectorBundle.ComplexToReal

namespace OnePoint

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- For `k ≠ 0`, the section `1 = z⁰` of `𝒪(k)` vanishes exactly at `∞`. -/
theorem monomialSection_zero_eq_zero_iff {k : ℕ} (hk : k ≠ 0) {p : OnePoint 𝕜} :
    monomialSection k 0 p = 0 ↔ p = (∞ : OnePoint 𝕜) := by
  induction p using OnePoint.rec with
  | infty => simp [hk.symm]
  | coe z => simp

/-- The sections `z` and `1` of `𝒪(1)` have no common zero: at every point of the projective line
one of them does not vanish. -/
theorem identitySection_ne_zero_or_monomialSection_ne_zero (p : OnePoint 𝕜) :
    identitySection p ≠ 0 ∨ monomialSection 1 0 p ≠ 0 := by
  rw [Ne, Ne, identitySection_eq_zero_iff, monomialSection_zero_eq_zero_iff one_ne_zero]
  induction p using OnePoint.rec <;> simp

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


/-- **Leibniz rule for `D_i` against a holomorphic section.** If a section `σ` of `𝒪(1)` is
holomorphic at `x`, and `g : OnePoint ℂ → ℂ` is differentiable at `x`, then
`D_i (g σ) = (∂bar g) σ` at `x`. -/
theorem twistOneDelBar_ofComplexManifold_smul_apply {g : OnePoint ℂ → ℂ}
    {σ : Π x, (twistCore (𝕜 := ℂ) 1).Fiber x} {x : OnePoint ℂ}
    (hg : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) g x)
    (hσℂ : MDifferentiableAt 𝓘(ℂ, ℂ) (𝓘(ℂ, ℂ).prod 𝓘(ℂ, ℂ))
      (fun p ↦ TotalSpace.mk' ℂ (E := (twistCore (𝕜 := ℂ) 1).Fiber) p (σ p)) x)
    (v : TangentSpace 𝓘(ℝ, ℂ) x) :
    twistOneDelBar 𝒊 (g • σ) x v = 𝒊.dbarFunction g x v • σ x := by
  have hσ : MDifferentiableAt 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ))
      (fun p ↦ TotalSpace.mk' ℂ (E := (twistCore (𝕜 := ℂ) 1).Fiber) p (σ p)) x := by
    simpa only [ModelWithCorners.restrictScalars_prod, modelWithCornersSelf_restrictScalars] using
      hσℂ.restrictScalars ℝ
  rw [(isRealCauchyRiemannOperator_twistOneDelBar 𝒊).leibniz_complex
      (isComplexLinearOperator_twistOneDelBar 𝒊) hσ hg,
    (twistOneDelBar_ofComplexManifold_eq_zero_iff hσ).2 hσℂ, smul_zero, zero_add,
    SmoothAlmostComplexStructure.zeroOnePart_apply,
    SmoothAlmostComplexStructure.dbarFunction_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.smulRight_apply, smul_assoc, add_smul, smul_assoc]

/-- Let `α` be a smooth `(0,1)`-form with values in `𝒪(k)`, `σ` a smooth section of `𝒪(k)` and `χ`
a smooth real function such that `σ` does not vanish on the closed support of `χ`. Then the
complex valued form `(χ / σ) α` is `∂bar g` for a smooth function `g`. -/
private theorem exists_dbarFunction_eq_div_smul {k : ℤ}
    (α : ContMDiffSection 𝓘(ℝ, ℂ) (ℂ →L[ℝ] ℂ) ∞
      (fun x : OnePoint ℂ ↦ TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] (twistCore (𝕜 := ℂ) k).Fiber x))
    (hα : ∀ x, 𝒊.IsZeroOneForm (α x)) {σ : OnePoint ℂ → ℂ}
    (hσ : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ)) ∞
      (fun p ↦ TotalSpace.mk' ℂ (E := (twistCore (𝕜 := ℂ) k).Fiber) p (σ p)))
    {χ : OnePoint ℂ → ℝ} (hχ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ χ)
    (hχσ : ∀ x ∈ tsupport χ, σ x ≠ 0) :
    ∃ g : OnePoint ℂ → ℂ, ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ g ∧
      ∀ x v, 𝒊.dbarFunction g x v =
        ((χ x : ℂ) / σ x) • (twistCore (𝕜 := ℂ) k).fiberEquiv x (α x v) := by
  let β : ContMDiffSection 𝓘(ℝ, ℂ) (ℂ →L[ℝ] ℂ) ∞
      (fun x : OnePoint ℂ ↦ TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] ℂ) :=
    ⟨fun x ↦ ((χ x : ℂ) / σ x) • (((twistCore (𝕜 := ℂ) k).fiberEquiv x :
      (twistCore (𝕜 := ℂ) k).Fiber x →L[ℂ] ℂ).restrictScalars ℝ).comp (α x),
      OnePoint.contMDiff_div_smul_twistCore_hom α hσ hχ hχσ⟩
  have hβ (x : OnePoint ℂ) : 𝒊.IsZeroOneForm (V := Bundle.Trivial (OnePoint ℂ) ℂ) (β x) := by
    rw [ContMDiffSection.coeFn_mk]
    simpa only [ContinuousLinearMap.restrictScalars_smul, ContinuousLinearMap.smul_comp] using
      (hα x).restrictScalars_comp (W := Bundle.Trivial (OnePoint ℂ) ℂ)
        (((χ x : ℂ) / σ x) • ((twistCore (𝕜 := ℂ) k).fiberEquiv x :
          (twistCore (𝕜 := ℂ) k).Fiber x →L[ℂ] ℂ))
  obtain ⟨g, hg, hdbar⟩ := OnePoint.exists_contMDiff_dbarFunction_eq β hβ
  refine ⟨g, hg, fun x v ↦ ?_⟩
  rw [hdbar, ContMDiffSection.coeFn_mk, smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', ContinuousLinearEquiv.coe_coe]

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
    · convert isOpen_compl_singleton (x := (OnePoint.infty : OnePoint ℂ)) using 1
      ext p
      simp [U, σ, OnePoint.monomialSection_zero_eq_zero_iff]
    · convert isOpen_compl_singleton (x := ((0 : ℂ) : OnePoint ℂ)) using 1
      ext p
      simp [U, σ, OnePoint.identitySection_eq_zero_iff]
  have hUcov : (univ : Set (OnePoint ℂ)) ⊆ ⋃ b, U b := fun p _ ↦ mem_iUnion.2 <|
    (OnePoint.identitySection_ne_zero_or_monomialSection_ne_zero p).elim
      (fun h ↦ ⟨true, h⟩) (fun h ↦ ⟨false, h⟩)
  obtain ⟨f, hf⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, ℂ) isClosed_univ U hUo hUcov
  have hfσ (b : Bool) : ∀ x ∈ tsupport (f b), σ b x ≠ 0 := fun x hx ↦ hf b hx
  choose g hg hdbar using fun b ↦
    exists_dbarFunction_eq_div_smul α hα (hσr b) (f b).contMDiff (hfσ b)
  -- The section `g true • z + g false • 1`.
  let σ' (b : Bool) : Π x, (twistCore (𝕜 := ℂ) 1).Fiber x := σ b
  have ht (b : Bool) : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ)) ∞
      (fun x ↦ TotalSpace.mk' ℂ (E := (twistCore (𝕜 := ℂ) 1).Fiber) x ((g b • σ' b) x)) :=
    (hg b).smul_totalSpace (hσr b)
  refine ⟨g true • σ' true + g false • σ' false, (ht true).add_section (ht false),
    funext fun x ↦ ?_⟩
  ext v
  have hsmul (b : Bool) := twistOneDelBar_ofComplexManifold_smul_apply
    ((hg b).mdifferentiableAt (by simp) (x := x)) ((hσω b).mdifferentiableAt (by simp)) v
  rw [(isRealCauchyRiemannOperator_twistOneDelBar 𝒊).add ((ht true).mdifferentiableAt (by simp))
    ((ht false).mdifferentiableAt (by simp)), add_apply, hsmul, hsmul, hdbar, hdbar,
    VectorBundleCore.fiberEquiv_def]
  -- The fibres of `𝒪(1)` are `ℂ`, on which `ℂ` acts by multiplication, and `fiberEquiv` is the
  -- identity of `ℂ`.
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

/-! ### `D_i` on Sobolev sections -/

/-- The `(0,1)`-part for `𝒊` of a smooth `𝒪(1)`-valued one-form `s` on the sphere, as a Sobolev
form of order `k`, is `D_i` of a Sobolev section of order `k + 1`. -/
private theorem exists_twistOneDelBarSobolev_eq_zeroOnePartSobolevL (k : ℕ)
    (s : Cₛ^k⟮𝓘(ℝ, ℂ); ℂ →L[ℝ] ℂ,
      fun x : OnePoint ℂ ↦ TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] (twistCore (𝕜 := ℂ) 1).Fiber x⟯)
    (hs : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ →L[ℝ] ℂ)) ∞
      (fun x ↦ TotalSpace.mk' (ℂ →L[ℝ] ℂ)
        (E := fun x : OnePoint ℂ ↦ TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] (twistCore (𝕜 := ℂ) 1).Fiber x)
        x (s x))) :
    ∃ w, twistOneDelBarSobolev 𝒊 k w = zeroOnePartSobolevL (twistCoreAtlas 1) volume 2 k
      (SobolevSection.ofContMDiffSection (twistCoreAtlas 1).tangentHom volume 2 k s) := by
  let α : Cₛ^k⟮𝓘(ℝ, ℂ); ℂ →L[ℝ] ℂ,
      fun x : OnePoint ℂ ↦ TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] (twistCore (𝕜 := ℂ) 1).Fiber x⟯ :=
    ⟨fun x ↦ 𝒊.zeroOnePart (s x),
      ((𝒊.contMDiff_totalSpace_zeroOnePart le_rfl).comp hs).of_le (by exact_mod_cast le_top)⟩
  have hα : ⇑α = fun x ↦ 𝒊.zeroOnePart (s x) := ContMDiffSection.coeFn_mk _ _
  obtain ⟨t, ht, htα⟩ := exists_twistOneDelBar_eq ⟨_, (𝒊.contMDiff_totalSpace_zeroOnePart
    le_rfl).comp hs⟩ fun x ↦ 𝒊.isZeroOneForm_zeroOnePart (s x)
  rw [ContMDiffSection.coeFn_mk] at htα
  let t' : Cₛ^((k + 1 : ℕ) : WithTop ℕ∞)⟮𝓘(ℝ, ℂ); ℂ, (twistCore (𝕜 := ℂ) 1).Fiber⟯ :=
    ⟨t, ht.of_le (by exact_mod_cast le_top)⟩
  have hDt : (fun x ↦ 𝒊.zeroOnePart (twistOneDelBar 𝒊 t' x)) = ⇑α := by
    rw [show (t' : Π x, (twistCore (𝕜 := ℂ) 1).Fiber x) = t from ContMDiffSection.coeFn_mk _ _,
      htα, hα]
    simp only [SmoothAlmostComplexStructure.zeroOnePart_zeroOnePart]
  refine ⟨SobolevSection.ofContMDiffSection (twistCoreAtlas 1) volume 2 (k + 1) t',
    Subtype.ext ?_⟩
  rw [coe_zeroOnePartSobolevL_ofContMDiffSection (congrFun hα)]
  refine SectionChartData.eq_of_chartValueL_ae_eq fun i ↦
    (FiniteBundleAtlas.ae_image_tangentHom_iff (twistCoreAtlas 1) volume i).2 ?_
  have h1 := chartValueL_twistOneDelBarSobolev_ofContMDiffSection_ae_coord 𝒊 k t' i
  have h2 := (FiniteBundleAtlas.ae_image_tangentHom_iff (twistCoreAtlas 1) volume i).1
    (SobolevSection.chartValueL_ofContMDiffSection_ae (twistCoreAtlas 1).tangentHom volume 2 k
      α i)
  filter_upwards [h1, h2] with y hy1 hy2
  rw [hy1, hy2, hDt]

/-- **`D_i` is onto on Sobolev sections.** For every order `k`, every `W^{k,2}` `(0,1)`-form with
values in `𝒪(1)` on the sphere is `D_i w` for a `W^{k+1,2}` section `w` of `𝒪(1)`. -/
theorem twistOneDelBarSobolev_ofComplexManifold_surjective (k : ℕ) :
    Function.Surjective (twistOneDelBarSobolev 𝒊 k) := by
  -- The `(0,1)`-parts of smooth forms are dense, and lie in the range, which is closed.
  have hdense := dense_zeroOnePartSobolevL_ofContMDiffSection (twistCoreAtlas 1) volume 2 k
    ENNReal.ofNat_ne_top
  refine fun v ↦ (isClosed_range_twistOneDelBarSobolev 𝒊 k
    OnePoint.compatible_fubiniStudyForm.tames OnePoint.compatible_fubiniStudyForm.tames
    ).closure_subset_iff.2 ?_ (hdense.closure_eq ▸ mem_univ v)
  rintro _ ⟨s, hs, rfl⟩
  exact exists_twistOneDelBarSobolev_eq_zeroOnePartSobolevL k s hs

/-- **The Sobolev kernel of `D_i`.** For every order `k`, the kernel of `D_i` on `W^{k+1,2}(𝒪(1))`
over the sphere has real dimension four. -/
theorem finrank_ker_twistOneDelBarSobolev_ofComplexManifold (k : ℕ) :
    Module.finrank ℝ (twistOneDelBarSobolev 𝒊 k).ker = 4 := by
  rw [finrank_ker_twistOneDelBarSobolev OnePoint.compatible_fubiniStudyForm.tames
    OnePoint.compatible_fubiniStudyForm.tames k, finrank_real_of_complex,
    finrank_twistOneKernel_ofComplexManifold]

/-- **`D_i` is Fredholm of index four.** For every order `k`, the operator
`D_i : W^{k+1,2}(𝒪(1)) → W^{k,2}(Λ^{0,1} ⊗ 𝒪(1))` over the sphere is Fredholm, of real index
`4`. -/
theorem isFredholm_twistOneDelBarSobolev_ofComplexManifold (k : ℕ) :
    (twistOneDelBarSobolev 𝒊 k).IsFredholm ∧ (twistOneDelBarSobolev 𝒊 k).index = 4 := by
  have hsurj := twistOneDelBarSobolev_ofComplexManifold_surjective k
  have := finiteDimensional_ker_twistOneDelBarSobolev 𝒊 k
    OnePoint.compatible_fubiniStudyForm.tames OnePoint.compatible_fubiniStudyForm.tames
  refine ⟨ContinuousLinearMap.IsFredholm.of_surjective hsurj, ?_⟩
  rw [ContinuousLinearMap.index_of_surjective _ hsurj,
    finrank_ker_twistOneDelBarSobolev_ofComplexManifold k, Nat.cast_ofNat]

end SymplecticGeometry

end
