/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.OnePoint.LineBundle
public import TauCeti.Geometry.Manifold.VectorBundle.RestrictScalars
public import SymplecticGeometry.Topology.VectorBundle.Complex.RestrictScalars
public import SymplecticGeometry.Topology.VectorBundle.Core.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import TauCeti.Geometry.Manifold.Complex.Orientation
import SymplecticGeometry.Topology.VectorBundle.Basic
import SymplecticGeometry.Geometry.Manifold.VectorBundle.CoordRatio

/-!
# The line bundles `𝒪(k)` on the Riemann sphere as real vector bundles

On the Riemann sphere `OnePoint ℂ`, Tau Ceti's `OnePoint.twistCore k` is the holomorphic line
bundle `𝒪(k)`, glued from trivial lines over the affine and the inverted chart along the
transition functions `OnePoint.twistTransition k`. This file records the structure it has as a
smooth real vector bundle over the underlying real surface, by restriction of scalars, for every
degree `k`:

* the instances `ContinuousSMul ℝ` on its fibres, `ContMDiffVectorBundle n ℂ _ 𝓘(ℝ, ℂ)` for
  every `n` (from Tau Ceti's `ContMDiffVectorBundle.restrictScalars_modelWithCornersSelf`), and
  `MemTrivializationAtlas` for its local trivializations `(twistCore k).localTriv y`;
* `OnePoint.twistTransition_ne_zero`: the transition functions do not vanish on chart overlaps;
* `OnePoint.mdifferentiableAt_div_twistCore`: the quotient of two sections of `𝒪(k)` that are
  real differentiable at a point is real differentiable there where the denominator is nonzero;
* `OnePoint.eventually_ne_zero_twistCore`: a section of `𝒪(k)` that is real differentiable and
  nonzero at a point is nonzero near it;
* `OnePoint.contMDiffAt_div_twistCore`: the same for sections that are `C^n` at a point, by the
  same reading in coordinates, adapted to `C^n` from the differentiability step of Tau Ceti's
  `TauCeti.IsRealCauchyRiemannOperator.exists_mdifferentiableOn_eq_smul`;
* `OnePoint.twistCore_localTriv_symmL_apply`: over the chart at `y`, the real frame of the
  trivialization at `y` is multiplication by a transition function;
* `OnePoint.twistCore_localTriv_symmL_smul`: that frame commutes with complex scalars;
* `OnePoint.contMDiff_div_smul_twistCore_hom`: multiplying a `C^n` one-form with values in `𝒪(k)`
  by `χ / σ`, for a `C^n` real function `χ` and a `C^n` section `σ` of `𝒪(k)` that does not
  vanish on the closed support of `χ`, gives a `C^n` complex valued one-form.

`OnePoint.mdifferentiableAt_div_twistCore` follows from the general
`Bundle.Trivialization.mdifferentiableAt_coordRatio`: near the point, the quotient is the ratio
of the two sections read in the trivialization `(twistCore k).localTriv x`.

Files using the real structure `open scoped VectorBundle.ComplexToReal`.
-/

public section

open Bundle Filter Set
open scoped Manifold ContDiff Topology VectorBundle.ComplexToReal

noncomputable section

namespace OnePoint

variable {k : ℤ}

/-- The transition functions of `𝒪(k)` do not vanish on the chart overlaps. -/
theorem twistTransition_ne_zero {𝕜 : Type*} [NontriviallyNormedField 𝕜] [ProperSpace 𝕜]
    (k : ℤ) {x y p : OnePoint 𝕜} (hx : p ∈ (chartAt 𝕜 x).source)
    (hy : p ∈ (chartAt 𝕜 y).source) : twistTransition k x y p ≠ 0 := by
  have h := twistTransition_mul_twistTransition k hx hy hx (x := x) (y := y) (z := x)
  rw [twistTransition_self] at h
  exact right_ne_zero_of_mul_eq_one h

/-- The fibres of `𝒪(k)` on the Riemann sphere carry the topology of `ℂ`, for which multiplication
by real scalars is continuous. -/
instance (k : ℤ) (x : OnePoint ℂ) : ContinuousSMul ℝ ((twistCore (𝕜 := ℂ) k).Fiber x) :=
  inferInstanceAs (ContinuousSMul ℝ ℂ)

/-- `𝒪(k)` on the Riemann sphere is a `C^n` real vector bundle over the underlying real
surface, for every `n`. -/
instance (k : ℤ) {n : ℕ∞ω} : ContMDiffVectorBundle n ℂ (twistCore (𝕜 := ℂ) k).Fiber 𝓘(ℝ, ℂ) :=
  have : ContMDiffVectorBundle n ℂ (twistCore (𝕜 := ℂ) k).Fiber 𝓘(ℂ, ℂ) :=
    ContMDiffVectorBundle.of_le le_top
  ContMDiffVectorBundle.restrictScalars_modelWithCornersSelf ℝ this

/-- The local trivializations of `𝒪(k)` belong to its trivialization atlas. -/
instance (k : ℤ) (y : OnePoint ℂ) :
    MemTrivializationAtlas ((twistCore (𝕜 := ℂ) k).localTriv y) :=
  ⟨⟨y, rfl⟩⟩

/-- Over the chart at `y`, the frame of the trivialization of `𝒪(k)` at `y` is multiplication by
the transition function from the chart at `y` to the chart at the point. -/
theorem twistCore_localTriv_symmL_apply {y x : OnePoint ℂ} (hx : x ∈ (chartAt ℂ y).source)
    (v : ℂ) :
    ((twistCore (𝕜 := ℂ) k).localTriv y).symmL ℝ x v = twistTransition k y x x * v := by
  have hb : x ∈ ((twistCore (𝕜 := ℂ) k).localTriv y).baseSet := by simpa using hx
  rw [Trivialization.symmL_apply _ hb]
  have h := (twistCore (𝕜 := ℂ) k).localTriv_symm_apply y hb v
  rwa [twistCore_indexAt, twistCore_coordChange_apply] at h

/-- The real frame of a trivialization of `𝒪(k)` commutes with complex scalars. -/
theorem twistCore_localTriv_symmL_smul (y x : OnePoint ℂ) (c w : ℂ) :
    ((twistCore (𝕜 := ℂ) k).localTriv y).symmL ℝ x (c • w) =
      c • ((twistCore (𝕜 := ℂ) k).localTriv y).symmL ℝ x w := by
  by_cases hb : x ∈ ((twistCore (𝕜 := ℂ) k).localTriv y).baseSet
  · rw [Trivialization.symmL_apply _ hb, Trivialization.symmL_apply _ hb,
      ← Trivialization.symmL_apply (R := ℂ) _ hb, ← Trivialization.symmL_apply (R := ℂ) _ hb,
      map_smul]
  · simp [Trivialization.symmL_apply_of_notMem _ hb]

/-- The quotient `p ↦ s p / t p` of two sections of `𝒪(k)` that are real differentiable at `x`
is real differentiable at `x` if `t x ≠ 0`. The quotient is a function, since `s p` and `t p`
lie in the same fibre. -/
theorem mdifferentiableAt_div_twistCore (k : ℤ) {s t : OnePoint ℂ → ℂ} {x : OnePoint ℂ}
    (hs : MDifferentiableAt 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ))
      (fun p ↦ TotalSpace.mk' ℂ (E := (twistCore (𝕜 := ℂ) k).Fiber) p (s p)) x)
    (ht : MDifferentiableAt 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ))
      (fun p ↦ TotalSpace.mk' ℂ (E := (twistCore (𝕜 := ℂ) k).Fiber) p (t p)) x)
    (hx : t x ≠ 0) :
    MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun p ↦ s p / t p) x := by
  set e := (twistCore (𝕜 := ℂ) k).localTriv x
  -- `s` and `t` as sections of `𝒪(k)`, whose fibres are `ℂ`.
  let s' : Π p, (twistCore (𝕜 := ℂ) k).Fiber p := s
  let t' : Π p, (twistCore (𝕜 := ℂ) k).Fiber p := t
  -- Near `x` the quotient is the ratio of `s` to `t` read in the trivialization at `x`.
  refine (e.mdifferentiableAt_coordRatio (σ := t') (τ := s') (by simp [e]) ht hs
    hx).congr_of_eventuallyEq ?_
  filter_upwards [(chartAt ℂ x).open_source.eventually_mem (mem_chart_source ℂ x)] with p hp
  have hb : p ∈ e.baseSet := by simpa [e] using hp
  rw [e.coordRatio_eq_div_of_mem hb, twistCore_localTriv_apply, twistCore_localTriv_apply]
  exact (mul_div_mul_left _ _ (twistTransition_ne_zero k (mem_chart_source ℂ p) hp)).symm

/-- A section `t` of `𝒪(k)` that is real differentiable at `x` and does not vanish at `x` does
not vanish near `x`. -/
theorem eventually_ne_zero_twistCore (k : ℤ) {t : OnePoint ℂ → ℂ} {x : OnePoint ℂ}
    (ht : MDifferentiableAt 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ))
      (fun p ↦ TotalSpace.mk' ℂ (E := (twistCore (𝕜 := ℂ) k).Fiber) p (t p)) x)
    (hx : t x ≠ 0) : ∀ᶠ p in 𝓝 x, t p ≠ 0 := by
  set e := (twistCore (𝕜 := ℂ) k).localTriv x
  have hxe : x ∈ e.baseSet := by simp [e]
  -- The coordinate of `t` in the trivialization at `x` is continuous at `x` and nonzero there.
  have hc := ((e.mdifferentiableAt_section_iff 𝓘(ℝ, ℂ) t hxe).1 ht).continuousAt
  have hc0 : (e ⟨x, t x⟩).2 ≠ 0 :=
    (e.snd_apply_ne_zero_iff ℝ (v := TotalSpace.mk' ℂ x (t x)) hxe).2 hx
  filter_upwards [hc.eventually_ne hc0, e.open_baseSet.mem_nhds hxe] with p hp hpe
  exact (e.snd_apply_ne_zero_iff ℝ (v := TotalSpace.mk' ℂ p (t p)) hpe).1 hp

/-- The quotient `p ↦ s p / t p` of two sections of `𝒪(k)` that are `C^n` at `x` for the real
structure is `C^n` at `x` if `t x ≠ 0`. The quotient is a function, since `s p` and `t p` lie in
the same fibre. -/
theorem contMDiffAt_div_twistCore (k : ℤ) {n : ℕ∞ω} {s t : OnePoint ℂ → ℂ} {x : OnePoint ℂ}
    (hs : ContMDiffAt 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ)) n
      (fun p ↦ TotalSpace.mk' ℂ (E := (twistCore (𝕜 := ℂ) k).Fiber) p (s p)) x)
    (ht : ContMDiffAt 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ)) n
      (fun p ↦ TotalSpace.mk' ℂ (E := (twistCore (𝕜 := ℂ) k).Fiber) p (t p)) x)
    (hx : t x ≠ 0) :
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) n (fun p ↦ s p / t p) x := by
  -- The coordinates of `s` and `t` in the trivialization at `x`.
  have hxx : x ∈ ((twistCore (𝕜 := ℂ) k).localTriv x).baseSet := by simp
  have hcs := (Trivialization.contMDiffAt_section_iff _ hxx).1 hs
  have hct := (Trivialization.contMDiffAt_section_iff _ hxx).1 ht
  simp only [twistCore_localTriv_apply] at hcs hct
  have hct0 : twistTransition k x x x * t x ≠ 0 := by rwa [twistTransition_self, one_mul]
  -- Near `x` the quotient is the quotient of the coordinates.
  have hdiv : ContDiffAt ℝ n (fun z : ℂ × ℂ ↦ z.1 / z.2)
      (twistTransition k x x x * s x, twistTransition k x x x * t x) :=
    (contDiffAt_fst.div contDiffAt_snd hct0).restrict_scalars ℝ
  refine (hdiv.contMDiffAt.comp x (hcs.prodMk_space hct)).congr_of_eventuallyEq ?_
  filter_upwards [(chartAt ℂ x).open_source.eventually_mem (mem_chart_source ℂ x)] with p hp
  exact (mul_div_mul_left _ _ (twistTransition_ne_zero k (mem_chart_source ℂ p) hp)).symm

open scoped TauCeti.ComplexManifold in
/-- Let `α` be a `C^n` one-form on the Riemann sphere with values in `𝒪(k)`, `σ` a `C^n` section
of `𝒪(k)` and `χ` a `C^n` real function such that `σ` does not vanish on the closed support of
`χ`. Then the complex valued one-form `(χ / σ) α`, which reads `α x` in `ℂ` through the
identification `VectorBundleCore.fiberEquiv` of the fibre with `ℂ` and is zero off the support
of `χ`, is `C^n`. -/
theorem contMDiff_div_smul_twistCore_hom {k : ℤ} {n : ℕ∞ω}
    (α : ContMDiffSection 𝓘(ℝ, ℂ) (ℂ →L[ℝ] ℂ) n
      (fun x : OnePoint ℂ ↦ TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] (twistCore (𝕜 := ℂ) k).Fiber x))
    {σ : OnePoint ℂ → ℂ}
    (hσ : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ)) n
      (fun p ↦ TotalSpace.mk' ℂ (E := (twistCore (𝕜 := ℂ) k).Fiber) p (σ p)))
    {χ : OnePoint ℂ → ℝ} (hχ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) n χ)
    (hχσ : ∀ x ∈ tsupport χ, σ x ≠ 0) :
    ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ →L[ℝ] ℂ)) n
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
    simp [hp, zeroSection_def]
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  have hα := ((contMDiffAt_hom_bundle _).1 (α.contMDiff x₀)).2
  have hσ' := (contMDiffAt_section_iff x₀).1 (hσ x₀)
  set e := trivializationAt ℂ (twistCore (𝕜 := ℂ) k).Fiber x₀ with he
  have he' : e = (twistCore (𝕜 := ℂ) k).localTriv x₀ := by
    rw [he, VectorBundleCore.trivializationAt, ← VectorBundleCore.localTrivAt_def,
      OnePoint.twistCore_indexAt]
  have hr : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) n (fun p ↦ χ p • ((e ⟨p, σ p⟩).2)⁻¹) x₀ := by
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
  have ht : twistTransition k p x₀ p ≠ 0 := twistTransition_ne_zero k (mem_chart_source ℂ p) hp
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

end
