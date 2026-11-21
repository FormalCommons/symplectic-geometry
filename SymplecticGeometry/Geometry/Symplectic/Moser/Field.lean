/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.Flat
public import TauCeti.Geometry.Manifold.DifferentialForm.LieDeriv
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Family
import SymplecticGeometry.Geometry.Symplectic.Manifold.Family
import TauCeti.Geometry.Manifold.DifferentialForm.Flow.Family
import TauCeti.Geometry.Manifold.VectorBundle.Hom
import TauCeti.Geometry.Manifold.VectorBundle.Scalar

/-!
# The cut-off Moser field of a segment of two-forms

For smooth two-forms `σ₀`, `σ₁` on a manifold `M`, a one-form `β` and a function `ρ` on `ℝ × M`,
`SymplecticGeometry.moserField σ₀ σ₁ β ρ` is the time-dependent vector field
`X_t = ρ(t, ·) (σ_t♭)⁻¹(-β)` of the segment `σ_t = σ₀ + t (σ₁ - σ₀)`, where `σ_t♭` is the flat
map `v ↦ ι_v σ_t`. Where `σ_t` is nondegenerate it is the field with `ι_{X_t} σ_t = -ρ(t, ·) β`.

If `σ₀` is closed and `β` is a primitive of `σ₁ - σ₀` near a point `y`, then at every `(t, y)`
near which `ρ = 1` and `σ_t` is nondegenerate, Cartan's formula gives Moser's equation
`∂_t σ_t + L_{X_t} σ_t = (σ₁ - σ₀) - dβ = 0`, which is the hypothesis of Tau Ceti's Moser
principle along trajectories
(`TauCeti.mpullback_timeDependentFlowOf_mpullback_prodMk_apply_eq_of_forall_mem_uIcc`).

## Main definitions and results

* `SymplecticGeometry.moserField`: the cut-off Moser field of the segment from `σ₀` to `σ₁`.
* `SymplecticGeometry.interior_moserField`, `SymplecticGeometry.interior_moserField_eq`:
  the identity `ι_{X_t} σ_t = -ρ(t, ·) β`.
* `SymplecticGeometry.contMDiffAt_moserField`, `SymplecticGeometry.contMDiff_moserField`: the
  field is jointly smooth on `ℝ × M` where `ρ` is smooth and `σ_t` is nondegenerate at every
  point `(t, x)` of the support of `ρ`.
* `SymplecticGeometry.moserField_rate_eq_zero`: Moser's equation at a point near which `ρ = 1`,
  `σ_t` is nondegenerate and `β` is a primitive of `σ₁ - σ₀`.

The definition and the proofs adapt Tau Ceti's private `moserField`, `moserField_eq_zero`,
`interior_moserField`, `interior_moserField_eq`, `contMDiff_moserField` and `moserRate_eq_zero`
(`TauCeti/Geometry/Symplectic/Manifold/RelativeMoser.lean`) from the segment
reparametrized by `Real.smoothTransition` and a cutoff on `M` to the linear segment and a cutoff
on `ℝ × M`. With the linear segment, `σ_t = ω_t` for every `t ∈ [0, 1]`, which is what an isotopy
`ψ_t` with `ψ_t^* ω_t = ω_0` for every such `t` needs.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §3.2.
* [A. Cannas da Silva, *Lectures on Symplectic Geometry*][CannasdaSilva2001], Lectures 6–7.
* J. Moser, *On the volume elements on a manifold*, Transactions of the American Mathematical
  Society 120 (1965), 286–294.
-/

public section

noncomputable section

open Bundle Set Filter TauCeti
open scoped Manifold Topology ContDiff

namespace SymplecticGeometry

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {σ₀ σ₁ : SmoothTwoForm I M} {β : SmoothForm I M ℝ 1} {ρ : ℝ × M → ℝ}

/-- The **cut-off Moser field** of the segment `σ_t = σ₀ + t (σ₁ - σ₀)` of two-forms and the
one-form `β`, cut off by `ρ : ℝ × M → ℝ`: `X_t(x) = ρ(t, x) (σ_t♭)⁻¹(-β)(x)`, where `σ_t♭` is the
flat map of `σ_t` at `x`. Where the flat map is not invertible, `ContinuousLinearMap.inverse`
gives `0`. -/
def moserField (σ₀ σ₁ : SmoothTwoForm I M) (β : SmoothForm I M ℝ 1) (ρ : ℝ × M → ℝ)
    (t : ℝ) (x : M) : TangentSpace I x :=
  ρ (t, x) • ((σ₀ + t • (σ₁ - σ₀)).flat x).inverse (-SmoothForm.degreeOneEquiv β x)

theorem moserField_def (σ₀ σ₁ : SmoothTwoForm I M) (β : SmoothForm I M ℝ 1) (ρ : ℝ × M → ℝ)
    (t : ℝ) (x : M) :
    moserField σ₀ σ₁ β ρ t x =
      ρ (t, x) • ((σ₀ + t • (σ₁ - σ₀)).flat x).inverse (-SmoothForm.degreeOneEquiv β x) :=
  (rfl)

/-- The Moser field vanishes where the one-form `β` does. -/
theorem moserField_eq_zero_of_apply_eq_zero {x : M} (hx : β.val x = 0) (t : ℝ) :
    moserField σ₀ σ₁ β ρ t x = 0 := by
  have h : SmoothForm.degreeOneEquiv β x = 0 :=
    (ContinuousLinearMap.coe_injective.eq_iff' ContinuousLinearMap.toLinearMap_zero).1
      (SmoothForm.degreeOneEquiv_coe_eq_zero_iff.2 hx)
  rw [moserField_def, h, neg_zero, map_zero, smul_zero]

/-- The Moser field vanishes outside the support of the cutoff `ρ`. -/
theorem moserField_eq_zero_of_notMem_tsupport {t : ℝ} {x : M} (h : (t, x) ∉ tsupport ρ) :
    moserField σ₀ σ₁ β ρ t x = 0 := by
  rw [moserField_def, image_eq_zero_of_notMem_tsupport h, zero_smul]

/-- Where the flat map of `σ_t = σ₀ + t (σ₁ - σ₀)` is invertible, the Moser field satisfies
`ι_{X_t} σ_t = -ρ(t, x) β` at `x`. -/
theorem interior_moserField (σ₀ σ₁ : SmoothTwoForm I M) (β : SmoothForm I M ℝ 1)
    (ρ : ℝ × M → ℝ) {t : ℝ} {x : M} (hx : ((σ₀ + t • (σ₁ - σ₀)).flat x).IsInvertible) :
    RoughForm.interior (moserField σ₀ σ₁ β ρ t) (σ₀ + t • (σ₁ - σ₀)).val x =
      -ρ (t, x) • β.val x := by
  rw [SmoothTwoForm.interior_apply_eq_ofSubsingleton_flat, moserField_def, map_smul,
    hx.self_apply_inverse]
  ext v
  have hv : v = ![v 0] := funext fun i ↦ by rw [Fin.fin_one_eq_zero i, Matrix.cons_val_zero]
  rw [hv]
  simp

/-- When the flat map of `σ_t = σ₀ + t (σ₁ - σ₀)` at `x` is invertible at every point `(t, x)` of
the support of `ρ`, the Moser field satisfies `ι_{X_t} σ_t = -ρ(t, ·) β` everywhere: off the
support of `ρ` both sides vanish. -/
theorem interior_moserField_eq
    (hinv : ∀ p ∈ tsupport ρ, ((σ₀ + p.1 • (σ₁ - σ₀)).flat p.2).IsInvertible) (t : ℝ) :
    RoughForm.interior (moserField σ₀ σ₁ β ρ t) (σ₀ + t • (σ₁ - σ₀)).val =
      fun y ↦ -ρ (t, y) • β.val y := by
  funext y
  by_cases hy : (t, y) ∈ tsupport ρ
  · exact interior_moserField σ₀ σ₁ β ρ (hinv _ hy)
  · rw [SmoothTwoForm.interior_apply_eq_ofSubsingleton_flat,
      moserField_eq_zero_of_notMem_tsupport hy, map_zero, image_eq_zero_of_notMem_tsupport hy,
      neg_zero, zero_smul]
    ext v
    simp

variable [FiniteDimensional ℝ E]

/-- The cut-off Moser field `(t, x) ↦ X_t(x)` is smooth at `p₀ = (t₀, x₀)` when `ρ` is smooth at
`p₀` and, if `p₀` lies in the support of `ρ`, the flat map of `σ_{t₀} = σ₀ + t₀ (σ₁ - σ₀)` at `x₀`
is invertible. -/
theorem contMDiffAt_moserField (β : SmoothForm I M ℝ 1) {p₀ : ℝ × M}
    (hρ : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞ ρ p₀)
    (hinv : p₀ ∈ tsupport ρ → ((σ₀ + p₀.1 • (σ₁ - σ₀)).flat p₀.2).IsInvertible) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod I) I.tangent ∞
      (fun p : ℝ × M ↦ (⟨p.2, moserField σ₀ σ₁ β ρ p.1 p.2⟩ : TangentBundle I M)) p₀ := by
  by_cases hp₀ : p₀ ∈ tsupport ρ
  · -- The flat maps of the slices form a smooth section along `Prod.snd`.
    have hflat : ContMDiffAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
        (fun p : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
          (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) p.2
          ((σ₀ + p.1 • (σ₁ - σ₀)).flat p.2)) p₀ := by
      have hσ := SmoothForm.contMDiff_mpullback_prodMk
        (SmoothForm.lineMapFamily σ₀ σ₁ (contDiff_id (n := ∞))) p₀
      simp only [SmoothForm.mpullback_prodMk_lineMapFamily, id_eq] at hσ
      simpa only [← SmoothTwoForm.flat_def] using
        SmoothTwoForm.contMDiffAt_sectionAlong_flatL (b := Prod.snd) hσ
    have hβ : ContMDiffAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
        (fun p : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] ℝ)
          (E := fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) p.2
          (SmoothForm.degreeOneEquiv (-β) p.2)) p₀ :=
      SmoothForm.contMDiffAt_sectionAlong_degreeOneEquiv_iff (α := fun _ ↦ -β).2
        (((-β).contMDiff.comp contMDiff_snd).contMDiffAt)
    simp only [map_neg, ContMDiffSection.coe_neg, Pi.neg_apply] at hβ
    have h := (ContMDiffAt.clm_bundle_inverse (x := p₀) (b := Prod.snd)
      (ϕ := fun p : ℝ × M ↦ (σ₀ + p.1 • (σ₁ - σ₀)).flat p.2)
      hflat (hinv hp₀)).clm_bundle_apply hβ
    exact hρ.smul_totalSpace h
  · -- Away from the support of `ρ` the field vanishes identically.
    refine ((contMDiff_zeroSection ℝ (TangentSpace I)).comp contMDiff_snd).contMDiffAt
      |>.congr_of_eventuallyEq ?_
    filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hp₀] with p hp
    rw [Function.comp_apply, moserField_def, hp, Pi.zero_apply, zero_smul]
    -- The zero section at `p.2` is the pair `⟨p.2, 0⟩` by definition.
    rfl

/-- The cut-off Moser field `(t, x) ↦ X_t(x)` is jointly smooth on `ℝ × M` when `ρ` is smooth and
the flat map of `σ_t = σ₀ + t (σ₁ - σ₀)` at `x` is invertible at every point `(t, x)` of the
support of `ρ`. -/
theorem contMDiff_moserField (β : SmoothForm I M ℝ 1)
    (hρ : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞ ρ)
    (hinv : ∀ p ∈ tsupport ρ, ((σ₀ + p.1 • (σ₁ - σ₀)).flat p.2).IsInvertible) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent ∞
      (fun p : ℝ × M ↦ (⟨p.2, moserField σ₀ σ₁ β ρ p.1 p.2⟩ : TangentBundle I M)) :=
  fun p ↦ contMDiffAt_moserField β (hρ p) (hinv p)

/-- **Moser's equation for the cut-off Moser field.** Let `σ₀` be closed, let `ρ = 1` and let the
flat map of `σ_s` at `z` be invertible at every point `(s, z)` near `(t, y)`, and let
`dβ = σ₁ - σ₀` near `y`. Then the rate `∂_t σ_t + L_{X_t} σ_t` of the family
`σ_t = σ₀ + t (σ₁ - σ₀)` (`TauCeti.SmoothForm.lineMapFamily`) along the cut-off Moser field
vanishes at `y`: `∂_t σ_t = σ₁ - σ₀`, while Cartan's formula gives
`L_{X_t} σ_t = d (ι_{X_t} σ_t) = -dβ`. -/
theorem moserField_rate_eq_zero [I.Boundaryless] (h₀ : σ₀.IsClosed) {t : ℝ} {y : M}
    (hρ : ∀ᶠ p in 𝓝 (t, y), ρ p = 1 ∧ ((σ₀ + p.1 • (σ₁ - σ₀)).flat p.2).IsInvertible)
    (hβ : ∀ᶠ z in 𝓝 y, mextDeriv β.val z = (σ₁ - σ₀).val z) :
    (mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t)
        (mlieDerivForm (fun _ ↦ ((1 : ℝ), (0 : E)))
          (SmoothForm.lineMapFamily σ₀ σ₁ (contDiff_id (n := ∞))).val) +
      mlieDerivForm (moserField σ₀ σ₁ β ρ t)
        (mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t)
          (SmoothForm.lineMapFamily σ₀ σ₁ (contDiff_id (n := ∞))).val)) y = 0 := by
  -- The slices `σ₀ + u (σ₁ - σ₀)` have velocity `σ₁ - σ₀`.
  have hvel : mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t)
      (mlieDerivForm (fun _ ↦ ((1 : ℝ), (0 : E)))
        (SmoothForm.lineMapFamily σ₀ σ₁ (contDiff_id (n := ∞))).val) y = (σ₁ - σ₀).val y := by
    have h := SmoothForm.hasDerivAt_mpullback_prodMk_timeDeriv
      (SmoothForm.lineMapFamily σ₀ σ₁ (contDiff_id (n := ∞))) t y
    simp only [SmoothForm.mpullback_prodMk_lineMapFamily, SmoothForm.coe_mpullback,
      SmoothForm.coe_timeDeriv, id_eq] at h
    refine h.unique ?_
    -- The values of the slices are read in the model fibre `E [⋀^Fin 2]→L[ℝ] ℝ`.
    have h2 := ((hasDerivAt_id t).smul_const
      (@id (E [⋀^Fin 2]→L[ℝ] ℝ) ((σ₁ - σ₀).val y))).const_add
        (@id (E [⋀^Fin 2]→L[ℝ] ℝ) (σ₀.val y))
    rw [one_smul] at h2
    -- `h2` is the goal up to the identity maps, which only fix the type of the values.
    exact h2
  -- The slice at time `t` is closed at `y`, since `σ₁ - σ₀ = dβ` near `y`.
  have hclosed : mextDeriv (σ₀ + t • (σ₁ - σ₀)).val y = 0 := by
    have h₁ : mextDeriv (σ₁ - σ₀).val y = 0 := by
      rw [← mextDeriv_congr_of_eventuallyEq hβ, SmoothForm.mextDeriv_mextDeriv, Pi.zero_apply]
    rw [← mextDerivₗ_apply, map_add, map_smul]
    simp only [SmoothForm.add_toRoughForm, SetLike.val_smul, Pi.add_apply, Pi.smul_apply,
      mextDerivₗ_apply, (SmoothForm.isClosed_def σ₀).1 h₀, h₁, smul_zero, add_zero,
      Pi.zero_apply]
  have hXt : MDifferentiableAt I I.tangent
      (fun z ↦ (⟨z, moserField σ₀ σ₁ β ρ t z⟩ : TangentBundle I M)) y :=
    have hρt : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞ ρ (t, y) :=
      contMDiffAt_const.congr_of_eventuallyEq (hρ.mono fun _ hp ↦ hp.1)
    ((contMDiffAt_moserField β hρt fun _ ↦ hρ.self_of_nhds.2).comp y
      (contMDiffAt_const.prodMk contMDiffAt_id)).mdifferentiableAt (by simp)
  -- Near `y` the contraction `ι_{X_t} σ_t` is `-β`, whose exterior derivative is `-(σ₁ - σ₀)`.
  have hL : mlieDerivForm (moserField σ₀ σ₁ β ρ t) (σ₀ + t • (σ₁ - σ₀)).val y =
      -(σ₁ - σ₀).val y := by
    rw [mlieDerivForm_eq_mextDeriv_interior_apply (SmoothForm.mdifferentiableAt _ y) hXt hclosed]
    have hev : ∀ᶠ z in 𝓝 y, RoughForm.interior (moserField σ₀ σ₁ β ρ t)
        (σ₀ + t • (σ₁ - σ₀)).val z = ((-1 : ℝ) • β.val) z := by
      filter_upwards [(Continuous.prodMk_right t).continuousAt.eventually hρ] with z hz
      rw [interior_moserField σ₀ σ₁ β ρ hz.2, hz.1, Pi.smul_apply]
    rw [mextDeriv_congr_of_eventuallyEq hev, mextDeriv_smul, Pi.smul_apply,
      hβ.self_of_nhds, neg_one_smul]
  rw [Pi.add_apply, hvel, SmoothForm.coe_mpullback_prodMk_lineMapFamily, id_eq, hL,
    add_neg_cancel]

end SymplecticGeometry
