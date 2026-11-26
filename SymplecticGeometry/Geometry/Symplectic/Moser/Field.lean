/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.Flat
public import TauCeti.Geometry.Manifold.DifferentialForm.LieDeriv
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Family
public import TauCeti.Geometry.Manifold.DifferentialForm.Flow.Family
import SymplecticGeometry.Topology.Algebra.Module.Alternating.Basic
import SymplecticGeometry.Geometry.Symplectic.Manifold.Flat
import TauCeti.Geometry.Manifold.VectorBundle.Scalar
import SymplecticGeometry.Topology.VectorBundle.Basic

/-!
# The cut-off Moser field of a family of two-forms

Let `σ` be a smooth two-form and `β` a smooth one-form on `N × M`, with slices
`σ_t = ι_t^* σ` and `β_t = ι_t^* β` along `ι_t : x ↦ (t, x)`, and let `ρ : N × M → ℝ`.
`SymplecticGeometry.moserField σ β ρ` is the field `X_t = ρ(t, ·) (σ_t♭)⁻¹(-β_t)` on `M`,
depending on `t : N`, where `σ_t♭` is the flat map `v ↦ ι_v σ_t`. Where `σ_t` is nondegenerate it
is the field with `ι_{X_t} σ_t = -ρ(t, ·) β_t`.

For `N = ℝ`, suppose that `σ_t` is closed at a point `y`, that the time derivative of `σ` at
`(t, y)` is `dβ_t`, and that near `y` we have `ρ(t, ·) = 1` and `σ_t` nondegenerate. Then
Cartan's formula gives Moser's equation `∂_t σ_t + L_{X_t} σ_t = dβ_t - dβ_t = 0` at `y`, which
is the hypothesis of Tau Ceti's Moser principle along trajectories
(`TauCeti.mpullback_timeDependentFlowOf_mpullback_prodMk_apply_eq_of_forall_mem_uIcc`).
The segment `σ_t = σ₀ + t (σ₁ - σ₀)` with a primitive `β` constant in time is the family
`TauCeti.SmoothForm.lineMapFamily σ₀ σ₁ contDiff_id` with `β` pulled back along `Prod.snd`.

## Main definitions and results

* `SymplecticGeometry.moserField`: the cut-off Moser field of a family of two-forms.
* `SymplecticGeometry.interior_moserField`, `SymplecticGeometry.interior_moserField_eq`:
  the identity `ι_{X_t} σ_t = -ρ(t, ·) β_t`.
* `SymplecticGeometry.exists_isCompact_moserField_eq_zero`: for a cutoff with compact support,
  the field vanishes at every time outside one compact subset of `M`.
* `SymplecticGeometry.isCompleteVectorField_timeDependentSuspensionField_moserField`: for a cutoff
  with compact support, the suspension of a jointly `C¹` field is complete.
* `SymplecticGeometry.contMDiffAt_moserField`, `SymplecticGeometry.contMDiff_moserField`: the
  field is jointly smooth on `N × M` where `ρ` is smooth and `σ_t` is nondegenerate at every
  point `(t, x)` of the support of `ρ`.
* `SymplecticGeometry.contMDiff_moserField_lineMapFamily`: for the segment `s ↦ W + s • D`, the
  field is jointly smooth where `ρ` is smooth and `W + s • D` is nondegenerate on the support
  of `ρ`.
* `SymplecticGeometry.moserField_rate_eq_zero`: Moser's equation at a point `y` near which
  `ρ(t, ·) = 1` and `σ_t` is nondegenerate, where `σ_t` is closed and `∂_t σ_t = dβ_t`.
* `TauCeti.SmoothTwoForm.mpullback_timeDependentFlowOf_moserField_lineMapFamily_apply`: Moser's
  argument at one point along a segment, with a primitive constant in the Moser time.

The definition and the proofs adapt Tau Ceti's private `moserField`, `moserField_eq_zero`,
`interior_moserField`, `interior_moserField_eq`, `contMDiff_moserField` and `moserRate_eq_zero`
(`TauCeti/Geometry/Symplectic/Manifold/RelativeMoser.lean`) from the segment
reparametrized by `Real.smoothTransition`, a fixed primitive and a cutoff on `M` to a general
family, a primitive depending on the parameter and a cutoff on `N × M`. The proof of joint
smoothness follows Tau Ceti's
`TauCeti.SmoothTwoForm.contMDiff_interiorEquiv_symm_mpullback_prodMk`. The proof of
`TauCeti.SmoothTwoForm.mpullback_timeDependentFlowOf_moserField_lineMapFamily_apply` adapts the
trajectory argument of Tau Ceti's
`TauCeti.SmoothTwoForm.exists_diffeomorph_fix_eventually_mpullback_eq_of_mextDeriv_eq_sub`
(`TauCeti/Geometry/Symplectic/Manifold/RelativeMoser.lean`) from a segment reparametrized by
`Real.smoothTransition` and a cutoff on `N` to the plain segment and a cutoff on `ℝ × N`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §3.2.
* [A. Cannas da Silva, *Lectures on Symplectic Geometry*][CannasdaSilva2001Lectures], Lectures 6–7.
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
  {EN HN N : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
  {J : ModelWithCorners ℝ EN HN} [TopologicalSpace N] [ChartedSpace HN N] [IsManifold J ∞ N]
  {σ : SmoothForm (J.prod I) (N × M) ℝ 2} {β : SmoothForm (J.prod I) (N × M) ℝ 1}
  {ρ : N × M → ℝ}

/-- The **cut-off Moser field** of a family of two-forms, given as a two-form `σ` on `N × M`,
and of a family of one-forms, given as a one-form `β` on `N × M`, cut off by `ρ : N × M → ℝ`:
`X_t(x) = ρ(t, x) (σ_t♭)⁻¹(-β_t)(x)`, where `σ_t` and `β_t` are the slices of `σ` and `β` at
`t : N` and `σ_t♭` is the flat map of `σ_t` at `x`. Where the flat map is not invertible,
`ContinuousLinearMap.inverse` gives `0`. -/
def moserField (σ : SmoothForm (J.prod I) (N × M) ℝ 2) (β : SmoothForm (J.prod I) (N × M) ℝ 1)
    (ρ : N × M → ℝ) (t : N) (x : M) : TangentSpace I x :=
  ρ (t, x) • (SmoothTwoForm.flat
    (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) σ) x).inverse
      (-SmoothForm.degreeOneEquiv
        (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) β) x)

theorem moserField_def (σ : SmoothForm (J.prod I) (N × M) ℝ 2)
    (β : SmoothForm (J.prod I) (N × M) ℝ 1) (ρ : N × M → ℝ) (t : N) (x : M) :
    moserField σ β ρ t x =
      ρ (t, x) • (SmoothTwoForm.flat
        (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) σ) x).inverse
          (-SmoothForm.degreeOneEquiv
            (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) β) x) :=
  (rfl)

/-- The Moser field vanishes where the slice of the one-form `β` does. -/
theorem moserField_eq_zero_of_apply_eq_zero {t : N} {x : M}
    (hx : (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) β).val x = 0) :
    moserField σ β ρ t x = 0 := by
  have h : SmoothForm.degreeOneEquiv
      (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) β) x = 0 :=
    SmoothForm.degreeOneEquiv_apply_eq_zero_iff.2 hx
  rw [moserField_def, h, neg_zero, map_zero, smul_zero]

/-- The Moser field vanishes outside the support of the cutoff `ρ`. -/
theorem moserField_eq_zero_of_notMem_tsupport {t : N} {x : M} (h : (t, x) ∉ tsupport ρ) :
    moserField σ β ρ t x = 0 := by
  rw [moserField_def, image_eq_zero_of_notMem_tsupport h, zero_smul]

/-- When the cutoff `ρ` has compact support, the cut-off Moser field vanishes, at every time,
outside a compact subset of `M`: the projection of the support of `ρ`. -/
theorem exists_isCompact_moserField_eq_zero (hρ : HasCompactSupport ρ) :
    ∃ K : Set M, IsCompact K ∧ ∀ t, ∀ x ∉ K, moserField σ β ρ t x = 0 :=
  ⟨Prod.snd '' tsupport ρ, hρ.isCompact.image continuous_snd, fun _ _ hx ↦
    moserField_eq_zero_of_notMem_tsupport fun h ↦ hx ⟨_, h, rfl⟩⟩

/-- **The suspension of the cut-off Moser field is complete** when the cutoff has compact support
and the field is jointly `C¹`: the field then vanishes, at every time, outside a fixed compact
set, so its time-dependent flow is defined between any two times. -/
theorem isCompleteVectorField_timeDependentSuspensionField_moserField [CompleteSpace E]
    [T2Space M] [BoundarylessManifold I M] {σ : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) ℝ 2}
    {β : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) ℝ 1} {ρ : ℝ × M → ℝ}
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 1
      (fun p : ℝ × M ↦ (⟨p.2, moserField σ β ρ p.1 p.2⟩ : TangentBundle I M)))
    (hρ : HasCompactSupport ρ) :
    IsCompleteVectorField (timeDependentSuspensionField (moserField σ β ρ)) := by
  obtain ⟨K, hK, hXK⟩ := exists_isCompact_moserField_eq_zero (J := 𝓘(ℝ, ℝ)) (σ := σ) (β := β) hρ
  exact isCompleteVectorField_timeDependentSuspensionField hX hK hXK

/-- Where the flat map of the slice `σ_t` at `x` is invertible, the Moser field satisfies
`ι_{X_t} σ_t = -ρ(t, x) β_t` at `x`. -/
theorem interior_moserField (σ : SmoothForm (J.prod I) (N × M) ℝ 2)
    (β : SmoothForm (J.prod I) (N × M) ℝ 1) (ρ : N × M → ℝ) {t : N} {x : M}
    (hx : (SmoothTwoForm.flat
      (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) σ) x).IsInvertible) :
    RoughForm.interior (moserField σ β ρ t)
        (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) σ).val x =
      -ρ (t, x) •
        (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) β).val x := by
  rw [SmoothTwoForm.interior_apply_eq_ofSubsingleton_flat, moserField_def, map_smul,
    hx.self_apply_inverse]
  ext w
  simp

/-- When the flat map of the slice `σ_t` at `x` is invertible at every point `(t, x)` of the
support of `ρ`, the Moser field satisfies `ι_{X_t} σ_t = -ρ(t, ·) β_t` everywhere: off the
support of `ρ` both sides vanish. -/
theorem interior_moserField_eq
    (hinv : ∀ p ∈ tsupport ρ, (SmoothTwoForm.flat
      (SmoothForm.mpullback (Prod.mk p.1) (contMDiff_const.prodMk contMDiff_id) σ)
        p.2).IsInvertible) (t : N) :
    RoughForm.interior (moserField σ β ρ t)
        (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) σ).val =
      fun y ↦ -ρ (t, y) •
        (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) β).val y := by
  funext y
  by_cases hy : (t, y) ∈ tsupport ρ
  · exact interior_moserField σ β ρ (hinv _ hy)
  · rw [SmoothTwoForm.interior_apply_eq_ofSubsingleton_flat,
      moserField_eq_zero_of_notMem_tsupport hy, map_zero, image_eq_zero_of_notMem_tsupport hy,
      neg_zero, zero_smul]
    ext v
    simp

variable [FiniteDimensional ℝ E]

/-- The cut-off Moser field `(t, x) ↦ X_t(x)` is smooth at `p₀ = (t₀, x₀)` when `ρ` is smooth at
`p₀` and, if `p₀` lies in the support of `ρ`, the flat map of the slice `σ_{t₀}` at `x₀` is
invertible. -/
theorem contMDiffAt_moserField (σ : SmoothForm (J.prod I) (N × M) ℝ 2)
    (β : SmoothForm (J.prod I) (N × M) ℝ 1) {p₀ : N × M}
    (hρ : ContMDiffAt (J.prod I) 𝓘(ℝ) ∞ ρ p₀)
    (hinv : p₀ ∈ tsupport ρ → (SmoothTwoForm.flat
      (SmoothForm.mpullback (Prod.mk p₀.1) (contMDiff_const.prodMk contMDiff_id) σ)
        p₀.2).IsInvertible) :
    ContMDiffAt (J.prod I) I.tangent ∞
      (fun p : N × M ↦ (⟨p.2, moserField σ β ρ p.1 p.2⟩ : TangentBundle I M)) p₀ := by
  by_cases hp₀ : p₀ ∈ tsupport ρ
  · -- The slices of `σ` and of `-β` are smooth sections along `Prod.snd`.
    have hσ := SmoothForm.contMDiff_mpullback_prodMk σ p₀
    have hβ := (SmoothForm.contMDiffAt_sectionAlong_degreeOneEquiv_iff (b := Prod.snd)
      (α := fun q : N × M ↦
        SmoothForm.mpullback (Prod.mk q.1) (contMDiff_const.prodMk contMDiff_id) (-β))).2
      (SmoothForm.contMDiff_mpullback_prodMk (-β) p₀)
    simp only [map_neg, ContMDiffSection.coe_neg, Pi.neg_apply] at hβ
    exact hρ.smul_totalSpace
      (SmoothTwoForm.contMDiffAt_sectionAlong_flat_inverse_apply hσ (hinv hp₀) hβ)
  · -- Away from the support of `ρ` the field vanishes identically.
    refine ((contMDiff_zeroSection ℝ (TangentSpace I)).comp contMDiff_snd).contMDiffAt
      |>.congr_of_eventuallyEq ?_
    filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hp₀] with p hp
    rw [Function.comp_apply, moserField_def, hp, Pi.zero_apply, zero_smul, zeroSection_def]

/-- The cut-off Moser field `(t, x) ↦ X_t(x)` is jointly smooth on `N × M` when `ρ` is smooth and
the flat map of the slice `σ_t` at `x` is invertible at every point `(t, x)` of the support of
`ρ`. -/
theorem contMDiff_moserField (σ : SmoothForm (J.prod I) (N × M) ℝ 2)
    (β : SmoothForm (J.prod I) (N × M) ℝ 1)
    (hρ : ContMDiff (J.prod I) 𝓘(ℝ) ∞ ρ)
    (hinv : ∀ p ∈ tsupport ρ, (SmoothTwoForm.flat
      (SmoothForm.mpullback (Prod.mk p.1) (contMDiff_const.prodMk contMDiff_id) σ)
        p.2).IsInvertible) :
    ContMDiff (J.prod I) I.tangent ∞
      (fun p : N × M ↦ (⟨p.2, moserField σ β ρ p.1 p.2⟩ : TangentBundle I M)) :=
  fun p ↦ contMDiffAt_moserField σ β (hρ p) (hinv p)

/-- The cut-off Moser field of the segment `s ↦ W + s • D` of two-forms on `M`
(`TauCeti.SmoothForm.lineMapFamily W (W + D) contDiff_id`) is jointly smooth on `ℝ × M` when `ρ`
is smooth and `W + s • D` is nondegenerate at `x` for every point `(s, x)` of the support of
`ρ`. -/
theorem contMDiff_moserField_lineMapFamily (W D : SmoothForm I M ℝ 2)
    (β : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) ℝ 1) {ρ : ℝ × M → ℝ}
    (hρ : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞ ρ)
    (hnd : ∀ p ∈ tsupport ρ, ((W + p.1 • D).bilinFormAt p.2).Nondegenerate) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent ∞ (fun p : ℝ × M ↦ (⟨p.2, moserField
      (SmoothForm.lineMapFamily W (W + D) (contDiff_id (E := ℝ))) β ρ p.1 p.2⟩ :
        TangentBundle I M)) :=
  contMDiff_moserField _ _ hρ fun p hp ↦ by
    rw [SmoothForm.mpullback_prodMk_lineMapFamily, add_sub_cancel_left, id]
    exact SmoothTwoForm.isInvertible_flat_iff.mpr (hnd p hp)

/-- **Moser's equation for the cut-off Moser field.** Let `σ` and `β` be forms on `ℝ × M`. At a
point `y` where the slice `σ_t` is closed and the slice of the time derivative `∂_t σ` is `dβ_t`,
if `ρ (t, z) = 1` and the flat map of `σ_t` at `z` is invertible at every point `z` near `y`,
then the rate `∂_t σ_t + L_{X_t} σ_t` of `σ` along the cut-off Moser field vanishes at `y`:
Cartan's formula gives `L_{X_t} σ_t = d (ι_{X_t} σ_t) = -dβ_t` at `y`. -/
theorem moserField_rate_eq_zero {σ : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) ℝ 2}
    {β : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) ℝ 1} {ρ : ℝ × M → ℝ} {t : ℝ} {y : M}
    (hσ : mextDeriv
      (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) σ).val y = 0)
    (hρ : ∀ᶠ z in 𝓝 y, ρ (t, z) = 1 ∧ (SmoothTwoForm.flat
      (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) σ)
        z).IsInvertible)
    (hβ : (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id)
        σ.timeDeriv).val y =
      mextDeriv (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) β).val
        y) :
    (mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t)
        (mlieDerivForm (fun _ ↦ ((1 : ℝ), (0 : E))) σ.val) +
      mlieDerivForm (moserField σ β ρ t) (mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t) σ.val))
        y = 0 := by
  -- The cutoff `(s, z) ↦ ρ (t, z)` gives the same field at time `t` and is constant near
  -- `(t, y)`, so smoothness of the field at `y` needs `hρ` only on the slice at `t`.
  have hXt : MDifferentiableAt I I.tangent
      (fun z ↦ (⟨z, moserField σ β ρ t z⟩ : TangentBundle I M)) y :=
    have hρ' : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞ (fun p : ℝ × M ↦ ρ (t, p.2)) (t, y) :=
      contMDiffAt_const.congr_of_eventuallyEq
        ((continuous_snd.continuousAt.eventually hρ).mono fun _ hp ↦ hp.1)
    ((contMDiffAt_moserField σ β hρ' fun _ ↦ hρ.self_of_nhds.2).comp y
      (contMDiffAt_const.prodMk contMDiffAt_id)).mdifferentiableAt (by simp)
  -- Near `y` the contraction `ι_{X_t} σ_t` is `-β_t`, whose exterior derivative at `y` is
  -- `-(∂_t σ)_t`.
  have hL : mlieDerivForm (moserField σ β ρ t)
      (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) σ).val y =
      -(SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id)
        σ.timeDeriv).val y := by
    rw [mlieDerivForm_eq_mextDeriv_interior_apply (SmoothForm.mdifferentiableAt _ y) hXt hσ]
    have hev : ∀ᶠ z in 𝓝 y, RoughForm.interior (moserField σ β ρ t)
        (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) σ).val z =
        ((-1 : ℝ) •
          (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) β).val) z := by
      filter_upwards [hρ] with z hz
      rw [interior_moserField σ β ρ hz.2, hz.1, Pi.smul_apply]
    rw [mextDeriv_congr_of_eventuallyEq hev, mextDeriv_smul, Pi.smul_apply, ← hβ, neg_one_smul]
  have hs : ContMDiff I (𝓘(ℝ, ℝ).prod I) ∞ (Prod.mk t : M → ℝ × M) :=
    contMDiff_const.prodMk contMDiff_id
  rw [Pi.add_apply, ← SmoothForm.coe_timeDeriv, ← SmoothForm.coe_mpullback _ hs,
    ← SmoothForm.coe_mpullback _ hs, hL, add_neg_cancel]

end SymplecticGeometry

namespace TauCeti.SmoothTwoForm

open SymplecticGeometry

variable {E H N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T2Space N]

/-- **Moser's argument at one point along a segment.** Let `ω₀` be a closed two-form and `α` a
two-form on `N` with `α - ω₀ = dγ`, and let the cut-off Moser field of the segment
`s ↦ ω₀ + s (α - ω₀)`, with the primitive `γ` constant in `s` and a cutoff `ρ` on `ℝ × N`, be
jointly `C²` with complete suspension. If, for every `s ∈ [0, 1]`, the point reached at time `s`
by the trajectory of `x` from time `0` has a neighbourhood on which `ρ (s, ·) = 1` and the flat
map of `ω₀ + s (α - ω₀)` is invertible, then the time-one map pulls `α` back to `ω₀` at `x`. -/
theorem mpullback_timeDependentFlowOf_moserField_lineMapFamily_apply
    {ω₀ α : SmoothTwoForm I N} (hω₀ : ω₀.IsClosed) {γ : SmoothForm I N ℝ 1}
    (hγ : α - ω₀ = mextDerivₗ I 1 γ) {ρ : ℝ × N → ℝ}
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 2 (fun p : ℝ × N ↦
      (⟨p.2, moserField (SmoothForm.lineMapFamily ω₀ α contDiff_id)
        (SmoothForm.mpullback Prod.snd contMDiff_snd γ) ρ p.1 p.2⟩ : TangentBundle I N)))
    (hc : IsCompleteVectorField (timeDependentSuspensionField
      (moserField (SmoothForm.lineMapFamily ω₀ α contDiff_id)
        (SmoothForm.mpullback Prod.snd contMDiff_snd γ) ρ)))
    {x : N} (hx : ∀ s ∈ Icc (0 : ℝ) 1, ∀ᶠ z in 𝓝 (timeDependentFlowOf
      (moserField (SmoothForm.lineMapFamily ω₀ α contDiff_id)
        (SmoothForm.mpullback Prod.snd contMDiff_snd γ) ρ) 0 s x),
      ρ (s, z) = 1 ∧ (SmoothTwoForm.flat (ω₀ + s • (α - ω₀)) z).IsInvertible) :
    TauCeti.mpullback I I (timeDependentFlowOf
      (moserField (SmoothForm.lineMapFamily ω₀ α contDiff_id)
        (SmoothForm.mpullback Prod.snd contMDiff_snd γ) ρ) 0 1) α.val x = ω₀.val x := by
  set Λ := SmoothForm.lineMapFamily ω₀ α contDiff_id
  -- Moser's equation holds along the trajectory of `x` up to time `1`.
  have hrate (s : ℝ) (hs : s ∈ uIcc (0 : ℝ) 1) :
      (TauCeti.mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk s)
          (mlieDerivForm (fun _ ↦ ((1 : ℝ), (0 : E))) Λ.val) +
        mlieDerivForm (moserField Λ (SmoothForm.mpullback Prod.snd contMDiff_snd γ) ρ s)
          (TauCeti.mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk s) Λ.val))
        (timeDependentFlowOf
          (moserField Λ (SmoothForm.mpullback Prod.snd contMDiff_snd γ) ρ) 0 s x) = 0 := by
    have hcl : (SmoothForm.mpullback (Prod.mk s) (contMDiff_const.prodMk contMDiff_id)
        Λ).IsClosed := by
      rw [SmoothForm.mpullback_prodMk_lineMapFamily, hγ]
      exact hω₀.add ((SmoothForm.isClosed_mextDerivₗ _).smul _)
    refine moserField_rate_eq_zero (congrFun ((SmoothForm.isClosed_def _).1 hcl) _)
      (by simpa only [Λ, SmoothForm.mpullback_prodMk_lineMapFamily, id] using
        hx s (uIcc_of_le (zero_le_one (α := ℝ)) ▸ hs)) ?_
    rw [SmoothForm.mpullback_prodMk_timeDeriv_lineMapFamily, deriv_id, one_smul,
      SmoothForm.mpullback_prodMk_mpullback_snd, hγ, mextDerivₗ_apply]
  have h := mpullback_timeDependentFlowOf_mpullback_prodMk_apply_eq_of_forall_mem_uIcc
    hX hc (fun _ _ ↦ (Λ.contMDiff.of_le (by simp)).contMDiffAt)
    (s := 0) (t := 1) (x := x) hrate
  have h1 : SmoothForm.mpullback (Prod.mk 1) (contMDiff_const.prodMk contMDiff_id) Λ = α := by
    rw [SmoothForm.mpullback_prodMk_lineMapFamily, id, one_smul, add_sub_cancel]
  have h0 : SmoothForm.mpullback (Prod.mk 0) (contMDiff_const.prodMk contMDiff_id) Λ = ω₀ := by
    rw [SmoothForm.mpullback_prodMk_lineMapFamily, id, zero_smul, add_zero]
  rw [← h1, SmoothForm.coe_mpullback, ← h0, SmoothForm.coe_mpullback]
  exact h

end TauCeti.SmoothTwoForm
