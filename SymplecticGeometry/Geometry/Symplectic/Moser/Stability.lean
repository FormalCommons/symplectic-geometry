/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Basic
public import TauCeti.Geometry.Manifold.DeRham.Basic
public import TauCeti.Geometry.Manifold.Instances.Icc
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.SmoothFamily.Basic
import SymplecticGeometry.Geometry.Diffeomorphism.Diffeotopy.Real
import SymplecticGeometry.Geometry.Manifold.DeRham.SmoothFamily.GoodCover
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Flow.Family
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.TimeExtension
import SymplecticGeometry.Geometry.Symplectic.Manifold.Family
import TauCeti.Geometry.Symplectic.Manifold.Moser.Local
import SymplecticGeometry.Geometry.Manifold.DeRham.GoodCover.Compact
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Family
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Smooth
import SymplecticGeometry.Analysis.SpecialFunctions.SmoothTransition.Basic
import SymplecticGeometry.Topology.Order.NhdsSet

/-!
# Moser stability

Let `M` be a closed manifold and `σ` a smooth two-form on `[0, 1] × M` whose slices
`σ_t = ι_t^* σ` are symplectic and all lie in the de Rham class of `σ_0`. Moser's stability
theorem gives a diffeotopy `ψ_t` of `M` with `ψ_t^* σ_t = σ_0` for every `t`
(`TauCeti.SmoothTwoForm.exists_diffeotopy_mpullback_eq`).

It is a case of a version that holds on any boundaryless manifold: let `τ_t`, `t ∈ [0, 1]`, be
symplectic forms with a smooth family of primitives `β_t` of `τ_t - τ_0` that all vanish outside
a compact set `K`; then a diffeotopy fixed outside `K` pulls each `τ_t` back to `τ_0`
(`TauCeti.SmoothTwoForm.exists_diffeotopy_mpullback_eq_of_isSmoothFamily`). Its proof:

1. Seeley's time extension (`TauCeti.SmoothForm.timeExtend`) extends `β` to a one-form `B` on
   `ℝ × M`. The closed form `ρ = pr_M^* τ_0 + dB` on `ℝ × M` has slices `τ_t` for `t ∈ [0, 1]`,
   and `τ_0` at points outside `K`.
2. Nondegeneracy is open
   (`TauCeti.SmoothTwoForm.isOpen_setOfPred_isInvertible_flat_mpullback_prodMk`) and `K` is
   compact, so the slices of `ρ` are symplectic for times in some `(-δ, 1 + δ)`. Pulling `ρ` back
   along `h × id`, for a smooth `h` that is the identity on `[0, 1]` with values in
   `(-δ, 1 + δ)` (`SymplecticGeometry.exists_contDiff_eqOn_id_Icc_mem_Ioo`), gives a closed form
   all of whose slices are symplectic.
3. The time derivative of a closed form on `ℝ × M` is exact slice by slice, with the
   contraction `ι_{∂_t}` of the form as primitive
   (`TauCeti.SmoothForm.mpullback_prodMk_mlieDerivForm_eq_mextDeriv_timeInterior`). This
   primitive vanishes outside `K`, since `dB` does there, so Tau Ceti's
   `TauCeti.SmoothTwoForm.exists_isotopy_mpullback_eq_of_isCompact` applies, and the isotopy it
   gives restricts to a diffeotopy (`TauCeti.Diffeotopy.ofReal`).

On a closed manifold, the differences `σ_t - σ_0` are a smooth family of exact forms, so they
have a smooth family of primitives (`SymplecticGeometry.exists_isSmoothFamily_mextDerivₗ_eq`,
since a compact manifold has a finite good cover), and the version above with `K = M` gives
Moser stability.

A segment `σ₀ + s (σ₁ - σ₀)`, `s ∈ [0, 1]`, of symplectic forms whose difference `σ₁ - σ₀ = dβ`
has a primitive `β` supported in a compact set `K` is the case `τ_t = σ₀ + t (σ₁ - σ₀)`,
`β_t = t β`, and is joined by a diffeotopy fixed outside `K`
(`TauCeti.SmoothTwoForm.exists_diffeotopy_mpullback_eq_of_mextDeriv_eq_sub`).

Over all of `ℝ`, the primitive of step 3 and Tau Ceti's
`TauCeti.SmoothTwoForm.exists_isotopy_mpullback_eq` give a Moser isotopy of a closed form on
`ℝ × M` with symplectic slices, on a closed manifold
(`TauCeti.SmoothForm.IsClosed.exists_isotopy_mpullback_eq`).

## Main results

* `TauCeti.SmoothForm.IsClosed.exists_isotopy_mpullback_eq`: a closed two-form on `ℝ × M` whose
  slices are symplectic, on a closed manifold, has an isotopy `ψ_t` with `ψ_t^* ρ_t = ρ_0`.
* `TauCeti.SmoothTwoForm.exists_diffeotopy_mpullback_eq`: Moser stability for a family of
  cohomologous symplectic forms over `[0, 1]` on a closed manifold.
* `TauCeti.SmoothTwoForm.exists_diffeotopy_mpullback_eq_of_mextDeriv_eq_sub`: Moser's theorem for
  a segment of symplectic forms with a compactly supported primitive of the difference, as a
  diffeotopy fixed outside the support.
* `TauCeti.SmoothTwoForm.exists_diffeotopy_mpullback_eq_of_isSmoothFamily`: Moser's theorem along
  a family of symplectic forms whose differences have a smooth family of primitives vanishing
  outside a compact set `K`, as a diffeotopy fixed outside `K`.

## References

* J. Moser, *On the volume elements on a manifold*, Transactions of the American Mathematical
  Society 120 (1965), 286–294.
* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §3.2,
  Theorem 3.2.4.
-/

public section

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace TauCeti.SmoothForm.IsClosed

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [CompactSpace M]

/-- **Moser's theorem for a closed form over `ℝ`.** Let `M` be a closed manifold and `ρ` a closed
two-form on `ℝ × M` whose slices `ρ_t = ι_t^* ρ` are all symplectic. Then there is an isotopy
`ψ_t` of `M`, jointly smooth in `(t, x)`, with `ψ_0 = id` and `ψ_t^* ρ_t = ρ_0` for every `t`. -/
theorem exists_isotopy_mpullback_eq {ρ : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) ℝ 2}
    (hρc : ρ.IsClosed)
    (hρ : ∀ t, SmoothTwoForm.IsSymplectic
      (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) ρ)) :
    ∃ ψ : ℝ → M ≃ₘ⟮I, I⟯ M, ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M ↦ ψ p.1 p.2) ∧
      (∀ x, ψ 0 x = x) ∧
      ∀ t, SmoothForm.mpullback (ψ t) (ψ t).contMDiff
          (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) ρ) =
        SmoothForm.mpullback (Prod.mk 0) (contMDiff_const.prodMk contMDiff_id) ρ := by
  obtain ⟨ψ, hψ, hψ₀, -, hψρ⟩ := TauCeti.SmoothTwoForm.exists_isotopy_mpullback_eq ρ
    ρ.timeInterior hρ (SmoothForm.mpullback_prodMk_mlieDerivForm_eq_mextDeriv_timeInterior hρc)
  exact ⟨ψ, hψ, hψ₀, hψρ⟩

end TauCeti.SmoothForm.IsClosed

namespace TauCeti.SmoothTwoForm

open SymplecticGeometry

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] in
/-- Let `C = (h × id)^* timeExtend Ω` for a smooth reparametrization `h` of time, where the slices
of the time extension of `Ω` vanish outside a closed set `K`. The slices of the contraction with
`∂_t` of `pr_M^* σ + dC` vanish outside `K`. -/
private theorem mpullback_prodMk_timeInterior_apply_eq_zero (σ : SmoothTwoForm I M) {h : ℝ → ℝ}
    (hh : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ h) {Ω : SmoothForm ((𝓡∂ 1).prod I) (unitInterval × M) ℝ 1}
    {K : Set M} (hK : IsClosed K) (hΩK : ∀ s, ∀ x ∉ K, (Ω.timeExtendSlice s).val x = 0) (s : ℝ)
    {x : M} (hx : x ∉ K) :
    (SmoothForm.mpullback (Prod.mk s) (contMDiff_const.prodMk contMDiff_id)
      (SmoothForm.mpullback Prod.snd contMDiff_snd σ + mextDerivₗ (𝓘(ℝ, ℝ).prod I) 1
        (SmoothForm.mpullback (Prod.map h id) (hh.prodMap contMDiff_id)
          (SmoothForm.timeExtend Ω))).timeInterior).val x = 0 := by
  set C := SmoothForm.mpullback (Prod.map h id) (hh.prodMap contMDiff_id)
    (SmoothForm.timeExtend Ω)
  have hCK (p : ℝ × M) (hp : p.2 ∉ K) : C.val p = 0 := by
    ext v
    rw [SmoothForm.mpullback_apply, SmoothForm.timeExtend_def, SmoothForm.ofSlices_apply]
    simp only [Prod.map_snd, id_eq]
    rw [hΩK _ _ hp, ContinuousAlternatingMap.coe_zero, Pi.zero_apply,
      ContinuousAlternatingMap.coe_zero, Pi.zero_apply]
  have hdCK : (mextDerivₗ (𝓘(ℝ, ℝ).prod I) 1 C).val (s, x) = 0 := by
    rw [mextDerivₗ_apply, mextDeriv_congr_of_eventuallyEq (η := 0)
      (Filter.eventually_of_mem ((hK.isOpen_compl.preimage continuous_snd).mem_nhds hx)
        fun q hq ↦ hCK q hq), mextDeriv_zero, Pi.zero_apply]
  ext v
  rw [SmoothForm.mpullback_apply, SmoothForm.timeInterior_add,
    SmoothForm.timeInterior_mpullback_snd, zero_add, SmoothForm.timeInterior_def,
    SmoothForm.coe_interiorProduct, RoughForm.interior_apply, hdCK,
    ContinuousAlternatingMap.coe_zero, Pi.zero_apply,
    ContinuousAlternatingMap.coe_zero, Pi.zero_apply]

/-- **Moser's theorem along a family with compactly supported primitives.** Let `τ_t`,
`t ∈ [0, 1]`, be symplectic forms on a boundaryless manifold `M`, and let `β_t` be a smooth family
of one-forms with `dβ_t = τ_t - τ_0`, all vanishing outside a compact set `K`. Then there is a
diffeotopy `Φ` of `M` that fixes every point outside `K` at all times and satisfies
`Φ_t^* τ_t = τ_0` for every `t`. -/
theorem exists_diffeotopy_mpullback_eq_of_isSmoothFamily {τ : unitInterval → SmoothTwoForm I M}
    (hτ : ∀ t, IsSymplectic (τ t)) {β : unitInterval → SmoothForm I M ℝ 1}
    (hβ : IsSmoothFamily (𝓡∂ 1) β) (hdβ : ∀ t, mextDeriv (β t).val = (τ t - τ 0).val)
    {K : Set M} (hK : IsCompact K) (hβK : ∀ t, ∀ x ∉ K, (β t).val x = 0) :
    ∃ Φ : Diffeotopy I ∞ M, (∀ t, ∀ x ∉ K, Φ (t, x) = x) ∧
      ∀ t, SmoothForm.mpullback (Φ.timeSlice t) (Φ.timeSlice t).contMDiff (τ t) = τ 0 := by
  obtain ⟨Ω, hΩ⟩ := isSmoothFamily_def.mp hβ
  -- Step 1: the slices `B_s` of the time extension of `Ω` vanish outside `K`, and so do their
  -- exterior derivatives, since `K` is closed.
  have hBK (s : ℝ) (x : M) (hx : x ∉ K) : (Ω.timeExtendSlice s).val x = 0 := by
    rw [SmoothForm.coe_timeExtendSlice]
    exact timeExtend_eq_zero (F := E [⋀^Fin 1]→L[ℝ] ℝ) (fun t ↦ by rw [hΩ]; exact hβK t x hx) s
  have hdBK (s : ℝ) (x : M) (hx : x ∉ K) : (mextDerivₗ I 1 (Ω.timeExtendSlice s)).val x = 0 := by
    rw [mextDerivₗ_apply, mextDeriv_congr_of_eventuallyEq (η := 0)
      (Filter.eventually_of_mem (hK.isClosed.isOpen_compl.mem_nhds hx) fun y hy ↦ hBK s y hy),
      mextDeriv_zero, Pi.zero_apply]
  -- Step 2: the closed form `ρ = pr_M^* τ_0 + d (timeExtend Ω)` on `ℝ × M`, whose slices
  -- `ρ_s = τ_0 + d B_s` are `τ_s` for `s ∈ [0, 1]`, and `τ_0` outside `K`.
  set ρ : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) ℝ 2 :=
    SmoothForm.mpullback Prod.snd contMDiff_snd (τ 0) +
      mextDerivₗ (𝓘(ℝ, ℝ).prod I) 1 (SmoothForm.timeExtend Ω) with hρ
  have hρc : ρ.IsClosed :=
    ((hτ 0).isClosed.mpullback _ _).add (SmoothForm.isClosed_mextDerivₗ _)
  have hρs (s : ℝ) : SmoothForm.mpullback (Prod.mk s) (contMDiff_const.prodMk contMDiff_id) ρ =
      τ 0 + mextDerivₗ I 1 (Ω.timeExtendSlice s) := by
    rw [hρ, map_add, SmoothForm.mpullback_prodMk_mpullback_snd, ← SmoothForm.mextDerivₗ_mpullback,
      SmoothForm.mpullback_prodMk_timeExtend_eq_timeExtendSlice]
  have hρI (t : unitInterval) :
      SmoothForm.mpullback (Prod.mk (t : ℝ)) (contMDiff_const.prodMk contMDiff_id) ρ = τ t := by
    have h : mextDerivₗ I 1 (β t) = τ t - τ 0 := Subtype.ext (by rw [mextDerivₗ_apply, hdβ])
    rw [hρs, SmoothForm.timeExtendSlice_coe, hΩ, h, add_sub_cancel]
  have hρK (s : ℝ) (x : M) (hx : x ∉ K) :
      (SmoothForm.mpullback (Prod.mk s) (contMDiff_const.prodMk contMDiff_id) ρ).val x =
        (τ 0).val x := by
    rw [hρs, SmoothBundleForm.add_apply, hdBK s x hx, add_zero]
  -- Step 3: the slices `ρ_s` are symplectic for `s` in a neighbourhood `(-δ, 1 + δ)` of
  -- `[0, 1]`: nondegeneracy is open, it holds on `[0, 1] × M`, and off `K` every slice is `τ_0`.
  have hI (t : unitInterval) (x : M) : (flat (SmoothForm.mpullback (Prod.mk (t : ℝ))
      (contMDiff_const.prodMk contMDiff_id) ρ) x).IsInvertible := by
    rw [hρI t]
    exact isNondegenerate_iff_isInvertible_flat.mp (hτ t).isNondegenerate x
  have hKc (s : ℝ) (x : M) (hx : x ∉ K) : (flat (SmoothForm.mpullback (Prod.mk s)
      (contMDiff_const.prodMk contMDiff_id) ρ) x).IsInvertible := by
    rw [flat_def, hρK s x hx, ← flat_def]
    exact isNondegenerate_iff_isInvertible_flat.mp (hτ 0).isNondegenerate x
  set W := {p : ℝ × M | (flat (SmoothForm.mpullback (Prod.mk p.1)
    (contMDiff_const.prodMk contMDiff_id) ρ) p.2).IsInvertible}
  obtain ⟨u, v, hu, -, hIu, hKv, huv⟩ := generalized_tube_lemma isCompact_Icc hK
    (isOpen_setOfPred_isInvertible_flat_mpullback_prodMk ρ) fun p hp ↦ hI ⟨p.1, hp.1⟩ p.2
  obtain ⟨δ, hδ, hsub⟩ := hu.exists_pos_Ioo_subset_of_Icc_subset hIu
  have hgood (s : ℝ) (hs : s ∈ Ioo (0 - δ) (1 + δ)) (x : M) : (flat (SmoothForm.mpullback
      (Prod.mk s) (contMDiff_const.prodMk contMDiff_id) ρ) x).IsInvertible := by
    by_cases hx : x ∈ K
    · exact (huv (mk_mem_prod (hsub hs) (hKv hx)) : (s, x) ∈ W)
    · exact hKc s x hx
  -- Step 4: reparametrize time by a smooth `h` that is the identity on `[0, 1]` and takes its
  -- values in `(-δ, 1 + δ)`, so that every slice of `ρ' = (h × id)^* ρ` is symplectic.
  obtain ⟨h, hh, hhI, hhδ, -⟩ := exists_contDiff_eqOn_id_Icc_mem_Ioo zero_le_one hδ
  have hhm : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ h := hh.contMDiff
  set ρ' := SmoothForm.mpullback (Prod.map h id) (hhm.prodMap contMDiff_id) ρ with hρ'def
  have hρ's (s : ℝ) := SmoothForm.mpullback_prodMk_mpullback_prodMap_id ρ hhm s
  have hρ'c : ρ'.IsClosed := hρc.mpullback _ _
  have hρ'symp (s : ℝ) : IsSymplectic
      (SmoothForm.mpullback (Prod.mk s) (contMDiff_const.prodMk contMDiff_id) ρ') := by
    rw [hρ's]
    exact ⟨hρc.mpullback _ _, isNondegenerate_iff_isInvertible_flat.mpr (hgood _ (hhδ s))⟩
  -- Step 5: `ρ' = pr_M^* τ_0 + d ((h × id)^* timeExtend Ω)`, so the primitive `ι_{∂_t} ρ'` of the
  -- velocity vanishes outside `K`.
  have hρ'C : ρ' = SmoothForm.mpullback Prod.snd contMDiff_snd (τ 0) +
      mextDerivₗ (𝓘(ℝ, ℝ).prod I) 1 (SmoothForm.mpullback (Prod.map h id)
        (hhm.prodMap contMDiff_id) (SmoothForm.timeExtend Ω)) := by
    rw [hρ'def, hρ, map_add, SmoothForm.mpullback_mpullback, SmoothForm.mextDerivₗ_mpullback,
      SmoothForm.mpullback_congr _ contMDiff_snd
        (show Prod.snd ∘ Prod.map h id = Prod.snd from rfl)]
  have hαK (s : ℝ) (x : M) (hx : x ∉ K) : (SmoothForm.mpullback (Prod.mk s)
      (contMDiff_const.prodMk contMDiff_id) ρ'.timeInterior).val x = 0 := by
    rw [hρ'C]
    exact mpullback_prodMk_timeInterior_apply_eq_zero (τ 0) hhm hK.isClosed hBK s hx
  -- Step 6: Tau Ceti's Moser theorem over `ℝ`, restricted to `[0, 1]`.
  obtain ⟨ψ, hψ, hψ₀, hψK, hψρ⟩ := exists_isotopy_mpullback_eq_of_isCompact ρ' ρ'.timeInterior
    hρ'symp (SmoothForm.mpullback_prodMk_mlieDerivForm_eq_mextDeriv_timeInterior hρ'c) hK hαK
  refine ⟨Diffeotopy.ofReal ψ hψ hψ₀, fun t x hx ↦ ?_, fun t ↦ ?_⟩
  · rw [Diffeotopy.ofReal_apply]
    exact hψK t x fun u ↦ hαK u x hx
  · have hρ't (t : unitInterval) :
        SmoothForm.mpullback (Prod.mk (t : ℝ)) (contMDiff_const.prodMk contMDiff_id) ρ' = τ t := by
      rw [hρ's, hhI t.property, id_eq, hρI]
    have h₀ := hρ't 0
    rw [Icc.coe_zero] at h₀
    have h := hψρ t
    rw [hρ't, h₀] at h
    rw [Diffeotopy.timeSlice_ofReal]
    exact h

/-- **Moser's theorem for a segment with a compactly supported primitive.** Let `σ₀`, `σ₁` be
two-forms on a boundaryless manifold `M` such that every form `σ₀ + s (σ₁ - σ₀)`, `s ∈ [0, 1]`, is
symplectic, and let `β` be a primitive of `σ₁ - σ₀` that vanishes outside a compact set `K`. Then
there is a diffeotopy `Φ` of `M` that fixes every point outside `K` at all times, and whose final
map pulls `σ₁` back to `σ₀`. -/
theorem exists_diffeotopy_mpullback_eq_of_mextDeriv_eq_sub {σ₀ σ₁ : SmoothTwoForm I M}
    (hσ : ∀ s ∈ Icc (0 : ℝ) 1, IsSymplectic (σ₀ + s • (σ₁ - σ₀)))
    {β : SmoothForm I M ℝ 1} (hβ : mextDeriv β.val = (σ₁ - σ₀).val) {K : Set M}
    (hK : IsCompact K) (hβK : ∀ x ∉ K, β.val x = 0) :
    ∃ Φ : Diffeotopy I ∞ M, (∀ t, ∀ x ∉ K, Φ (t, x) = x) ∧
      SmoothForm.mpullback Φ.final Φ.final.contMDiff σ₁ = σ₀ := by
  have hdβ : mextDerivₗ I 1 β = σ₁ - σ₀ := Subtype.ext (by rw [mextDerivₗ_apply, hβ])
  obtain ⟨Φ, hΦK, hΦ⟩ := exists_diffeotopy_mpullback_eq_of_isSmoothFamily
    (τ := fun t : unitInterval ↦ σ₀ + (t : ℝ) • (σ₁ - σ₀)) (β := fun t ↦ (t : ℝ) • β)
    (fun t ↦ hσ t t.property) ((isSmoothFamily_const β).fun_smul contMDiff_subtypeVal_Icc)
    (fun t ↦ by
      rw [Icc.coe_zero, zero_smul, add_zero, add_sub_cancel_left, ← mextDerivₗ_apply, map_smul,
        hdβ])
    hK fun t x hx ↦ by rw [SmoothBundleForm.smul_apply, hβK x hx, smul_zero]
  refine ⟨Φ, hΦK, ?_⟩
  have h := hΦ 1
  simp only [Icc.coe_one, Icc.coe_zero, one_smul, zero_smul, add_zero, add_sub_cancel] at h
  rwa [Diffeotopy.final_def]

/-- **Moser stability.** Let `M` be a closed manifold and `σ` a smooth two-form on
`[0, 1] × M` whose slices `σ_t = ι_t^* σ` are symplectic and cohomologous, `σ_t - σ_0` being
exact for every `t`. Then there is a diffeotopy `ψ` of `M`, starting at the identity, with
`ψ_t^* σ_t = σ_0` for every `t ∈ [0, 1]`.

Milestone: *Moser stability*. -/
theorem exists_diffeotopy_mpullback_eq [CompactSpace M]
    (σ : SmoothTwoForm ((𝓡∂ 1).prod I) (unitInterval × M))
    (hσ : ∀ t, IsSymplectic (SmoothForm.mpullback (Prod.mk t)
      (contMDiff_const.prodMk contMDiff_id) σ))
    (hcoh : ∀ t, SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) σ -
        SmoothForm.mpullback (Prod.mk 0) (contMDiff_const.prodMk contMDiff_id) σ ∈
      exactForms I M 2) :
    ∃ Ψ : Diffeotopy I ∞ M, ∀ t, SmoothForm.mpullback (Ψ.timeSlice t) (Ψ.timeSlice t).contMDiff
        (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) σ) =
      SmoothForm.mpullback (Prod.mk 0) (contMDiff_const.prodMk contMDiff_id) σ := by
  obtain ⟨β, hβ, hdβ⟩ := exists_isSmoothFamily_mextDerivₗ_eq (k := 1)
    (hasFiniteGoodCover_of_compactSpace (I := I) (M := M))
    ((isSmoothFamily_mpullback_prodMk σ).sub (isSmoothFamily_const _)) hcoh
  obtain ⟨Ψ, -, hΨ⟩ := exists_diffeotopy_mpullback_eq_of_isSmoothFamily hσ hβ
    (fun t ↦ by rw [← mextDerivₗ_apply, hdβ]) isCompact_univ fun t x hx ↦ absurd (mem_univ x) hx
  exact ⟨Ψ, hΨ⟩

end TauCeti.SmoothTwoForm

end
