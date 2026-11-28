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
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Pullback.Smooth
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Smooth
import SymplecticGeometry.Analysis.SpecialFunctions.SmoothTransition.Basic

/-!
# Moser stability

Let `M` be a closed manifold and `σ` a smooth two-form on `[0, 1] × M` whose slices
`σ_t = ι_t^* σ` are symplectic and all lie in the de Rham class of `σ_0`. Moser's stability
theorem gives a diffeotopy `ψ_t` of `M` with `ψ_t^* σ_t = σ_0` for every `t`
(`TauCeti.SmoothTwoForm.exists_diffeotopy_mpullback_eq`).

The proof reduces to Tau Ceti's Moser theorem over a compact interval of times,
`TauCeti.SmoothTwoForm.exists_isotopy_mpullback_eq_of_uIcc_subset`, which takes a family over an
open set `J` of times with symplectic slices, an interval `[a, b] ⊆ J`, and a smooth family of
primitives of its velocity.

1. The differences `σ_t - σ_0` are a smooth family of exact forms, so they have a smooth family
   of primitives `β_t` (`SymplecticGeometry.exists_isSmoothFamily_mextDerivₗ_eq`, since a compact
   manifold has a finite good cover).
2. Seeley's time extension (`TauCeti.SmoothForm.timeExtend`) extends `β` to a one-form `B` on
   `ℝ × M`. The closed form `τ = pr_M^* σ_0 + dB` on `ℝ × M` has the slices
   `τ_s = σ_0 + d B_s`, equal to `σ_s` for `s ∈ [0, 1]`.
3. Nondegeneracy is open and `M` is compact, so the parameters `s` at which `τ_s` is
   nondegenerate form an open set `P` containing `[0, 1]`
   (`TauCeti.SmoothTwoForm.isOpen_setOfPred_forall_isInvertible_flat_mpullback_prodMk`). The
   restriction of `τ` to `P × M` has symplectic slices.
4. The time derivative of a closed form `ρ` on `ℝ × M` is exact
   (`TauCeti.SmoothForm.mextDerivₗ_timeInterior`: `∂_t ρ = d (ι_{∂_t} ρ)`), slice by slice
   (`TauCeti.SmoothForm.mpullback_prodMk_mlieDerivForm_eq_mextDeriv_timeInterior`), and the
   restriction to `P × M` keeps the time derivative
   (`TauCeti.mpullback_prodMk_mlieDerivForm_mpullback_prodMap_subtypeVal`). So the restriction
   of `ι_{∂_t} τ` is the primitive that Tau Ceti's theorem asks for on `[0, 1] ⊆ P`, and the
   isotopy it gives restricts to a diffeotopy (`TauCeti.Diffeotopy.ofReal`).

The same computation over all of `ℝ`, with Tau Ceti's
`TauCeti.SmoothTwoForm.exists_isotopy_mpullback_eq`, gives a Moser isotopy of a closed form on
`ℝ × M` with symplectic slices (`TauCeti.SmoothForm.IsClosed.exists_isotopy_mpullback_eq`).

On a manifold that need not be compact, a segment `σ₀ + s (σ₁ - σ₀)`, `s ∈ [0, 1]`, of
symplectic forms whose difference `σ₁ - σ₀ = dβ` has a primitive `β` supported in a compact set
`K` is joined by a diffeotopy fixed outside `K`
(`TauCeti.SmoothTwoForm.exists_diffeotopy_mpullback_eq_of_mextDeriv_eq_sub`). It applies Tau
Ceti's `TauCeti.SmoothTwoForm.exists_isotopy_mpullback_eq_of_isCompact` to the path
`σ₀ + c(t) (σ₁ - σ₀)` (`TauCeti.SmoothForm.lineMapFamily`), `c = Real.smoothTransition`, whose
velocity has the primitive `c'(t) β`, as the proof of the local version
`TauCeti.SmoothTwoForm.exists_partialDiffeomorph_mpullback_eq_of_mextDeriv_eq_sub` does, and
restricts the isotopy to `[0, 1]`.

The same holds along a family: let `τ_t`, `t ∈ [0, 1]`, be symplectic forms with a smooth family
of primitives `β_t` of `τ_t - τ_0` that all vanish outside a compact set `K`
(`TauCeti.SmoothTwoForm.exists_diffeotopy_mpullback_eq_of_isSmoothFamily`). Seeley's time
extension of `β` gives the closed form `ρ = pr_M^* τ_0 + dB` on `ℝ × M`, with slices `τ_t` for
`t ∈ [0, 1]` and `τ_0` at points outside `K`. Nondegeneracy is open
(`TauCeti.SmoothTwoForm.isOpen_setOfPred_isInvertible_flat_mpullback_prodMk`) and `K` is compact,
so the slices of `ρ` are symplectic for times in some `(-δ, 1 + δ)`. Pulling `ρ` back along
`h × id`, for a smooth `h` that is the identity on `[0, 1]` with values in `(-δ, 1 + δ)`
(`SymplecticGeometry.exists_contDiff_eqOn_id_Icc_mem_Ioo`), gives a form all of whose slices are
symplectic. Its contraction with `∂_t` is a primitive of its velocity, as in step 4 above, and it
vanishes outside `K` since `dB` does there; Tau Ceti's
`TauCeti.SmoothTwoForm.exists_isotopy_mpullback_eq_of_isCompact` applies.

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
  [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [CompactSpace M]

/-- **Moser stability.** Let `M` be a closed manifold and `σ` a smooth two-form on
`[0, 1] × M` whose slices `σ_t = ι_t^* σ` are symplectic and cohomologous, `σ_t - σ_0` being
exact for every `t`. Then there is a diffeotopy `ψ` of `M`, starting at the identity, with
`ψ_t^* σ_t = σ_0` for every `t ∈ [0, 1]`.

Milestone: *Moser stability*. -/
theorem exists_diffeotopy_mpullback_eq (σ : SmoothTwoForm ((𝓡∂ 1).prod I) (unitInterval × M))
    (hσ : ∀ t, IsSymplectic (SmoothForm.mpullback (Prod.mk t)
      (contMDiff_const.prodMk contMDiff_id) σ))
    (hcoh : ∀ t, SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) σ -
        SmoothForm.mpullback (Prod.mk 0) (contMDiff_const.prodMk contMDiff_id) σ ∈
      exactForms I M 2) :
    ∃ Ψ : Diffeotopy I ∞ M, ∀ t, SmoothForm.mpullback (Ψ.timeSlice t) (Ψ.timeSlice t).contMDiff
        (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) σ) =
      SmoothForm.mpullback (Prod.mk 0) (contMDiff_const.prodMk contMDiff_id) σ := by
  set σ₀ := SmoothForm.mpullback (Prod.mk (0 : unitInterval))
    (contMDiff_const.prodMk contMDiff_id) σ
  -- Step 1: a smooth family of primitives of `σ_t - σ_0`.
  obtain ⟨β, hβ, hdβ⟩ := exists_isSmoothFamily_mextDerivₗ_eq (k := 1)
    (hasFiniteGoodCover_of_compactSpace (I := I) (M := M))
    ((isSmoothFamily_mpullback_prodMk σ).sub (isSmoothFamily_const σ₀)) hcoh
  obtain ⟨B, hB⟩ := isSmoothFamily_def.mp hβ
  -- Step 2: the closed form `τ = pr_M^* σ_0 + d B` on `ℝ × M`.
  set τ : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) ℝ 2 :=
    SmoothForm.mpullback Prod.snd contMDiff_snd σ₀ +
      mextDerivₗ (𝓘(ℝ, ℝ).prod I) 1 (SmoothForm.timeExtend B) with hτ
  have hτc : τ.IsClosed :=
    ((hσ 0).isClosed.mpullback _ _).add (SmoothForm.isClosed_mextDerivₗ _)
  have hτs (s : ℝ) : SmoothForm.mpullback (Prod.mk s) (contMDiff_const.prodMk contMDiff_id) τ =
      σ₀ + mextDerivₗ I 1 (SmoothForm.timeExtendSlice B s) := by
    rw [hτ, map_add, SmoothForm.mpullback_prodMk_mpullback_snd, ← SmoothForm.mextDerivₗ_mpullback,
      SmoothForm.mpullback_prodMk_timeExtend_eq_timeExtendSlice]
  have hτI (t : unitInterval) :
      SmoothForm.mpullback (Prod.mk (t : ℝ)) (contMDiff_const.prodMk contMDiff_id) τ =
        SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) σ := by
    rw [hτs, SmoothForm.timeExtendSlice_coe, hB, hdβ, add_sub_cancel]
  -- Step 3: the slices of `τ` are nondegenerate at the times of an open set `P ⊇ [0, 1]`, so the
  -- restriction `τ'` of `τ` to `P × M` has symplectic slices.
  let P : TopologicalSpace.Opens ℝ := ⟨{s | ∀ x : M, (flat (SmoothForm.mpullback (Prod.mk s)
    (contMDiff_const.prodMk contMDiff_id) τ) x).IsInvertible},
    isOpen_setOfPred_forall_isInvertible_flat_mpullback_prodMk τ⟩
  have hIP : uIcc (0 : ℝ) 1 ⊆ P := fun s hs x ↦ by
    rw [uIcc_of_le zero_le_one] at hs
    have h := hτI ⟨s, hs⟩
    rw [Subtype.coe_mk] at h
    rw [h]
    exact isNondegenerate_iff_isInvertible_flat.mp (hσ _).isNondegenerate x
  have hres {k : ℕ} (β : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) ℝ k) (t : P) :=
    SmoothForm.mpullback_prodMk_mpullback_prodMap_id β contMDiff_subtypeVal t
  set τ' := SmoothForm.mpullback (Prod.map (Subtype.val : P → ℝ) id)
    (contMDiff_subtypeVal.prodMap contMDiff_id) τ
  have hτ'symp (t : P) : IsSymplectic
      (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) τ') := by
    rw [hres]
    exact ⟨hτc.mpullback _ _, isNondegenerate_iff_isInvertible_flat.mpr t.property⟩
  -- Step 4: Moser's theorem over `[0, 1] ⊆ P`, with the restriction of `ι_{∂_t} τ` as the
  -- primitive of the velocity.
  obtain ⟨ψ, hψ, hψ₀, hψρ⟩ := exists_isotopy_mpullback_eq_of_uIcc_subset τ'
    (SmoothForm.mpullback (Prod.map Subtype.val id) (contMDiff_subtypeVal.prodMap contMDiff_id)
      τ.timeInterior) hτ'symp hIP fun t _ ↦ by
    rw [mpullback_prodMk_mlieDerivForm_mpullback_prodMap_subtypeVal, hres]
    exact SmoothForm.mpullback_prodMk_mlieDerivForm_eq_mextDeriv_timeInterior hτc t
  refine ⟨Diffeotopy.ofReal ψ hψ hψ₀, fun t ↦ ?_⟩
  have h₀ := hτI 0
  rw [Icc.coe_zero] at h₀
  have h := hψρ t (by rw [uIcc_of_le zero_le_one]; exact t.property)
  rw [hres, hres] at h
  simpa [hτI t, h₀] using h

end TauCeti.SmoothTwoForm

namespace TauCeti.SmoothTwoForm

open SymplecticGeometry

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

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
  have hc' : ContDiff ℝ ∞ (deriv Real.smoothTransition) :=
    (contDiff_infty_iff_deriv.1 Real.smoothTransition.contDiff).2
  -- The path `σ_t = σ₀ + c(t) (σ₁ - σ₀)` on `ℝ × M`, `c = Real.smoothTransition`, and the
  -- one-form `α` with slices `c'(t) β`.
  set σ := SmoothForm.lineMapFamily σ₀ σ₁ Real.smoothTransition.contDiff
  set α := SmoothForm.lineMapFamily (0 : SmoothForm I M ℝ 1) β hc'
  have hαt (t : ℝ) : SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α =
      deriv Real.smoothTransition t • β := by
    rw [SmoothForm.mpullback_prodMk_lineMapFamily, zero_add, sub_zero]
  -- Since `c(t) ∈ [0, 1]`, every slice `σ_t` is symplectic.
  have hσt (t : ℝ) : IsSymplectic
      (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) σ) := by
    rw [SmoothForm.mpullback_prodMk_lineMapFamily]
    exact hσ _ ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  have hαK (t : ℝ) (x : M) (hx : x ∉ K) :
      (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).val x = 0 := by
    rw [hαt, SmoothBundleForm.smul_apply, hβK x hx, smul_zero]
  obtain ⟨ψ, hψ, hψ₀, hψK, hψσ⟩ :=
    exists_isotopy_mpullback_eq_of_isCompact σ α hσt
      (SmoothForm.mpullback_prodMk_mlieDerivForm_lineMapFamily_eq_mextDeriv hβ _) hK hαK
  refine ⟨Diffeotopy.ofReal ψ hψ hψ₀, fun t x hx ↦ ?_, ?_⟩
  · rw [Diffeotopy.ofReal_apply]
    exact hψK t x fun u ↦ hαK u x hx
  · have h := hψσ 1
    simp only [σ, SmoothForm.mpullback_prodMk_lineMapFamily, Real.smoothTransition.one,
      Real.smoothTransition.zero, one_smul, zero_smul, add_zero, add_sub_cancel] at h
    rw [Diffeotopy.final_ofReal]
    exact h

omit [I.Boundaryless] [T2Space M] in
/-- If the slices `ρ_t` of a two-form `ρ` on `ℝ × M` have invertible flat maps at every point for
the times `t ∈ [0, 1]`, and at the points outside a compact set `K` for all times, then they have
invertible flat maps at every point for the times of some `(-δ, 1 + δ)`. -/
private theorem exists_pos_forall_isInvertible_flat_mpullback_prodMk
    (ρ : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) ℝ 2) {K : Set M} (hK : IsCompact K)
    (hI : ∀ (t : unitInterval) x, (flat (SmoothForm.mpullback (Prod.mk (t : ℝ))
      (contMDiff_const.prodMk contMDiff_id) ρ) x).IsInvertible)
    (hKc : ∀ s, ∀ x ∉ K, (flat (SmoothForm.mpullback (Prod.mk s)
      (contMDiff_const.prodMk contMDiff_id) ρ) x).IsInvertible) :
    ∃ δ > 0, ∀ s ∈ Ioo (0 - δ) (1 + δ), ∀ x, (flat (SmoothForm.mpullback (Prod.mk s)
      (contMDiff_const.prodMk contMDiff_id) ρ) x).IsInvertible := by
  set W := {p : ℝ × M | (flat (SmoothForm.mpullback (Prod.mk p.1)
    (contMDiff_const.prodMk contMDiff_id) ρ) p.2).IsInvertible}
  have hW : IsOpen W := isOpen_setOfPred_isInvertible_flat_mpullback_prodMk ρ
  -- the tube lemma for the compact set `K`, near each time of `[0, 1]`
  have hnhds (t : unitInterval) : ∀ᶠ s in 𝓝 (t : ℝ), ∀ x, (s, x) ∈ W := by
    refine (hK.eventually_forall_of_forall_eventually (P := fun s x ↦ (s, x) ∈ W) fun x _ ↦
      hW.mem_nhds (hI t x)).mono fun s hs x ↦ ?_
    by_cases hx : x ∈ K
    · exact hs x hx
    · exact hKc s x hx
  obtain ⟨δ₀, hδ₀, h₀⟩ := Metric.eventually_nhds_iff_ball.mp (hnhds 0)
  obtain ⟨δ₁, hδ₁, h₁⟩ := Metric.eventually_nhds_iff_ball.mp (hnhds 1)
  refine ⟨min δ₀ δ₁, lt_min hδ₀ hδ₁, fun s hs x ↦ ?_⟩
  rcases lt_or_ge s 0 with h | h
  · refine h₀ s ?_ x
    rw [Metric.mem_ball, Real.dist_eq, Icc.coe_zero, sub_zero, abs_of_neg h]
    linarith [hs.1, min_le_left δ₀ δ₁]
  rcases le_or_gt s 1 with h' | h'
  · exact hI ⟨s, h, h'⟩ x
  · refine h₁ s ?_ x
    rw [Metric.mem_ball, Real.dist_eq, Icc.coe_one, abs_of_pos (by linarith)]
    linarith [hs.2, min_le_right δ₀ δ₁]

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
  obtain ⟨δ, hδ, hgood⟩ := exists_pos_forall_isInvertible_flat_mpullback_prodMk ρ hK
    (fun t x ↦ by
      rw [hρI t]
      exact isNondegenerate_iff_isInvertible_flat.mp (hτ t).isNondegenerate x)
    (fun s x hx ↦ by
      rw [flat_def, hρK s x hx, ← flat_def]
      exact isNondegenerate_iff_isInvertible_flat.mp (hτ 0).isNondegenerate x)
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

end TauCeti.SmoothTwoForm

end
