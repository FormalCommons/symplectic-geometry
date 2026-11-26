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
import SymplecticGeometry.Geometry.Diffeomorphism.Diffeotopy.Real
import SymplecticGeometry.Geometry.Manifold.DeRham.SmoothFamily.GoodCover
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Flow.Family
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.TimeExtension
import SymplecticGeometry.Geometry.Symplectic.Manifold.Family
import TauCeti.Geometry.Symplectic.Manifold.Moser.Local

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

## Main results

* `TauCeti.SmoothForm.IsClosed.exists_isotopy_mpullback_eq`: a closed two-form on `ℝ × M` whose
  slices are symplectic, on a closed manifold, has an isotopy `ψ_t` with `ψ_t^* ρ_t = ρ_0`.
* `TauCeti.SmoothTwoForm.exists_diffeotopy_mpullback_eq`: Moser stability for a family of
  cohomologous symplectic forms over `[0, 1]` on a closed manifold.

## References

* J. Moser, *On the volume elements on a manifold*, Transactions of the American Mathematical
  Society 120 (1965), 286–294.
* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §3.2,
  Theorem 3.2.4.
-/

public section

noncomputable section

open Set
open scoped Manifold ContDiff

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
    SmoothForm.mpullback_prodMk_mpullback_prodMap_id_right contMDiff_subtypeVal β t
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

end
