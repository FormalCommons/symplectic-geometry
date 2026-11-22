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
import SymplecticGeometry.Analysis.SpecialFunctions.SmoothTransition
import SymplecticGeometry.Geometry.Diffeomorphism.Diffeotopy.Real
import SymplecticGeometry.Geometry.Manifold.DeRham.SmoothFamily.GoodCover
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Flow.Family
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.TimeExtension
import SymplecticGeometry.Geometry.Symplectic.Manifold.Family
import TauCeti.Geometry.Symplectic.Manifold.Moser

/-!
# Moser stability

Let `M` be a closed manifold and `σ` a smooth two-form on `[0, 1] × M` whose slices
`σ_t = ι_t^* σ` are symplectic and all lie in the de Rham class of `σ_0`. Moser's stability
theorem gives a diffeotopy `ψ_t` of `M` with `ψ_t^* σ_t = σ_0` for every `t`
(`TauCeti.SmoothTwoForm.exists_diffeotopy_mpullback_eq`).

The proof reduces to Tau Ceti's Moser theorem over `ℝ`,
`TauCeti.SmoothTwoForm.exists_isotopy_mpullback_eq`, which takes a family over `ℝ` with symplectic
slices and a smooth family of primitives of its velocity.

1. The differences `σ_t - σ_0` are a smooth family of exact forms, so they have a smooth family
   of primitives `β_t` (`SymplecticGeometry.exists_isSmoothFamily_mextDerivₗ_eq`, since a compact
   manifold has a finite good cover).
2. Seeley's time extension (`TauCeti.SmoothForm.timeExtend`) extends `β` to a one-form `B` on
   `ℝ × M`. The closed form `τ = pr_M^* σ_0 + dB` on `ℝ × M` has the slices
   `τ_s = σ_0 + d B_s`, equal to `σ_s` for `s ∈ [0, 1]`.
3. Nondegeneracy is open and `M` is compact, so the parameters `s` at which `τ_s` is
   nondegenerate form an open set containing `[0, 1]`
   (`TauCeti.SmoothTwoForm.isOpen_setOf_forall_isInvertible_flat_mpullback_prodMk`). It contains
   an interval `(-ε, 1 + ε)`, and a smooth `c : ℝ → ℝ` that is the identity on `[0, 1]` with
   values in that interval (`SymplecticGeometry.exists_contDiff_eqOn_id_Icc_mem_Ioo`, through
   `SymplecticGeometry.exists_contDiff_eqOn_id_Icc_mem_of_isOpen`) gives the closed form
   `(c × id)^* τ`, all of whose slices are symplectic.
4. The time derivative of a closed form on `ℝ × M` is exact
   (`TauCeti.SmoothForm.mextDerivₗ_timeInterior`: `∂_t ρ = d (ι_{∂_t} ρ)`), which is the
   hypothesis on the velocity in Tau Ceti's theorem. So a closed form on `ℝ × M` with symplectic
   slices has a Moser isotopy (`TauCeti.SmoothForm.IsClosed.exists_isotopy_mpullback_eq`), and the
   isotopy over `ℝ` of `(c × id)^* τ` restricts to a diffeotopy (`TauCeti.Diffeotopy.ofReal`).

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
  have hα := (SmoothForm.mextDerivₗ_timeInterior hρc).symm
  have hvel (t : ℝ) : TauCeti.mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t)
        (mlieDerivForm (fun _ ↦ ((1 : ℝ), (0 : E))) ρ.val) =
      mextDeriv (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id)
        ρ.timeInterior).val := by
    have h := congrArg Subtype.val
      (congrArg (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id)) hα)
    simpa [← SmoothForm.mextDerivₗ_mpullback] using h
  obtain ⟨ψ, hψ, hψ₀, -, hψρ⟩ :=
    TauCeti.SmoothTwoForm.exists_isotopy_mpullback_eq ρ ρ.timeInterior hρ hvel
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
  -- Step 3: the slices of `τ` are nondegenerate for parameters in an open set `P ⊇ [0, 1]`, and
  -- `(c × id)^* τ`, for `c` the identity on `[0, 1]` with values in `P`, has symplectic slices.
  set P : Set ℝ := {s | ∀ x : M, (flat (SmoothForm.mpullback (Prod.mk s)
    (contMDiff_const.prodMk contMDiff_id) τ) x).IsInvertible}
  have hIP : Icc (0 : ℝ) 1 ⊆ P := fun s hs x ↦ by
    have h := hτI ⟨s, hs⟩
    rw [Subtype.coe_mk] at h
    rw [h]
    exact isNondegenerate_iff_isInvertible_flat.mp (hσ _).isNondegenerate x
  obtain ⟨c, hc, hcI, hcP⟩ := exists_contDiff_eqOn_id_Icc_mem_of_isOpen zero_le_one
    (isOpen_setOf_forall_isInvertible_flat_mpullback_prodMk τ) hIP
  have hcs : ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) ∞ (Prod.map c (id : M → M)) :=
    hc.contMDiff.prodMap contMDiff_id
  set ρ := SmoothForm.mpullback (Prod.map c id) hcs τ
  have hρs (t : ℝ) : SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) ρ =
      SmoothForm.mpullback (Prod.mk (c t)) (contMDiff_const.prodMk contMDiff_id) τ :=
    SmoothForm.mpullback_prodMk_mpullback_prodMap_id_right hc.contMDiff τ t
  have hρsymp (t : ℝ) : IsSymplectic
      (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) ρ) := by
    rw [hρs]
    exact ⟨hτc.mpullback _ _, isNondegenerate_iff_isInvertible_flat.mpr (hcP t)⟩
  -- Step 4: Moser's theorem over `ℝ` for the closed form `ρ`, restricted to `[0, 1]`.
  obtain ⟨ψ, hψ, hψ₀, hψρ⟩ := (hτc.mpullback _ hcs).exists_isotopy_mpullback_eq hρsymp
  refine ⟨Diffeotopy.ofReal ψ hψ hψ₀, fun t ↦ ?_⟩
  have h₀ := hτI 0
  rw [Icc.coe_zero] at h₀
  have h := hψρ t
  rw [hρs, hρs] at h
  simpa [hcI t.property, hcI ⟨le_rfl, zero_le_one⟩, hτI t, h₀] using h

end TauCeti.SmoothTwoForm

end
