/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
import TauCeti.Geometry.Manifold.Diffeomorph.Family
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
public import TauCeti.Geometry.Manifold.DifferentialForm.Closed
public import TauCeti.Geometry.Manifold.DifferentialForm.ExtDeriv
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import TauCeti.Geometry.Manifold.TwoForm.Basic
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import SymplecticGeometry.Geometry.Symplectic.Moser.Field
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Smooth
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.SmoothFamily.Basic
import SymplecticGeometry.Geometry.Manifold.Flow.TimeDependent

/-!
# Moser stability on a closed manifold with a parameter in a manifold

Let `N` be a closed manifold, `P` a manifold, `ω₀` a closed two-form on `N`, and `σ`, `β` forms
on `P × N` with slices `σ_p` and `β_p` such that `dβ_p = σ_p - ω₀` and every form
`ω₀ + s (σ_p - ω₀)`, `s ∈ [0, 1]`, is nondegenerate. Moser's argument for each segment gives a
diffeomorphism `χ_p` of `N` with `χ_p^* σ_p = ω₀`, and the `χ_p` depend smoothly on `p`, so that
`(p, x) ↦ (p, χ_p x)` is a diffeomorphism of `P × N`.

The segments are run with the smooth step `Real.smoothTransition` as clock: the forms
`Ω_{p,s} = ω₀ + c(s) (σ_p - ω₀)`, `c = Real.smoothTransition`, are nondegenerate for every real
`s`, since `c(s) ∈ [0, 1]`, and `∂_s Ω_{p,s} = d(c'(s) β_p)`. So the Moser fields `X_{p,s}` of
these families need no cutoff. They are those of one family of two-forms over the points `(p, s)`
of `P × ℝ` (`SymplecticGeometry.moserField`), hence jointly smooth in `(p, s, x)`. Their flows
are complete because `N` is compact, and `χ_p` is the time-one map, jointly smooth in `(p, x)`
by `TauCeti.contMDiff_timeDependentFlowDiffeomorph_param`; `Diffeomorph.prodCongrRight` turns
the family `χ` into a diffeomorphism of `P × N`. Moser's equation along the trajectories is
`TauCeti.SmoothTwoForm.mpullback_timeDependentFlowOf_moserField_lineMapFamily_apply_of_contDiff`
(`Moser/Field.lean`).

For each `p`, the construction follows Tau Ceti's
`TauCeti.SmoothTwoForm.exists_diffeomorph_fix_eventually_mpullback_eq_of_cutoff`
(`TauCeti/Geometry/Symplectic/Manifold/RelativeMoser.lean`): the `Real.smoothTransition` clock,
the time-one map of the flow, and the points where the primitive vanishes fixed through
`TauCeti.timeDependentFlowOf_eq_self_of_forall_eq_zero`. Here it is run with a parameter in `P`,
and with no cutoff, since `N` is compact. The argument also adapts that of
`TauCeti.SmoothTwoForm.exists_diffeotopy_fix_eventually_mpullback_eq_of_mextDeriv_eq_sub`
(`Moser/Family.lean`), with a parameter in a manifold instead of `[0, 1]` and no cutoff in space,
and that of `TauCeti.SmoothForm.IsClosed.exists_isotopy_mpullback_eq` (`Moser/Stability.lean`),
on a closed manifold.

## Main results

* `TauCeti.SmoothTwoForm.exists_diffeomorph_prod_mpullback_eq_of_mextDeriv_eq_sub`: Moser
  stability on a closed manifold, with a parameter in a manifold.

## References

* J. Moser, *On the volume elements on a manifold*, Transactions of the American Mathematical
  Society 120 (1965), 286–294.
* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §3.2
  (Moser's argument).
-/

public section

open Set TauCeti
open scoped Manifold ContDiff

namespace TauCeti.SmoothTwoForm

open SymplecticGeometry

variable {E H N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T2Space N]

variable {EP HP P : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP] [CompleteSpace EP]
  [TopologicalSpace HP] {IP : ModelWithCorners ℝ EP HP} [TopologicalSpace P] [ChartedSpace HP P]
  [IsManifold IP ∞ P] [T2Space P] [BoundarylessManifold IP P] [CompactSpace N]

/-- **Moser stability with a parameter in a manifold.** Let `N` be a closed manifold, `P` a
Hausdorff boundaryless manifold modelled on a complete space, `ω₀` a closed two-form on `N`, and
`σ` a two-form and `β` a one-form on `P × N`, with slices `σ_p` and `β_p`, such that
`dβ_p = σ_p - ω₀` for every `p` and every form `ω₀ + s (σ_p - ω₀)`, `s ∈ [0, 1]`, is
nondegenerate. Then there is a diffeomorphism `Φ` of `P × N` of the form
`(p, x) ↦ (p, χ_p x)`, for diffeomorphisms `χ_p` of `N`, with `χ_p^* σ_p = ω₀` for every `p`, and
`χ_p x = x` at every point `x` where `β_p` vanishes. -/
theorem exists_diffeomorph_prod_mpullback_eq_of_mextDeriv_eq_sub
    {ω₀ : SmoothTwoForm I N} (hω₀ : ω₀.IsClosed)
    (σ : SmoothForm (IP.prod I) (P × N) ℝ 2) (β : SmoothForm (IP.prod I) (P × N) ℝ 1)
    (hβ : ∀ p, mextDeriv
      (SmoothForm.mpullback (Prod.mk p) (contMDiff_const.prodMk contMDiff_id) β).val =
        (SmoothForm.mpullback (Prod.mk p) (contMDiff_const.prodMk contMDiff_id) σ - ω₀).val)
    (hnd : ∀ p, ∀ x, ∀ s ∈ Icc (0 : ℝ) 1, ((ω₀ + s •
      (SmoothForm.mpullback (Prod.mk p) (contMDiff_const.prodMk contMDiff_id) σ - ω₀)).bilinFormAt
        x).Nondegenerate) :
    ∃ Φ : (P × N) ≃ₘ⟮IP.prod I, IP.prod I⟯ (P × N), ∃ χ : P → N ≃ₘ⟮I, I⟯ N,
      (∀ q, Φ q = (q.1, χ q.1 q.2)) ∧
      (∀ p, SmoothForm.mpullback (χ p) (χ p).contMDiff
          (SmoothForm.mpullback (Prod.mk p) (contMDiff_const.prodMk contMDiff_id) σ) = ω₀) ∧
      ∀ p x, (SmoothForm.mpullback (Prod.mk p) (contMDiff_const.prodMk contMDiff_id) β).val x =
        0 → χ p x = x := by
  set σ' : P → SmoothTwoForm I N := fun p ↦
    SmoothForm.mpullback (Prod.mk p) (contMDiff_const.prodMk contMDiff_id) σ
  set β' : P → SmoothForm I N ℝ 1 := fun p ↦
    SmoothForm.mpullback (Prod.mk p) (contMDiff_const.prodMk contMDiff_id) β
  -- The clock `c` of the segments.
  set c : ℝ → ℝ := Real.smoothTransition
  have hc : ContDiff ℝ ∞ c := Real.smoothTransition.contDiff
  -- The forms `ω₀ + c(s) (σ_p - ω₀)` and `c'(s) β_p`, as families over the points `(p, s)`.
  obtain ⟨Ω, hΩ⟩ := isSmoothFamily_def.mp <| show IsSmoothFamily (IP.prod 𝓘(ℝ, ℝ))
      (fun q : P × ℝ ↦ ω₀ + c q.2 • (σ' q.1 - ω₀)) from
    (isSmoothFamily_const ω₀).add ((((isSmoothFamily_mpullback_prodMk σ).comp Prod.fst
      contMDiff_fst).sub (isSmoothFamily_const ω₀)).fun_smul (hc.contMDiff.comp contMDiff_snd))
  obtain ⟨B, hB⟩ := isSmoothFamily_def.mp <| show IsSmoothFamily (IP.prod 𝓘(ℝ, ℝ))
      (fun q : P × ℝ ↦ deriv c q.2 • β' q.1) from
    ((isSmoothFamily_mpullback_prodMk β).comp Prod.fst contMDiff_fst).fun_smul
      ((contDiff_infty_iff_deriv.mp hc).2.contMDiff.comp contMDiff_snd)
  -- All of these forms are nondegenerate, since `c` takes values in `[0, 1]`.
  have hinv (q : P × ℝ) (x : N) :
      (SmoothTwoForm.flat (SmoothForm.mpullback (Prod.mk q) (contMDiff_const.prodMk contMDiff_id)
        Ω) x).IsInvertible := by
    rw [hΩ, SmoothTwoForm.isInvertible_flat_iff]
    exact hnd q.1 x _ ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  -- The Moser fields `Y p s`, jointly smooth in `(p, s, x)`, with no cutoff.
  set Y : P → ℝ → (x : N) → TangentSpace I x := fun p s ↦ moserField Ω B (fun _ ↦ 1) (p, s)
  have hY : ContMDiff ((IP.prod 𝓘(ℝ, ℝ)).prod I) I.tangent ∞
      (fun q : (P × ℝ) × N ↦ (⟨q.2, Y q.1.1 q.1.2 q.2⟩ : TangentBundle I N)) :=
    contMDiff_moserField Ω B contMDiff_const fun q _ ↦ hinv q.1 q.2
  have hYp (p : P) : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent ∞
      (fun q : ℝ × N ↦ (⟨q.2, Y p q.1 q.2⟩ : TangentBundle I N)) :=
    hY.comp ((contMDiff_const.prodMk contMDiff_fst).prodMk contMDiff_snd)
  have hcY (p : P) : IsCompleteVectorField (timeDependentSuspensionField (Y p)) :=
    isCompleteVectorField_timeDependentSuspensionField_of_compactSpace
      ((hYp p).of_le (m := 1) (by simp))
  -- `χ_p` is the time-one map of the flow of `Y p`.
  set χ : P → N ≃ₘ⟮I, I⟯ N := fun p ↦ timeDependentFlowDiffeomorph (hcY p) le_top (hYp p) 0 1
  have hχ (p : P) (x : N) : χ p x = timeDependentFlowOf (Y p) 0 1 x :=
    timeDependentFlowDiffeomorph_apply _ _ _ _ _ _
  let Φ : (P × N) ≃ₘ⟮IP.prod I, IP.prod I⟯ (P × N) :=
    Diffeomorph.prodCongrRight χ (contMDiff_timeDependentFlowDiffeomorph_param le_top hY hcY 0 1)
      (by simp)
  refine ⟨Φ, χ, fun q ↦ Diffeomorph.prodCongrRight_apply _ _ _ .., fun p ↦ ?_,
    fun p x hx ↦ ?_⟩
  · -- For this `p`, `Y p` is the Moser field of the family `ω₀ + c(s) (σ_p - ω₀)`, with the
    -- primitives `c'(s) β_p`.
    have hYp' : Y p = moserField (SmoothForm.lineMapFamily ω₀ (σ' p) hc)
        (SmoothForm.lineMapFamily 0 (β' p) (contDiff_infty_iff_deriv.mp hc).2) fun _ ↦ 1 := by
      funext s y
      rw [moserField_def, SmoothForm.mpullback_prodMk_lineMapFamily, ← hΩ (p, s),
        SmoothForm.mpullback_prodMk_lineMapFamily, sub_zero, zero_add, ← hB (p, s)]
      exact moserField_def Ω B _ _ y
    have hX := hYp p
    have hcp := hcY p
    rw [hYp'] at hX hcp
    refine Subtype.ext (funext fun x ↦ ?_)
    rw [SmoothForm.coe_mpullback, funext (hχ p), hYp']
    refine mpullback_timeDependentFlowOf_moserField_lineMapFamily_apply_of_contDiff hω₀
      (Subtype.ext (by rw [mextDerivₗ_apply, hβ p])) hc Real.smoothTransition.zero
      Real.smoothTransition.one (hX.of_le (by simp)) hcp fun s _ ↦
        Filter.Eventually.of_forall fun z ↦ ⟨rfl, ?_⟩
    have h := hinv (p, s) z
    rwa [hΩ] at h
  · rw [hχ]
    exact timeDependentFlowOf_eq_self_of_forall_eq_zero ((hYp p).of_le (by simp))
      (fun s ↦ moserField_eq_zero_of_apply_eq_zero (by rw [hB, SmoothBundleForm.smul_apply, hx,
        smul_zero])) 0 1

end TauCeti.SmoothTwoForm

end
