/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Flow.Family
import TauCeti.Analysis.ODE.ScalarLinear

/-!
# Moser's principle along trajectories of local time-dependent flows

Let `X` be a jointly `C²` time-dependent vector field on a finite-dimensional manifold `M`
without boundary, with time-dependent flow `φ_{s,t}` (`TauCeti.timeDependentFlowOf`), and let `α`
be a form on `ℝ × M` with slices `α_u = ι_u^* α`. Tau Ceti proves that if the rate
`ι_u^* L_{∂_t} α + L_{X_u} α_u` equals `g_u • α_u` everywhere, then
`(φ_{s,t}^* α_t)ₓ = exp (∫ₛᵗ g (u, φ_{s,u} x) du) • (α_s)ₓ`
(`TauCeti.mpullback_timeDependentFlowOf_mpullback_prodMk_apply_eq_exp_integral_smul_of_mem`),
and that if the rate vanishes only at the points `φ_{s,u} x` for `u` between `s` and `t`, then
`(φ_{s,t}^* α_t)ₓ = (α_s)ₓ`
(`TauCeti.mpullback_timeDependentFlowOf_mpullback_prodMk_apply_eq_of_forall_mem_uIcc_of_mem`).

This file combines the two: the rescaling identity
`(φ_{s,t}^* α_t)ₓ = exp (∫ₛᵗ c u du) • (α_s)ₓ` holds as soon as the rate at `φ_{s,u} x` is
`c u • α_u` at that point, for every `u` between `s` and `t`, with a coefficient `c` continuous in
time, and `α` is `C¹` only along the trajectory. This is the form in which Gray's argument uses
the identity when the contact structures are given only by local defining forms.

The proof is that of Tau Ceti's
`TauCeti.mpullback_timeDependentFlowOf_mpullback_prodMk_apply_eq_exp_integral_smul_of_mem`, with
the derivative read only along the trajectory through
`TauCeti.hasDerivAt_mpullback_timeDependentFlowOf_mpullback_prodMk` and the interval between `s`
and `t` in place of the whole domain of the flow, as in Tau Ceti's
`TauCeti.mpullback_timeDependentFlowOf_mpullback_prodMk_apply_eq_of_forall_mem_uIcc_of_mem`.

The file also applies Tau Ceti's
`TauCeti.mpullback_timeDependentFlowOf_mpullback_prodMk_apply_eq_of_mem` to the constant family
`(u, y) ↦ β_y` of a closed form `β` whose contractions `ι_{X_u} β` are all closed: the local
time-dependent flow preserves `β` wherever it is defined, with no completeness. This is the
local form of Tau Ceti's `TauCeti.mpullback_timeDependentFlowOf_of_mextDeriv_interior_eq_zero`,
and gives the preservation of a symplectic form by local time-dependent Hamiltonian flows.

## Main results

* `TauCeti.mpullback_timeDependentFlowOf_mpullback_prodMk_…_smul_of_forall_mem_uIcc_of_mem`
  (in full, `…_prodMk_apply_eq_exp_integral_smul_of_forall_mem_uIcc_of_mem`): if the rate is
  `c u • α_u` along the trajectory of `x` between `s` and `t`, then
  `(φ_{s,t}^* α_t)ₓ = exp (∫ₛᵗ c u du) • (α_s)ₓ`.
* `TauCeti.mpullback_timeDependentFlowOf_apply_of_mextDeriv_interior_eq_zero`: a closed smooth
  form whose contractions with every `X u` are closed satisfies `(φ_{s,t}^* β)ₓ = βₓ` wherever
  the flow is defined.

## References

* Hansjörg Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Theorem 2.2.2 (Gray stability, whose proof integrates this rescaling).
* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer, 2012, Chapter 22 (the
  derivative of pullbacks of a time-dependent family of forms along a time-dependent flow).
-/

public section

noncomputable section

open Set Bundle

open scoped ContDiff Manifold

namespace TauCeti

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M] [T2Space M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}
  {X : ℝ → (x : M) → TangentSpace I x} {α : RoughForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) F k}

/-- **Moser's principle along a trajectory**, rescaling case. Let `X` be a jointly `C²`
time-dependent vector field with time-dependent flow `φ`, defined at `x` from time `s` to time `t`,
and let `α` be a form on `ℝ × M` with slices `α_u = ι_u^* α`, which is `C¹` at `(u, φ_{s,u} x)`
for every time `u` between `s` and `t`. If, for each such `u`, the rate
`ι_u^* L_{∂_t} α + L_{X_u} α_u` at the point `φ_{s,u} x` is `c u • (α_u)_{φ_{s,u} x}`, for a
function `c` of time continuous between `s` and `t`, then
`(φ_{s,t}^* α_t)ₓ = exp (∫ₛᵗ c u du) • (α_s)ₓ`. Nothing is assumed away from the trajectory
of `x`. -/
theorem
mpullback_timeDependentFlowOf_mpullback_prodMk_apply_eq_exp_integral_smul_of_forall_mem_uIcc_of_mem
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 2
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
    {s t : ℝ} {x : M} (h : ((s, t), x) ∈ timeDependentFlowDomain X)
    (hα : ∀ u ∈ uIcc s t, ContMDiffAt (𝓘(ℝ, ℝ).prod I)
      ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, (ℝ × E) [⋀^Fin k]→L[ℝ] F)) 1
      (fun p ↦ TotalSpace.mk' ((ℝ × E) [⋀^Fin k]→L[ℝ] F) p (α p))
      (u, timeDependentFlowOf X s u x))
    {c : ℝ → ℝ} (hc : ContinuousOn c (uIcc s t))
    (hL : ∀ u ∈ uIcc s t, (mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk u)
          (mlieDerivForm (fun _ ↦ ((1 : ℝ), (0 : E))) α) +
        mlieDerivForm (X u) (mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk u) α))
          (timeDependentFlowOf X s u x) =
        c u • mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk u) α (timeDependentFlowOf X s u x)) :
    mpullback I I (timeDependentFlowOf X s t) (mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t) α) x =
      Real.exp (∫ u in s..t, c u) • mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk s) α x := by
  -- The flow from `(s, x)` is defined at all times between `s` and `t`.
  have hJ : uIcc s t ⊆ {u | ((s, u), x) ∈ timeDependentFlowDomain X} :=
    (ordConnected_setOf_mem_timeDependentFlowDomain s x).uIcc_subset
      (mem_timeDependentFlowDomain_self_of_mem h) h
  -- The pullbacks at `x`, as alternating maps on the model space.
  set P : ℝ → E [⋀^Fin k]→L[ℝ] F := fun u ↦
    mpullback I I (timeDependentFlowOf X s u) (mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk u) α) x
  -- Between `s` and `t` they satisfy the scalar linear equation `P' = c • P`.
  have hP (u : ℝ) (hu : u ∈ uIcc s t) : HasDerivWithinAt P (c u • P u) (uIcc s t) u := by
    refine ((hasDerivAt_mpullback_timeDependentFlowOf_mpullback_prodMk hX (hJ hu)
      (hα u hu)).congr_deriv ?_).hasDerivWithinAt
    rw [mpullback_apply_eq_compContinuousLinearMapCLM, hL u hu, _root_.map_smul,
      ← mpullback_apply_eq_compContinuousLinearMapCLM]
    -- The two sides differ only in the unfolding of `P` and in whether the scalar action is that
    -- of forms on the fibre `T_x M` or on the model space `E`.
    rfl
  have hP0 : P s = mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk s) α x := by
    have hid : timeDependentFlowOf X s s = id := funext (timeDependentFlowOf_self X s)
    exact (congrArg (fun f ↦ mpullback I I f (mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk s) α) x)
      hid).trans (congrFun (mpullback_id _) x)
  rw [← hP0]
  exact eq_exp_integral_smul_of_hasDerivWithinAt_smul (V := E [⋀^Fin k]→L[ℝ] F) ordConnected_uIcc
    hc hP left_mem_uIcc right_mem_uIcc

/-- **Local time-dependent flows preserve closed forms with closed contractions.** Let `X` be a
jointly `C²` time-dependent vector field and `β` a closed smooth form whose contraction
`ι_{X_t} β` is closed for every time `t`. Wherever the time-dependent flow `φ` of `X` from
`(s, x)` is defined up to time `t`, it satisfies `(φ_{s,t}^* β)ₓ = βₓ`. The suspension of `X`
need not be complete. -/
theorem mpullback_timeDependentFlowOf_apply_of_mextDeriv_interior_eq_zero
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 2
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
    {β : SmoothForm I M F (k + 1)} (hβ : β.IsClosed)
    (hXβ : ∀ t, mextDeriv (RoughForm.interior (X t) β.val) = 0)
    {s t : ℝ} {x : M} (h : ((s, t), x) ∈ timeDependentFlowDomain X) :
    mpullback I I (timeDependentFlowOf X s t) β.val x = β.val x := by
  -- The constant family `p ↦ β (p.2)` on `ℝ × M`, whose slices are all `β`.
  set α := SmoothForm.mpullback (Prod.snd : ℝ × M → M)
    (contMDiff_snd : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (Prod.snd : ℝ × M → M)) β
  have hslice (u : ℝ) : mpullback (F := F) (k := k + 1) I (𝓘(ℝ, ℝ).prod I)
      (Prod.mk u : M → ℝ × M) α.val = β.val := by
    have hc : (Prod.snd : ℝ × M → M) ∘ Prod.mk u = id := rfl
    rw [← SmoothForm.coe_mpullback (Prod.mk u) (contMDiff_const.prodMk contMDiff_id),
      ← LinearMap.comp_apply, ← SmoothForm.mpullback_comp]
    simp only [hc, SmoothForm.mpullback_id, LinearMap.id_apply]
  have hL (u : ℝ) : mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk u)
        (mlieDerivForm (fun _ ↦ ((1 : ℝ), (0 : E))) α.val) +
      mlieDerivForm (X u) (mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk u : M → ℝ × M) α.val) = 0 := by
    funext y
    -- The slices of the constant family do not move, so their time derivative vanishes.
    have hd := hasDerivAt_mpullback_prodMk u y (α.mdifferentiable (u, y))
    simp only [hslice] at hd
    have hXu : MDifferentiable I I.tangent (fun y ↦ (⟨y, X u y⟩ : TangentBundle I M)) :=
      (hX.comp ((contMDiff_const (c := u)).prodMk contMDiff_id)).mdifferentiable two_ne_zero
    rw [Pi.add_apply, hd.unique (hasDerivAt_const u _), hslice,
      mlieDerivForm_eq_mextDeriv_interior β.mdifferentiable hXu
        ((SmoothForm.isClosed_def β).1 hβ), hXβ u, Pi.zero_apply]
    exact add_zero _
  simpa only [hslice] using
    mpullback_timeDependentFlowOf_mpullback_prodMk_apply_eq_of_mem hX
      (α.contMDiff.of_le (by simp)) hL h

end TauCeti

end
