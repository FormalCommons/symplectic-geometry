/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Flow.Family
import TauCeti.Analysis.ODE.ScalarLinear

/-!
# Rescaling of a family of forms along one trajectory of a time-dependent flow

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

The file also records how slices behave under pullback along `id × f : ℝ × M → ℝ × N`, for a
smooth `f : M → N`. The slice of `(id × f)^* α` at time `t` is `f^* α_t`, and the slice at time
`t` of its time derivative (`TauCeti.SmoothForm.timeDeriv`) is the pullback along `f` of the
slice of `∂_t α`: both are the velocity of `u ↦ f^* α_u`, by Tau Ceti's
`TauCeti.SmoothForm.hasDerivAt_mpullback_prodMk_timeDeriv`.

## Main results

* `TauCeti.mpullback_timeDependentFlowOf_mpullback_prodMk_…_smul_of_forall_mem_uIcc_of_mem`
  (in full, `…_prodMk_apply_eq_exp_integral_smul_of_forall_mem_uIcc_of_mem`): if the rate is
  `c u • α_u` along the trajectory of `x` between `s` and `t`, then
  `(φ_{s,t}^* α_t)ₓ = exp (∫ₛᵗ c u du) • (α_s)ₓ`.
* `TauCeti.SmoothForm.mpullback_prodMk_mpullback_prodMap`: `ι_t^* (id × f)^* α = f^* ι_t^* α`.
* `TauCeti.SmoothForm.mpullback_prodMk_timeDeriv_mpullback_prodMap`: the same for the time
  derivative, `ι_t^* ∂_t ((id × f)^* α) = f^* ι_t^* ∂_t α`.

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
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I 2 M]
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

end TauCeti

/-! ### Slices of pullbacks along `id × f` -/

namespace TauCeti.SmoothForm

variable {E H M E' H' N F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

/-- The slice at time `t` of the pullback of a form `α` on `ℝ × N` along `id × f` is the pullback
along `f` of the slice of `α` at time `t`: `ι_t^* (id × f)^* α = f^* ι_t^* α`. -/
theorem mpullback_prodMk_mpullback_prodMap (f : M → N) (hf : ContMDiff I J ∞ f)
    (α : SmoothForm (𝓘(ℝ, ℝ).prod J) (ℝ × N) F k) (t : ℝ) :
    mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id)
        (mpullback (Prod.map id f) (contMDiff_id.prodMap hf) α) =
      mpullback f hf (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α) := by
  rw [← LinearMap.comp_apply, ← mpullback_comp, ← LinearMap.comp_apply, ← mpullback_comp]
  have h : Prod.map id f ∘ Prod.mk t = Prod.mk t ∘ f := by
    ext x <;> simp
  simp only [h]

variable [I.Boundaryless] [J.Boundaryless]

/-- The time derivative commutes with pullback along `id × f`, slice by slice: the slice at time
`t` of `∂_t ((id × f)^* α)` is the pullback along `f` of the slice of `∂_t α` at time `t`. -/
theorem mpullback_prodMk_timeDeriv_mpullback_prodMap (f : M → N) (hf : ContMDiff I J ∞ f)
    (α : SmoothForm (𝓘(ℝ, ℝ).prod J) (ℝ × N) F k) (t : ℝ) :
    mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id)
        (mpullback (Prod.map id f) (contMDiff_id.prodMap hf) α).timeDeriv =
      mpullback f hf
        (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α.timeDeriv) := by
  apply Subtype.ext
  funext x
  -- Both sides at `x` are the velocity at `t` of `u ↦ (f^* α_u)ₓ`.
  have h₁ := hasDerivAt_mpullback_prodMk_timeDeriv
    (mpullback (Prod.map id f) (contMDiff_id.prodMap hf) α) t x
  -- The values of the slices at `f x` are read in the model fibre `E' [⋀^Fin k]→L[ℝ] F`.
  have h₃ : HasDerivAt
      (fun u ↦ @id (E' [⋀^Fin k]→L[ℝ] F)
        ((mpullback (Prod.mk u) (contMDiff_const.prodMk contMDiff_id) α).val (f x)))
      (@id (E' [⋀^Fin k]→L[ℝ] F)
        ((mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α.timeDeriv).val (f x))) t :=
    α.hasDerivAt_mpullback_prodMk_timeDeriv t (f x)
  have h₂ := ((ContinuousAlternatingMap.compContinuousLinearMapCLM
    (mfderiv I J f x : E →L[ℝ] E') :
      (E' [⋀^Fin k]→L[ℝ] F) →L[ℝ] E [⋀^Fin k]→L[ℝ] F)).hasFDerivAt.comp_hasDerivAt t h₃
  have hx (γ : SmoothForm J N F k) : (mpullback f hf γ).val x =
      ContinuousAlternatingMap.compContinuousLinearMapCLM (ι := Fin k) (F := F)
        (mfderiv I J f x : E →L[ℝ] E') (γ.val (f x)) := by
    rw [coe_mpullback, TauCeti.mpullback_apply_eq_compContinuousLinearMapCLM]
  have hs (u : ℝ) := congrArg (fun γ ↦ γ.val x) (mpullback_prodMk_mpullback_prodMap f hf α u)
  simp only [hs, hx] at h₁ ⊢
  exact h₁.unique h₂

end TauCeti.SmoothForm

end
