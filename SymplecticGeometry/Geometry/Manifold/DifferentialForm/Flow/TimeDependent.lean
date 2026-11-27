/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Flow.TimeDependent

/-!
# Lie derivatives from pull-backs along time-dependent flows that stay constant

Let `X` be a jointly `C¹` time-dependent vector field on a finite-dimensional manifold `M`
without boundary, `φ_{t,u}` its flow from time `t` to time `u` (`TauCeti.timeDependentFlowOf`),
`α` a form on `M` and `ι : N → M` a map. If the pull-backs `((φ_{t,u} ∘ ι)^* α)ₓ` do not depend
on `u` near `u = t`, then `(ι^* L_{X_t} α)ₓ = 0`
(`TauCeti.mpullback_mlieDerivForm_apply_eq_zero_of_eventuallyEq_const`). The velocity of these
pull-backs at `u = t` is `(ι^* L_{X_t} α)ₓ`, by Tau Ceti's
`TauCeti.hasDerivAt_mpullback_timeDependentFlowOf_self` composed with `ι` through
`TauCeti.hasDerivAt_mpullback_of_eq_comp`, and a curve that is constant near `t` has velocity
zero there.

No completeness of the suspension is needed: the flow is `C¹` on its open domain, which contains
`((t, t), ι x)`.
-/

public section

open Filter Bundle
open scoped Manifold Topology

namespace TauCeti

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I 2 M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}
  {X : ℝ → (x : M) → TangentSpace I x} {α : RoughForm I M F k}

/-- **Constant pull-backs along a flow have vanishing Lie derivative.** Let `X` be a jointly `C¹`
time-dependent vector field, `α` a form differentiable at `ι x`, and `ι : N → M` differentiable
at `x`. If the pull-backs of `α` at `x` along the flow of `X` from `t` to `u`, composed with `ι`,
are eventually constant for `u` near `t`, then the Lie derivative of `α` along `X t` pulls back
along `ι` to zero at `x`. -/
theorem mpullback_mlieDerivForm_apply_eq_zero_of_eventuallyEq_const
    {EN HN N : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
    {IN : ModelWithCorners ℝ EN HN} [TopologicalSpace N] [ChartedSpace HN N]
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 1
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
    {ι : N → M} {x : N} (hι : MDifferentiableAt IN I ι x) (t : ℝ)
    (hα : MDifferentiableAt I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F))
      (fun z ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F) z (α z)) (ι x))
    {c : EN [⋀^Fin k]→L[ℝ] F}
    (hconst : (fun u ↦ mpullback IN I (timeDependentFlowOf X t u ∘ ι) α x) =ᶠ[𝓝 t]
      fun _ ↦ c) :
    mpullback IN I ι (mlieDerivForm (X t) α) x = 0 := by
  -- The flow from `t` is differentiable at `ι x` up to every time near `t`.
  have hφ : ∀ᶠ u in 𝓝 t, MDifferentiableAt I I (timeDependentFlowOf X t u) (ι x) := by
    have hmem := mem_timeDependentFlowDomain_self hX t (ι x)
    filter_upwards [(by fun_prop : Continuous fun u : ℝ ↦ ((t, u), ι x)).continuousAt
      |>.eventually_mem ((isOpen_timeDependentFlowDomain hX).mem_nhds hmem)] with u hu
    exact mdifferentiableAt_timeDependentFlowOf hX hu
  have hderiv := hasDerivAt_mpullback_of_eq_comp (χ := timeDependentFlowOf X t) (g := ι)
    (Eventually.of_forall fun _ ↦ EventuallyEq.rfl) hι hφ
    (hasDerivAt_mpullback_timeDependentFlowOf_self hX t (ι x) hα)
  exact hderiv.unique ((hasDerivAt_const _ _).congr_of_eventuallyEq hconst)

end TauCeti

end
