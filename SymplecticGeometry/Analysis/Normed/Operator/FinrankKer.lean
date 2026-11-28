/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Order.Filter.Basic
public import Mathlib.Topology.ContinuousOn
import Mathlib.Analysis.Normed.Module.FiniteDimension
import TauCeti.Analysis.Fredholm.SemiFredholm

/-!
# Upper semicontinuity of the dimension of the kernel

For a family `L x` of linear maps from a finite-dimensional space `F` to a Banach space `E`, each
of whose values `L x p` depends continuously on `x` at `x₀`, the kernel of `L x` has dimension at
most that of `L x₀` for every `x` near `x₀` (`LinearMap.eventually_finrank_ker_le`).

`F` carries no topology: a basis identifies it with `𝕜ⁿ`, on which the family becomes a family
of continuous linear maps that is continuous at `x₀`, and the bound is then Tau Ceti's
`ContinuousLinearMap.eventually_nhds_finiteDimensional_ker_and_finrank_ker_le`, since an operator
on a finite-dimensional space has closed range.

## References

* T. Kato, *Perturbation Theory for Linear Operators*, second edition, Chapter IV, §5.1.
-/

public section

open Filter Module Topology

namespace LinearMap

/-- **The dimension of the kernel is upper semicontinuous.** Let `L x` be linear maps from a
finite-dimensional space `F` to a Banach space `E` with `x ↦ L x p` continuous at `x₀` for each
`p`. Then for `x` near `x₀`, the kernel of `L x` has dimension at most that of `L x₀`. -/
theorem eventually_finrank_ker_le {𝕜 X F E : Type*} [RCLike 𝕜] [TopologicalSpace X]
    [AddCommGroup F] [Module 𝕜 F] [FiniteDimensional 𝕜 F]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    {L : X → F →ₗ[𝕜] E} {x₀ : X} (hL : ∀ p, ContinuousAt (fun x ↦ L x p) x₀) :
    ∀ᶠ x in 𝓝 x₀, finrank 𝕜 (ker (L x)) ≤ finrank 𝕜 (ker (L x₀)) := by
  -- The same maps on `𝕜ⁿ ≃ F`, as continuous linear maps.
  let ψ := (Module.finBasis 𝕜 F).equivFun.symm
  let L' (x : X) : (Fin (finrank 𝕜 F) → 𝕜) →L[𝕜] E := toContinuousLinearMap (L x ∘ₗ ψ.toLinearMap)
  have hfr (x : X) : finrank 𝕜 (L' x).ker = finrank 𝕜 (ker (L x)) := by
    have h : (L' x).ker = (ker (L x)).comap ψ.toLinearMap := by
      simp only [L', coe_toContinuousLinearMap, ker_comp]
    rw [h, Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq]
  have hcont : ContinuousAt L' x₀ := continuousAt_clm_apply.2 fun p ↦ hL (ψ p)
  filter_upwards [hcont.eventually
    (ContinuousLinearMap.eventually_nhds_finiteDimensional_ker_and_finrank_ker_le
      (Submodule.isClosed_of_finiteDimensional (L' x₀).range))] with x hx
  rw [← hfr x, ← hfr x₀]
  exact hx.2

end LinearMap

end
