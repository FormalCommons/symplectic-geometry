/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Alternating.Curry
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import TauCeti.Analysis.Normed.Module.Alternating.Uncurry.Fin

/-!
# Interior and exterior products against a covector

For a covector `ξ : E →L[𝕜] 𝕜`, the exterior product `ε_ξ` on forms is
`alternatizeUncurryFin (ξ.smulRight ·)`, and for a vector `v` the interior product `ι_v` is
`curryLeft · v`. This file gives the anticommutation identity `ι_v ε_ξ + ε_ξ ι_v = ξ(v)`, its
degree-`0` form `ι_v ε_ξ = ξ(v)`, and the expansion of `alternatizeUncurryFin f` over a basis.

## Main results

* `ContinuousAlternatingMap.curryLeft_alternatizeUncurryFin_smulRight_add`: the identity
  `ι_v ε_ξ + ε_ξ ι_v = ξ(v)` in positive degree. It is Tau Ceti's
  `ContinuousAlternatingMap.alternatizeUncurryFin_curryLeft_comp_add_curryLeft` for the family
  `ξ.smulRight w`.
* `ContinuousAlternatingMap.curryLeft_alternatizeUncurryFin_smulRight_zero`: `ι_v ε_ξ = ξ(v)` in
  degree `0`.
* `ContinuousAlternatingMap.alternatizeUncurryFin_eq_sum_coord_smulRight`: for a basis `b`,
  `alternatizeUncurryFin f` is the sum of the alternatizations of `b.coord i • f (b i)`.
* `ContinuousAlternatingMap.curryLeft_sum`: the interior product of a finite sum.
-/

public section

namespace ContinuousAlternatingMap

section

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] {n : ℕ}

/-- The interior product of a finite sum of forms is the sum of their interior products. -/
@[simp]
theorem curryLeft_sum {ι : Type*} (s : Finset ι) (f : ι → E [⋀^Fin (n + 1)]→L[𝕜] F) :
    (∑ i ∈ s, f i).curryLeft = ∑ i ∈ s, (f i).curryLeft := by
  ext v u
  simp [curryLeft_apply_apply]

/-- For a covector `ξ`, a vector `v` and a form `w` of positive degree,
`ι_v (ε_ξ w) + ε_ξ (ι_v w) = ξ v • w`, where `ε_ξ` is the exterior product
`alternatizeUncurryFin (ξ.smulRight ·)` and `ι_v` the interior product `curryLeft · v`. This is
`alternatizeUncurryFin_curryLeft_comp_add_curryLeft` for `ξ.smulRight w`. -/
theorem curryLeft_alternatizeUncurryFin_smulRight_add (ξ : E →L[𝕜] 𝕜)
    (w : E [⋀^Fin (n + 1)]→L[𝕜] F) (v : E) :
    (alternatizeUncurryFin (ξ.smulRight w)).curryLeft v +
        alternatizeUncurryFin (ξ.smulRight (w.curryLeft v)) = ξ v • w := by
  have hc : (curryLeftLI (𝕜 := 𝕜) (E := E) (F := F)).toContinuousLinearMap.flip v ∘L
      ξ.smulRight w = ξ.smulRight (w.curryLeft v) := by
    ext1 u
    simp
  rw [← hc, add_comm ((alternatizeUncurryFin (ξ.smulRight w)).curryLeft v),
    alternatizeUncurryFin_curryLeft_comp_add_curryLeft, ContinuousLinearMap.smulRight_apply]

/-- For a covector `ξ`, a vector `v` and a form `w` of degree `0`, `ι_v (ε_ξ w) = ξ v • w`, where
`ε_ξ` is the exterior product `alternatizeUncurryFin (ξ.smulRight ·)`. -/
@[simp]
theorem curryLeft_alternatizeUncurryFin_smulRight_zero (ξ : E →L[𝕜] 𝕜)
    (w : E [⋀^Fin 0]→L[𝕜] F) (v : E) :
    (alternatizeUncurryFin (ξ.smulRight w)).curryLeft v = ξ v • w := by
  ext u
  simp [alternatizeUncurryFin_apply, curryLeft_apply_apply, Subsingleton.elim u Fin.elim0,
    Matrix.vecCons]

end

variable {𝕜 E F ι : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [Fintype ι]

/-- For a basis `b`, `alternatizeUncurryFin f` is the sum over `i` of the alternatizations of
`b.coord i • f (b i)`, as `f = ∑ i, b.coord i • f (b i)`. -/
theorem alternatizeUncurryFin_eq_sum_coord_smulRight (b : Module.Basis ι 𝕜 E) {n : ℕ}
    (f : E →L[𝕜] E [⋀^Fin n]→L[𝕜] F) :
    alternatizeUncurryFin f = ∑ i, alternatizeUncurryFin
      ((LinearMap.toContinuousLinearMap (b.coord i)).smulRight (f (b i))) := by
  have hf : f = ∑ i, (LinearMap.toContinuousLinearMap (b.coord i)).smulRight (f (b i)) := by
    ext1 v
    simp only [FunLike.coe_sum, Finset.sum_apply, ContinuousLinearMap.smulRight_apply,
      LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply]
    simp_rw [← map_smul, ← _root_.map_sum, b.sum_repr]
  conv_lhs => rw [hf]
  rw [← alternatizeUncurryFinCLM_apply, _root_.map_sum]
  simp only [alternatizeUncurryFinCLM_apply]

end ContinuousAlternatingMap

end
