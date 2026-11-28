/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Moment maps of a rescaled two-form

Tau Ceti's moment maps (`TauCeti.SmoothTwoForm.IsMomentMap`) satisfy `ι_{Z_M} σ = d μ_Z`, which is
linear in the pair `(σ, μ)`. Tau Ceti records the case of the factor `-1`
(`TauCeti.SmoothTwoForm.IsMomentMap.neg`); this file adds a general real factor.

## Main results

* `TauCeti.SmoothTwoForm.IsMomentMap.const_smul`: if `μ` is a moment map of an infinitesimal
  action for `σ`, then `c • μ` is a moment map of the same action for `c • σ`.
-/

public section

open scoped ContDiff Manifold

namespace TauCeti.SmoothTwoForm.IsMomentMap

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
  {σ : SmoothTwoForm I M} {a : InfinitesimalAction 𝔤 I M} {μ : M → Module.Dual ℝ 𝔤}

/-- **Rescaling a moment map.** If `μ` is a moment map of the infinitesimal action `a` for the
two-form `σ`, then for every real `c` the map `x ↦ c • μ x` is a moment map of `a` for `c • σ`. -/
theorem const_smul (h : σ.IsMomentMap a μ) (c : ℝ) :
    (c • σ).IsMomentMap a fun x ↦ c • μ x where
  contMDiff Z := (contDiff_id.const_smul c).contMDiff.comp (h.contMDiff Z)
  isHamiltonianVectorField Z := SmoothTwoForm.isHamiltonianVectorField_iff.2 fun x v ↦ by
    have hc : (fun y ↦ (c • μ y) Z) = c • fun y ↦ μ y Z := rfl
    rw [hc, mvfderiv_const_smul_field, SmoothForm.eval₂_smul, h.eval₂_apply,
      smul_apply]

end TauCeti.SmoothTwoForm.IsMomentMap

end
