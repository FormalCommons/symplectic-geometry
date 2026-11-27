/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.Orientation
public import TauCeti.Geometry.Symplectic.SymplecticTransport
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.Normed.Module.FiniteDimension
import TauCeti.Geometry.Symplectic.ExistsCompatible
import TauCeti.Topology.Algebra.Module.BilinearForm

/-!
# Adapted bases of a transported almost complex structure

If a symplectic form `ω` on `V` tames an almost complex structure `J`, and `e : V ≃ W` is a
linear equivalence, then every basis `(v₁, J' v₁, …, vₙ, J' vₙ)` of `W` adapted to the transport
`J' = e ∘ J ∘ e⁻¹` induces the image under `e` of the symplectic orientation of `ω`
(`TauCeti.SymplecticForm.Tames.orientation_reindex_transport`). This combines Tau Ceti's
`TauCeti.SymplecticForm.Tames.orientation_reindex`, applied to the transported form, with the
naturality `TauCeti.SymplecticForm.IsSymplectomorphism.map_orientation`.

The symplectic orientation is also unchanged along a continuous family of symplectic forms: if
`x ↦ ω x v w` is continuous for all `v, w`, then `x ↦ (ω x).orientation hk` is locally constant
(`TauCeti.SymplecticForm.isLocallyConstant_orientation`), hence constant over a preconnected
parameter space (`TauCeti.SymplecticForm.orientation_eq_of_preconnectedSpace`). Near `x₀`, an
almost complex structure tamed by `ω x₀` (`TauCeti.SymplecticForm.exists_tames`) is still tamed,
since taming is an open condition (`TauCeti.isOpen_setOf_forall_bilinear_apply_endomorphism_pos`),
and forms taming a common structure have the same orientation
(`TauCeti.SymplecticForm.Tames.orientation_eq`). This adapts the proof of Tau Ceti's private
`eventually_mapOrientation_orientation_eq` (`TauCeti/Geometry/Symplectic/Manifold/Orientation.lean`)
from the tangent spaces of a manifold to a family of forms on one vector space.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017]
-/

public section

open Module Topology

namespace TauCeti.SymplecticForm

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
  [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]
  {ω : SymplecticForm V} {J : AlmostComplexStructure V} {n k : ℕ}
  {b : Basis (Fin n × Fin 2) ℝ W}

/-- If `ω` tames `J` and `e : V ≃ W` is a linear equivalence, every basis
`(v₁, J' v₁, …, vₙ, J' vₙ)` of `W` adapted to the transport `J' = e ∘ J ∘ e⁻¹` induces the
image under `e` of the symplectic orientation of `ω`. -/
theorem Tames.orientation_reindex_transport (hJ : ω.Tames J) (e : V ≃ₗ[ℝ] W)
    (hk : finrank ℝ V = k) (hb : ∀ i, b (i, 1) = J.transport e (b (i, 0))) (h : n * 2 = k) :
    (b.reindex (finProdFinEquiv.trans (finCongr h))).orientation =
      Orientation.map (Fin k) e (ω.orientation hk) := by
  rw [(hJ.transport e).orientation_reindex hb (e.finrank_eq.symm.trans hk) h,
    (isSymplectomorphism_iff_transport_eq.2 rfl).map_orientation hk]

section Family

variable {X : Type*} [TopologicalSpace X] {ω : X → SymplecticForm V}

/-- Along a family of symplectic forms `ω x` on `V` whose values `ω x v w` depend continuously on
`x`, the symplectic orientation is locally constant. -/
theorem isLocallyConstant_orientation (hω : ∀ v w, Continuous fun x ↦ ω x v w)
    (hk : finrank ℝ V = k) : IsLocallyConstant fun x ↦ (ω x).orientation hk := by
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun x₀ ↦ ?_
  obtain ⟨J, hJ⟩ := (ω x₀).exists_tames
  -- Carry the forms and `J` to a normed space, where taming is an open condition.
  let e := (Module.finBasis ℝ V).equivFun
  let B : X → (Fin (finrank ℝ V) → ℝ) →L[ℝ] (Fin (finrank ℝ V) → ℝ) →L[ℝ] ℝ := fun x ↦
    LinearMap.toContinuousLinearMap
      (LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ
        (ω x).toBilinForm.compl₁₂ e.symm.toLinearMap e.symm.toLinearMap)
  have hB (x u u') : B x u u' = ω x (e.symm u) (e.symm u') := rfl
  let A := LinearMap.toContinuousLinearMap (e.toLinearMap ∘ₗ J.toLinearMap ∘ₗ e.symm.toLinearMap)
  have hA (u) : A u = e (J (e.symm u)) := rfl
  have hc : Continuous fun x ↦ (B x, A) := by
    refine Continuous.prodMk (continuous_clm_apply.2 fun u ↦ continuous_clm_apply.2 fun u' ↦ ?_)
      continuous_const
    simpa only [hB] using hω _ _
  have htame : ∀ᶠ x in 𝓝 x₀, (ω x).Tames J := by
    refine (hc.continuousAt.eventually_mem
      (TauCeti.isOpen_setOf_forall_bilinear_apply_endomorphism_pos.mem_nhds fun u hu ↦ ?_)).mono
      fun x hx v hv ↦ ?_
    · simpa [hB, hA] using hJ _ ((LinearEquiv.map_ne_zero_iff _).2 hu)
    · simpa [hB, hA] using hx (e v) ((LinearEquiv.map_ne_zero_iff _).2 hv)
  exact htame.mono fun x hx ↦ hx.orientation_eq hJ hk

/-- Along a family of symplectic forms over a preconnected parameter space, whose values
`ω x v w` depend continuously on `x`, the symplectic orientation is constant. -/
theorem orientation_eq_of_preconnectedSpace [PreconnectedSpace X]
    (hω : ∀ v w, Continuous fun x ↦ ω x v w) (hk : finrank ℝ V = k) (x y : X) :
    (ω x).orientation hk = (ω y).orientation hk :=
  (isLocallyConstant_orientation hω hk).apply_eq_of_preconnectedSpace x y

end Family

end TauCeti.SymplecticForm

end
