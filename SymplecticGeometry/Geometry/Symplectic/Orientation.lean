/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.Orientation
public import TauCeti.Geometry.Symplectic.Restrict
public import TauCeti.Geometry.Symplectic.SymplecticTransport
public import Mathlib.Topology.LocallyConstant.Basic
public import SymplecticGeometry.LinearAlgebra.Symplectic.Subspace
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
import TauCeti.Geometry.Symplectic.ExistsCompatible
import TauCeti.Topology.Algebra.Module.BilinearForm

/-!
# Symplectic orientations: transported bases, continuous families and orthogonal splittings

If a symplectic form `ω` on `V` tames an almost complex structure `J`, and `e : V ≃ W` is a
linear equivalence, then every basis `(v₁, J' v₁, …, vₙ, J' vₙ)` of `W` adapted to the transport
`J' = e ∘ J ∘ e⁻¹` induces the image under `e` of the symplectic orientation of `ω`
(`TauCeti.SymplecticForm.Tames.orientation_reindex_transport`). This combines Tau Ceti's
`TauCeti.SymplecticForm.Tames.orientation_reindex`, applied to the transported form, with the
naturality `TauCeti.SymplecticForm.IsSymplectomorphism.map_orientation`.

The symplectic orientation is also unchanged along a continuous family of symplectic forms. If
`x ↦ ω x v w` is continuous at `x₀` for all `v, w`, an almost complex structure tamed by
`ω x₀` is tamed by `ω x` for `x` near `x₀` (`TauCeti.SymplecticForm.eventually_tames`), since
taming is an open condition (`TauCeti.isOpen_setOf_forall_bilinear_apply_endomorphism_pos`).
Taking such a structure (`TauCeti.SymplecticForm.exists_tames`), and since forms taming a common
structure have the same orientation (`TauCeti.SymplecticForm.Tames.orientation_eq`), `ω x` has
the orientation of `ω x₀` near `x₀` (`TauCeti.SymplecticForm.eventually_orientation_eq`). Under
continuity everywhere, `x ↦ (ω x).orientation hk` is therefore locally constant
(`TauCeti.SymplecticForm.isLocallyConstant_orientation`), hence constant over a preconnected
parameter space (`TauCeti.SymplecticForm.orientation_eq_of_preconnectedSpace`). This adapts the
proof of Tau Ceti's private `eventually_mapOrientation_orientation_eq`
(`TauCeti/Geometry/Symplectic/Manifold/Orientation.lean`) from the tangent spaces of a manifold
to a family of forms on one vector space.

If `V = H ⊕ L` is a splitting into `ω`-orthogonal subspaces, then the symplectic orientation of
`ω` is the image under `H × L ≃ V` of the product of the symplectic orientations of the
restrictions of `ω` to `H` and to `L`
(`TauCeti.SymplecticForm.orientation_eq_map_prod_of_isCompl`). The splitting gives `L = H^ω`
and makes both summands symplectic, by `TauCeti.SymplecticForm.orthogonal_eq_of_isCompl`,
`TauCeti.SymplecticForm.isSymplectic_left_of_isCompl` and
`TauCeti.SymplecticForm.isSymplectic_right_of_isCompl` of the library's
`LinearAlgebra/Symplectic/Subspace.lean`; the proof then combines Tau Ceti's
`TauCeti.SymplecticForm.isSymplectomorphism_prodEquivOfIsCompl`,
`TauCeti.SymplecticForm.IsSymplectomorphism.map_orientation` and
`TauCeti.SymplecticForm.orientation_prod`.

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

/-- If `ω x₀` tames `J` and the values `ω x v w` depend continuously on `x` at `x₀`, then `ω x`
tames `J` for all `x` near `x₀`. -/
theorem eventually_tames {x₀ : X} (hω : ∀ v w, ContinuousAt (fun x ↦ ω x v w) x₀)
    (hJ : (ω x₀).Tames J) : ∀ᶠ x in 𝓝 x₀, (ω x).Tames J := by
  -- Carry the forms and `J` to a normed space, where taming is an open condition.
  let e := (Module.finBasis ℝ V).equivFun
  let B : X → (Fin (finrank ℝ V) → ℝ) →L[ℝ] (Fin (finrank ℝ V) → ℝ) →L[ℝ] ℝ := fun x ↦
    ((ω x).toBilinForm.compl₁₂ e.symm.toLinearMap e.symm.toLinearMap).toContinuousBilinearMap
  have hB (x u u') : B x u u' = ω x (e.symm u) (e.symm u') := by simp [B]
  let A := LinearMap.toContinuousLinearMap (e.toLinearMap ∘ₗ J.toLinearMap ∘ₗ e.symm.toLinearMap)
  have hA (u) : A u = e (J (e.symm u)) := by simp [A]
  have hc : ContinuousAt (fun x ↦ (B x, A)) x₀ := by
    refine ContinuousAt.prodMk
      (continuousAt_clm_apply.2 fun u ↦ continuousAt_clm_apply.2 fun u' ↦ ?_) continuousAt_const
    simpa only [hB] using hω _ _
  refine (hc.eventually_mem
    (TauCeti.isOpen_setOf_forall_bilinear_apply_endomorphism_pos.mem_nhds fun u hu ↦ ?_)).mono
    fun x hx v hv ↦ ?_
  · simpa [hB, hA] using hJ _ ((LinearEquiv.map_ne_zero_iff _).2 hu)
  · simpa [hB, hA] using hx (e v) ((LinearEquiv.map_ne_zero_iff _).2 hv)

/-- If the values `ω x v w` of a family of symplectic forms depend continuously on `x` at `x₀`,
then `ω x` has the symplectic orientation of `ω x₀` for all `x` near `x₀`. -/
theorem eventually_orientation_eq {x₀ : X} (hω : ∀ v w, ContinuousAt (fun x ↦ ω x v w) x₀)
    (hk : finrank ℝ V = k) : ∀ᶠ x in 𝓝 x₀, (ω x).orientation hk = (ω x₀).orientation hk := by
  obtain ⟨J, hJ⟩ := (ω x₀).exists_tames
  exact (eventually_tames hω hJ).mono fun x hx ↦ hx.orientation_eq hJ hk

/-- Along a family of symplectic forms `ω x` on `V` whose values `ω x v w` depend continuously on
`x`, the symplectic orientation is locally constant. -/
theorem isLocallyConstant_orientation (hω : ∀ v w, Continuous fun x ↦ ω x v w)
    (hk : finrank ℝ V = k) : IsLocallyConstant fun x ↦ (ω x).orientation hk :=
  (IsLocallyConstant.iff_eventually_eq _).2 fun _ ↦
    eventually_orientation_eq (fun v w ↦ (hω v w).continuousAt) hk

/-- Along a family of symplectic forms over a preconnected parameter space, whose values
`ω x v w` depend continuously on `x`, the symplectic orientation is constant. -/
theorem orientation_eq_of_preconnectedSpace [PreconnectedSpace X]
    (hω : ∀ v w, Continuous fun x ↦ ω x v w) (hk : finrank ℝ V = k) (x y : X) :
    (ω x).orientation hk = (ω y).orientation hk :=
  (isLocallyConstant_orientation hω hk).apply_eq_of_preconnectedSpace x y

end Family

section Splitting

variable {H L : Submodule ℝ V}

/-- If `V = H ⊕ L` with `H` and `L` orthogonal for `ω`, the symplectic orientation of `ω` is the
image under `H × L ≃ V` of the product of the symplectic orientations of the restrictions of `ω`
to `H` and to `L`. -/
theorem orientation_eq_map_prod_of_isCompl (ω : SymplecticForm V) (hc : IsCompl H L)
    (hHL : ∀ h ∈ H, ∀ l ∈ L, ω h l = 0) {m n : ℕ} (hm : finrank ℝ H = m)
    (hn : finrank ℝ L = n) (hV : finrank ℝ V = m + n) :
    ω.orientation hV = Orientation.map (Fin (m + n)) (Submodule.prodEquivOfIsCompl H L hc)
      (((ω.restrict H (ω.isSymplectic_left_of_isCompl hc hHL).nondegenerate_restrict).orientation
          hm).prod
        ((ω.restrict L (ω.isSymplectic_right_of_isCompl hc hHL).nondegenerate_restrict).orientation
          hn) hm hn) := by
  obtain rfl := ω.orthogonal_eq_of_isCompl hc hHL
  rw [← orientation_prod _ _ hm hn (by rw [finrank_prod, hm, hn]),
    (ω.isSymplectomorphism_prodEquivOfIsCompl hc).map_orientation]

end Splitting

end TauCeti.SymplecticForm

end
