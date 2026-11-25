/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.HomotopyOperator
public import Mathlib.Geometry.Manifold.Instances.Icc
public import Mathlib.Topology.UnitInterval

/-!
# The collar correction of a form in the handle-core lemma

Let `Φ : D × [0, 1] → D` be a smooth homotopy to the identity on the handle core
`D = (ι → ℝ) × (κ → ℝ)`, with sup norms, and let `h` be the homotopy operator
`TauCeti.SmoothForm.homotopyOperator`. For a smooth `(k + 1)`-form `τ` on `D`, the
*collar correction* is the form `η = h (Φ^* dτ)`. Its use in the handle-core lemma
(McDuff–Salamon, Lemma 7.3.2) is to replace a form that is exact only on some neighbourhood of
the attaching faces by one that is exact on a fixed collar of them.

Let `A = sphere 0 1 ×ˢ closedBall 0 1` and `Q = closedBall 0 1`. The clipping homotopy of
`SymplecticGeometry.exists_contMDiff_cubeClipping` maps `A` and `Q` into themselves at every
time, and its first stage maps each thin product collar
`{x | |‖x.1‖ - 1| < ε ∧ ‖x.2‖ < 1 + ε}` with `ε ≤ δ` into `A`. For any such `Φ`, this file
proves:

* if `τ = dβ` on a neighbourhood of `A`, then `η` vanishes on a neighbourhood of `A`
  (`SymplecticGeometry.eventually_homotopyOperator_mpullback_mextDerivₗ_eq_zero_sphere_prod`);
* if `τ = dβ` on a set containing `A`, and `Φ (·, 0)` maps a set `W₀` into `A`, then
  `τ - η = dγ` on `W₀` for a smooth form `γ`
  (`SymplecticGeometry.exists_mextDerivₗ_eq_sub_homotopyOperator_mpullback_sphere_prod`);
* if `τ = dγ'` on a neighbourhood of `Q`, then `η` vanishes on a neighbourhood of `Q`
  (`SymplecticGeometry.eventually_homotopyOperator_mpullback_mextDerivₗ_eq_zero_closedBall`).

They are the handle-core cases of two facts on any manifold, in
`SymplecticGeometry/Geometry/Manifold/DifferentialForm/HomotopyOperator.lean`:
`TauCeti.SmoothForm.eventually_homotopyOperator_mpullback_mextDerivₗ_eq_zero` (the correction
vanishes near a compact set whose paths stay where `τ` is exact, since there `dτ = ddβ = 0`) and
`TauCeti.SmoothForm.exists_mextDerivₗ_eq_sub_homotopyOperator_mpullback_on` (by the homotopy
formula, `τ - η = g^* τ + d (h (Φ^* τ))`, and `g^* τ = d (g^* β)` where `g = Φ (·, 0)` lands in
the domain of the primitive `β`).

## Main results

* `SymplecticGeometry.eventually_homotopyOperator_mpullback_mextDerivₗ_eq_zero_sphere_prod`
* `SymplecticGeometry.exists_mextDerivₗ_eq_sub_homotopyOperator_mpullback_sphere_prod`
* `SymplecticGeometry.eventually_homotopyOperator_mpullback_mextDerivₗ_eq_zero_closedBall`

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Lemma 7.3.2.
* [R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982], §4.
-/

public section

open Set Metric
open scoped Manifold ContDiff Topology

namespace SymplecticGeometry

open TauCeti TauCeti.SmoothForm

variable {ι κ F : Type*} [Fintype ι] [Fintype κ] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {k : ℕ} {Φ : ((ι → ℝ) × (κ → ℝ)) × unitInterval → (ι → ℝ) × (κ → ℝ)}
  {τ : SmoothForm 𝓘(ℝ, (ι → ℝ) × (κ → ℝ)) ((ι → ℝ) × (κ → ℝ)) F (k + 1)}
  {β : SmoothForm 𝓘(ℝ, (ι → ℝ) × (κ → ℝ)) ((ι → ℝ) × (κ → ℝ)) F k}
  {W : Set ((ι → ℝ) × (κ → ℝ))}

/-- **The collar correction vanishes near the attaching faces.** On `D = (ι → ℝ) × (κ → ℝ)`, let
`Φ : D × [0, 1] → D` be smooth with every stage `Φ (·, t)` mapping
`A = sphere 0 1 ×ˢ closedBall 0 1` into itself. If a smooth form `τ` is `dβ` on a neighbourhood
`W` of `A`, then `h (Φ^* dτ)` vanishes on a neighbourhood of `A`. -/
theorem eventually_homotopyOperator_mpullback_mextDerivₗ_eq_zero_sphere_prod
    (hΦ : ContMDiff (𝓘(ℝ, (ι → ℝ) × (κ → ℝ)).prod (𝓡∂ 1)) 𝓘(ℝ, (ι → ℝ) × (κ → ℝ)) ∞ Φ)
    (hA : ∀ t, MapsTo (fun x ↦ Φ (x, t)) (sphere 0 1 ×ˢ closedBall 0 1)
      (sphere 0 1 ×ˢ closedBall 0 1))
    (hW : W ∈ 𝓝ˢ (sphere 0 1 ×ˢ closedBall 0 1))
    (hβ : ∀ x ∈ W, (mextDerivₗ 𝓘(ℝ, (ι → ℝ) × (κ → ℝ)) k β).val x = τ.val x) :
    ∀ᶠ x in 𝓝ˢ (sphere 0 1 ×ˢ closedBall 0 1),
      (homotopyOperator (mpullback Φ hΦ
        (mextDerivₗ 𝓘(ℝ, (ι → ℝ) × (κ → ℝ)) (k + 1) τ))).val x = 0 :=
  eventually_homotopyOperator_mpullback_mextDerivₗ_eq_zero hΦ isOpen_interior
    (fun y hy ↦ hβ y (interior_subset hy))
    ((isCompact_sphere _ _).prod (isCompact_closedBall _ _))
    fun _ hx t ↦ subset_interior_iff_mem_nhdsSet.2 hW (hA t hx)

/-- **The collar correction leaves a form exact on the collar.** On `D = (ι → ℝ) × (κ → ℝ)`, let
`Φ : D × [0, 1] → D` be a smooth homotopy to the identity, `Φ (x, 1) = x`, whose first stage
`Φ (·, 0)` maps a set `W₀` into `A = sphere 0 1 ×ˢ closedBall 0 1`. If a smooth form `τ` with
values in a Banach space is `dβ` on a set `W` containing `A`, then `τ - h (Φ^* dτ)` is `dγ` on
`W₀` for a smooth form `γ` on `D`. -/
theorem exists_mextDerivₗ_eq_sub_homotopyOperator_mpullback_sphere_prod
    [CompleteSpace F]
    (hΦ : ContMDiff (𝓘(ℝ, (ι → ℝ) × (κ → ℝ)).prod (𝓡∂ 1)) 𝓘(ℝ, (ι → ℝ) × (κ → ℝ)) ∞ Φ)
    (h₁ : ∀ x, Φ (x, 1) = x) {W₀ : Set ((ι → ℝ) × (κ → ℝ))}
    (hW₀ : MapsTo (fun x ↦ Φ (x, 0)) W₀ (sphere 0 1 ×ˢ closedBall 0 1))
    (hW : sphere 0 1 ×ˢ closedBall 0 1 ⊆ W)
    (hβ : ∀ x ∈ W, (mextDerivₗ 𝓘(ℝ, (ι → ℝ) × (κ → ℝ)) k β).val x = τ.val x) :
    ∃ γ : SmoothForm 𝓘(ℝ, (ι → ℝ) × (κ → ℝ)) ((ι → ℝ) × (κ → ℝ)) F k, ∀ x ∈ W₀,
      (mextDerivₗ 𝓘(ℝ, (ι → ℝ) × (κ → ℝ)) k γ).val x =
        (τ - homotopyOperator (mpullback Φ hΦ
          (mextDerivₗ 𝓘(ℝ, (ι → ℝ) × (κ → ℝ)) (k + 1) τ))).val x :=
  exists_mextDerivₗ_eq_sub_homotopyOperator_mpullback_on hΦ h₁ hβ fun _ hx ↦ hW (hW₀ hx)

/-- **The collar correction vanishes near the core.** On `D = (ι → ℝ) × (κ → ℝ)`, let
`Φ : D × [0, 1] → D` be smooth with every stage `Φ (·, t)` mapping `Q = closedBall 0 1` into
itself. If a smooth form `τ` is `dγ'` on a neighbourhood `V` of `Q`, then `h (Φ^* dτ)` vanishes
on a neighbourhood of `Q`. -/
theorem eventually_homotopyOperator_mpullback_mextDerivₗ_eq_zero_closedBall
    (hΦ : ContMDiff (𝓘(ℝ, (ι → ℝ) × (κ → ℝ)).prod (𝓡∂ 1)) 𝓘(ℝ, (ι → ℝ) × (κ → ℝ)) ∞ Φ)
    (hQ : ∀ t, MapsTo (fun x ↦ Φ (x, t)) (closedBall 0 1) (closedBall 0 1))
    {γ' : SmoothForm 𝓘(ℝ, (ι → ℝ) × (κ → ℝ)) ((ι → ℝ) × (κ → ℝ)) F k}
    {V : Set ((ι → ℝ) × (κ → ℝ))} (hV : V ∈ 𝓝ˢ (closedBall 0 1))
    (hγ' : ∀ x ∈ V, (mextDerivₗ 𝓘(ℝ, (ι → ℝ) × (κ → ℝ)) k γ').val x = τ.val x) :
    ∀ᶠ x in 𝓝ˢ (closedBall (0 : (ι → ℝ) × (κ → ℝ)) 1),
      (homotopyOperator (mpullback Φ hΦ
        (mextDerivₗ 𝓘(ℝ, (ι → ℝ) × (κ → ℝ)) (k + 1) τ))).val x = 0 :=
  eventually_homotopyOperator_mpullback_mextDerivₗ_eq_zero hΦ isOpen_interior
    (fun y hy ↦ hγ' y (interior_subset hy)) (isCompact_closedBall _ _)
    fun _ hx t ↦ subset_interior_iff_mem_nhdsSet.2 hV (hQ t hx)

end SymplecticGeometry

end
