/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.HomotopyOperator
public import Mathlib.Geometry.Manifold.Instances.Icc
public import Mathlib.Topology.UnitInterval
import TauCeti.Geometry.Manifold.DifferentialForm.Squared

/-!
# The collar correction of a form in the handle-core lemma

Let `Φ : M × [0, 1] → M` be a smooth homotopy from `g = Φ (·, 0)` to the identity, and let `h` be
the homotopy operator `TauCeti.SmoothForm.homotopyOperator`. For a smooth `(k + 1)`-form `τ` on `M`,
the *collar correction* is the form `η = h (Φ^* dτ)`. Its use in the handle-core lemma
(McDuff–Salamon, Lemma 7.3.2) is to replace a form that is exact only on some neighbourhood of
the attaching faces by one that is exact on a fixed collar of them. This file proves the local
properties of `η` that this needs:

* if `τ = dβ` on a neighbourhood of a compact set `S` that every stage `Φ (·, t)` maps into
  itself, then `η` vanishes on a neighbourhood of `S`
  (`SymplecticGeometry.eventually_homotopyOperator_mpullback_mextDerivₗ_eq_zero`). The reason is
  that `dτ = ddβ = 0` near `S`, and points near `S` keep their whole path near `S`;
* if `τ = dβ` on a set `W` and `g` maps a set `W₀` into `W`, then `τ - η = dγ` on `W₀` for a
  smooth form `γ` (`SymplecticGeometry.exists_mextDerivₗ_eq_sub_homotopyOperator_mpullback_on`).
  Indeed the homotopy formula gives `τ - η = g^* τ + d (h (Φ^* τ))` on all of `M`, and on `W₀`
  the form `g^* τ` agrees with `g^* dβ = d (g^* β)`, so `γ = g^* β + h (Φ^* τ)`.

On the handle core `D = (ι → ℝ) × (κ → ℝ)`, with `A = sphere 0 1 ×ˢ closedBall 0 1` and
`Q = closedBall 0 1`, the clipping homotopy of `SymplecticGeometry.exists_contMDiff_cubeClipping`
maps `A` and `Q` into themselves at every time, and its first stage maps each thin product collar
`{x | |‖x.1‖ - 1| < ε ∧ ‖x.2‖ < 1 + ε}` with `ε ≤ δ` into `A`. For such a `Φ` the three facts are
`SymplecticGeometry.collarCorrection_of_cubeClipping`.

## Main results

* `SymplecticGeometry.eventually_homotopyOperator_mpullback_mextDerivₗ_eq_zero`
* `SymplecticGeometry.exists_mextDerivₗ_eq_sub_homotopyOperator_mpullback_on`
* `SymplecticGeometry.collarCorrection_of_cubeClipping`

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

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

/-- **The collar correction vanishes near an invariant compact set.** Let `Φ : M × [0, 1] → M` be
smooth and let every stage `Φ (·, t)` map a compact set `S` into itself. If a smooth form `τ` is
`dβ` on a neighbourhood `W` of `S`, then `h (Φ^* dτ)` vanishes on a neighbourhood of `S`. -/
theorem eventually_homotopyOperator_mpullback_mextDerivₗ_eq_zero {Φ : M × unitInterval → M}
    (hΦ : ContMDiff (I.prod (𝓡∂ 1)) I ∞ Φ) {S : Set M} (hS : IsCompact S)
    (hΦS : ∀ x ∈ S, ∀ t, Φ (x, t) ∈ S) {τ : SmoothForm I M F (k + 1)} {β : SmoothForm I M F k}
    {W : Set M} (hW : W ∈ 𝓝ˢ S) (hβ : ∀ x ∈ W, (mextDerivₗ I k β).val x = τ.val x) :
    ∀ᶠ x in 𝓝ˢ S, (homotopyOperator (mpullback Φ hΦ (mextDerivₗ I (k + 1) τ))).val x = 0 := by
  -- `dτ = ddβ = 0` on the interior of `W`, since the exterior derivative is local.
  have hdτ : ∀ y ∈ interior W, (mextDerivₗ I (k + 1) τ).val y = 0 := fun y hy ↦ by
    have hev : ∀ᶠ z in 𝓝 y, τ.val z = (mextDerivₗ I k β).val z :=
      Filter.eventually_of_mem (mem_interior_iff_mem_nhds.1 hy) fun z hz ↦ (hβ z hz).symm
    have hdd := congrArg (fun φ : SmoothForm I M F (k + 2) ↦ φ.val y)
      (LinearMap.congr_fun (mextDerivₗ_comp_mextDerivₗ I (M := M) (F := F) k) β)
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, Submodule.coe_zero, Pi.zero_apply,
      mextDerivₗ_apply] at hdd
    rw [mextDerivₗ_apply, mextDeriv_congr_of_eventuallyEq hev, mextDerivₗ_apply, hdd]
  simp only [coe_homotopyOperator, coe_mpullback]
  exact eventually_homotopyOperator_mpullback_eq_zero hΦ.continuous isOpen_interior hdτ hS
    fun x hx t ↦ subset_interior_iff_mem_nhdsSet.2 hW (hΦS x hx t)

/-- **The collar correction leaves a form exact where the homotopy starts in a primitive's
domain.** Let `Φ : M × [0, 1] → M` be a smooth homotopy to the identity, `Φ (x, 1) = x`, and let
a smooth form `τ` be `dβ` on a set `W`. If `Φ (·, 0)` maps a set `W₀` into `W`, then
`τ - h (Φ^* dτ)` is `dγ` on `W₀` for a smooth form `γ` on `M`. -/
theorem exists_mextDerivₗ_eq_sub_homotopyOperator_mpullback_on [CompleteSpace F]
    {Φ : M × unitInterval → M} (hΦ : ContMDiff (I.prod (𝓡∂ 1)) I ∞ Φ) (h₁ : ∀ x, Φ (x, 1) = x)
    {τ : SmoothForm I M F (k + 1)} {β : SmoothForm I M F k} {W : Set M}
    (hβ : ∀ x ∈ W, (mextDerivₗ I k β).val x = τ.val x) {W₀ : Set M}
    (hW₀ : ∀ x ∈ W₀, Φ (x, 0) ∈ W) :
    ∃ γ : SmoothForm I M F k, ∀ x ∈ W₀, (mextDerivₗ I k γ).val x =
      (τ - homotopyOperator (mpullback Φ hΦ (mextDerivₗ I (k + 1) τ))).val x := by
  have hg : ContMDiff I I ∞ (Φ ∘ fun x : M ↦ (x, (0 : unitInterval))) :=
    hΦ.comp (contMDiff_id.prodMk contMDiff_const)
  -- The homotopy formula for `Φ^* τ`, whose end slices are `τ` and `g^* τ`.
  have key := mextDerivₗ_homotopyOperator_add_homotopyOperator_mextDerivₗ (mpullback Φ hΦ τ)
  rw [mextDerivₗ_mpullback, mpullback_mpullback, mpullback_mpullback] at key
  have hid : Φ ∘ (fun x : M ↦ (x, (1 : unitInterval))) = id := funext h₁
  simp_rw [hid, SmoothForm.mpullback_id, LinearMap.id_apply] at key
  have hη : homotopyOperator (mpullback Φ hΦ (mextDerivₗ I (k + 1) τ)) =
      τ - mpullback _ hg τ - mextDerivₗ I k (homotopyOperator (mpullback Φ hΦ τ)) := by
    rw [← key]
    abel
  refine ⟨mpullback _ hg β + homotopyOperator (mpullback Φ hΦ τ), fun x hx ↦ ?_⟩
  -- At a point of `W₀`, the form `g^* dβ = d (g^* β)` agrees with `g^* τ`.
  have hgx : (mpullback _ hg (mextDerivₗ I k β)).val x = (mpullback _ hg τ).val x := by
    rw [coe_mpullback, coe_mpullback, mpullback_apply_eq_compContinuousLinearMap,
      mpullback_apply_eq_compContinuousLinearMap,
      hβ ((Φ ∘ fun x : M ↦ (x, (0 : unitInterval))) x) (hW₀ x hx)]
  rw [hη, map_add, mextDerivₗ_mpullback]
  simp only [Submodule.coe_add, Submodule.coe_sub, Pi.add_apply, Pi.sub_apply, hgx]
  abel

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- **The collar correction on the handle core.** On `D = (ι → ℝ) × (κ → ℝ)`, with sup norms,
let `A = sphere 0 1 ×ˢ closedBall 0 1`, `Q = closedBall 0 1`, and let `W₀` be a set. Let
`Φ : D × [0, 1] → D` be a smooth homotopy to the identity whose stages all map `A` into `A` and
`Q` into `Q`, and whose first stage maps `W₀` into `A`, as the clipping homotopy of
`exists_contMDiff_cubeClipping` does for each collar `{x | |‖x.1‖ - 1| < ε ∧ ‖x.2‖ < 1 + ε}` with
`ε ≤ δ`. Let `τ` be a smooth form on `D` and `η = h (Φ^* dτ)`. Then:
* if `τ` is `dβ` on a neighbourhood of `A`, then `η` vanishes on a neighbourhood of `A`, and
  `τ - η` is `dγ` on `W₀` for a smooth form `γ`;
* if `τ` is `dγ'` on a neighbourhood of `Q`, then `η` vanishes on a neighbourhood of `Q`. -/
theorem collarCorrection_of_cubeClipping [CompleteSpace F]
    {Φ : ((ι → ℝ) × (κ → ℝ)) × unitInterval → (ι → ℝ) × (κ → ℝ)}
    (hΦ : ContMDiff (𝓘(ℝ, (ι → ℝ) × (κ → ℝ)).prod (𝓡∂ 1)) 𝓘(ℝ, (ι → ℝ) × (κ → ℝ)) ∞ Φ)
    (h₁ : ∀ x, Φ (x, 1) = x)
    (hA : ∀ t, MapsTo (fun x ↦ Φ (x, t)) (sphere 0 1 ×ˢ closedBall 0 1)
      (sphere 0 1 ×ˢ closedBall 0 1))
    (hQ : ∀ t, MapsTo (fun x ↦ Φ (x, t)) (closedBall 0 1) (closedBall 0 1))
    {W₀ : Set ((ι → ℝ) × (κ → ℝ))}
    (hW₀ : MapsTo (fun x ↦ Φ (x, 0)) W₀ (sphere 0 1 ×ˢ closedBall 0 1))
    (τ : SmoothForm 𝓘(ℝ, (ι → ℝ) × (κ → ℝ)) ((ι → ℝ) × (κ → ℝ)) F (k + 1)) :
    ((∃ β : SmoothForm 𝓘(ℝ, (ι → ℝ) × (κ → ℝ)) ((ι → ℝ) × (κ → ℝ)) F k,
        ∃ W ∈ 𝓝ˢ (sphere 0 1 ×ˢ closedBall 0 1),
          ∀ x ∈ W, (mextDerivₗ 𝓘(ℝ, (ι → ℝ) × (κ → ℝ)) k β).val x = τ.val x) →
      (∀ᶠ x in 𝓝ˢ (sphere 0 1 ×ˢ closedBall 0 1),
        (homotopyOperator (mpullback Φ hΦ
          (mextDerivₗ 𝓘(ℝ, (ι → ℝ) × (κ → ℝ)) (k + 1) τ))).val x = 0) ∧
      ∃ γ : SmoothForm 𝓘(ℝ, (ι → ℝ) × (κ → ℝ)) ((ι → ℝ) × (κ → ℝ)) F k, ∀ x ∈ W₀,
        (mextDerivₗ 𝓘(ℝ, (ι → ℝ) × (κ → ℝ)) k γ).val x =
          (τ - homotopyOperator (mpullback Φ hΦ
            (mextDerivₗ 𝓘(ℝ, (ι → ℝ) × (κ → ℝ)) (k + 1) τ))).val x) ∧
    ((∃ γ' : SmoothForm 𝓘(ℝ, (ι → ℝ) × (κ → ℝ)) ((ι → ℝ) × (κ → ℝ)) F k,
        ∃ V ∈ 𝓝ˢ (closedBall (0 : (ι → ℝ) × (κ → ℝ)) 1),
          ∀ x ∈ V, (mextDerivₗ 𝓘(ℝ, (ι → ℝ) × (κ → ℝ)) k γ').val x = τ.val x) →
      ∀ᶠ x in 𝓝ˢ (closedBall (0 : (ι → ℝ) × (κ → ℝ)) 1),
        (homotopyOperator (mpullback Φ hΦ
          (mextDerivₗ 𝓘(ℝ, (ι → ℝ) × (κ → ℝ)) (k + 1) τ))).val x = 0) :=
  ⟨fun ⟨_, _, hW, hβ⟩ ↦
    ⟨eventually_homotopyOperator_mpullback_mextDerivₗ_eq_zero hΦ
        ((isCompact_sphere _ _).prod (isCompact_closedBall _ _)) (fun _ hx t ↦ hA t hx) hW hβ,
      exists_mextDerivₗ_eq_sub_homotopyOperator_mpullback_on hΦ h₁ hβ
        fun _ hx ↦ subset_of_mem_nhdsSet hW (hW₀ hx)⟩,
    fun ⟨_, _, hV, hγ'⟩ ↦ eventually_homotopyOperator_mpullback_mextDerivₗ_eq_zero hΦ
      (isCompact_closedBall _ _) (fun _ hx t ↦ hQ t hx) hV hγ'⟩

end SymplecticGeometry

end
