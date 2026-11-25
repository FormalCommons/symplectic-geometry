/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.HomotopyOperator
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.SmoothFamily.HomotopyOperator
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.SmoothFamily.NormedSpace
public import SymplecticGeometry.Geometry.Symplectic.HPrinciple.CubeClipping
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
`attachingCollar ι κ ε` with `ε ≤ δ` into `A`. For any such `Φ`, this file
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

For a smooth family `τ` of two-forms over a manifold, nondegenerate on `Q` and exact near `A`
for each parameter in a compact set `K`, the corrections `η l = h (Φ^* d (τ l))` form a smooth
family. With the clipping homotopy of a width `δ` chosen by compactness, they give one product
collar on which `τ l - η l` is exact for every `l ∈ K`, while `τ l - s • η l`, `s ∈ [0, 1]`,
stays nondegenerate on `Q` (`SymplecticGeometry.exists_isSmoothFamily_collarCorrection`). The
width comes from the bound `‖h (Φ^* d (τ l))‖ ≤ 2δ · 5² · sup_Q ‖d (τ l)‖` of
`SymplecticGeometry.norm_homotopyOperator_mpullback_apply_le_of_affine` and from
`SymplecticGeometry.IsSmoothFamily.exists_pos_forall_nondegenerate_sub_smul`.

## Main results

* `SymplecticGeometry.eventually_homotopyOperator_mpullback_mextDerivₗ_eq_zero_sphere_prod`
* `SymplecticGeometry.exists_mextDerivₗ_eq_sub_homotopyOperator_mpullback_sphere_prod`
* `SymplecticGeometry.eventually_homotopyOperator_mpullback_mextDerivₗ_eq_zero_closedBall`
* `SymplecticGeometry.exists_isSmoothFamily_collarCorrection`: a common collar for a smooth
  family of forms that are exact near `A`, each on its own neighbourhood.

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

section Family

variable {EN HN N : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
  [TopologicalSpace N] [ChartedSpace HN N] {J : ModelWithCorners ℝ EN HN} [IsManifold J ∞ N]

/-- **A common collar for a family of forms exact near the attaching faces.** On the handle core
`D = (ι → ℝ) × (κ → ℝ)` with sup norms, let `Q = closedBall 0 1` and
`A = sphere 0 1 ×ˢ closedBall 0 1`, and let `τ` be a smooth family of two-forms on `D` over a
manifold `N`, with a compact set `K` of parameters, such that for every `l ∈ K` the form `τ l` is
nondegenerate on `Q` and is `dβ` on some neighbourhood of `A`, which may depend on `l`.

Then there are `0 < ε ≤ 1` and a smooth family `η` of two-forms on `D` over `N` such that, for
every `l ∈ K`, with `W₀ = attachingCollar ι κ ε` the product collar of `A`:
* `η l` vanishes on a neighbourhood of `A`;
* `τ l - s • η l` is nondegenerate on `Q` for every `s ∈ [0, 1]`;
* `τ l - η l` is `dγ` on `W₀` for a smooth one-form `γ` on `D`;
* if `τ l` is `dγ'` on a neighbourhood of `Q`, then so is each `τ l - s • η l`, `s ∈ [0, 1]`. -/
theorem exists_isSmoothFamily_collarCorrection
    {τ : N → SmoothTwoForm 𝓘(ℝ, (ι → ℝ) × (κ → ℝ)) ((ι → ℝ) × (κ → ℝ))}
    (hτ : IsSmoothFamily J τ) {K : Set N} (hK : IsCompact K)
    (hnd : ∀ l ∈ K, ∀ x ∈ closedBall (0 : (ι → ℝ) × (κ → ℝ)) 1,
      ((τ l).bilinFormAt x).Nondegenerate)
    (hex : ∀ l ∈ K, ∃ W ∈ 𝓝ˢ (sphere (0 : ι → ℝ) 1 ×ˢ closedBall (0 : κ → ℝ) 1),
      ∃ β : SmoothForm 𝓘(ℝ, (ι → ℝ) × (κ → ℝ)) ((ι → ℝ) × (κ → ℝ)) ℝ 1,
        ∀ x ∈ W, (mextDerivₗ 𝓘(ℝ, (ι → ℝ) × (κ → ℝ)) 1 β).val x = (τ l).val x) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
      ∃ η : N → SmoothTwoForm 𝓘(ℝ, (ι → ℝ) × (κ → ℝ)) ((ι → ℝ) × (κ → ℝ)),
        IsSmoothFamily J η ∧ ∀ l ∈ K,
          (∀ᶠ x in 𝓝ˢ (sphere (0 : ι → ℝ) 1 ×ˢ closedBall (0 : κ → ℝ) 1), (η l).val x = 0) ∧
          (∀ s ∈ Icc (0 : ℝ) 1, ∀ x ∈ closedBall (0 : (ι → ℝ) × (κ → ℝ)) 1,
            ((τ l - s • η l).bilinFormAt x).Nondegenerate) ∧
          (∃ γ : SmoothForm 𝓘(ℝ, (ι → ℝ) × (κ → ℝ)) ((ι → ℝ) × (κ → ℝ)) ℝ 1,
            ∀ x ∈ attachingCollar ι κ ε,
              (mextDerivₗ 𝓘(ℝ, (ι → ℝ) × (κ → ℝ)) 1 γ).val x = (τ l - η l).val x) ∧
          ((∃ V ∈ 𝓝ˢ (closedBall (0 : (ι → ℝ) × (κ → ℝ)) 1),
              ∃ γ' : SmoothForm 𝓘(ℝ, (ι → ℝ) × (κ → ℝ)) ((ι → ℝ) × (κ → ℝ)) ℝ 1,
                ∀ x ∈ V, (mextDerivₗ 𝓘(ℝ, (ι → ℝ) × (κ → ℝ)) 1 γ').val x = (τ l).val x) →
            ∀ s ∈ Icc (0 : ℝ) 1, ∃ V ∈ 𝓝ˢ (closedBall (0 : (ι → ℝ) × (κ → ℝ)) 1),
              ∃ γ' : SmoothForm 𝓘(ℝ, (ι → ℝ) × (κ → ℝ)) ((ι → ℝ) × (κ → ℝ)) ℝ 1,
                ∀ x ∈ V, (mextDerivₗ 𝓘(ℝ, (ι → ℝ) × (κ → ℝ)) 1 γ').val x =
                  (τ l - s • η l).val x) := by
  -- Nondegeneracy on `Q` survives subtracting `s • η` with `‖η‖ < r`, uniformly over `K`.
  obtain ⟨r, hr, hrnd⟩ :=
    hτ.exists_pos_forall_nondegenerate_sub_smul hK (isCompact_closedBall 0 1) hnd
  -- The exterior derivatives `d (τ l)` are bounded on `Q` by `C`, uniformly over `K`.
  obtain ⟨C, hC⟩ := hτ.mextDeriv.exists_norm_val_le hK (isCompact_closedBall 0 1)
  set C' := max C 0
  -- A width `δ` of the clipping homotopy for which `2 δ 5² C' < r`.
  set δ := min (1 / 2) (r / (100 * (C' + 1)))
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ₂ : δ ≤ 1 / 2 := min_le_left _ _
  have hδr : 2 * δ * 5 ^ 2 * C' < r := by
    have h₁ : δ * (100 * (C' + 1)) ≤ r :=
      (le_div_iff₀ (by positivity)).1 (min_le_right _ _)
    nlinarith [le_max_right C 0]
  obtain ⟨Φ, hΦ, haff, h₁, -, hA, hQ, -, hcol, hd, hL⟩ :=
    exists_contMDiff_cubeClipping (ι := ι) (κ := κ) hδ hδ₂
  refine ⟨δ, hδ, by linarith,
    fun l ↦ homotopyOperator (mpullback Φ hΦ (mextDerivₗ _ 2 (τ l))),
    (hτ.mextDeriv.mpullback Φ hΦ).homotopyOperator, fun l hl ↦ ?_⟩
  obtain ⟨W, hW, β, hβ⟩ := hex l hl
  refine ⟨eventually_homotopyOperator_mpullback_mextDerivₗ_eq_zero_sphere_prod hΦ hA hW hβ,
    fun s hs x hx ↦ hrnd l hl x hx _ ?_ s hs,
    exists_mextDerivₗ_eq_sub_homotopyOperator_mpullback_sphere_prod hΦ h₁ (hcol δ le_rfl)
      (subset_of_mem_nhdsSet hW) hβ, ?_⟩
  · -- On `Q` the correction has norm at most `2 δ 5² C' < r`.
    rw [coe_homotopyOperator, coe_mpullback]
    exact (norm_homotopyOperator_mpullback_apply_le_of_affine (hΦ.of_le (by simp)) haff hQ
      (fun x hx ↦ hd 0 x hx) (fun t x _ ↦ hL t x) _
      (fun y hy ↦ (hC l hl y hy).trans (le_max_left _ _)) hx).trans_lt hδr
  · -- Near `Q` the correction vanishes, so there each `τ l - s • η l` is `τ l`.
    rintro ⟨V, hV, γ', hγ'⟩ s -
    have h0 := eventually_homotopyOperator_mpullback_mextDerivₗ_eq_zero_closedBall hΦ hQ hV hγ'
    refine ⟨V ∩ {x | (homotopyOperator (mpullback Φ hΦ (mextDerivₗ _ 2 (τ l)))).val x = 0},
      Filter.inter_mem hV h0, γ', fun x hx ↦ ?_⟩
    simp only [Submodule.coe_sub, Submodule.coe_smul, Pi.sub_apply, Pi.smul_apply]
    rw [hx.2, smul_zero, sub_zero, hγ' x hx.1]

end Family

end SymplecticGeometry

end
