/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.SmoothFamily.Basic
public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Basic
import Mathlib.Geometry.Manifold.PartitionOfUnity
import SymplecticGeometry.Analysis.Calculus.HolonomicApproximation.Parametric
import SymplecticGeometry.Geometry.Symplectic.HPrinciple.AttachingCollar
import SymplecticGeometry.Geometry.Symplectic.HPrinciple.FormalPrimitive
import TauCeti.Geometry.Manifold.ContMDiff.Prod

/-!
# Holonomic approximation of the formal primitive near the handle core

Let `D = (Fin m → ℝ) × (Fin k → ℝ)` with the sup norms, `0 < k`, with the cube
`Q = closedBall 0 1`, the attaching faces `A = sphere 0 1 ×ˢ closedBall 0 1` and the core
`closedBall 0 1 ×ˢ {0}`. Take smooth families `τ` of two-forms and `β` of one-forms on `D` over a
finite-dimensional real normed space `L`, and an open `W ⊇ A` on which `dβ l = τ l` for the
parameters `l` of a compact `K`. This file proves
`SymplecticGeometry.exists_diffeotopy_norm_mextDerivₗ_sub_lt_near_core`: for every `r > 0` there
are a slab width `ε₀`, a family of diffeotopies `H` of `D` over `L` and a smooth family `β'` of
one-forms, both unchanged on the slab `1 - ε₀ < ‖u‖` next to `A` and off the open cube, and an
open set `V` containing the moved core over `K`, on which `dβ'` is within `r` of `τ`.

These are the steps of the approximation-and-compression proof of the handle-core lemma that come
before the compression of the cube.

## The construction

1. *A slab inside the collar.* `W` contains a product collar `attachingCollar (Fin m) (Fin k) ε`
   (`SymplecticGeometry.exists_attachingCollar_subset`). So for `ε₀ ≤ ε / 4` and `η ≤ ε / 2`, the
   points `(u, v)` with `‖v‖ ≤ 1` and `1 - 2ε₀ ≤ ‖u‖ ≤ 1 + η` lie in `W`.
2. *The formal primitive, made holonomic near the faces.* Let `χ` be a smooth cutoff on `D` that
   vanishes near `B ×ˢ {0}`, for `B = {1 - 2ε₀ ≤ ‖u‖ ≤ 1 + η}`, and is `1` off `W`
   (`exists_contMDiffMap_zero_one_nhds_of_isClosed`), and let `τ' l = dβ l + χ • (τ l - dβ l)`,
   a smooth family of two-forms. The datum is `f l := β l` with the field
   `G l = formalPrimitive (τ' l) (β l)`, smooth by `SymplecticGeometry.contMDiff_formalPrimitive`.
   As `τ' l = dβ l` near `B ×ˢ {0}`, it is holonomic there for every parameter
   (`SymplecticGeometry.formalPrimitive_eq_fderiv`); for the parameters of `K`, `τ' l = τ l`
   everywhere (on `W` as `dβ l = τ l` there, off `W` as `χ = 1`), so `G l` is the formal primitive
   of `τ l`.
3. *Holonomic approximation.* `SymplecticGeometry.exists_holonomic_approximation_family` with
   `P₀ = ∅`, accuracy `r / 4` and width `η / 2` gives `H` and `β'`. A point that is moved, or at
   which `β'` differs from `β`, lies within `η / 2` of the core and has its core coordinate off
   `B`, hence `‖u‖ < 1 - 2ε₀`. Near the moved core the derivative of `β' l` is within `r / 4` of
   the formal primitive, so `dβ' l` is within `r / 2` of `τ l`
   (`SymplecticGeometry.norm_extDeriv_sub_le_of_norm_fderiv_sub_formalPrimitive_le`), the
   manifold exterior derivative on `D` being `extDeriv` (`TauCeti.mextDeriv_eq_extDeriv`).

## Main results

* `SymplecticGeometry.exists_diffeotopy_norm_mextDerivₗ_sub_lt_near_core`

## References

* [Y. Eliashberg and N. Mishachev, *Introduction to the h-principle*][EliashbergMishachev2002],
  §10.2 and Theorem 4.7.4.
-/

public section

open Set Metric TauCeti ContinuousAlternatingMap
open scoped Manifold ContDiff Topology

namespace SymplecticGeometry

variable {m k : ℕ} {L : Type*} [NormedAddCommGroup L] [NormedSpace ℝ L] [FiniteDimensional ℝ L]

/-- **Holonomic approximation of the formal primitive near the handle core.** Let
`D = (Fin m → ℝ) × (Fin k → ℝ)` with the sup norms and `0 < k`, let `τ` and `β` be smooth
families of two-forms and one-forms on `D` over a finite-dimensional normed space `L`, and let
`W` be an open neighbourhood of the attaching faces `sphere 0 1 ×ˢ closedBall 0 1` on which
`dβ l = τ l` for every `l` in a compact `K`. Then for every `r > 0` there are

* `0 < ε₀ ≤ 1/4` such that every point `x` of the cube `closedBall 0 1` with
  `1 - 2 * ε₀ ≤ ‖x.1‖` lies in `W`,
* a diffeotopy `H` of `L × D` that keeps the parameter, a smooth family `β'` of one-forms on `D`
  over `L`, and an open `V ⊆ L × D`,

such that `H` fixes, and `β'` agrees with `β` at, every point `p` with `1 - ε₀ < ‖p.2.1‖` or
`1 ≤ ‖p.2‖`; `H (1, (l, y)) ∈ V` for `l ∈ K` and `y` in the core `closedBall 0 1 ×ˢ {0}`; and at
every `p ∈ V` with `p.1 ∈ K` the value of `dβ' p.1` at `p.2` is within `r` of that of
`τ p.1`. -/
theorem exists_diffeotopy_norm_mextDerivₗ_sub_lt_near_core (hk : 0 < k) {K : Set L}
    (hK : IsCompact K) {τ : L → SmoothTwoForm 𝓘(ℝ, (Fin m → ℝ) × (Fin k → ℝ))
      ((Fin m → ℝ) × (Fin k → ℝ))} (hτ : IsSmoothFamily 𝓘(ℝ, L) τ)
    {β : L → SmoothForm 𝓘(ℝ, (Fin m → ℝ) × (Fin k → ℝ)) ((Fin m → ℝ) × (Fin k → ℝ)) ℝ 1}
    (hβ : IsSmoothFamily 𝓘(ℝ, L) β) {W : Set ((Fin m → ℝ) × (Fin k → ℝ))} (hW : IsOpen W)
    (hAW : sphere (0 : Fin m → ℝ) 1 ×ˢ closedBall (0 : Fin k → ℝ) 1 ⊆ W)
    (hτβ : ∀ l ∈ K, ∀ x ∈ W,
      (mextDerivₗ 𝓘(ℝ, (Fin m → ℝ) × (Fin k → ℝ)) 1 (β l)).val x = (τ l).val x)
    {r : ℝ} (hr : 0 < r) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 4 ∧
      (∀ x ∈ closedBall (0 : (Fin m → ℝ) × (Fin k → ℝ)) 1, 1 - 2 * ε₀ ≤ ‖x.1‖ → x ∈ W) ∧
      ∃ (H : Diffeotopy 𝓘(ℝ, L × (Fin m → ℝ) × (Fin k → ℝ)) ∞ (L × (Fin m → ℝ) × (Fin k → ℝ)))
        (β' : L → SmoothForm 𝓘(ℝ, (Fin m → ℝ) × (Fin k → ℝ)) ((Fin m → ℝ) × (Fin k → ℝ)) ℝ 1)
        (V : Set (L × (Fin m → ℝ) × (Fin k → ℝ))),
        (∀ t p, (H (t, p)).1 = p.1) ∧ IsSmoothFamily 𝓘(ℝ, L) β' ∧ IsOpen V ∧
        (∀ t p, (1 - ε₀ < ‖p.2.1‖ ∨ 1 ≤ ‖p.2‖) →
          H (t, p) = p ∧ (β' p.1).val p.2 = (β p.1).val p.2) ∧
        (∀ l ∈ K, ∀ y ∈ closedBall (0 : Fin m → ℝ) 1 ×ˢ {(0 : Fin k → ℝ)}, H (1, (l, y)) ∈ V) ∧
        ∀ p ∈ V, p.1 ∈ K →
          @norm (((Fin m → ℝ) × (Fin k → ℝ)) [⋀^Fin 2]→L[ℝ] ℝ) _
            ((mextDerivₗ 𝓘(ℝ, (Fin m → ℝ) × (Fin k → ℝ)) 1 (β' p.1)).val p.2 -
              (τ p.1).val p.2) < r := by
  -- Step 1: a slab of the cube next to the faces, and a collar of the sphere in the core, in `W`.
  obtain ⟨ε, hε, hεW⟩ := exists_attachingCollar_subset hW hAW
  set ε₀ : ℝ := min (1 / 4) (ε / 4)
  set η : ℝ := min (1 / 4) (ε / 2)
  have hε₀pos : 0 < ε₀ := by positivity
  have hηpos : 0 < η := by positivity
  have hε₀₁ : ε₀ ≤ 1 / 4 := min_le_left _ _
  have hε₀₂ : ε₀ ≤ ε / 4 := min_le_right _ _
  have hη₁ : η ≤ 1 / 4 := min_le_left _ _
  have hη₂ : η ≤ ε / 2 := min_le_right _ _
  set B : Set (Fin m → ℝ) := {u | 1 - 2 * ε₀ ≤ ‖u‖ ∧ ‖u‖ ≤ 1 + η}
  have hcollar : ∀ x : (Fin m → ℝ) × (Fin k → ℝ), ‖x.2‖ ≤ 1 → x.1 ∈ B → x ∈ W :=
    fun x hv ⟨hu₁, hu₂⟩ ↦ hεW (mem_attachingCollar_iff.2
      ⟨abs_lt.2 ⟨by linarith, by linarith⟩, by linarith⟩)
  have hslab : ∀ x ∈ closedBall (0 : (Fin m → ℝ) × (Fin k → ℝ)) 1,
      1 - 2 * ε₀ ≤ ‖x.1‖ → x ∈ W := by
    intro x hx hx₁
    have hxn : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.mp hx
    exact hcollar x ((norm_snd_le x).trans hxn)
      ⟨hx₁, ((norm_fst_le x).trans hxn).trans (by linarith)⟩
  have hB : IsClosed B :=
    (isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)
  have hSB : sphere (0 : Fin m → ℝ) 1 ⊆ B := fun u hu ↦ by
    rw [mem_sphere_zero_iff_norm] at hu
    exact ⟨by linarith, by linarith⟩
  have hBW : B ×ˢ {(0 : Fin k → ℝ)} ⊆ W := by
    rintro ⟨u, v⟩ ⟨hu, hv⟩
    obtain rfl : v = 0 := hv
    exact hcollar _ (by simp) hu
  -- Step 2: a cutoff `χ`, zero near `B ×ˢ {0}` and one off `W`.
  obtain ⟨χ, hχ0, hχ1, -⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed
    (I := 𝓘(ℝ, (Fin m → ℝ) × (Fin k → ℝ))) (n := ⊤) (hB.prod isClosed_singleton)
    hW.isClosed_compl (disjoint_compl_right_iff_subset.mpr hBW)
  obtain ⟨O, hO, hBO, hOχ⟩ := mem_nhdsSet_iff_exists.mp hχ0
  have hχW : ∀ x ∉ W, χ x = 1 := fun x hx ↦ hχ1.self_of_nhdsSet x hx
  -- The forms as maps into fixed spaces of alternating maps.
  set b : L → (Fin m → ℝ) × (Fin k → ℝ) → ((Fin m → ℝ) × (Fin k → ℝ)) [⋀^Fin 1]→L[ℝ] ℝ :=
    fun l ↦ (β l).val
  set c : L → (Fin m → ℝ) × (Fin k → ℝ) → ((Fin m → ℝ) × (Fin k → ℝ)) [⋀^Fin 2]→L[ℝ] ℝ :=
    fun l ↦ (τ l).val
  have hbc : ∀ l ∈ K, ∀ x ∈ W, extDeriv (b l) x = c l x := fun l hl x hx ↦ by
    have := hτβ l hl x hx
    rwa [mextDerivₗ_apply, mextDeriv_eq_extDeriv] at this
  -- The two-forms `τ'`, equal to `dβ` near `B ×ˢ {0}` and to `τ` off `W`.
  set τ' : L → SmoothTwoForm 𝓘(ℝ, (Fin m → ℝ) × (Fin k → ℝ)) ((Fin m → ℝ) × (Fin k → ℝ)) :=
    fun l ↦ mextDerivₗ _ 1 (β l) + SmoothForm.funSMulₗ χ (τ l - mextDerivₗ _ 1 (β l))
  have hτ' : IsSmoothFamily 𝓘(ℝ, L) τ' := hβ.mextDeriv.add ((hτ.sub hβ.mextDeriv).funSMul χ)
  set c' : L → (Fin m → ℝ) × (Fin k → ℝ) → ((Fin m → ℝ) × (Fin k → ℝ)) [⋀^Fin 2]→L[ℝ] ℝ :=
    fun l ↦ (τ' l).val
  have hτ'v : ∀ l x, c' l x = extDeriv (b l) x + χ x • (c l x - extDeriv (b l) x) :=
    fun l x ↦ by
      simp only [c', τ', Submodule.coe_add, Submodule.coe_sub, SmoothForm.coe_funSMulₗ,
        Pi.add_apply, Pi.sub_apply, mextDerivₗ_apply, mextDeriv_eq_extDeriv, b, c]
      -- The sides differ only in their instances: the left one reads the alternating maps on
      -- `TangentSpace 𝓘(ℝ, _) x`, which is the model space by definition.
      rfl
  -- The datum: `f p = β p.1` at `p.2`, and `G`, the formal primitive of `τ'`.
  set f : L × (Fin m → ℝ) × (Fin k → ℝ) → ((Fin m → ℝ) × (Fin k → ℝ)) [⋀^Fin 1]→L[ℝ] ℝ :=
    fun p ↦ b p.1 p.2
  set G : L × (Fin m → ℝ) × (Fin k → ℝ) →
      (Fin m → ℝ) × (Fin k → ℝ) →L[ℝ] ((Fin m → ℝ) × (Fin k → ℝ)) [⋀^Fin 1]→L[ℝ] ℝ :=
    fun p ↦ formalPrimitive (c' p.1) (b p.1) p.2 with hG_def
  have hf : ContDiff ℝ ∞ f :=
    contMDiff_iff_contDiff.mp (contMDiff_prod_modelWithCornersSelf_iff.mp hβ.contMDiff_val)
  have hG : ContDiff ℝ ∞ G := contMDiff_iff_contDiff.mp
    (contMDiff_prod_modelWithCornersSelf_iff.mp (contMDiff_formalPrimitive hτ' hβ))
  -- `G` is holonomic over `O`, and is the formal primitive of `τ` over `K`.
  have hUf : ∀ p ∈ univ ×ˢ O, fderiv ℝ (fun x ↦ f (p.1, x)) p.2 = G p := by
    rintro p ⟨-, hp⟩
    refine (formalPrimitive_eq_fderiv ?_).symm
    rw [hτ'v, hOχ hp, zero_smul, add_zero]
  have hGK : ∀ p : L × (Fin m → ℝ) × (Fin k → ℝ), p.1 ∈ K →
      G p = formalPrimitive (c p.1) (b p.1) p.2 := by
    intro p hp
    have : c' p.1 p.2 = c p.1 p.2 := by
      rw [hτ'v]
      by_cases hpW : p.2 ∈ W
      · rw [hbc p.1 hp p.2 hpW, sub_self, smul_zero, add_zero]
      · rw [hχW _ hpW, one_smul, add_sub_cancel]
    simp only [hG_def, formalPrimitive_def, this]
  -- Step 3: holonomic approximation with accuracy `r / 4` and width `η / 2`.
  obtain ⟨h, f', V, hfst, hf', ⟨C, -, hCQ, hCfix⟩, -, ⟨N, hN, hNfix⟩, -, hV, hQV, happrox⟩ :=
    exists_holonomic_approximation_family hk hf hG hK isClosed_empty hB hSB
      (isOpen_univ.prod hO) (prod_mono subset_rfl hBO) (by simp) hUf (ε := r / 4)
      (δ := η / 2) (by positivity) (by positivity)
  -- The family `β'` read off `f'`.
  have hf'l : ∀ l, ContDiff ℝ ∞ fun x ↦ f' (l, x) := fun l ↦
    hf'.comp (contDiff_const.prodMk contDiff_id)
  set β' : L → SmoothForm 𝓘(ℝ, (Fin m → ℝ) × (Fin k → ℝ)) ((Fin m → ℝ) × (Fin k → ℝ)) ℝ 1 :=
    fun l ↦ ⟨fun x ↦ f' (l, x), (isSmoothForm_modelSpace_iff.mpr (hf'l l)).mem_smoothBundleForms⟩
  have hBN : B ⊆ N := subset_of_mem_nhdsSet hN
  refine ⟨ε₀, hε₀pos, hε₀₁, hslab, h, β', V, hfst,
    IsSmoothFamily.of_contMDiff_val (contMDiff_prod_modelWithCornersSelf_iff.mpr
      (contMDiff_iff_contDiff.mpr hf')), hV, ?_, hQV, ?_⟩
  · -- Points moved, or where `β' ≠ β`, lie near the core with core coordinate off `B`.
    intro t p hp
    suffices (∀ t, h (t, p) = p) ∧ f' p = f p from ⟨this.1 t, this.2⟩
    by_cases hpC : p ∈ C
    · refine hNfix p (hBN ?_)
      obtain ⟨z, ⟨hz₁, hz₂⟩, hz⟩ := mem_thickening_iff.1 (hCQ p hpC)
      rw [mem_singleton_iff] at hz₂
      rw [Prod.dist_eq, max_lt_iff, hz₂, dist_zero_right] at hz
      have hz₁' : ‖z.1‖ ≤ 1 := mem_closedBall_zero_iff.mp hz₁
      have hu : ‖p.2.1‖ ≤ ‖z.1‖ + dist p.2.1 z.1 := by
        rw [dist_eq_norm]
        exact norm_le_norm_add_norm_sub' _ _ |>.trans (by rw [add_comm])
      refine ⟨?_, by linarith⟩
      rcases hp with hp | hp
      · linarith
      · rw [Prod.norm_def] at hp
        rcases le_max_iff.mp hp with hp | hp <;> linarith
    · exact hCfix p hpC
  · -- The estimate near the moved core.
    intro p hp hpK
    rw [mextDerivₗ_apply, mextDeriv_eq_extDeriv]
    have h₁ : ‖fderiv ℝ (fun x ↦ f' (p.1, x)) p.2 -
        formalPrimitive (c p.1) (b p.1) p.2‖ ≤ r / 4 := by
      rw [← hGK p hpK]
      exact (happrox p hp).2.le
    have h₂ := norm_extDeriv_sub_le_of_norm_fderiv_sub_formalPrimitive_le h₁
    exact h₂.trans_lt (by linarith)

end SymplecticGeometry

end
