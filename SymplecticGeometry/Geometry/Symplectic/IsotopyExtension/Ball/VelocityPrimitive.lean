/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.IsotopyExtension.Ball.Basic
public import SymplecticGeometry.Geometry.Symplectic.IsotopyExtension.Velocity
import SymplecticGeometry.Geometry.Symplectic.IsotopyExtension.Ball.Isotopy

/-!
# Primitives of the velocity forms of a family of ball isotopies

Let `G : [0, 1] × [0, 1] × StdSpace (Fin n) → M` be jointly smooth on `[0, 1]² × P`, for a
nonempty open convex set `P ⊆ B(ρ)`, and for each `t` let the maps `G (t, s, ·)`, `s ∈ [0, 1]`,
form a smooth family of symplectic balls of radius `ρ`
(`SymplecticGeometry.IsSymplecticBallFamily`). On `P`, each of these families is a symplectic
isotopy `k_t`
(`SymplecticGeometry.IsSymplecticBallFamily.exists_smoothIsotopy_isSymplectic`). This file gives
primitives `h ((t, s), ·)` on `P` of the velocity forms
`v ↦ σ (∂ₛ G (t, s, x), d (G (t, s, ·))_x v)` of all the `k_t` at once, smooth in both
parameters, and zero for each `t` at which `G` stands still
(`SymplecticGeometry.IsSymplecticBallFamily.exists_contMDiff_velocityForm_eq_mextDeriv`).

This is the general statement for families of symplectic isotopies of a convex set,
`SymplecticGeometry.exists_contMDiff_velocityForm_eq_mextDeriv`, applied to these `k_t`. It
follows the one-parameter case,
`SymplecticGeometry.IsSymplecticBallFamily.exists_hasHamiltonian_forall_apply_eq`.

## Main results

* `SymplecticGeometry.IsSymplecticBallFamily.exists_contMDiff_velocityForm_eq_mextDeriv`: smooth
  primitives of the velocity forms of a family of ball isotopies with a parameter.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §3.3.
-/

public section

noncomputable section

open Set Function Metric
open scoped ContDiff Manifold

namespace SymplecticGeometry

open TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

variable [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] {n : ℕ} {σ : SmoothTwoForm I M}

/-- **Primitives of the velocity forms of a family of ball isotopies.** Let `σ` be a closed
two-form on a Hausdorff boundaryless manifold `M` modelled on a finite-dimensional space, let
`0 < ρ`, and let `P ⊆ B(ρ)` be a nonempty open convex set. Let
`G : [0, 1] × [0, 1] × StdSpace (Fin n) → M` be jointly smooth on `[0, 1]² × P`, and for each
`t` let the maps `G (t, s, ·)`, `s ∈ [0, 1]`, form a smooth family of symplectic balls of radius
`ρ`. Then there are smooth isotopies `k_t` of `P` with `k_t (s, x) = G (t, s, x)`, and a jointly
smooth function `h` on `[0, 1]² × P` such that:
* for all `t` and `s`, `h ((t, s), ·)` is a primitive of the slice at time `s` of the velocity
  form of `k_t`, the one-form `v ↦ σ (∂ₛ G (t, s, x), d (G (t, s, ·))_x v)`;
* `h ((t, ·), ·) = 0` for every `t` such that `G (t, s, z) = G (t, 0, z)` for all `s` and
  `z ∈ P`. -/
theorem IsSymplecticBallFamily.exists_contMDiff_velocityForm_eq_mextDeriv (hσ : σ.IsClosed)
    {ρ : ℝ} (hρ : 0 < ρ) {P : TopologicalSpace.Opens (StdSpace (Fin n))}
    (hPc : Convex ℝ (P : Set (StdSpace (Fin n)))) (hPne : (P : Set (StdSpace (Fin n))).Nonempty)
    (hPρ : (P : Set (StdSpace (Fin n))) ⊆ closedBall 0 ρ)
    {G : unitInterval × unitInterval × StdSpace (Fin n) → M}
    (hG : ContMDiffOn ((𝓡∂ 1).prod ((𝓡∂ 1).prod 𝓘(ℝ, StdSpace (Fin n)))) I ∞ G
      (univ ×ˢ (univ ×ˢ P)))
    (he : ∀ t, IsSymplecticBallFamily σ ρ fun p ↦ G (t, p.1, p.2)) :
    ∃ (f₀ f₁ : unitInterval → C^∞⟮𝓘(ℝ, StdSpace (Fin n)), P; I, M⟯)
      (k : ∀ t, SmoothIsotopy (f₀ t) (f₁ t)) (h : (unitInterval × unitInterval) × P → ℝ),
      (∀ t p, k t p = G (t, p.1, p.2)) ∧
      ContMDiff (((𝓡∂ 1).prod (𝓡∂ 1)).prod 𝓘(ℝ, StdSpace (Fin n))) 𝓘(ℝ) ∞ h ∧
      (∀ t s, (SmoothForm.mpullback (Prod.mk s) (contMDiff_const.prodMk contMDiff_id)
          ((k t).velocityForm σ)).val =
        mextDeriv (RoughForm.ofFunction 𝓘(ℝ, StdSpace (Fin n)) fun x ↦ h ((t, s), x))) ∧
      ∀ t, (∀ s, ∀ z ∈ P, G (t, s, z) = G (t, 0, z)) → ∀ s x, h ((t, s), x) = 0 := by
  choose f₀ f₁ k hk hks using fun t ↦ (he t).exists_smoothIsotopy_isSymplectic hρ hPρ
  obtain ⟨h, hh, hdh, hzero⟩ :=
    SymplecticGeometry.exists_contMDiff_velocityForm_eq_mextDeriv hσ hPc hPne
    (hG.comp_contMDiff ((contMDiff_fst.comp contMDiff_fst).prodMk
      ((contMDiff_snd.comp contMDiff_fst).prodMk (contMDiff_subtypeVal.comp contMDiff_snd)))
      fun q ↦ ⟨mem_univ _, mem_univ _, q.2.property⟩) k (fun t p ↦ hk t p) hks
  exact ⟨f₀, f₁, k, h, hk, hh, hdh, fun t ht ↦ hzero t fun s x ↦ ht s x x.property⟩

end SymplecticGeometry

end
