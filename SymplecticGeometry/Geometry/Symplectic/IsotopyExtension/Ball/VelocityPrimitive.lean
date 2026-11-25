/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.IsotopyExtension.Ball.Basic
public import SymplecticGeometry.Geometry.Symplectic.IsotopyExtension.Velocity
import SymplecticGeometry.Geometry.Symplectic.IsotopyExtension.Ball.Isotopy
import SymplecticGeometry.Geometry.Symplectic.IsotopyExtension.VelocityFamily
import SymplecticGeometry.Geometry.Manifold.DeRham.FamilyPrimitive

/-!
# Primitives of the velocity forms of a family of ball isotopies

Let `G : [0, 1] × [0, 1] × StdSpace (Fin n) → M` be jointly smooth on `[0, 1]² × P`, for a
nonempty open convex set `P ⊆ B(ρ)`, and for each `t` let `s ↦ G (t, s, ·)` be a smooth family of
symplectic embeddings of `B(ρ)` (`SymplecticGeometry.IsSymplecticBallFamily`). On `P`, each of
these families is a symplectic isotopy `k_t`
(`SymplecticGeometry.IsSymplecticBallFamily.exists_smoothIsotopy_isSymplectic`). This file gives
primitives `h ((t, s), ·)` on `P` of the velocity forms
`v ↦ σ (∂ₛ G (t, s, x), d (G (t, s, ·))_x v)` of all the `k_t` at once, smooth in both
parameters, and zero for each `t` at which `G` stands still
(`SymplecticGeometry.IsSymplecticBallFamily.exists_contMDiff_velocityForm_eq_mextDeriv`).

The proof is that of the one-parameter case,
`SymplecticGeometry.IsSymplecticBallFamily.exists_hasHamiltonian_forall_apply_eq`, in which the
velocity forms of one isotopy are closed
(`TauCeti.SmoothIsotopy.IsSymplectic.mextDeriv_mpullback_prodMk_velocityForm`) and have smooth
primitives on the contractible set `P`
(`IsSmoothlyContractible.exists_contMDiff_mextDeriv_eq_of_forall_mem_closedForms`). With the
parameter `t`, the forms are a smooth family over `(t, s)`
(`SymplecticGeometry.isSmoothFamily_velocityForm`). The primitives are then normalized to vanish
at a point of `P`. Where `G (t, ·, ·)` stands still, the velocity forms vanish, so the normalized
primitives are locally constant, hence zero on the connected set `P`.

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
`G : [0, 1] × [0, 1] × StdSpace (Fin n) → M` be jointly smooth on
`[0, 1]² × P`, and for each `t` let `s ↦ G (t, s, ·)` be a smooth family of symplectic embeddings of
`B(ρ)`. Then there are smooth isotopies `k_t` of `P` with `k_t (s, x) = G (t, s, x)`, and a
jointly smooth function `h` on `[0, 1]² × P` such that:
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
  -- The velocity forms are the slices of one smooth form on `[0, 1]² × P`, and are closed.
  have hĜ : ContMDiff (((𝓡∂ 1).prod (𝓡∂ 1)).prod 𝓘(ℝ, StdSpace (Fin n))) I ∞
      fun q : (unitInterval × unitInterval) × P ↦ G (q.1.1, q.1.2, q.2) :=
    hG.comp_contMDiff ((contMDiff_fst.comp contMDiff_fst).prodMk
      ((contMDiff_snd.comp contMDiff_fst).prodMk (contMDiff_subtypeVal.comp contMDiff_snd)))
      fun q ↦ ⟨mem_univ _, mem_univ _, q.2.property⟩
  have hcl (q : unitInterval × unitInterval) :
      SmoothForm.mpullback (Prod.mk q.2) (contMDiff_const.prodMk contMDiff_id)
        ((k q.1).velocityForm σ) ∈ closedForms 𝓘(ℝ, StdSpace (Fin n)) P 1 :=
    (mem_closedForms_iff_mextDerivₗ_eq_zero _ _).2 <| Subtype.ext <| by
      rw [mextDerivₗ_apply, ZeroMemClass.coe_zero]
      exact (hks q.1).mextDeriv_mpullback_prodMk_velocityForm hσ q.2
  obtain ⟨h, hh, hdh⟩ := (Convex.isSmoothlyContractible hPc hPne
    ).exists_contMDiff_mextDeriv_eq_of_forall_mem_closedForms
    (isSmoothFamily_velocityForm σ hĜ k fun t p ↦ hk t p) hcl
  -- Normalize the primitives to vanish at a point `x₀` of `P`.
  obtain ⟨x₀, hx₀⟩ := hPne
  have hd (t s : unitInterval) :
      mextDeriv (RoughForm.ofFunction 𝓘(ℝ, StdSpace (Fin n))
        fun x ↦ h ((t, s), x) - h ((t, s), ⟨x₀, hx₀⟩)) =
      mextDeriv (RoughForm.ofFunction 𝓘(ℝ, StdSpace (Fin n)) fun x ↦ h ((t, s), x)) :=
    funext fun x ↦ mextDeriv_ofFunction_eq_of_eventuallyEq_add_const
      (Filter.Eventually.of_forall fun y ↦ sub_eq_add_neg _ _)
  refine ⟨f₀, f₁, k, fun q ↦ h q - h (q.1, ⟨x₀, hx₀⟩), hk,
    hh.sub (hh.comp (contMDiff_fst.prodMk contMDiff_const)),
    fun t s ↦ ((hd t s).trans (hdh (t, s))).symm, fun t ht s x ↦ sub_eq_zero.2 ?_⟩
  -- Where `G (t, ·, ·)` does not move, the velocity forms vanish, so `h ((t, s), ·)` is constant.
  have hzero : mextDeriv (RoughForm.ofFunction 𝓘(ℝ, StdSpace (Fin n))
      fun x ↦ h ((t, s), x)) = 0 := by
    rw [hdh (t, s)]
    dsimp only
    refine funext fun y ↦ ContinuousAlternatingMap.ext fun w ↦ ?_
    have hw : w = ![w 0] := by
      ext i
      fin_cases i
      rfl
    have hconst : (fun s₁ ↦ k t (s₁, y)) = fun _ ↦ k t (0, y) :=
      funext fun s₁ ↦ by rw [hk, hk, ht s₁ y y.property]
    rw [hw]
    refine (SmoothIsotopy.mpullback_prodMk_velocityForm σ (k t) s y (w 0)).trans ?_
    rw [hconst, mfderiv_const, Pi.zero_apply, ContinuousAlternatingMap.coe_zero, Pi.zero_apply]
    exact ContinuousAlternatingMap.map_coord_zero _ 0 rfl
  have : PreconnectedSpace P := isPreconnected_iff_preconnectedSpace.1 hPc.isPreconnected
  exact ((mextDeriv_ofFunction_eq_zero_iff
    ((hh.comp (contMDiff_const.prodMk contMDiff_id)).mdifferentiable (by simp))).1 hzero
    ).apply_eq_of_preconnectedSpace _ _

end SymplecticGeometry

end
