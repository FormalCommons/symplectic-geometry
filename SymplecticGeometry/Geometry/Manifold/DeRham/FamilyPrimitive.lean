/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.Basic
public import SymplecticGeometry.Geometry.Manifold.DeRham.GoodCover.Basic
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.SmoothFamily.Basic
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.SmoothFamily.Poincare
import TauCeti.Geometry.Manifold.DifferentialForm.ParametricPrimitive
import SymplecticGeometry.Geometry.Manifold.MFDeriv.Prod

/-!
# Smooth primitives of smooth families of one-forms

Let `α_t`, `t ∈ N`, be a smooth family of one-forms on a manifold `M` over a parameter manifold
`N` (`SymplecticGeometry.IsSmoothFamily`). If every `α_t` is exact, then the primitives can be
chosen to depend smoothly on `t`: there is a smooth `f : N × M → ℝ` with `d (f (t, ·)) = α_t` for
every `t`. Neither compactness of `M` nor finite dimension is needed.

The file has two results.

* *Smoothly contractible manifolds.* Let `M` be smoothly contractible, through
  `G : M × [0, 1] → M` with `G (·, 0) = c` and `G (·, 1) = id`. By the parametric Poincaré lemma
  `SymplecticGeometry.IsSmoothlyContractible.exists_isSmoothFamily_mextDerivₗ_eq`, the
  primitives `h (G^* α_t)`, the homotopy operator after pullback along `G`, form a smooth
  family of `0`-forms over `N`, so they are the slices `f (t, ·)` of a smooth function `f` on
  `N × M`, explicitly `f (t, x) = ∫₀¹ α_t (G (x, s)) (∂ₛ G (x, s)) ds`. Here the forms need only
  be closed.
* *Exact forms on any manifold.* This is Tau Ceti's
  `TauCeti.exists_contMDiff_mvfderiv_eq_of_forall_exists`, which needs no connectedness of `M`,
  applied to the family pulled back to `M × N` by the swap of the factors: its slices are the
  differentials of chosen primitives `g_t` of the `α_t`.

## Main results

* `IsSmoothlyContractible.exists_contMDiff_mextDeriv_eq_of_forall_mem_closedForms`: on a smoothly
  contractible manifold, a smooth family of closed one-forms has a jointly smooth family of
  primitives (the parametric Poincaré lemma in degree one).
* `exists_contMDiff_mextDeriv_eq_of_forall_mem_exactForms`: on any manifold, a smooth family of
  exact one-forms has a jointly smooth family of primitives.

## References

* [R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982], §4 (the
  homotopy operator and the Poincaré lemma).
* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §3.1
  (the Hamiltonian of an isotopy, a smooth family of primitives of its velocity forms).
-/

public section

open Set TopologicalSpace TauCeti
open scoped Manifold ContDiff Topology

namespace SymplecticGeometry

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
  {EN HN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
  {K : ModelWithCorners ℝ EN HN} {N : Type*} [TopologicalSpace N] [ChartedSpace HN N]
  [IsManifold K ∞ N]

/-- **The parametric Poincaré lemma in degree one.** On a smoothly contractible manifold `M`, a
smooth family `α_t`, `t ∈ N`, of closed one-forms has a jointly smooth family of primitives: there
is a smooth `f : N × M → ℝ` with `d (f (t, ·)) = α_t` for every `t`. -/
theorem IsSmoothlyContractible.exists_contMDiff_mextDeriv_eq_of_forall_mem_closedForms
    (hM : IsSmoothlyContractible I M) {α : N → SmoothForm I M ℝ 1} (hα : IsSmoothFamily K α)
    (hcl : ∀ t, α t ∈ closedForms I M 1) :
    ∃ f : N × M → ℝ, ContMDiff (K.prod I) 𝓘(ℝ) ∞ f ∧
      ∀ t, mextDeriv (RoughForm.ofFunction I fun x ↦ f (t, x)) = (α t : RoughForm I M ℝ 1) := by
  -- A smooth family `β_t` of primitives, as `0`-forms: the slices of `Ω`.
  obtain ⟨β, hβ, hdβ⟩ := hM.exists_isSmoothFamily_mextDerivₗ_eq hα
    fun t ↦ (mem_closedForms_iff_mextDerivₗ_eq_zero I _).1 (hcl t)
  obtain ⟨Ω, hΩ⟩ := isSmoothFamily_def.1 hβ
  refine ⟨fun p ↦ Ω.val p 0, ?_, fun t ↦ ?_⟩
  · exact Ω.contMDiff_apply_zero
  have hslice : RoughForm.ofFunction I (fun x ↦ Ω.val (t, x) 0) = (β t).val := by
    rw [← hΩ t, SmoothForm.coe_mpullback]
    conv_rhs => rw [RoughForm.eq_ofFunction Ω.val, mpullback_ofFunction]
    -- Both sides are the `0`-form of `x ↦ Ω (t, x)`, written with and without `∘`.
    rfl
  rw [hslice, ← mextDerivₗ_apply, hdβ t]

/-- **Smooth primitives of a smooth family of exact one-forms.** On any manifold `M`, a smooth
family `α_t`, `t ∈ N`, of exact one-forms has a jointly smooth family of primitives: there is a
smooth `f : N × M → ℝ` with `d (f (t, ·)) = α_t` for every `t`. -/
theorem exists_contMDiff_mextDeriv_eq_of_forall_mem_exactForms {α : N → SmoothForm I M ℝ 1}
    (hα : IsSmoothFamily K α) (hex : ∀ t, α t ∈ exactForms I M 1) :
    ∃ f : N × M → ℝ, ContMDiff (K.prod I) 𝓘(ℝ) ∞ f ∧
      ∀ t, mextDeriv (RoughForm.ofFunction I fun x ↦ f (t, x)) = (α t : RoughForm I M ℝ 1) := by
  rcases isEmpty_or_nonempty M with hM | ⟨⟨x₀⟩⟩
  · exact ⟨0, contMDiff_const, fun t ↦ funext isEmptyElim⟩
  choose g hg hdg using fun t ↦ exists_contMDiff_mextDeriv_eq_of_mem_exactForms I (hex t)
  obtain ⟨Ω, hΩ⟩ := isSmoothFamily_def.1 hα
  have hψ : ContMDiff (I.prod K) (K.prod I) ∞ fun q : M × N ↦ (q.2, q.1) :=
    contMDiff_snd.prodMk contMDiff_fst
  -- The slices of the pullback `B` of `Ω` to `M × N` are the differentials of the `g_t`.
  have hB (t : N) (z : M) (v : E) :
      mvfderiv I (g t) z v = (SmoothForm.mpullback _ hψ Ω).val (z, t) ![(v, (0 : EN))] := by
    have h1 : mvfderiv I (g t) z v = mextDeriv (RoughForm.ofFunction I (g t)) z ![v] :=
      ((mextDeriv_ofFunction_apply _ z v).trans (mvfderiv_apply_eq_mfderiv_apply ..).symm).symm
    rw [h1, hdg t, ← hΩ t]
    -- The vectors `v` and `(v, 0)` are stated in the model spaces, so the two evaluation lemmas
    -- are applied by unification rather than by `rw`.
    refine (SmoothForm.mpullback_apply_one _ _ Ω z v).trans
      (Eq.trans ?_ (SmoothForm.mpullback_apply_one _ hψ Ω (z, t) (v, 0)).symm)
    congr 2
    exact (MDifferentiableAt.mfderiv_uncurry_apply_mk_zero (f := fun z t ↦ (t, z))
      (hψ.mdifferentiable (by simp) (z, t)) v).symm
  obtain ⟨F, hF, -, hFd⟩ := exists_contMDiff_mvfderiv_eq_of_forall_exists (r := ⊤)
    (SmoothForm.mpullback _ hψ Ω).isSmoothForm
    (fun t ↦ ⟨_, (hg t).mdifferentiable (by simp), hB t⟩) x₀
  refine ⟨fun p ↦ F (p.2, p.1), hF.comp (contMDiff_snd.prodMk contMDiff_fst), fun t ↦ ?_⟩
  rw [← hdg t]
  funext z
  rw [mextDeriv_ofFunction, mextDeriv_ofFunction]
  congr 1
  ext v
  exact (hFd t z v).trans (hB t z v).symm

end SymplecticGeometry

end
