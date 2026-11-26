/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.DeRham.SmoothFamily.OpenSubset
public import SymplecticGeometry.Geometry.Symplectic.HPrinciple.AttachingCollar

/-!
# Smooth families of primitives near the attaching faces of a handle core

On the handle core `D = (ι → ℝ) × (κ → ℝ)`, with sup norms, the attaching faces are
`A = sphere 0 1 ×ˢ closedBall 0 1`, and `attachingCollar ι κ ε` is their product collar, the
open set of the `(u, v)` with `|‖u‖ - 1| < ε` and `‖v‖ < 1 + ε`. For `ε ≤ 1` it is the union of
the `2 * card ι` convex slabs on which moreover `1 - ε < u i` or `1 - ε < -u i`, so it has a
finite good cover (`hasFiniteGoodCover_attachingCollar`, by `hasFiniteGoodCover_of_convex`).

So a smooth family `τ` of two-forms on `D` whose restriction to the collar is exact for the
parameters in a set `K` has a smooth family `β` of primitives near `A`: an open `W ⊇ A` with
`dβ t = τ t` on `W` for `t ∈ K`
(`exists_isSmoothFamily_mextDerivₗ_eq_near_sphere_prod_closedBall`, by
`exists_isSmoothFamily_mextDerivₗ_eq_on_of_hasFiniteGoodCover`). These are the primitives near
the attaching faces that McDuff and Salamon's handle-core lemma, Lemma 7.3.2, starts from.

## Main results

* `SymplecticGeometry.hasFiniteGoodCover_attachingCollar`
* `SymplecticGeometry.exists_isSmoothFamily_mextDerivₗ_eq_near_sphere_prod_closedBall`

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], proof of
  Lemma 7.3.2.
-/

public section

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace SymplecticGeometry

open TauCeti

variable {ι κ : Type*} [Fintype ι] [Fintype κ] {ε : ℝ}

/-- For `q = (i, s)`, the slab of the product collar on which moreover `1 - ε < u i` if `s` is
`true`, and `1 - ε < -u i` if not. -/
private def collarSlab (q : ι × Bool) : Opens ((ι → ℝ) × (κ → ℝ)) :=
  ⟨{p | ‖p.1‖ < 1 + ε ∧ 1 - ε < (if q.2 then p.1 q.1 else -p.1 q.1) ∧ ‖p.2‖ < 1 + ε},
    by
      simp only [ofPred_and]
      refine (isOpen_lt (by fun_prop) (by fun_prop)).inter
        ((isOpen_lt (by fun_prop) ?_).inter (isOpen_lt (by fun_prop) (by fun_prop)))
      cases q.2 <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> fun_prop⟩

/-- For `ε ≤ 1` the product collar is the union of its slabs. -/
private theorem iSup_collarSlab (hε : ε ≤ 1) :
    ⨆ q, collarSlab (κ := κ) (ε := ε) q = attachingCollar ι κ ε := by
  ext ⟨u, v⟩
  simp only [collarSlab, Opens.coe_iSup, Opens.coe_mk, mem_iUnion, SetLike.mem_coe,
    mem_attachingCollar_iff, Prod.exists, Bool.exists_bool, Bool.false_eq_true, ite_false,
    ite_true, abs_sub_lt_iff]
  have hlt : 1 - ε < ‖u‖ ↔ ∃ i, 1 - ε < |u i| := by
    rw [← not_iff_not, not_lt, not_exists]
    simp only [not_lt]
    exact pi_norm_le_iff_of_nonneg (by linarith)
  constructor
  · rintro ⟨i, (⟨h₁, h₂, h₃⟩ | ⟨h₁, h₂, h₃⟩)⟩
    · exact ⟨⟨by linarith, by linarith [hlt.mpr ⟨i, h₂.trans_le (neg_le_abs _)⟩]⟩, h₃⟩
    · exact ⟨⟨by linarith, by linarith [hlt.mpr ⟨i, h₂.trans_le (le_abs_self _)⟩]⟩, h₃⟩
  · rintro ⟨⟨h₁, h₂⟩, h₃⟩
    obtain ⟨i, hi⟩ := hlt.mp (by linarith)
    rcases lt_abs.mp hi with hi | hi
    · exact ⟨i, Or.inr ⟨by linarith, hi, h₃⟩⟩
    · exact ⟨i, Or.inl ⟨by linarith, hi, h₃⟩⟩

/-- The slabs of the product collar are convex. -/
private theorem convex_collarSlab (q : ι × Bool) :
    Convex ℝ (collarSlab (κ := κ) (ε := ε) q : Set ((ι → ℝ) × (κ → ℝ))) := by
  have hfst : Convex ℝ {p : (ι → ℝ) × (κ → ℝ) | ‖p.1‖ < 1 + ε} := by
    simpa [Set.preimage, mem_ball_zero_iff] using
      (convex_ball (0 : ι → ℝ) (1 + ε)).linear_preimage (LinearMap.fst ℝ _ (κ → ℝ))
  have hsnd : Convex ℝ {p : (ι → ℝ) × (κ → ℝ) | ‖p.2‖ < 1 + ε} := by
    simpa [Set.preimage, mem_ball_zero_iff] using
      (convex_ball (0 : κ → ℝ) (1 + ε)).linear_preimage (LinearMap.snd ℝ (ι → ℝ) _)
  have hlin : IsLinearMap ℝ fun p : (ι → ℝ) × (κ → ℝ) ↦ p.1 q.1 :=
    (LinearMap.proj q.1 ∘ₗ LinearMap.fst ℝ _ (κ → ℝ)).isLinear
  have hmid : Convex ℝ {p : (ι → ℝ) × (κ → ℝ) |
      1 - ε < (if q.2 then p.1 q.1 else -p.1 q.1)} := by
    cases q.2
    · simpa using convex_halfSpace_gt
        (-(LinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) q.1 ∘ₗ
          LinearMap.fst ℝ _ (κ → ℝ))).isLinear (1 - ε)
    · simpa using convex_halfSpace_gt hlin (1 - ε)
  simpa only [collarSlab, Opens.coe_mk, ofPred_and] using hfst.inter (hmid.inter hsnd)

/-- For `ε ≤ 1` the product collar of the attaching faces has a finite good cover, by
`2 * card ι` convex slabs. -/
theorem hasFiniteGoodCover_attachingCollar (hε : ε ≤ 1) :
    HasFiniteGoodCover 𝓘(ℝ, (ι → ℝ) × (κ → ℝ)) (attachingCollar ι κ ε) :=
  hasFiniteGoodCover_of_convex convex_collarSlab (iSup_collarSlab hε)

variable {EN HN N : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  [TopologicalSpace HN] [TopologicalSpace N] [ChartedSpace HN N]
  {J : ModelWithCorners ℝ EN HN} [IsManifold J ∞ N]

/-- **Smooth primitives near the attaching faces of a handle core.** On `D = (ι → ℝ) × (κ → ℝ)`
with sup norms, let `τ` be a smooth family of two-forms over a manifold `N` whose restriction to
the product collar `attachingCollar ι κ ε`, `0 < ε ≤ 1`, is exact for every parameter in `K`. Then
there are a smooth family `β` of one-forms on `D` and an open set `W` containing the attaching
faces `sphere 0 1 ×ˢ closedBall 0 1` with `dβ t = τ t` on `W` for every `t ∈ K`. -/
theorem exists_isSmoothFamily_mextDerivₗ_eq_near_sphere_prod_closedBall (hε₀ : 0 < ε)
    (hε₁ : ε ≤ 1)
    {τ : N → SmoothTwoForm 𝓘(ℝ, (ι → ℝ) × (κ → ℝ)) ((ι → ℝ) × (κ → ℝ))}
    (hτ : IsSmoothFamily J τ) {K : Set N}
    (hK : ∀ t ∈ K, SmoothForm.mpullback (Subtype.val : attachingCollar ι κ ε → _)
      contMDiff_subtypeVal (τ t) ∈
        exactForms 𝓘(ℝ, (ι → ℝ) × (κ → ℝ)) (attachingCollar ι κ ε) 2) :
    ∃ β : N → SmoothForm 𝓘(ℝ, (ι → ℝ) × (κ → ℝ)) ((ι → ℝ) × (κ → ℝ)) ℝ 1,
      IsSmoothFamily J β ∧ ∃ W : Set ((ι → ℝ) × (κ → ℝ)), IsOpen W ∧
        Metric.sphere (0 : ι → ℝ) 1 ×ˢ Metric.closedBall (0 : κ → ℝ) 1 ⊆ W ∧
        ∀ t ∈ K, ∀ x ∈ W,
          (mextDerivₗ 𝓘(ℝ, (ι → ℝ) × (κ → ℝ)) 1 (β t)).val x = (τ t).val x :=
  exists_isSmoothFamily_mextDerivₗ_eq_on_of_hasFiniteGoodCover
    (hasFiniteGoodCover_attachingCollar hε₁)
    ((isCompact_sphere (0 : ι → ℝ) 1).prod (isCompact_closedBall (0 : κ → ℝ) 1))
    (sphere_prod_closedBall_subset_attachingCollar hε₀) hτ hK

end SymplecticGeometry

end
