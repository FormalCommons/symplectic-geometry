/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Group
public import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Support, fixed points and displacement of products and conjugates of diffeotopies

For Tau Ceti's diffeotopies `TauCeti.Diffeotopy`, this file records how three properties behave
under the pointwise product `Ψ * Φ` of `TauCeti.Diffeotopy.instGroup`, whose value at `(t, x)`
is `Ψ (t, Φ (t, x))`, and under the conjugation `Ψ.transDiffeomorph f` by a diffeomorphism `f`,
whose value at `(t, y)` is `f (Ψ (t, f⁻¹ y))`:

* fixed points: a point fixed at time `t` by `Φ` and by `Ψ` is fixed by `Ψ * Φ`, and
  `Ψ.transDiffeomorph f` fixes `y` at time `t` exactly when `Ψ` fixes `f⁻¹ y`; hence a set
  fixed at every time by `Φ` and by `Ψ` is fixed by `Ψ * Φ`, and the image `f '' W` of a set `W`
  fixed by `Ψ` is fixed by `Ψ.transDiffeomorph f`;
* the support: if `Φ` fixes every point outside `C₁` and `Ψ` every point outside `C₂`, then
  `Ψ * Φ` fixes every point outside `C₁ ∪ C₂`, and if `Ψ` fixes every point outside `C`, then
  `Ψ.transDiffeomorph f` fixes every point outside `f '' C`;
* on a pseudo-metric space, the displacement `dist (Φ (t, x)) x`: displacements add under the
  product, by the triangle inequality, and are multiplied by at most `L` under conjugation by an
  `L`-Lipschitz diffeomorphism.

The last results are about the product `Ψ.transDiffeomorph f * Φ`, which runs `Φ` and then `Ψ`
conjugated by `f`. For any `f`, it is the identity outside `C₁ ∪ f '' C₂`, and it moves points
by less than `δ₁ + L * δ₂` when `f` is `L`-Lipschitz. For `f = Φ.final`, its final map is
`Φ.final * Ψ.final`, and it fixes at every time each point that both `Φ` and `Ψ` fix at every
time.

## Main results

* `TauCeti.Diffeotopy.mul_apply_eq_self`,
  `TauCeti.Diffeotopy.transDiffeomorph_apply_eq_self_iff`: fixed points at one time.
* `TauCeti.Diffeotopy.mul_apply_eq_self_of_mem`,
  `TauCeti.Diffeotopy.transDiffeomorph_apply_eq_self_of_mem_image`: fixed sets.
* `TauCeti.Diffeotopy.mul_apply_eq_self_of_notMem_union`,
  `TauCeti.Diffeotopy.transDiffeomorph_apply_eq_self_of_notMem_image`: supports.
* `TauCeti.Diffeotopy.dist_mul_apply_le`, `TauCeti.Diffeotopy.dist_mul_apply_lt_add`: the
  displacement of a product.
* `TauCeti.Diffeotopy.dist_transDiffeomorph_apply_le`,
  `TauCeti.Diffeotopy.dist_transDiffeomorph_apply_le_mul`: the displacement of a conjugate.
* `TauCeti.Diffeotopy.final_transDiffeomorph_final_mul`,
  `TauCeti.Diffeotopy.image_transDiffeomorph_final_mul_apply_one_subset`: the final map of
  `Ψ.transDiffeomorph Φ.final * Φ`.
* `TauCeti.Diffeotopy.transDiffeomorph_mul_apply_eq_self_of_notMem_union_image`,
  `TauCeti.Diffeotopy.transDiffeomorph_final_mul_apply_eq_self_of_mem_inter`,
  `TauCeti.Diffeotopy.exists_mem_nhdsSet_transDiffeomorph_final_mul_apply_eq_self`,
  `TauCeti.Diffeotopy.dist_transDiffeomorph_mul_apply_lt`: support, fixed sets and displacement
  of `Ψ.transDiffeomorph f * Φ`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], third
  edition, §10.2 (the pointwise product of isotopies).
-/

public section

open Set unitInterval
open scoped Manifold ContDiff NNReal Topology

namespace TauCeti.Diffeotopy

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {J : ModelWithCorners ℝ E H} {n : ℕ∞ω}

section Support

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {P : Type*} [TopologicalSpace P] [ChartedSpace H P]

/-- A point fixed at time `t` by two diffeotopies is fixed at time `t` by their product. -/
theorem mul_apply_eq_self {Φ Ψ : Diffeotopy J n M} {t : I} {x : M} (hΦ : Φ (t, x) = x)
    (hΨ : Ψ (t, x) = x) : (Ψ * Φ) (t, x) = x := by
  rw [mul_apply, hΦ, hΨ]

/-- The conjugate of `Ψ` by a diffeomorphism `f` fixes `y` at time `t` exactly when `Ψ` fixes
`f⁻¹ y` at time `t`. -/
theorem transDiffeomorph_apply_eq_self_iff {Ψ : Diffeotopy J n M} {f : M ≃ₘ^n⟮J, J⟯ P} {t : I}
    {y : P} : Ψ.transDiffeomorph f (t, y) = y ↔ Ψ (t, f.symm y) = f.symm y := by
  rw [transDiffeomorph_apply, ← f.toEquiv.apply_eq_iff_eq]
  simp

/-- If two diffeotopies fix every point of `W` at every time, so does their product. -/
theorem mul_apply_eq_self_of_mem {Φ Ψ : Diffeotopy J n M} {W : Set M}
    (hΦ : ∀ t, ∀ x ∈ W, Φ (t, x) = x) (hΨ : ∀ t, ∀ x ∈ W, Ψ (t, x) = x) :
    ∀ t, ∀ x ∈ W, (Ψ * Φ) (t, x) = x := fun t x hx ↦
  mul_apply_eq_self (hΦ t x hx) (hΨ t x hx)

/-- If `Φ` fixes every point outside `C₁` and `Ψ` every point outside `C₂`, at every time, then
`Ψ * Φ` fixes every point outside `C₁ ∪ C₂` at every time. -/
theorem mul_apply_eq_self_of_notMem_union {Φ Ψ : Diffeotopy J n M} {C₁ C₂ : Set M}
    (hΦ : ∀ t, ∀ x ∉ C₁, Φ (t, x) = x) (hΨ : ∀ t, ∀ x ∉ C₂, Ψ (t, x) = x) :
    ∀ t, ∀ x ∉ C₁ ∪ C₂, (Ψ * Φ) (t, x) = x := fun t x hx ↦
  mul_apply_eq_self (hΦ t x fun h ↦ hx (.inl h)) (hΨ t x fun h ↦ hx (.inr h))

/-- If `Ψ` fixes every point of `W` at every time, then its conjugate by a diffeomorphism `f`
fixes every point of `f '' W` at every time. -/
theorem transDiffeomorph_apply_eq_self_of_mem_image {Ψ : Diffeotopy J n M}
    (f : M ≃ₘ^n⟮J, J⟯ P) {W : Set M} (hΨ : ∀ t, ∀ x ∈ W, Ψ (t, x) = x) :
    ∀ t, ∀ y ∈ f '' W, Ψ.transDiffeomorph f (t, y) = y := by
  rintro t _ ⟨x, hx, rfl⟩
  rw [transDiffeomorph_apply_eq_self_iff, Diffeomorph.symm_apply_apply]
  exact hΨ t x hx

/-- If `Ψ` fixes every point outside `C` at every time, then its conjugate by a diffeomorphism
`f` fixes every point outside `f '' C` at every time. -/
theorem transDiffeomorph_apply_eq_self_of_notMem_image {Ψ : Diffeotopy J n M}
    (f : M ≃ₘ^n⟮J, J⟯ P) {C : Set M} (hΨ : ∀ t, ∀ x ∉ C, Ψ (t, x) = x) :
    ∀ t, ∀ y ∉ f '' C, Ψ.transDiffeomorph f (t, y) = y := fun t y hy ↦
  transDiffeomorph_apply_eq_self_iff.2 <| hΨ t _ fun h ↦ hy ⟨_, h, f.apply_symm_apply y⟩

/-- If `Φ` fixes every point outside `C₁` and `Ψ` every point outside `C₂`, at every time, then
the product `Ψ.transDiffeomorph f * Φ` of `Φ` with the conjugate of `Ψ` by a diffeomorphism `f`
fixes every point outside `C₁ ∪ f '' C₂` at every time. -/
theorem transDiffeomorph_mul_apply_eq_self_of_notMem_union_image {Φ Ψ : Diffeotopy J n M}
    (f : M ≃ₘ^n⟮J, J⟯ M) {C₁ C₂ : Set M} (hΦ : ∀ t, ∀ x ∉ C₁, Φ (t, x) = x)
    (hΨ : ∀ t, ∀ x ∉ C₂, Ψ (t, x) = x) :
    ∀ t, ∀ x ∉ C₁ ∪ f '' C₂, (Ψ.transDiffeomorph f * Φ) (t, x) = x :=
  mul_apply_eq_self_of_notMem_union hΦ (transDiffeomorph_apply_eq_self_of_notMem_image f hΨ)

/-- The final map of the product `Ψ.transDiffeomorph Φ.final * Φ`, which runs `Φ` and then `Ψ`
conjugated by the final map of `Φ`, is `Φ.final * Ψ.final`. -/
theorem final_transDiffeomorph_final_mul (Φ Ψ : Diffeotopy J n M) :
    (Ψ.transDiffeomorph Φ.final * Φ).final = Φ.final * Ψ.final := by
  rw [final_mul, final_transDiffeomorph_eq_mul_mul_inv, inv_mul_cancel_right]

/-- If the final map of `Ψ` sends `S` into `V`, then the final map of the product
`Ψ.transDiffeomorph Φ.final * Φ` sends `S` into `Φ.final '' V`. -/
theorem image_transDiffeomorph_final_mul_apply_one_subset {Φ Ψ : Diffeotopy J n M}
    {S V : Set M} (hΨ : (fun x ↦ Ψ (1, x)) '' S ⊆ V) :
    (fun x ↦ (Ψ.transDiffeomorph Φ.final * Φ) (1, x)) '' S ⊆ Φ.final '' V := by
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨Ψ (1, x), hΨ ⟨x, hx, rfl⟩, ?_⟩
  have h := DFunLike.congr_fun (final_transDiffeomorph_final_mul Φ Ψ) x
  rw [final_apply, Diffeomorph.mul_apply, final_apply Ψ] at h
  exact h.symm

/-- If `Φ` fixes every point of `W₁` and `Ψ` every point of `W₂`, at every time, then the product
`Ψ.transDiffeomorph Φ.final * Φ` fixes every point of `W₁ ∩ W₂` at every time. -/
theorem transDiffeomorph_final_mul_apply_eq_self_of_mem_inter {Φ Ψ : Diffeotopy J n M}
    {W₁ W₂ : Set M} (hΦ : ∀ t, ∀ x ∈ W₁, Φ (t, x) = x) (hΨ : ∀ t, ∀ x ∈ W₂, Ψ (t, x) = x) :
    ∀ t, ∀ x ∈ W₁ ∩ W₂, (Ψ.transDiffeomorph Φ.final * Φ) (t, x) = x := by
  refine fun t x hx ↦ mul_apply_eq_self (hΦ t x hx.1)
    (transDiffeomorph_apply_eq_self_of_mem_image _ hΨ t x ⟨x, hx.2, ?_⟩)
  rw [final_apply, hΦ 1 x hx.1]

/-- If `Φ` and `Ψ` each fix, at every time, every point of a neighbourhood of `S`, then so does
the product `Ψ.transDiffeomorph Φ.final * Φ`. -/
theorem exists_mem_nhdsSet_transDiffeomorph_final_mul_apply_eq_self {Φ Ψ : Diffeotopy J n M}
    {S : Set M} (hΦ : ∃ W ∈ 𝓝ˢ S, ∀ t, ∀ x ∈ W, Φ (t, x) = x)
    (hΨ : ∃ W ∈ 𝓝ˢ S, ∀ t, ∀ x ∈ W, Ψ (t, x) = x) :
    ∃ W ∈ 𝓝ˢ S, ∀ t, ∀ x ∈ W, (Ψ.transDiffeomorph Φ.final * Φ) (t, x) = x := by
  obtain ⟨W₁, hW₁, hΦ⟩ := hΦ
  obtain ⟨W₂, hW₂, hΨ⟩ := hΨ
  exact ⟨W₁ ∩ W₂, Filter.inter_mem hW₁ hW₂,
    transDiffeomorph_final_mul_apply_eq_self_of_mem_inter hΦ hΨ⟩

end Support

section Displacement

variable {M : Type*} [PseudoMetricSpace M] [ChartedSpace H M]

/-- The displacement of a product of diffeotopies is at most the sum of the displacements of its
factors: `dist ((Ψ * Φ) (t, x)) x ≤ dist (Ψ (t, Φ (t, x))) (Φ (t, x)) + dist (Φ (t, x)) x`. -/
theorem dist_mul_apply_le (Φ Ψ : Diffeotopy J n M) (t : I) (x : M) :
    dist ((Ψ * Φ) (t, x)) x ≤ dist (Ψ (t, Φ (t, x))) (Φ (t, x)) + dist (Φ (t, x)) x := by
  rw [mul_apply]
  exact dist_triangle _ _ _

/-- If `Φ` moves every point by less than `δ₁` and `Ψ` by less than `δ₂`, at every time, then
`Ψ * Φ` moves every point by less than `δ₁ + δ₂` at every time. -/
theorem dist_mul_apply_lt_add {Φ Ψ : Diffeotopy J n M} {δ₁ δ₂ : ℝ}
    (hΦ : ∀ t x, dist (Φ (t, x)) x < δ₁) (hΨ : ∀ t x, dist (Ψ (t, x)) x < δ₂) (t : I) (x : M) :
    dist ((Ψ * Φ) (t, x)) x < δ₁ + δ₂ :=
  (dist_mul_apply_le Φ Ψ t x).trans_lt <|
    (add_lt_add (hΨ t _) (hΦ t x)).trans_eq (add_comm _ _)

variable {P : Type*} [PseudoMetricSpace P] [ChartedSpace H P]

/-- Conjugating a diffeotopy by an `L`-Lipschitz diffeomorphism `f` multiplies displacements by
at most `L`: the conjugate moves `y` by at most `L` times the distance by which `Ψ` moves
`f⁻¹ y`. -/
theorem dist_transDiffeomorph_apply_le (Ψ : Diffeotopy J n M) {f : M ≃ₘ^n⟮J, J⟯ P} {L : ℝ≥0}
    (hf : LipschitzWith L f) (t : I) (y : P) :
    dist (Ψ.transDiffeomorph f (t, y)) y ≤ L * dist (Ψ (t, f.symm y)) (f.symm y) := by
  simpa only [transDiffeomorph_apply, Diffeomorph.apply_symm_apply] using
    hf.dist_le_mul (Ψ (t, f.symm y)) (f.symm y)

/-- If `Ψ` moves every point by at most `δ` at every time and `f` is an `L`-Lipschitz
diffeomorphism, then the conjugate of `Ψ` by `f` moves every point by at most `L * δ` at every
time. -/
theorem dist_transDiffeomorph_apply_le_mul {Ψ : Diffeotopy J n M} {f : M ≃ₘ^n⟮J, J⟯ P}
    {L : ℝ≥0} {δ : ℝ} (hf : LipschitzWith L f) (hΨ : ∀ t x, dist (Ψ (t, x)) x ≤ δ) (t : I)
    (y : P) : dist (Ψ.transDiffeomorph f (t, y)) y ≤ L * δ :=
  (dist_transDiffeomorph_apply_le Ψ hf t y).trans <|
    mul_le_mul_of_nonneg_left (hΨ t _) L.coe_nonneg

/-- If `Φ` moves every point by less than `δ₁` and `Ψ` by less than `δ₂`, at every time, and the
diffeomorphism `f` is `L`-Lipschitz, then `Ψ.transDiffeomorph f * Φ` moves every point by less
than `δ₁ + L * δ₂` at every time. -/
theorem dist_transDiffeomorph_mul_apply_lt {Φ Ψ : Diffeotopy J n M} {f : M ≃ₘ^n⟮J, J⟯ M}
    {L : ℝ≥0} {δ₁ δ₂ : ℝ} (hf : LipschitzWith L f) (hΦ : ∀ t x, dist (Φ (t, x)) x < δ₁)
    (hΨ : ∀ t x, dist (Ψ (t, x)) x < δ₂) (t : I) (x : M) :
    dist ((Ψ.transDiffeomorph f * Φ) (t, x)) x < δ₁ + L * δ₂ := by
  refine (dist_mul_apply_le Φ _ t x).trans_lt ?_
  rw [add_comm δ₁]
  exact add_lt_add_of_le_of_lt
    (dist_transDiffeomorph_apply_le_mul hf (fun t x ↦ (hΨ t x).le) t _) (hΦ t x)

end Displacement

end TauCeti.Diffeotopy

end
