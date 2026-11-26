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

* the points fixed at every time: a set fixed by `Φ` and by `Ψ` is fixed by `Ψ * Φ`, and the
  image `f '' W` of a set `W` fixed by `Ψ` is fixed by `Ψ.transDiffeomorph f`;
* the support: if `Φ` fixes every point outside `C₁` and `Ψ` every point outside `C₂`, then
  `Ψ * Φ` fixes every point outside `C₁ ∪ C₂`, and if `Ψ` fixes every point outside `C`, then
  `Ψ.transDiffeomorph f` fixes every point outside `f '' C`;
* on a pseudo-metric space, the displacement `dist (Φ (t, x)) x`: displacements add under the
  product, by the triangle inequality, and are multiplied by at most `L` under conjugation by an
  `L`-Lipschitz diffeomorphism.

## Main results

* `TauCeti.Diffeotopy.mul_apply_eq_self_of_mem`,
  `TauCeti.Diffeotopy.transDiffeomorph_apply_eq_self_of_mem_image`: fixed sets.
* `TauCeti.Diffeotopy.mul_apply_eq_self_of_notMem_union`,
  `TauCeti.Diffeotopy.transDiffeomorph_apply_eq_self_of_notMem_image`: supports.
* `TauCeti.Diffeotopy.dist_mul_apply_le`, `TauCeti.Diffeotopy.dist_mul_apply_lt_add`: the
  displacement of a product.
* `TauCeti.Diffeotopy.dist_transDiffeomorph_apply_le`,
  `TauCeti.Diffeotopy.dist_transDiffeomorph_apply_le_mul`: the displacement of a conjugate.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], third
  edition, §10.2 (the pointwise product of isotopies).
-/

public section

open Set unitInterval
open scoped Manifold ContDiff NNReal

namespace TauCeti.Diffeotopy

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {J : ModelWithCorners ℝ E H} {n : ℕ∞ω}

section Support

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {P : Type*} [TopologicalSpace P] [ChartedSpace H P]

/-- If two diffeotopies fix every point of `W` at every time, so does their product. -/
theorem mul_apply_eq_self_of_mem {Φ Ψ : Diffeotopy J n M} {W : Set M}
    (hΦ : ∀ t, ∀ x ∈ W, Φ (t, x) = x) (hΨ : ∀ t, ∀ x ∈ W, Ψ (t, x) = x) :
    ∀ t, ∀ x ∈ W, (Ψ * Φ) (t, x) = x := fun t x hx ↦ by
  rw [mul_apply, hΦ t x hx, hΨ t x hx]

/-- If `Φ` fixes every point outside `C₁` and `Ψ` every point outside `C₂`, at every time, then
`Ψ * Φ` fixes every point outside `C₁ ∪ C₂` at every time. -/
theorem mul_apply_eq_self_of_notMem_union {Φ Ψ : Diffeotopy J n M} {C₁ C₂ : Set M}
    (hΦ : ∀ t, ∀ x ∉ C₁, Φ (t, x) = x) (hΨ : ∀ t, ∀ x ∉ C₂, Ψ (t, x) = x) :
    ∀ t, ∀ x ∉ C₁ ∪ C₂, (Ψ * Φ) (t, x) = x := by
  simp only [← mem_compl_iff, compl_union] at hΦ hΨ ⊢
  exact mul_apply_eq_self_of_mem (fun t x hx ↦ hΦ t x hx.1) fun t x hx ↦ hΨ t x hx.2

/-- If `Ψ` fixes every point of `W` at every time, then its conjugate by a diffeomorphism `f`
fixes every point of `f '' W` at every time. -/
theorem transDiffeomorph_apply_eq_self_of_mem_image {Ψ : Diffeotopy J n M}
    (f : M ≃ₘ^n⟮J, J⟯ P) {W : Set M} (hΨ : ∀ t, ∀ x ∈ W, Ψ (t, x) = x) :
    ∀ t, ∀ y ∈ f '' W, Ψ.transDiffeomorph f (t, y) = y := by
  rintro t _ ⟨x, hx, rfl⟩
  rw [transDiffeomorph_apply, Diffeomorph.symm_apply_apply, hΨ t x hx]

/-- If `Ψ` fixes every point outside `C` at every time, then its conjugate by a diffeomorphism
`f` fixes every point outside `f '' C` at every time. -/
theorem transDiffeomorph_apply_eq_self_of_notMem_image {Ψ : Diffeotopy J n M}
    (f : M ≃ₘ^n⟮J, J⟯ P) {C : Set M} (hΨ : ∀ t, ∀ x ∉ C, Ψ (t, x) = x) :
    ∀ t, ∀ y ∉ f '' C, Ψ.transDiffeomorph f (t, y) = y := by
  intro t y hy
  have hy' : f.symm y ∉ C := fun h ↦ hy ⟨_, h, f.apply_symm_apply y⟩
  rw [transDiffeomorph_apply, hΨ t _ hy', Diffeomorph.apply_symm_apply]

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

/-- If `Ψ` moves every point by less than `δ` at every time and `f` is an `L`-Lipschitz
diffeomorphism, then the conjugate of `Ψ` by `f` moves every point by at most `L * δ` at every
time. -/
theorem dist_transDiffeomorph_apply_le_mul {Ψ : Diffeotopy J n M} {f : M ≃ₘ^n⟮J, J⟯ P}
    {L : ℝ≥0} {δ : ℝ} (hf : LipschitzWith L f) (hΨ : ∀ t x, dist (Ψ (t, x)) x < δ) (t : I)
    (y : P) : dist (Ψ.transDiffeomorph f (t, y)) y ≤ L * δ :=
  (dist_transDiffeomorph_apply_le Ψ hf t y).trans <|
    mul_le_mul_of_nonneg_left (hΨ t _).le L.coe_nonneg

end Displacement

end TauCeti.Diffeotopy

end
