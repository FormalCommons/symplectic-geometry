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

For Tau Ceti's diffeotopies `TauCeti.Diffeotopy`, this file records how fixed points, supports
and displacement behave under the pointwise product `Ψ * Φ` of `TauCeti.Diffeotopy.instGroup`,
whose value at `(t, x)` is `Ψ (t, Φ (t, x))`, and under the conjugation `Ψ.transDiffeomorph f`
by a diffeomorphism `f`, whose value at `(t, y)` is `f (Ψ (t, f⁻¹ y))`:

* fixed points: a point fixed at time `t` by `Φ` and by `Ψ` is fixed by `Ψ * Φ`, and
  `Ψ.transDiffeomorph f` fixes `y` at time `t` exactly when `Ψ` fixes `f⁻¹ y`; hence a set
  fixed at every time by `Φ` and by `Ψ` is fixed by `Ψ * Φ`, and the image `f '' W` of a set `W`
  fixed by `Ψ` is fixed by `Ψ.transDiffeomorph f`;
* finite products: if each `Φ i` fixes every point outside `W i` at every time, the sets `W i`
  being pairwise disjoint, then at every time the product of the `Φ i` over a list acts on each
  `W i` as `Φ i` and fixes every point outside the union of the `W i`. Tau Ceti's
  `TauCeti.exists_diffeotopy_final_comp_eqOn_of_pairwise_disjoint` shows this for the final
  maps, by the same induction over the factors, and the step that a diffeotopy fixing the
  complement of `W` keeps `W` in place follows Tau Ceti's
  `TauCeti.Diffeotopy.mapsTo_final_of_eqOn_compl`, at a time `t` instead of time `1`;
* on a pseudo-metric space, the displacement `dist (Φ (t, x)) x`: displacements add under the
  product, by the triangle inequality, and are multiplied by at most `L` under conjugation by an
  `L`-Lipschitz diffeomorphism.

The last results are about the product `Ψ.transDiffeomorph f * Φ`, which runs `Φ` and then `Ψ`
conjugated by `f`. For any `f`, it is the identity outside `C₁ ∪ f '' C₂`, by Tau Ceti's
`TauCeti.Diffeotopy.eqOn_id_trans` and `TauCeti.Diffeotopy.eqOn_id_transDiffeomorph`, and it
moves points by less than `δ₁ + L * δ₂` when `f` is `L`-Lipschitz. For `f = Φ.final`, its final
map is `Φ.final * Ψ.final`, and it fixes at every time each point that both `Φ` and `Ψ` fix at
every time.

## Main results

* `TauCeti.Diffeotopy.mul_apply_eq_self`,
  `TauCeti.Diffeotopy.transDiffeomorph_apply_eq_self_iff`: fixed points at one time.
* `TauCeti.Diffeotopy.mul_apply_eq_self_of_mem`,
  `TauCeti.Diffeotopy.transDiffeomorph_apply_eq_self_of_mem_image`: fixed sets.
* `TauCeti.Diffeotopy.mapsTo_apply_of_eq_self_of_notMem`: a diffeotopy fixing the complement
  of `W` at time `t` maps `W` into itself at time `t`.
* `TauCeti.Diffeotopy.list_prod_map_apply_of_mem`,
  `TauCeti.Diffeotopy.list_prod_map_apply_eq_self_of_notMem_biUnion`: a product of diffeotopies
  with pairwise disjoint supports, at every time.
* `TauCeti.Diffeotopy.dist_mul_apply_le`, `TauCeti.Diffeotopy.dist_mul_apply_lt_add`: the
  displacement of a product.
* `TauCeti.Diffeotopy.dist_transDiffeomorph_apply_le`,
  `TauCeti.Diffeotopy.dist_transDiffeomorph_apply_le_mul`: the displacement of a conjugate.
* `TauCeti.Diffeotopy.final_transDiffeomorph_final_mul`,
  `TauCeti.Diffeotopy.transDiffeomorph_final_mul_apply_one`,
  `TauCeti.Diffeotopy.image_transDiffeomorph_final_mul_apply_one_subset`: the final map of
  `Ψ.transDiffeomorph Φ.final * Φ`.
* `TauCeti.Diffeotopy.transDiffeomorph_mul_apply_eq_self_of_notMem_union_image`,
  `TauCeti.Diffeotopy.transDiffeomorph_final_mul_apply_eq_self_of_mem_inter`,
  `TauCeti.Diffeotopy.dist_transDiffeomorph_mul_apply_lt`: support, fixed sets and displacement
  of `Ψ.transDiffeomorph f * Φ`.

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

/-- If `Ψ` fixes every point of `W` at every time, then its conjugate by a diffeomorphism `f`
fixes every point of `f '' W` at every time. -/
theorem transDiffeomorph_apply_eq_self_of_mem_image {Ψ : Diffeotopy J n M}
    (f : M ≃ₘ^n⟮J, J⟯ P) {W : Set M} (hΨ : ∀ t, ∀ x ∈ W, Ψ (t, x) = x) :
    ∀ t, ∀ y ∈ f '' W, Ψ.transDiffeomorph f (t, y) = y := by
  rintro t _ ⟨x, hx, rfl⟩
  rw [transDiffeomorph_apply_eq_self_iff, Diffeomorph.symm_apply_apply]
  exact hΨ t x hx

/-- If `Φ` fixes every point outside `C₁` and `Ψ` every point outside `C₂`, at every time, then
the product `Ψ.transDiffeomorph f * Φ` of `Φ` with the conjugate of `Ψ` by a diffeomorphism `f`
fixes every point outside `C₁ ∪ f '' C₂` at every time. -/
theorem transDiffeomorph_mul_apply_eq_self_of_notMem_union_image {Φ Ψ : Diffeotopy J n M}
    (f : M ≃ₘ^n⟮J, J⟯ M) {C₁ C₂ : Set M} (hΦ : ∀ t, ∀ x ∉ C₁, Φ (t, x) = x)
    (hΨ : ∀ t, ∀ x ∉ C₂, Ψ (t, x) = x) :
    ∀ t, ∀ x ∉ C₁ ∪ f '' C₂, (Ψ.transDiffeomorph f * Φ) (t, x) = x :=
  fun t x hx ↦ by
    rw [mul_def]
    exact eqOn_id_trans (fun t _ hy ↦ hΦ t _ (Set.notMem_of_mem_compl hy))
      (eqOn_id_transDiffeomorph f fun t _ hy ↦ hΨ t _ (Set.notMem_of_mem_compl hy)) t
      (Set.mem_compl hx)

/-- The final map of the product `Ψ.transDiffeomorph Φ.final * Φ`, which runs `Φ` and then `Ψ`
conjugated by the final map of `Φ`, is `Φ.final * Ψ.final`. -/
theorem final_transDiffeomorph_final_mul (Φ Ψ : Diffeotopy J n M) :
    (Ψ.transDiffeomorph Φ.final * Φ).final = Φ.final * Ψ.final := by
  rw [final_mul, final_transDiffeomorph_eq_mul_mul_inv, inv_mul_cancel_right]

/-- At time `1`, the product `Ψ.transDiffeomorph Φ.final * Φ` sends `x` to
`Φ.final (Ψ (1, x))`. -/
theorem transDiffeomorph_final_mul_apply_one (Φ Ψ : Diffeotopy J n M) (x : M) :
    (Ψ.transDiffeomorph Φ.final * Φ) (1, x) = Φ.final (Ψ (1, x)) := by
  have h := DFunLike.congr_fun (final_transDiffeomorph_final_mul Φ Ψ) x
  rwa [final_apply, Diffeomorph.mul_apply, final_apply Ψ] at h

/-- If the final map of `Ψ` sends `S` into `V`, then the final map of the product
`Ψ.transDiffeomorph Φ.final * Φ` sends `S` into `Φ.final '' V`. -/
theorem image_transDiffeomorph_final_mul_apply_one_subset {Φ Ψ : Diffeotopy J n M}
    {S V : Set M} (hΨ : (fun x ↦ Ψ (1, x)) '' S ⊆ V) :
    (fun x ↦ (Ψ.transDiffeomorph Φ.final * Φ) (1, x)) '' S ⊆ Φ.final '' V := by
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨Ψ (1, x), hΨ ⟨x, hx, rfl⟩, (transDiffeomorph_final_mul_apply_one Φ Ψ x).symm⟩

/-- If `Φ` fixes every point of `W₁` and `Ψ` every point of `W₂`, at every time, then the product
`Ψ.transDiffeomorph Φ.final * Φ` fixes every point of `W₁ ∩ W₂` at every time. -/
theorem transDiffeomorph_final_mul_apply_eq_self_of_mem_inter {Φ Ψ : Diffeotopy J n M}
    {W₁ W₂ : Set M} (hΦ : ∀ t, ∀ x ∈ W₁, Φ (t, x) = x) (hΨ : ∀ t, ∀ x ∈ W₂, Ψ (t, x) = x) :
    ∀ t, ∀ x ∈ W₁ ∩ W₂, (Ψ.transDiffeomorph Φ.final * Φ) (t, x) = x := by
  refine fun t x hx ↦ mul_apply_eq_self (hΦ t x hx.1)
    (transDiffeomorph_apply_eq_self_of_mem_image _ hΨ t x ⟨x, hx.2, ?_⟩)
  rw [final_apply, hΦ 1 x hx.1]

/-- A diffeotopy that fixes every point outside `W` at time `t` maps `W` into itself at time
`t`. -/
theorem mapsTo_apply_of_eq_self_of_notMem {Φ : Diffeotopy J n M} {t : I} {W : Set M}
    (hΦ : ∀ x ∉ W, Φ (t, x) = x) : MapsTo (fun x ↦ Φ (t, x)) W W := by
  have hfix : EqOn (Φ.timeSlice t) id Wᶜ := fun x hx ↦ by
    rw [timeSlice_apply, hΦ x hx, id]
  have h := ((surjOn_id Wᶜ).congr hfix.symm).mapsTo_compl (Φ.timeSlice t).injective
  rw [compl_compl] at h
  intro x hx
  have hy := h hx
  rwa [timeSlice_apply] at hy

/-- A product of diffeotopies over a list fixes at time `t` every point that each factor fixes
at time `t`. -/
theorem list_prod_map_apply_eq_self {ι : Type*} {Φ : ι → Diffeotopy J n M} {l : List ι}
    {t : I} {x : M} (hx : ∀ i ∈ l, Φ i (t, x) = x) : (l.map Φ).prod (t, x) = x := by
  induction l with
  | nil => rw [List.map_nil, List.prod_nil, one_apply]
  | cons j l ih =>
    rw [List.map_cons, List.prod_cons]
    exact mul_apply_eq_self (ih fun i hi ↦ hx i (List.mem_cons_of_mem j hi))
      (hx j List.mem_cons_self)

/-- Let each diffeotopy `Φ i` fix every point outside `W i` at every time, the sets `W i` being
pairwise disjoint along a list `l`. Then at every time the product of the `Φ i` over `l`, in
the order of `l`, acts on `W i` as `Φ i`, for each `i` in `l`. -/
theorem list_prod_map_apply_of_mem {ι : Type*} {Φ : ι → Diffeotopy J n M} {W : ι → Set M}
    {l : List ι} (hW : l.Pairwise fun i j ↦ Disjoint (W i) (W j))
    (hΦ : ∀ i ∈ l, ∀ t, ∀ x ∉ W i, Φ i (t, x) = x) {i : ι} (hi : i ∈ l) (t : I) {x : M}
    (hx : x ∈ W i) : (l.map Φ).prod (t, x) = Φ i (t, x) := by
  induction l with
  | nil => simp at hi
  | cons j l ih =>
    rw [List.pairwise_cons] at hW
    have hΦl : ∀ k ∈ l, ∀ t, ∀ x ∉ W k, Φ k (t, x) = x := fun k hk ↦
      hΦ k (List.mem_cons_of_mem j hk)
    rw [List.map_cons, List.prod_cons, mul_apply]
    rcases List.mem_cons.mp hi with rfl | hi
    · rw [list_prod_map_apply_eq_self fun k hk ↦
        hΦl k hk t x fun hxk ↦ (hW.1 k hk).ne_of_mem hx hxk rfl]
    · have hy : Φ i (t, x) ∈ W i := mapsTo_apply_of_eq_self_of_notMem (hΦl i hi t) hx
      rw [ih hW.2 hΦl hi]
      exact hΦ j List.mem_cons_self t _ fun hyj ↦ (hW.1 i hi).ne_of_mem hyj hy rfl

/-- If each diffeotopy `Φ i` fixes every point outside `W i` at every time, then at every time
the product of the `Φ i` over a list `l` fixes every point outside the union of the `W i` over
`l`. -/
theorem list_prod_map_apply_eq_self_of_notMem_biUnion {ι : Type*} {Φ : ι → Diffeotopy J n M}
    {W : ι → Set M} {l : List ι} (hΦ : ∀ i ∈ l, ∀ t, ∀ x ∉ W i, Φ i (t, x) = x) (t : I)
    {x : M} (hx : x ∉ ⋃ i ∈ l, W i) : (l.map Φ).prod (t, x) = x :=
  list_prod_map_apply_eq_self fun i hi ↦ hΦ i hi t x fun hxi ↦ hx (mem_iUnion₂_of_mem hi hxi)

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
