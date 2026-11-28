/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# Projections along the orthogonal of a subspace for a bilinear form

Let `B` be a bilinear form on a module `M` over a commutative ring and `W` a submodule that is
complementary to its `B`-orthogonal. This file characterizes the projection onto `W` along the
`B`-orthogonal of `W`: it sends `v` to the unique `w ∈ W` with `B u w = B u v` for all `u ∈ W`
(`LinearMap.BilinForm.projection_orthogonal_eq_iff`). It also compares the orthogonals of `W`
for two forms: forms that agree on `W × M` have the same orthogonal of `W`
(`LinearMap.BilinForm.orthogonal_eq_orthogonal_of_forall`), and for forms that agree on `W × W`
the converse holds when `W` and its orthogonal span `M`
(`LinearMap.BilinForm.orthogonal_eq_orthogonal_iff`). A surjective linear map that carries one
form to another maps orthogonals onto orthogonals
(`LinearMap.BilinForm.map_orthogonal_of_surjective`). In finite dimension, a form whose
quadratic form is anisotropic, such as a positive definite symmetric form, makes every subspace
complementary to its orthogonal (`LinearMap.BilinForm.isCompl_orthogonal_of_anisotropic`).
-/

public section

namespace LinearMap.BilinForm

section CommRing

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- The projection onto a subspace `W` along its `B`-orthogonal sends `v` to `w` exactly when `w`
lies in `W` and pairs with every vector of `W` as `v` does: `B u w = B u v` for all `u ∈ W`. -/
theorem projection_orthogonal_eq_iff (B : LinearMap.BilinForm R M) {W : Submodule R M}
    (h : IsCompl W (B.orthogonal W)) (v w : M) :
    W.projection (B.orthogonal W) h v = w ↔ w ∈ W ∧ ∀ u ∈ W, B u w = B u v := by
  have hsub (v w : M) : v - w ∈ B.orthogonal W ↔ ∀ u ∈ W, B u w = B u v := by
    simp only [mem_orthogonal_iff, map_sub, sub_eq_zero]
    exact forall₂_congr fun _ _ ↦ eq_comm
  constructor
  · rintro rfl
    exact ⟨Submodule.projection_apply_mem h v, (hsub _ _).mp (Submodule.sub_projection_mem h v)⟩
  · rintro ⟨hw, hwv⟩
    have hv : v = w + (v - w) := (add_sub_cancel w v).symm
    rw [hv, map_add, Submodule.projection_apply_of_mem_left h hw,
      (Submodule.projection_apply_eq_zero_iff h).mpr ((hsub v w).mpr hwv), add_zero]

end CommRing

section CommSemiring

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- Two bilinear forms that agree on `W × M` have the same orthogonal of `W`. -/
theorem orthogonal_eq_orthogonal_of_forall {B₁ B₂ : LinearMap.BilinForm R M} {W : Submodule R M}
    (h : ∀ w ∈ W, ∀ v, B₁ w v = B₂ w v) : B₁.orthogonal W = B₂.orthogonal W := by
  ext v
  simp only [mem_orthogonal_iff]
  exact forall₂_congr fun w hw ↦ by rw [h w hw v]

/-- Two bilinear forms that agree on `W × W` have the same orthogonal of `W` exactly when they
agree on `W × M`, provided `W` and its `B₁`-orthogonal span `M`. -/
theorem orthogonal_eq_orthogonal_iff {B₁ B₂ : LinearMap.BilinForm R M} {W : Submodule R M}
    (hW : ∀ w ∈ W, ∀ w' ∈ W, B₁ w w' = B₂ w w') (hc : Codisjoint W (B₁.orthogonal W)) :
    B₁.orthogonal W = B₂.orthogonal W ↔ ∀ w ∈ W, ∀ v, B₁ w v = B₂ w v := by
  refine ⟨fun h w hw v ↦ ?_, orthogonal_eq_orthogonal_of_forall⟩
  obtain ⟨w', u, hw', hu, rfl⟩ := Submodule.codisjoint_iff_exists_add_eq.1 hc v
  have hu₂ : u ∈ B₂.orthogonal W := h ▸ hu
  rw [map_add, map_add, (mem_orthogonal_iff.1 hu) w hw, (mem_orthogonal_iff.1 hu₂) w hw,
    hW w hw w' hw']

/-- A surjective linear map `f` that carries the form `B` to the form `B'`, in the sense that
`B' (f v) (f w) = B v w`, maps the `B`-orthogonal of `W` onto the `B'`-orthogonal of `f(W)`. -/
theorem map_orthogonal_of_surjective {M' : Type*} [AddCommMonoid M'] [Module R M']
    {B : LinearMap.BilinForm R M} {B' : LinearMap.BilinForm R M'} {f : M →ₗ[R] M'}
    (hf : Function.Surjective f) (h : ∀ v w, B' (f v) (f w) = B v w) (W : Submodule R M) :
    (B.orthogonal W).map f = B'.orthogonal (W.map f) := by
  ext u
  constructor
  · rintro ⟨v, hv, rfl⟩
    rintro _ ⟨w, hw, rfl⟩
    exact (h w v).trans (hv w hw)
  · intro hu
    obtain ⟨v, rfl⟩ := hf u
    exact ⟨v, fun w hw ↦ (h w v).symm.trans (hu _ ⟨w, hw, rfl⟩), rfl⟩

end CommSemiring

section Field

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- In finite dimension, if the quadratic form `x ↦ B x x` of `B` is anisotropic, then every
subspace `W` is complementary to its `B`-orthogonal. This applies to a symmetric form whose
quadratic form is positive definite, through `QuadraticMap.PosDef.anisotropic`. -/
theorem isCompl_orthogonal_of_anisotropic {B : LinearMap.BilinForm K V}
    (hBa : B.toQuadraticMap.Anisotropic) (W : Submodule K V) : IsCompl W (B.orthogonal W) := by
  have hd : Disjoint W (B.orthogonal W) := Submodule.disjoint_def.2 fun v hv hv' ↦ hBa v <| by
    rw [LinearMap.BilinMap.toQuadraticMap_apply]
    exact mem_orthogonal_iff.1 hv' v hv
  refine ⟨hd, codisjoint_iff.2 (Submodule.eq_top_of_finrank_eq ?_)⟩
  have h₁ := Submodule.finrank_sup_add_finrank_inf_eq W (B.orthogonal W)
  have h₂ := finrank_add_finrank_orthogonal' (B := B) W
  have h₃ := Submodule.finrank_le (W ⊔ B.orthogonal W)
  rw [hd.eq_bot, finrank_bot] at h₁
  omega

end Field

end LinearMap.BilinForm

end
