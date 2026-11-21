/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

/-!
# Gram–Schmidt and skew-adjoint maps

Let `J` be a skew-adjoint linear map of a real inner product space, `⟪J u, v⟫ = -⟪u, J v⟫`. If
the Gram–Schmidt input `f` has `f j = J (f i)` at an index `j` covering `i`, and the span of the
inputs before `i` is `J`-invariant, then Mathlib's Gram–Schmidt process gives
`gramSchmidt ℝ f j = J (gramSchmidt ℝ f i)`
(`InnerProductSpace.gramSchmidt_eq_apply_gramSchmidt`), and the same for the normalized process
when `J` also preserves norms (`InnerProductSpace.gramSchmidtNormed_eq_apply_gramSchmidtNormed`).

For a complex structure `J` that is orthogonal for the inner product, applied to the inputs
`u₀, J u₀, u₁, J u₁, …`, this says that the output has the form `e₀, J e₀, e₁, J e₁, …`
(`InnerProductSpace.gramSchmidtNormed_two_mul_add_one`): the
real Gram–Schmidt process is then a complex one. This is the step of the construction of
Darboux frames in McDuff–Salamon, §2.6, that orthonormalizes a complex basis.

Over any `RCLike` field, `InnerProductSpace.gramSchmidt_sub_mem_span` says that each output differs
from its input by a vector in the span of the earlier outputs.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.6
-/

public section

open Submodule Set
open scoped RealInnerProductSpace

namespace InnerProductSpace

variable {ι : Type*} [LinearOrder ι] [LocallyFiniteOrderBot ι]

section RCLike

variable (𝕜 : Type*) {E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The difference between a Gram–Schmidt output and its input lies in the span of the earlier
outputs. -/
theorem gramSchmidt_sub_mem_span (f : ι → E) (n : ι) :
    gramSchmidt 𝕜 f n - f n ∈ span 𝕜 (gramSchmidt 𝕜 f '' Iio n) := by
  rw [gramSchmidt_def 𝕜 f n, sub_sub_cancel_left]
  refine neg_mem (sum_mem fun k hk ↦ ?_)
  rw [starProjection_singleton]
  exact smul_mem _ _ (subset_span (mem_image_of_mem _ (Finset.mem_Iio.1 hk)))

end RCLike

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Let `J` be skew-adjoint, `⟪J u, v⟫ = -⟪u, J v⟫`. If `j` covers `i`, `f j = J (f i)`, and `J`
maps the span of the inputs `f k`, `k < i`, into itself, then the Gram–Schmidt outputs satisfy
`gramSchmidt ℝ f j = J (gramSchmidt ℝ f i)`. -/
theorem gramSchmidt_eq_apply_gramSchmidt {J : E →ₗ[ℝ] E} (hJ : ∀ u v, ⟪J u, v⟫ = -⟪u, J v⟫)
    {f : ι → E} {i j : ι} (hij : i ⋖ j) (hf : f j = J (f i))
    (hS : ∀ v ∈ span ℝ (f '' Iio i), J v ∈ span ℝ (f '' Iio i)) :
    gramSchmidt ℝ f j = J (gramSchmidt ℝ f i) := by
  set g := gramSchmidt ℝ f
  have hIio : Iio j = Iic i := ext fun k ↦ ⟨hij.le_of_lt, fun hk ↦ hk.trans_lt hij.lt⟩
  have hspan : span ℝ (g '' Iio i) ≤ span ℝ (g '' Iio j) :=
    span_mono (image_mono (Iio_subset_Iio hij.lt.le))
  -- `J` maps the span of the outputs before `i` into itself.
  have hS' : ∀ v ∈ span ℝ (g '' Iio i), J v ∈ span ℝ (g '' Iio i) := by
    simpa only [g, span_gramSchmidt_Iio] using hS
  -- The output at `i` is orthogonal to `J` applied to the earlier outputs.
  have hperp : ∀ v ∈ span ℝ (g '' Iio i), ⟪g i, J v⟫ = 0 := by
    intro v hv
    refine span_induction (fun _ ⟨k, hk, hkv⟩ ↦ ?_) (by simp) (fun _ _ _ _ h₁ h₂ ↦ ?_)
      (fun c _ _ h ↦ ?_) (hS' v hv)
    · rw [← hkv]
      exact gramSchmidt_orthogonal ℝ f (ne_of_gt hk)
    · rw [inner_add_right, h₁, h₂, add_zero]
    · rw [inner_smul_right, h, mul_zero]
  -- The difference of the two sides lies in the span of the outputs before `j` and is orthogonal
  -- to each of them, so it vanishes.
  set d := g j - J (g i)
  have hd : d ∈ span ℝ (g '' Iio j) := by
    have h₁ := gramSchmidt_sub_mem_span ℝ f j
    have h₂ := hspan (hS' _ (gramSchmidt_sub_mem_span ℝ f i))
    rw [map_sub, ← hf] at h₂
    simpa [d] using sub_mem h₁ h₂
  have hdk : ∀ k ∈ Iio j, ⟪g k, d⟫ = 0 := by
    intro k hk
    rw [hIio] at hk
    rw [inner_sub_right, gramSchmidt_orthogonal ℝ f (ne_of_lt (hk.trans_lt hij.lt)), zero_sub,
      neg_eq_zero]
    rcases hk.lt_or_eq with hk | rfl
    · rw [← neg_eq_zero, ← hJ, real_inner_comm]
      exact hperp _ (subset_span (mem_image_of_mem _ hk))
    · have := hJ (g k) (g k)
      rw [real_inner_comm] at this
      linarith
  have hdd : ∀ v ∈ span ℝ (g '' Iio j), ⟪v, d⟫ = 0 := by
    intro v hv
    induction hv using span_induction with
    | mem x hx =>
      obtain ⟨k, hk, rfl⟩ := hx
      exact hdk k hk
    | zero => simp
    | add x y _ _ h₁ h₂ => rw [inner_add_left, h₁, h₂, add_zero]
    | smul c x _ h => rw [inner_smul_left, h, mul_zero]
  exact sub_eq_zero.1 (inner_self_eq_zero.1 (hdd d hd))

/-- The normalized form of `gramSchmidt_eq_apply_gramSchmidt`: if moreover `J` preserves norms,
then `gramSchmidtNormed ℝ f j = J (gramSchmidtNormed ℝ f i)`. -/
theorem gramSchmidtNormed_eq_apply_gramSchmidtNormed {J : E →ₗ[ℝ] E}
    (hJ : ∀ u v, ⟪J u, v⟫ = -⟪u, J v⟫) (hJn : ∀ v, ‖J v‖ = ‖v‖)
    {f : ι → E} {i j : ι} (hij : i ⋖ j) (hf : f j = J (f i))
    (hS : ∀ v ∈ span ℝ (f '' Iio i), J v ∈ span ℝ (f '' Iio i)) :
    gramSchmidtNormed ℝ f j = J (gramSchmidtNormed ℝ f i) := by
  rw [gramSchmidtNormed, gramSchmidtNormed, gramSchmidt_eq_apply_gramSchmidt hJ hij hf hS, hJn,
    map_smul]

/-- Let `J` be skew-adjoint and norm-preserving, so that `J` is an orthogonal complex structure.
Apply Gram–Schmidt to the inputs `u₀, J u₀, u₁, J u₁, …`, indexed by `Fin (2 * k)`. Then each
output at an odd index `2 i + 1` is `J` applied to the output at `2 i`. -/
theorem gramSchmidtNormed_two_mul_add_one {J : E →ₗ[ℝ] E} (hJ : ∀ u v, ⟪J u, v⟫ = -⟪u, J v⟫)
    (hJn : ∀ v, ‖J v‖ = ‖v‖) {k : ℕ} (u : Fin k → E) (i : Fin k) :
    gramSchmidtNormed ℝ (fun j : Fin (2 * k) ↦
        if (j : ℕ) % 2 = 0 then u ⟨j / 2, by omega⟩ else J (u ⟨j / 2, by omega⟩))
        ⟨2 * i + 1, by omega⟩ =
      J (gramSchmidtNormed ℝ (fun j : Fin (2 * k) ↦
        if (j : ℕ) % 2 = 0 then u ⟨j / 2, by omega⟩ else J (u ⟨j / 2, by omega⟩))
        ⟨2 * i, by omega⟩) := by
  set w : Fin (2 * k) → E := fun j ↦
    if (j : ℕ) % 2 = 0 then u ⟨j / 2, by omega⟩ else J (u ⟨j / 2, by omega⟩)
  -- `J` squares to `-1`, being skew-adjoint and orthogonal.
  have hJJ (v : E) : J (J v) = -v := by
    refine ext_inner_right ℝ fun x ↦ ?_
    have := LinearIsometry.inner_map_map (⟨J, hJn⟩ : E →ₗᵢ[ℝ] E) v x
    simp only [LinearIsometry.coe_mk] at this
    rw [hJ, this, inner_neg_left]
  have hw (j : ℕ) (hj : j < k) :
      w ⟨2 * j, by omega⟩ = u ⟨j, hj⟩ ∧ w ⟨2 * j + 1, by omega⟩ = J (u ⟨j, hj⟩) := by
    have h₀ : (2 * j) / 2 = j := by omega
    have h₁ : (2 * j + 1) / 2 = j := by omega
    simp [w, h₀, h₁, Nat.mul_mod_right, Nat.add_mod]
  refine gramSchmidtNormed_eq_apply_gramSchmidtNormed hJ hJn
    (Fin.covBy_iff.2 (Nat.covBy_iff_add_one_eq.2 rfl)) ((hw i i.isLt).2.trans ?_) ?_
  · rw [(hw i i.isLt).1]
  -- The span of the inputs before `2 i` is `J`-invariant.
  suffices h : w '' Iio ⟨2 * i, by omega⟩ ⊆
      (span ℝ (w '' Iio ⟨2 * i, by omega⟩)).comap J from fun v hv ↦ span_le.2 h hv
  rintro _ ⟨⟨j, hj⟩, hji, rfl⟩
  simp only [mem_Iio, Fin.mk_lt_mk] at hji
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' j
  · refine subset_span ⟨⟨2 * m + 1, by omega⟩, by simp only [mem_Iio, Fin.mk_lt_mk]; omega, ?_⟩
    rw [(hw m (by omega)).1, (hw m (by omega)).2]
  · have h : J (w ⟨2 * m + 1, hj⟩) = -w ⟨2 * m, by omega⟩ := by
      rw [(hw m (by omega)).2, hJJ, (hw m (by omega)).1]
    rw [SetLike.mem_coe, mem_comap, h]
    exact neg_mem (subset_span ⟨⟨2 * m, by omega⟩, by simp only [mem_Iio, Fin.mk_lt_mk]; omega,
      rfl⟩)

end InnerProductSpace
