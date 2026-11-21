/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Stability of immersions transverse to a vector field

Let `f : M → N` be a `C¹` map from a manifold with finite-dimensional model space, and `Z` a
vector field on `N`, continuous at `f x`. If the differential of `f` at `x` is injective and
`Z (f x)` is not in its range, the same holds at every point near `x`
(`ContMDiffAt.eventually_injective_mfderiv_and_notMem_range`). Both conditions together say that
`(v, t) ↦ df_y v + t Z (f y)` is injective (`LinearMap.injective_coprod_toSpanSingleton_iff`);
read in tangent coordinates, this is a continuous family of linear maps on the finite-dimensional
space `E × ℝ`, and injectivity is open there.

The proof follows Tau Ceti's `ContMDiffAt.eventually_injective_mfderiv`, with the column `Z`
added to the differential.
-/

public section

open Bundle Filter Function Set
open scoped ContDiff Manifold Topology

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J 1 N]
  {f : M → N} {Z : Π y : N, TangentSpace J y} {x : M} {n : ℕ∞ω}

/-- Over a division ring, the map `(v, t) ↦ A v + t • z` is injective exactly when `A` is
injective and `z` is not in the range of `A`. -/
theorem LinearMap.injective_coprod_toSpanSingleton_iff {K V W : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] (A : V →ₗ[K] W) (z : W) :
    Injective (A.coprod (LinearMap.toSpanSingleton K W z)) ↔
      Injective A ∧ z ∉ LinearMap.range A := by
  simp only [injective_iff_map_eq_zero, LinearMap.coprod_apply, LinearMap.toSpanSingleton_apply,
    Prod.forall, Prod.mk_eq_zero, LinearMap.mem_range, not_exists]
  refine ⟨fun h ↦ ⟨fun v hv ↦ (h v 0 (by simp [hv])).1, fun v hv ↦ ?_⟩,
    fun ⟨h, hz⟩ v t hvt ↦ ?_⟩
  · have := (h v (-1) (by simp [hv])).2
    norm_num at this
  · by_cases ht : t = 0
    · subst ht
      exact ⟨h v (by simpa using hvt), rfl⟩
    · refine absurd ?_ (hz (-t⁻¹ • v))
      rw [map_smul, eq_neg_of_add_eq_zero_left hvt, smul_neg, neg_smul, neg_neg, smul_smul,
        inv_mul_cancel₀ ht, one_smul]

/-- For a source with finite-dimensional model space, the conditions that the differential of a
`Cⁿ` map, `1 ≤ n`, is injective and that a vector field of the target, continuous at the image
of the point, is not in its range both persist near a point where they hold. -/
theorem ContMDiffAt.eventually_injective_mfderiv_and_notMem_range
    (hf : ContMDiffAt I J n f x) (hn : 1 ≤ n)
    (hZ : ContinuousAt (fun y ↦ (⟨y, Z y⟩ : TangentBundle J N)) (f x))
    (hinj : Injective (mfderiv I J f x)) (hZx : Z (f x) ∉ (mfderiv I J f x).range) :
    ∀ᶠ y in 𝓝 x, Injective (mfderiv I J f y) ∧ Z (f y) ∉ (mfderiv I J f y).range := by
  -- A linear map `A` is injective with `z` outside its range exactly when
  -- `(v, t) ↦ A v + t z` is injective.
  have key (A : E →L[ℝ] E') (z : E') :
      Injective (ContinuousLinearMap.coprodEquivL (S := ℝ)
        (A, ContinuousLinearMap.toSpanSingletonCLE z)) ↔ Injective A ∧ z ∉ A.range := by
    convert LinearMap.injective_coprod_toSpanSingleton_iff (A : E →ₗ[ℝ] E') z using 2
    ext p
    simp
  let e₁ := trivializationAt E (TangentSpace I) x
  let e₂ := trivializationAt E' (TangentSpace J) (f x)
  let A := inTangentCoordinates I J id f (mfderiv I J f) x
  let z : M → E' := fun y ↦ (e₂ ⟨f y, Z (f y)⟩).2
  have hA : ContinuousAt A x :=
    (hf.mfderiv_const (m := 0) (by simpa using hn)).continuousAt
  have hz : ContinuousAt z x := by
    have he : ContinuousAt e₂ ⟨f x, Z (f x)⟩ :=
      e₂.continuousOn.continuousAt (e₂.open_source.mem_nhds
        (e₂.mem_source.2 (FiberBundle.mem_baseSet_trivializationAt E' (TangentSpace J) (f x))))
    exact continuous_snd.continuousAt.comp (ContinuousAt.comp (x := x) he (hZ.comp hf.continuousAt))
  let B : M → (E × ℝ) →L[ℝ] E' := fun y ↦
    ContinuousLinearMap.coprodEquivL (S := ℝ) (A y, ContinuousLinearMap.toSpanSingletonCLE (z y))
  have hB : ContinuousAt B x :=
    (ContinuousLinearMap.coprodEquivL (S := ℝ)).continuous.continuousAt.comp (hA.prodMk
      ((ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℝ)).continuous.continuousAt.comp hz))
  have hcoord (y : M) (hx : y ∈ e₁.baseSet) (hy : f y ∈ e₂.baseSet) :
      Injective (B y) ↔ Injective (mfderiv I J f y) ∧ Z (f y) ∉ (mfderiv I J f y).range := by
    let T₁ := e₁.continuousLinearEquivAt ℝ y hx
    let T₂ := e₂.continuousLinearEquivAt ℝ (f y) hy
    have hA' : A y = (T₂ : _ →L[ℝ] E') ∘L mfderiv I J f y ∘L (T₁.symm : E →L[ℝ] _) :=
      ContinuousLinearMap.inCoordinates_eq hx hy
    have hz' : z y = T₂ (Z (f y)) := (e₂.continuousLinearEquivAt_apply' ⟨f y, Z (f y)⟩
      (e₂.mem_source.2 hy)).symm
    simp only [B, key, hA', hz']
    simp only [ContinuousLinearMap.coe_comp, ContinuousLinearEquiv.coe_coe,
      EquivLike.comp_injective, EquivLike.injective_comp, LinearMap.mem_range,
      ContinuousLinearMap.coe_coe, Function.comp_apply]
    refine and_congr_right fun _ ↦ not_congr ⟨fun ⟨v, hv⟩ ↦ ⟨T₁.symm v, T₂.injective hv⟩,
      fun ⟨v, hv⟩ ↦ ⟨T₁ v, by simp [hv]⟩⟩
  have hB0 : Injective (B x) :=
    (hcoord x (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) x)
      (FiberBundle.mem_baseSet_trivializationAt E' (TangentSpace J) (f x))).2 ⟨hinj, hZx⟩
  have hBn := hB.preimage_mem_nhds (ContinuousLinearMap.isOpen_injective.mem_nhds hB0)
  have hxn := e₁.open_baseSet.mem_nhds
    (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) x)
  have hyn := hf.continuousAt.preimage_mem_nhds (e₂.open_baseSet.mem_nhds
    (FiberBundle.mem_baseSet_trivializationAt E' (TangentSpace J) (f x)))
  filter_upwards [hBn, hxn, hyn] with y hy hx hfy
  exact (hcoord y hx hfy).1 hy
