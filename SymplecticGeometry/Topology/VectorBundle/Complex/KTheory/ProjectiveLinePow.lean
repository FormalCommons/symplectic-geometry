/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.CategoryTheory.GrothendieckGroup.Monoidal.Basic
public import TauCeti.Topology.VectorBundle.FiniteRank.Monoidal
public import SymplecticGeometry.Topology.VectorBundle.ProjectiveBundle.Tautological
import SymplecticGeometry.Topology.VectorBundle.Complex.KTheory.ProductSphere
import SymplecticGeometry.Topology.VectorBundle.FiniteRank.Biproduct

/-!
# The line bundles `L_T` over `(ℂP¹)^m` generate `K`

Write `P = ℙ ℂ (Fin 2 → ℂ)` for the complex projective line and `H_i` for the pullback of its
tautological line `Projectivization.tautologicalCore ℂ (Fin 2 → ℂ)` along the evaluation
`ContinuousMap.eval i : (Fin m → P) → P` at the `i`th factor. For a subset `T` of `Fin m`, the
line `L_T` is the tensor product of the `H_i` for `i ∈ T`, taken in the increasing order of
`T`, and the trivial line for `T = ∅`. Its class in the split Grothendieck group
`K((ℂP¹)^m) = TauCeti.SplitK0 (FiniteRankBundleCore ℂ (Fin m → P))` is the product of the classes
of the `H_i`.

The classes of the `2 ^ m` lines `L_T` generate `K((ℂP¹)^m)` as an additive group. This follows
from the surjective half of the product theorem for `X × P`,
`TauCeti.SplitK0.closure_range_of_pullback_fst_union_mul_eq_top`, applied `m` times through the
homeomorphism `(Fin m → P) × P ≃ (Fin (m + 1) → P)` given by `Fin.snoc`, as in
[Hatcher2017, §2.1]. The subsets `T` here are not the integers `m` of the clutched lines `L m` of
`KTheory/ProductSphere.lean`.

## Main definitions and results

* `SymplecticGeometry.Bundle.tensorTautological T`: the line `L_T` over `Fin m → P`;
  `rank_tensorTautological` says that it has rank one.
* `SymplecticGeometry.Bundle.of_tensorTautological`: its class is `∏ i ∈ T, [H_i]`, and
  `of_pullback_tensorTautological` gives the class of its pullback along a continuous map.
* `SymplecticGeometry.Bundle.closure_range_of_tensorTautological_eq_top`: the classes of the
  `L_T` generate `K((ℂP¹)^m)`.

## References

* [A. Hatcher, *Vector Bundles and K-Theory*, version 2.2 (2017)][Hatcher2017], §2.1 (the
  product theorem and `K` of a product of spheres `S²`)
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory TauCeti

open scoped LinearAlgebra.Projectivization

namespace SymplecticGeometry.Bundle

variable {m : ℕ}

/-- The line bundle `L_T` over `(ℂP¹)^m = Fin m → ℙ ℂ (Fin 2 → ℂ)`, for a subset `T` of the
factors: the tensor product, in the increasing order of `T`, of the pullbacks of the tautological
line of `ℙ ℂ (Fin 2 → ℂ)` along the evaluations at the factors `i ∈ T`. For `T = ∅` it is the
trivial line. -/
def tensorTautological (T : Finset (Fin m)) :
    FiniteRankBundleCore ℂ (Fin m → ℙ ℂ (Fin 2 → ℂ)) :=
  (T.sort (· ≤ ·)).foldr
    (fun i A ↦ (Projectivization.tautologicalCore ℂ (Fin 2 → ℂ)).pullback
      (ContinuousMap.eval i) ⊗ A) (𝟙_ _)

theorem tensorTautological_def (T : Finset (Fin m)) :
    tensorTautological T = (T.sort (· ≤ ·)).foldr
      (fun i A ↦ (Projectivization.tautologicalCore ℂ (Fin 2 → ℂ)).pullback
        (ContinuousMap.eval i) ⊗ A) (𝟙_ _) :=
  (rfl)

/-- Each line `L_T` has rank one. -/
@[simp]
theorem rank_tensorTautological (T : Finset (Fin m)) : (tensorTautological T).rank = 1 := by
  rw [tensorTautological_def]
  induction T.sort (· ≤ ·) with
  | nil => exact FiniteRankBundleCore.rank_tensorUnit
  | cons i l ih =>
    rw [List.foldr_cons, FiniteRankBundleCore.rank_tensorObj, ih,
      FiniteRankBundleCore.rank_pullback, Projectivization.rank_tautologicalCore]

/-- The class of `L_T` in `K((ℂP¹)^m)` is the product of the classes of the pullbacks `H_i` of
the tautological line along the evaluations at the factors `i ∈ T`. -/
theorem of_tensorTautological (T : Finset (Fin m)) :
    (SplitK0.of (tensorTautological T) :
      SplitK0 (FiniteRankBundleCore ℂ (Fin m → ℙ ℂ (Fin 2 → ℂ)))) =
      ∏ i ∈ T, SplitK0.of ((Projectivization.tautologicalCore ℂ (Fin 2 → ℂ)).pullback
        (ContinuousMap.eval i)) := by
  conv_rhs => rw [← Finset.sort_toFinset T (· ≤ ·)]
  rw [List.prod_toFinset _ (Finset.sort_nodup T (· ≤ ·)), tensorTautological_def]
  induction T.sort (· ≤ ·) with
  | nil => exact SplitK0.one_def.symm
  | cons i l ih => rw [List.foldr_cons, ← SplitK0.of_mul_of, ih, List.map_cons, List.prod_cons]

/-- The class of the pullback of `L_T` along a continuous map `f : Y → (ℂP¹)^m` is the product of
the classes of the pullbacks of the tautological line along the components `f_i` of `f`, for
`i ∈ T`. -/
theorem of_pullback_tensorTautological {Y : Type} [TopologicalSpace Y]
    (f : C(Y, Fin m → ℙ ℂ (Fin 2 → ℂ))) (T : Finset (Fin m)) :
    (SplitK0.of ((tensorTautological T).pullback f) : SplitK0 (FiniteRankBundleCore ℂ Y)) =
      ∏ i ∈ T, SplitK0.of ((Projectivization.tautologicalCore ℂ (Fin 2 → ℂ)).pullback
        ((ContinuousMap.eval i).comp f)) := by
  rw [← FiniteRankBundleCore.pullbackFunctor_obj, ← SplitK0.mapRingHom_of, of_tensorTautological,
    map_prod]
  simp only [SplitK0.mapRingHom_of, FiniteRankBundleCore.pullback_comp]

/-- Over `(ℂP¹)^0`, a point, the classes of the lines `L_T` generate `K`. -/
private theorem closure_range_of_tensorTautological_eq_top_zero :
    AddSubgroup.closure (Set.range fun T : Finset (Fin 0) ↦
      (SplitK0.of (tensorTautological T) :
        SplitK0 (FiniteRankBundleCore ℂ (Fin 0 → ℙ ℂ (Fin 2 → ℂ))))) = ⊤ := by
  rw [eq_top_iff, ← SplitK0.closure_range_of, AddSubgroup.closure_le]
  rintro _ ⟨A, rfl⟩
  have h1 : (SplitK0.of (FiniteRankBundleCore.trivial ℂ (Fin 0 → ℙ ℂ (Fin 2 → ℂ)) 1) :
      SplitK0 (FiniteRankBundleCore ℂ (Fin 0 → ℙ ℂ (Fin 2 → ℂ)))) = SplitK0.of
        (tensorTautological ∅) := by
    rw [of_tensorTautological, Finset.prod_empty]
    exact SplitK0.one_def.symm
  have hA := FiniteRankBundleCore.pullback_const A (X := Fin 0 → ℙ ℂ (Fin 2 → ℂ)) default
  rw [show ContinuousMap.const _ default = ContinuousMap.id _ from
    ContinuousMap.ext fun _ ↦ Subsingleton.elim _ _, FiniteRankBundleCore.pullback_id] at hA
  rw [SetLike.mem_coe, hA, SplitK0.of_trivial, h1]
  exact nsmul_mem (AddSubgroup.subset_closure (Set.mem_range_self ∅)) _

/-- **The lines `L_T` generate `K((ℂP¹)^m)`.** The additive group of the split Grothendieck
group of complex finite-rank cores over `Fin m → ℙ ℂ (Fin 2 → ℂ)` is generated by the classes of
the lines `L_T`, the tensor products of the pullbacks of the tautological line along the
evaluations at the factors in `T`, for the subsets `T` of `Fin m`. -/
theorem closure_range_of_tensorTautological_eq_top (m : ℕ) :
    AddSubgroup.closure (Set.range fun T : Finset (Fin m) ↦
      (SplitK0.of (tensorTautological T) :
        SplitK0 (FiniteRankBundleCore ℂ (Fin m → ℙ ℂ (Fin 2 → ℂ))))) = ⊤ := by
  induction m with
  | zero => exact closure_range_of_tensorTautological_eq_top_zero
  | succ m ih =>
    -- The homeomorphism `(Fin m → P) × P ≃ (Fin (m + 1) → P)` given by `Fin.snoc`.
    let φ : C((Fin m → ℙ ℂ (Fin 2 → ℂ)) × ℙ ℂ (Fin 2 → ℂ), Fin (m + 1) → ℙ ℂ (Fin 2 → ℂ)) :=
      ⟨fun z ↦ Fin.snoc z.1 z.2, by fun_prop⟩
    let ψ : C(Fin (m + 1) → ℙ ℂ (Fin 2 → ℂ), (Fin m → ℙ ℂ (Fin 2 → ℂ)) × ℙ ℂ (Fin 2 → ℂ)) :=
      ⟨fun z ↦ (Fin.init z, z (Fin.last m)),
        (continuous_pi fun i ↦ continuous_apply _).prodMk (continuous_apply _)⟩
    have hφψ : φ.comp ψ = ContinuousMap.id _ := by
      ext z : 1
      exact Fin.snoc_init_self z
    have hfst (i : Fin m) : (ContinuousMap.eval i).comp (ContinuousMap.fst.comp ψ) =
        ContinuousMap.eval (Fin.castSucc i) := rfl
    have hsnd : ContinuousMap.snd.comp ψ = ContinuousMap.eval (Fin.last m) := rfl
    set S := AddSubgroup.closure (Set.range fun T : Finset (Fin (m + 1)) ↦
      (SplitK0.of (tensorTautological T) :
        SplitK0 (FiniteRankBundleCore ℂ (Fin (m + 1) → ℙ ℂ (Fin 2 → ℂ)))))
    -- Pulling back to `Fin (m + 1) → P` along the first `m` coordinates, and multiplying by
    -- `[H_m]`, both take `K((ℂP¹)^m)` into `S`, since they take `L_T` to `L_{T'}`.
    let Φ : SplitK0 (FiniteRankBundleCore ℂ (Fin m → ℙ ℂ (Fin 2 → ℂ))) →+*
        SplitK0 (FiniteRankBundleCore ℂ (Fin (m + 1) → ℙ ℂ (Fin 2 → ℂ))) :=
      SplitK0.mapRingHom (FiniteRankBundleCore.pullbackFunctor (ContinuousMap.fst.comp ψ))
    have hΦ (T : Finset (Fin m)) :
        Φ (SplitK0.of (tensorTautological T)) =
          SplitK0.of (tensorTautological (T.map Fin.castSuccEmb)) := by
      rw [SplitK0.mapRingHom_of, FiniteRankBundleCore.pullbackFunctor_obj,
        of_pullback_tensorTautological, of_tensorTautological, Finset.prod_map]
      simp only [hfst, Fin.coe_castSuccEmb]
    have hH : (SplitK0.of ((Projectivization.tautologicalCore ℂ (Fin 2 → ℂ)).pullback
        (ContinuousMap.eval (Fin.last m))) :
          SplitK0 (FiniteRankBundleCore ℂ (Fin (m + 1) → ℙ ℂ (Fin 2 → ℂ)))) =
          SplitK0.mapRingHom (FiniteRankBundleCore.pullbackFunctor ψ)
            (SplitK0.of ((Projectivization.tautologicalCore ℂ (Fin 2 → ℂ)).pullback
              ContinuousMap.snd)) := by
      rw [SplitK0.mapRingHom_of, FiniteRankBundleCore.pullbackFunctor_obj,
        FiniteRankBundleCore.pullback_comp, hsnd]
    have hΦH (T : Finset (Fin m)) :
        Φ (SplitK0.of (tensorTautological T)) *
          SplitK0.of ((Projectivization.tautologicalCore ℂ (Fin 2 → ℂ)).pullback
            (ContinuousMap.eval (Fin.last m))) =
          SplitK0.of (tensorTautological ((T.map Fin.castSuccEmb).cons (Fin.last m)
            (by simp [Fin.castSucc_ne_last]))) := by
      rw [hΦ, of_tensorTautological, of_tensorTautological, Finset.prod_cons, mul_comm]
    have h₀ (x) : Φ x ∈ S := by
      refine (AddSubgroup.closure_le (S.comap Φ.toAddMonoidHom)).2 ?_ (ih ▸ AddSubgroup.mem_top x)
      rintro _ ⟨T, rfl⟩
      exact AddSubgroup.subset_closure ⟨_, (hΦ T).symm⟩
    have h₁ (x) : Φ x * SplitK0.of ((Projectivization.tautologicalCore ℂ (Fin 2 → ℂ)).pullback
        (ContinuousMap.eval (Fin.last m))) ∈ S := by
      refine (AddSubgroup.closure_le (S.comap ((AddMonoidHom.mulRight _).comp
        Φ.toAddMonoidHom))).2 ?_ (ih ▸ AddSubgroup.mem_top x)
      rintro _ ⟨T, rfl⟩
      exact AddSubgroup.subset_closure ⟨_, (hΦH T).symm⟩
    -- Every class `x` is the pullback along `ψ` of its pullback along `φ`, which the product
    -- theorem writes in terms of the classes `[p*A]` and `[p*A] * [H]`.
    rw [eq_top_iff]
    rintro x -
    have hx : x = SplitK0.mapRingHom (FiniteRankBundleCore.pullbackFunctor ψ)
        (SplitK0.mapRingHom (FiniteRankBundleCore.pullbackFunctor φ) x) := by
      induction x using SplitK0.induction_on with
      | zero => simp
      | of A => rw [SplitK0.mapRingHom_of, SplitK0.mapRingHom_of,
          FiniteRankBundleCore.pullbackFunctor_obj, FiniteRankBundleCore.pullbackFunctor_obj,
          FiniteRankBundleCore.pullback_comp, hφψ, FiniteRankBundleCore.pullback_id]
      | add x y hx hy => rw [map_add, map_add, ← hx, ← hy]
      | neg x hx => rw [map_neg, map_neg, ← hx]
    have hgen := SplitK0.closure_range_of_pullback_fst_union_mul_eq_top
      (X := Fin m → ℙ ℂ (Fin 2 → ℂ))
    rw [hx]
    refine (AddSubgroup.closure_le (S.comap (SplitK0.mapRingHom
      (FiniteRankBundleCore.pullbackFunctor ψ)).toAddMonoidHom)).2 ?_
      (hgen ▸ AddSubgroup.mem_top _)
    rintro _ (⟨A, rfl⟩ | ⟨A, rfl⟩)
    · have := h₀ (SplitK0.of A)
      rwa [SplitK0.mapRingHom_of, FiniteRankBundleCore.pullbackFunctor_obj,
        ← FiniteRankBundleCore.pullback_comp, ← FiniteRankBundleCore.pullbackFunctor_obj,
        ← SplitK0.mapRingHom_of] at this
    · have := h₁ (SplitK0.of A)
      rwa [hH, SplitK0.mapRingHom_of, FiniteRankBundleCore.pullbackFunctor_obj,
        ← FiniteRankBundleCore.pullback_comp, ← FiniteRankBundleCore.pullbackFunctor_obj,
        ← SplitK0.mapRingHom_of, ← map_mul] at this

end SymplecticGeometry.Bundle

end

end
