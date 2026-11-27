/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.FiberIntegral.Product.Basic
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Smooth
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.ExtDeriv
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.FiberIntegral.Product.ExtDeriv.BaseDeriv
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.FiberIntegral.Product.ExtDeriv.Integrand
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.BoundarylessStokes
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Regularity

/-!
# The fibre integral commutes with `d` over an open subset of a normed space

Let `U` be an open subset of a finite-dimensional normed space `E`, with the model `𝓘(ℝ, E)`, and
let `F` be a compact, Hausdorff, boundaryless manifold of dimension `m`, oriented by `o`. For a
smooth form `α` of degree `r + m` on `U × F`, this file proves
`SymplecticGeometry.prodFiberIntegral_mextDeriv_opens`:
`∫_F dα = d ∫_F α`, the degree of `dα` being cast along `(r + m) + 1 = (r + 1) + m`. It holds for
every `m`, including `m = 0`.

The proof integrates over `F` the pointwise formula for the integrand of `dα`
(`SymplecticGeometry.prodFiberIntegrand_cast_mextDerivₗ_apply_succ` and
`SymplecticGeometry.prodFiberIntegrand_cast_mextDerivₗ_apply_zero`). Its base terms integrate to
the derivatives in the base of the fibre integrals
(`SymplecticGeometry.mfderiv_integralTopForm_prodFiberIntegrand_apply`), whose alternating sum is
`d ∫_F α` (`TauCeti.mextDeriv_opens_apply`). For `m = n + 1` the remaining term is the exterior
derivative of an `n`-form on `F`, whose integral vanishes by Stokes's theorem on the closed
manifold `F` (`TauCeti.integralTopForm_mextDeriv_eq_zero`).

This is the case of a flat base of the argument of Bott–Tu, §6, that integration along the fibre
commutes with `d`.

## References

* [R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982], §6.
-/

public section

noncomputable section

open TopologicalSpace
open scoped Manifold ContDiff

namespace SymplecticGeometry

open TauCeti

variable {E E' H' F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace F] [ChartedSpace H' F] [IsManifold J ∞ F]
  [BoundarylessManifold J F] [T2Space F] [CompactSpace F] {U : Opens E} {r : ℕ}

/-- The derivative at `b`, in the direction `a`, of the integrands
`b' ↦ prodFiberIntegrand α b' u`, as a smooth form on `F`. -/
private def mfderivIntegrand {m : ℕ}
    (α : SmoothForm (𝓘(ℝ, E).prod J) (U × F) ℝ (r + m)) (u : Fin r → E) (b : U) (a : E) :
    SmoothForm J F ℝ m :=
  ⟨_, (isSmoothForm_mfderiv_prodFiberIntegrand α u b a).mem_smoothBundleForms⟩

omit [FiniteDimensional ℝ E] [BoundarylessManifold J F] [T2Space F] [CompactSpace F] in
/-- The value of `mfderivIntegrand α u b a` at `y`. -/
private theorem mfderivIntegrand_apply {m : ℕ}
    (α : SmoothForm (𝓘(ℝ, E).prod J) (U × F) ℝ (r + m)) (u : Fin r → E) (b : U) (a : E)
    (y : F) :
    (mfderivIntegrand α u b a).val y =
      show E' [⋀^Fin m]→L[ℝ] ℝ from mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E' [⋀^Fin m]→L[ℝ] ℝ)
        (fun b' : U ↦ show E' [⋀^Fin m]→L[ℝ] ℝ from prodFiberIntegrand α.val b' u y) b a :=
  rfl

omit [BoundarylessManifold J F] in
/-- The integral over `F` of `mfderivIntegrand α u b a` is the derivative at `b`, in the
direction `a`, of the fibre integral of `α` on `u`. -/
private theorem integralTopFormₗ_mfderivIntegrand {m : ℕ} (o : Manifold.Orientation J F (Fin m))
    (α : SmoothForm (𝓘(ℝ, E).prod J) (U × F) ℝ (r + m)) (u : Fin r → E) (b : U) (a : E) :
    SmoothForm.integralTopFormₗ o (mfderivIntegrand α u b a) =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ) (fun b' : U ↦ (prodFiberIntegral o α).val b' u) b a := by
  have h : (fun b' : U ↦ (prodFiberIntegral o α).val b' u) =
      fun b' ↦ integralTopForm o (prodFiberIntegrand α.val b' u) :=
    funext fun b' ↦ prodFiberIntegral_apply o α b' u
  rw [SmoothForm.integralTopFormₗ_apply, h]
  exact (mfderiv_integralTopForm_prodFiberIntegrand_apply o α u b a).symm

omit [BoundarylessManifold J F] in
/-- The alternating sum over `i` of the forms `mfderivIntegrand α (v without vᵢ) b vᵢ` takes,
at `y` on `w`, the alternating sum of the values of the base derivatives of the integrands, and
its integral over `F` is the alternating sum of the base derivatives of the fibre integrals. -/
private theorem sum_mfderivIntegrand {m : ℕ} (o : Manifold.Orientation J F (Fin m))
    (α : SmoothForm (𝓘(ℝ, E).prod J) (U × F) ℝ (r + m)) (b : U) (v : Fin (r + 1) → E) :
    (∀ (y : F) (w : Fin m → TangentSpace J y),
      (∑ i : Fin (r + 1), (-1 : ℤ) ^ (i : ℕ) •
        mfderivIntegrand α (Fin.removeNth i v) b (v i)).val y w =
      ∑ i : Fin (r + 1), (-1 : ℤ) ^ (i : ℕ) • (show E' [⋀^Fin m]→L[ℝ] ℝ from
        mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E' [⋀^Fin m]→L[ℝ] ℝ)
          (fun b' : U ↦ show E' [⋀^Fin m]→L[ℝ] ℝ from
            prodFiberIntegrand α.val b' (Fin.removeNth i v) y) b (v i)) w) ∧
    SmoothForm.integralTopFormₗ o (∑ i : Fin (r + 1), (-1 : ℤ) ^ (i : ℕ) •
        mfderivIntegrand α (Fin.removeNth i v) b (v i)) =
      ∑ i : Fin (r + 1), (-1 : ℤ) ^ (i : ℕ) • mfderiv 𝓘(ℝ, E) 𝓘(ℝ)
        (fun b' : U ↦ (prodFiberIntegral o α).val b' (Fin.removeNth i v)) b (v i) := by
  refine ⟨fun y w ↦ ?_, ?_⟩
  · rw [SmoothBundleForm.sum_apply, ContinuousAlternatingMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [SmoothBundleForm.smul_apply, ContinuousAlternatingMap.smul_apply,
      mfderivIntegrand_apply]
    -- The sides differ only in reading `w` in `TangentSpace J y` or in `E'`, which agree.
    rfl
  · rw [map_sum]
    exact Finset.sum_congr rfl fun i _ ↦
      (map_zsmul _ _ _).trans (congrArg _ (integralTopFormₗ_mfderivIntegrand o α _ b _))

/-- **The fibre integral commutes with `d` over an open subset of a normed space.** Let `U` be an
open subset of a finite-dimensional normed space `E`, and `F` a compact, Hausdorff, boundaryless
manifold oriented by `o`. For a smooth form `α` of degree `r + m` on `U × F`, the fibre integral
of `dα`, its degree cast along `(r + m) + 1 = (r + 1) + m`, is `d` of the fibre integral of
`α`. -/
theorem prodFiberIntegral_mextDeriv_opens {m : ℕ} (o : Manifold.Orientation J F (Fin m))
    (α : SmoothForm (𝓘(ℝ, E).prod J) (U × F) ℝ (r + m)) :
    prodFiberIntegral o (LinearEquiv.cast (R := ℝ)
        (M := fun k ↦ SmoothForm (𝓘(ℝ, E).prod J) (U × F) ℝ k)
        (by omega : r + m + 1 = r + 1 + m) (mextDerivₗ (𝓘(ℝ, E).prod J) (r + m) α)) =
      mextDerivₗ 𝓘(ℝ, E) r (prodFiberIntegral o α) := by
  refine SmoothBundleForm.ext fun b v ↦ ?_
  rw [prodFiberIntegral_apply, mextDerivₗ_apply]
  -- Read the tangent vectors at `b` as vectors of `E`, as the pointwise formulas take them.
  revert v
  refine fun (v : Fin (r + 1) → E) ↦ ?_
  rw [mextDeriv_opens_apply
      ((prodFiberIntegral o α).isSmoothForm.mdifferentiableAt_opens (by simp) b) v,
    ← (sum_mfderivIntegrand o α b v).2, SmoothForm.integralTopFormₗ_apply]
  obtain _ | n := m
  · congr 1
    funext y
    refine ContinuousAlternatingMap.ext fun (w : Fin 0 → TangentSpace J y) ↦ ?_
    exact (prodFiberIntegrand_cast_mextDerivₗ_apply_zero α b v y w).trans
      ((sum_mfderivIntegrand o α b v).1 y w).symm
  · set β : SmoothForm J F ℝ n := ⟨_, (isSmoothForm_prodFiberIntegrand
      (LinearEquiv.cast (R := ℝ) (M := fun k ↦ SmoothForm (𝓘(ℝ, E).prod J) (U × F) ℝ k)
        (by omega : r + (n + 1) = r + 1 + n) α).isSmoothForm b v).mem_smoothBundleForms⟩
    have h : prodFiberIntegrand (LinearEquiv.cast (R := ℝ)
        (M := fun k ↦ SmoothForm (𝓘(ℝ, E).prod J) (U × F) ℝ k)
        (by omega : r + (n + 1) + 1 = r + 1 + (n + 1))
        (mextDerivₗ (𝓘(ℝ, E).prod J) (r + (n + 1)) α)).val b v =
        (∑ i : Fin (r + 1), (-1 : ℤ) ^ (i : ℕ) •
          mfderivIntegrand α (Fin.removeNth i v) b (v i) +
          (-1 : ℤ) ^ (r + 1) • mextDerivₗ J n β : SmoothForm J F ℝ (n + 1)).val := by
      funext y
      refine ContinuousAlternatingMap.ext fun (w : Fin (n + 1) → TangentSpace J y) ↦ ?_
      refine (prodFiberIntegrand_cast_mextDerivₗ_apply_succ α b v y w).trans ?_
      simp only [SmoothBundleForm.add_apply, ContinuousAlternatingMap.add_apply,
        (sum_mfderivIntegrand o α b v).1 y w, SmoothBundleForm.smul_apply,
        ContinuousAlternatingMap.smul_apply, mextDerivₗ_apply]
      -- `β` is, by its definition, the integrand `prodFiberIntegrand (cast α) b v`.
      rfl
    rw [h, ← SmoothForm.integralTopFormₗ_apply, ← SmoothForm.integralTopFormₗ_apply, map_add,
      map_zsmul, SmoothForm.integralTopFormₗ_apply o (mextDerivₗ J n β), mextDerivₗ_apply,
      integralTopForm_mextDeriv_eq_zero o (SmoothForm.isSmoothForm _ |>.of_le (by simp))
        (isClosed_tsupport _).isCompact, smul_zero, add_zero]

end SymplecticGeometry

end
