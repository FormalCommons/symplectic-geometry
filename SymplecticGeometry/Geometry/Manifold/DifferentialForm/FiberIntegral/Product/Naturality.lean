/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.FiberIntegral.Product.Basic

/-!
# Naturality of the fibre integral on a product

How the fibre integral `SymplecticGeometry.prodFiberIntegral o` over a compact oriented `F` meets
pull-backs along maps of the base. For a map `f : B' → B`, the product map `Prod.map f id` sends
the lift `(v, 0)` of a base vector to the lift `(df v, 0)` and fixes the vertical vectors
`(0, w)`, so the integrand of the pull-back of `α` at `b'` is the integrand of `α` at `f b'` on
the vectors `df v`. Integrating over `F` gives that the fibre integral commutes with pull-back.

With `f` the inclusion of an open subset `U` of `B` (`U` as a manifold, `f = Subtype.val`), this
says that the fibre integral of the restriction of `α` to `U × F` is the restriction of the
fibre integral of `α` to `U`.

## Main results

* `SymplecticGeometry.prodFiberIntegrand_mpullback_prodMap`: the integrand of the pull-back of `α`
  along `Prod.map f id` at `b'` on `v` is that of `α` at `f b'` on `df v`.
* `SymplecticGeometry.prodFiberIntegral_mpullback_prodMap`: for smooth `f : B' → B`, the fibre
  integral of the pull-back of `α` along `Prod.map f id` is the pull-back along `f` of the fibre
  integral of `α`.

## References

* [R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982], §6.
-/

public section

noncomputable section

open Function
open scoped Manifold ContDiff

namespace SymplecticGeometry

open TauCeti

variable {E H E' H' E'' H'' B F B' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace B] [ChartedSpace H B]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace F] [ChartedSpace H' F]
  [NormedAddCommGroup E''] [NormedSpace ℝ E''] [TopologicalSpace H'']
  {I' : ModelWithCorners ℝ E'' H''} [TopologicalSpace B'] [ChartedSpace H'' B'] {r m : ℕ}

/-- **The integrand of a pull-back along a map of the base.** For `f : B' → B` differentiable at
`b`, the integrand at `b` on `v` of the pull-back of `α` along `Prod.map f id` is the integrand of
`α` at `f b` on the vectors `df v`. -/
theorem prodFiberIntegrand_mpullback_prodMap {f : B' → B} {b : B'}
    (hf : MDifferentiableAt I' I f b) (α : RoughForm (I.prod J) (B × F) ℝ (r + m))
    (v : Fin r → TangentSpace I' b) :
    prodFiberIntegrand (mpullback (I'.prod J) (I.prod J) (Prod.map f id) α) b v =
      prodFiberIntegrand α (f b) fun i ↦ mfderiv I' I f b (v i) := by
  funext y
  ext w
  rw [prodFiberIntegrand_apply, prodFiberIntegrand_apply, mpullback_apply]
  congr 1
  funext p
  rw [Manifold.mfderiv_prodMap_apply (p := (b, y)) hf mdifferentiableAt_id]
  refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) p <;>
    simp only [Fin.append_left, Fin.append_right, mfderiv_id, ContinuousLinearMap.id_apply,
      map_zero, id_eq]

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [FiniteDimensional ℝ E'']
  [IsManifold I ∞ B] [IsManifold J ∞ F] [IsManifold I' ∞ B'] [CompactSpace F] [T2Space F]
  [I.Boundaryless] [I'.Boundaryless]

/-- **The fibre integral commutes with pull-back along maps of the base.** For a smooth map
`f : B' → B` and a smooth form `α` of degree `r + m` on `B × F`, the fibre integral of the
pull-back of `α` along `Prod.map f id : B' × F → B × F` is the pull-back along `f` of the fibre
integral of `α`. For the inclusion of an open subset of `B`, this is the restriction of the fibre
integral to that subset. -/
theorem prodFiberIntegral_mpullback_prodMap (o : Manifold.Orientation J F (Fin m)) {f : B' → B}
    (hf : ContMDiff I' I ∞ f) (α : SmoothForm (I.prod J) (B × F) ℝ (r + m)) :
    prodFiberIntegral o (SmoothForm.mpullback (Prod.map f id) (hf.prodMap contMDiff_id) α) =
      SmoothForm.mpullback f hf (prodFiberIntegral o α) :=
  SmoothBundleForm.ext fun b v ↦ by
    rw [prodFiberIntegral_apply, SmoothForm.coe_mpullback, SmoothForm.coe_mpullback,
      mpullback_apply, prodFiberIntegral_apply,
      prodFiberIntegrand_mpullback_prodMap ((hf b).mdifferentiableAt (by simp))]

end SymplecticGeometry
