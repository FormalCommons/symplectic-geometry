/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.FiberIntegral.Basic
public import TauCeti.Geometry.Manifold.DeRham.Basic
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Components
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.FiberIntegral.Product.ExtDeriv.Basic
import TauCeti.Geometry.Manifold.DifferentialForm.Naturality

/-!
# Calculus of the fibre integral of a fibration

Let `A` be a smooth atlas of `proj : M → B` whose coordinate changes preserve an orientation `o`
of the compact, Hausdorff, boundaryless model fibre `F`, with `B` boundaryless. This file proves
that the fibre integral `TauCeti.MapFiber.Atlas.fiberIntegral A hA ho` commutes with the exterior
derivative (`TauCeti.MapFiber.Atlas.fiberIntegral_mextDeriv`), the degree of `dα` being cast
along `(r + m) + 1 = (r + 1) + m`; so the fibre integral of a closed form is closed.

Both sides are smooth forms on `B`, and such forms are equal once their restrictions to the base
sets of the charts `A.trivAt b'` agree (`TauCeti.SmoothForm.ext_of_mpullback_subtype_val`). On
such a base set `U` the fibre integral is the fibre integral on the product `U × F` of the
pull-back along `(b, y) ↦ e⁻¹ (b, y)`
(`TauCeti.MapFiber.Atlas.mpullback_subtype_val_fiberIntegral`). Pull-back along smooth maps
commutes with `d` (`TauCeti.SmoothForm.mextDerivₗ_mpullback`), and on a product the statement is
`SymplecticGeometry.prodFiberIntegral_mextDeriv`.

This is the argument of Bott–Tu, §6, that integration along the fibre commutes with `d`.

## Main results

* `TauCeti.MapFiber.Atlas.fiberIntegral_mextDeriv`: the fibre integral commutes with `d`.
* `TauCeti.MapFiber.Atlas.fiberIntegral_mem_closedForms`: the fibre integral of a closed form is
  closed.

## References

* [R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982], §6.
-/

public section

open scoped Manifold ContDiff

variable {E H E' H' EM HM B F M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace B]
  [ChartedSpace H B] [IsManifold I ∞ B] [BoundarylessManifold I B]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace F] [ChartedSpace H' F] [IsManifold J ∞ F]
  [BoundarylessManifold J F] [T2Space F] [CompactSpace F]
  [NormedAddCommGroup EM] [NormedSpace ℝ EM] [TopologicalSpace HM]
  {IM : ModelWithCorners ℝ EM HM} [TopologicalSpace M] [ChartedSpace HM M] [IsManifold IM 2 M]
  {proj : M → B} {r m : ℕ}

namespace TauCeti.MapFiber.Atlas

open SymplecticGeometry

variable {A : Atlas F proj} {o : Manifold.Orientation J F (Fin m)} (hA : A.IsContMDiff ∞ I J IM)
  {hn : (∞ : ℕ∞ω) ≠ 0} (ho : A.HasStructureGroup (Diffeomorph.orientationPreservingSubgroup hn o))

/-- **The fibre integral commutes with `d`.** Let `A` be a smooth atlas of `proj : M → B` whose
coordinate changes preserve the orientation `o` of the compact, Hausdorff, boundaryless model
fibre `F`, with `B` boundaryless. For a smooth form `α` of degree `r + m` on `M`, the fibre
integral of `dα`, its degree cast along `(r + m) + 1 = (r + 1) + m`, is `d` of the fibre integral
of `α`. -/
theorem fiberIntegral_mextDeriv (α : SmoothForm IM M ℝ (r + m)) :
    A.fiberIntegral hA ho (LinearEquiv.cast (R := ℝ) (M := fun k ↦ SmoothForm IM M ℝ k)
        (by omega : r + m + 1 = r + 1 + m) (mextDerivₗ IM (r + m) α)) =
      mextDerivₗ I r (A.fiberIntegral hA ho α) := by
  refine SmoothForm.ext_of_mpullback_subtype_val A.isOpenCover_baseSet_trivAt fun b' ↦ ?_
  rw [mpullback_subtype_val_fiberIntegral, SmoothForm.mpullback_cast,
    ← SmoothForm.mextDerivₗ_mpullback, prodFiberIntegral_mextDeriv,
    ← SmoothForm.mextDerivₗ_mpullback, mpullback_subtype_val_fiberIntegral]

/-- **The fibre integral of a closed form is closed.** Under the hypotheses of
`TauCeti.MapFiber.Atlas.fiberIntegral_mextDeriv`, the fibre integral of a closed form of degree
`r + m` on `M` is a closed `r`-form on `B`. -/
theorem fiberIntegral_mem_closedForms {α : SmoothForm IM M ℝ (r + m)}
    (hα : α ∈ closedForms IM M (r + m)) : A.fiberIntegral hA ho α ∈ closedForms I B r := by
  rw [mem_closedForms_iff_mextDerivₗ_eq_zero] at hα ⊢
  rw [← fiberIntegral_mextDeriv, hα, map_zero, map_zero]

end TauCeti.MapFiber.Atlas

end
