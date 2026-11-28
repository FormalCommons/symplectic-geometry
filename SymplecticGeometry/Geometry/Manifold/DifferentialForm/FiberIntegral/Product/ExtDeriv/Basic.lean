/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.FiberIntegral.Product.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Closed
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.FiberIntegral.Product.ExtDeriv.Flat
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.FiberIntegral.Product.Naturality
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Opens
import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset

/-!
# The fibre integral on a product commutes with `d`

Let `B` be a boundaryless manifold, and `F` a compact, Hausdorff, boundaryless manifold of
dimension `m`, oriented by `o`. For a smooth form `α` of degree `r + m` on `B × F`, this file
proves `SymplecticGeometry.prodFiberIntegral_mextDeriv`: `∫_F dα = d ∫_F α`, the degree of `dα`
being cast along `(r + m) + 1 = (r + 1) + m`. It holds for every `m`, including `m = 0`.

The proof reduces to a flat base, where the statement is
`SymplecticGeometry.prodFiberIntegral_mextDeriv_opens`. Both sides are local in the base and
natural under pull-back along maps of the base
(`SymplecticGeometry.prodFiberIntegral_mpullback_prodMap`, with
`TauCeti.SmoothForm.mextDerivₗ_mpullback` and `TauCeti.SmoothForm.mpullback_cast`). So at `b : B`
it is enough to compare their pull-backs to the target of the extended chart at `b`, an open
subset of the model space, along the inverse of the chart
(`TauCeti.SmoothForm.apply_eq_of_mpullback_symm_mpullback_subtypeVal_apply_eq`).

This is the argument of Bott–Tu, §6, that integration along the fibre commutes with `d`.

## References

* [R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982], §6.
-/

public section

noncomputable section

open TopologicalSpace
open scoped Manifold ContDiff

namespace SymplecticGeometry

open TauCeti

variable {E H E' H' B F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace B] [ChartedSpace H B]
  [IsManifold I ∞ B] [BoundarylessManifold I B]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace F] [ChartedSpace H' F] [IsManifold J ∞ F]
  [BoundarylessManifold J F] [T2Space F] [CompactSpace F] {r : ℕ}

/-- **The fibre integral on a product commutes with `d`.** Let `B` be a boundaryless manifold
and `F` a compact, Hausdorff, boundaryless manifold oriented by `o`. For a smooth form `α` of
degree `r + m` on `B × F`, the fibre integral of `dα`, its degree cast along
`(r + m) + 1 = (r + 1) + m`, is `d` of the fibre integral of `α`. -/
theorem prodFiberIntegral_mextDeriv {m : ℕ} (o : Manifold.Orientation J F (Fin m))
    (α : SmoothForm (I.prod J) (B × F) ℝ (r + m)) :
    prodFiberIntegral o (LinearEquiv.cast (R := ℝ)
        (M := fun k ↦ SmoothForm (I.prod J) (B × F) ℝ k)
        (by omega : r + m + 1 = r + 1 + m) (mextDerivₗ (I.prod J) (r + m) α)) =
      mextDerivₗ I r (prodFiberIntegral o α) := by
  refine Subtype.ext (funext fun b ↦ ?_)
  -- The inverse of the extended chart at `b`, as a diffeomorphism from an open subset of `E`.
  let ψ := extChartPartialDiffeomorph I ∞ b
  let Φ := ψ.toDiffeomorphSourceTarget
  have hb : b ∈ ψ.source := by
    simpa [ψ] using BoundarylessManifold.isInteriorPoint (I := I) (x := b)
  refine SmoothForm.apply_eq_of_mpullback_symm_mpullback_subtypeVal_apply_eq Φ ⟨b, hb⟩ ?_
  -- Both sides pulled back along `f`, the inverse of the chart read in `B`.
  let f : (⟨ψ.target, ψ.open_target⟩ : Opens E) → B := Subtype.val ∘ Φ.symm
  have hf : ContMDiff 𝓘(ℝ, E) I ∞ f := contMDiff_subtypeVal.comp Φ.symm.contMDiff
  have hpb (σ : SmoothForm I B ℝ (r + 1)) :
      SmoothForm.mpullback Φ.symm Φ.symm.contMDiff
          (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal σ) =
        SmoothForm.mpullback f hf σ :=
    SmoothForm.mpullback_mpullback _ _ _ _ σ
  rw [hpb, hpb, ← prodFiberIntegral_mpullback_prodMap o hf, SmoothForm.mpullback_cast,
    ← SmoothForm.mextDerivₗ_mpullback, prodFiberIntegral_mextDeriv_opens,
    prodFiberIntegral_mpullback_prodMap o hf, SmoothForm.mextDerivₗ_mpullback]


/-- **The fibre integral of a closed form is closed**, by `prodFiberIntegral_mextDeriv`. -/
theorem isClosed_prodFiberIntegral {m : ℕ} (o : Manifold.Orientation J F (Fin m))
    {α : SmoothForm (I.prod J) (B × F) ℝ (r + m)} (hα : α.IsClosed) :
    (prodFiberIntegral o α).IsClosed := by
  have h0 : mextDerivₗ (I.prod J) (r + m) α = 0 :=
    Subtype.ext ((mextDerivₗ_apply (φ := α) ..).trans ((SmoothForm.isClosed_def α).1 hα))
  rw [SmoothForm.isClosed_def, ← mextDerivₗ_apply, ← prodFiberIntegral_mextDeriv, h0,
    map_zero, map_zero, Submodule.coe_zero]
end SymplecticGeometry

end
