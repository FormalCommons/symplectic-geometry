/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.FiberBundle.MapFiber
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.SmoothFamily.Basic

/-!
# Fibre restrictions of a form along a trivialization

Let `e : Trivialization F proj` be a trivialization of a map `proj : M → B` whose inverse is
smooth on its target, and `U` an open set of `B` inside the base set of `e`. A smooth form `τ` on
`M` restricts to each fibre over a point `p` of `U`, read through `e`, as its pull-back along the
fibre inclusion `e.fiberInclusionMap`. These restrictions are the slices of one smooth form on
`U × F`, the pull-back of `τ` along `(p, v) ↦ e⁻¹ (p, v)`
(`Bundle.Trivialization.contMDiff_symm_val_prod`), so they form a smooth family over `U`.

## Main results

* `Bundle.Trivialization.mpullback_prodMk_mpullback_symm`: the slice at `p` of the pull-back of
  `τ` along `(p, v) ↦ e⁻¹ (p, v)` is the restriction of `τ` to the fibre over `p`.
* `Bundle.Trivialization.isSmoothFamily_mpullback_fiberInclusionMap`: the restrictions of `τ` to
  the fibres over `U` form a smooth family over `U`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §6.1.
-/

public section

noncomputable section

open SymplecticGeometry TauCeti
open scoped Manifold ContDiff

namespace Bundle.Trivialization

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] {HB : Type*}
  [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {B : Type*} [TopologicalSpace B]
  [ChartedSpace HB B] [IsManifold IB 1 B]
  {EF : Type*} [NormedAddCommGroup EF] [NormedSpace ℝ EF] {HF : Type*} [TopologicalSpace HF]
  {IF : ModelWithCorners ℝ EF HF} {F : Type*} [TopologicalSpace F] [ChartedSpace HF F]
  [IsManifold IF 1 F]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners ℝ EM HM} {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  [IsManifold IM 1 M]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {k : ℕ}
  {proj : M → B} (e : Trivialization F proj)

/-- **Slices of the pull-back along a trivialization.** For a trivialization `e` whose inverse is
smooth on its target and an open set `U` inside its base set, the slice at a point `p` of `U` of
the pull-back of a smooth form `τ` on `M` along `(p, v) ↦ e⁻¹ (p, v)` is the pull-back of `τ`
along the fibre inclusion of `e` over `p`. -/
theorem mpullback_prodMk_mpullback_symm
    (he : ContMDiffOn (IB.prod IF) IM ∞ e.toOpenPartialHomeomorph.symm e.target)
    {U : TopologicalSpace.Opens B} (hU : (U : Set B) ⊆ e.baseSet) (τ : SmoothForm IM M G k)
    (p : U) :
    SmoothForm.mpullback (Prod.mk p) (contMDiff_const.prodMk contMDiff_id)
        (SmoothForm.mpullback _ (e.contMDiff_symm_val_prod he hU) τ) =
      SmoothForm.mpullback (e.fiberInclusionMap (hU p.property))
        (e.contMDiff_fiberInclusionMap he (hU p.property)) τ := by
  rw [SmoothForm.mpullback_mpullback]
  exact SmoothForm.mpullback_congr _ _ (e.coe_fiberInclusionMap (hU p.property)).symm τ

/-- **Fibre restrictions form a smooth family.** For a trivialization `e` whose inverse is smooth
on its target, an open set `U` inside its base set and a smooth form `τ` on `M`, the pull-backs
of `τ` along the fibre inclusions of `e` over the points of `U` form a smooth family over `U`:
they are the slices of the pull-back of `τ` along `(p, v) ↦ e⁻¹ (p, v)`
(`Bundle.Trivialization.mpullback_prodMk_mpullback_symm`). -/
theorem isSmoothFamily_mpullback_fiberInclusionMap
    (he : ContMDiffOn (IB.prod IF) IM ∞ e.toOpenPartialHomeomorph.symm e.target)
    {U : TopologicalSpace.Opens B} (hU : (U : Set B) ⊆ e.baseSet) (τ : SmoothForm IM M G k) :
    IsSmoothFamily IB fun p : U ↦ SmoothForm.mpullback (e.fiberInclusionMap (hU p.property))
      (e.contMDiff_fiberInclusionMap he (hU p.property)) τ :=
  isSmoothFamily_def.2 ⟨_, e.mpullback_prodMk_mpullback_symm he hU τ⟩

end Bundle.Trivialization

end
