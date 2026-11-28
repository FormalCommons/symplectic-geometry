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
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.FiberIntegral.Product.Naturality
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.ChangeOfVariables
import TauCeti.Geometry.Manifold.DifferentialForm.Naturality

/-!
# Calculus of the fibre integral of a fibration

Let `A` be a smooth atlas of `proj : M → B` whose coordinate changes preserve an orientation `o`
of the compact, Hausdorff, boundaryless model fibre `F`, with `B` boundaryless. This file proves
that the fibre integral `TauCeti.MapFiber.Atlas.fiberIntegral A hA ho` commutes with the exterior
derivative (`TauCeti.MapFiber.Atlas.fiberIntegral_mextDeriv`), the degree of `dα` being cast
along `(r + m) + 1 = (r + 1) + m`; so the fibre integral of a closed form is closed. It also
proves the projection formula `TauCeti.MapFiber.Atlas.fiberIntegral_wedge_mpullback`: the fibre
integral of `proj^* β ∧ α` is `β ∧` the fibre integral of `α`, the degree cast along
`p + (q + m) = (p + q) + m`.

Both sides are smooth forms on `B`, and such forms are equal once their restrictions to the base
sets of the charts `A.trivAt b'` agree (`TauCeti.SmoothForm.ext_of_mpullback_subtypeVal`). On
such a base set `U` the fibre integral is the fibre integral on the product `U × F` of the
pull-back along `(b, y) ↦ e⁻¹ (b, y)`
(`TauCeti.MapFiber.Atlas.mpullback_subtypeVal_fiberIntegral`). Pull-back along smooth maps
commutes with `d` (`TauCeti.SmoothForm.mextDerivₗ_mpullback`), and on a product the statement is
`SymplecticGeometry.prodFiberIntegral_mextDeriv`. For the projection formula, pull-back
commutes with the wedge product (`TauCeti.SmoothForm.mpullback_wedge`), `proj ∘ e⁻¹` is the
first projection on `U × F`, and on a product the statement is
`SymplecticGeometry.prodFiberIntegral_wedge_mpullback_fst`.

The fibre integral is natural along maps of fibrations
(`TauCeti.MapFiber.Atlas.fiberIntegral_mpullback`): for a second such atlas `A₁` of
`proj₁ : M₁ → B₁`, oriented by the same `o`, and smooth maps `g : M₁ → M` and `f : B₁ → B` with
`proj ∘ g = f ∘ proj₁` whose fibre maps, read in the charts at `b₁` and at `f b₁`, are
diffeomorphisms of `F` preserving `o`, the fibre integral of `g^* α` is `f^*` of the fibre
integral of `α`. At each point `b₁`, the integrand of `g^* α` read in the chart at `b₁` is the
pull-back along the fibre map of the integrand of `α` over `f b₁` read in the chart at `f b₁`
(`Bundle.Trivialization.fiberIntegrand_mpullback`, in
`SymplecticGeometry.Geometry.Manifold.DifferentialForm.FiberIntegral.Basic`), and change of
variables over `F`
(`Topology.IsOpenEmbedding.integralTopForm_mpullback_of_isOrientationPreservingAt`) ends the
proof.

This is the argument of Bott–Tu, §6, that integration along the fibre commutes with `d`, and their
reduction of the projection formula to a product.

## Main results

* `TauCeti.MapFiber.Atlas.fiberIntegral_mextDeriv`: the fibre integral commutes with `d`.
* `TauCeti.MapFiber.Atlas.fiberIntegral_mem_closedForms`: the fibre integral of a closed form is
  closed.
* `TauCeti.MapFiber.Atlas.fiberIntegral_wedge_mpullback`: the projection formula.
* `TauCeti.MapFiber.Atlas.fiberIntegral_mpullback`: naturality along maps of fibrations.

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
  {IM : ModelWithCorners ℝ EM HM} [TopologicalSpace M] [ChartedSpace HM M] [IsManifold IM 1 M]
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
theorem fiberIntegral_mextDeriv [IsManifold IM 2 M] (α : SmoothForm IM M ℝ (r + m)) :
    A.fiberIntegral hA ho (LinearEquiv.cast (R := ℝ) (M := fun k ↦ SmoothForm IM M ℝ k)
        (by omega : r + m + 1 = r + 1 + m) (mextDerivₗ IM (r + m) α)) =
      mextDerivₗ I r (A.fiberIntegral hA ho α) := by
  refine SmoothForm.ext_of_mpullback_subtypeVal A.isOpenCover_baseSet_trivAt fun b' ↦ ?_
  rw [mpullback_subtypeVal_fiberIntegral, SmoothForm.mpullback_cast,
    ← SmoothForm.mextDerivₗ_mpullback, prodFiberIntegral_mextDeriv,
    ← SmoothForm.mextDerivₗ_mpullback, mpullback_subtypeVal_fiberIntegral]

/-- **The fibre integral of a closed form is closed.** Under the hypotheses of
`TauCeti.MapFiber.Atlas.fiberIntegral_mextDeriv`, the fibre integral of a closed form of degree
`r + m` on `M` is a closed `r`-form on `B`. -/
theorem fiberIntegral_mem_closedForms [IsManifold IM 2 M] {α : SmoothForm IM M ℝ (r + m)}
    (hα : α ∈ closedForms IM M (r + m)) : A.fiberIntegral hA ho α ∈ closedForms I B r := by
  rw [mem_closedForms_iff_mextDerivₗ_eq_zero] at hα ⊢
  rw [← fiberIntegral_mextDeriv, hα, map_zero, map_zero]

omit [BoundarylessManifold J F] in
/-- **The projection formula.** Let `A` be a smooth atlas of `proj : M → B` whose coordinate
changes preserve the orientation `o` of the compact Hausdorff model fibre `F`, with `B`
boundaryless. For a smooth form `β` of degree `p` on `B` and a smooth form `α` of degree
`q + m` on `M`, the fibre integral of `proj^* β ∧ α`, its degree cast along
`p + (q + m) = (p + q) + m`, is `β ∧` the fibre integral of `α`. -/
theorem fiberIntegral_wedge_mpullback {p q : ℕ} (β : SmoothForm I B ℝ p)
    (α : SmoothForm IM M ℝ (q + m)) :
    A.fiberIntegral hA ho (LinearEquiv.cast (R := ℝ) (M := fun k ↦ SmoothForm IM M ℝ k)
        (Nat.add_assoc p q m).symm
        (SmoothForm.wedge (SmoothForm.mpullback proj hA.contMDiff_proj β) α)) =
      SmoothForm.wedge β (A.fiberIntegral hA ho α) := by
  refine SmoothForm.ext_of_mpullback_subtypeVal A.isOpenCover_baseSet_trivAt fun b' ↦ ?_
  rw [mpullback_subtypeVal_fiberIntegral, SmoothForm.mpullback_cast, SmoothForm.mpullback_wedge,
    SmoothForm.mpullback_mpullback_of_comp_eq ((A.trivAt b').contMDiff_symm_val_prod
      (hA.contMDiffOn_trivAt_symm b') subset_rfl) hA.contMDiff_proj contMDiff_fst
      contMDiff_subtypeVal (funext fun x ↦ (A.trivAt b').proj_symm_apply
        ((A.trivAt b').mem_target.2 x.1.property)),
    prodFiberIntegral_wedge_mpullback_fst, SmoothForm.mpullback_wedge,
    mpullback_subtypeVal_fiberIntegral]

end TauCeti.MapFiber.Atlas

/-! ### Naturality along maps of fibrations -/

variable {E₁ H₁ EM₁ HM₁ B₁ M₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [TopologicalSpace H₁] {I₁ : ModelWithCorners ℝ E₁ H₁} [TopologicalSpace B₁]
  [ChartedSpace H₁ B₁] [NormedAddCommGroup EM₁] [NormedSpace ℝ EM₁] [TopologicalSpace HM₁]
  {IM₁ : ModelWithCorners ℝ EM₁ HM₁} [TopologicalSpace M₁] [ChartedSpace HM₁ M₁]
  {proj₁ : M₁ → B₁}

namespace TauCeti.MapFiber.Atlas

open SymplecticGeometry

variable [FiniteDimensional ℝ E₁] [IsManifold I₁ ∞ B₁] [BoundarylessManifold I₁ B₁]
  [IsManifold IM₁ 1 M₁] {A : Atlas F proj} {o : Manifold.Orientation J F (Fin m)}
  (hA : A.IsContMDiff ∞ I J IM) {hn : (∞ : ℕ∞ω) ≠ 0}
  (ho : A.HasStructureGroup (Diffeomorph.orientationPreservingSubgroup hn o))

omit [BoundarylessManifold J F] in
/-- **Naturality of the fibre integral along maps of fibrations.** Let `A₁` and `A` be smooth
atlases of `proj₁ : M₁ → B₁` and `proj : M → B` whose coordinate changes preserve the same
orientation `o` of the compact Hausdorff model fibre `F`, with `B₁` and `B` boundaryless. Let
`g : M₁ → M` be a smooth map covering a smooth map `f : B₁ → B`, `proj ∘ g = f ∘ proj₁`, such
that for every `b₁` the fibre map `y ↦ (e (g (e₁⁻¹ (b₁, y)))).2`, read in the charts
`e₁ = A₁.trivAt b₁` and `e = A.trivAt (f b₁)`, is a diffeomorphism of `F` preserving `o`. Then
the fibre integral of the pull-back of a smooth form `α` along `g` is the pull-back along `f` of
the fibre integral of `α`. -/
theorem fiberIntegral_mpullback {A₁ : Atlas F proj₁} (hA₁ : A₁.IsContMDiff ∞ I₁ J IM₁)
    (ho₁ : A₁.HasStructureGroup (Diffeomorph.orientationPreservingSubgroup hn o))
    {f : B₁ → B} (hf : ContMDiff I₁ I ∞ f) {g : M₁ → M} (hg : ContMDiff IM₁ IM ∞ g)
    (hfg : proj ∘ g = f ∘ proj₁)
    (hfib : ∀ b₁, ∃ φ ∈ Diffeomorph.orientationPreservingSubgroup hn o, ⇑φ = fun y ↦
      (A.trivAt (f b₁) (g ((A₁.trivAt b₁).toOpenPartialHomeomorph.symm (b₁, y)))).2)
    (α : SmoothForm IM M ℝ (r + m)) :
    A₁.fiberIntegral hA₁ ho₁ (SmoothForm.mpullback g hg α) =
      SmoothForm.mpullback f hf (A.fiberIntegral hA ho α) :=
  SmoothBundleForm.ext fun b₁ v ↦ by
    obtain ⟨φ, hφ, hφg⟩ := hfib b₁
    rw [fiberIntegral_apply, SmoothForm.mpullback_apply, fiberIntegral_apply, fiberIntegrand_def,
      fiberIntegrand_def, SmoothForm.coe_mpullback,
      Bundle.Trivialization.fiberIntegrand_mpullback
        ((hA₁.contMDiffOn_trivAt_symm b₁).mdifferentiableOn (by simp))
        (hA.mdifferentiable_trivAt (by simp) (f b₁)) (hg.mdifferentiable (by simp)) hfg
        ((hf b₁).mdifferentiableAt (by simp)) (A₁.mem_baseSet_trivAt b₁)
        (A.mem_baseSet_trivAt (f b₁)) (by simpa using o.card_eq.symm.le), ← hφg]
    exact φ.toHomeomorph.isOpenEmbedding.integralTopForm_mpullback_of_isOrientationPreservingAt
      (Diffeomorph.mem_orientationPreservingSubgroup_iff.mp hφ) (by simp)

end TauCeti.MapFiber.Atlas

end
