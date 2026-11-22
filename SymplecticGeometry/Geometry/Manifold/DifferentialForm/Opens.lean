/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Interior
public import TauCeti.Geometry.Manifold.DifferentialForm.Opens
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import TauCeti.Geometry.Manifold.TwoForm.Basic
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.LocalDiffeomorph
import SymplecticGeometry.Geometry.Manifold.MFDeriv.Opens

/-!
# Differential forms restricted to open subsets

For an open subset `U` of a manifold `M`, a rough form on `M` restricts to `U` by pullback along
`Subtype.val : U → M`. Tau Ceti's file of the same name treats restriction along
`TopologicalSpace.Opens.inclusion` between two open subsets, and pull-backs along
`PartialDiffeomorph.liftOpens`; this file gives the counterparts for restriction from `M` itself,
and the pull-back of restricted forms along a partial diffeomorphism of open subsets.

## Restriction along `Subtype.val`

* Every form on `U` is the restriction of a form on `M`, its extension by zero
  (`TauCeti.mpullback_subtype_val_surjective`).
* At a point of `U`, a form and its restriction have the same regularity
  (`TauCeti.contMDiffAt_mpullback_subtype_val_iff`), since `Subtype.val` is a local
  diffeomorphism.
* A form that is `C^n` on `U` restricts to a `C^n` form on `U`
  (`TauCeti.isSmoothForm_mpullback_subtype_val_of_contMDiffOn`).
* For a form `γ` and a vector field `Z` that are both `C^n` on `U`, the restriction of `ι_Z γ`
  to `U` is a `C^n` form (`TauCeti.isSmoothForm_mpullback_subtypeVal_interior`), although
  `ι_Z γ` need not be smooth on all of `M`. For a smooth form `γ`, this restriction is the smooth
  form `TauCeti.SmoothForm.restrictInterior γ Z hZ`.
* A smooth map `ψ` between open subsets that pulls the restriction of a two-form `σ'` back to the
  restriction of a two-form `σ` preserves the forms on tangent vectors at each point
  (`TauCeti.SmoothForm.eval₂_mfderiv_eq_of_mpullback_subtype_val_eq`).
* Restriction commutes with the exterior derivative, with no regularity assumption
  (`TauCeti.mpullback_subtype_val_mextDeriv`), since near every point of `U` the coordinate
  expressions of a form and of its restriction agree
  (`TauCeti.RoughForm.inChartAt_mpullback_subtype_val_eventuallyEq`).

The proofs of the last item adapt those of Tau Ceti's `TauCeti.mpullback_inclusion_mextDeriv` and
`TauCeti.RoughForm.inChartAt_mpullback_inclusion_eventuallyEq`, with Tau Ceti's
`TopologicalSpace.Opens.coe_extChartAt_symm_apply` for the agreement of the inverse charts.

## Pull-back along a partial diffeomorphism of open subsets

Let `Φ` be a partial diffeomorphism from an open subset `U` of `M` to an open subset `V` of `M'`.
Tau Ceti reads `Φ` in the ambient manifolds as `PartialDiffeomorph.liftOpens`, and a partial
diffeomorphism as a diffeomorphism between its source and its target as
`PartialDiffeomorph.toDiffeomorphSourceTarget`. Composing the two gives a diffeomorphism `φ`
between open subsets of `M` and `M'`.

An identity `Φ^* (σ|_V) = τ|_U` between forms, known at the points of the source of `Φ`, becomes
the identity `φ^* (σ|_{target}) = τ|_{source}` between the smooth forms restricted to the source
and the target of `φ` (`PartialDiffeomorph.mpullback_toDiffeomorphSourceTarget_liftOpens`). This
is how a construction carried out on an open submanifold, such as a Moser flow defined only on
part of a tube, gives a diffeomorphism of open subsets of the ambient manifold that pulls one form
back to another.

The proof combines Tau Ceti's `TauCeti.mpullback_liftOpens_apply_coe` with the functoriality of
pull-backs at a point (`TauCeti.mpullback_comp_at`). The relative Moser theorem
`TauCeti.SmoothEmbedding.exists_diffeomorph_opens_of_eq_along` uses it.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer, 2013, Chapter 14.
-/

public section

open Set Filter TopologicalSpace Bundle
open scoped Manifold Topology ContDiff

namespace TauCeti

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

/-- Every form on an open subset `U` of `M` is the restriction to `U` of a form on `M`. -/
theorem mpullback_subtype_val_surjective (U : Opens M) :
    Function.Surjective (mpullback (F := F) (k := k) I I (Subtype.val : U → M)) := by
  classical
  refine fun ξ ↦ ⟨fun y ↦ if hy : y ∈ U then ξ ⟨y, hy⟩ else 0, funext fun x ↦ ?_⟩
  rw [mpullback_subtype_val_apply]
  exact dite_eq_left x.property

/-- At a point of an open subset `U`, a form on `M` is `C^n` exactly when its restriction to `U`
is. -/
theorem contMDiffAt_mpullback_subtype_val_iff [IsManifold I 1 M] {U : Opens M}
    {n : WithTop ℕ∞} (γ : RoughForm I M F k) (x : U) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F)) n
        (fun y ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F) y
          (mpullback I I (Subtype.val : U → M) γ y)) x ↔
      ContMDiffAt I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F)) n
        (fun y ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F) y (γ y)) (x : M) :=
  (isLocalDiffeomorph_subtype_val (n := ω) x).contMDiffAt_mpullback_form_iff (by simp)

variable [IsManifold I 1 M]

/-- A form on `M` that is `C^n` on an open subset `U` restricts to a `C^n` form on `U`. -/
theorem isSmoothForm_mpullback_subtype_val_of_contMDiffOn {U : Opens M} {n : WithTop ℕ∞}
    {γ : RoughForm I M F k}
    (hγ : ContMDiffOn I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F)) n
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F) y (γ y)) U) :
    IsSmoothForm I n (mpullback I I (Subtype.val : U → M) γ) :=
  (isSmoothForm_def n _).mpr fun x ↦ (contMDiffAt_mpullback_subtype_val_iff _ x).2
    (hγ.contMDiffAt (U.isOpen.mem_nhds x.property))

/-- Let `γ` be a form and `Z` a vector field on `M`, both `C^n` on an open subset `U`. Then the
restriction to `U` of the interior product `ι_Z γ` is a `C^n` form on `U`. -/
theorem isSmoothForm_mpullback_subtypeVal_interior {U : Opens M} {n : WithTop ℕ∞}
    {γ : RoughForm I M F (k + 1)} {Z : (x : M) → TangentSpace I x}
    (hγ : ContMDiffOn I (I.prod 𝓘(ℝ, E [⋀^Fin (k + 1)]→L[ℝ] F)) n
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin (k + 1)]→L[ℝ] F) y (γ y)) U)
    (hZ : ContMDiffOn I I.tangent n (T% Z) U) :
    IsSmoothForm I n (mpullback I I (Subtype.val : U → M) (γ.interior Z)) :=
  isSmoothForm_mpullback_subtype_val_of_contMDiffOn fun _ hx ↦
    (RoughForm.contMDiffAt_interior (hZ.contMDiffAt (U.isOpen.mem_nhds hx))
      (hγ.contMDiffAt (U.isOpen.mem_nhds hx))).contMDiffWithinAt

/-- For a smooth `(k + 1)`-form `γ` on `M` and a vector field `Z` on `M` that is smooth on an open
subset `U`, the restriction to `U` of the interior product `ι_Z γ`, as a smooth `k`-form on `U`.
The field `Z` need not be smooth outside `U`. -/
noncomputable def SmoothForm.restrictInterior (γ : SmoothForm I M F (k + 1))
    (Z : (x : M) → TangentSpace I x) {U : Opens M} (hZ : ContMDiffOn I I.tangent ∞ (T% Z) U) :
    SmoothForm I U F k :=
  ⟨TauCeti.mpullback (F := F) (k := k) I I (Subtype.val : U → M)
      (RoughForm.interior Z γ.val),
    (isSmoothForm_mpullback_subtypeVal_interior γ.contMDiff.contMDiffOn hZ).mem_smoothBundleForms⟩

@[simp]
theorem SmoothForm.coe_restrictInterior (γ : SmoothForm I M F (k + 1))
    (Z : (x : M) → TangentSpace I x) {U : Opens M} (hZ : ContMDiffOn I I.tangent ∞ (T% Z) U) :
    (γ.restrictInterior Z hZ : RoughForm I U F k) =
      TauCeti.mpullback (F := F) (k := k) I I (Subtype.val : U → M)
        (RoughForm.interior Z γ.val) :=
  (rfl)

/-- Near the chart image of a point of an open subset `U`, the coordinate expression of the
restriction to `U` of a form on `M` agrees with that of the form itself. -/
theorem RoughForm.inChartAt_mpullback_subtype_val_eventuallyEq {U : Opens M}
    (γ : RoughForm I M F k) (x : U) :
    (mpullback I I (Subtype.val : U → M) γ).inChartAt x =ᶠ[𝓝[range I] (extChartAt I x x)]
      γ.inChartAt (x : M) := by
  filter_upwards [extChartAt_target_mem_nhdsWithin x] with z hz
  have hev : (extChartAt I (x : M)).symm =ᶠ[𝓝[range I] z] Subtype.val ∘ (extChartAt I x).symm :=
    Filter.mem_of_superset (extChartAt_target_mem_nhdsWithin_of_mem hz)
      fun w hw ↦ (U.coe_extChartAt_symm_apply x hw).symm
  have h0 : (Subtype.val ∘ (extChartAt I x).symm) z = (extChartAt I (x : M)).symm z :=
    U.coe_extChartAt_symm_apply x hz
  have hmf : mfderivWithin 𝓘(ℝ, E) I (Subtype.val ∘ (extChartAt I x).symm) (range I) z =
      mfderivWithin 𝓘(ℝ, E) I (extChartAt I (x : M)).symm (range I) z :=
    hev.symm.mfderivWithin_eq h0
  rw [inChartAt_mpullback γ _ x hz mdifferentiableAt_subtypeVal, hmf,
    ← Function.comp_apply (f := Subtype.val), h0]
  ext v
  exact (inChartAt_apply γ (x : M) z v).symm

/-- Restriction to an open subset commutes with the exterior derivative, with no regularity
assumption. -/
theorem mpullback_subtype_val_mextDeriv {U : Opens M} (γ : RoughForm I M F k) :
    mpullback I I (Subtype.val : U → M) (mextDeriv γ) =
      mextDeriv (mpullback I I (Subtype.val : U → M) γ) := by
  funext x
  have heq := RoughForm.inChartAt_mpullback_subtype_val_eventuallyEq γ x
  rw [mpullback_subtype_val_apply, mextDeriv_def, mextDeriv_def,
    ← Opens.extChartAt_apply U x x]
  exact (heq.extDerivWithin_eq (heq.self_of_nhdsWithin (mem_range_self _))).symm

section TwoForm

variable {E' H' M' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' 1 M']

/-- Let `ψ : U → V` be a smooth map between open subsets of `M` and `M'` that pulls the restriction
of a two-form `σ'` on `M'` back to the restriction of a two-form `σ` on `M`. Then at each point
`x` of `U`, `σ'` at `ψ x` takes the same values on `dψ a` and `dψ b` as `σ` at `x` on `a` and
`b`. -/
theorem SmoothForm.eval₂_mfderiv_eq_of_mpullback_subtype_val_eq {U : Opens M} {V : Opens M'}
    {ψ : U → V} (hψ : ContMDiff I I' ∞ ψ) {σ : SmoothForm I M F 2} {σ' : SmoothForm I' M' F 2}
    (h : SmoothForm.mpullback ψ hψ (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal σ') =
      SmoothForm.mpullback Subtype.val contMDiff_subtypeVal σ) (x : U) (a b : TangentSpace I x) :
    SmoothBundleForm.eval₂ σ' (ψ x : M') (mfderiv I I' ψ x a) (mfderiv I I' ψ x b) =
      SmoothBundleForm.eval₂ σ (x : M) a b := by
  have := congrArg (fun s ↦ SmoothBundleForm.eval₂ s x a b) h
  simpa only [SmoothForm.eval₂_mpullback, Manifold.mfderiv_subtype_val,
    ContinuousLinearEquiv.coe_coe, Manifold.tangentSpaceOpenEquiv_apply] using this

end TwoForm

end TauCeti

namespace PartialDiffeomorph

variable {E H M E' H' M' F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

/-- Let `Φ` be a partial diffeomorphism from an open subset `U` of `M` to an open subset `V` of
`M'`, and let `φ` be its reading in the ambient manifolds as a diffeomorphism between its source
and its target. If, at every point of the source of `Φ`, `Φ` pulls the restriction of a form `σ`
on `M'` to `V` back to the value of a form `τ` on `M`, then `φ` pulls the restriction of `σ` to
the target of `φ` back to the restriction of `τ` to the source of `φ`. -/
theorem mpullback_toDiffeomorphSourceTarget_liftOpens {U : Opens M} {V : Opens M'}
    (Φ : PartialDiffeomorph I I' U V ∞) (hU : Nonempty U) (hV : Nonempty V)
    {σ : TauCeti.SmoothForm I' M' F k} {τ : TauCeti.SmoothForm I M F k}
    (h : ∀ x ∈ Φ.source, TauCeti.mpullback I I' Φ
      (TauCeti.mpullback I' I' (Subtype.val : V → M') σ.val) x = τ.val x) :
    TauCeti.SmoothForm.mpullback (Φ.liftOpens hU hV).toDiffeomorphSourceTarget
        (Φ.liftOpens hU hV).toDiffeomorphSourceTarget.contMDiff
        (TauCeti.SmoothForm.mpullback Subtype.val contMDiff_subtypeVal σ) =
      TauCeti.SmoothForm.mpullback Subtype.val contMDiff_subtypeVal τ := by
  set Ψ := Φ.liftOpens hU hV
  set φ := Ψ.toDiffeomorphSourceTarget
  have hφΨ : Subtype.val ∘ ⇑φ = ⇑Ψ ∘ Subtype.val := funext Ψ.toDiffeomorphSourceTarget_apply_coe
  -- At a point `z` of the source of `Ψ`, `φ^* σ` is `Φ^* σ` at the point of `U` that `z` is.
  apply Subtype.ext
  funext z
  obtain ⟨y, hy, hyz⟩ : (z : M) ∈ Subtype.val '' Φ.source :=
    Φ.liftOpens_source hU hV ▸ z.property
  have hφz : MDifferentiableAt I I' φ z := φ.contMDiff.mdifferentiableAt (by simp)
  have hΨz : MDifferentiableAt I I' Ψ z := Ψ.mdifferentiableAt (by simp) z.property
  rw [TauCeti.SmoothForm.coe_mpullback_subtype_val_apply τ z, TauCeti.SmoothForm.coe_mpullback,
    TauCeti.SmoothForm.coe_mpullback, ← TauCeti.mpullback_comp_at hφz mdifferentiableAt_subtypeVal,
    hφΨ, TauCeti.mpullback_comp_at mdifferentiableAt_subtypeVal hΨz,
    TauCeti.mpullback_subtype_val_apply, ← hyz,
    TauCeti.mpullback_liftOpens_apply_coe Φ (by simp) hU hV _ hy, h y hy]

end PartialDiffeomorph

end
