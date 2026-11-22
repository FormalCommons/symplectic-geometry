/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Interior
public import TauCeti.Geometry.Manifold.DifferentialForm.Opens
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.LocalDiffeomorph

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
* For a `C^n` form `γ` on `M` and a vector field `Z` that is `C^n` on `U`, the restriction of
  `ι_Z γ` to `U` is a `C^n` form (`TauCeti.isSmoothForm_mpullback_subtypeVal_interior`), although
  `ι_Z γ` need not be smooth on all of `M`.
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

/-- Let `γ` be a `C^n` form on `M` and `Z` a vector field that is `C^n` on an open subset `U`.
Then the restriction to `U` of the interior product `ι_Z γ` is a `C^n` form on `U`. -/
theorem isSmoothForm_mpullback_subtypeVal_interior {U : Opens M} {n : WithTop ℕ∞}
    {γ : RoughForm I M F (k + 1)} {Z : (x : M) → TangentSpace I x} (hγ : IsSmoothForm I n γ)
    (hZ : ContMDiffOn I I.tangent n (T% Z) U) :
    IsSmoothForm I n (mpullback I I (Subtype.val : U → M) (γ.interior Z)) :=
  (isSmoothForm_def n _).mpr fun x ↦ (contMDiffAt_mpullback_subtype_val_iff _ x).2
    (RoughForm.contMDiffAt_interior (hZ.contMDiffAt (U.isOpen.mem_nhds x.property))
      (hγ.contMDiff x))

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
  rw [inChartAt_mpullback γ _ x hz (contMDiff_subtypeVal.mdifferentiableAt one_ne_zero), hmf,
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
  have hval {N : Opens M'} (x : N) : MDifferentiableAt I' I' (Subtype.val : N → M') x :=
    (contMDiff_subtypeVal (n := 1)).mdifferentiableAt one_ne_zero
  rw [TauCeti.SmoothForm.coe_mpullback_subtype_val_apply τ z, TauCeti.SmoothForm.coe_mpullback,
    TauCeti.SmoothForm.coe_mpullback, ← TauCeti.mpullback_comp_at hφz (hval _), hφΨ,
    TauCeti.mpullback_comp_at ((contMDiff_subtypeVal (n := 1)).mdifferentiableAt one_ne_zero)
      hΨz, TauCeti.mpullback_subtype_val_apply, ← hyz,
    TauCeti.mpullback_liftOpens_apply_coe Φ (by simp) hU hV _ hy, h y hy]

end PartialDiffeomorph

end
