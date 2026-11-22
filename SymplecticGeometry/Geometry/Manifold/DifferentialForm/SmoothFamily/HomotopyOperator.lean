/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.HomotopyOperator
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.SmoothFamily.Map

/-!
# The homotopy operator on smooth families of forms

Let `Φ : M' × [0, 1] → M` be smooth. The linear map `ω ↦ h (Φ^* ω)`, the homotopy operator
`TauCeti.SmoothForm.homotopyOperator` after pullback along `Φ`, takes smooth families of forms
over the unit interval to smooth families
(`SymplecticGeometry.preservesSmoothFamilies_homotopyOperator_mpullback`). For a contraction `Φ`
of `M`, this is the primitive of closed forms that the Poincaré lemma gives, and it depends
smoothly on the form.

The proof applies the homotopy operator on a larger cylinder. If the family `t ↦ ω t` consists of
the slices of a smooth form `Ω` on `[0, 1] × M`, pull `Ω` back along
`G ((t, x), s) = (t, Φ (x, s))` on `([0, 1] × M') × [0, 1]` and apply the homotopy operator in
the last variable. The slices of the result are the forms `h (Φ^* ω t)`, because the homotopy
operator commutes with pullback along the slice inclusions `x ↦ (t, x)`, by Tau Ceti's
`TauCeti.homotopyOperator_mpullback_prodMap_id_of_isSmoothForm`.

## Main results

* `SymplecticGeometry.preservesSmoothFamilies_homotopyOperator_mpullback`: `ω ↦ h (Φ^* ω)`,
  restricted to any submodule of forms, takes smooth families to smooth families.

## References

* [A. Weil, *Sur les théorèmes de de Rham*][Weil1952], §2 (the homotopy operator of a
  contraction).
* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], proof of
  Theorem 3.2.4.
-/

public section

open Set
open scoped Manifold ContDiff

namespace SymplecticGeometry

open TauCeti

variable {E H M E' H' M' F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H} [IsManifold I ∞ M]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  [TopologicalSpace M'] [ChartedSpace H' M'] {I' : ModelWithCorners ℝ E' H'} [IsManifold I' ∞ M']
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {k : ℕ}

/-- **The homotopy operator on smooth families.** For a smooth map `Φ : M' × [0, 1] → M` and a
submodule `D` of the smooth `(k + 1)`-forms on `M` with values in a Banach space, the linear map
`ω ↦ h (Φ^* ω)` on `D`, the homotopy operator after pullback along `Φ`, takes smooth families of
forms over the unit interval to smooth families. -/
theorem preservesSmoothFamilies_homotopyOperator_mpullback {Φ : M' × Icc (0 : ℝ) 1 → M}
    (hΦ : ContMDiff (I'.prod (𝓡∂ 1)) I ∞ Φ) (D : Submodule ℝ (SmoothForm I M F (k + 1))) :
    PreservesSmoothFamilies
      (SmoothForm.homotopyOperator ∘ₗ SmoothForm.mpullback Φ hΦ ∘ₗ D.subtype) := by
  refine preservesSmoothFamilies_def.mpr fun α hα ↦ ?_
  obtain ⟨Ω, hΩ⟩ := isSmoothFamily_def.mp hα
  -- The family is read on the cylinder `([0, 1] × M') × [0, 1]`, through `(t, Φ (x, s))`.
  let G : (unitInterval × M') × Icc (0 : ℝ) 1 → unitInterval × M :=
    fun p ↦ (p.1.1, Φ (p.1.2, p.2))
  have hG : ContMDiff (((𝓡∂ 1).prod I').prod (𝓡∂ 1)) ((𝓡∂ 1).prod I) ∞ G :=
    (contMDiff_fst.comp contMDiff_fst).prodMk
      (hΦ.comp ((contMDiff_snd.comp contMDiff_fst).prodMk contMDiff_snd))
  refine isSmoothFamily_def.mpr
    ⟨SmoothForm.homotopyOperator (SmoothForm.mpullback G hG Ω), fun t ↦ ?_⟩
  -- The slice inclusion at `t`, and the inclusion of the cylinder over it.
  have hι : ContMDiff I' ((𝓡∂ 1).prod I') ∞ (Prod.mk t : M' → unitInterval × M') :=
    contMDiff_const.prodMk contMDiff_id
  have hιc : ContMDiff (I'.prod (𝓡∂ 1)) (((𝓡∂ 1).prod I').prod (𝓡∂ 1)) ∞
      (Prod.map (Prod.mk t) (id : Icc (0 : ℝ) 1 → Icc (0 : ℝ) 1)) := hι.prodMap contMDiff_id
  have hslice : SmoothForm.mpullback (Prod.map (Prod.mk t) id) hιc (SmoothForm.mpullback G hG Ω) =
      SmoothForm.mpullback Φ hΦ (α t : SmoothForm I M F (k + 1)) := by
    rw [← hΩ t, SmoothForm.mpullback_mpullback, SmoothForm.mpullback_mpullback]
    -- Both composites are `(x, s) ↦ (t, Φ (x, s))`, by the definition of `G`.
    rfl
  refine Subtype.ext ?_
  rw [SmoothForm.coe_mpullback, SmoothForm.coe_homotopyOperator,
    ← homotopyOperator_mpullback_prodMap_id_of_isSmoothForm (hι.mdifferentiable (by simp))
      ((SmoothForm.mpullback G hG Ω).isSmoothForm.of_le (by simp)),
    ← SmoothForm.coe_mpullback _ hιc, hslice, LinearMap.comp_apply, LinearMap.comp_apply,
    Submodule.subtype_apply, SmoothForm.coe_homotopyOperator]

end SymplecticGeometry
