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

The homotopy operator `TauCeti.SmoothForm.homotopyOperator`, integration in the last variable of
the cylinder `M' × [0, 1]`, takes smooth families of forms on the cylinder, over any parameter
manifold `N`, to smooth families of forms on `M'`
(`SymplecticGeometry.IsSmoothFamily.homotopyOperator`). With
`SymplecticGeometry.IsSmoothFamily.mpullback`, so does `ω ↦ h (Φ^* ω)` for a smooth
`Φ : M' × [0, 1] → M`, and in particular, as a linear map, it preserves smooth families over the
unit interval (`SymplecticGeometry.preservesSmoothFamilies_homotopyOperator_mpullback`).
For a contraction `Φ` of `M`, this is the primitive of closed forms that the Poincaré lemma
gives, and it depends smoothly on the form.

The proof applies the homotopy operator on a larger cylinder. If the family `t ↦ ω t` consists of
the slices of a smooth form `Ω` on `N × (M' × [0, 1])`, pull `Ω` back along
`G ((t, x), s) = (t, (x, s))` on `(N × M') × [0, 1]` and apply the homotopy operator in
the last variable. The slices of the result are the forms `h (ω t)`, because the homotopy
operator commutes with pullback along the slice inclusions `x ↦ (t, x)`
(`TauCeti.SmoothForm.mpullback_homotopyOperator`).

## Main results

* `SymplecticGeometry.IsSmoothFamily.homotopyOperator`: `t ↦ h (ω t)` is a smooth family of
  forms on `M'` whenever `t ↦ ω t` is one on `M' × [0, 1]`, over any parameter manifold.
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

/-- **The homotopy operator on smooth families.** For a smooth family `α_t`, `t ∈ N`, of
`(k + 1)`-forms on the cylinder `M' × [0, 1]` with values in a Banach space, over any parameter
manifold `N`, the family `t ↦ h α_t` of `k`-forms on `M'`, the homotopy operator in the last
variable, is smooth. -/
theorem IsSmoothFamily.homotopyOperator {EN HN N : Type*} [NormedAddCommGroup EN]
    [NormedSpace ℝ EN] [TopologicalSpace HN] [TopologicalSpace N] [ChartedSpace HN N]
    {K : ModelWithCorners ℝ EN HN} [IsManifold K ∞ N]
    {α : N → SmoothForm (I'.prod (𝓡∂ 1)) (M' × Icc (0 : ℝ) 1) F (k + 1)}
    (hα : IsSmoothFamily K α) :
    IsSmoothFamily K fun t ↦ SmoothForm.homotopyOperator (α t) := by
  obtain ⟨Ω, hΩ⟩ := isSmoothFamily_def.mp hα
  -- The family is read on the cylinder `(N × M') × [0, 1]`, through `((t, x), s) ↦ (t, (x, s))`.
  let G : (N × M') × Icc (0 : ℝ) 1 → N × (M' × Icc (0 : ℝ) 1) := fun p ↦ (p.1.1, (p.1.2, p.2))
  have hG : ContMDiff ((K.prod I').prod (𝓡∂ 1)) (K.prod (I'.prod (𝓡∂ 1))) ∞ G :=
    (contMDiff_fst.comp contMDiff_fst).prodMk
      ((contMDiff_snd.comp contMDiff_fst).prodMk contMDiff_snd)
  refine isSmoothFamily_def.mpr
    ⟨SmoothForm.homotopyOperator (SmoothForm.mpullback G hG Ω), fun t ↦ ?_⟩
  -- The slice inclusion at `t`, and the inclusion of the cylinder over it.
  have hι : ContMDiff I' (K.prod I') ∞ (Prod.mk t : M' → N × M') :=
    contMDiff_const.prodMk contMDiff_id
  have hιc : ContMDiff (I'.prod (𝓡∂ 1)) ((K.prod I').prod (𝓡∂ 1)) ∞
      (Prod.map (Prod.mk t) (id : Icc (0 : ℝ) 1 → Icc (0 : ℝ) 1)) := hι.prodMap contMDiff_id
  have hslice :
      SmoothForm.mpullback (Prod.map (Prod.mk t) id) hιc (SmoothForm.mpullback G hG Ω) = α t := by
    rw [← hΩ t, SmoothForm.mpullback_mpullback]
    -- Both maps are `(x, s) ↦ (t, (x, s))`, by the definition of `G`.
    rfl
  rw [SmoothForm.mpullback_homotopyOperator, hslice]

/-- **The homotopy operator preserves smooth families.** For a smooth map `Φ : M' × [0, 1] → M`
and a submodule `D` of the smooth `(k + 1)`-forms on `M` with values in a Banach space, the linear
map `ω ↦ h (Φ^* ω)` on `D`, the homotopy operator after pullback along `Φ`, takes smooth families
of forms over the unit interval to smooth families. -/
theorem preservesSmoothFamilies_homotopyOperator_mpullback {Φ : M' × Icc (0 : ℝ) 1 → M}
    (hΦ : ContMDiff (I'.prod (𝓡∂ 1)) I ∞ Φ) (D : Submodule ℝ (SmoothForm I M F (k + 1))) :
    PreservesSmoothFamilies
      (SmoothForm.homotopyOperator ∘ₗ SmoothForm.mpullback Φ hΦ ∘ₗ D.subtype) :=
  preservesSmoothFamilies_def.mpr fun _ hα ↦ (hα.mpullback Φ hΦ).homotopyOperator

end SymplecticGeometry
