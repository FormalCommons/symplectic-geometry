/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.DeRham.MayerVietoris
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.SmoothFamily.Basic

/-!
# Cut-off extensions of smooth families

For a cut-off function `ρ` of a cover of `U ⊔ V` by two open sets
(`SymplecticGeometry.MayerVietorisCutoff`), multiplying a form on `U ⊓ V` by `ρ`, or by `1 - ρ`,
and extending it by zero to `U`, or to `V`, takes smooth families of forms to smooth families
(`MayerVietorisCutoff.isSmoothFamily_extendLeft`,
`MayerVietorisCutoff.isSmoothFamily_extendRight`).
-/

public section

open TopologicalSpace
open scoped Manifold ContDiff

namespace SymplecticGeometry.MayerVietorisCutoff

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}
  {U V : Opens M} (c : MayerVietorisCutoff I U V)
  {EN HN N : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
  [TopologicalSpace N] [ChartedSpace HN N] {J : ModelWithCorners ℝ EN HN} [IsManifold J 1 N]

/-- `extendLeft` takes smooth families to smooth families. -/
theorem isSmoothFamily_extendLeft {α : N → TauCeti.SmoothForm I (U ⊓ V : Opens M) F k}
    (hα : IsSmoothFamily J α) : IsSmoothFamily J (fun t ↦ c.extendLeft (α t)) :=
  hα.extendByZero_smul inf_le_left (c.contMDiff.comp (contMDiff_inclusion le_sup_left))
    (fun _ hx ↦ c.eventually_eq_zero hx) fun _ ↦ c.coe_extendLeft _

/-- `extendRight` takes smooth families to smooth families. -/
theorem isSmoothFamily_extendRight {α : N → TauCeti.SmoothForm I (U ⊓ V : Opens M) F k}
    (hα : IsSmoothFamily J α) : IsSmoothFamily J (fun t ↦ c.extendRight (α t)) :=
  hα.extendByZero_smul inf_le_right
    (contMDiff_const.sub (c.contMDiff.comp (contMDiff_inclusion le_sup_right)))
    (fun _ hx ↦ c.eventually_one_sub_eq_zero hx) fun _ ↦ c.coe_extendRight _

end SymplecticGeometry.MayerVietorisCutoff

end
