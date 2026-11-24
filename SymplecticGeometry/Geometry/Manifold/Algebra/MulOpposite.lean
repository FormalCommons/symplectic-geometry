/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.Geometry.Manifold.Algebra.SMul
public import TauCeti.Geometry.Manifold.PullbackGroupoid
import TauCeti.Geometry.Manifold.GroupAction.Quotient
import TauCeti.Topology.Algebra.ProperAction.Basic

/-!
# The opposite of a manifold, and of a Lie group

For a charted space `M` modelled on `H`, the type `Mᵐᵒᵖ` receives the charts of `M` moved along
`MulOpposite.opHomeomorph`, that is, pulled back along `MulOpposite.unop`
(`MulOpposite.chartedSpace`). For these charts `op : M → Mᵐᵒᵖ` is a diffeomorphism, the opposite
of a `C^n` manifold is a `C^n` manifold, and the opposite of a `C^n` Lie group is a `C^n` Lie
group. A right action of a Lie group `G` on `X`, written as an action of `Gᵐᵒᵖ`, is then jointly
`C^n` in the sense of `ContMDiffSMul` exactly when `(x, g) ↦ op g • x` is `C^n`.

The charted space is a definition marked `@[instance_reducible]`, to be used as a local instance,
and not a global instance: Mathlib gives `Eᵐᵒᵖ` its own normed space structure for a normed algebra
`E`, hence `chartedSpaceSelf : ChartedSpace Eᵐᵒᵖ Eᵐᵒᵖ`, and Tau Ceti places no charted space on
`Gᵐᵒᵖ` for that reason. Once it is in place, the manifold and Lie group structures are found by
instance search, as for Tau Ceti's `ProperSMul.orbitRelQuotientChartedSpace`. They let Tau Ceti's
results on left Lie group actions, such as its quotient manifold theorem, apply to right actions.

The construction is Tau Ceti's `Homeomorph.pullbackChartedSpace` for `opHomeomorph.symm`, and
everything here follows from `Homeomorph.pullback_isManifold` and
`Homeomorph.pullbackDiffeomorph`.

## Main definitions

* `MulOpposite.chartedSpace H M`: the charts of `M` on `Mᵐᵒᵖ`.
* `MulOpposite.opDiffeomorph I n M`: `op` as a `C^n` diffeomorphism `M ≃ₘ^n⟮I, I⟯ Mᵐᵒᵖ`.

## Main results

* `MulOpposite.instIsManifold`: the opposite of a `C^n` manifold is a `C^n` manifold.
* `MulOpposite.contMDiff_op`, `MulOpposite.contMDiff_unop`: `op` and `unop` are `C^n`.
* `MulOpposite.instContMDiffMul`, `MulOpposite.instLieGroup`: the opposite of a `C^n` monoid,
  or of a `C^n` Lie group, is one too.
* `MulOpposite.contMDiffSMul_iff`: a right action of `M` on `X`, as an action of `Mᵐᵒᵖ`, is
  `ContMDiffSMul` if and only if `(x, g) ↦ op g • x` is `C^n`.

An example at the end of the file applies Tau Ceti's `ProperSMul.orbitRelQuotientChartedSpace` to
a smooth free right action of a compact Lie group.
-/

public section

open scoped Manifold ContDiff

namespace MulOpposite

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M]

variable (H) in
/-- The charted space structure on `Mᵐᵒᵖ` given by the charts of `M`: the chart at `x` is the
chart of `M` at `unop x`, precomposed with `unop`. It is not a global instance, since it would
compete with `chartedSpaceSelf` on `Eᵐᵒᵖ` for a normed algebra `E`. -/
@[expose, instance_reducible]
def chartedSpace : ChartedSpace H Mᵐᵒᵖ :=
  (opHomeomorph (M := M)).symm.pullbackChartedSpace

/-- The chart of `Mᵐᵒᵖ` at `x` is the chart of `M` at `unop x`, precomposed with `unop`. -/
-- `high`: these must fire before Tau Ceti's `Homeomorph.pullbackChartedSpace_chartAt` and
-- `_atlas`, which leave `opHomeomorph.symm x` and `opHomeomorph.symm.symm` in their place.
@[mfld_simps high]
theorem chartedSpace_chartAt (x : Mᵐᵒᵖ) :
    letI := chartedSpace H M
    chartAt H x = (opHomeomorph (M := M)).symm.transOpenPartialHomeomorph (chartAt H (unop x)) :=
  (rfl)

/-- The atlas of `Mᵐᵒᵖ` consists of the charts of `M`, precomposed with `unop`. -/
@[mfld_simps high]
theorem chartedSpace_atlas :
    letI := chartedSpace H M
    atlas H Mᵐᵒᵖ = ((opHomeomorph (M := M)).symm.transOpenPartialHomeomorph ·) '' atlas H M :=
  (rfl)

/-- The opposite of a `C^n` manifold is a `C^n` manifold. -/
instance instIsManifold [IsManifold I n M] :
    letI := chartedSpace H M
    IsManifold I n Mᵐᵒᵖ :=
  (opHomeomorph (M := M)).symm.pullback_isManifold I n

/-- `op : M → Mᵐᵒᵖ` as a `C^n` diffeomorphism, for the charts `MulOpposite.chartedSpace`. -/
def opDiffeomorph :
    letI := chartedSpace H M
    M ≃ₘ^n⟮I, I⟯ Mᵐᵒᵖ :=
  letI := chartedSpace H M
  ((opHomeomorph (M := M)).symm.pullbackDiffeomorph I n).symm

/-- The underlying map of `opDiffeomorph` is `op`. -/
@[simp]
theorem coe_opDiffeomorph :
    letI := chartedSpace H M
    ⇑(opDiffeomorph I n M) = op :=
  let := chartedSpace H M
  Homeomorph.coe_pullbackDiffeomorph_symm _ (I := I) (n := n)

/-- The underlying map of the inverse of `opDiffeomorph` is `unop`. -/
@[simp]
theorem coe_opDiffeomorph_symm :
    letI := chartedSpace H M
    ⇑(opDiffeomorph I n M).symm = unop :=
  let := chartedSpace H M
  Homeomorph.coe_pullbackDiffeomorph _ (I := I) (n := n)

variable {M}

/-- `op : M → Mᵐᵒᵖ` is `C^n`. -/
theorem contMDiff_op :
    letI := chartedSpace H M
    ContMDiff I I n (op : M → Mᵐᵒᵖ) := by
  let := chartedSpace H M
  simpa using (opDiffeomorph I n M).contMDiff

/-- `unop : Mᵐᵒᵖ → M` is `C^n`. -/
theorem contMDiff_unop :
    letI := chartedSpace H M
    ContMDiff I I n (unop : Mᵐᵒᵖ → M) := by
  let := chartedSpace H M
  simpa using (opDiffeomorph I n M).symm.contMDiff

variable (M)

/-- The opposite of a `C^n` monoid is a `C^n` monoid: its product
`(a, b) ↦ op (unop b * unop a)` is `C^n`. -/
instance instContMDiffMul [Mul M] [ContMDiffMul I n M] :
    letI := chartedSpace H M
    ContMDiffMul I n Mᵐᵒᵖ := by
  let := chartedSpace H M
  refine { toIsManifold := instIsManifold I n M, contMDiff_mul := ?_ }
  have hu := contMDiff_unop I n (M := M)
  exact (contMDiff_op I n).comp ((hu.comp contMDiff_snd).mul (hu.comp contMDiff_fst))

/-- The opposite of a `C^n` Lie group is a `C^n` Lie group. -/
instance instLieGroup [Group M] [LieGroup I n M] :
    letI := chartedSpace H M
    LieGroup I n Mᵐᵒᵖ := by
  let := chartedSpace H M
  refine { toContMDiffMul := instContMDiffMul I n M, contMDiff_inv := ?_ }
  exact (contMDiff_op I n).comp ((contMDiff_unop I n).inv)

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H' X]

variable {I n M} in
/-- A right action of `M` on `X`, written as an action of `Mᵐᵒᵖ`, is jointly `C^n` in the sense
of `ContMDiffSMul` exactly when `(x, g) ↦ op g • x` is `C^n`. -/
theorem contMDiffSMul_iff [SMul Mᵐᵒᵖ X] :
    letI := chartedSpace H M
    ContMDiffSMul I I' n Mᵐᵒᵖ X ↔ ContMDiff (I'.prod I) I' n fun p : X × M ↦ op p.2 • p.1 := by
  let := chartedSpace H M
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨?_⟩⟩
  · exact h.contMDiff_smul.comp (((contMDiff_op I n).comp contMDiff_snd).prodMk contMDiff_fst)
  · have := h.comp (contMDiff_snd.prodMk ((contMDiff_unop I n).comp contMDiff_fst))
    simpa only [Function.comp_def, op_unop] using this

/- With the charts of `G` on `Gᵐᵒᵖ`, a smooth free right action of a compact Lie group `G` on a
Hausdorff boundaryless finite-dimensional manifold `X` is `ContMDiffSMul` and proper, so Tau Ceti's
slice charts on the orbit space `X ⧸ Gᵐᵒᵖ` apply. -/
noncomputable example
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {IG : ModelWithCorners ℝ E H}
    {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup IG ∞ G]
    [CompactSpace G]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    {H' : Type*} [TopologicalSpace H'] {IX : ModelWithCorners ℝ E' H'} [IX.Boundaryless]
    {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace H' X] [IsManifold IX ∞ X]
    [MulAction Gᵐᵒᵖ X] [IsCancelSMul Gᵐᵒᵖ X]
    (h : ContMDiff (IX.prod IG) IX ∞ fun p : X × G ↦ op p.2 • p.1) :
    ChartedSpace (ProperSMul.QuotientModelSpace E E') (MulAction.orbitRel.Quotient Gᵐᵒᵖ X) :=
  letI := chartedSpace H G
  haveI := contMDiffSMul_iff.2 h
  haveI := ContMDiffSMul.continuousSMul (I := IG) (I' := IX) (G := Gᵐᵒᵖ) (M := X) ∞
  haveI := TauCeti.properSMul_of_compactSpace Gᵐᵒᵖ X
  ProperSMul.orbitRelQuotientChartedSpace IG Gᵐᵒᵖ IX X

end MulOpposite

end
