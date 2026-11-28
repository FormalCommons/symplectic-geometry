/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.MFDeriv.IsInvertible
import TauCeti.Geometry.Manifold.MFDeriv.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Submersion
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic

/-!
# Differentials read in a chart

This file reads differentials in an extended chart, in both directions: for maps from a manifold
into a normed space, and for maps from a normed space into a manifold through the inverse chart.
It also reads the tangent map of a map between manifolds in the charts of the tangent bundles.

For a map `f : M → F` into a normed space and a point `y` of the source of the extended chart at
`x`, which need not be centred at `y`, the range of `mvfderiv I f y` is the range of the Fréchet
derivative of the coordinate expression `f ∘ (extChartAt I x).symm` at the chart image of `y`.
This is the off-centre form of Tau Ceti's
`TauCeti.range_mvfderiv_eq_range_fderiv_comp_extChartAt_symm`, and its proof reads `mvfderiv I f y`
in the chart by Tau Ceti's `TauCeti.mfderiv_eq_fderiv_comp_mfderiv_extChartAt`.

For a map `h` from a normed space into the target of the extended chart at `x`, the differential
of `(extChartAt I x).symm ∘ h` is the derivative of `h` followed by the differential of the
inverse chart, which is invertible by Tau Ceti's `TauCeti.isInvertible_mfderiv_extChartAt_symm`;
so it is injective where the derivative of `h` is.

In the charts of the tangent bundles that Mathlib builds from base charts, the tangent map of
`f : M → M'` reads as `(z, v) ↦ (f̃ z, Df̃(z) v)`, where
`f̃ = extChartAt I' y ∘ f ∘ (extChartAt I x).symm` is the expression of `f` in the base charts and
the derivative is taken within the target of the chart at `x`. The fibre coordinate of a
tangent-bundle chart is a tangent coordinate change, so this rests on Tau Ceti's
`ContinuousAt.fderivWithin_extChartAt_comp_extChartAt_symm`, which writes the derivative of `f̃`
within `range I` as `mfderiv I I' f` conjugated by tangent coordinate changes. The targets and
sources of the tangent-bundle charts are described by Mathlib's `FiberBundle.extChartAt_target`
and `TangentBundle.mem_chart_source_iff`.

## Main results

* `SymplecticGeometry.range_mvfderiv_eq_range_fderiv_comp_extChartAt_symm_of_mem_source`: the
  range of `mvfderiv I f y` is that of the coordinate derivative at the chart image of `y`.
* `ContMDiff.contDiffOn_comp_extChartAt_symm`: a `C^n` map into a normed space is `C^n` in every
  chart.
* `ContMDiffOn.contDiffOn_extChartAt_comp`: a map from a normed space into a manifold, `C^n` on a
  set, is `C^n` in every chart where its reading is defined.
* `writtenInExtChartAt_model_space_left`: the reading of a map from a normed space in extended
  charts.
* `SymplecticGeometry.injective_mfderiv_extChartAt_symm_comp`: a map into the chart target with
  injective derivative, composed with the inverse chart, has injective differential.
* `ContinuousAt.extChartAt_tangentMap_extChartAt_symm`: the tangent map of a map continuous at a
  point, read in the charts of the tangent bundles.
* `ContinuousAt.fderivWithin_extChartAt_comp_extChartAt_symm_eq_trivializationAt`: the derivative
  of a map in the base charts at `x` and `y`, at any point of their sources, is its differential
  read in the tangent trivializations at `x` and `y`.
* `TangentBundle.extChartAt_target`, `tangentMap_extChartAt_symm_mem_extChartAt_source_iff`: the
  target of a tangent-bundle chart is the product of the base chart target with the fibre, and
  the tangent map of `f` meets the source of a tangent-bundle chart where `f` meets the base one.
* `MDifferentiableAt.isInvertible_fderivWithin_extChartAt_iff`: on a boundaryless source, the
  derivative of a map read in any pair of extended charts is invertible at a point exactly when
  its manifold derivative is invertible there.

## References

* [M. W. Hirsch, *Differential Topology*][Hirsch1976], Chapter 1, §2
-/

public section

open scoped Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : M → F} {x y : M}

namespace SymplecticGeometry

/-- At a point `y` of the source of the extended chart at `x`, the range of the differential of a
map into a normed space is the range of the Fréchet derivative of its coordinate expression at the
chart image of `y`, provided the coordinate expression is differentiable there. -/
theorem range_mvfderiv_eq_range_fderiv_comp_extChartAt_symm_of_mem_source [IsManifold I 1 M]
    (hy : y ∈ (extChartAt I x).source)
    (hf : DifferentiableAt 𝕜 (f ∘ (extChartAt I x).symm) (extChartAt I x y)) :
    (mvfderiv I f y).range = (fderiv 𝕜 (f ∘ (extChartAt I x).symm) (extChartAt I x y)).range := by
  obtain ⟨L, hL⟩ := isInvertible_mfderiv_extChartAt hy
  -- `show` reads Tau Ceti's `mfderiv` equation, whose codomain is the tangent space
  -- `TangentSpace 𝓘(𝕜, F) (f y)`, as one about `mvfderiv`, whose codomain is `F`.
  rw [show mvfderiv I f y = _ from
    TauCeti.mfderiv_eq_fderiv_comp_mfderiv_extChartAt hy hf, ← hL]
  exact LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr L.surjective)

/-- On a boundaryless model, let `h` map a normed space `F` into the target of the extended chart
at `x`. If `h` has injective derivative at `z`, then the map `w ↦ (extChartAt I x).symm (h w)`
into `M` has injective differential at `z`. -/
theorem injective_mfderiv_extChartAt_symm_comp [I.Boundaryless] [IsManifold I 1 M] {h : F → E}
    {z : F} (hz : h z ∈ (extChartAt I x).target) (hinj : Function.Injective (fderiv 𝕜 h z)) :
    Function.Injective (mfderiv 𝓘(𝕜, F) I (fun w ↦ (extChartAt I x).symm (h w)) z) :=
  TauCeti.injective_mfderiv_comp (f := h)
    (TauCeti.isInvertible_mfderiv_extChartAt_symm (I := I) hz).injective
    (by rwa [mfderiv_eq_fderiv])

end SymplecticGeometry

/-- A `C^n` map into a normed space is `C^n` in every chart: its coordinate expression
`f ∘ (extChartAt I x).symm` is `C^n` on the target of the extended chart. -/
theorem ContMDiff.contDiffOn_comp_extChartAt_symm {n : WithTop ℕ∞} [IsManifold I n M]
    (hf : ContMDiff I 𝓘(𝕜, F) n f) (x : M) :
    ContDiffOn 𝕜 n (f ∘ (extChartAt I x).symm) (extChartAt I x).target :=
  contMDiffOn_iff_contDiffOn.mp (hf.comp_contMDiffOn (contMDiffOn_extChartAt_symm x))

/-- A map from a normed space into `M` that is `C^n` on a set `s` is `C^n` in every chart: its
reading `extChartAt I x ∘ g` is `C^n` on the points of `s` that `g` maps into the source of the
chart at `x`. -/
theorem ContMDiffOn.contDiffOn_extChartAt_comp {n : WithTop ℕ∞} [IsManifold I n M] {g : F → M}
    {s : Set F} (hg : ContMDiffOn 𝓘(𝕜, F) I n g s) (x : M) :
    ContDiffOn 𝕜 n (extChartAt I x ∘ g) (s ∩ g ⁻¹' (chartAt H x).source) :=
  (contMDiffOn_extChartAt.comp (hg.mono Set.inter_subset_left) fun _ hy ↦ hy.2).contDiffOn

/-- The reading of a map `g` from a normed space into `M` in extended charts at `x` and at
`g x` is `extChartAt I (g x) ∘ g`: the chart of the normed space is the identity. -/
@[simp, mfld_simps]
theorem writtenInExtChartAt_model_space_left (g : F → M) (x : F) :
    writtenInExtChartAt 𝓘(𝕜, F) I x g = extChartAt I (g x) ∘ g :=
  rfl

section TangentMap

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  [IsManifold I 1 M] [IsManifold I' 1 M']

/-- **Chart expression of a tangent map.** Let `p` be a tangent vector of `M` and `q` one of
`M'`. A point `w = (z, v)` of the target of the tangent-bundle chart at `p` whose base point
`x = (extChartAt I p.proj).symm z` is sent by `f` into the source of the chart at `q.proj` is
sent by the tangent map of `f`, read in the tangent-bundle charts at `p` and `q`, to
`(f̃ z, Df̃(z) v)`, where `f̃ = extChartAt I' q.proj ∘ f ∘ (extChartAt I p.proj).symm` and the
derivative is taken within the target of the chart at `p.proj`. Only continuity of `f` at `x` is
assumed: where `f` is not differentiable both derivatives are zero. -/
theorem ContinuousAt.extChartAt_tangentMap_extChartAt_symm {f : M → M'}
    {p : TangentBundle I M} {q : TangentBundle I' M'} {w : E × E}
    (hw : w ∈ (extChartAt I.tangent p).target)
    (hc : ContinuousAt f ((extChartAt I p.proj).symm w.1))
    (hf : f ((extChartAt I p.proj).symm w.1) ∈ (extChartAt I' q.proj).source) :
    extChartAt I'.tangent q (tangentMap I I' f ((extChartAt I.tangent p).symm w)) =
      ((extChartAt I' q.proj ∘ f ∘ (extChartAt I p.proj).symm) w.1,
        fderivWithin 𝕜 (extChartAt I' q.proj ∘ f ∘ (extChartAt I p.proj).symm)
          (extChartAt I p.proj).target w.1 w.2) := by
  set b := (extChartAt I.tangent p).symm w
  set x := (extChartAt I p.proj).symm w.1
  have hz : w.1 ∈ (extChartAt I p.proj).target := Bundle.fst_mem_extChartAt_target p hw
  have hbx : b.proj = x := Bundle.proj_extChartAt_symm p hw
  have hx : x ∈ (extChartAt I p.proj).source := (extChartAt I p.proj).map_target hz
  have hxw : extChartAt I p.proj x = w.1 := (extChartAt I p.proj).right_inv hz
  obtain ⟨-, hbv⟩ := TauCeti.Manifold.extChartAt_tangent_symm_mem_baseSet_and_snd p hw
  rw [TangentBundle.trivializationAt_snd_eq_tangentCoordChange b.snd, hbx] at hbv
  have hfb : (tangentMap I I' f b).proj ∈
      (trivializationAt E' (TangentSpace I') q.proj).baseSet := by
    rw [tangentMap_proj, hbx]
    exact TangentBundle.mem_trivializationAt_baseSet_of_mem_extChartAt_source hf
  rw [Bundle.extChartAt_apply_of_mem_baseSet q hfb]
  refine Prod.ext ?_ ?_
  · simp [tangentMap_proj, hbx, x]
  clear_value b x
  obtain ⟨y, u⟩ := b
  obtain rfl : y = x := hbx
  rw [fderivWithin_congr_set (extChartAt_target_eventuallyEqSet_of_mem hz), ← hxw,
    hc.fderivWithin_extChartAt_comp_extChartAt_symm hx hf, ← hbv, tangentMap,
    TangentBundle.trivializationAt_snd_eq_tangentCoordChange]
  -- `TangentSpace I y` is `E` by definition, which hides the composite from
  -- `ContinuousLinearMap.comp_apply`; it is the nested application by definition.
  exact congrArg _ (congrArg _
    (TauCeti.tangentCoordChange_tangentCoordChange (mem_extChartAt_source y) hx u).symm)

/-- **A differential read in tangent trivializations.** Let `f : M → M'` be continuous at `z`,
with `z` in the base set of the tangent trivialization at `x` and `f z` in that at `y`. Then the
derivative of `extChartAt I' y ∘ f ∘ (extChartAt I x).symm`, taken within the target of the chart
at `x` at the chart image of `z`, is `mfderiv I I' f z` read in these two trivializations. Where
`f` is not differentiable at `z`, both sides are zero. -/
theorem ContinuousAt.fderivWithin_extChartAt_comp_extChartAt_symm_eq_trivializationAt
    {f : M → M'} {x z : M} {y : M'} (hc : ContinuousAt f z)
    (hz : z ∈ (trivializationAt E (TangentSpace I) x).baseSet)
    (hfz : f z ∈ (trivializationAt E' (TangentSpace I') y).baseSet) :
    fderivWithin 𝕜 (extChartAt I' y ∘ f ∘ (extChartAt I x).symm) (extChartAt I x).target
        (extChartAt I x z) =
      ((trivializationAt E' (TangentSpace I') y).continuousLinearMapAt 𝕜 (f z)).comp
        ((mfderiv I I' f z).comp ((trivializationAt E (TangentSpace I) x).symmL 𝕜 z)) := by
  rw [TangentBundle.trivializationAt_baseSet] at hz hfz
  have hz' : z ∈ (extChartAt I x).source := by rwa [extChartAt_source]
  rw [fderivWithin_congr_set (extChartAt_target_eventuallyEqSet_of_mem
      ((extChartAt I x).map_source hz')),
    hc.fderivWithin_extChartAt_comp_extChartAt_symm hz' (by rwa [extChartAt_source]),
    TangentBundle.symmL_trivializationAt_eq_core hz,
    TangentBundle.continuousLinearMapAt_trivializationAt_eq_core hfz]
  -- `tangentCoordChange I x y` is an abbreviation for this coordinate change of
  -- `tangentBundleCore`, which Mathlib states with no lemma.
  rfl

/-- The target of the chart of the tangent bundle at `p` is the product of the target of the base
chart at `p.proj` with the whole fibre. -/
theorem TangentBundle.extChartAt_target (p : TangentBundle I M) :
    (extChartAt I.tangent p).target = (extChartAt I p.proj).target ×ˢ Set.univ := by
  rw [FiberBundle.extChartAt_target, Set.inter_eq_left.mpr fun z hz ↦
    TangentBundle.extChartAt_symm_mem_trivializationAt_baseSet hz]

/-- For any `w : E × E`, the tangent map of `f` sends the inverse image of `w` under the
tangent-bundle chart at `p` into the source of the tangent-bundle chart at `q` exactly when `f`
sends the inverse image of `w.1` under the base chart at `p.proj` into the source of the base
chart at `q.proj`. -/
theorem tangentMap_extChartAt_symm_mem_extChartAt_source_iff (f : M → M')
    {p : TangentBundle I M} {q : TangentBundle I' M'} {w : E × E} :
    tangentMap I I' f ((extChartAt I.tangent p).symm w) ∈ (extChartAt I'.tangent q).source ↔
      f ((extChartAt I p.proj).symm w.1) ∈ (extChartAt I' q.proj).source := by
  rw [extChartAt_source, extChartAt_source, TangentBundle.mem_chart_source_iff, tangentMap_proj,
    extChartAt_coe_symm, extChartAt_coe_symm, Function.comp_apply, Function.comp_apply,
    TangentBundle.coe_chartAt_symm_fst, ModelWithCorners.tangent, modelWithCorners_prod_coe_symm,
    Prod.map_fst]

end TangentMap

section InvertibleDerivative

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  [I.Boundaryless] [IsManifold I 1 M] [IsManifold I' 1 M']

/-- On a boundaryless source, the derivative of `g` read in the extended charts at `x` and at `y`
is invertible at a point `z` of the source chart target whose image lies in the target chart,
exactly when the manifold derivative of `g` is invertible at the point of `M` that `z`
represents. The charts need not be centred at that point or at its image. -/
theorem MDifferentiableAt.isInvertible_fderivWithin_extChartAt_iff {g : M → M'} {x : M} {y : M'}
    {z : E} (hg : MDifferentiableAt I I' g ((extChartAt I x).symm z))
    (hz : z ∈ (extChartAt I x).target)
    (hgz : g ((extChartAt I x).symm z) ∈ (extChartAt I' y).source) :
    (fderivWithin 𝕜 (extChartAt I' y ∘ g ∘ (extChartAt I x).symm) (extChartAt I x).target
        z).IsInvertible ↔
      (mfderiv I I' g ((extChartAt I x).symm z)).IsInvertible := by
  obtain ⟨a, ha⟩ := isInvertible_mfderiv_extChartAt (I := I') hgz
  obtain ⟨b, hb⟩ := TauCeti.isInvertible_mfderiv_extChartAt_symm (I := I) (M := M) hz
  have hsymm : MDifferentiableAt 𝓘(𝕜, E) I (extChartAt I x).symm z :=
    mdifferentiableAt_of_isInvertible_mfderiv ⟨b, hb⟩
  have hy : MDifferentiableAt I' 𝓘(𝕜, E') (extChartAt I' y) ((g ∘ (extChartAt I x).symm) z) :=
    mdifferentiableAt_extChartAt (by rwa [← extChartAt_source (I := I')])
  -- Between normed spaces, `mfderiv` is `fderiv` up to the identifications of tangent spaces.
  have hfd :
      (mfderiv 𝓘(𝕜, E) 𝓘(𝕜, E') (extChartAt I' y ∘ g ∘ (extChartAt I x).symm) z).IsInvertible ↔
        (fderiv 𝕜 (extChartAt I' y ∘ g ∘ (extChartAt I x).symm) z).IsInvertible := by
    rw [mfderiv_eq_fderiv, ContinuousLinearMap.isInvertible_equiv_comp,
      ContinuousLinearMap.isInvertible_comp_equiv]
  rw [fderivWithin_of_isOpen (isOpen_extChartAt_target x) hz, ← hfd,
    mfderiv_comp z hy (hg.comp z hsymm), mfderiv_comp z hg hsymm]
  simp only [Function.comp_apply] at ha ⊢
  rw [← ha, ← hb, ContinuousLinearMap.isInvertible_equiv_comp,
    ContinuousLinearMap.isInvertible_comp_equiv]

end InvertibleDerivative

end
