/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Icc
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Family
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.LocalDiffeomorph
public import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
public import TauCeti.Geometry.Manifold.DifferentialForm.Opens
public import TauCeti.Geometry.Manifold.DifferentialForm.Vertical
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Prod.Basic
public import TauCeti.Geometry.Symplectic.Manifold.Flat
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Semibasic
public import SymplecticGeometry.Geometry.Manifold.Instances.Icc
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.SmoothFamily.Slice
import TauCeti.Geometry.Manifold.ContMDiff.Prod
import TauCeti.Geometry.Manifold.MFDeriv.Prod
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Vertical
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Pullback.Smooth
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Smooth
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.Basic
import SymplecticGeometry.Geometry.Manifold.MFDeriv.Prod
import SymplecticGeometry.Geometry.Manifold.VectorBundle.ContinuousAlternatingMap

/-!
# Smooth families of forms

A family `α : N → SmoothForm I M F k` of smooth forms on `M`, indexed by the points of a parameter
manifold `N` (in the uses, `unitInterval` or `ℝ`), is smooth (`SymplecticGeometry.IsSmoothFamily`)
when there is a smooth form `Ω` on `N × M` with `α t = ι_t^* Ω` for every `t`, where
`ι_t : y ↦ (t, y)`. Such a family is read through its *slice section*
`(t, y) ↦ (α t) y`, a section along the projection `N × M → M`
(`SymplecticGeometry.sliceSection`, in `SmoothFamily/Slice.lean`).

The slice section of a family of slices is smooth (Tau Ceti's
`TauCeti.contMDiff_mpullback_prodMk_form`). Conversely, if the slice section of `α` is smooth,
then Tau Ceti's vertical form `TauCeti.verticalForm J` of the family, the form on `N × M` whose
value at `(t, y)` evaluates `α t` on the components along `M`, is smooth
(`TauCeti.contMDiffAt_verticalForm_iff`, `TauCeti.SmoothForm.ofSlices`), and its slices are the
`α t` (Tau Ceti's `TauCeti.mpullback_prodMk_verticalForm`). So a family is
smooth exactly when its slice section is (`SymplecticGeometry.isSmoothFamily_iff_contMDiff`).
This makes smoothness of a family a local property in `M`, and gives the closure properties of
smooth families: under the linear operations, multiplication by smooth functions of the parameter
or of the point, pullback along smooth maps, the exterior derivative, cut-off and extension by
zero from an open subset, reparametrization, and concatenation over `[0, 1]`; and smoothness on
`U ⊔ V` is smoothness on `U` and on `V`.

Families live on `N × M`, the parameter first. A form on `M × N` is turned around by Mathlib's
`Diffeomorph.prodComm`, and its slices are then its pullbacks along `x ↦ (x, t)`
(`TauCeti.SmoothForm.mpullback_prodMk_mpullback_prodComm`).

## Main definitions

* `SymplecticGeometry.IsSmoothFamily J α`: the family `α` is the family of slices of a smooth form
  on `N × M`.
* `TauCeti.SmoothForm.ofSlices α hα`: the smooth form on `N × M` with slices `α t`, for a family
  with a smooth slice section.

## Main results

* `SymplecticGeometry.isSmoothFamily_iff_contMDiff`: a family is smooth exactly when its slice
  section is smooth.
* `SymplecticGeometry.IsSmoothFamily.contMDiff_val_apply`: the value of a smooth family at a
  point is smooth in the parameter.
* `SymplecticGeometry.IsSmoothFamily.contMDiff_apply`: the values of a smooth family at a point,
  on fixed tangent vectors, are smooth in the parameter.
* `SymplecticGeometry.IsSmoothFamily.contMDiff_val`: the value of a smooth family of forms on a
  normed space is jointly smooth in the parameter and the point.
* `SymplecticGeometry.IsSmoothFamily.contDiff_val`: the same as a `ContDiff` statement, when the
  parameter space is a normed space.
* `SymplecticGeometry.IsSmoothFamily.of_contMDiff_val`: conversely, a family of forms on a
  normed space whose value is jointly smooth in the parameter and the point is smooth.
* `SymplecticGeometry.IsSmoothFamily.of_contDiff_val`: the same as a `ContDiff` hypothesis, when
  the parameter space is a normed space.
* `SymplecticGeometry.isSmoothFamily_iff_contDiff_val`: over a normed parameter space, a family
  of forms on a normed space is smooth exactly when its value is a `C^∞` function of the
  parameter and the point.
* `SymplecticGeometry.IsSmoothFamily.continuous_val`: the value of a smooth family of forms on a
  normed space is jointly continuous in the parameter and the point.
* `SymplecticGeometry.IsSmoothFamily.continuous_apply_one`: the values of a smooth family of
  one-forms on `ℝ` on the unit vector are jointly continuous in the parameter and the point.
* `SymplecticGeometry.IsSmoothFamily.ext_on`: two smooth families that agree on a dense set of
  parameters are equal.
* `SymplecticGeometry.isSmoothFamily_mpullback_prodMk`: the slices of a form on `N × M` are a
  smooth family.
* `SymplecticGeometry.isSmoothFamily_const` and the closure lemmas `IsSmoothFamily.add`, `.neg`,
  `.sub`, `.smul`, `.fun_smul`, `.funSMul`, `.funSMul_family`, `.sum`, `.mpullback`,
  `.mpullback_family`, `.mextDeriv`, `.extendByZero_smul`, `.comp` and `.glue_collaredHalves`
  (concatenation of two families over `[0, 1]` that agree at the seam, by Tau Ceti's
  `ContMDiff.glue_collaredHalves`).
* `SymplecticGeometry.IsSmoothFamily.of_mpullback`: a family is smooth when its pullbacks along a
  smooth map with smooth local sections over an open cover of its target form a smooth family.
* `SymplecticGeometry.IsSmoothFamily.of_mpullback_prodMk_eq`: in particular, a family is smooth
  when its pullbacks along such a map are the slices of a smooth form.
* `SymplecticGeometry.IsSmoothFamily.contMDiffAt_of_mpullback_family`: the slice section of a
  family is smooth at `(p.1, f p)` when its pullbacks along the maps `f (t, ·)` form a smooth
  family and `q ↦ (q.1, f q)` is a local diffeomorphism at `p`.
* `SymplecticGeometry.isSmoothFamily_interiorₗ`: the contractions of a two-form with a jointly
  smooth family of vector fields form a smooth family of one-forms.
* `SymplecticGeometry.isSmoothFamily_iff_mpullback_inclusion_sup`: smoothness of a family on
  `U ⊔ V` is smoothness of its restrictions to `U` and to `V`.
* `TauCeti.SmoothForm.mpullback_prodMap_ofSlices`: the pullback of `ofSlices α hα` along a
  product `f × g` of smooth maps is the form with the slices `g^* (α (f t))`.
* `TauCeti.SmoothForm.mpullback_prodMk_mpullback_prodComm`: slices of a form on `M × N` turned
  around by `Diffeomorph.prodComm`.
* `TauCeti.SmoothForm.val_apply_eq_mpullback_val_apply`: a form on `M × N` semibasic for the
  projection to `M` is, at each point, its slice through that point evaluated on the components
  along `M`; and `TauCeti.SmoothForm.eq_of_forall_mpullback_eq`: two such forms with the same
  slices are equal.

## Implementation notes

The form with prescribed slices is smooth by `TauCeti.contMDiffAt_verticalForm_iff`
(`Geometry/Manifold/DifferentialForm/Vertical.lean`). The constant family is the pullback along
the projection, whose slices Tau Ceti's `TauCeti.SmoothForm.mpullback_prodMk_mpullback_snd`
computes. Locality in `M` comes from Tau Ceti's
`IsLocalDiffeomorphAt.contMDiffAt_mpullback_form_iff`, applied to `id × (U ↪ W)`, and the proof
of `SymplecticGeometry.IsSmoothFamily.extendByZero_smul` follows that of Tau Ceti's
`TauCeti.IsSmoothForm.extendByZero`.

The descent of smooth families along a map `f` with local sections
(`SymplecticGeometry.IsSmoothFamily.of_mpullback`) follows the proof of Tau Ceti's
`Manifold.IsSubmersion.isSmoothForm_mpullback_iff`, for the vertical forms of the families and
the map `id × f`, with the local sections `id × s`: near each point, a form is the pullback of
its pullback along `f`, by Tau Ceti's `TauCeti.contMDiffAt_mpullback_form_iff_of_section`. Unlike
that lemma, it needs no boundaryless source, so `N × M'` may have boundary, as for
`N = Set.Icc a b`.

For a family of maps `f (t, ·)`
(`SymplecticGeometry.IsSmoothFamily.contMDiffAt_of_mpullback_family`) the vertical forms do not
fit this pattern, since pulling back along `q ↦ (q.1, f q)` adds the derivative of `f` in `t`.
Instead, let `Ω` be a smooth form on `N × M'` whose slices are the pulled-back forms, and `L` a
local inverse of `q ↦ (q.1, f q)` near `(p.1, f p)`. Since `L` keeps the first coordinate, the
pullbacks of `Ω` along the maps `L (t, ·)` are the `α t` near `(p.1, f p)`, and they are jointly
smooth there by `SymplecticGeometry.contMDiffAt_sliceSection_of_eventually_eq_mpullback`, which
applies Tau Ceti's `ContMDiffAt.mpullback_form_family`.

The value of a form with no component along `N` is computed from its slices by
`TauCeti.RoughForm.IsSemibasicAt.apply_eq_of_mfderiv_eq`, for the projection `Prod.fst`
(`Geometry/Manifold/DifferentialForm/Semibasic.lean`).

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], proof of
  Theorem 3.2.4 (smooth families of forms, in Moser's argument).
-/

public section

noncomputable section

open Bundle Set Filter TopologicalSpace
open SymplecticGeometry (sliceSection sliceSection_def)
open scoped Manifold Topology ContDiff

namespace TauCeti

variable {E H M EN HN N F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H} [IsManifold I 1 M]
  [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
  [TopologicalSpace N] [ChartedSpace HN N] {J : ModelWithCorners ℝ EN HN} [IsManifold J 1 N]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

/-- **Slice sections are local in `M`.** For a family `β` of rough forms on an open subset `W`
of `M` and an open subset `U ≤ W`, the slice section of the restrictions of the `β t` to `U` is
`C^m` at `(t, x)` exactly when the slice section of `β` is `C^m` at `(t, x)`. -/
theorem contMDiffAt_mpullback_inclusion_iff_of_family {m : WithTop ℕ∞} {U W : Opens M}
    (h : U ≤ W) (β : N → RoughForm I W F k) (p : N × U) :
    ContMDiffAt (J.prod I) (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F)) m
        (sliceSection fun t ↦ mpullback I I (Opens.inclusion h) (β t)) p ↔
      ContMDiffAt (J.prod I) (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F)) m
        (sliceSection β)
        (p.1, Opens.inclusion h p.2) := by
  have hf : IsLocalDiffeomorphAt (J.prod I) (J.prod I) ω (Prod.map id (Opens.inclusion h)) p :=
    (SymplecticGeometry.isLocalDiffeomorph_id p.1).prodMap (isLocalDiffeomorph_inclusion h p.2)
  rw [← contMDiffAt_verticalForm_iff β,
    ← contMDiffAt_verticalForm_iff (fun t ↦ mpullback I I (Opens.inclusion h) (β t))]
  refine Iff.trans (Iff.of_eq (congrArg (ContMDiffAt _ _ _ · p) (funext fun q ↦ ?_)))
    (hf.contMDiffAt_mpullback_form_iff le_top)
  have hq : MDifferentiableAt (J.prod I) (J.prod I) (Prod.map id (Opens.inclusion h)) q :=
    mdifferentiableAt_id.prodMap ((contMDiff_inclusion h).mdifferentiableAt (n := 1) one_ne_zero)
  rw [mpullback_verticalForm_apply _ hq, Prod.map_snd',
    mpullback_comp_at mdifferentiableAt_snd
      ((contMDiff_inclusion h).mdifferentiableAt (n := 1) one_ne_zero), Prod.map_fst, id_eq,
    verticalForm_apply_eq_mpullback_snd]

end TauCeti

namespace TauCeti.SmoothForm

variable {E H M EN HN N F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H} [IsManifold I 1 M]
  [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
  [TopologicalSpace N] [ChartedSpace HN N] {J : ModelWithCorners ℝ EN HN} [IsManifold J 1 N]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

/-- **The form on `N × M` with prescribed slices.** For a family `α` of smooth forms on `M`
over `N` whose slice section `(t, y) ↦ (α t) y`, along the projection to `M`, is smooth, the
smooth form on `N × M` whose underlying form is the vertical form `TauCeti.verticalForm J` of the
family (`TauCeti.SmoothForm.coe_ofSlices`), so that it vanishes on the directions of `N`
(`TauCeti.SmoothForm.ofSlices_apply`), and
whose slice at `t` is `α t` (`TauCeti.SmoothForm.mpullback_prodMk_ofSlices`). -/
def ofSlices (α : N → SmoothForm I M F k)
    (hα : ContMDiff (J.prod I) (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F)) ∞
      (sliceSection fun t ↦ (α t).val)) :
    SmoothForm (J.prod I) (N × M) F k :=
  ⟨verticalForm J fun t ↦ (α t).val,
    IsSmoothForm.mem_smoothBundleForms <| (isSmoothForm_def _ _).mpr fun p ↦
      (contMDiffAt_verticalForm_iff (fun t ↦ (α t).val) p).mpr (hα p)⟩

variable {α : N → SmoothForm I M F k}
  {hα : ContMDiff (J.prod I) (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F)) ∞
    (sliceSection fun t ↦ (α t).val)}

/-- The underlying form of `TauCeti.SmoothForm.ofSlices α hα` is the vertical form of the family
of underlying forms of the `α t`. -/
theorem coe_ofSlices :
    (ofSlices α hα).val = verticalForm J fun t ↦ (α t).val :=
  (rfl)

/-- The form `TauCeti.SmoothForm.ofSlices α hα` evaluates `α t` on the components along `M` of
the tangent vectors at `(t, y)`. -/
theorem ofSlices_apply (p : N × M) (v : Fin k → TangentSpace (J.prod I) p) :
    (ofSlices α hα).val p v =
      (α p.1).val p.2 (fun i ↦ (Manifold.tangentSpaceProdEquiv p (v i)).2) := by
  simp only [coe_ofSlices, verticalForm_apply, Manifold.tangentSpaceProdEquiv_apply]

/-- The slice at `t` of `TauCeti.SmoothForm.ofSlices α hα` is `α t`. -/
@[simp]
theorem mpullback_prodMk_ofSlices (t : N) :
    mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) (ofSlices α hα) = α t :=
  (mpullback_eq_iff _).2 <| funext fun x ↦ by
    rw [coe_ofSlices]
    exact congrFun (mpullback_prodMk_verticalForm (fun t ↦ (α t).val) t) x

/-- The pullback of `TauCeti.SmoothForm.ofSlices α hα` along a product `f × g` of smooth maps
`f : N' → N` and `g : M' → M` is the form on `N' × M'` with the slices `g^* (α (f t))`. -/
theorem mpullback_prodMap_ofSlices {EN' HN' N' E' H' M' : Type*} [NormedAddCommGroup EN']
    [NormedSpace ℝ EN'] [TopologicalSpace HN'] [TopologicalSpace N'] [ChartedSpace HN' N']
    {J' : ModelWithCorners ℝ EN' HN'} [IsManifold J' 1 N'] [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [TopologicalSpace H'] [TopologicalSpace M'] [ChartedSpace H' M']
    {I' : ModelWithCorners ℝ E' H'} [IsManifold I' 1 M'] {f : N' → N} (hf : ContMDiff J' J ∞ f)
    {g : M' → M} (hg : ContMDiff I' I ∞ g)
    (hα' : ContMDiff (J'.prod I') (I'.prod 𝓘(ℝ, E' [⋀^Fin k]→L[ℝ] F)) ∞
      (sliceSection fun t ↦ (mpullback g hg (α (f t))).val)) :
    mpullback (Prod.map f g) (hf.prodMap hg) (ofSlices α hα) =
      ofSlices (fun t ↦ mpullback g hg (α (f t))) hα' := by
  rw [mpullback_eq_iff, coe_ofSlices, coe_ofSlices,
    mpullback_prodMap_verticalForm _ (hf.mdifferentiable (by simp))
      (hg.mdifferentiable (by simp))]
  simp only [coe_mpullback]

/-- **The two orders of a cylinder.** The slice at `t` of the pullback of a form `Ω` on `M × N`
along the swap `N × M → M × N` is the pullback of `Ω` along `x ↦ (x, t)`. -/
theorem mpullback_prodMk_mpullback_prodComm (Ω : SmoothForm (I.prod J) (M × N) F k) (t : N) :
    mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id)
        (mpullback (Diffeomorph.prodComm J I N M ∞) (Diffeomorph.prodComm J I N M ∞).contMDiff
          Ω) =
      mpullback (fun x ↦ (x, t)) (contMDiff_id.prodMk contMDiff_const) Ω := by
  have hcomp :
      (Diffeomorph.prodComm J I N M ∞ ∘ Prod.mk t : M → M × N) = fun x ↦ (x, t) := by
    rw [Diffeomorph.coe_prodComm]
    rfl
  simp only [mpullback_mpullback, hcomp]

/-- **A form with no component along `N` is read off its slices.** Let `η` be a smooth form on
`M × N` semibasic for `Prod.fst` at `p`: at `p` it vanishes whenever one of its arguments has
zero component along `M`. Its value at `p` on `v` is the value at `p.1` of its slice along
`x ↦ (x, p.2)` on the components along `M` of the `v i`. -/
theorem val_apply_eq_mpullback_val_apply {η : SmoothForm (I.prod J) (M × N) F k} {p : M × N}
    (hη : RoughForm.IsSemibasicAt (F := F) I Prod.fst η.val p)
    (v : Fin k → TangentSpace (I.prod J) p) :
    η.val p v = (mpullback (fun x ↦ (x, p.2)) (contMDiff_id.prodMk contMDiff_const) η).val p.1
      (fun i ↦ (Manifold.tangentSpaceProdEquiv p (v i)).1) := by
  rw [mpullback_apply]
  refine hη.apply_eq_of_mfderiv_eq fun i ↦ ?_
  have hd (y : TangentSpace I p.1) : mfderiv I (I.prod J) (fun x ↦ (x, p.2)) p.1 y =
      (Manifold.tangentSpaceProdEquiv (I := I) (J := J) p).symm (y, 0) :=
    (ContinuousLinearEquiv.eq_symm_apply _).mpr
      (TauCeti.Manifold.tangentSpaceProdEquiv_mfderiv_prodMk_left y)
  rw [hd, mfderiv_fst_apply, mfderiv_fst_apply, Manifold.tangentSpaceProdEquiv_symm_apply,
    Manifold.tangentSpaceProdEquiv_apply]

/-- **Forms with no component along `N` are determined by their slices.** Two smooth forms on
`M × N` semibasic for `Prod.fst`, that is, vanishing whenever one of their arguments has zero
component along `M`, and whose slices along `x ↦ (x, t)` agree for every `t`, are equal. -/
theorem eq_of_forall_mpullback_eq {η η' : SmoothForm (I.prod J) (M × N) F k}
    (hη : RoughForm.IsSemibasic (F := F) I Prod.fst η.val)
    (hη' : RoughForm.IsSemibasic (F := F) I Prod.fst η'.val)
    (h : ∀ t : N, mpullback (fun x ↦ (x, t)) (contMDiff_id.prodMk contMDiff_const) η =
      mpullback (fun x ↦ (x, t)) (contMDiff_id.prodMk contMDiff_const) η') :
    η = η' := by
  ext p v
  rw [val_apply_eq_mpullback_val_apply (RoughForm.isSemibasic_def.mp hη p),
    val_apply_eq_mpullback_val_apply (RoughForm.isSemibasic_def.mp hη' p), h]

end TauCeti.SmoothForm

namespace SymplecticGeometry

open TauCeti

variable {E H M EN HN N F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H} [IsManifold I 1 M]
  [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
  [TopologicalSpace N] [ChartedSpace HN N] {J : ModelWithCorners ℝ EN HN} [IsManifold J 1 N]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

variable (J) in
/-- **Smooth families of forms.** A family `α` of smooth `k`-forms on `M`, indexed by the points
of a manifold `N`, is smooth when it is the family of slices of a smooth form `Ω` on `N × M`:
`α t` is the pullback of `Ω` along the inclusion `y ↦ (t, y)`. -/
def IsSmoothFamily (α : N → SmoothForm I M F k) : Prop :=
  ∃ Ω : SmoothForm (J.prod I) (N × M) F k, ∀ t,
    SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) Ω = α t

/-- The defining property of `SymplecticGeometry.IsSmoothFamily`. -/
theorem isSmoothFamily_def {α : N → SmoothForm I M F k} :
    IsSmoothFamily J α ↔ ∃ Ω : SmoothForm (J.prod I) (N × M) F k, ∀ t,
      SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) Ω = α t :=
  Iff.rfl

/-- **Smooth families are those with a smooth slice section.** A family `α` of smooth forms on
`M` over `N` is smooth exactly when `(t, y) ↦ (α t) y` is a smooth section along the projection
`N × M → M`. -/
theorem isSmoothFamily_iff_contMDiff {α : N → SmoothForm I M F k} :
    IsSmoothFamily J α ↔ ContMDiff (J.prod I) (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F)) ∞
      (sliceSection fun t ↦ (α t).val) := by
  refine ⟨?_, fun h ↦ ⟨SmoothForm.ofSlices α h, SmoothForm.mpullback_prodMk_ofSlices⟩⟩
  rintro ⟨Ω, hΩ⟩
  simp_rw [← hΩ, SmoothForm.coe_mpullback, sliceSection_def]
  exact contMDiff_mpullback_prodMk_form Ω.contMDiff

/-- A family `α` of smooth forms on `M` over `N` is smooth exactly when its vertical form
`TauCeti.verticalForm J` on `N × M` is smooth. -/
theorem isSmoothFamily_iff_isSmoothForm {α : N → SmoothForm I M F k} :
    IsSmoothFamily J α ↔
      IsSmoothForm (J.prod I) ∞ (verticalForm J fun t ↦ (α t).val) := by
  rw [isSmoothFamily_iff_contMDiff, isSmoothForm_def]
  exact forall_congr' fun p ↦ (contMDiffAt_verticalForm_iff (fun t ↦ (α t).val) p).symm

namespace IsSmoothFamily

variable {α β : N → SmoothForm I M F k}

/-- The value of a smooth family at a point, as an alternating map on the tangent space there,
depends smoothly on the parameter. -/
theorem contMDiff_val_apply (h : IsSmoothFamily J α) (x : M) :
    ContMDiff (M' := E [⋀^Fin k]→L[ℝ] F) J 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F) ∞ fun t ↦ (α t).val x :=
  fun t ↦ ContMDiffAt.roughForm_family_apply (q₀ := (t, x)) (isSmoothFamily_iff_contMDiff.mp h _)

/-- The values of a smooth family at a point `x` on fixed tangent vectors depend smoothly on the
parameter. -/
theorem contMDiff_apply (h : IsSmoothFamily J α) (x : M) (v : Fin k → TangentSpace I x) :
    ContMDiff J 𝓘(ℝ, F) ∞ (fun t ↦ (α t).val x v) :=
  (ContinuousAlternatingMap.apply ℝ E F v).contMDiff.comp (h.contMDiff_val_apply x)

/-- **Joint smoothness of a smooth family.** For a smooth family `α` of `k`-forms on a normed
space `E`, the value `(α t) x`, an element of `E [⋀^Fin k]→L[ℝ] F`, depends smoothly on
`(t, x)`. -/
theorem contMDiff_val {α : N → SmoothForm 𝓘(ℝ, E) E F k} (h : IsSmoothFamily J α) :
    ContMDiff (M' := E [⋀^Fin k]→L[ℝ] F) (J.prod 𝓘(ℝ, E)) 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F) ∞
      fun p : N × E ↦ (α p.1).val p.2 := by
  intro p₀
  rw [isSmoothFamily_iff_contMDiff] at h
  have hc := contMDiffAt_sliceSection_iff.mp (h p₀)
  simpa only [sliceSection_apply,
    FiberBundle.trivializationAt_continuousAlternatingMap_model_space_apply_snd] using hc

/-- **Smooth families from jointly smooth values.** A family `α` of `k`-forms on a normed space
`E` whose value `(α t) x`, an element of `E [⋀^Fin k]→L[ℝ] F`, depends smoothly on `(t, x)` is a
smooth family. This is the converse of `SymplecticGeometry.IsSmoothFamily.contMDiff_val`. -/
theorem of_contMDiff_val {α : N → SmoothForm 𝓘(ℝ, E) E F k}
    (h : ContMDiff (M' := E [⋀^Fin k]→L[ℝ] F) (J.prod 𝓘(ℝ, E)) 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F) ∞
      fun p : N × E ↦ (α p.1).val p.2) :
    IsSmoothFamily J α := by
  rw [isSmoothFamily_iff_contMDiff]
  refine fun p₀ ↦ contMDiffAt_sliceSection_iff.mpr ?_
  simpa only [sliceSection_apply,
    FiberBundle.trivializationAt_continuousAlternatingMap_model_space_apply_snd] using h p₀

/-- **Joint continuity of a smooth family.** For a smooth family `α` of `k`-forms on a normed
space `E`, the value `(α t) x`, an element of `E [⋀^Fin k]→L[ℝ] F`, depends continuously on
`(t, x)`. -/
theorem continuous_val {α : N → SmoothForm 𝓘(ℝ, E) E F k} (h : IsSmoothFamily J α) :
    Continuous (Y := E [⋀^Fin k]→L[ℝ] F) fun p : N × E ↦ (α p.1).val p.2 :=
  h.contMDiff_val.continuous

/-- **Joint smoothness of a smooth family over a normed space.** For a smooth family `α` of
`k`-forms on a normed space `E` over a normed space `L`, the value `(α t) x`, an element of
`E [⋀^Fin k]→L[ℝ] F`, is a `C^∞` function of `(t, x) ∈ L × E`. -/
theorem contDiff_val {L : Type*} [NormedAddCommGroup L] [NormedSpace ℝ L]
    {α : L → SmoothForm 𝓘(ℝ, E) E F k} (h : IsSmoothFamily 𝓘(ℝ, L) α) :
    ContDiff (F := E [⋀^Fin k]→L[ℝ] F) ℝ ∞ fun p : L × E ↦ (α p.1).val p.2 :=
  contMDiff_iff_contDiff.mp (contMDiff_prod_modelWithCornersSelf_iff.mp h.contMDiff_val)

/-- **Smooth families from `C^∞` values over a normed space.** A family `α` of `k`-forms on a
normed space `E` over a normed space `L`, whose value `(α t) x`, an element of
`E [⋀^Fin k]→L[ℝ] F`, is a `C^∞` function of `(t, x) ∈ L × E`, is a smooth family. This is the
converse of `SymplecticGeometry.IsSmoothFamily.contDiff_val`. -/
theorem of_contDiff_val {L : Type*} [NormedAddCommGroup L] [NormedSpace ℝ L]
    {α : L → SmoothForm 𝓘(ℝ, E) E F k}
    (h : ContDiff (F := E [⋀^Fin k]→L[ℝ] F) ℝ ∞ fun p : L × E ↦ (α p.1).val p.2) :
    IsSmoothFamily 𝓘(ℝ, L) α :=
  of_contMDiff_val (contMDiff_prod_modelWithCornersSelf_iff.mpr (contMDiff_iff_contDiff.mpr h))

/-- For a smooth family `α` of one-forms on `ℝ`, the value of `α t` at `s` on the unit tangent
vector `1` depends jointly continuously on `(t, s)`. -/
theorem continuous_apply_one {α : N → SmoothForm 𝓘(ℝ, ℝ) ℝ F 1} (h : IsSmoothFamily J α) :
    Continuous fun p : N × ℝ ↦ (α p.1).val p.2 (fun _ ↦ 1) :=
  (ContinuousAlternatingMap.apply ℝ ℝ F fun _ ↦ (1 : ℝ)).continuous.comp h.continuous_val

/-- Two smooth families of forms that agree at the parameters of a dense set are equal. -/
theorem ext_on (hα : IsSmoothFamily J α) (hβ : IsSmoothFamily J β) {s : Set N} (hs : Dense s)
    (h : EqOn α β s) : α = β := by
  funext t
  ext x v
  exact congrFun (Continuous.ext_on hs (hα.contMDiff_apply x v).continuous
    (hβ.contMDiff_apply x v).continuous fun r hr ↦ by rw [h hr]) t

/-- The sum of two smooth families is smooth. -/
protected theorem add (hα : IsSmoothFamily J α) (hβ : IsSmoothFamily J β) :
    IsSmoothFamily J (fun t ↦ α t + β t) := by
  obtain ⟨Ω, hΩ⟩ := hα
  obtain ⟨Θ, hΘ⟩ := hβ
  exact ⟨Ω + Θ, fun t ↦ by rw [map_add, hΩ, hΘ]⟩

/-- The negative of a smooth family is smooth. -/
protected theorem neg (hα : IsSmoothFamily J α) : IsSmoothFamily J (fun t ↦ -α t) := by
  obtain ⟨Ω, hΩ⟩ := hα
  exact ⟨-Ω, fun t ↦ by rw [map_neg, hΩ]⟩

/-- The difference of two smooth families is smooth. -/
protected theorem sub (hα : IsSmoothFamily J α) (hβ : IsSmoothFamily J β) :
    IsSmoothFamily J (fun t ↦ α t - β t) := by
  obtain ⟨Ω, hΩ⟩ := hα
  obtain ⟨Θ, hΘ⟩ := hβ
  exact ⟨Ω - Θ, fun t ↦ by rw [map_sub, hΩ, hΘ]⟩

/-- A constant multiple of a smooth family is smooth. -/
protected theorem smul (hα : IsSmoothFamily J α) (c : ℝ) :
    IsSmoothFamily J (fun t ↦ c • α t) := by
  obtain ⟨Ω, hΩ⟩ := hα
  exact ⟨c • Ω, fun t ↦ by rw [map_smul, hΩ]⟩

/-- The product of a smooth family with a smooth function of the parameter is smooth. -/
protected theorem fun_smul (hα : IsSmoothFamily J α) {c : N → ℝ}
    (hc : ContMDiff J 𝓘(ℝ) ∞ c) :
    IsSmoothFamily J (fun t ↦ c t • α t) := by
  rw [isSmoothFamily_iff_isSmoothForm] at hα ⊢
  simp only [Submodule.coe_smul, verticalForm_fun_smul_fst]
  exact hα.fun_smul (hc.comp contMDiff_fst)

/-- The product of a smooth family with a family `g` of smooth functions on `M` is smooth when
`g` is jointly smooth, as a function of the parameter and the point. -/
protected theorem funSMul_family (hα : IsSmoothFamily J α) (g : N → C^∞⟮I, M; ℝ⟯)
    (hg : ContMDiff (J.prod I) 𝓘(ℝ) ∞ fun p : N × M ↦ g p.1 p.2) :
    IsSmoothFamily J (fun t ↦ SmoothForm.funSMulₗ (g t) (α t)) := by
  obtain ⟨Ω, hΩ⟩ := hα
  let G : C^∞⟮J.prod I, N × M; ℝ⟯ := ⟨_, hg⟩
  refine ⟨SmoothForm.funSMulₗ G Ω, fun t ↦ ?_⟩
  rw [SmoothForm.mpullback_funSMulₗ, hΩ]
  congr 1

/-- The product of a smooth family with a fixed smooth function on `M` is smooth. -/
protected theorem funSMul (hα : IsSmoothFamily J α) (g : C^∞⟮I, M; ℝ⟯) :
    IsSmoothFamily J (fun t ↦ SmoothForm.funSMulₗ g (α t)) :=
  hα.funSMul_family (fun _ ↦ g) (g.contMDiff.comp contMDiff_snd)

end IsSmoothFamily

/-- A family `α` of `k`-forms on a normed space `E` over a normed space `L` is smooth exactly
when its value `(α t) x`, an element of `E [⋀^Fin k]→L[ℝ] F`, is a `C^∞` function of
`(t, x) ∈ L × E`. -/
theorem isSmoothFamily_iff_contDiff_val {L : Type*} [NormedAddCommGroup L] [NormedSpace ℝ L]
    {α : L → SmoothForm 𝓘(ℝ, E) E F k} :
    IsSmoothFamily 𝓘(ℝ, L) α ↔
      ContDiff (F := E [⋀^Fin k]→L[ℝ] F) ℝ ∞ fun p : L × E ↦ (α p.1).val p.2 :=
  ⟨IsSmoothFamily.contDiff_val, IsSmoothFamily.of_contDiff_val⟩

/-- A constant family is smooth: it is the family of slices of the pullback of its value along
the projection `N × M → M`. -/
theorem isSmoothFamily_const (α : SmoothForm I M F k) : IsSmoothFamily J (fun _ : N ↦ α) :=
  ⟨_, fun t ↦ SmoothForm.mpullback_prodMk_mpullback_snd α t⟩

/-- The slices `t ↦ Ω (t, ·)` of a smooth form `Ω` on `N × M` form a smooth family. -/
theorem isSmoothFamily_mpullback_prodMk (Ω : SmoothForm (J.prod I) (N × M) F k) :
    IsSmoothFamily J fun t ↦
      SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) Ω :=
  ⟨Ω, fun _ ↦ rfl⟩

namespace IsSmoothFamily

/-- A finite sum of smooth families is smooth. -/
protected theorem sum {ι : Type*} {s : Finset ι} {α : ι → N → SmoothForm I M F k}
    (hα : ∀ i ∈ s, IsSmoothFamily J (α i)) :
    IsSmoothFamily J (fun t ↦ ∑ i ∈ s, α i t) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using isSmoothFamily_const (J := J) (N := N) 0
  | insert i s hi ih =>
    simp_rw [Finset.sum_insert hi]
    exact (hα i (Finset.mem_insert_self i s)).add
      (ih fun j hj ↦ hα j (Finset.mem_insert_of_mem hj))

/-- The exterior derivatives of a smooth family form a smooth family. -/
protected theorem mextDeriv [IsManifold I 2 M] [IsManifold J 2 N] {α : N → SmoothForm I M F k}
    (hα : IsSmoothFamily J α) : IsSmoothFamily J (fun t ↦ mextDerivₗ I k (α t)) := by
  obtain ⟨Ω, hΩ⟩ := hα
  exact ⟨mextDerivₗ (J.prod I) k Ω, fun t ↦ by
    dsimp only
    rw [← SmoothForm.mextDerivₗ_mpullback, hΩ]⟩

/-- **Concatenation of smooth families.** Two smooth families `α` and `β` over `[0, 1]` with
`α 1 = β 0` concatenate to a smooth family `SymplecticGeometry.collaredConcat α β`. -/
protected theorem glue_collaredHalves {α β : unitInterval → SmoothForm I M F k}
    (hα : IsSmoothFamily (𝓡∂ 1) α) (hβ : IsSmoothFamily (𝓡∂ 1) β) (hαβ : α 1 = β 0) :
    IsSmoothFamily (𝓡∂ 1) (collaredConcat α β) := by
  rw [isSmoothFamily_iff_contMDiff, sliceSection_def] at hα hβ ⊢
  refine (hα.glue_collaredHalves_left hβ (fun x ↦ by rw [hαβ]) le_rfl).congr fun p ↦ ?_
  exact apply_collaredConcat (fun γ : SmoothForm I M F k ↦ TotalSpace.mk'
    (E := fun y : M ↦ TangentSpace I y [⋀^Fin k]→L[ℝ] Trivial M F y) _ p.2 (γ.val p.2))
    α β p.1

section Maps

variable {E' H' M' EN' HN' N' : Type*}
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  [TopologicalSpace M'] [ChartedSpace H' M'] {I' : ModelWithCorners ℝ E' H'} [IsManifold I' 1 M']
  [NormedAddCommGroup EN'] [NormedSpace ℝ EN'] [TopologicalSpace HN']
  [TopologicalSpace N'] [ChartedSpace HN' N'] {J' : ModelWithCorners ℝ EN' HN'}
  [IsManifold J' 1 N'] {α : N → SmoothForm I M F k}

/-- **Pullback of a smooth family along a smooth family of maps.** For a smooth map
`f : N × M' → M`, the pullbacks of `α t` along the slices `f (t, ·)` form a smooth family. -/
protected theorem mpullback_family (hα : IsSmoothFamily J α) {f : N × M' → M}
    (hf : ContMDiff (J.prod I') I ∞ f) :
    IsSmoothFamily J (fun t ↦ SmoothForm.mpullback (fun x ↦ f (t, x))
      (hf.comp (contMDiff_const.prodMk contMDiff_id)) (α t)) := by
  obtain ⟨Ω, hΩ⟩ := hα
  refine ⟨SmoothForm.mpullback (fun p ↦ (p.1, f p)) (contMDiff_fst.prodMk hf) Ω, fun t ↦ ?_⟩
  have hcomp : ((fun p ↦ (p.1, f p)) ∘ Prod.mk t : M' → N × M) =
      Prod.mk t ∘ fun x ↦ f (t, x) := rfl
  simp only [← hΩ, SmoothForm.mpullback_mpullback, hcomp]

/-- The pullbacks of a smooth family along a smooth map form a smooth family. -/
protected theorem mpullback (hα : IsSmoothFamily J α) (f : M' → M) (hf : ContMDiff I' I ∞ f) :
    IsSmoothFamily J (fun t ↦ SmoothForm.mpullback f hf (α t)) :=
  hα.mpullback_family (f := fun p : N × M' ↦ f p.2) (hf.comp contMDiff_snd)

/-- Reparametrizing a smooth family by a smooth map of parameter manifolds gives a smooth
family. -/
protected theorem comp (hα : IsSmoothFamily J α) (φ : N' → N) (hφ : ContMDiff J' J ∞ φ) :
    IsSmoothFamily J' (fun s ↦ α (φ s)) := by
  obtain ⟨Ω, hΩ⟩ := hα
  refine ⟨SmoothForm.mpullback (Prod.map φ id) (hφ.prodMap contMDiff_id) Ω, fun s ↦ ?_⟩
  have hcomp : (Prod.map φ id ∘ Prod.mk s : M → N × M) = Prod.mk (φ s) := rfl
  simp only [← hΩ, SmoothForm.mpullback_mpullback, hcomp]

/-- **Smooth families descend along maps with local sections.** Let `f : M' → M` be smooth, and
let every point of `M` have an open neighbourhood `U` with a map `s`, smooth on `U`, such that
`f (s y) = y` for `y ∈ U`. A family `α` of forms on `M` whose pullbacks along `f` form a smooth
family is smooth. -/
theorem of_mpullback {f : M' → M} (hf : ContMDiff I' I ∞ f)
    (hsec : ∀ x : M, ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
      ∃ s : M → M', ContMDiffOn I I' ∞ s U ∧ ∀ y ∈ U, f (s y) = y)
    (h : IsSmoothFamily J (fun t ↦ SmoothForm.mpullback f hf (α t))) :
    IsSmoothFamily J α := by
  rw [isSmoothFamily_iff_isSmoothForm, isSmoothForm_def] at h ⊢
  rintro ⟨t, x⟩
  obtain ⟨U, hU, hxU, s, hs, hfs⟩ := hsec x
  have hpull : mpullback (J.prod I') (J.prod I) (Prod.map id f)
      (verticalForm J fun t ↦ (α t).val) =
        verticalForm J fun t ↦ (SmoothForm.mpullback f hf (α t)).val := by
    rw [mpullback_prodMap_verticalForm _ mdifferentiable_id (hf.mdifferentiable (by simp))]
    simp only [id_eq, SmoothForm.coe_mpullback]
  have key := contMDiffAt_mpullback_form_iff_of_section (m := ∞) (n := ∞)
    (f := Prod.map id f) (x := (t, s x)) (s := Prod.map id s) (U := univ ×ˢ U)
    («ω» := verticalForm J fun t ↦ (α t).val)
    (isOpen_univ.prod hU) ⟨mem_univ _, by simpa only [Prod.map_snd, hfs x hxU] using hxU⟩
    (by simp only [Prod.map_apply, id_eq, hfs x hxU])
    ((contMDiffOn_univ.mpr contMDiff_id).prodMap hs)
    (fun y hy ↦ Prod.ext rfl (hfs y.2 hy.2))
    (contMDiff_id.prodMap hf).contMDiffAt (by simp)
  rw [hpull] at key
  simpa only [Prod.map_apply, id_eq, hfs x hxU] using key.mp (h (t, s x))

/-- **A family read off the slices of a smooth form is smooth.** Let `f : M' → M` be smooth with
smooth local sections over an open neighbourhood of every point of `M`, and `σ` a smooth form on
`M' × N`. A family `τ` of forms on `M` whose pullback `f^* (τ t)` along `f` is, for every `t`,
the pullback of `σ` along `x ↦ (x, t)` is smooth. -/
theorem of_mpullback_prodMk_eq {f : M' → M} (hf : ContMDiff I' I ∞ f)
    (hsec : ∀ x : M, ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
      ∃ s : M → M', ContMDiffOn I I' ∞ s U ∧ ∀ y ∈ U, f (s y) = y)
    {σ : SmoothForm (I'.prod J) (M' × N) F k} {τ : N → SmoothForm I M F k}
    (h : ∀ t, SmoothForm.mpullback (fun x ↦ (x, t)) (contMDiff_id.prodMk contMDiff_const) σ =
      SmoothForm.mpullback f hf (τ t)) :
    IsSmoothFamily J τ := by
  refine of_mpullback hf hsec ?_
  simp_rw [← h, ← SmoothForm.mpullback_prodMk_mpullback_prodComm]
  exact isSmoothFamily_mpullback_prodMk _

/-- **Smoothness through a smooth family of local diffeomorphisms.** Let `f : N × M' → M` be
smooth, and `p` a point of `N × M'` at which `q ↦ (q.1, f q)` is a local diffeomorphism. If the
pullbacks of the `α t` along the maps `f (t, ·)` form a smooth family, then the slice section
`(t, y) ↦ (α t) y` of `α` is smooth at `(p.1, f p)`. -/
theorem contMDiffAt_of_mpullback_family {f : N × M' → M} (hf : ContMDiff (J.prod I') I ∞ f)
    {p : N × M'} (hΦ : IsLocalDiffeomorphAt (J.prod I') (J.prod I) ∞ (fun q ↦ (q.1, f q)) p)
    (h : IsSmoothFamily J (fun t ↦ SmoothForm.mpullback (fun x ↦ f (t, x))
      (hf.comp (contMDiff_const.prodMk contMDiff_id)) (α t))) :
    ContMDiffAt (J.prod I) (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F)) ∞
      (sliceSection fun t ↦ (α t).val) (p.1, f p) := by
  obtain ⟨Ω, hΩ⟩ := h
  -- A local inverse `L` of `q ↦ (q.1, f q)` near `(p.1, f p)`; it keeps the first coordinate.
  set L := hΦ.localInverse
  have hsrc : L.source ∈ 𝓝 (p.1, f p) :=
    hΦ.localInverse_open_source.mem_nhds hΦ.localInverse_mem_source
  have hLd : ∀ z ∈ L.source, ContMDiffAt (J.prod I) (J.prod I') ∞ L z := fun z hz ↦
    hΦ.contMDiffOn_localInverse.contMDiffAt (hΦ.localInverse_open_source.mem_nhds hz)
  -- Near `(p.1, f p)`, the `α t` are the slices of the pullback of `Ω` along `L`.
  refine contMDiffAt_sliceSection_of_eventually_eq_mpullback (g := fun t y ↦ L (t, y))
    (Ω.contMDiff _) (hLd _ (mem_of_mem_nhds hsrc)) (by simp) ?_
  filter_upwards [hsrc] with q hq
  obtain ⟨t, y⟩ := q
  have hy : {y' | (t, y') ∈ L.source} ∈ 𝓝 y :=
    (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds
      (hΦ.localInverse_open_source.mem_nhds hq)
  obtain ⟨s, hs_def⟩ : ∃ s : M → M', s = fun y' ↦ (L (t, y')).2 := ⟨_, rfl⟩
  have hLs : ∀ y' ∈ {y' | (t, y') ∈ L.source}, L (t, y') = (t, s y') := fun y' hy' ↦
    Prod.ext (congrArg Prod.fst (hΦ.localInverse_right_inv hy') :) (by rw [hs_def])
  have hs : MDifferentiableAt I I' s y := by
    rw [hs_def]
    exact (contMDiffAt_snd.comp _ ((hLd _ hq).comp _
      (contMDiffAt_const.prodMk contMDiffAt_id))).mdifferentiableAt (by simp)
  have hft : MDifferentiableAt I' I (fun x ↦ f (t, x)) (s y) :=
    (hf.comp (contMDiff_const.prodMk contMDiff_id)).mdifferentiableAt (by simp)
  have hL : (fun y' ↦ L (t, y')) =ᶠ[𝓝 y] Prod.mk t ∘ s := by
    filter_upwards [hy] with y' hy'
    exact hLs y' hy'
  have hfs : (fun x ↦ f (t, x)) ∘ s =ᶠ[𝓝 y] id := by
    filter_upwards [hy] with y' hy'
    have h1 := congrArg Prod.snd (hΦ.localInverse_right_inv hy')
    rw [hLs y' hy'] at h1
    exact h1
  have hslice := congrArg Subtype.val (hΩ t)
  simp only [SmoothForm.coe_mpullback] at hslice
  have hmk : MDifferentiableAt I' (J.prod I') (Prod.mk t) (s y) :=
    (contMDiff_const.prodMk contMDiff_id (n := ∞)).mdifferentiableAt (by simp)
  symm
  rw [hL.mpullback_eq, mpullback_comp_at hs hmk, hslice, ← mpullback_comp_at hs hft,
    hfs.mpullback_apply_eq_self]

end Maps

/-- **Cut-off and extension by zero of a smooth family.** Let `α` be a smooth family of forms on
an open subset `U ≤ W`, and `g` a smooth function on `W` vanishing near every point of `W` outside
`U`. A family `β` of smooth forms on `W` whose value at `t` is the extension by zero of
`g • α t` is smooth. -/
protected theorem extendByZero_smul {U W : Opens M} (h : U ≤ W)
    {α : N → SmoothForm I U F k} (hα : IsSmoothFamily J α) {g : W → ℝ}
    (hg : ContMDiff I 𝓘(ℝ) ∞ g)
    (hzero : ∀ x : W, (x : M) ∉ U → ∀ᶠ y in 𝓝 x, g y = 0)
    {β : N → SmoothForm I W F k}
    (hβ : ∀ t, (β t).val =
      RoughForm.extendByZero W fun y : U ↦ g (Opens.inclusion h y) • (α t).val y) :
    IsSmoothFamily J β := by
  rw [isSmoothFamily_iff_contMDiff]
  rintro ⟨t, x⟩
  by_cases hx : (x : M) ∈ U
  · -- Near `x`, the restriction of `β` to `U` is the smooth family `g • α`.
    have hgα :=
      (isSmoothFamily_iff_isSmoothForm.mp hα).fun_smul
        (f := fun q : N × U ↦ g (Opens.inclusion h q.2))
        ((hg.comp (contMDiff_inclusion h)).comp contMDiff_snd)
    refine (contMDiffAt_mpullback_inclusion_iff_of_family h (fun s ↦ (β s).val)
      (t, ⟨x, hx⟩)).mp ?_
    simp only [hβ, RoughForm.mpullback_inclusion_extendByZero]
    refine (contMDiffAt_verticalForm_iff
      (fun s y ↦ g (Opens.inclusion h y) • (α s).val y) _).mp ?_
    simpa only [verticalForm_fun_smul] using hgα.contMDiff (t, ⟨x, hx⟩)
  · -- Near `x`, every `β s` vanishes.
    refine contMDiffAt_sliceSection_of_eventually_eq_zero ?_
    have hy : ∀ᶠ y in 𝓝 x, ∀ s, (β s).val y = 0 := by
      filter_upwards [(hzero x hx).eventually_nhds] with y hy s
      rw [hβ]
      exact (RoughForm.eventually_extendByZero_smul_eq_zero h (α s).val hy).self_of_nhds
    exact ((continuous_snd.tendsto (t, x)).eventually hy).mono fun q hq ↦ hq q.1

end IsSmoothFamily

/-- **Smoothness of families is local.** A family of forms on `U ⊔ V` is smooth exactly when its
restrictions to `U` and to `V` are. -/
theorem isSmoothFamily_iff_mpullback_inclusion_sup {U V : Opens M}
    {α : N → SmoothForm I (U ⊔ V : Opens M) F k} :
    IsSmoothFamily J α ↔
      IsSmoothFamily J (fun t ↦
        SmoothForm.mpullback (Opens.inclusion le_sup_left) (contMDiff_inclusion _) (α t)) ∧
      IsSmoothFamily J (fun t ↦
        SmoothForm.mpullback (Opens.inclusion le_sup_right) (contMDiff_inclusion _) (α t)) := by
  refine ⟨fun h ↦ ⟨h.mpullback _ _, h.mpullback _ _⟩, fun ⟨hU, hV⟩ ↦ ?_⟩
  rw [isSmoothFamily_iff_contMDiff] at hU hV ⊢
  rintro ⟨t, x⟩
  rcases Opens.mem_sup.mp x.property with hx | hx
  · exact (contMDiffAt_mpullback_inclusion_iff_of_family le_sup_left (fun s ↦ (α s).val)
      (t, ⟨x, hx⟩)).mp
        (by simpa only [SmoothForm.coe_mpullback] using hU (t, ⟨x, hx⟩))
  · exact (contMDiffAt_mpullback_inclusion_iff_of_family le_sup_right (fun s ↦ (α s).val)
      (t, ⟨x, hx⟩)).mp
        (by simpa only [SmoothForm.coe_mpullback] using hV (t, ⟨x, hx⟩))

section Interior

variable {E H M EN HN N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H} [IsManifold I ∞ M]
  [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
  [TopologicalSpace N] [ChartedSpace HN N] {J : ModelWithCorners ℝ EN HN} [IsManifold J 1 N]

/-- For a jointly smooth family `X_t`, `t ∈ N`, of vector fields, the contractions `ι_{X_t} σ` of
a two-form `σ` form a smooth family of one-forms. -/
theorem isSmoothFamily_interiorₗ (σ : SmoothTwoForm I M)
    {X : N → Cₛ^∞⟮I; E, TangentSpace I (M := M)⟯}
    (hX : ContMDiff (J.prod I) I.tangent ∞
      fun p : N × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)) :
    IsSmoothFamily J fun t ↦ σ.interiorₗ (X t) := by
  rw [isSmoothFamily_iff_contMDiff, sliceSection_def]
  intro p
  rw [← SmoothForm.contMDiffAt_sectionAlong_degreeOneEquiv_iff (b := Prod.snd)
    (α := fun q : N × M ↦ σ.interiorₗ (X q.1))]
  simp only [SmoothTwoForm.degreeOneEquiv_interiorₗ]
  exact ((σ.contMDiff_flat.comp contMDiff_snd).clm_bundle_apply hX) p

end Interior

end SymplecticGeometry
