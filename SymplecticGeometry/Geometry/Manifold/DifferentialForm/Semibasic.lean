/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic
public import SymplecticGeometry.LinearAlgebra.Alternating.Conormal
import TauCeti.Geometry.Manifold.MFDeriv.Prod

/-!
# Forms semibasic for a map

A smooth form `η` on `M` is *semibasic* for a map `f : M → B` at a point `x`
(`TauCeti.SmoothForm.IsSemibasicAt IB f η x`) when its value at `x` vanishes as soon as one of its
arguments lies in the kernel of the differential of `f` at `x`, that is, when it lies in Tau
Ceti's `Submodule.conormalForms` of that kernel. It is semibasic for `f`
(`TauCeti.SmoothForm.IsSemibasic IB f η`) when this holds at every point. The condition is
pointwise: unlike Tau Ceti's `TauCeti.RoughForm.IsBasic`, it does not compare the values of `η`
at two points of a fibre of `f`.

## Main definitions

* `TauCeti.SmoothForm.IsSemibasicAt IB f η x`: the form `η` is semibasic for `f` at `x`.
* `TauCeti.SmoothForm.IsSemibasic IB f η`: the form `η` is semibasic for `f` at every point.

## Main results

* `TauCeti.SmoothForm.IsSemibasicAt.apply_eq_of_mfderiv_eq`: at `x`, a form semibasic for `f`
  takes the same value on two tuples whose images under the differential of `f` agree.
* Closure of both predicates under `0`, `+`, `-` and real multiples, and every `0`-form is
  semibasic.
* `TauCeti.SmoothForm.IsSemibasicAt.mpullback_of_comp_eq`: for a smooth `g` and maps with
  `f ∘ g = h ∘ f'`, the pullback along `g` of a form semibasic for `f` is semibasic for `f'`;
  in particular (`TauCeti.SmoothForm.IsSemibasicAt.mpullback_comp`) it is semibasic for `f ∘ g`.
  The linear step is `Submodule.compLinearMap_mem_conormalForms`.
* `TauCeti.SmoothForm.isSemibasicAt_fst_iff`: a form on `M × N` is semibasic for `Prod.fst` at
  `p` exactly when it vanishes at `p` on every tuple one of whose vectors has zero component
  along `M`; and `TauCeti.SmoothForm.IsSemibasic.mpullback_prodMap`: pullback along a product of
  smooth maps keeps forms semibasic for `Prod.fst`.
-/

public section

noncomputable section

open Manifold
open scoped Manifold ContDiff

namespace TauCeti.SmoothForm

variable {E H M EB HB B F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H} [IsManifold I 1 M]
  [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  [TopologicalSpace B] [ChartedSpace HB B] {IB : ModelWithCorners ℝ EB HB}
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ} {f : M → B}

section IsSemibasicAt

variable (IB f) in
/-- **Forms semibasic for a map at a point.** A smooth form `η` on `M` is semibasic for
`f : M → B` at `x` when its value at `x` vanishes as soon as one of its arguments lies in the
kernel of the differential of `f` at `x`, that is, is tangent to the fibre of `f` through `x`
when `f` is a submersion. -/
def IsSemibasicAt (η : SmoothForm I M F k) (x : M) : Prop :=
  (η.val x).toAlternatingMap ∈ (mfderiv I IB f x).ker.conormalForms (Fin k) F

/-- The defining property of `TauCeti.SmoothForm.IsSemibasicAt`. -/
theorem isSemibasicAt_def {η : SmoothForm I M F k} {x : M} :
    IsSemibasicAt IB f η x ↔
      (η.val x).toAlternatingMap ∈ (mfderiv I IB f x).ker.conormalForms (Fin k) F :=
  Iff.rfl

/-- A form is semibasic for `f` at `x` exactly when its value at `x` vanishes on every tuple one
of whose vectors is sent to zero by the differential of `f` at `x`. -/
theorem isSemibasicAt_iff {η : SmoothForm I M F k} {x : M} :
    IsSemibasicAt IB f η x ↔ ∀ (v : Fin k → TangentSpace I x) (i : Fin k),
      mfderiv I IB f x (v i) = 0 → η.val x v = 0 := by
  simp only [isSemibasicAt_def, Submodule.mem_conormalForms, LinearMap.mem_ker,
    ContinuousLinearMap.coe_coe, ContinuousAlternatingMap.coe_toAlternatingMap]

/-- A form semibasic for `f` at `x` vanishes at `x` on tuples one of which is sent to zero by
the differential of `f`. -/
theorem IsSemibasicAt.apply_eq_zero {η : SmoothForm I M F k} {x : M}
    (hη : IsSemibasicAt IB f η x) (v : Fin k → TangentSpace I x) (i : Fin k)
    (hv : mfderiv I IB f x (v i) = 0) : η.val x v = 0 :=
  isSemibasicAt_iff.mp hη v i hv

/-- **Semibasic forms only see the differential.** At `x`, a form semibasic for `f` takes the
same value on two tuples of tangent vectors whose images under the differential of `f` at `x`
agree. -/
theorem IsSemibasicAt.apply_eq_of_mfderiv_eq {η : SmoothForm I M F k} {x : M}
    (hη : IsSemibasicAt IB f η x) {v w : Fin k → TangentSpace I x}
    (h : ∀ i, mfderiv I IB f x (v i) = mfderiv I IB f x (w i)) : η.val x v = η.val x w :=
  Submodule.conormalForms_apply_eq_of_sub_mem (α := (η.val x).toAlternatingMap) hη
    fun i ↦ by simp [h i]

variable (IB f) in
/-- Every `0`-form is semibasic for every map at every point. -/
theorem isSemibasicAt_of_degree_zero (η : SmoothForm I M F 0) (x : M) :
    IsSemibasicAt IB f η x :=
  isSemibasicAt_iff.mpr fun _ i ↦ i.elim0

variable (IB f) in
/-- The zero form is semibasic for every map at every point. -/
@[simp]
theorem isSemibasicAt_zero (x : M) : IsSemibasicAt IB f (0 : SmoothForm I M F k) x :=
  Submodule.zero_mem _

/-- The sum of two forms semibasic for `f` at `x` is semibasic for `f` at `x`. -/
theorem IsSemibasicAt.add {η η' : SmoothForm I M F k} {x : M} (hη : IsSemibasicAt IB f η x)
    (hη' : IsSemibasicAt IB f η' x) : IsSemibasicAt IB f (η + η') x :=
  add_mem hη hη'

/-- The negative of a form semibasic for `f` at `x` is semibasic for `f` at `x`. -/
theorem IsSemibasicAt.neg {η : SmoothForm I M F k} {x : M} (hη : IsSemibasicAt IB f η x) :
    IsSemibasicAt IB f (-η) x :=
  neg_mem hη

/-- The difference of two forms semibasic for `f` at `x` is semibasic for `f` at `x`. -/
theorem IsSemibasicAt.sub {η η' : SmoothForm I M F k} {x : M} (hη : IsSemibasicAt IB f η x)
    (hη' : IsSemibasicAt IB f η' x) : IsSemibasicAt IB f (η - η') x :=
  sub_mem hη hη'

/-- A real multiple of a form semibasic for `f` at `x` is semibasic for `f` at `x`. -/
theorem IsSemibasicAt.smul {η : SmoothForm I M F k} {x : M} (hη : IsSemibasicAt IB f η x)
    (c : ℝ) : IsSemibasicAt IB f (c • η) x :=
  Submodule.smul_mem _ c hη

end IsSemibasicAt

section IsSemibasic

variable (IB f) in
/-- **Forms semibasic for a map.** A smooth form `η` on `M` is semibasic for `f : M → B` when it
is so at every point: its value at `x` vanishes as soon as one of its arguments lies in the
kernel of the differential of `f` at `x`. -/
def IsSemibasic (η : SmoothForm I M F k) : Prop :=
  ∀ x, IsSemibasicAt IB f η x

/-- The defining property of `TauCeti.SmoothForm.IsSemibasic`. -/
theorem isSemibasic_def {η : SmoothForm I M F k} :
    IsSemibasic IB f η ↔ ∀ x, IsSemibasicAt IB f η x :=
  Iff.rfl

/-- A form is semibasic for `f` exactly when, at every point `x`, it vanishes on every tuple one
of whose vectors is sent to zero by the differential of `f` at `x`. -/
theorem isSemibasic_iff {η : SmoothForm I M F k} :
    IsSemibasic IB f η ↔ ∀ (x : M) (v : Fin k → TangentSpace I x) (i : Fin k),
      mfderiv I IB f x (v i) = 0 → η.val x v = 0 :=
  forall_congr' fun _ ↦ isSemibasicAt_iff

variable (IB f) in
/-- Every `0`-form is semibasic for every map. -/
theorem isSemibasic_of_degree_zero (η : SmoothForm I M F 0) : IsSemibasic IB f η :=
  isSemibasicAt_of_degree_zero IB f η

variable (IB f) in
/-- The zero form is semibasic for every map. -/
@[simp]
theorem isSemibasic_zero : IsSemibasic IB f (0 : SmoothForm I M F k) :=
  isSemibasicAt_zero IB f

/-- The sum of two forms semibasic for `f` is semibasic for `f`. -/
theorem IsSemibasic.add {η η' : SmoothForm I M F k} (hη : IsSemibasic IB f η)
    (hη' : IsSemibasic IB f η') : IsSemibasic IB f (η + η') :=
  fun x ↦ (hη x).add (hη' x)

/-- The negative of a form semibasic for `f` is semibasic for `f`. -/
theorem IsSemibasic.neg {η : SmoothForm I M F k} (hη : IsSemibasic IB f η) :
    IsSemibasic IB f (-η) :=
  fun x ↦ (hη x).neg

/-- The difference of two forms semibasic for `f` is semibasic for `f`. -/
theorem IsSemibasic.sub {η η' : SmoothForm I M F k} (hη : IsSemibasic IB f η)
    (hη' : IsSemibasic IB f η') : IsSemibasic IB f (η - η') :=
  fun x ↦ (hη x).sub (hη' x)

/-- A real multiple of a form semibasic for `f` is semibasic for `f`. -/
theorem IsSemibasic.smul {η : SmoothForm I M F k} (hη : IsSemibasic IB f η) (c : ℝ) :
    IsSemibasic IB f (c • η) :=
  fun x ↦ (hη x).smul c

end IsSemibasic

section Pullback

variable {E' H' M' EB' HB' B' : Type*}
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  [TopologicalSpace M'] [ChartedSpace H' M'] {I' : ModelWithCorners ℝ E' H'} [IsManifold I' 1 M']
  [NormedAddCommGroup EB'] [NormedSpace ℝ EB'] [TopologicalSpace HB']
  [TopologicalSpace B'] [ChartedSpace HB' B'] {IB' : ModelWithCorners ℝ EB' HB'}
  {g : M' → M} {f' : M' → B'}

/-- **Pullback of semibasic forms.** Let `g : M' → M` be smooth and let `f' : M' → B'` be a map
whose differential at `x'` has a kernel that the differential of `g` sends into the kernel of
the differential of `f` at `g x'`. Then the pullback along `g` of a form semibasic for `f` at
`g x'` is semibasic for `f'` at `x'`. -/
theorem IsSemibasicAt.mpullback_of_mfderiv {η : SmoothForm I M F k} {x' : M'}
    (hη : IsSemibasicAt IB f η (g x')) (hg : ContMDiff I' I ∞ g)
    (hker : ∀ v : TangentSpace I' x', mfderiv I' IB' f' x' v = 0 →
      mfderiv I IB f (g x') (mfderiv I' I g x' v) = 0) :
    IsSemibasicAt IB' f' (mpullback g hg η) x' := by
  have h := Submodule.compLinearMap_mem_conormalForms
    (φ := (mfderiv I' I g x' : TangentSpace I' x' →ₗ[ℝ] TangentSpace I (g x')))
    (W := (mfderiv I IB f (g x')).ker) (W' := (mfderiv I' IB' f' x').ker)
    (fun v hv ↦ hker v hv) (isSemibasicAt_def.mp hη)
  refine isSemibasicAt_def.mpr (Eq.subst (motive := (· ∈ _)) ?_ h)
  ext v
  simp only [AlternatingMap.compLinearMap_apply, ContinuousAlternatingMap.coe_toAlternatingMap,
    ContinuousLinearMap.coe_coe, mpullback_apply]

/-- **Pullback of semibasic forms along a commuting square.** Let `g : M' → M` be smooth, and
let `f' : M' → B'` and `h : B' → B` be maps with `f ∘ g = h ∘ f'`, with `f` differentiable at
`g x'`, `h` at `f' x'` and `f'` at `x'`. Then the pullback along `g` of a form
semibasic for `f` at `g x'` is semibasic for `f'` at `x'`. -/
theorem IsSemibasicAt.mpullback_of_comp_eq {η : SmoothForm I M F k} {x' : M'} {h : B' → B}
    (hη : IsSemibasicAt IB f η (g x')) (hg : ContMDiff I' I ∞ g)
    (hfg : f ∘ g = h ∘ f') (hf : MDifferentiableAt I IB f (g x'))
    (hh : MDifferentiableAt IB' IB h (f' x')) (hf' : MDifferentiableAt I' IB' f' x') :
    IsSemibasicAt IB' f' (mpullback g hg η) x' := by
  refine hη.mpullback_of_mfderiv hg fun v hv ↦ ?_
  have hd : mfderiv I' IB (f ∘ g) x' = mfderiv I' IB (h ∘ f') x' := by rw [hfg]
  rw [← mfderiv_comp_apply x' hf (hg.mdifferentiableAt (by simp))]
  have h0 := mfderiv_comp_apply x' hh hf' v
  rw [hv, map_zero] at h0
  exact (congrArg (· v) hd).trans h0

/-- **Pullback of semibasic forms along a composite.** For a smooth `g : M' → M` and a map `f`
differentiable at `g x'`, the pullback along `g` of a form semibasic for `f` at `g x'` is
semibasic for `f ∘ g` at `x'`. -/
theorem IsSemibasicAt.mpullback_comp {η : SmoothForm I M F k} {x' : M'}
    (hη : IsSemibasicAt IB f η (g x')) (hg : ContMDiff I' I ∞ g)
    (hf : MDifferentiableAt I IB f (g x')) :
    IsSemibasicAt IB (f ∘ g) (mpullback g hg η) x' :=
  hη.mpullback_of_mfderiv hg fun v hv ↦ by
    rwa [mfderiv_comp_apply x' hf (hg.mdifferentiableAt (by simp))] at hv

/-- **Pullback of semibasic forms along a commuting square.** For a smooth `g : M' → M` and
differentiable maps `f`, `f' : M' → B'` and `h : B' → B` with `f ∘ g = h ∘ f'`, the pullback
along `g` of a form semibasic for `f` is semibasic for `f'`. -/
theorem IsSemibasic.mpullback_of_comp_eq {η : SmoothForm I M F k} {h : B' → B}
    (hη : IsSemibasic IB f η) (hg : ContMDiff I' I ∞ g) (hfg : f ∘ g = h ∘ f')
    (hf : MDifferentiable I IB f) (hh : MDifferentiable IB' IB h)
    (hf' : MDifferentiable I' IB' f') :
    IsSemibasic IB' f' (mpullback g hg η) :=
  fun x' ↦ (hη (g x')).mpullback_of_comp_eq hg hfg (hf _) (hh _) (hf' _)

/-- **Pullback of semibasic forms along a composite.** For a smooth `g : M' → M` and a
differentiable map `f`, the pullback along `g` of a form semibasic for `f` is semibasic for
`f ∘ g`. -/
theorem IsSemibasic.mpullback_comp {η : SmoothForm I M F k} (hη : IsSemibasic IB f η)
    (hg : ContMDiff I' I ∞ g) (hf : MDifferentiable I IB f) :
    IsSemibasic IB (f ∘ g) (mpullback g hg η) :=
  fun x' ↦ (hη (g x')).mpullback_comp hg (hf _)

end Pullback

section Prod

variable {EN HN N : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
  [TopologicalSpace N] [ChartedSpace HN N] {J : ModelWithCorners ℝ EN HN} [IsManifold J 1 N]

/-- A form on `M × N` is semibasic for `Prod.fst` at `p` exactly when its value at `p` vanishes
on every tuple one of whose vectors has zero component along `M`. -/
theorem isSemibasicAt_fst_iff {η : SmoothForm (I.prod J) (M × N) F k} {p : M × N} :
    IsSemibasicAt I Prod.fst η p ↔ ∀ (v : Fin k → TangentSpace (I.prod J) p) (i : Fin k),
      (Manifold.tangentSpaceProdEquiv p (v i)).1 = 0 → η.val p v = 0 := by
  simp only [isSemibasicAt_iff, mfderiv_fst_apply, Manifold.tangentSpaceProdEquiv_apply]

/-- A form on `M × N` is semibasic for `Prod.fst` exactly when it vanishes on every tuple one of
whose vectors has zero component along `M`. -/
theorem isSemibasic_fst_iff {η : SmoothForm (I.prod J) (M × N) F k} :
    IsSemibasic I Prod.fst η ↔ ∀ (p : M × N) (v : Fin k → TangentSpace (I.prod J) p) (i : Fin k),
      (Manifold.tangentSpaceProdEquiv p (v i)).1 = 0 → η.val p v = 0 :=
  forall_congr' fun _ ↦ isSemibasicAt_fst_iff

/-- **Pullback of semibasic forms along products.** For smooth maps `g : M' → M` and
`h : N' → N`, the pullback along `g × h : M' × N' → M × N` of a form on `M × N` semibasic for
`Prod.fst` is semibasic for `Prod.fst`. -/
theorem IsSemibasic.mpullback_prodMap {E' H' M' EN' HN' N' : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [TopologicalSpace H'] [TopologicalSpace M'] [ChartedSpace H' M']
    {I' : ModelWithCorners ℝ E' H'} [IsManifold I' 1 M'] [NormedAddCommGroup EN']
    [NormedSpace ℝ EN'] [TopologicalSpace HN'] [TopologicalSpace N'] [ChartedSpace HN' N']
    {J' : ModelWithCorners ℝ EN' HN'} [IsManifold J' 1 N']
    {η : SmoothForm (I.prod J) (M × N) F k} (hη : IsSemibasic I Prod.fst η) {g : M' → M}
    (hg : ContMDiff I' I ∞ g) {h : N' → N} (hh : ContMDiff J' J ∞ h) :
    IsSemibasic I' Prod.fst (mpullback (Prod.map g h) (hg.prodMap hh) η) :=
  hη.mpullback_of_comp_eq _ (rfl) mdifferentiable_fst (hg.mdifferentiable (by simp))
    mdifferentiable_fst

end Prod

end TauCeti.SmoothForm

end
