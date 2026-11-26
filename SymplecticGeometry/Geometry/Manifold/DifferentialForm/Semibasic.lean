/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.ExtDeriv
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Smooth
public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic
public import SymplecticGeometry.Topology.Algebra.Module.Alternating.Wedge.Basic
public import SymplecticGeometry.LinearAlgebra.Alternating.Conormal
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Smooth
import TauCeti.Geometry.Manifold.MFDeriv.Prod

/-!
# Forms semibasic for a map

A form `α` on `M` (a rough form: nothing is asked of its regularity) is *semibasic* for a map
`f : M → B` at a point `x` (`TauCeti.RoughForm.IsSemibasicAt IB f α x`) when its value at `x`
vanishes as soon as one of its arguments lies in the kernel of the differential of `f` at `x`,
that is, when it lies in Tau Ceti's `Submodule.conormalForms` of that kernel. It is semibasic for
`f` (`TauCeti.RoughForm.IsSemibasic IB f α`) when this holds at every point. The condition is
pointwise: unlike Tau Ceti's `TauCeti.RoughForm.IsBasic`, it does not compare the values of `α`
at two points of a fibre of `f`. A smooth form `η` is semibasic when `η.val` is; its smooth
pullbacks are reached through `TauCeti.SmoothForm.coe_mpullback`.

## Main definitions

* `TauCeti.RoughForm.IsSemibasicAt IB f α x`: the form `α` is semibasic for `f` at `x`.
* `TauCeti.RoughForm.IsSemibasic IB f α`: the form `α` is semibasic for `f` at every point.

## Main results

* `TauCeti.RoughForm.IsSemibasicAt.apply_eq_of_mfderiv_eq`: at `x`, a form semibasic for `f`
  takes the same value on two tuples whose images under the differential of `f` agree.
* Closure of both predicates under `0`, `+`, `-` and real multiples, and every `0`-form is
  semibasic. `TauCeti.SmoothForm.isSemibasic_add`, `TauCeti.SmoothForm.isSemibasic_smul`, … and
  `TauCeti.SmoothForm.isSemibasic_iff` state closure and the vanishing on vertical arguments for
  the underlying rough forms of smooth forms, with the instances of `TauCeti.SmoothForm`.
* `TauCeti.RoughForm.IsSemibasicAt.mpullback_of_mfderiv`: the pullback along a map `g` of a form
  semibasic for `f` is semibasic for `f'` when the differential of `g` sends the kernel of that
  of `f'` into the kernel of that of `f`. The linear step is
  `Submodule.compLinearMap_mem_conormalForms`.
* `TauCeti.RoughForm.IsSemibasicAt.mpullback_of_comp_eq`: for differentiable maps with
  `f ∘ g = h ∘ f'`, the pullback along `g` of a form semibasic for `f` is semibasic for `f'`; in
  particular (`TauCeti.RoughForm.IsSemibasicAt.mpullback_comp`) it is semibasic for `f ∘ g`.
* `TauCeti.RoughForm.IsSemibasicAt.wedge_apply_eq_zero`: at `x`, the wedge `φ ∧ ψ` of a one-form
  `φ` semibasic for `f` with a two-form `ψ` that vanishes on pairs of vectors of the kernel of the
  differential of `f` vanishes on every triple whose first two vectors lie in that kernel. It is
  the case `K = ker (mfderiv f x)` of `ContinuousAlternatingMap.pairedWedge_apply_eq_zero_of_mem`.
* `TauCeti.RoughForm.isSemibasicAt_mextDeriv_ofFunction_comp`: the differential of `g ∘ f`, a
  function on `B` pulled back along `f`, is semibasic for `f`; and
  `TauCeti.RoughForm.isSemibasic_mextDeriv_ofFunction_comp`, the same at every point.
* `TauCeti.RoughForm.isSemibasicAt_fst_iff`: a form on `M × N` is semibasic for `Prod.fst` at
  `p` exactly when it vanishes at `p` on every tuple one of whose vectors has zero component
  along `M`; and `TauCeti.RoughForm.IsSemibasic.mpullback_prodMap`: pullback along a product of
  differentiable maps keeps forms semibasic for `Prod.fst`.
* `TauCeti.SmoothForm.isSemibasicAt_iff_ker_mfderiv_le`: a smooth two-form `σ` is semibasic for
  `f` at `x` exactly when the kernel of the differential of `f` at `x` lies in the kernel of the
  bilinear form `σ.bilinFormAt x`. So the hypothesis `hker` of Tau Ceti's
  `TauCeti.SmoothTwoForm.isBasic_of_mpullback_eq_of_ker_mfderiv_le` says that `σ` is semibasic.
  It is the pointwise case of `Submodule.mem_conormalForms_fin_two_iff_le_ker`.

## Implementation notes

The value of a smooth form `η` is a section of a trivial bundle, so reading `η.val` as a rough
form makes Lean solve for the instances of the space of values. When that space is normed through
other instances, as the Lie algebra `GroupLieAlgebra I G` is through those of the tangent space
at the identity, the solution can be the unfolded structures, on which instance search then finds
neither `ContinuousAdd` nor `ContinuousConstSMul`. The `TauCeti.SmoothForm` lemmas above are
stated for any normed space of values, where nothing unfolds, and so apply to such forms.
-/

public section

noncomputable section

open Manifold
open scoped Manifold

namespace TauCeti.RoughForm

variable {E H M EB HB B F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H}
  [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  [TopologicalSpace B] [ChartedSpace HB B] {IB : ModelWithCorners ℝ EB HB}
  [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] {k : ℕ} {f : M → B}

section IsSemibasicAt

variable (IB f) in
/-- **Forms semibasic for a map at a point.** A form `α` on `M` is semibasic for `f : M → B` at
`x` when its value at `x` vanishes as soon as one of its arguments lies in the kernel of the
differential of `f` at `x`, that is, is tangent to the fibre of `f` through `x` when `f` is a
submersion. -/
def IsSemibasicAt (α : RoughForm I M F k) (x : M) : Prop :=
  (α x).toAlternatingMap ∈ (mfderiv I IB f x).ker.conormalForms (Fin k) F

/-- The defining property of `TauCeti.RoughForm.IsSemibasicAt`. -/
theorem isSemibasicAt_def {α : RoughForm I M F k} {x : M} :
    IsSemibasicAt IB f α x ↔
      (α x).toAlternatingMap ∈ (mfderiv I IB f x).ker.conormalForms (Fin k) F :=
  Iff.rfl

/-- A form is semibasic for `f` at `x` exactly when its value at `x` vanishes on every tuple one
of whose vectors is sent to zero by the differential of `f` at `x`. -/
theorem isSemibasicAt_iff {α : RoughForm I M F k} {x : M} :
    IsSemibasicAt IB f α x ↔ ∀ (v : Fin k → TangentSpace I x) (i : Fin k),
      mfderiv I IB f x (v i) = 0 → α x v = 0 := by
  simp only [isSemibasicAt_def, Submodule.mem_conormalForms, LinearMap.mem_ker,
    ContinuousLinearMap.coe_coe, ContinuousAlternatingMap.coe_toAlternatingMap]

/-- A form semibasic for `f` at `x` vanishes at `x` on tuples one of which is sent to zero by
the differential of `f`. -/
theorem IsSemibasicAt.apply_eq_zero {α : RoughForm I M F k} {x : M}
    (hα : IsSemibasicAt IB f α x) (v : Fin k → TangentSpace I x) (i : Fin k)
    (hv : mfderiv I IB f x (v i) = 0) : α x v = 0 :=
  isSemibasicAt_iff.mp hα v i hv

/-- **Semibasic forms only see the differential.** At `x`, a form semibasic for `f` takes the
same value on two tuples of tangent vectors whose images under the differential of `f` at `x`
agree. -/
theorem IsSemibasicAt.apply_eq_of_mfderiv_eq {α : RoughForm I M F k} {x : M}
    (hα : IsSemibasicAt IB f α x) {v w : Fin k → TangentSpace I x}
    (h : ∀ i, mfderiv I IB f x (v i) = mfderiv I IB f x (w i)) : α x v = α x w :=
  Submodule.conormalForms_apply_eq_of_sub_mem (α := (α x).toAlternatingMap) hα
    fun i ↦ by simp [h i]

variable (IB f) in
/-- Every `0`-form is semibasic for every map at every point. -/
theorem isSemibasicAt_of_degree_zero (α : RoughForm I M F 0) (x : M) :
    IsSemibasicAt IB f α x :=
  isSemibasicAt_iff.mpr fun _ i ↦ i.elim0

variable (IB f) in
/-- The zero form is semibasic for every map at every point. -/
@[simp]
theorem isSemibasicAt_zero (x : M) : IsSemibasicAt IB f (0 : RoughForm I M F k) x :=
  Submodule.zero_mem _

/-- The sum of two forms semibasic for `f` at `x` is semibasic for `f` at `x`. -/
theorem IsSemibasicAt.add [ContinuousAdd F]
    {α β : RoughForm I M F k} {x : M} (hα : IsSemibasicAt IB f α x)
    (hβ : IsSemibasicAt IB f β x) : IsSemibasicAt IB f (α + β) x :=
  add_mem hα hβ

/-- The negative of a form semibasic for `f` at `x` is semibasic for `f` at `x`. -/
theorem IsSemibasicAt.neg [IsTopologicalAddGroup F]
    {α : RoughForm I M F k} {x : M} (hα : IsSemibasicAt IB f α x) :
    IsSemibasicAt IB f (-α) x :=
  neg_mem hα

/-- The difference of two forms semibasic for `f` at `x` is semibasic for `f` at `x`. -/
theorem IsSemibasicAt.sub [IsTopologicalAddGroup F]
    {α β : RoughForm I M F k} {x : M} (hα : IsSemibasicAt IB f α x)
    (hβ : IsSemibasicAt IB f β x) : IsSemibasicAt IB f (α - β) x :=
  sub_mem hα hβ

/-- A real multiple of a form semibasic for `f` at `x` is semibasic for `f` at `x`. -/
theorem IsSemibasicAt.smul [ContinuousConstSMul ℝ F]
    {α : RoughForm I M F k} {x : M} (hα : IsSemibasicAt IB f α x)
    (c : ℝ) : IsSemibasicAt IB f (c • α) x :=
  Submodule.smul_mem _ c hα

end IsSemibasicAt

section IsSemibasic

variable (IB f) in
/-- **Forms semibasic for a map.** A form `α` on `M` is semibasic for `f : M → B` when it is so
at every point: its value at `x` vanishes as soon as one of its arguments lies in the kernel of
the differential of `f` at `x`. -/
def IsSemibasic (α : RoughForm I M F k) : Prop :=
  ∀ x, IsSemibasicAt IB f α x

/-- The defining property of `TauCeti.RoughForm.IsSemibasic`. -/
theorem isSemibasic_def {α : RoughForm I M F k} :
    IsSemibasic IB f α ↔ ∀ x, IsSemibasicAt IB f α x :=
  Iff.rfl

/-- A form is semibasic for `f` exactly when, at every point `x`, it vanishes on every tuple one
of whose vectors is sent to zero by the differential of `f` at `x`. -/
theorem isSemibasic_iff {α : RoughForm I M F k} :
    IsSemibasic IB f α ↔ ∀ (x : M) (v : Fin k → TangentSpace I x) (i : Fin k),
      mfderiv I IB f x (v i) = 0 → α x v = 0 :=
  forall_congr' fun _ ↦ isSemibasicAt_iff

/-- A form semibasic for `f` vanishes at every point `x` on the tuples one of which is sent to
zero by the differential of `f` at `x`. -/
theorem IsSemibasic.apply_eq_zero {α : RoughForm I M F k} (hα : IsSemibasic IB f α) (x : M)
    (v : Fin k → TangentSpace I x) (i : Fin k) (hv : mfderiv I IB f x (v i) = 0) : α x v = 0 :=
  (hα x).apply_eq_zero v i hv

variable (IB f) in
/-- Every `0`-form is semibasic for every map. -/
theorem isSemibasic_of_degree_zero (α : RoughForm I M F 0) : IsSemibasic IB f α :=
  isSemibasicAt_of_degree_zero IB f α

variable (IB f) in
/-- The zero form is semibasic for every map. -/
@[simp]
theorem isSemibasic_zero : IsSemibasic IB f (0 : RoughForm I M F k) :=
  isSemibasicAt_zero IB f

/-- The sum of two forms semibasic for `f` is semibasic for `f`. -/
theorem IsSemibasic.add [ContinuousAdd F] {α β : RoughForm I M F k} (hα : IsSemibasic IB f α)
    (hβ : IsSemibasic IB f β) : IsSemibasic IB f (α + β) :=
  fun x ↦ (hα x).add (hβ x)

/-- The negative of a form semibasic for `f` is semibasic for `f`. -/
theorem IsSemibasic.neg [IsTopologicalAddGroup F]
    {α : RoughForm I M F k} (hα : IsSemibasic IB f α) :
    IsSemibasic IB f (-α) :=
  fun x ↦ (hα x).neg

/-- The difference of two forms semibasic for `f` is semibasic for `f`. -/
theorem IsSemibasic.sub [IsTopologicalAddGroup F]
    {α β : RoughForm I M F k} (hα : IsSemibasic IB f α)
    (hβ : IsSemibasic IB f β) : IsSemibasic IB f (α - β) :=
  fun x ↦ (hα x).sub (hβ x)

/-- A real multiple of a form semibasic for `f` is semibasic for `f`. -/
theorem IsSemibasic.smul [ContinuousConstSMul ℝ F]
    {α : RoughForm I M F k} (hα : IsSemibasic IB f α) (c : ℝ) :
    IsSemibasic IB f (c • α) :=
  fun x ↦ (hα x).smul c

end IsSemibasic

section Pullback

variable {E' H' M' EB' HB' B' : Type*}
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  [TopologicalSpace M'] [ChartedSpace H' M'] {I' : ModelWithCorners ℝ E' H'}
  [NormedAddCommGroup EB'] [NormedSpace ℝ EB'] [TopologicalSpace HB']
  [TopologicalSpace B'] [ChartedSpace HB' B'] {IB' : ModelWithCorners ℝ EB' HB'}
  {g : M' → M} {f' : M' → B'}

/-- **Pullback of semibasic forms.** Let `g : M' → M` and `f' : M' → B'` be maps such that the
differential of `g` at `x'` sends the kernel of the differential of `f'` at `x'` into the kernel
of the differential of `f` at `g x'`. Then the pullback along `g` of a form semibasic for `f` at
`g x'` is semibasic for `f'` at `x'`. -/
theorem IsSemibasicAt.mpullback_of_mfderiv {α : RoughForm I M F k} {x' : M'}
    (hα : IsSemibasicAt IB f α (g x'))
    (hker : ∀ v : TangentSpace I' x', mfderiv I' IB' f' x' v = 0 →
      mfderiv I IB f (g x') (mfderiv I' I g x' v) = 0) :
    IsSemibasicAt IB' f' (mpullback I' I g α) x' := by
  have h := Submodule.compLinearMap_mem_conormalForms
    (φ := (mfderiv I' I g x' : TangentSpace I' x' →ₗ[ℝ] TangentSpace I (g x')))
    (W := (mfderiv I IB f (g x')).ker) (W' := (mfderiv I' IB' f' x').ker)
    (fun v hv ↦ hker v hv) (isSemibasicAt_def.mp hα)
  refine isSemibasicAt_def.mpr (Eq.subst (motive := (· ∈ _)) ?_ h)
  ext v
  simp only [AlternatingMap.compLinearMap_apply, ContinuousAlternatingMap.coe_toAlternatingMap,
    ContinuousLinearMap.coe_coe, mpullback_apply]

/-- **Pullback of semibasic forms along a commuting square.** Let `g : M' → M`, `f' : M' → B'`
and `h : B' → B` be maps with `f ∘ g = h ∘ f'`, with `g` and `f'` differentiable at `x'`, `f` at
`g x'` and `h` at `f' x'`. Then the pullback along `g` of a form semibasic for `f` at `g x'` is
semibasic for `f'` at `x'`. -/
theorem IsSemibasicAt.mpullback_of_comp_eq {α : RoughForm I M F k} {x' : M'} {h : B' → B}
    (hα : IsSemibasicAt IB f α (g x')) (hfg : f ∘ g = h ∘ f')
    (hg : MDifferentiableAt I' I g x') (hf : MDifferentiableAt I IB f (g x'))
    (hh : MDifferentiableAt IB' IB h (f' x')) (hf' : MDifferentiableAt I' IB' f' x') :
    IsSemibasicAt IB' f' (mpullback I' I g α) x' := by
  refine hα.mpullback_of_mfderiv fun v hv ↦ ?_
  have hd : mfderiv I' IB (f ∘ g) x' = mfderiv I' IB (h ∘ f') x' := by rw [hfg]
  rw [← mfderiv_comp_apply x' hf hg]
  have h0 := mfderiv_comp_apply x' hh hf' v
  rw [hv, map_zero] at h0
  exact (congrArg (· v) hd).trans h0

/-- **Pullback of semibasic forms along a composite.** For a map `g : M' → M` differentiable at
`x'` and a map `f` differentiable at `g x'`, the pullback along `g` of a form semibasic for `f`
at `g x'` is semibasic for `f ∘ g` at `x'`. -/
theorem IsSemibasicAt.mpullback_comp {α : RoughForm I M F k} {x' : M'}
    (hα : IsSemibasicAt IB f α (g x')) (hg : MDifferentiableAt I' I g x')
    (hf : MDifferentiableAt I IB f (g x')) :
    IsSemibasicAt IB (f ∘ g) (mpullback I' I g α) x' :=
  hα.mpullback_of_mfderiv fun v hv ↦ by rwa [mfderiv_comp_apply x' hf hg] at hv

/-- **Pullback of semibasic forms along a commuting square.** For differentiable maps
`g : M' → M`, `f' : M' → B'`, `f : M → B` and `h : B' → B` with `f ∘ g = h ∘ f'`, the pullback
along `g` of a form semibasic for `f` is semibasic for `f'`. -/
theorem IsSemibasic.mpullback_of_comp_eq {α : RoughForm I M F k} {h : B' → B}
    (hα : IsSemibasic IB f α) (hfg : f ∘ g = h ∘ f') (hg : MDifferentiable I' I g)
    (hf : MDifferentiable I IB f) (hh : MDifferentiable IB' IB h)
    (hf' : MDifferentiable I' IB' f') :
    IsSemibasic IB' f' (mpullback I' I g α) :=
  fun x' ↦ (hα (g x')).mpullback_of_comp_eq hfg (hg _) (hf _) (hh _) (hf' _)

/-- **Pullback of semibasic forms along a composite.** For differentiable maps `g : M' → M` and
`f : M → B`, the pullback along `g` of a form semibasic for `f` is semibasic for `f ∘ g`. -/
theorem IsSemibasic.mpullback_comp {α : RoughForm I M F k} (hα : IsSemibasic IB f α)
    (hg : MDifferentiable I' I g) (hf : MDifferentiable I IB f) :
    IsSemibasic IB (f ∘ g) (mpullback I' I g α) :=
  fun x' ↦ (hα (g x')).mpullback_comp (hg _) (hf _)

end Pullback

section Wedge

/-- **Wedge with a semibasic one-form.** Let `φ` be a one-form semibasic for `f` at `x`, and `ψ`
a two-form whose value at `x` vanishes on every pair of vectors of the kernel `K` of the
differential of `f` at `x`. Then `(φ ∧ ψ)_x (η₁, η₂, v) = 0` for `η₁ η₂ ∈ K` and every `v`. -/
theorem IsSemibasicAt.wedge_apply_eq_zero {φ : RoughForm I M ℝ 1} {ψ : RoughForm I M ℝ 2}
    {x : M} (hφ : IsSemibasicAt IB f φ x)
    (hψ : ∀ u w : TangentSpace I x, mfderiv I IB f x u = 0 → mfderiv I IB f x w = 0 →
      ψ x ![u, w] = 0)
    {η₁ η₂ : TangentSpace I x} (h₁ : mfderiv I IB f x η₁ = 0) (h₂ : mfderiv I IB f x η₂ = 0)
    (v : TangentSpace I x) : φ.wedge ψ x ![η₁, η₂, v] = 0 := by
  rw [wedge_def, wedgeWith_apply']
  exact ContinuousAlternatingMap.pairedWedge_apply_eq_zero_of_mem _ _
    (K := (mfderiv I IB f x).ker) (fun u hu ↦ hφ.apply_eq_zero _ 0 hu)
    (fun u hu w hw ↦ hψ u w hu hw) h₁ h₂ v

end Wedge

section ExtDeriv

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Differentials of functions on the base are semibasic.** For `f : M → B` differentiable at
`x` and `g : B → F` differentiable at `f x`, the differential `d (g ∘ f)` is semibasic for `f` at
`x`. -/
theorem isSemibasicAt_mextDeriv_ofFunction_comp {g : B → F} {x : M}
    (hg : MDifferentiableAt IB 𝓘(ℝ, F) g (f x)) (hf : MDifferentiableAt I IB f x) :
    IsSemibasicAt IB f (mextDeriv (RoughForm.ofFunction I (g ∘ f))) x := by
  refine isSemibasicAt_iff.mpr fun v i hv ↦ ?_
  obtain rfl : i = 0 := Subsingleton.elim (α := Fin 1) _ _
  have hv' : v = ![v 0] := by
    ext j
    fin_cases j
    rfl
  rw [hv', mextDeriv_ofFunction_apply, mfderiv_comp_apply x hg hf, hv]
  exact map_zero _

/-- **Differentials of functions on the base are semibasic.** For differentiable `f : M → B` and
`g : B → F`, the differential `d (g ∘ f)` is semibasic for `f`. -/
theorem isSemibasic_mextDeriv_ofFunction_comp {g : B → F}
    (hg : MDifferentiable IB 𝓘(ℝ, F) g) (hf : MDifferentiable I IB f) :
    IsSemibasic IB f (mextDeriv (RoughForm.ofFunction I (g ∘ f))) :=
  fun _ ↦ isSemibasicAt_mextDeriv_ofFunction_comp (hg _) (hf _)

end ExtDeriv

section Prod

variable {EN HN N : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
  [TopologicalSpace N] [ChartedSpace HN N] {J : ModelWithCorners ℝ EN HN}

/-- A form on `M × N` is semibasic for `Prod.fst` at `p` exactly when its value at `p` vanishes
on every tuple one of whose vectors has zero component along `M`. -/
theorem isSemibasicAt_fst_iff {α : RoughForm (I.prod J) (M × N) F k} {p : M × N} :
    IsSemibasicAt I Prod.fst α p ↔ ∀ (v : Fin k → TangentSpace (I.prod J) p) (i : Fin k),
      (Manifold.tangentSpaceProdEquiv p (v i)).1 = 0 → α p v = 0 := by
  simp only [isSemibasicAt_iff, mfderiv_fst_apply, Manifold.tangentSpaceProdEquiv_apply]

/-- A form on `M × N` is semibasic for `Prod.fst` exactly when it vanishes on every tuple one of
whose vectors has zero component along `M`. -/
theorem isSemibasic_fst_iff {α : RoughForm (I.prod J) (M × N) F k} :
    IsSemibasic I Prod.fst α ↔ ∀ (p : M × N) (v : Fin k → TangentSpace (I.prod J) p) (i : Fin k),
      (Manifold.tangentSpaceProdEquiv p (v i)).1 = 0 → α p v = 0 :=
  forall_congr' fun _ ↦ isSemibasicAt_fst_iff

/-- **Pullback of semibasic forms along products.** For differentiable maps `g : M' → M` and
`h : N' → N`, the pullback along `g × h : M' × N' → M × N` of a form on `M × N` semibasic for
`Prod.fst` is semibasic for `Prod.fst`. -/
theorem IsSemibasic.mpullback_prodMap {E' H' M' EN' HN' N' : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [TopologicalSpace H'] [TopologicalSpace M'] [ChartedSpace H' M']
    {I' : ModelWithCorners ℝ E' H'} [NormedAddCommGroup EN']
    [NormedSpace ℝ EN'] [TopologicalSpace HN'] [TopologicalSpace N'] [ChartedSpace HN' N']
    {J' : ModelWithCorners ℝ EN' HN'}
    {α : RoughForm (I.prod J) (M × N) F k} (hα : IsSemibasic I Prod.fst α) {g : M' → M}
    (hg : MDifferentiable I' I g) {h : N' → N} (hh : MDifferentiable J' J h) :
    IsSemibasic I' Prod.fst (mpullback (I'.prod J') (I.prod J) (Prod.map g h) α) :=
  hα.mpullback_of_comp_eq (rfl) (hg.prodMap hh) mdifferentiable_fst hg mdifferentiable_fst

end Prod

end TauCeti.RoughForm

namespace TauCeti.SmoothForm

variable {E H M EB HB B : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H} [IsManifold I 1 M]
  [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  [TopologicalSpace B] [ChartedSpace HB B] {IB : ModelWithCorners ℝ EB HB} {f : M → B}

section Linear

/-! The closure properties of `TauCeti.RoughForm.IsSemibasic`, for the underlying rough forms of
smooth forms: see the implementation notes. -/

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

/-- A smooth form is semibasic for `f` exactly when, at every point `x`, it vanishes on every
tuple one of whose vectors is sent to zero by the differential of `f` at `x`. This is
`TauCeti.RoughForm.isSemibasic_iff`, with the value of the form read with the instances of
`TauCeti.SmoothForm`. -/
theorem isSemibasic_iff {α : SmoothForm I M F k} :
    RoughForm.IsSemibasic (F := F) IB f α.val ↔ ∀ (x : M) (v : Fin k → TangentSpace I x)
      (i : Fin k), mfderiv I IB f x (v i) = 0 → α.val x v = 0 :=
  RoughForm.isSemibasic_iff

/-- The sum of two smooth forms semibasic for `f` is semibasic for `f`. -/
theorem isSemibasic_add {α β : SmoothForm I M F k} (hα : RoughForm.IsSemibasic (F := F) IB f α.val)
    (hβ : RoughForm.IsSemibasic (F := F) IB f β.val) :
    RoughForm.IsSemibasic (F := F) IB f (α + β).val := by
  rw [Submodule.coe_add]
  exact hα.add hβ

/-- A real multiple of a smooth form semibasic for `f` is semibasic for `f`. -/
theorem isSemibasic_smul {α : SmoothForm I M F k} (hα : RoughForm.IsSemibasic (F := F) IB f α.val)
    (c : ℝ) : RoughForm.IsSemibasic (F := F) IB f (c • α).val := by
  rw [Submodule.coe_smul]
  exact hα.smul c

/-- The negative of a smooth form semibasic for `f` is semibasic for `f`. -/
theorem isSemibasic_neg {α : SmoothForm I M F k} (hα : RoughForm.IsSemibasic (F := F) IB f α.val) :
    RoughForm.IsSemibasic (F := F) IB f (-α).val := by
  rw [Submodule.coe_neg]
  exact hα.neg

/-- The difference of two smooth forms semibasic for `f` is semibasic for `f`. -/
theorem isSemibasic_sub {α β : SmoothForm I M F k} (hα : RoughForm.IsSemibasic (F := F) IB f α.val)
    (hβ : RoughForm.IsSemibasic (F := F) IB f β.val) :
    RoughForm.IsSemibasic (F := F) IB f (α - β).val := by
  rw [Submodule.coe_sub]
  exact hα.sub hβ

end Linear

/-- **Semibasic two-forms.** A smooth two-form `σ` is semibasic for `f` at `x` exactly when every
vector in the kernel of the differential of `f` at `x` lies in the kernel of the bilinear form
`σ_x`. -/
theorem isSemibasicAt_iff_ker_mfderiv_le {σ : SmoothForm I M ℝ 2} {x : M} :
    RoughForm.IsSemibasicAt IB f σ.val x ↔
      (mfderiv I IB f x).ker ≤ LinearMap.ker (σ.bilinFormAt x) := by
  rw [RoughForm.isSemibasicAt_def, bilinFormAt_def, Submodule.mem_conormalForms_fin_two_iff_le_ker]

/-- A smooth two-form `σ` is semibasic for `f` exactly when, at every point `x`, every vector in
the kernel of the differential of `f` at `x` lies in the kernel of the bilinear form `σ_x`. -/
theorem isSemibasic_iff_ker_mfderiv_le {σ : SmoothForm I M ℝ 2} :
    RoughForm.IsSemibasic IB f σ.val ↔
      ∀ x, (mfderiv I IB f x).ker ≤ LinearMap.ker (σ.bilinFormAt x) :=
  forall_congr' fun _ ↦ isSemibasicAt_iff_ker_mfderiv_le

end TauCeti.SmoothForm

end
