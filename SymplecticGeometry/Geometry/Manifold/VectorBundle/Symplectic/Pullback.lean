/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Pullback
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Symplectic.ComplexStructure.Basic
public import TauCeti.Geometry.Manifold.ContMDiffMap.Basic

/-!
# Pull-backs of two-forms on vector bundles

Let `V → M` be a real vector bundle and `f : N → M` a `C^n` map, of any type `K` with
`[ContinuousMapClass K N M]`, with `hf : ContMDiff I' I n f`. A two-form `ω` on `V` pulls back to
the two-form `ω.pullback f hf` on the pull-back bundle `f *ᵖ V`, whose value at `y` is `ω (f y)`:
both are alternating maps on the same fibre `V (f y)`. This file defines the pull-back and shows
that it is compatible with the rest of the structure that `Symplectic/Basic.lean` and
`Symplectic/ComplexStructure/Basic.lean` put on two-forms.

## Main definitions and results

* `SymplecticGeometry.Bundle.ContMDiffTwoForm.pullback ω f hf`, with `pullback_apply`,
  `bilinFormAt_pullback`, `bilinFormAt_pullback_apply`, `pullback_apply_apply` and the linear map
  `pullbackLinearMap f hf`.
* `bilinFormAt_apply_pullback`: a two-form on a pull-back bundle `f *ᵖ V` evaluates on vectors
  typed in `V (f y)`, for `simp`.
* `IsNondegenerate.pullback` and `IsNondegenerate.symplecticFormAt_pullback`: the pull-back of a
  symplectic structure is one, with the symplectic form of `ω` at `f y` on the fibre over `y`;
  `IsNondegenerate.symplecticFormAt_pullback_apply` evaluates it on vectors.
* `Tames.pullback`, `Invariant.pullback`, `Compatible.pullback`: pulling back the form and the
  complex structure (`ContMDiffComplexStructure.pullback`) together keeps the pair tame,
  invariant or compatible.
* `pullback_pushforward`: pulling back commutes with transport along an isomorphism of bundles
  `Φ`, the isomorphism of the pull-back bundles being `y ↦ Φ (f y)`. In particular a symplectic
  isomorphism pulls back to one.
* `pushforward_pullback_id`, `pushforward_pullback_comp`: the pull-back along the identity is the
  form itself, and the pull-back along `g ∘ f` is the pull-back along `g` and then along `f`, once
  the bundles are identified by the identity of each fibre; `bilinFormAt_pullback_id_apply` and
  `bilinFormAt_pullback_comp_apply` are the same facts on vectors, for `simp`. These four take
  bundled `C^n` maps, as Tau Ceti's `Bundle.Pullback.idDiffeomorph` and
  `Bundle.Pullback.compDiffeomorph` do.
* `bilinFormAt_pullback_pullback_apply` and
  `IsNondegenerate.symplecticFormAt_pullback_pullback_apply`: `simp` evaluates the form of an
  iterated pull-back `(ω.pullback g hg).pullback f hf`, and its symplectic form, on vectors of
  `V (g (f z))`; `bilinFormAt_pullback_pullback_pullback_apply` does the same for three
  pull-backs.
  `bilinFormAt_pullback_comp_apply_pullback` evaluates the pull-back along a composite
  `g.comp f` on vectors of `V (g (f z))`, `bilinFormAt_pullback_comp_pullback_apply` that
  pull-back pulled back again along `e` on vectors of `V (g (f (e q)))`, and
  `pullback_apply_apply_fiber` evaluates a pull-back on a pair formed in the pull-back fibre.
  `IsNondegenerate.symplecticFormAt_pullback_pullback_pullback_apply`,
  `IsNondegenerate.symplecticFormAt_pullback_comp_apply_pullback` and
  `IsNondegenerate.symplecticFormAt_pullback_comp_pullback_apply` evaluate the symplectic form
  in the last three of these cases, so that `simp` does so also for a sum.
* `IsSymplecticFrameOn.pullback` and `frameTransition_pullback`: a symplectic frame `Φ` over `U`
  pulls back to the symplectic frame `y ↦ Φ (f y)` over `f ⁻¹' U`, with transition maps those of
  `Φ` at `f y`.
* `compMFDeriv f hf ω`, with `compMFDeriv_apply`, `bilinFormAt_compMFDeriv`,
  `compMFDeriv_apply_apply`, and `compMFDeriv_zero`, `compMFDeriv_add`, `compMFDeriv_smul`,
  `compMFDeriv_neg`, `compMFDeriv_sub`: for a `C^∞` map `f : N → M` and a two-form `ω` on
  `f *ᵖ TM`, the two-form `σ(u, v) = ω(df u, df v)` on `TN`. It uses only the smoothness of `f`,
  not that `f` is an immersion.

## Implementation notes

The value of `ω.pullback f hf` is that of Tau Ceti's `ContMDiffSection.pullback ω f`, which is a
section of the pull-back of the bundle of alternating maps; its smoothness as a section of the
bundle of alternating maps of the pull-back is
`Bundle.Pullback.contMDiff_continuousAlternatingMap_section_iff`. The identifications of the
pull-back bundles along the identity and along a composite are Tau Ceti's
`Bundle.Pullback.idDiffeomorph` and `Bundle.Pullback.compDiffeomorph`, and the pull-back of an
isomorphism of bundles is smooth by `Bundle.Pullback.contMDiff_fiberwise`. The API `pullback_zero`,
`pullback_add`, `pullback_smul` and `pullbackLinearMap` adapts Tau Ceti's
`ContMDiffSection.pullback_zero`, `pullback_add`, `pullback_smul` and `pullbackLinearMap`
(`TauCeti/Geometry/Manifold/VectorBundle/Section/Module.lean`).

`bilinFormAt_pullback` and `IsNondegenerate.symplecticFormAt_pullback` are not `@[simp]`: the
form they give lives on `V (f y)`, but the instances around it still name the fibre
`(f *ᵖ V) y`, so the lemmas that evaluate it no longer apply. `simp` evaluates the pulled-back
form on vectors with `bilinFormAt_apply_pullback`, which gives the value of the pull-back on a
pair, and then `pullback_apply_apply`. `bilinFormAt_pullback_apply` states the value of the
pulled-back bilinear form, and is not `@[simp]`, since `simp` proves it.

For the same reason `simp` cannot evaluate `ω.pullback f hf y ![v, w]` once `pullback_apply` has
rewritten `ω.pullback f hf y`: the pair stays a family in `(f *ᵖ V) y`. `pullback_apply_apply`
evaluates the whole application, and is applied before the subterms are simplified (`simp↓`), so
that it fires before `pullback_apply` rewrites `ω.pullback f hf y`, and also on the pull-back of a
sum, a difference, a negative or a multiple, which `pullback_add`, `pullback_sub`, `pullback_neg`
and `pullback_smul` would otherwise split first.

`bilinFormAt_apply` does not fire on vectors typed in `V (f y)` for a form on `f *ᵖ V`: Mathlib's
`Bundle.Pullback` is a plain definition, so at the transparency `simp` uses, such a term is not
type-correct. `bilinFormAt_apply_pullback` states the evaluation with the vectors typed in
`V (f y)`, so that `simp` matches it as written.

For the same reason, a lemma that evaluates a form on vectors of a fibre of `V` matches only
as many pull-backs as its statement names: on vectors of `V (g (f z))`, the form of
`(ω.pullback g hg).pullback f hf` at `z` lives on the fibre `(f *ᵖ (g *ᵖ V)) z`, which unfolds to
`V (g (f z))` only after two steps. So `bilinFormAt_apply_pullback`, which names one, does not
match, and each depth of iterated pull-back needs its own statement, such as
`bilinFormAt_pullback_pullback_apply` and `bilinFormAt_pullback_pullback_pullback_apply`. Since
Mathlib's `Bundle.Pullback` cannot be made reducible outside its own file, no single lemma covers
every depth. These lemmas are applied before the subterms are simplified (`simp↓`), so that they
also match the iterated pull-back of a sum, a difference, a negative or a multiple.

`simp` evaluates the symplectic form of a pull-back through
`IsNondegenerate.toBilinForm_symplecticFormAt` (`Symplectic/Basic.lean`): it turns
`h.symplecticFormAt y v w` into the bilinear form of the two-form at `y` on `v` and `w`, which
the lemmas above then evaluate. For a single form this works in the cases those lemmas cover:
one, two or three pull-backs, a pull-back along a composite `g.comp f`, and that pull-back
pulled back once more. So `IsNondegenerate.symplecticFormAt_pullback_apply`, which states the
value for one pull-back, is not `@[simp]`. In other cases, such as four pull-backs or a pull-back
along `(g.comp f).comp e`, `simp` leaves the bilinear form unevaluated. For a sum, a difference,
a negative or a multiple, this route fails beyond one pull-back: `simp` rewrites the form with
`pullback_add` and its partners and splits its bilinear form with `bilinFormAt_add` before a lemma
on the whole application can fire, and `Pi.add_apply` does not apply to vectors typed in a
fibre of `V`. So the symplectic form of two or three pull-backs, of a pull-back along a
composite, and of that pull-back pulled back once more, has a `simp↓` lemma of its own, such as
`IsNondegenerate.symplecticFormAt_pullback_pullback_apply`, which `simp` applies to the whole
application first. A single such lemma for every two-form `σ`, rewriting `h.symplecticFormAt x v w`
to `σ.bilinFormAt x v w`, does not help: its vectors are typed in the fibre of the bundle of `σ`,
and `simp` cannot match vectors typed in a fibre of `V` against them. In the cases that no lemma
covers, `simp` leaves the symplectic form of such a form split into unevaluated bilinear forms.

In `pushforward_pullback_id` and `pushforward_pullback_comp`, the identity of each fibre is
`Bundle.Pullback.idFiberEquiv` or `Bundle.Pullback.compFiberEquiv`
(`SymplecticGeometry/Geometry/Manifold/VectorBundle/Pullback.lean`), whose types name both
fibres. The two sides of each statement are forms on different bundles, and evaluating each
separately leaves values that differ in hidden arguments naming those bundles.
`bilinFormAt_pullback_id_apply` and `bilinFormAt_pullback_comp_apply`, which are `@[simp high]`,
instead write the left-hand form through the fibre equivalence in terms of the right-hand one, so
that `simp` brings both sides to the same term.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.6
  (symplectic vector bundles).
* D. Husemoller, *Fibre Bundles*, 3rd ed., Graduate Texts in Mathematics 20, Springer, 1994,
  Chapter 2 (induced bundles).
-/

public section

noncomputable section

open _root_.Bundle
open scoped Manifold

namespace SymplecticGeometry.Bundle

/-! ### Transition maps of pulled-back frames -/

section FrameTransition

variable {M N W : Type*} [AddCommGroup W] [Module ℝ W] [TopologicalSpace W]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]

/-- The transition map between the pull-backs `y ↦ Φ (f y)` and `y ↦ Φ' (f y)` of two frames along
a map `f` is the transition map between `Φ` and `Φ'` at `f y`. -/
@[simp]
theorem frameTransition_pullback (Φ Φ' : ∀ x, W ≃L[ℝ] V x) (f : N → M) (y : N) :
    frameTransition (V := f *ᵖ V) (fun y ↦ Φ (f y)) (fun y ↦ Φ' (f y)) y =
      frameTransition Φ Φ' (f y) := by
  ext v
  exact (frameTransition_apply _ _ y v).trans (frameTransition_apply Φ Φ' (f y) v).symm

end FrameTransition

variable {EB HB M : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [TopologicalSpace HB] {I : ModelWithCorners ℝ EB HB}
  [TopologicalSpace M] [ChartedSpace HB M]
  {EN HN N : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
  {I' : ModelWithCorners ℝ EN HN} [TopologicalSpace N] [ChartedSpace HN N]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V] {n : ℕ∞}
  {K : Type*} [FunLike K N M] [ContinuousMapClass K N M]

namespace ContMDiffTwoForm

/-! ### The pull-back of a two-form -/

/-- The pull-back of a two-form `ω` on `V` along a `C^n` map `f : N → M`: the two-form on the
pull-back bundle `f *ᵖ V` whose value at `y` is `ω (f y)`. -/
def pullback (ω : ContMDiffTwoForm I n F V) (f : K) (hf : ContMDiff I' I n f) :
    ContMDiffTwoForm I' n F ((f : N → M) *ᵖ V) where
  toFun y := ω (f y)
  contMDiff_toFun :=
    (Pullback.contMDiff_continuousAlternatingMap_section_iff f hf _).2
      (ω.contMDiff.comp hf)

/-- The pull-back takes the value `ω (f y)` at `y`. -/
@[simp]
theorem pullback_apply (ω : ContMDiffTwoForm I n F V) (f : K) (hf : ContMDiff I' I n f) (y : N) :
    ω.pullback f hf y = ω (f y) :=
  (rfl)

/-- A two-form `ω` on a pull-back bundle `f *ᵖ V` evaluates on vectors `v w : V (f y)` as
`ω y ![v, w]`. This is `bilinFormAt_apply` for vectors typed in `V (f y)` rather than in the
fibre `(f *ᵖ V) y`: the two types are the same, but `simp` does not see it. -/
@[simp]
theorem bilinFormAt_apply_pullback {f : K}
    (ω : ContMDiffTwoForm I' n F ((f : N → M) *ᵖ V)) (y : N) (v w : V (f y)) :
    ω.bilinFormAt y v w = ω y ![v, w] :=
  bilinFormAt_apply ω y v w

/-- The bilinear form of the pull-back at `y` is that of `ω` at `f y`.

This is not `@[simp]`: after it rewrites, the instances around the form still name the fibre
`(f *ᵖ V) y`, and `bilinFormAt_apply` no longer applies. On vectors, `simp` uses
`bilinFormAt_apply_pullback` and then `pullback_apply_apply` instead. -/
theorem bilinFormAt_pullback (ω : ContMDiffTwoForm I n F V) (f : K) (hf : ContMDiff I' I n f)
    (y : N) : (ω.pullback f hf).bilinFormAt y = ω.bilinFormAt (f y) := by
  rw [bilinFormAt_def, bilinFormAt_def, pullback_apply]
  -- The two sides differ only in the fibre type, `(f *ᵖ V) y` against `V (f y)`.
  rfl

/-- The bilinear form of the pull-back at `y` evaluates on `v w : V (f y)` as `ω (f y) ![v, w]`.

This is not `@[simp]`: `simp` proves it with `bilinFormAt_apply_pullback` and
`pullback_apply_apply`. -/
theorem bilinFormAt_pullback_apply (ω : ContMDiffTwoForm I n F V) (f : K) (hf : ContMDiff I' I n f)
    (y : N) (v w : V (f y)) : (ω.pullback f hf).bilinFormAt y v w = ω (f y) ![v, w] :=
  ((ω.pullback f hf).bilinFormAt_apply y v w).trans
    (congrArg (· ![v, w]) (pullback_apply ω f hf y))

/-- The pull-back at `y` takes on the pair `![v, w]` of vectors `v w : V (f y)` the value of
`ω (f y)` on that pair.

On the left the pair is a family in the fibre `(f *ᵖ V) y`, on the right one in `V (f y)`, and
`simp` does not identify the two. The lemma is a `simp` lemma applied before the subterms are
simplified (`simp↓`): otherwise `pullback_apply` would rewrite `ω.pullback f hf y` first, and on the
pull-back of a combination `pullback_add`, `pullback_sub`, `pullback_neg` or `pullback_smul`
would, so a plain `@[simp]` lemma would never fire. `simp` then evaluates the form `ω (f y)` on
vectors of `V (f y)`. -/
@[simp↓]
theorem pullback_apply_apply (ω : ContMDiffTwoForm I n F V) (f : K) (hf : ContMDiff I' I n f)
    (y : N) (v w : V (f y)) : ω.pullback f hf y ![v, w] = ω (f y) ![v, w] :=
  congrArg (· ![v, w]) (pullback_apply ω f hf y)

/-- The pull-back at `y` takes on the pair `![v, w]` of vectors `v w : (f *ᵖ V) y` of the
pull-back fibre the value of `ω (f y)` on the same pair, formed in `V (f y)`.

This is `pullback_apply_apply` for vectors typed in the pull-back fibre. `simp` meets such a
pair when it evaluates an iterated pull-back `(ω.pullback g hg).pullback f hf` on vectors of
the middle fibre `(g *ᵖ V) (f z)`: after `pullback_apply_apply`, the pair is formed in that
fibre. It is applied before the subterms are simplified (`simp↓`), as `pullback_apply_apply`
is. -/
@[simp↓]
theorem pullback_apply_apply_fiber (ω : ContMDiffTwoForm I n F V) (f : K)
    (hf : ContMDiff I' I n f) (y : N) (v w : ((f : N → M) *ᵖ V) y) :
    ω.pullback f hf y ![v, w] = ω (f y) ![v, w] :=
  congrArg (· ![v, w]) (pullback_apply ω f hf y)

/-- The pull-back of the zero form is zero. -/
@[simp]
theorem pullback_zero (f : K) (hf : ContMDiff I' I n f) :
    (0 : ContMDiffTwoForm I n F V).pullback f hf = 0 := by
  ext y
  exact rfl

/-- The pull-back of a sum is the sum of the pull-backs. -/
@[simp]
theorem pullback_add (ω ω' : ContMDiffTwoForm I n F V) (f : K) (hf : ContMDiff I' I n f) :
    (ω + ω').pullback f hf = ω.pullback f hf + ω'.pullback f hf := by
  ext y
  exact rfl

/-- The pull-back of a multiple is the multiple of the pull-back. -/
@[simp]
theorem pullback_smul (c : ℝ) (ω : ContMDiffTwoForm I n F V) (f : K) (hf : ContMDiff I' I n f) :
    (c • ω).pullback f hf = c • ω.pullback f hf := by
  ext y
  exact rfl

variable (I F V n) in
/-- The pull-back of two-forms along a `C^n` map `f`, as a linear map. -/
def pullbackLinearMap (f : K) (hf : ContMDiff I' I n f) :
    ContMDiffTwoForm I n F V →ₗ[ℝ] ContMDiffTwoForm I' n F ((f : N → M) *ᵖ V) where
  toFun ω := ω.pullback f hf
  map_add' ω ω' := pullback_add ω ω' f hf
  map_smul' c ω := pullback_smul c ω f hf

/-- The linear map `pullbackLinearMap f hf` sends `ω` to its pull-back along `f`. -/
@[simp]
theorem pullbackLinearMap_apply (f : K) (hf : ContMDiff I' I n f) (ω : ContMDiffTwoForm I n F V) :
    pullbackLinearMap I F V n f hf ω = ω.pullback f hf :=
  (rfl)

/-- The pull-back of the negative of a two-form is the negative of its pull-back. -/
@[simp]
theorem pullback_neg (ω : ContMDiffTwoForm I n F V) (f : K) (hf : ContMDiff I' I n f) :
    (-ω).pullback f hf = -ω.pullback f hf :=
  map_neg (pullbackLinearMap I F V n f hf) ω

/-- The pull-back of a difference is the difference of the pull-backs. -/
@[simp]
theorem pullback_sub (ω ω' : ContMDiffTwoForm I n F V) (f : K) (hf : ContMDiff I' I n f) :
    (ω - ω').pullback f hf = ω.pullback f hf - ω'.pullback f hf :=
  map_sub (pullbackLinearMap I F V n f hf) ω ω'

/-- `simp` evaluates the pull-back of a sum, a difference, a negative or a multiple on vectors of
`V (f y)`, with `Bundle.Pullback.add_apply_pullback`, `linearMap_sub_apply_pullback`,
`neg_apply_pullback` and `smul_apply_pullback`. -/
example (ω ω' : ContMDiffTwoForm I n F V) (f : K) (hf : ContMDiff I' I n f) (y : N) (c : ℝ)
    (v w : V (f y)) :
    ((ω + ω').pullback f hf).bilinFormAt y v w = ω (f y) ![v, w] + ω' (f y) ![v, w] ∧
      ((ω - ω').pullback f hf).bilinFormAt y v w = ω (f y) ![v, w] - ω' (f y) ![v, w] ∧
      ((-ω).pullback f hf).bilinFormAt y v w = -ω (f y) ![v, w] ∧
      ((c • ω).pullback f hf).bilinFormAt y v w = c * ω (f y) ![v, w] := by
  simp

/-- `simp` evaluates the bilinear form of the pull-back of the zero form, with
`Bundle.Pullback.linearMap_zero_apply_pullback`, and the pull-back of a sum, a difference, a
negative or a multiple on a pair `![v, w]` of vectors of `V (f y)`, with `pullback_apply_apply`. -/
example (ω ω' : ContMDiffTwoForm I n F V) (f : K) (hf : ContMDiff I' I n f) (y : N)
    (c : ℝ) (v w : V (f y)) :
    ((0 : ContMDiffTwoForm I n F V).pullback f hf).bilinFormAt y v w = 0 ∧
      (ω + ω').pullback f hf y ![v, w] = ω (f y) ![v, w] + ω' (f y) ![v, w] ∧
      (ω - ω').pullback f hf y ![v, w] = ω (f y) ![v, w] - ω' (f y) ![v, w] ∧
      (-ω).pullback f hf y ![v, w] = -ω (f y) ![v, w] ∧
      (c • ω).pullback f hf y ![v, w] = c * ω (f y) ![v, w] := by
  simp

/-! ### Nondegeneracy -/

variable {ω : ContMDiffTwoForm I n F V}

/-- The pull-back of a nondegenerate two-form is nondegenerate. -/
theorem IsNondegenerate.pullback (h : ω.IsNondegenerate) (f : K) (hf : ContMDiff I' I n f) :
    (ω.pullback f hf).IsNondegenerate :=
  isNondegenerate_def.2 fun y ↦ by
    rw [bilinFormAt_pullback]
    exact h.nondegenerate_bilinFormAt (f y)

/-- The symplectic form of the pull-back on the fibre over `y` is that of `ω` over `f y`.

This is not `@[simp]`, for the reason given at `bilinFormAt_pullback`. On vectors, `simp` uses
`IsNondegenerate.toBilinForm_symplecticFormAt` and the lemmas that evaluate `bilinFormAt`
instead. -/
theorem IsNondegenerate.symplecticFormAt_pullback (h : ω.IsNondegenerate) (f : K)
    (hf : ContMDiff I' I n f) (y : N) :
    (h.pullback f hf).symplecticFormAt y = h.symplecticFormAt (f y) :=
  TauCeti.SymplecticForm.toBilinForm_injective <| by
    rw [IsNondegenerate.toBilinForm_symplecticFormAt, IsNondegenerate.toBilinForm_symplecticFormAt,
      bilinFormAt_pullback]

/-- The symplectic form of the pull-back on the fibre over `y` evaluates as `ω (f y)`, for any
proof `h` that the pull-back is nondegenerate, such as `h.pullback f hf`.

This is not `@[simp]`: `simp` proves it with `IsNondegenerate.toBilinForm_symplecticFormAt`,
`bilinFormAt_apply_pullback` and `pullback_apply_apply`. -/
theorem IsNondegenerate.symplecticFormAt_pullback_apply {f : K} {hf : ContMDiff I' I n f}
    (h : (ω.pullback f hf).IsNondegenerate) (y : N) (v w : V (f y)) :
    h.symplecticFormAt y v w = ω (f y) ![v, w] :=
  (h.symplecticFormAt_apply y v w).trans
    (congrArg (· ![v, w]) (pullback_apply ω f hf y))

/-- `simp` evaluates the symplectic form of the pull-back of a sum, a difference or a multiple of
two-forms on vectors of `V (f y)`, with `IsNondegenerate.toBilinForm_symplecticFormAt` and the
lemmas that evaluate the bilinear form of such a pull-back. -/
example (ω ω' : ContMDiffTwoForm I n F V) (f : K) (hf : ContMDiff I' I n f) (y : N) (c : ℝ)
    (v w : V (f y)) (h₁ : ((ω + ω').pullback f hf).IsNondegenerate)
    (h₂ : ((ω - ω').pullback f hf).IsNondegenerate)
    (h₃ : ((c • ω).pullback f hf).IsNondegenerate) :
    h₁.symplecticFormAt y v w = ω (f y) ![v, w] + ω' (f y) ![v, w] ∧
      h₂.symplecticFormAt y v w = ω (f y) ![v, w] - ω' (f y) ![v, w] ∧
      h₃.symplecticFormAt y v w = c * ω (f y) ![v, w] := by
  simp

/-! ### Tame and compatible pairs -/

variable {J : ContMDiffComplexStructure I n F V}

/-- If `ω` tames `J`, the pull-back of `ω` tames the pull-back of `J`. -/
theorem Tames.pullback (h : ω.Tames J) (f : K) (hf : ContMDiff I' I n f) :
    (ω.pullback f hf).Tames (J.pullback f hf) :=
  tames_def.2 fun y v hv ↦ by
    simp only [bilinFormAt_pullback, ContMDiffComplexStructure.pullback_toEndomorphism]
    exact tames_def.1 h (f y) v hv

/-- If `ω` is invariant under `J`, the pull-back of `ω` is invariant under the pull-back of `J`. -/
theorem Invariant.pullback (h : ω.Invariant J) (f : K) (hf : ContMDiff I' I n f) :
    (ω.pullback f hf).Invariant (J.pullback f hf) :=
  invariant_def.2 fun y v w ↦ by
    simp only [bilinFormAt_pullback, ContMDiffComplexStructure.pullback_toEndomorphism]
    exact invariant_def.1 h (f y) v w

/-- If `ω` is compatible with `J`, the pull-back of `ω` is compatible with the pull-back of `J`. -/
theorem Compatible.pullback (h : ω.Compatible J) (f : K) (hf : ContMDiff I' I n f) :
    (ω.pullback f hf).Compatible (J.pullback f hf) :=
  ⟨h.invariant.pullback f hf, h.tames.pullback f hf⟩

/-! ### Symplectic frames -/

/-- A symplectic frame `Φ` of `ω` over `U`, modelled on `(W, σ)`, pulls back along `f` to the
symplectic frame `y ↦ Φ (f y)` of the pull-back of `ω` over `f ⁻¹' U`. -/
theorem IsSymplecticFrameOn.pullback {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {σ : TauCeti.SymplecticForm W} {U : Set M} {Φ : ∀ x, W ≃L[ℝ] V x}
    (h : ω.IsSymplecticFrameOn σ U Φ) (f : K) (hf : ContMDiff I' I n f) :
    (ω.pullback f hf).IsSymplecticFrameOn σ (f ⁻¹' U) fun y ↦ Φ (f y) where
  contMDiffOn p hp := by
    rw [Pullback.contMDiffWithinAt_iff f (hf _)]
    exact ⟨contMDiffWithinAt_fst, h.contMDiffOn.comp (hf.prodMap contMDiff_id).contMDiffOn
      (fun q (hq : q ∈ ((f : N → M) ⁻¹' U) ×ˢ (Set.univ : Set W)) ↦ ⟨hq.1, Set.mem_univ _⟩) p hp⟩
  map_bilinFormAt y hy v w := by
    rw [bilinFormAt_pullback]
    exact h.map_bilinFormAt (f y) hy v w

/-! ### Pull-backs and isomorphisms of bundles -/

section Pushforward

variable {F₁ F₂ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
  {V₁ V₂ : M → Type*}
  [∀ x, AddCommGroup (V₁ x)] [∀ x, Module ℝ (V₁ x)]
  [∀ x, TopologicalSpace (V₁ x)] [∀ x, IsTopologicalAddGroup (V₁ x)]
  [∀ x, ContinuousSMul ℝ (V₁ x)] [TopologicalSpace (TotalSpace F₁ V₁)]
  [FiberBundle F₁ V₁] [VectorBundle ℝ F₁ V₁]
  [∀ x, AddCommGroup (V₂ x)] [∀ x, Module ℝ (V₂ x)]
  [∀ x, TopologicalSpace (V₂ x)] [∀ x, IsTopologicalAddGroup (V₂ x)]
  [∀ x, ContinuousSMul ℝ (V₂ x)] [TopologicalSpace (TotalSpace F₂ V₂)]
  [FiberBundle F₂ V₂] [VectorBundle ℝ F₂ V₂]
  [FiniteDimensional ℝ F₁]
  (Φ : ∀ x, V₁ x ≃L[ℝ] V₂ x)
  (hΦ : ContMDiff (I.prod 𝓘(ℝ, F₁)) (I.prod 𝓘(ℝ, F₂)) n
    (fun p : TotalSpace F₁ V₁ ↦ TotalSpace.mk' F₂ p.proj (Φ p.proj p.snd)))

/-- Pulling back commutes with transport along an isomorphism of bundles: the pull-back along `f`
of the transport of `ω` along `Φ` is the transport of the pull-back of `ω` along the pulled-back
isomorphism `y ↦ Φ (f y)` of `f *ᵖ V₁` onto `f *ᵖ V₂`. -/
theorem pullback_pushforward (ω : ContMDiffTwoForm I n F₁ V₁) (f : K) (hf : ContMDiff I' I n f) :
    (pushforward Φ hΦ ω).pullback f hf =
      pushforward (V₁ := (f : N → M) *ᵖ V₁) (V₂ := (f : N → M) *ᵖ V₂) (fun y ↦ Φ (f y))
        (Pullback.contMDiff_fiberwise (fun x v ↦ Φ x v) hΦ f hf) (ω.pullback f hf) := by
  refine ContMDiffSection.ext fun y ↦
    ((pullback_apply _ f hf y).trans (pushforward_apply Φ hΦ ω (f y))).trans ?_
  -- `ω.pullback f hf y` is `ω (f y)`, read in the fibre `(f *ᵖ V₁) y`.
  exact (pushforward_apply (V₁ := (f : N → M) *ᵖ V₁) (V₂ := (f : N → M) *ᵖ V₂) (fun y ↦ Φ (f y)) _
    (ω.pullback f hf) y).symm

end Pushforward

/-! ### Pull-backs along the identity and along a composite -/

/-- The bilinear form of the pull-back of `ω` along the identity at `x` takes on `v` and `w` the
value of the bilinear form of `ω` at `x` on their images under `Bundle.Pullback.idFiberEquiv`,
the identity of the fibre read as a map to `V x`.

It has priority `high`, so that `simp` uses it before `bilinFormAt_apply`: that lemma would
evaluate the form on `![v, w]` formed in the pull-back fibre, which a value of `ω x` on vectors
of `V x` does not match. -/
@[simp high]
theorem bilinFormAt_pullback_id_apply (ω : ContMDiffTwoForm I n F V) (x : M)
    (v w : (((ContMDiffMap.id : C^n⟮I, M; I, M⟯) : M → M) *ᵖ V) x) :
    (ω.pullback ContMDiffMap.id ContMDiffMap.id.contMDiff).bilinFormAt x v w =
      ω.bilinFormAt x (Pullback.idFiberEquiv I n ℝ V x v) (Pullback.idFiberEquiv I n ℝ V x w) := by
  rw [bilinFormAt_apply, bilinFormAt_apply, pullback_apply, Pullback.idFiberEquiv_apply,
    Pullback.idFiberEquiv_apply]
  -- The sides are `ω (ContMDiffMap.id x) ![v, w]` and `ω x ![v, w]`, with `![v, w]` formed in
  -- the pull-back fibre on the left and in `V x` on the right: equal by definition only.
  rfl

variable {EP HP P : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
  {I'' : ModelWithCorners ℝ EP HP} [TopologicalSpace P] [ChartedSpace HP P]
  {EQ HQ Q : Type*} [NormedAddCommGroup EQ] [NormedSpace ℝ EQ] [TopologicalSpace HQ]
  {I''' : ModelWithCorners ℝ EQ HQ} [TopologicalSpace Q] [ChartedSpace HQ Q]

/-- The bilinear form of the pull-back of `ω` along a composite `g ∘ f` at `z` takes on `v` and
`w` the value of the bilinear form of the pull-back along `g` and then along `f` on their images
under `Bundle.Pullback.compFiberEquiv`, the identity of the fibre read as a map to the fibre of
`f *ᵖ (g *ᵖ V)`.

It has priority `high`, for the reason given at `bilinFormAt_pullback_id_apply`. -/
@[simp high]
theorem bilinFormAt_pullback_comp_apply (ω : ContMDiffTwoForm I n F V) (g : C^n⟮I', N; I, M⟯)
    (f : C^n⟮I'', P; I', N⟯) (z : P)
    (v w : (((g.comp f : C^n⟮I'', P; I, M⟯) : P → M) *ᵖ V) z) :
    (ω.pullback (g.comp f) (g.comp f).contMDiff).bilinFormAt z v w =
      ((ω.pullback g g.contMDiff).pullback f f.contMDiff).bilinFormAt z
        (Pullback.compFiberEquiv ℝ V g f z v) (Pullback.compFiberEquiv ℝ V g f z w) := by
  rw [bilinFormAt_apply, bilinFormAt_apply, pullback_apply, pullback_apply, pullback_apply,
    Pullback.compFiberEquiv_apply, Pullback.compFiberEquiv_apply]
  -- The sides are `ω ((g.comp f) z) ![v, w]` and `ω (g (f z)) ![v, w]`, with `![v, w]` formed
  -- in the two different pull-back fibres: equal by definition only.
  rfl

/-- The bilinear form of the pull-back of `ω` along a composite `g.comp f` at `z` evaluates on
`v w : V (g (f z))` as `ω (g (f z)) ![v, w]`, for any proof that the composite is `C^n`.

`bilinFormAt_apply_pullback` does not match such vectors: the fibre of the pull-back at `z` is
`V ((g.comp f) z)`, which `simp` does not identify with `V (g (f z))`.

It is applied before the subterms are simplified (`simp↓`), so that it still matches the
pull-back of a sum, a difference, a negative or a multiple, which `pullback_add`,
`pullback_sub`, `pullback_neg` and `pullback_smul` would otherwise split first. -/
@[simp↓]
theorem bilinFormAt_pullback_comp_apply_pullback (ω : ContMDiffTwoForm I n F V)
    (g : C^n⟮I', N; I, M⟯) (f : C^n⟮I'', P; I', N⟯) (hgf : ContMDiff I'' I n (g.comp f)) (z : P)
    (v w : V (g (f z))) :
    (ω.pullback (g.comp f) hgf).bilinFormAt z v w = ω (g (f z)) ![v, w] :=
  -- `bilinFormAt_pullback_apply` gives `ω ((g.comp f) z) ![v, w]`; the fibre `V x` depends on
  -- `x`, so `ContMDiffMap.comp_apply` cannot rewrite the point, and the two agree by definition.
  ω.bilinFormAt_pullback_apply (g.comp f) hgf z v w

/-- The bilinear form of the pull-back of `ω` along `g` and then along `f` at `z` evaluates on
`v w : V (g (f z))` as `ω (g (f z)) ![v, w]`. It is `bilinFormAt_pullback_apply` for the form
`ω.pullback g`, restated with the vectors typed in the fibre of `V` rather than in that of
`g *ᵖ V`, since `simp` cannot match that lemma on such vectors.

It is applied before the subterms are simplified (`simp↓`), so that it still matches the
iterated pull-back of a sum, a difference, a negative or a multiple, which `pullback_add`,
`pullback_sub`, `pullback_neg` and `pullback_smul` would otherwise split first. -/
@[simp↓]
theorem bilinFormAt_pullback_pullback_apply {K' : Type*} [FunLike K' P N]
    [ContinuousMapClass K' P N] (ω : ContMDiffTwoForm I n F V) (g : K) (hg : ContMDiff I' I n g)
    (f : K') (hf : ContMDiff I'' I' n f) (z : P) (v w : V (g (f z))) :
    ((ω.pullback g hg).pullback f hf).bilinFormAt z v w = ω (g (f z)) ![v, w] :=
  (ω.pullback g hg).bilinFormAt_pullback_apply f hf z v w

/-- The symplectic form of the pull-back of `ω` along `g` and then along `f` at `z` evaluates on
`v w : V (g (f z))` as `ω (g (f z)) ![v, w]`, for any proof of the nondegeneracy of the iterated
pull-back.

On a single form `simp` does not need it: `IsNondegenerate.toBilinForm_symplecticFormAt` and
`bilinFormAt_pullback_pullback_apply` give the value. But when the iterated pull-back is that of a
sum, a difference, a negative or a multiple, `simp` first rewrites the form named in the type of
`h` with `pullback_add` and its partners, and then splits the bilinear form that
`IsNondegenerate.toBilinForm_symplecticFormAt` gives, before a lemma on the whole application can
fire. So this lemma is applied before the subterms are simplified (`simp↓`), as
`bilinFormAt_pullback_pullback_apply` is. The same splitting happens at other depths, where
`IsNondegenerate.symplecticFormAt_pullback_pullback_pullback_apply`,
`IsNondegenerate.symplecticFormAt_pullback_comp_apply_pullback` and
`IsNondegenerate.symplecticFormAt_pullback_comp_pullback_apply` play the same part. -/
@[simp↓]
theorem IsNondegenerate.symplecticFormAt_pullback_pullback_apply {K' : Type*} [FunLike K' P N]
    [ContinuousMapClass K' P N] {g : K} {hg : ContMDiff I' I n g} {f : K'}
    {hf : ContMDiff I'' I' n f} (h : ((ω.pullback g hg).pullback f hf).IsNondegenerate) (z : P)
    (v w : V (g (f z))) : h.symplecticFormAt z v w = ω (g (f z)) ![v, w] :=
  IsNondegenerate.symplecticFormAt_pullback_apply (ω := ω.pullback g hg) h z v w

/-- The bilinear form of the pull-back of `ω` along `g`, then `f`, then `e` at `z` evaluates on
`v w : V (g (f (e z)))` as `ω (g (f (e z))) ![v, w]`. It is `bilinFormAt_pullback_pullback_apply`
one level deeper, with the vectors typed in the fibre of `V`, and it is applied before the
subterms are simplified (`simp↓`) for the same reason. -/
@[simp↓]
theorem bilinFormAt_pullback_pullback_pullback_apply {K' K'' : Type*} [FunLike K' P N]
    [ContinuousMapClass K' P N] [FunLike K'' Q P] [ContinuousMapClass K'' Q P]
    (ω : ContMDiffTwoForm I n F V) (g : K) (hg : ContMDiff I' I n g) (f : K')
    (hf : ContMDiff I'' I' n f) (e : K'') (he : ContMDiff I''' I'' n e) (z : Q)
    (v w : V (g (f (e z)))) :
    (((ω.pullback g hg).pullback f hf).pullback e he).bilinFormAt z v w =
      ω (g (f (e z))) ![v, w] :=
  ((ω.pullback g hg).pullback f hf).bilinFormAt_pullback_apply e he z v w

/-- The bilinear form of the pull-back of `ω` along a composite `g.comp f`, pulled back again
along `e`, at `q` evaluates on `v w : V (g (f (e q)))` as `ω (g (f (e q))) ![v, w]`, for any
proof that the composite is `C^n`. Neither `bilinFormAt_pullback_comp_apply_pullback` nor
`bilinFormAt_pullback_pullback_apply` matches such vectors, since the fibre of the inner
pull-back at `e q` is `V ((g.comp f) (e q))`. It is applied before the subterms are simplified
(`simp↓`), as `bilinFormAt_pullback_comp_apply_pullback` is. -/
@[simp↓]
theorem bilinFormAt_pullback_comp_pullback_apply (ω : ContMDiffTwoForm I n F V)
    (g : C^n⟮I', N; I, M⟯) (f : C^n⟮I'', P; I', N⟯) (hgf : ContMDiff I'' I n (g.comp f))
    {K'' : Type*} [FunLike K'' Q P] [ContinuousMapClass K'' Q P] (e : K'')
    (he : ContMDiff I''' I'' n e) (q : Q) (v w : V (g (f (e q)))) :
    ((ω.pullback (g.comp f) hgf).pullback e he).bilinFormAt q v w = ω (g (f (e q))) ![v, w] :=
  -- As in `bilinFormAt_pullback_comp_apply_pullback`, the point `(g.comp f) (e q)` given by
  -- `bilinFormAt_pullback_apply` agrees with `g (f (e q))` by definition only.
  (ω.pullback (g.comp f) hgf).bilinFormAt_pullback_apply e he q v w

/-- The symplectic form of the pull-back of `ω` along `g`, then `f`, then `e` at `z` evaluates on
`v w : V (g (f (e z)))` as `ω (g (f (e z))) ![v, w]`, for any proof of the nondegeneracy of the
iterated pull-back. It is `IsNondegenerate.symplecticFormAt_pullback_pullback_apply` one level
deeper, and is applied before the subterms are simplified (`simp↓`) for the same reason: so that
`simp` also evaluates it when `ω` is a sum, a difference, a negative or a multiple. -/
@[simp↓]
theorem IsNondegenerate.symplecticFormAt_pullback_pullback_pullback_apply {K' K'' : Type*}
    [FunLike K' P N] [ContinuousMapClass K' P N] [FunLike K'' Q P] [ContinuousMapClass K'' Q P]
    {g : K} {hg : ContMDiff I' I n g} {f : K'} {hf : ContMDiff I'' I' n f} {e : K''}
    {he : ContMDiff I''' I'' n e}
    (h : (((ω.pullback g hg).pullback f hf).pullback e he).IsNondegenerate) (z : Q)
    (v w : V (g (f (e z)))) : h.symplecticFormAt z v w = ω (g (f (e z))) ![v, w] :=
  IsNondegenerate.symplecticFormAt_pullback_apply (ω := (ω.pullback g hg).pullback f hf) h z v w

/-- The symplectic form of the pull-back of `ω` along a composite `g.comp f` at `z` evaluates on
`v w : V (g (f z))` as `ω (g (f z)) ![v, w]`, for any proofs that the composite is `C^n` and that
the pull-back is nondegenerate. It is applied before the subterms are simplified (`simp↓`), as
`IsNondegenerate.symplecticFormAt_pullback_pullback_apply` is, so that `simp` also evaluates it
when `ω` is a sum, a difference, a negative or a multiple. -/
@[simp↓]
theorem IsNondegenerate.symplecticFormAt_pullback_comp_apply_pullback {g : C^n⟮I', N; I, M⟯}
    {f : C^n⟮I'', P; I', N⟯} {hgf : ContMDiff I'' I n (g.comp f)}
    (h : (ω.pullback (g.comp f) hgf).IsNondegenerate) (z : P) (v w : V (g (f z))) :
    h.symplecticFormAt z v w = ω (g (f z)) ![v, w] :=
  -- As in `bilinFormAt_pullback_comp_apply_pullback`, the point `(g.comp f) z` agrees with
  -- `g (f z)` by definition only.
  h.symplecticFormAt_pullback_apply z v w

/-- The symplectic form of the pull-back of `ω` along a composite `g.comp f`, pulled back again
along `e`, at `q` evaluates on `v w : V (g (f (e q)))` as `ω (g (f (e q))) ![v, w]`, for any
proofs that the composite is `C^n` and that the pull-back is nondegenerate. It is applied before
the subterms are simplified (`simp↓`), as
`IsNondegenerate.symplecticFormAt_pullback_pullback_apply` is, so that `simp` also evaluates it
when `ω` is a sum, a difference, a negative or a multiple. -/
@[simp↓]
theorem IsNondegenerate.symplecticFormAt_pullback_comp_pullback_apply {g : C^n⟮I', N; I, M⟯}
    {f : C^n⟮I'', P; I', N⟯} {hgf : ContMDiff I'' I n (g.comp f)} {K'' : Type*}
    [FunLike K'' Q P] [ContinuousMapClass K'' Q P] {e : K''} {he : ContMDiff I''' I'' n e}
    (h : ((ω.pullback (g.comp f) hgf).pullback e he).IsNondegenerate) (q : Q)
    (v w : V (g (f (e q)))) : h.symplecticFormAt q v w = ω (g (f (e q))) ![v, w] :=
  -- The point `(g.comp f) (e q)` agrees with `g (f (e q))` by definition only.
  IsNondegenerate.symplecticFormAt_pullback_apply (ω := ω.pullback (g.comp f) hgf) h q v w

/-- `simp` evaluates the iterated pull-back of a form, and its symplectic form, on vectors of the
fibre of `V`, also when the form is a sum. -/
example {K' : Type*} [FunLike K' P N] [ContinuousMapClass K' P N]
    (ω ω' : ContMDiffTwoForm I n F V) (g : K) (hg : ContMDiff I' I n g) (f : K')
    (hf : ContMDiff I'' I' n f) (z : P) (v w : V (g (f z)))
    (h : ((ω.pullback g hg).pullback f hf).IsNondegenerate)
    (h' : (((ω + ω').pullback g hg).pullback f hf).IsNondegenerate) :
    ((ω.pullback g hg).pullback f hf).bilinFormAt z v w = ω (g (f z)) ![v, w] ∧
      h.symplecticFormAt z v w = ω (g (f z)) ![v, w] ∧
      h'.symplecticFormAt z v w = ω (g (f z)) ![v, w] + ω' (g (f z)) ![v, w] := by
  simp

/-- `simp` evaluates three iterated pull-backs on vectors of the fibre of `V`, the pull-back
along a composite on vectors of the fibre of `V`, and two iterated pull-backs on vectors of the
middle fibre `(g *ᵖ V) (f z)`. -/
example (ω : ContMDiffTwoForm I n F V) (g : C^n⟮I', N; I, M⟯) (f : C^n⟮I'', P; I', N⟯)
    (e : C^n⟮I''', Q; I'', P⟯) (q : Q) (v₃ w₃ : V (g (f (e q)))) (z : P) (v w : V (g (f z)))
    (v' w' : ((g : N → M) *ᵖ V) (f z)) :
    (((ω.pullback g g.contMDiff).pullback f f.contMDiff).pullback e e.contMDiff).bilinFormAt q
        v₃ w₃ = ω (g (f (e q))) ![v₃, w₃] ∧
      (ω.pullback (g.comp f) (g.comp f).contMDiff).bilinFormAt z v w = ω (g (f z)) ![v, w] ∧
      ((ω.pullback g g.contMDiff).pullback f f.contMDiff).bilinFormAt z v' w' =
        ω (g (f z)) ![v', w'] := by
  simp

/-- `simp` evaluates the symplectic form of three iterated pull-backs and of a pull-back along a
composite, and the pull-back along a composite pulled back again, on vectors of the fibre
of `V`. -/
example (ω : ContMDiffTwoForm I n F V) (g : C^n⟮I', N; I, M⟯) (f : C^n⟮I'', P; I', N⟯)
    (e : C^n⟮I''', Q; I'', P⟯) (hgf : ContMDiff I'' I n (g.comp f)) (q : Q)
    (v₃ w₃ : V (g (f (e q)))) (z : P) (v w : V (g (f z)))
    (h₃ : (((ω.pullback g g.contMDiff).pullback f f.contMDiff).pullback e
      e.contMDiff).IsNondegenerate)
    (h : (ω.pullback (g.comp f) hgf).IsNondegenerate) :
    h₃.symplecticFormAt q v₃ w₃ = ω (g (f (e q))) ![v₃, w₃] ∧
      h.symplecticFormAt z v w = ω (g (f z)) ![v, w] ∧
      ((ω.pullback (g.comp f) hgf).pullback e e.contMDiff).bilinFormAt q v₃ w₃ =
        ω (g (f (e q))) ![v₃, w₃] := by
  simp

/-- `simp` evaluates iterated pull-backs, and pull-backs along a composite, of sums,
differences, negatives and multiples on vectors of the fibre of `V`. -/
example (ω ω' : ContMDiffTwoForm I n F V) (g : C^n⟮I', N; I, M⟯) (f : C^n⟮I'', P; I', N⟯)
    (e : C^n⟮I''', Q; I'', P⟯) (c : ℝ) (q : Q) (v₃ w₃ : V (g (f (e q)))) (z : P)
    (v w : V (g (f z))) :
    (((ω + ω').pullback g g.contMDiff).pullback f f.contMDiff).bilinFormAt z v w =
        ω (g (f z)) ![v, w] + ω' (g (f z)) ![v, w] ∧
      (((-ω).pullback g g.contMDiff).pullback f f.contMDiff).bilinFormAt z v w =
        -ω (g (f z)) ![v, w] ∧
      ((((ω - c • ω').pullback g g.contMDiff).pullback f f.contMDiff).pullback e
        e.contMDiff).bilinFormAt q v₃ w₃ =
        ω (g (f (e q))) ![v₃, w₃] - c * ω' (g (f (e q))) ![v₃, w₃] ∧
      ((ω + ω').pullback (g.comp f) (g.comp f).contMDiff).bilinFormAt z v w =
        ω (g (f z)) ![v, w] + ω' (g (f z)) ![v, w] ∧
      ((c • ω).pullback (g.comp f) (g.comp f).contMDiff).bilinFormAt z v w =
        c * ω (g (f z)) ![v, w] ∧
      (((ω + ω').pullback (g.comp f) (g.comp f).contMDiff).pullback e e.contMDiff).bilinFormAt q
        v₃ w₃ = ω (g (f (e q))) ![v₃, w₃] + ω' (g (f (e q))) ![v₃, w₃] := by
  simp

/-- `simp` evaluates the symplectic form of three iterated pull-backs, of a pull-back along a
composite, and of that pull-back pulled back again, of a sum, on vectors of the fibre of `V`. -/
example (ω ω' : ContMDiffTwoForm I n F V) (g : C^n⟮I', N; I, M⟯) (f : C^n⟮I'', P; I', N⟯)
    (e : C^n⟮I''', Q; I'', P⟯) (hgf : ContMDiff I'' I n (g.comp f)) (q : Q)
    (v₃ w₃ : V (g (f (e q)))) (z : P) (v w : V (g (f z)))
    (h₃ : ((((ω + ω').pullback g g.contMDiff).pullback f f.contMDiff).pullback e
      e.contMDiff).IsNondegenerate)
    (h : ((ω + ω').pullback (g.comp f) hgf).IsNondegenerate)
    (h' : (((ω + ω').pullback (g.comp f) hgf).pullback e e.contMDiff).IsNondegenerate) :
    h₃.symplecticFormAt q v₃ w₃ = ω (g (f (e q))) ![v₃, w₃] + ω' (g (f (e q))) ![v₃, w₃] ∧
      h.symplecticFormAt z v w = ω (g (f z)) ![v, w] + ω' (g (f z)) ![v, w] ∧
      h'.symplecticFormAt q v₃ w₃ = ω (g (f (e q))) ![v₃, w₃] + ω' (g (f (e q))) ![v₃, w₃] := by
  simp

variable [FiniteDimensional ℝ F]

/-- The pull-back along the identity, moved to `V` by the identity of each fibre, is the form
itself. -/
theorem pushforward_pullback_id (ω : ContMDiffTwoForm I n F V) :
    pushforward (V₁ := ((ContMDiffMap.id : C^n⟮I, M; I, M⟯) : M → M) *ᵖ V) (V₂ := V)
      (Pullback.idFiberEquiv I n ℝ V)
      ((Pullback.idDiffeomorph (F := F) (I := I) (m := n) (n := n) V).contMDiff.congr
        fun p ↦ by rw [Pullback.idDiffeomorph_apply, Pullback.idFiberEquiv_apply])
      (ω.pullback ContMDiffMap.id ContMDiffMap.id.contMDiff) = ω :=
  (pushforward_eq_iff _ _).2 fun x v w ↦ by simp

/-- The pull-back along a composite `g ∘ f`, moved to `f *ᵖ (g *ᵖ V)` by the identity of each
fibre, is the pull-back along `g` and then along `f`. -/
theorem pushforward_pullback_comp (ω : ContMDiffTwoForm I n F V) (g : C^n⟮I', N; I, M⟯)
    (f : C^n⟮I'', P; I', N⟯) :
    pushforward (V₁ := ((g.comp f : C^n⟮I'', P; I, M⟯) : P → M) *ᵖ V)
      (V₂ := (f : P → N) *ᵖ ((g : N → M) *ᵖ V))
      (Pullback.compFiberEquiv ℝ V g f)
      ((Pullback.compDiffeomorph (F := F) (n := n) V g f).contMDiff.congr
        fun p ↦ by rw [Pullback.compDiffeomorph_apply, Pullback.compFiberEquiv_apply])
      (ω.pullback (g.comp f) (g.comp f).contMDiff) =
        (ω.pullback g g.contMDiff).pullback f f.contMDiff :=
  (pushforward_eq_iff _ _).2 fun x v w ↦ by simp

/-! ### The form induced on the tangent bundle along a smooth map -/

section CompMFDeriv

variable [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M] [IsManifold I' ((⊤ : ℕ∞) : WithTop ℕ∞) N]
  [FiniteDimensional ℝ EN]

/-- The two-form `σ(u, v) = ω(df u, df v)` on the tangent bundle of `N` that a two-form `ω` on
the pull-back `f *ᵖ TM` induces along a `C^∞` map `f : N → M`. -/
def compMFDeriv (f : K) (hf : ContMDiff I' I ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (ω : ContMDiffTwoForm I' ⊤ EB ((f : N → M) *ᵖ (TangentSpace I))) :
    ContMDiffTwoForm I' ⊤ EN (TangentSpace I' (M := N)) :=
  compContinuousLinearMap (V := (f : N → M) *ᵖ (TangentSpace I)) (V₂ := TangentSpace I')
    (fun y ↦ mfderiv I' I f y) (Pullback.contMDiff_mfderiv_hom f hf) ω

theorem compMFDeriv_def (f : K) (hf : ContMDiff I' I ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (ω : ContMDiffTwoForm I' ⊤ EB ((f : N → M) *ᵖ (TangentSpace I))) :
    ω.compMFDeriv f hf = compContinuousLinearMap (V := (f : N → M) *ᵖ (TangentSpace I))
      (V₂ := TangentSpace I') (fun y ↦ mfderiv I' I f y) (Pullback.contMDiff_mfderiv_hom f hf)
      ω :=
  (rfl)

/-- The induced form at `y` is `ω_y(df ·, df ·)`.

This is not `@[simp]`: after it rewrites, the vectors still lie in the fibre of `TN`, while
`mfderiv I' I f y` lands in `TangentSpace I (f y)` and not in `(f *ᵖ TangentSpace I) y`, so
`simp` cannot evaluate the composite on vectors. `simp` uses `compMFDeriv_apply_apply`
instead. -/
theorem compMFDeriv_apply (f : K) (hf : ContMDiff I' I ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (ω : ContMDiffTwoForm I' ⊤ EB ((f : N → M) *ᵖ (TangentSpace I))) (y : N) :
    ω.compMFDeriv f hf y = (ω y).compContinuousLinearMap (mfderiv I' I f y) := by
  rw [compMFDeriv_def]
  exact compContinuousLinearMap_apply _ _ ω y

/-- The induced form takes on `u`, `v` the value of `ω` on `df u`, `df v`. -/
theorem bilinFormAt_compMFDeriv (f : K) (hf : ContMDiff I' I ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (ω : ContMDiffTwoForm I' ⊤ EB ((f : N → M) *ᵖ (TangentSpace I))) (y : N)
    (u v : TangentSpace I' y) :
    (ω.compMFDeriv f hf).bilinFormAt y u v =
      ω.bilinFormAt y (mfderiv I' I f y u) (mfderiv I' I f y v) := by
  rw [compMFDeriv_def]
  exact bilinFormAt_compContinuousLinearMap _ _ ω y u v

/-- The induced form at `y` takes on `u`, `v` the value of `ω y` on `df u`, `df v`. -/
@[simp]
theorem compMFDeriv_apply_apply (f : K) (hf : ContMDiff I' I ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (ω : ContMDiffTwoForm I' ⊤ EB ((f : N → M) *ᵖ (TangentSpace I))) (y : N)
    (u v : TangentSpace I' y) :
    ω.compMFDeriv f hf y ![u, v] = ω y ![mfderiv I' I f y u, mfderiv I' I f y v] :=
  ((bilinFormAt_apply _ y u v).symm.trans (bilinFormAt_compMFDeriv f hf ω y u v)).trans
    (bilinFormAt_apply ω y _ _)

/-- The form induced by the zero form is zero. -/
@[simp]
theorem compMFDeriv_zero (f : K) (hf : ContMDiff I' I ((⊤ : ℕ∞) : WithTop ℕ∞) f) :
    (0 : ContMDiffTwoForm I' ⊤ EB ((f : N → M) *ᵖ (TangentSpace I))).compMFDeriv f hf = 0 := by
  rw [compMFDeriv_def]
  exact map_zero _

/-- The form induced by a sum is the sum of the induced forms. -/
@[simp]
theorem compMFDeriv_add (f : K) (hf : ContMDiff I' I ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (ω ω' : ContMDiffTwoForm I' ⊤ EB ((f : N → M) *ᵖ (TangentSpace I))) :
    (ω + ω').compMFDeriv f hf = ω.compMFDeriv f hf + ω'.compMFDeriv f hf := by
  simp only [compMFDeriv_def]
  exact map_add _ ω ω'

/-- The form induced by a multiple is the multiple of the induced form. -/
@[simp]
theorem compMFDeriv_smul (f : K) (hf : ContMDiff I' I ((⊤ : ℕ∞) : WithTop ℕ∞) f) (c : ℝ)
    (ω : ContMDiffTwoForm I' ⊤ EB ((f : N → M) *ᵖ (TangentSpace I))) :
    (c • ω).compMFDeriv f hf = c • ω.compMFDeriv f hf := by
  simp only [compMFDeriv_def]
  exact map_smul _ c ω

/-- The form induced by the negative of a form is the negative of the induced form. -/
@[simp]
theorem compMFDeriv_neg (f : K) (hf : ContMDiff I' I ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (ω : ContMDiffTwoForm I' ⊤ EB ((f : N → M) *ᵖ (TangentSpace I))) :
    (-ω).compMFDeriv f hf = -ω.compMFDeriv f hf := by
  simp only [compMFDeriv_def]
  exact map_neg _ ω

/-- The form induced by a difference is the difference of the induced forms. -/
@[simp]
theorem compMFDeriv_sub (f : K) (hf : ContMDiff I' I ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (ω ω' : ContMDiffTwoForm I' ⊤ EB ((f : N → M) *ᵖ (TangentSpace I))) :
    (ω - ω').compMFDeriv f hf = ω.compMFDeriv f hf - ω'.compMFDeriv f hf := by
  simp only [compMFDeriv_def]
  exact map_sub _ ω ω'

end CompMFDeriv

end ContMDiffTwoForm

end SymplecticGeometry.Bundle

end
