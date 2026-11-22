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

Let `V → M` be a real vector bundle and `f : N → M` a `C^n` map. A two-form `ω` on `V` pulls back
to the two-form `ω.pullback f` on the pull-back bundle `f *ᵖ V`, whose value at `y` is `ω (f y)`:
both are alternating maps on the same fibre `V (f y)`. This file defines the pull-back and shows
that it is compatible with the rest of the structure that `Symplectic/Basic.lean` and
`Symplectic/ComplexStructure/Basic.lean` put on two-forms.

## Main definitions and results

* `SymplecticGeometry.Bundle.ContMDiffTwoForm.pullback ω f`, with `pullback_apply`,
  `bilinFormAt_pullback`, `bilinFormAt_pullback_apply` and the linear map `pullbackLinearMap f`.
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
  the bundles are identified by the identity of each fibre.
* `IsSymplecticFrameOn.pullback` and `frameTransition_pullback`: a symplectic frame `Φ` over `U`
  pulls back to the symplectic frame `y ↦ Φ (f y)` over `f ⁻¹' U`, with transition maps those of
  `Φ` at `f y`.
* `compMFDeriv f hf ω`, with `compMFDeriv_apply`, `bilinFormAt_compMFDeriv`,
  `compMFDeriv_apply_apply`, and `compMFDeriv_zero`, `compMFDeriv_add`, `compMFDeriv_smul`,
  `compMFDeriv_neg`, `compMFDeriv_sub`: for a `C^∞` map `f : N → M` and a two-form `ω` on
  `f *ᵖ TM`, the two-form `σ(u, v) = ω(df u, df v)` on `TN`. It uses only the smoothness of `f`,
  not that `f` is an immersion.

## Implementation notes

The value of `ω.pullback f` is that of Tau Ceti's `ContMDiffSection.pullback ω f`, which is a
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
form on vectors with `bilinFormAt_apply_pullback` and `pullback_apply`, and its symplectic form
with `IsNondegenerate.symplecticFormAt_pullback_apply`.

`bilinFormAt_apply` does not fire on vectors typed in `V (f y)` for a form on `f *ᵖ V`: Mathlib's
`Bundle.Pullback` is a plain definition, so at the transparency `simp` uses, such a term is not
type-correct. `bilinFormAt_apply_pullback` states the evaluation with the vectors typed in
`V (f y)`, so that `simp` matches it as written. The same mismatch remains in
`pushforward_pullback_id` and `pushforward_pullback_comp`, where the identity of each fibre is
`ContinuousLinearEquiv.refl` of `V _` but is applied to vectors of a pull-back fibre, and no
lemma about the forms removes it: `simp` evaluates the forms, with `ContMDiffMap.id_apply` and
`ContMDiffMap.comp_apply` for the base points, and the identity is closed by `rfl`.

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

namespace ContMDiffTwoForm

/-! ### The pull-back of a two-form -/

/-- The pull-back of a two-form `ω` on `V` along a `C^n` map `f : N → M`: the two-form on the
pull-back bundle `f *ᵖ V` whose value at `y` is `ω (f y)`. -/
def pullback (ω : ContMDiffTwoForm I n F V) (f : C^n⟮I', N; I, M⟯) :
    ContMDiffTwoForm I' n F ((f : N → M) *ᵖ V) where
  toFun y := ω (f y)
  contMDiff_toFun :=
    (Pullback.contMDiff_continuousAlternatingMap_section_iff f f.contMDiff _).2
      (ω.contMDiff.comp f.contMDiff)

/-- The pull-back takes the value `ω (f y)` at `y`. -/
@[simp]
theorem pullback_apply (ω : ContMDiffTwoForm I n F V) (f : C^n⟮I', N; I, M⟯) (y : N) :
    ω.pullback f y = ω (f y) :=
  (rfl)

/-- A two-form `ω` on a pull-back bundle `f *ᵖ V` evaluates on vectors `v w : V (f y)` as
`ω y ![v, w]`. This is `bilinFormAt_apply` for vectors typed in `V (f y)` rather than in the
fibre `(f *ᵖ V) y`: the two types are the same, but `simp` does not see it. -/
@[simp]
theorem bilinFormAt_apply_pullback {K : Type*} [FunLike K N M] [ContinuousMapClass K N M] {f : K}
    (ω : ContMDiffTwoForm I' n F ((f : N → M) *ᵖ V)) (y : N) (v w : V (f y)) :
    ω.bilinFormAt y v w = ω y ![v, w] :=
  bilinFormAt_apply ω y v w

/-- The bilinear form of the pull-back at `y` is that of `ω` at `f y`.

This is not `@[simp]`: after it rewrites, the instances around the form still name the fibre
`(f *ᵖ V) y`, and `bilinFormAt_apply` no longer applies. On vectors, `simp` uses
`bilinFormAt_apply_pullback` and `pullback_apply` instead. -/
theorem bilinFormAt_pullback (ω : ContMDiffTwoForm I n F V) (f : C^n⟮I', N; I, M⟯) (y : N) :
    (ω.pullback f).bilinFormAt y = ω.bilinFormAt (f y) := by
  rw [bilinFormAt_def, bilinFormAt_def, pullback_apply]
  -- The two sides differ only in the fibre type, `(f *ᵖ V) y` against `V (f y)`.
  rfl

/-- The bilinear form of the pull-back at `y` evaluates as `ω (f y)`. This is not `@[simp]`:
`simp` proves it with `bilinFormAt_apply_pullback` and `pullback_apply`. -/
theorem bilinFormAt_pullback_apply (ω : ContMDiffTwoForm I n F V) (f : C^n⟮I', N; I, M⟯) (y : N)
    (v w : V (f y)) : (ω.pullback f).bilinFormAt y v w = ω (f y) ![v, w] :=
  ((ω.pullback f).bilinFormAt_apply y v w).trans (congrArg (· ![v, w]) (pullback_apply ω f y))

/-- The pull-back of the zero form is zero. -/
@[simp]
theorem pullback_zero (f : C^n⟮I', N; I, M⟯) : (0 : ContMDiffTwoForm I n F V).pullback f = 0 := by
  ext y
  exact rfl

/-- The pull-back of a sum is the sum of the pull-backs. -/
@[simp]
theorem pullback_add (ω ω' : ContMDiffTwoForm I n F V) (f : C^n⟮I', N; I, M⟯) :
    (ω + ω').pullback f = ω.pullback f + ω'.pullback f := by
  ext y
  exact rfl

/-- The pull-back of a multiple is the multiple of the pull-back. -/
@[simp]
theorem pullback_smul (c : ℝ) (ω : ContMDiffTwoForm I n F V) (f : C^n⟮I', N; I, M⟯) :
    (c • ω).pullback f = c • ω.pullback f := by
  ext y
  exact rfl

variable (I F V n) in
/-- The pull-back of two-forms along a `C^n` map `f`, as a linear map. -/
def pullbackLinearMap (f : C^n⟮I', N; I, M⟯) :
    ContMDiffTwoForm I n F V →ₗ[ℝ] ContMDiffTwoForm I' n F ((f : N → M) *ᵖ V) where
  toFun ω := ω.pullback f
  map_add' ω ω' := pullback_add ω ω' f
  map_smul' c ω := pullback_smul c ω f

/-- The linear map `pullbackLinearMap f` sends `ω` to its pull-back along `f`. -/
@[simp]
theorem pullbackLinearMap_apply (f : C^n⟮I', N; I, M⟯) (ω : ContMDiffTwoForm I n F V) :
    pullbackLinearMap I F V n f ω = ω.pullback f :=
  (rfl)

/-- The pull-back of the negative of a two-form is the negative of its pull-back. -/
@[simp]
theorem pullback_neg (ω : ContMDiffTwoForm I n F V) (f : C^n⟮I', N; I, M⟯) :
    (-ω).pullback f = -ω.pullback f :=
  map_neg (pullbackLinearMap I F V n f) ω

/-- The pull-back of a difference is the difference of the pull-backs. -/
@[simp]
theorem pullback_sub (ω ω' : ContMDiffTwoForm I n F V) (f : C^n⟮I', N; I, M⟯) :
    (ω - ω').pullback f = ω.pullback f - ω'.pullback f :=
  map_sub (pullbackLinearMap I F V n f) ω ω'

/-! ### Nondegeneracy -/

variable {ω : ContMDiffTwoForm I n F V}

/-- The pull-back of a nondegenerate two-form is nondegenerate. -/
theorem IsNondegenerate.pullback (h : ω.IsNondegenerate) (f : C^n⟮I', N; I, M⟯) :
    (ω.pullback f).IsNondegenerate :=
  isNondegenerate_def.2 fun y ↦ by
    rw [bilinFormAt_pullback]
    exact h.nondegenerate_bilinFormAt (f y)

/-- The symplectic form of the pull-back on the fibre over `y` is that of `ω` over `f y`.

This is not `@[simp]`, for the reason given at `bilinFormAt_pullback`. `simp` uses
`IsNondegenerate.symplecticFormAt_pullback_apply` instead. -/
theorem IsNondegenerate.symplecticFormAt_pullback (h : ω.IsNondegenerate) (f : C^n⟮I', N; I, M⟯)
    (y : N) : (h.pullback f).symplecticFormAt y = h.symplecticFormAt (f y) :=
  TauCeti.SymplecticForm.toBilinForm_injective <| by
    rw [IsNondegenerate.toBilinForm_symplecticFormAt, IsNondegenerate.toBilinForm_symplecticFormAt,
      bilinFormAt_pullback]

/-- The symplectic form of the pull-back on the fibre over `y` evaluates as `ω (f y)`. The
hypothesis is the nondegeneracy of the pull-back, rather than of `ω`, so that `simp` can match
it against any proof of it, such as `h.pullback f`. -/
@[simp]
theorem IsNondegenerate.symplecticFormAt_pullback_apply {f : C^n⟮I', N; I, M⟯}
    (h : (ω.pullback f).IsNondegenerate) (y : N) (v w : V (f y)) :
    h.symplecticFormAt y v w = ω (f y) ![v, w] :=
  (h.symplecticFormAt_apply y v w).trans
    (congrArg (· ![v, w]) (pullback_apply ω f y))

/-! ### Tame and compatible pairs -/

variable {J : ContMDiffComplexStructure I n F V}

/-- If `ω` tames `J`, the pull-back of `ω` tames the pull-back of `J`. -/
theorem Tames.pullback (h : ω.Tames J) (f : C^n⟮I', N; I, M⟯) :
    (ω.pullback f).Tames (J.pullback f f.contMDiff) :=
  tames_def.2 fun y v hv ↦ by
    simp only [bilinFormAt_pullback, ContMDiffComplexStructure.pullback_toEndomorphism]
    exact tames_def.1 h (f y) v hv

/-- If `ω` is invariant under `J`, the pull-back of `ω` is invariant under the pull-back of `J`. -/
theorem Invariant.pullback (h : ω.Invariant J) (f : C^n⟮I', N; I, M⟯) :
    (ω.pullback f).Invariant (J.pullback f f.contMDiff) :=
  invariant_def.2 fun y v w ↦ by
    simp only [bilinFormAt_pullback, ContMDiffComplexStructure.pullback_toEndomorphism]
    exact invariant_def.1 h (f y) v w

/-- If `ω` is compatible with `J`, the pull-back of `ω` is compatible with the pull-back of `J`. -/
theorem Compatible.pullback (h : ω.Compatible J) (f : C^n⟮I', N; I, M⟯) :
    (ω.pullback f).Compatible (J.pullback f f.contMDiff) :=
  ⟨h.invariant.pullback f, h.tames.pullback f⟩

/-! ### Symplectic frames -/

/-- A symplectic frame `Φ` of `ω` over `U`, modelled on `(W, σ)`, pulls back along `f` to the
symplectic frame `y ↦ Φ (f y)` of the pull-back of `ω` over `f ⁻¹' U`. -/
theorem IsSymplecticFrameOn.pullback {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {σ : TauCeti.SymplecticForm W} {U : Set M} {Φ : ∀ x, W ≃L[ℝ] V x}
    (h : ω.IsSymplecticFrameOn σ U Φ) (f : C^n⟮I', N; I, M⟯) :
    (ω.pullback f).IsSymplecticFrameOn σ (f ⁻¹' U) fun y ↦ Φ (f y) where
  contMDiffOn p hp := by
    rw [Pullback.contMDiffWithinAt_iff f (f.contMDiff _)]
    exact ⟨contMDiffWithinAt_fst, h.contMDiffOn.comp (f.contMDiff.prodMap contMDiff_id).contMDiffOn
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
theorem pullback_pushforward (ω : ContMDiffTwoForm I n F₁ V₁) (f : C^n⟮I', N; I, M⟯) :
    (pushforward Φ hΦ ω).pullback f =
      pushforward (V₁ := (f : N → M) *ᵖ V₁) (V₂ := (f : N → M) *ᵖ V₂) (fun y ↦ Φ (f y))
        (Pullback.contMDiff_fiberwise (fun x v ↦ Φ x v) hΦ f f.contMDiff) (ω.pullback f) := by
  refine ContMDiffSection.ext fun y ↦
    ((pullback_apply _ f y).trans (pushforward_apply Φ hΦ ω (f y))).trans ?_
  -- `ω.pullback f y` is `ω (f y)`, read in the fibre `(f *ᵖ V₁) y`.
  exact (pushforward_apply (V₁ := (f : N → M) *ᵖ V₁) (V₂ := (f : N → M) *ᵖ V₂) (fun y ↦ Φ (f y)) _
    (ω.pullback f) y).symm

end Pushforward

variable [FiniteDimensional ℝ F]

/-- The pull-back along the identity, moved to `V` by the identity of each fibre, is the form
itself. -/
theorem pushforward_pullback_id (ω : ContMDiffTwoForm I n F V) :
    pushforward (V₁ := ((ContMDiffMap.id : C^n⟮I, M; I, M⟯) : M → M) *ᵖ V) (V₂ := V)
      (fun x ↦ ContinuousLinearEquiv.refl ℝ (V x))
      ((Pullback.idDiffeomorph (F := F) (I := I) (m := n) (n := n) V).contMDiff.congr
        fun p ↦ (Pullback.idDiffeomorph_apply p).symm)
      (ω.pullback ContMDiffMap.id) = ω := by
  refine (pushforward_eq_iff _ _).2 fun x v w ↦ ?_
  simp only [bilinFormAt_apply, pullback_apply, ContMDiffMap.id_apply]
  -- Only the identity of each fibre is left. It is stated as `ContinuousLinearEquiv.refl` of
  -- `V _` but applied to vectors of a pull-back fibre, so `ContinuousLinearEquiv.coe_refl'`
  -- does not match it.
  rfl

variable {EP HP P : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
  {I'' : ModelWithCorners ℝ EP HP} [TopologicalSpace P] [ChartedSpace HP P]

/-- The pull-back along a composite `g ∘ f`, moved to `f *ᵖ (g *ᵖ V)` by the identity of each
fibre, is the pull-back along `g` and then along `f`. -/
theorem pushforward_pullback_comp (ω : ContMDiffTwoForm I n F V) (g : C^n⟮I', N; I, M⟯)
    (f : C^n⟮I'', P; I', N⟯) :
    pushforward (V₁ := ((g.comp f : C^n⟮I'', P; I, M⟯) : P → M) *ᵖ V)
      (V₂ := (f : P → N) *ᵖ ((g : N → M) *ᵖ V))
      (fun z ↦ ContinuousLinearEquiv.refl ℝ (V (g (f z))))
      ((Pullback.compDiffeomorph (F := F) (n := n) V g f).contMDiff.congr
        fun p ↦ (Pullback.compDiffeomorph_apply g f p).symm)
      (ω.pullback (g.comp f)) = (ω.pullback g).pullback f := by
  refine (pushforward_eq_iff _ _).2 fun x v w ↦ ?_
  simp only [bilinFormAt_apply, pullback_apply, ContMDiffMap.comp_apply]
  -- Only the identity of each fibre is left. It is stated as `ContinuousLinearEquiv.refl` of
  -- `V _` but applied to vectors of a pull-back fibre, so `ContinuousLinearEquiv.coe_refl'`
  -- does not match it.
  rfl

/-! ### The form induced on the tangent bundle along a smooth map -/

section CompMFDeriv

variable [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M] [IsManifold I' ((⊤ : ℕ∞) : WithTop ℕ∞) N]
  [FiniteDimensional ℝ EN] {K : Type*} [FunLike K N M] [ContinuousMapClass K N M]

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
