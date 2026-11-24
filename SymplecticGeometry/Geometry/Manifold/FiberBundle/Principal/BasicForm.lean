/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.LieDeriv
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Descent
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import TauCeti.Geometry.Manifold.FiberBundle.Principal.FundamentalVectorField
import TauCeti.Geometry.Lie.Exponential.Derivative.Basic
import TauCeti.Geometry.Manifold.DifferentialForm.Flow
import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
import TauCeti.Geometry.Manifold.VectorField.Prod
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.LieDeriv
import SymplecticGeometry.Geometry.Manifold.VectorField.Prod

/-!
# Basic forms on smooth principal bundles

Let `P` be a smooth principal `G`-bundle over `B`, with charted total space
`TauCeti.ManifoldTotalSpace G P` and projection `π`. The projection is invariant under the right
action of `G`, so a form pulled back from `B` is invariant. Conversely, a form on the total space
that is invariant under the action and vanishes as soon as one of its arguments is vertical is
basic for `π` (`TauCeti.RoughForm.IsBasic`), hence a pull-back from `B` when Tau Ceti's descent
applies: the points of a fibre are related by the action, through the division map
`TauCeti.PrincipalBundle.division`.

## Main results

* `TauCeti.PrincipalBundle.proj_comp_op_smul`: the projection is invariant under the action.
* `TauCeti.PrincipalBundle.exists_op_smul_eq_of_proj_eq`: two points of one fibre differ by the
  action.
* `TauCeti.PrincipalBundle.mpullback_op_smul_mpullback_proj`: forms pulled back from the base are
  invariant under the action.
* `TauCeti.PrincipalBundle.isBasic_of_mpullback_op_smul`: an invariant form that vanishes on
  vertical vectors is basic for the projection. It is Tau Ceti's
  `TauCeti.RoughForm.isBasic_of_mpullback_eq` for the right translations of a principal bundle.
* `TauCeti.PrincipalBundle.mlieDerivForm_rightFundamentalVectorField_eq_zero`: an invariant form
  has vanishing Lie derivative along every fundamental vector field.
* `TauCeti.PrincipalBundle.mextDeriv_apply_rightFundamentalVectorField_prod`,
  `TauCeti.PrincipalBundle.interior_mextDeriv_rightFundamentalVectorField_prod`: on a product
  `P × N` with a manifold `N` that may have boundary, a one-form `A` invariant under the action
  on the first factor satisfies `ι_{(ξ_P, 0)} dA = -d (A (ξ_P, 0))`.
* `TauCeti.PrincipalBundle.mlieDerivForm_rightFundamentalVectorField_prod_eq_zero`: such a form
  has vanishing Lie derivative along `(ξ_P, 0)`.

## Implementation notes

The proof of `mlieDerivForm_rightFundamentalVectorField_eq_zero` adapts that of Tau Ceti's
`TauCeti.mlieDerivForm_fundamentalVectorField_eq_zero`, for left actions of a Lie group, to the
right action on a principal bundle: the form is constant along the flow `x ↦ x • exp (t ξ)` of
the fundamental vector field of `ξ`
(`TauCeti.PrincipalBundle.isMIntegralCurve_op_mulInvariantExp_smul`), and its Lie derivative is
the velocity at `0` of its pull-backs along this flow (`TauCeti.hasDerivAt_mpullback_of_eq_id`).

That argument needs a boundaryless model, which a product `P × N` does not have when `N` has
boundary, so the identity on `P × N` is proved one component of the tangent vector at a time.
On vectors tangent to a slice `P × {n}`, it is Cartan's formula
`TauCeti.mlieDerivForm_apply_eq_mextDeriv_add` on `P` for the invariant slice of `A`, by
naturality of `d` (`TauCeti.mpullback_mextDeriv_at`). On vectors tangent to `N`, pull `A` back
along `(s, m) ↦ (x • exp (s ξ), m)` to `ℝ × N`: by invariance all its slices `{s} × N` agree,
so its Lie derivative along `∂ₛ` vanishes on vectors tangent to `N`
(`TauCeti.mpullback_prodMk_mlieDerivForm_prodVectorField_zero_eq_zero`, which needs no
boundaryless model), and Cartan's formula on `ℝ × N` gives the identity. The vanishing of the
Lie derivative along `(ξ_P, 0)` and the identity of forms then follow from the pointwise identity
by Cartan's formula on `P × N` (`TauCeti.SmoothForm.mlieDerivForm_eq_interior_mextDeriv_add`).

## References

* S. Kobayashi and K. Nomizu, *Foundations of Differential Geometry*, Vol. I, Interscience, 1963,
  Chapter II, §5 (tensorial forms of type `ad` on a principal bundle; basic forms are the
  pull-backs of forms on the base).
* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Theorem 14.35 (Cartan's formula for the Lie derivative of forms).
-/

public section

noncomputable section

open Bundle Manifold MulOpposite
open scoped Manifold ContDiff

namespace TauCeti.PrincipalBundle

variable {B G : Type*}
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners ℝ EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  {EG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG] {HG : Type*} [TopologicalSpace HG]
  {IG : ModelWithCorners ℝ EG HG} [Group G] [TopologicalSpace G] [ChartedSpace HG G]
  {P : B → Type*} [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle G P] [∀ b, MulAction Gᵐᵒᵖ (P b)]

omit [TopologicalSpace B] [∀ b, TopologicalSpace (P b)] [FiberBundle G P] [TopologicalSpace G] in
/-- The projection of the charted total space of a principal bundle is invariant under the right
action. -/
@[simp]
theorem proj_comp_op_smul (g : G) :
    (fun y : ManifoldTotalSpace G P ↦ ((ManifoldTotalSpace.homeomorph G P).symm y).proj) ∘
      (fun x ↦ op g • x) =
      fun y ↦ ((ManifoldTotalSpace.homeomorph G P).symm y).proj := by
  funext x
  simp [ManifoldTotalSpace.homeomorph_symm_smul]

section Basic

variable [IsManifold IB ∞ B] [ContMDiffMul IG ∞ G] [ContMDiffFiberBundle ∞ G P IB IG]
  [PrincipalBundle G P]

omit [IsManifold IB ∞ B] [ContMDiffMul IG ∞ G] [ContMDiffFiberBundle ∞ G P IB IG] in
/-- Two points of the charted total space of a principal bundle with the same projection differ by
the right action of an element of the structure group. -/
theorem exists_op_smul_eq_of_proj_eq {x y : ManifoldTotalSpace G P}
    (hxy : ((ManifoldTotalSpace.homeomorph G P).symm x).proj =
      ((ManifoldTotalSpace.homeomorph G P).symm y).proj) :
    ∃ g : G, op g • y = x := by
  obtain ⟨⟨b, p⟩, rfl⟩ := (ManifoldTotalSpace.homeomorph G P).surjective x
  obtain ⟨⟨b', q⟩, rfl⟩ := (ManifoldTotalSpace.homeomorph G P).surjective y
  simp only [Homeomorph.symm_apply_apply] at hxy
  subst hxy
  exact ⟨division G q p, by rw [ManifoldTotalSpace.smul_homeomorph, smul_division]⟩

/-- A form pulled back from the base of a smooth principal bundle is invariant under the right
action. -/
@[simp]
theorem mpullback_op_smul_mpullback_proj {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {k : ℕ} (g : G) (a : SmoothForm IB B F k) :
    SmoothForm.mpullback (fun x : ManifoldTotalSpace G P ↦ op g • x)
      (contMDiff_const_smul (op g)) (SmoothForm.mpullback
        (fun y : ManifoldTotalSpace G P ↦ ((ManifoldTotalSpace.homeomorph G P).symm y).proj)
        (ManifoldTotalSpace.contMDiff_proj ∞ G P IB IG) a) =
      SmoothForm.mpullback
        (fun y : ManifoldTotalSpace G P ↦ ((ManifoldTotalSpace.homeomorph G P).symm y).proj)
        (ManifoldTotalSpace.contMDiff_proj ∞ G P IB IG) a := by
  simp only [SmoothForm.mpullback_mpullback, proj_comp_op_smul]

/-- **Invariant forms that vanish on vertical vectors are basic.** On a smooth principal bundle, a
smooth form that is invariant under the right action of `G` and vanishes as soon as one of its
arguments is vertical, that is, in the kernel of the derivative of the projection, is basic for
the projection. -/
theorem isBasic_of_mpullback_op_smul {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {k : ℕ} {β : SmoothForm (IB.prod IG) (ManifoldTotalSpace G P) F k}
    (hβ : ∀ g : G, SmoothForm.mpullback (fun x : ManifoldTotalSpace G P ↦ op g • x)
      (contMDiff_const_smul (op g)) β = β)
    (hvert : ∀ x (v : Fin k → TangentSpace (IB.prod IG) x) j,
      mfderiv (IB.prod IG) IB (fun y : ManifoldTotalSpace G P ↦
        ((ManifoldTotalSpace.homeomorph G P).symm y).proj) x (v j) = 0 → β.val x v = 0) :
    RoughForm.IsBasic (V := F) IB
      (fun y : ManifoldTotalSpace G P ↦ ((ManifoldTotalSpace.homeomorph G P).symm y).proj)
      β.val := by
  refine RoughForm.isBasic_of_mpullback_eq
    (σ := fun (g : G) (x : ManifoldTotalSpace G P) ↦ op g • x)
    ((ManifoldTotalSpace.contMDiff_proj ∞ G P IB IG).mdifferentiable (by simp))
    (fun g ↦ (contMDiff_const_smul (I := IB.prod IG) (n := ∞) (op g)).mdifferentiable (by simp))
    proj_comp_op_smul (fun x y hxy ↦ Or.inr (exists_op_smul_eq_of_proj_eq hxy.symm)) hvert
    fun g ↦ ?_
  rw [← SmoothForm.coe_mpullback _ (contMDiff_const_smul (op g)), hβ]

end Basic

section LieDeriv

variable [IsManifold IB ∞ B] [CompleteSpace EG] [LieGroup IG ∞ G]
  [ContMDiffFiberBundle ∞ G P IB IG] [PrincipalBundle G P]

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

/-- **Invariant forms have vanishing Lie derivative along fundamental vector fields.** On a smooth
principal bundle whose base and structure group are modelled without boundary, a smooth form that
is invariant under the right action has vanishing Lie derivative along the fundamental vector
field of every `ξ` in the Lie algebra. This is the right-action counterpart of Tau Ceti's
`TauCeti.mlieDerivForm_fundamentalVectorField_eq_zero`. -/
theorem mlieDerivForm_rightFundamentalVectorField_eq_zero [IB.Boundaryless] [IG.Boundaryless]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}
    {β : SmoothForm (IB.prod IG) (ManifoldTotalSpace G P) F k}
    (hβ : ∀ g : G, SmoothForm.mpullback (fun x : ManifoldTotalSpace G P ↦ op g • x)
      (contMDiff_const_smul (op g)) β = β)
    (ξ : GroupLieAlgebra IG G) :
    mlieDerivForm (rightFundamentalVectorField (IB.prod IG) ξ) β.val = 0 := by
  have : T2Space G := IG.t2Space_of_lieGroup ∞
  funext x
  -- The flow of the field is `x ↦ x • exp (t ξ)`, along which `β` is constant.
  have hψ : ContMDiff (𝓘(ℝ).prod (IB.prod IG)) (IB.prod IG) ∞
      (fun p : ℝ × ManifoldTotalSpace G P ↦ op (mulInvariantExp (p.1 • ξ)) • p.2) :=
    contMDiff_op_smul.comp
      (contMDiff_snd.prodMk ((contMDiff_mulInvariantExp_smul ξ).comp contMDiff_fst))
  have h := hasDerivAt_mpullback_of_eq_id (α := β.val)
    (V := rightFundamentalVectorField (IB.prod IG) ξ)
    (ψ := fun (t : ℝ) (y : ManifoldTotalSpace G P) ↦ op (mulInvariantExp (t • ξ)) • y) (t := 0) x
    (.of_forall fun y ↦ by simp [mulInvariantExp_zero]) ((hψ (0, x)).of_le (by simp))
    (.of_forall fun y ↦ isMIntegralCurve_op_mulInvariantExp_smul ξ y 0)
    (β.mdifferentiable x)
  have hconst : (fun t : ℝ ↦ TauCeti.mpullback (IB.prod IG) (IB.prod IG)
      (fun y : ManifoldTotalSpace G P ↦ op (mulInvariantExp (t • ξ)) • y) β.val x) =
        fun _ ↦ β.val x := by
    funext t
    rw [← SmoothForm.coe_mpullback _ (contMDiff_const_smul (op (mulInvariantExp (t • ξ)))), hβ]
  rw [hconst] at h
  exact h.unique (hasDerivAt_const 0 _)

/-! ### Invariant one-forms on a product `P × N` -/

section Prod

variable [IB.Boundaryless] [IG.Boundaryless]
  {EN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN] [CompleteSpace EN]
  {HN : Type*} [TopologicalSpace HN] {IN : ModelWithCorners ℝ EN HN}
  {N : Type*} [TopologicalSpace N] [ChartedSpace HN N] [IsManifold IN ∞ N]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {A : SmoothForm ((IB.prod IG).prod IN) (ManifoldTotalSpace G P × N) F 1}

omit [CompleteSpace EG] [IB.Boundaryless] [IG.Boundaryless] [CompleteSpace EN] in
/-- The field `(ξ_P, 0)` on `P × N` is differentiable. -/
theorem mdifferentiable_rightFundamentalVectorField_prod (ξ : GroupLieAlgebra IG G) :
    MDifferentiable ((IB.prod IG).prod IN) ((IB.prod IG).prod IN).tangent
      (fun x : ManifoldTotalSpace G P × N ↦
        (⟨x, (rightFundamentalVectorField (IB.prod IG) ξ x.1, (0 : EN))⟩ :
          TangentBundle ((IB.prod IG).prod IN) (ManifoldTotalSpace G P × N))) := by
  intro x
  have hX := (contMDiff_rightFundamentalVectorField (IB := IB) (n := ∞) (m := 1) (by simp)
    ξ).mdifferentiable one_ne_zero x.1
  have h0 : MDifferentiableAt IN IN.tangent
      (fun y ↦ (⟨y, (0 : Π y : N, TangentSpace IN y) y⟩ : TangentBundle IN N)) x.2 :=
    (contMDiff_zeroSection ℝ (TangentSpace IN)).mdifferentiableAt one_ne_zero
  have h := Manifold.mdifferentiableAt_prodVectorField hX h0
  convert h using 3 with y
  rw [Manifold.prodVectorField_apply]
  rfl

omit [IsManifold IB ∞ B] [CompleteSpace EG] [ContMDiffFiberBundle ∞ G P IB IG] [IB.Boundaryless]
  [IG.Boundaryless] [CompleteSpace EN] [IsManifold IN ∞ N] in
/-- The right action of `G` on the first factor of `P × N` is smooth. -/
theorem contMDiff_op_smul_prod (g : G) :
    ContMDiff ((IB.prod IG).prod IN) ((IB.prod IG).prod IN) ∞
      (fun x : ManifoldTotalSpace G P × N ↦ (op g • x.1, x.2)) :=
  ((contMDiff_const_smul (op g)).comp contMDiff_fst).prodMk contMDiff_snd

omit [CompleteSpace EG] [IB.Boundaryless] [IG.Boundaryless] [CompleteSpace EN] in
/-- The evaluation `A(ξ_P, 0)` of a smooth one-form on `P × N` is differentiable. -/
theorem mdifferentiable_apply_rightFundamentalVectorField_prod (ξ : GroupLieAlgebra IG G) :
    MDifferentiable ((IB.prod IG).prod IN) 𝓘(ℝ, F) (fun q : ManifoldTotalSpace G P × N ↦
      A.val q ![(rightFundamentalVectorField (IB.prod IG) ξ q.1, (0 : EN))]) := by
  intro q
  have h := SmoothForm.mdifferentiableAt_apply_vectorField A
    (V := ![fun q : ManifoldTotalSpace G P × N ↦
      (((rightFundamentalVectorField (IB.prod IG) ξ q.1 : EB × EG), (0 : EN)) :
        TangentSpace ((IB.prod IG).prod IN) q)]) (x := q)
    (fun i ↦ by fin_cases i; exact mdifferentiable_rightFundamentalVectorField_prod ξ q)
  convert h using 3 with y
  ext i
  fin_cases i
  rfl

variable (hA : ∀ g : G,
  SmoothForm.mpullback (fun x : ManifoldTotalSpace G P × N ↦ (op g • x.1, x.2))
    (contMDiff_op_smul_prod g) A = A)
include hA

omit [CompleteSpace EN] in
/-- The identity of `mextDeriv_apply_rightFundamentalVectorField_prod` on vectors tangent to a
slice `P × {n}`: the slice of `A` is invariant on the boundaryless `P`. -/
private theorem mextDeriv_apply_rightFundamentalVectorField_prod_inl (ξ : GroupLieAlgebra IG G)
    (x : ManifoldTotalSpace G P) (n : N) (u : TangentSpace (IB.prod IG) x) :
    mextDeriv A.val (x, n)
        ![(rightFundamentalVectorField (IB.prod IG) ξ x, (0 : EN)), (u, (0 : EN))] =
      -mvfderiv ((IB.prod IG).prod IN) (fun q : ManifoldTotalSpace G P × N ↦
        A.val q ![(rightFundamentalVectorField (IB.prod IG) ξ q.1, (0 : EN))]) (x, n)
          (u, (0 : EN)) := by
  have hι : ContMDiff (IB.prod IG) ((IB.prod IG).prod IN) ∞
      (fun y : ManifoldTotalSpace G P ↦ (y, n)) := contMDiff_id.prodMk contMDiff_const
  have hα (g : G) : SmoothForm.mpullback (fun y : ManifoldTotalSpace G P ↦ op g • y)
      (contMDiff_const_smul (op g)) (SmoothForm.mpullback _ hι A) =
        SmoothForm.mpullback _ hι A := by
    rw [SmoothForm.mpullback_mpullback_of_comp_eq _ _ hι (contMDiff_op_smul_prod g) (by rfl), hA]
  have hL := mlieDerivForm_rightFundamentalVectorField_eq_zero hα ξ
  have hX := (contMDiff_rightFundamentalVectorField (IB := IB) (n := ∞) (m := 1) (by simp)
    ξ).mdifferentiable one_ne_zero x
  have hC := mlieDerivForm_apply_eq_mextDeriv_add
    (f := (fun q : ManifoldTotalSpace G P × N ↦
        A.val q ![(rightFundamentalVectorField (IB.prod IG) ξ q.1, (0 : EN))]) ∘
      fun y : ManifoldTotalSpace G P ↦ (y, n))
    (fun y ↦ ?_) ((SmoothForm.mpullback _ hι A).mdifferentiableAt x) hX u
  · rw [hL, SmoothForm.coe_mpullback, ← mpullback_mextDeriv_at (hι.contMDiffAt.of_le (by simp))
      ((A.contMDiff _).of_le (by simp)), mpullback_apply_pair,
      mvfderiv_comp_apply x (mdifferentiable_apply_rightFundamentalVectorField_prod ξ _)
        (hι.mdifferentiableAt (by simp)), mfderiv_prod_left] at hC
    simp only [Pi.zero_apply, ContinuousAlternatingMap.coe_zero] at hC
    rw [eq_neg_iff_add_eq_zero]
    exact hC.symm
  · rw [SmoothForm.mpullback_apply, mfderiv_prod_left]
    simp only [Function.comp_apply]
    congr 1
    ext i
    fin_cases i
    rfl

omit [IB.Boundaryless] in
/-- The identity of `mextDeriv_apply_rightFundamentalVectorField_prod` on vectors tangent to `N`:
pulled back along `(s, m) ↦ (x • exp (s ξ), m)`, the form `A` has the same slice `{s} × N` for
every `s`, so its Lie derivative along `∂ₛ` vanishes on vectors tangent to `N`, and Cartan's
formula on `ℝ × N` gives the identity. -/
private theorem mextDeriv_apply_rightFundamentalVectorField_prod_inr (ξ : GroupLieAlgebra IG G)
    (x : ManifoldTotalSpace G P) (n : N) (v : EN) :
    mextDeriv A.val (x, n)
        ![(rightFundamentalVectorField (IB.prod IG) ξ x, (0 : EN)), ((0 : EB × EG), v)] =
      -mvfderiv ((IB.prod IG).prod IN) (fun q : ManifoldTotalSpace G P × N ↦
        A.val q ![(rightFundamentalVectorField (IB.prod IG) ξ q.1, (0 : EN))]) (x, n)
          ((0 : EB × EG), v) := by
  have : T2Space G := IG.t2Space_of_lieGroup ∞
  set γ : ℝ → ManifoldTotalSpace G P := fun s ↦ op (mulInvariantExp (s • ξ)) • x with hγdef
  have hγs : ContMDiff 𝓘(ℝ) (IB.prod IG) ∞ γ :=
    contMDiff_op_smul.comp (contMDiff_const.prodMk (contMDiff_mulInvariantExp_smul ξ))
  have hφ : ContMDiff (𝓘(ℝ).prod IN) ((IB.prod IG).prod IN) ∞
      (fun q : ℝ × N ↦ (γ q.1, q.2)) :=
    (hγs.comp contMDiff_fst).prodMk contMDiff_snd
  have hj : ContMDiff IN ((IB.prod IG).prod IN) ∞ (fun m : N ↦ (x, m)) :=
    contMDiff_const.prodMk contMDiff_id
  -- The slices of the pull-back of `A` are all the pull-back of `A` along `m ↦ (x, m)`.
  have hslice (s : ℝ) : SmoothForm.mpullback (Prod.mk s : N → ℝ × N)
      (contMDiff_const.prodMk contMDiff_id) (SmoothForm.mpullback _ hφ A) =
        SmoothForm.mpullback _ hj A := by
    rw [SmoothForm.mpullback_mpullback_of_comp_eq _ _ hj
        (contMDiff_op_smul_prod (mulInvariantExp (s • ξ))) (by rfl), hA]
  have hT : MDifferentiableAt 𝓘(ℝ) 𝓘(ℝ).tangent
      (fun s ↦ (⟨s, constVectorField (1 : ℝ) s⟩ : TangentBundle 𝓘(ℝ) ℝ)) 0 :=
    (contMDiff_constVectorField (1 : ℝ) (n := 1)).mdifferentiableAt one_ne_zero
  have hV := mpullback_prodMk_mlieDerivForm_prodVectorField_zero_eq_zero (t := 0) (x := n)
    ((SmoothForm.mpullback _ hφ A).mdifferentiableAt _) hT fun s ↦ by
      have h := congrArg Subtype.val ((hslice s).trans (hslice 0).symm)
      rwa [SmoothForm.coe_mpullback (Prod.mk s : N → ℝ × N),
        SmoothForm.coe_mpullback (Prod.mk (0 : ℝ) : N → ℝ × N)] at h
  -- The derivative of `(s, m) ↦ (γ s, m)`, from the integral curves `γ` of `ξ_P`.
  have hφ' (q : ℝ × N) : HasMFDerivAt (𝓘(ℝ).prod IN) ((IB.prod IG).prod IN)
      (fun q : ℝ × N ↦ (γ q.1, q.2)) q
      ((((1 : ℝ →L[ℝ] ℝ).smulRight (rightFundamentalVectorField (IB.prod IG) ξ (γ q.1))).comp
        (ContinuousLinearMap.fst ℝ ℝ (TangentSpace IN q.2))).prod
          (ContinuousLinearMap.snd ℝ ℝ (TangentSpace IN q.2))) :=
    ((isMIntegralCurve_op_mulInvariantExp_smul (IB := IB) ξ x q.1).comp q
      (hasMFDerivAt_fst q)).prodMk (hasMFDerivAt_snd q)
  have hW (q : ℝ × N) : Manifold.prodVectorField (constVectorField (1 : ℝ))
      (0 : Π y : N, TangentSpace IN y) q = ((1 : ℝ), (0 : EN)) :=
    Manifold.prodVectorField_constVectorField_zero_apply 1 q
  have hWd : MDifferentiableAt (𝓘(ℝ).prod IN) (𝓘(ℝ).prod IN).tangent
      (fun q ↦ (⟨q, Manifold.prodVectorField (constVectorField (1 : ℝ))
        (0 : Π y : N, TangentSpace IN y) q⟩ : TangentBundle (𝓘(ℝ).prod IN) (ℝ × N))) (0, n) :=
    Manifold.mdifferentiableAt_prodVectorField hT
      ((contMDiff_zeroSection ℝ (TangentSpace IN)).mdifferentiableAt one_ne_zero)
  -- The vector `(0, v)` at `(0, n)` is the image of `v` under the differential of
  -- `m ↦ (0, m)`; written so, it is a tangent vector of `ℝ × N` at `(0, n)`.
  have hw : mfderiv IN (𝓘(ℝ).prod IN) (Prod.mk (0 : ℝ)) n v = ((0 : ℝ), v) := by
    rw [mfderiv_prod_right]
    -- The zero of `TangentSpace 𝓘(ℝ) 0` is that of `ℝ` under another name of the instance.
    exact ContinuousLinearMap.inr_apply v
  -- Cartan's formula on `ℝ × N` for the pulled-back form, along `∂ₛ`.
  have hC := mlieDerivForm_apply_eq_mextDeriv_add
    (f := (fun q : ManifoldTotalSpace G P × N ↦
        A.val q ![(rightFundamentalVectorField (IB.prod IG) ξ q.1, (0 : EN))]) ∘
      fun q : ℝ × N ↦ (γ q.1, q.2))
    (fun q ↦ ?_) ((SmoothForm.mpullback _ hφ A).mdifferentiableAt (0, n)) hWd
    (mfderiv IN (𝓘(ℝ).prod IN) (Prod.mk (0 : ℝ)) n v)
  · -- The left side of `hC` vanishes, since the slices of the pulled-back form agree.
    have hV2 : mlieDerivForm (Manifold.prodVectorField (constVectorField (1 : ℝ))
        (0 : Π y : N, TangentSpace IN y)) (SmoothForm.mpullback _ hφ A).val (0, n)
          ![mfderiv IN (𝓘(ℝ).prod IN) (Prod.mk (0 : ℝ)) n v] = 0 := by
      have h := mpullback_apply (I := IN) (I' := 𝓘(ℝ).prod IN) (Prod.mk (0 : ℝ))
        (mlieDerivForm (Manifold.prodVectorField (constVectorField (1 : ℝ))
          (0 : Π y : N, TangentSpace IN y)) (SmoothForm.mpullback _ hφ A).val) n
        ![v]
      rw [hV, ContinuousAlternatingMap.coe_zero, Pi.zero_apply] at h
      rw [h]
      congr 1
      funext i
      fin_cases i
      exact congrArg _ (Matrix.cons_val_zero v ![]).symm
    -- Its right side is the identity, pushed forward along `(s, m) ↦ (γ s, m)`.
    rw [hC, SmoothForm.coe_mpullback, ← mpullback_mextDeriv_at
      (hφ.contMDiffAt.of_le (by simp)) ((A.contMDiff _).of_le (by simp)), mpullback_apply,
      mvfderiv_comp_apply _ (mdifferentiable_apply_rightFundamentalVectorField_prod ξ _)
        (hφ.mdifferentiableAt (by simp)), (hφ' _).mfderiv, hw] at hV2
    have hγ0 : γ 0 = x := by simp [hγdef, mulInvariantExp_zero]
    rw [← hγ0, eq_neg_iff_add_eq_zero, ← hV2]
    congr 2
    · funext i
      fin_cases i
      · rw [hW]
        exact Prod.ext (one_smul ℝ _).symm rfl
      · exact Prod.ext (zero_smul ℝ _).symm rfl
    · exact Prod.ext (zero_smul ℝ _).symm rfl
  · rw [SmoothForm.mpullback_apply, (hφ' q).mfderiv]
    congr 1
    funext i
    fin_cases i
    rw [hW]
    exact Prod.ext (one_smul ℝ _) rfl

/-- **Cartan's identity for invariant one-forms on `P × N`.** Let `A` be a smooth one-form on
`P × N`, for a smooth principal bundle `P` whose base and structure group are modelled without
boundary and any manifold `N`, possibly with boundary or corners. If `A` is invariant under the
right action `(x, m) ↦ (x • g, m)` of `G` on the first factor, then for every `ξ` in the Lie
algebra the contraction of `dA` with the field `(ξ_P, 0)` is minus the differential of the
function `A(ξ_P, 0)`: `dA ((ξ_P, 0), w) = -d (A (ξ_P, 0)) w`. -/
theorem mextDeriv_apply_rightFundamentalVectorField_prod (ξ : GroupLieAlgebra IG G)
    (p : ManifoldTotalSpace G P × N) (w : TangentSpace ((IB.prod IG).prod IN) p) :
    mextDeriv A.val p ![(rightFundamentalVectorField (IB.prod IG) ξ p.1, (0 : EN)), w] =
      -mvfderiv ((IB.prod IG).prod IN) (fun q : ManifoldTotalSpace G P × N ↦
        A.val q ![(rightFundamentalVectorField (IB.prod IG) ξ q.1, (0 : EN))]) p w := by
  obtain ⟨x, n⟩ := p
  obtain ⟨u, v⟩ := w
  have hw : ((u, v) : TangentSpace ((IB.prod IG).prod IN) (x, n)) =
      ((u, (0 : EN)) : TangentSpace ((IB.prod IG).prod IN) (x, n)) + ((0 : EB × EG), v) := by
    simp
  have e1 : mextDeriv A.val (x, n)
      ![(rightFundamentalVectorField (IB.prod IG) ξ x, (0 : EN)),
        (u, (0 : EN)) + ((0 : EB × EG), v)] =
        mextDeriv A.val (x, n) ![(rightFundamentalVectorField (IB.prod IG) ξ x, (0 : EN)),
          (u, (0 : EN))] +
        mextDeriv A.val (x, n) ![(rightFundamentalVectorField (IB.prod IG) ξ x, (0 : EN)),
          ((0 : EB × EG), v)] := by
    have := (mextDeriv A.val (x, n)).map_update_add
      ![(rightFundamentalVectorField (IB.prod IG) ξ x, (0 : EN)), (u, (0 : EN))] 1
      (u, (0 : EN)) ((0 : EB × EG), v)
    convert this using 3 <;> funext i <;> fin_cases i <;> rfl
  rw [hw, e1]
  refine (congrArg₂ (· + ·) (mextDeriv_apply_rightFundamentalVectorField_prod_inl hA ξ x n u)
    (mextDeriv_apply_rightFundamentalVectorField_prod_inr hA ξ x n v)).trans ?_
  rw [← neg_add]
  exact congrArg Neg.neg (map_add _ _ _).symm

/-- A smooth one-form on `P × N` that is invariant under the right action of `G` on the first
factor has vanishing Lie derivative along the field `(ξ_P, 0)`, for every `ξ` in the Lie algebra,
where `N` may have boundary or corners. -/
theorem mlieDerivForm_rightFundamentalVectorField_prod_eq_zero (ξ : GroupLieAlgebra IG G) :
    mlieDerivForm (fun q : ManifoldTotalSpace G P × N ↦
      ((rightFundamentalVectorField (IB.prod IG) ξ q.1, (0 : EN)) :
        TangentSpace ((IB.prod IG).prod IN) q)) A.val = 0 := by
  funext q
  ext v
  rw [Pi.zero_apply, ContinuousAlternatingMap.coe_zero, Pi.zero_apply, ← Matrix.cons_head_tail v,
    Subsingleton.elim (Matrix.vecTail v) ![],
    mlieDerivForm_apply_eq_mextDeriv_add (fun _ ↦ rfl) (A.mdifferentiableAt q)
      (mdifferentiable_rightFundamentalVectorField_prod ξ q),
    mextDeriv_apply_rightFundamentalVectorField_prod hA, neg_add_cancel]

/-- **Cartan's identity for invariant one-forms on `P × N`**, as an identity of forms:
`ι_{(ξ_P, 0)} dA = -d (ι_{(ξ_P, 0)} A)` for a smooth one-form `A` on `P × N` invariant under the
right action of `G` on the first factor, where `N` may have boundary or corners. -/
theorem interior_mextDeriv_rightFundamentalVectorField_prod (ξ : GroupLieAlgebra IG G) :
    RoughForm.interior (fun q : ManifoldTotalSpace G P × N ↦
        ((rightFundamentalVectorField (IB.prod IG) ξ q.1, (0 : EN)) :
          TangentSpace ((IB.prod IG).prod IN) q)) (mextDeriv A.val) =
      -mextDeriv (RoughForm.interior (fun q : ManifoldTotalSpace G P × N ↦
        ((rightFundamentalVectorField (IB.prod IG) ξ q.1, (0 : EN)) :
          TangentSpace ((IB.prod IG).prod IN) q)) A.val) :=
  eq_neg_of_add_eq_zero_left ((SmoothForm.mlieDerivForm_eq_interior_mextDeriv_add
    (mdifferentiable_rightFundamentalVectorField_prod ξ)).symm.trans
      (mlieDerivForm_rightFundamentalVectorField_prod_eq_zero hA ξ))

end Prod

end LieDeriv

end TauCeti.PrincipalBundle
