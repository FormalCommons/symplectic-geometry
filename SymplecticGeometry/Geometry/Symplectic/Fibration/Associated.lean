/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.FiberBundle.Associated.PullbackPrincipal
public import SymplecticGeometry.Geometry.Manifold.FiberBundle.Principal.Connection.Curvature
public import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.ContMDiff
public import TauCeti.Geometry.Manifold.DifferentialForm.Closed
public import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Smooth.Basic
public import TauCeti.Geometry.Manifold.MFDeriv.ContinuousLinearMap
public import TauCeti.Geometry.Symplectic.Hamiltonian.EquivariantMomentMap.Basic
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Smooth
import SymplecticGeometry.Geometry.Manifold.ContMDiff.Dual
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Wedge.Smooth.Leibniz
import SymplecticGeometry.Geometry.Manifold.FiberBundle.Principal.Connection.Basic
import SymplecticGeometry.Geometry.Manifold.MFDeriv.Prod
import TauCeti.Data.Fin.VecNotation

/-!
# Weinstein's form on `P × F` and its descent to `P ×_G F`

Let `P` be a smooth principal `G`-bundle over `B` with a connection form `A`, and let `G` act on
the left on a manifold `F` with a closed invariant two-form `σ` and a moment map `μ : F → 𝔤*`, in
the sign convention `⟨dμ, ξ⟩ = -ι_{X_ξ} σ` (so that `-μ` is a moment map in Tau Ceti's sense,
`TauCeti.SmoothTwoForm.IsEquivariantMomentMap`). On the product `P × F`, pairing `μ` with `A`
gives a real one-form `⟨μ, A⟩`, and **Weinstein's form** is the closed two-form

  `σ + d ⟨μ, A⟩`,

where `σ` stands for its pull-back along the projection to `F`. It is invariant under the diagonal
action `(x, v) ↦ (x · g, g⁻¹ • v)` of `G`, the action whose orbits are the fibres of the quotient
map `P × F → P ×_G F` (`TauCeti.AssociatedBundle.chartedMk`), and it vanishes on the vectors
`(x ξ, -X_ξ(v))` that span the kernel of the derivative of that map. These are the two hypotheses
of the descent theorem `TauCeti.AssociatedBundle.existsUnique_mpullback_chartedMk_eq`, so
Weinstein's form is the pull-back of a unique closed two-form on `P ×_G F`, which restricts to `σ`
on every fibre: this is Weinstein's construction.

## Main definitions

* `SymplecticGeometry.momentMapCLM μ hμs`: a map `μ : F → 𝔤*` with smooth components, as a smooth
  map to the continuous dual `𝔤 →L[ℝ] ℝ`.
* `SymplecticGeometry.momentPairing μ hμs A`: the one-form `⟨μ, A⟩` on `P × F`, the paired wedge
  of the zero-form `μ` with the pull-back of `A`, along the evaluation of `𝔤 →L[ℝ] ℝ` on `𝔤`.
* `SymplecticGeometry.weinsteinForm σ μ hμs A`: the two-form `σ + d ⟨μ, A⟩` on `P × F`.
* `SymplecticGeometry.associatedForm σ hμ hσG hA`: the two-form on `P ×_G F` whose pull-back
  to `P × F` is Weinstein's form.

## Main results

* `SymplecticGeometry.momentPairing_apply`: `⟨μ, A⟩_{(x, v)}(a, b) = μ(v)(A_x a)`.
* `SymplecticGeometry.mextDerivₗ_momentPairing_apply`: `d ⟨μ, A⟩` on two tangent vectors, by the
  Leibniz rule.
* `SymplecticGeometry.weinsteinForm_apply`: Weinstein's form in terms of the curvature `F_A`,
  `σ(b₁ + X_{A a₁}, b₂ + X_{A a₂}) + ⟨μ, F_A(a₁, a₂)⟩`.
* `SymplecticGeometry.isClosed_weinsteinForm`: Weinstein's form is closed.
* `SymplecticGeometry.mpullback_smul_momentPairing`: `⟨μ, A⟩` is invariant under the diagonal
  action when `A` is equivariant and `μ` is coadjoint-equivariant.
* `SymplecticGeometry.mpullback_smul_weinsteinForm`: Weinstein's form is invariant under the
  diagonal action of `G`.
* `SymplecticGeometry.weinsteinForm_apply_eq_zero_of_fundamental`: Weinstein's form vanishes on
  the fundamental vectors `(x ξ, -X_ξ(v))` of the diagonal action.
* `SymplecticGeometry.mpullback_chartedMk_associatedForm`,
  `SymplecticGeometry.isClosed_associatedForm`, `SymplecticGeometry.mpullback_associatedForm_fiber`:
  the associated form pulls back to Weinstein's form, is closed, and pulls back to `σ` along each
  fibre inclusion `v ↦ [x, v]`.
* `SymplecticGeometry.eq_associatedForm_iff`: the associated form is the only two-form on
  `P ×_G F` whose pull-back to `P × F` is Weinstein's form.
* `SymplecticGeometry.exists_isClosed_mpullback_eq_weinsteinForm`: Weinstein's construction.

## Implementation notes

The definitions take the smoothness of the components of `μ` as the argument `hμs`, which is all
they need; the theorems take it as an implicit argument, so that it is never asked for beside the
moment map hypothesis, from which it follows
(`TauCeti.SmoothTwoForm.IsMomentMap.contMDiff_of_neg`). The pairing turns `μ` into a map to
`𝔤 →L[ℝ] ℝ`, which is smooth since `𝔤` is finite-dimensional
(`SymplecticGeometry.contMDiff_toContinuousLinearMap_of_contMDiff_apply`).
Closedness needs only that `σ` is closed; invariance needs the
equivariance of `A` and of `μ`, and the invariance of `σ`, which Tau Ceti's moment maps
do not include. The expression in terms of the curvature (`weinsteinForm_apply`) needs only the
moment map condition and its infinitesimal equivariance, `σ(X_ξ, X_η) = -μ(⁅ξ, η⁆)`, which
Tau Ceti derives from equivariance
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.momentCocycle_eq_zero`).
The connection form takes its values in the model space `EG` of `G`, which is `𝔤` by definition,
and the moment map is paired with it through `momentMapCLM`, with values in `EG →L[ℝ] ℝ`.

The associated form is Tau Ceti's descent `TauCeti.SmoothForm.descendedForm` of Weinstein's form
along the quotient map, a surjective submersion
(`TauCeti.AssociatedBundle.isSubmersion_chartedMk`). Its statements take the smoothness of the
associated bundle as an instance argument, since smooth forms on `P ×_G F` need it; it holds by
`TauCeti.AssociatedBundle.contMDiffFiberBundle`, which is not an instance. Neither `F` nor `G`
need be compact, and `σ` need not be nondegenerate.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §6.3
  (Theorem 6.3.3 and the form (6.3.1)).
* [A. Weinstein, *A universal phase space for particles in Yang–Mills fields*][Weinstein1978].
-/

public section

noncomputable section

open Bundle Manifold MulOpposite TauCeti TauCeti.Lie
open TauCeti.PrincipalBundle (IsConnectionForm)
open scoped Manifold ContDiff

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

namespace SymplecticGeometry

variable {EB HB B : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  {IB : ModelWithCorners ℝ EB HB} [TopologicalSpace B] [ChartedSpace HB B] [IsManifold IB ∞ B]
  {EG HG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
  [TopologicalSpace HG] {IG : ModelWithCorners ℝ EG HG} [TopologicalSpace G] [ChartedSpace HG G]
  [Group G]
  {P : B → Type*} [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle G P]
  {EF HF F : Type*} [NormedAddCommGroup EF] [NormedSpace ℝ EF] [TopologicalSpace HF]
  {IF : ModelWithCorners ℝ EF HF} [TopologicalSpace F] [ChartedSpace HF F]

/-! ### The pairing of the moment map with the connection form -/

/-- A map `μ : F → 𝔤*` with smooth components, as a smooth map to the continuous dual
`EG →L[ℝ] ℝ` of the model space `EG`, which is `𝔤` by definition: it is finite-dimensional, so
every linear form on it is continuous. -/
def momentMapCLM (μ : F → Module.Dual ℝ (GroupLieAlgebra IG G))
    (hμs : ∀ ξ, ContMDiff IF 𝓘(ℝ) ∞ fun v ↦ μ v ξ) :
    C^∞⟮IF, F; 𝓘(ℝ, EG →L[ℝ] ℝ), EG →L[ℝ] ℝ⟯ where
  val v := LinearMap.toContinuousLinearMap (μ v)
  property := contMDiff_toContinuousLinearMap_of_contMDiff_apply hμs

@[simp]
theorem momentMapCLM_apply (μ : F → Module.Dual ℝ (GroupLieAlgebra IG G))
    (hμs : ∀ ξ, ContMDiff IF 𝓘(ℝ) ∞ fun v ↦ μ v ξ) (v : F) (ξ : EG) :
    momentMapCLM μ hμs v ξ = μ v ξ :=
  (rfl)

variable [IsManifold IF ∞ F] [LieGroup IG ∞ G] [ContMDiffFiberBundle ∞ G P IB IG]

/-- The **pairing** `⟨μ, A⟩` of a map `μ : F → 𝔤*` with smooth components and a `𝔤`-valued
one-form `A` on the total space of `P`: the real one-form on `P × F` whose value at `(x, v)` on a
tangent vector `(a, b)` is `μ(v)(A_x a)` (`momentPairing_apply`). It is the paired wedge, along
the evaluation of `EG →L[ℝ] ℝ` on `EG`, of the zero-form `(x, v) ↦ μ(v)` with the pull-back of `A`
along the first projection. -/
def momentPairing (μ : F → Module.Dual ℝ (GroupLieAlgebra IG G))
    (hμs : ∀ ξ, ContMDiff IF 𝓘(ℝ) ∞ fun v ↦ μ v ξ)
    (A : SmoothForm (IB.prod IG) (ManifoldTotalSpace G P) EG 1) :
    SmoothForm ((IB.prod IG).prod IF) (ManifoldTotalSpace G P × F) ℝ 1 :=
  SmoothForm.wedgeWith (ContinuousLinearMap.id ℝ (EG →L[ℝ] ℝ))
    (SmoothForm.mpullback Prod.snd contMDiff_snd (SmoothForm.ofFunction (momentMapCLM μ hμs)))
    (SmoothForm.mpullback Prod.fst contMDiff_fst A)

theorem momentPairing_def (μ : F → Module.Dual ℝ (GroupLieAlgebra IG G))
    (hμs : ∀ ξ, ContMDiff IF 𝓘(ℝ) ∞ fun v ↦ μ v ξ)
    (A : SmoothForm (IB.prod IG) (ManifoldTotalSpace G P) EG 1) :
    momentPairing μ hμs A =
      SmoothForm.wedgeWith (ContinuousLinearMap.id ℝ (EG →L[ℝ] ℝ))
        (SmoothForm.mpullback Prod.snd contMDiff_snd (SmoothForm.ofFunction (momentMapCLM μ hμs)))
        (SmoothForm.mpullback Prod.fst contMDiff_fst A) :=
  (rfl)

/-- The pairing `⟨μ, A⟩` at `(x, v)` on a tangent vector `(a, b)` is `μ(v)(A_x a)`. -/
theorem momentPairing_apply (μ : F → Module.Dual ℝ (GroupLieAlgebra IG G))
    (hμs : ∀ ξ, ContMDiff IF 𝓘(ℝ) ∞ fun v ↦ μ v ξ)
    (A : SmoothForm (IB.prod IG) (ManifoldTotalSpace G P) EG 1)
    (p : ManifoldTotalSpace G P × F) (w : TangentSpace ((IB.prod IG).prod IF) p) :
    (momentPairing μ hμs A).val p ![w] = μ p.2 (A.val p.1 ![w.1]) := by
  rw [momentPairing_def, SmoothForm.wedgeWith_flip, SmoothForm.wedgeWith_apply_zero_right]
  simp only [Nat.zero_mul, pow_zero, one_smul, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.id_apply, Fin.cast_refl, Function.comp_id, SmoothForm.mpullback_apply_one,
    mfderiv_fst]
  -- In a single call `mpullback_apply` would fire first and leave `mpullback_apply_one` unused.
  simp only [SmoothForm.mpullback_apply, SmoothForm.coe_ofFunction, RoughForm.ofFunction_apply,
    momentMapCLM_apply]
  -- The tangent space of the product is the product of the tangent spaces by definition.
  rfl

/-- The exterior derivative of the pairing, `d ⟨μ, A⟩ = ⟨dμ ∧ A⟩ + ⟨μ, dA⟩`, on two tangent
vectors `w₁ = (a₁, b₁)` and `w₂ = (a₂, b₂)` at `(x, v)`:
`dμ(b₁)(A_x a₂) - dμ(b₂)(A_x a₁) + μ(v)(dA_x(a₁, a₂))`, where `dμ(b)(ξ)` is the derivative along
`b` of the component `μ_ξ`. -/
theorem mextDerivₗ_momentPairing_apply (μ : F → Module.Dual ℝ (GroupLieAlgebra IG G))
    (hμs : ∀ ξ, ContMDiff IF 𝓘(ℝ) ∞ fun v ↦ μ v ξ)
    (A : SmoothForm (IB.prod IG) (ManifoldTotalSpace G P) EG 1)
    (p : ManifoldTotalSpace G P × F) (w₁ w₂ : TangentSpace ((IB.prod IG).prod IF) p) :
    (mextDerivₗ ((IB.prod IG).prod IF) 1 (momentPairing μ hμs A)).val p ![w₁, w₂] =
      mvfderiv IF (fun v ↦ μ v (A.val p.1 ![(Manifold.tangentSpaceProdEquiv p w₂).1])) p.2
          (Manifold.tangentSpaceProdEquiv p w₁).2 -
        mvfderiv IF (fun v ↦ μ v (A.val p.1 ![(Manifold.tangentSpaceProdEquiv p w₁).1])) p.2
          (Manifold.tangentSpaceProdEquiv p w₂).2 +
        μ p.2 (mextDeriv A.val p.1
          ![(Manifold.tangentSpaceProdEquiv p w₁).1, (Manifold.tangentSpaceProdEquiv p w₂).1]) := by
  have h₁ (w : TangentSpace ((IB.prod IG).prod IF) p) :
      (fun i ↦ (Manifold.tangentSpaceProdEquiv p (![w] i)).1) =
        ![(Manifold.tangentSpaceProdEquiv p w).1] :=
    (FinVec.etaExpand_eq _).symm
  have h₂ : (fun i ↦ (Manifold.tangentSpaceProdEquiv p (![w₁, w₂] i)).1) =
      ![(Manifold.tangentSpaceProdEquiv p w₁).1, (Manifold.tangentSpaceProdEquiv p w₂).1] :=
    (FinVec.etaExpand_eq _).symm
  have hd : MDifferentiableAt IF 𝓘(ℝ, EG →L[ℝ] ℝ) (momentMapCLM μ hμs) p.2 :=
    (momentMapCLM μ hμs).contMDiff.mdifferentiableAt (by simp)
  rw [momentPairing_def, mextDerivₗ_apply, SmoothForm.coe_wedgeWith,
    SmoothForm.mextDeriv_wedgeWith_zero_one_apply, ← mextDerivₗ_apply, ← mextDerivₗ_apply,
    SmoothForm.mextDerivₗ_mpullback, SmoothForm.mextDerivₗ_mpullback]
  simp only [ContinuousLinearMap.id_apply, SmoothForm.mpullback_fst_apply,
    SmoothForm.mpullback_snd_apply, mextDerivₗ_apply, SmoothForm.coe_ofFunction,
    mextDeriv_ofFunction, RoughForm.ofFunction_apply,
    ContinuousAlternatingMap.ofSubsingleton_apply_apply, Matrix.cons_val_zero, h₁, h₂]
  rw [← mvfderiv_clm_apply_const hd, ← mvfderiv_clm_apply_const hd]
  simp only [momentMapCLM_apply]

/-! ### Weinstein's form -/

/-- **Weinstein's form** `σ + d ⟨μ, A⟩` on `P × F`, for a two-form `σ` on `F`, a map `μ : F → 𝔤*`
with smooth components and a `𝔤`-valued one-form `A` on the total space of `P`; here `σ` stands
for its pull-back along the projection to `F`. -/
def weinsteinForm (σ : SmoothTwoForm IF F) (μ : F → Module.Dual ℝ (GroupLieAlgebra IG G))
    (hμs : ∀ ξ, ContMDiff IF 𝓘(ℝ) ∞ fun v ↦ μ v ξ)
    (A : SmoothForm (IB.prod IG) (ManifoldTotalSpace G P) EG 1) :
    SmoothForm ((IB.prod IG).prod IF) (ManifoldTotalSpace G P × F) ℝ 2 :=
  SmoothForm.mpullback Prod.snd contMDiff_snd σ +
    mextDerivₗ ((IB.prod IG).prod IF) 1 (momentPairing μ hμs A)

theorem weinsteinForm_def (σ : SmoothTwoForm IF F)
    (μ : F → Module.Dual ℝ (GroupLieAlgebra IG G))
    (hμs : ∀ ξ, ContMDiff IF 𝓘(ℝ) ∞ fun v ↦ μ v ξ)
    (A : SmoothForm (IB.prod IG) (ManifoldTotalSpace G P) EG 1) :
    weinsteinForm σ μ hμs A =
      SmoothForm.mpullback Prod.snd contMDiff_snd σ +
        mextDerivₗ ((IB.prod IG).prod IF) 1 (momentPairing μ hμs A) :=
  (rfl)

/-- **Weinstein's form in terms of the curvature.** For a moment map `μ` of an action of `G` on
`F`, in the sign convention where `-μ` is a moment map in Tau Ceti's sense, Weinstein's form at
`(x, v)` on two tangent vectors `(a₁, b₁)` and `(a₂, b₂)` is
`σ_v(b₁ + X_{A a₁}(v), b₂ + X_{A a₂}(v)) + μ(v)(F_A(a₁, a₂))`, where `X_ξ` is the fundamental
vector field of `ξ` on `F` and `F_A` the curvature of `A`. -/
theorem weinsteinForm_apply [CompleteSpace EF] [MulAction G F] [ContMDiffSMul IG IF ∞ G F]
    {σ : SmoothTwoForm IF F} {μ : F → Module.Dual ℝ (GroupLieAlgebra IG G)}
    (hμ : σ.IsEquivariantMomentMap fun v ↦ -μ v) {hμs : ∀ ξ, ContMDiff IF 𝓘(ℝ) ∞ fun v ↦ μ v ξ}
    (A : SmoothForm (IB.prod IG) (ManifoldTotalSpace G P) EG 1)
    (p : ManifoldTotalSpace G P × F) (w₁ w₂ : TangentSpace ((IB.prod IG).prod IF) p) :
    (weinsteinForm σ μ hμs A).val p ![w₁, w₂] =
      σ.val p.2 ![(Manifold.tangentSpaceProdEquiv p w₁).2 +
            fundamentalVectorField (I := IG) (G := G) IF
              (A.val p.1 ![(Manifold.tangentSpaceProdEquiv p w₁).1]) p.2,
          (Manifold.tangentSpaceProdEquiv p w₂).2 +
            fundamentalVectorField (I := IG) (G := G) IF
              (A.val p.1 ![(Manifold.tangentSpaceProdEquiv p w₂).1]) p.2] +
        μ p.2 ((gaugeCurvature (GroupLieAlgebra.bracketL IG G) A).val p.1
          ![(Manifold.tangentSpaceProdEquiv p w₁).1, (Manifold.tangentSpaceProdEquiv p w₂).1]) := by
  -- Infinitesimal equivariance: `σ(X_ξ, X_η) = -μ(⁅ξ, η⁆)`.
  have hc := SmoothTwoForm.momentCocycle_eq_zero_iff.1 (hμ.momentCocycle_eq_zero p.2)
    (A.val p.1 ![(Manifold.tangentSpaceProdEquiv p w₁).1])
    (A.val p.1 ![(Manifold.tangentSpaceProdEquiv p w₂).1])
  simp only [LinearMap.neg_apply] at hc
  rw [InfinitesimalAction.fundamental_apply (I' := IF) (M := F)
      (A.val p.1 ![(Manifold.tangentSpaceProdEquiv p w₁).1]),
    InfinitesimalAction.fundamental_apply (I' := IF) (M := F)
      (A.val p.1 ![(Manifold.tangentSpaceProdEquiv p w₂).1])] at hc
  rw [weinsteinForm_def, SmoothBundleForm.add_apply, ContinuousAlternatingMap.add_apply,
    mextDerivₗ_momentPairing_apply,
    gaugeCurvature_val _ (fun a b ↦ GroupLieAlgebra.bracketL_swap b a)]
  -- `μ p.2` is linear on `𝔤`, not on the model space `EG` where the values of `A` lie: split the
  -- sum through `momentMapCLM`, which is linear on `EG`.
  simp only [← momentMapCLM_apply μ hμs]
  rw [map_add]
  simp only [momentMapCLM_apply]
  rw [hμ.toIsMomentMap.mvfderiv_apply_of_neg (A.val p.1 ![(Manifold.tangentSpaceProdEquiv p w₂).1]),
    hμ.toIsMomentMap.mvfderiv_apply_of_neg (A.val p.1 ![(Manifold.tangentSpaceProdEquiv p w₁).1]),
    GroupLieAlgebra.bracketL_apply (I := IG) (G := G)
      (A.val p.1 ![(Manifold.tangentSpaceProdEquiv p w₁).1])
      (A.val p.1 ![(Manifold.tangentSpaceProdEquiv p w₂).1]),
    InfinitesimalAction.fundamental_apply (I' := IF) (M := F)
      (A.val p.1 ![(Manifold.tangentSpaceProdEquiv p w₁).1]),
    InfinitesimalAction.fundamental_apply (I' := IF) (M := F)
      (A.val p.1 ![(Manifold.tangentSpaceProdEquiv p w₂).1]),
    ← SmoothBundleForm.eval₂_apply, ← SmoothBundleForm.eval₂_apply,
    SmoothForm.eval₂_mpullback_snd, SmoothBundleForm.eval₂_add_left,
    SmoothBundleForm.eval₂_add_right, SmoothBundleForm.eval₂_add_right, hc,
    SmoothBundleForm.eval₂_swap σ p.2 (fundamentalVectorField (I := IG) (G := G) IF
      (A.val p.1 ![(Manifold.tangentSpaceProdEquiv p w₁).1]) p.2)
      (Manifold.tangentSpaceProdEquiv p w₂).2,
    SmoothBundleForm.eval₂_swap σ p.2 (fundamentalVectorField (I := IG) (G := G) IF
      (A.val p.1 ![(Manifold.tangentSpaceProdEquiv p w₂).1]) p.2)
      (Manifold.tangentSpaceProdEquiv p w₁).2]
  ring

/-- **Weinstein's form is closed** when `σ` is. -/
theorem isClosed_weinsteinForm {σ : SmoothTwoForm IF F} (hσ : σ.IsClosed)
    {μ : F → Module.Dual ℝ (GroupLieAlgebra IG G)} {hμs : ∀ ξ, ContMDiff IF 𝓘(ℝ) ∞ fun v ↦ μ v ξ}
    (A : SmoothForm (IB.prod IG) (ManifoldTotalSpace G P) EG 1) :
    (weinsteinForm σ μ hμs A).IsClosed :=
  (hσ.mpullback Prod.snd contMDiff_snd).add (SmoothForm.isClosed_mextDerivₗ _)

variable [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P] [MulAction G F]
  [ContMDiffSMul IG IF ∞ G F]

/-- The pairing `⟨μ, A⟩` is invariant under the diagonal action `(x, v) ↦ (x · g, g⁻¹ • v)` of
`G` on `P × F`, when `A` is equivariant as connection forms are and `μ` is coadjoint-equivariant:
the factor `Ad(g⁻¹)` that the action puts on `A` cancels the factor `Ad(g)` it puts on `μ`. -/
theorem mpullback_smul_momentPairing
    {μ : F → Module.Dual ℝ (GroupLieAlgebra IG G)} {hμs : ∀ ξ, ContMDiff IF 𝓘(ℝ) ∞ fun v ↦ μ v ξ}
    (hμG : ∀ (g : G) (v : F) (ξ : GroupLieAlgebra IG G),
      μ (g⁻¹ • v) ξ = μ v (adjointContinuousLinearMap g ξ))
    {A : SmoothForm (IB.prod IG) (ManifoldTotalSpace G P) EG 1}
    (hA : ∀ g : G, SmoothForm.mpullback (fun x : ManifoldTotalSpace G P ↦ op g • x)
      (contMDiff_const_smul (op g)) A =
        SmoothForm.mapCoeff (F := EG) (G := EG) (adjointContinuousLinearMap (I := IG) g⁻¹) A)
    (g : G) :
    SmoothForm.mpullback (fun x : ManifoldTotalSpace G P × F ↦ (op g • x.1, g⁻¹ • x.2))
      (AssociatedBundle.contMDiff_op_smul_inv_smul g) (momentPairing μ hμs A) =
      momentPairing μ hμs A := by
  have h1 : SmoothForm.mpullback (fun x : ManifoldTotalSpace G P × F ↦ (op g • x.1, g⁻¹ • x.2))
      (AssociatedBundle.contMDiff_op_smul_inv_smul (IB := IB) (IG := IG) (IF := IF) g)
      (SmoothForm.mpullback Prod.fst contMDiff_fst A) =
      SmoothForm.mpullback Prod.fst contMDiff_fst
        (SmoothForm.mapCoeff (F := EG) (G := EG) (adjointContinuousLinearMap (I := IG) g⁻¹) A) := by
    rw [← hA g]
    exact SmoothForm.mpullback_mpullback_of_comp_eq _ _ _ _ (by rfl) A
  have h2 : SmoothForm.mpullback (fun x : ManifoldTotalSpace G P × F ↦ (op g • x.1, g⁻¹ • x.2))
      (AssociatedBundle.contMDiff_op_smul_inv_smul (IB := IB) (IG := IG) (IF := IF) g)
      (SmoothForm.mpullback Prod.snd contMDiff_snd
        (SmoothForm.ofFunction (I := IF) (momentMapCLM μ hμs))) =
      SmoothForm.mpullback Prod.snd contMDiff_snd
        (SmoothForm.mpullback (fun v : F ↦ g⁻¹ • v)
          (ContMDiffSMul.contMDiff_const_smul (I := IG) (M := F) g⁻¹)
          (SmoothForm.ofFunction (momentMapCLM μ hμs))) :=
    SmoothForm.mpullback_mpullback_of_comp_eq _ _ _ _ (by rfl) _
  rw [momentPairing_def]
  -- The pull-back of the wedge is stated in degree `0 + 1`, which is `1` only by unfolding.
  refine (SmoothForm.mpullback_wedgeWith (k := 0) (l := 1)
    (ContinuousLinearMap.id ℝ (EG →L[ℝ] ℝ)) _
    (AssociatedBundle.contMDiff_op_smul_inv_smul (IB := IB) (IG := IG) (IF := IF) (P := P)
      (F := F) g) _ _).trans ?_
  rw [h1, h2]
  refine SmoothBundleForm.ext fun p w ↦ ?_
  rw [SmoothForm.wedgeWith_flip, SmoothForm.wedgeWith_apply_zero_right,
    SmoothForm.wedgeWith_flip, SmoothForm.wedgeWith_apply_zero_right]
  -- `Ad(g⁻¹)` is a map of `GroupLieAlgebra IG G`, read on `EG`; `simp` does not unify it with the
  -- coefficient map of the general lemmas, so they are instantiated first.
  have hL := SmoothForm.coe_mapCoeff (F := EG) (G := EG)
    (adjointContinuousLinearMap (I := IG) g⁻¹) A
  have hL' := RoughForm.mapCoeff_apply (F := EG) (G := EG)
    (adjointContinuousLinearMap (I := IG) g⁻¹) A.val
  simp only [Nat.zero_mul, pow_zero, one_smul, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.id_apply, SmoothForm.mpullback_apply, SmoothForm.coe_ofFunction,
    RoughForm.ofFunction_apply, hL, hL', momentMapCLM_apply]
  -- The factor `Ad(g)` on `μ` cancels the factor `Ad(g⁻¹)` on `A`.
  refine (hμG g p.2 _).trans ?_
  exact congrArg (μ p.2) (adjointContinuousLinearMap_adjointContinuousLinearMap_inv (I := IG) g _)

/-- **Weinstein's form is invariant** under the diagonal action `(x, v) ↦ (x · g, g⁻¹ • v)` of `G`
on `P × F`, for a connection form `A`, a two-form `σ` invariant under `G` and an equivariant moment
map `μ` (in the sign convention where `-μ` is a moment map in Tau Ceti's sense). -/
theorem mpullback_smul_weinsteinForm [CompleteSpace EF] {σ : SmoothTwoForm IF F}
    {μ : F → Module.Dual ℝ (GroupLieAlgebra IG G)} (hμ : σ.IsEquivariantMomentMap fun v ↦ -μ v)
    (hσG : ∀ g : G, SmoothForm.mpullback (fun v : F ↦ g • v)
      (ContMDiffSMul.contMDiff_const_smul (I := IG) g) σ = σ)
    {hμs : ∀ ξ, ContMDiff IF 𝓘(ℝ) ∞ fun v ↦ μ v ξ}
    {A : SmoothForm (IB.prod IG) (ManifoldTotalSpace G P) EG 1}
    (hA : IsConnectionForm A) (g : G) :
    SmoothForm.mpullback (fun x : ManifoldTotalSpace G P × F ↦ (op g • x.1, g⁻¹ • x.2))
      (AssociatedBundle.contMDiff_op_smul_inv_smul g) (weinsteinForm σ μ hμs A) =
      weinsteinForm σ μ hμs A := by
  have hμG (g : G) (v : F) (ξ : GroupLieAlgebra IG G) :
      μ (g⁻¹ • v) ξ = μ v (adjointContinuousLinearMap g ξ) := by
    simpa using congrArg (· ξ) (hμ.apply_smul g⁻¹ v)
  have hσ : SmoothForm.mpullback (fun x : ManifoldTotalSpace G P × F ↦ (op g • x.1, g⁻¹ • x.2))
      (AssociatedBundle.contMDiff_op_smul_inv_smul (IB := IB) (IG := IG) (IF := IF) g)
      (SmoothForm.mpullback Prod.snd contMDiff_snd σ) =
      SmoothForm.mpullback Prod.snd contMDiff_snd
        (SmoothForm.mpullback (fun v : F ↦ g⁻¹ • v)
          (ContMDiffSMul.contMDiff_const_smul (I := IG) (M := F) g⁻¹) σ) :=
    SmoothForm.mpullback_mpullback_of_comp_eq _ _ _ _ (by rfl) σ
  rw [weinsteinForm_def, map_add, ← SmoothForm.mextDerivₗ_mpullback,
    mpullback_smul_momentPairing hμG hA.mpullback_op_smul g, hσ, hσG g⁻¹]

variable [IB.Boundaryless] [IG.Boundaryless]

/-- **Weinstein's form is horizontal**: for a connection form `A` and a moment map `μ` (in the sign
convention where `-μ` is a moment map in Tau Ceti's sense), Weinstein's form at `(x, v)` vanishes
as soon as one of its arguments is `(x ξ, -X_ξ(v))`, the fundamental vector of `ξ` for the
diagonal action. This is the second hypothesis of the descent theorem
`TauCeti.AssociatedBundle.existsUnique_mpullback_chartedMk_eq`. -/
theorem weinsteinForm_apply_eq_zero_of_fundamental [CompleteSpace EF] {σ : SmoothTwoForm IF F}
    {μ : F → Module.Dual ℝ (GroupLieAlgebra IG G)} (hμ : σ.IsEquivariantMomentMap fun v ↦ -μ v)
    {hμs : ∀ ξ, ContMDiff IF 𝓘(ℝ) ∞ fun v ↦ μ v ξ}
    {A : SmoothForm (IB.prod IG) (ManifoldTotalSpace G P) EG 1}
    (hA : IsConnectionForm A) (p : ManifoldTotalSpace G P × F)
    (w : Fin 2 → TangentSpace ((IB.prod IG).prod IF) p) (j : Fin 2) (ξ : GroupLieAlgebra IG G)
    (hw : w j =
      (rightFundamentalVectorField (IB.prod IG) ξ p.1, -fundamentalVectorField IF ξ p.2)) :
    (weinsteinForm σ μ hμs A).val p w = 0 := by
  -- With the fundamental vector first: `b + X_{A a}` vanishes on it, and so does the curvature.
  have key (w₀ w' : TangentSpace ((IB.prod IG).prod IF) p)
      (h : w₀ = (rightFundamentalVectorField (IB.prod IG) ξ p.1,
        -fundamentalVectorField IF ξ p.2)) :
      (weinsteinForm σ μ hμs A).val p ![w₀, w'] = 0 := by
    have h' : Manifold.tangentSpaceProdEquiv p w₀ =
        (rightFundamentalVectorField (IB.prod IG) ξ p.1, -fundamentalVectorField IF ξ p.2) := by
      rw [Manifold.tangentSpaceProdEquiv_apply]
      exact h
    rw [weinsteinForm_apply hμ, h', hA.apply_rightFundamentalVectorField, neg_add_cancel,
      hA.gaugeCurvature_apply_rightFundamentalVectorField, ← momentMapCLM_apply μ hμs, map_zero,
      add_zero]
    exact (σ.val p.2).map_coord_zero 0 rfl
  have hw01 : w = ![w 0, w 1] := (FinVec.etaExpand_eq _).symm
  obtain rfl | rfl : j = 0 ∨ j = 1 := by fin_cases j <;> simp
  · rw [hw01]
    exact key _ _ hw
  · rw [hw01, ContinuousAlternatingMap.apply_vecCons_swap, key _ _ hw, neg_zero]

variable [ContinuousSMul G F] [FiniteDimensional ℝ EB] [FiniteDimensional ℝ EF] [IF.Boundaryless]
  [ContMDiffFiberBundle ∞ F (AssociatedBundle G P F) IB IF] [CompleteSpace EF]

/-! ### The descended form on `P ×_G F` -/

/-- The **associated form** on `P ×_G F`: the unique smooth two-form whose pull-back along the
quotient map `(x, v) ↦ [x, v]` is Weinstein's form `σ + d ⟨μ, A⟩`
(`mpullback_chartedMk_associatedForm`, `eq_associatedForm_iff`), for a connection form `A`, a
two-form `σ` invariant under `G` and an equivariant moment map `μ` (in the sign convention where
`-μ` is a moment map in Tau Ceti's sense). It is the descent of Weinstein's form, which is
invariant and horizontal. -/
def associatedForm (σ : SmoothTwoForm IF F) {μ : F → Module.Dual ℝ (GroupLieAlgebra IG G)}
    (hμ : σ.IsEquivariantMomentMap fun v ↦ -μ v)
    (hσG : ∀ g : G, SmoothForm.mpullback (fun v : F ↦ g • v)
      (ContMDiffSMul.contMDiff_const_smul (I := IG) g) σ = σ)
    {A : SmoothForm (IB.prod IG) (ManifoldTotalSpace G P) EG 1}
    (hA : IsConnectionForm A) :
    SmoothForm (IB.prod IF) (ManifoldTotalSpace F (AssociatedBundle G P F)) ℝ 2 :=
  SmoothForm.descendedForm (AssociatedBundle.isSubmersion_chartedMk ENat.LEInfty.out)
    AssociatedBundle.surjective_chartedMk
    (weinsteinForm σ μ hμ.toIsMomentMap.contMDiff_of_neg A)
    (AssociatedBundle.isBasic_chartedMk (mpullback_smul_weinsteinForm hμ hσG hA)
      (weinsteinForm_apply_eq_zero_of_fundamental hμ hA))

theorem associatedForm_def (σ : SmoothTwoForm IF F)
    {μ : F → Module.Dual ℝ (GroupLieAlgebra IG G)} (hμ : σ.IsEquivariantMomentMap fun v ↦ -μ v)
    (hσG : ∀ g : G, SmoothForm.mpullback (fun v : F ↦ g • v)
      (ContMDiffSMul.contMDiff_const_smul (I := IG) g) σ = σ)
    {A : SmoothForm (IB.prod IG) (ManifoldTotalSpace G P) EG 1}
    (hA : IsConnectionForm A) :
    associatedForm σ hμ hσG hA =
      SmoothForm.descendedForm (AssociatedBundle.isSubmersion_chartedMk ENat.LEInfty.out)
        AssociatedBundle.surjective_chartedMk
        (weinsteinForm σ μ hμ.toIsMomentMap.contMDiff_of_neg A)
        (AssociatedBundle.isBasic_chartedMk (mpullback_smul_weinsteinForm hμ hσG hA)
          (weinsteinForm_apply_eq_zero_of_fundamental hμ hA)) :=
  (rfl)

/-- The pull-back of the associated form along the quotient map `(x, v) ↦ [x, v]` is Weinstein's
form `σ + d ⟨μ, A⟩`. -/
@[simp]
theorem mpullback_chartedMk_associatedForm {σ : SmoothTwoForm IF F}
    {μ : F → Module.Dual ℝ (GroupLieAlgebra IG G)} (hμ : σ.IsEquivariantMomentMap fun v ↦ -μ v)
    (hσG : ∀ g : G, SmoothForm.mpullback (fun v : F ↦ g • v)
      (ContMDiffSMul.contMDiff_const_smul (I := IG) g) σ = σ)
    {A : SmoothForm (IB.prod IG) (ManifoldTotalSpace G P) EG 1}
    (hA : IsConnectionForm A) :
    SmoothForm.mpullback (AssociatedBundle.chartedMk G F P)
      (AssociatedBundle.contMDiff_chartedMk ∞ IB IG IF) (associatedForm σ hμ hσG hA) =
      weinsteinForm σ μ hμ.toIsMomentMap.contMDiff_of_neg A :=
  SmoothForm.mpullback_descendedForm

/-- The associated form is the only smooth two-form on `P ×_G F` whose pull-back along the
quotient map `(x, v) ↦ [x, v]` is Weinstein's form `σ + d ⟨μ, A⟩`. -/
theorem eq_associatedForm_iff {σ : SmoothTwoForm IF F}
    {μ : F → Module.Dual ℝ (GroupLieAlgebra IG G)} (hμ : σ.IsEquivariantMomentMap fun v ↦ -μ v)
    (hσG : ∀ g : G, SmoothForm.mpullback (fun v : F ↦ g • v)
      (ContMDiffSMul.contMDiff_const_smul (I := IG) g) σ = σ)
    {A : SmoothForm (IB.prod IG) (ManifoldTotalSpace G P) EG 1}
    (hA : IsConnectionForm A)
    {τ : SmoothForm (IB.prod IF) (ManifoldTotalSpace F (AssociatedBundle G P F)) ℝ 2} :
    τ = associatedForm σ hμ hσG hA ↔
      SmoothForm.mpullback (AssociatedBundle.chartedMk G F P)
        (AssociatedBundle.contMDiff_chartedMk ∞ IB IG IF) τ =
        weinsteinForm σ μ hμ.toIsMomentMap.contMDiff_of_neg A :=
  SmoothForm.eq_descendedForm_iff

/-- The associated form is **closed** when `σ` is: its pull-back, Weinstein's form, is closed, and
the quotient map is a surjective submersion. -/
theorem isClosed_associatedForm {σ : SmoothTwoForm IF F} (hσ : σ.IsClosed)
    {μ : F → Module.Dual ℝ (GroupLieAlgebra IG G)} (hμ : σ.IsEquivariantMomentMap fun v ↦ -μ v)
    (hσG : ∀ g : G, SmoothForm.mpullback (fun v : F ↦ g • v)
      (ContMDiffSMul.contMDiff_const_smul (I := IG) g) σ = σ)
    {A : SmoothForm (IB.prod IG) (ManifoldTotalSpace G P) EG 1}
    (hA : IsConnectionForm A) :
    (associatedForm σ hμ hσG hA).IsClosed :=
  SmoothForm.isClosed_descendedForm_iff.2 (isClosed_weinsteinForm hσ A)

/-- The associated form **restricts to `σ` on the fibres**: for every point `x` of the total space
of `P`, its pull-back along the inclusion `v ↦ [x, v]` of `F` onto a fibre of `P ×_G F` is `σ`. -/
@[simp]
theorem mpullback_associatedForm_fiber {σ : SmoothTwoForm IF F}
    {μ : F → Module.Dual ℝ (GroupLieAlgebra IG G)} (hμ : σ.IsEquivariantMomentMap fun v ↦ -μ v)
    (hσG : ∀ g : G, SmoothForm.mpullback (fun v : F ↦ g • v)
      (ContMDiffSMul.contMDiff_const_smul (I := IG) g) σ = σ)
    {A : SmoothForm (IB.prod IG) (ManifoldTotalSpace G P) EG 1}
    (hA : IsConnectionForm A) (x : ManifoldTotalSpace G P) :
    SmoothForm.mpullback (fun v : F ↦ AssociatedBundle.chartedMk G F P (x, v))
      (AssociatedBundle.contMDiff_chartedMk_right ∞ IB IG IF x) (associatedForm σ hμ hσG hA) =
      σ := by
  have h := SmoothForm.mpullback_mpullback (fun v : F ↦ (x, v)) (AssociatedBundle.chartedMk G F P)
    (contMDiff_const.prodMk contMDiff_id) (AssociatedBundle.contMDiff_chartedMk ∞ IB IG IF)
    (associatedForm σ hμ hσG hA)
  rw [mpullback_chartedMk_associatedForm] at h
  refine h.symm.trans ?_
  refine SmoothBundleForm.ext_eval₂ fun v a b ↦ ?_
  rw [SmoothBundleForm.eval₂_apply, SmoothBundleForm.eval₂_apply]
  rw [SmoothForm.coe_mpullback, TauCeti.mpullback_apply_pair, weinsteinForm_apply hμ,
    Manifold.tangentSpaceProdEquiv_mfderiv_prodMk_right,
    Manifold.tangentSpaceProdEquiv_mfderiv_prodMk_right, (A.val x).map_coord_zero 0 rfl,
    ((gaugeCurvature (GroupLieAlgebra.bracketL IG G) A).val x).map_coord_zero
      0 rfl]
  -- The zero of the model space `EG` is the zero of the Lie algebra.
  rw [show fundamentalVectorField (I := IG) (G := G) IF (0 : EG) = 0 from
    fundamentalVectorField_zero]
  -- `μ v` vanishes at the zero of `𝔤`; the zero here is that of `EG`, on which `momentMapCLM` is
  -- linear.
  rw [← momentMapCLM_apply μ hμ.toIsMomentMap.contMDiff_of_neg, map_zero]
  simp

/-- **Weinstein's construction.** Let `P` be a smooth principal `G`-bundle with a connection form
`A`, and let `G` act on a manifold `F` preserving a closed two-form `σ`, with an equivariant moment
map `μ` (in the sign convention `⟨dμ, ξ⟩ = -ι_{X_ξ} σ`, so that `-μ` is a moment map in Tau Ceti's
sense). Then there is a closed two-form `τ` on the associated bundle `P ×_G F` whose pull-back along
the quotient map `(x, v) ↦ [x, v]` is Weinstein's form `σ + d ⟨μ, A⟩`, and whose pull-back along
each fibre inclusion `v ↦ [x, v]` is `σ`; and Weinstein's form at `(x, v)` on `(a₁, b₁)` and
`(a₂, b₂)` is `σ_v(b₁ + X_{A a₁}(v), b₂ + X_{A a₂}(v)) + μ(v)(F_A(a₁, a₂))`, where `X_ξ` is the
fundamental vector field of `ξ` on `F` and `F_A` the curvature of `A`.

Milestone: *Weinstein's universal construction for associated symplectic fibrations*. -/
theorem exists_isClosed_mpullback_eq_weinsteinForm {σ : SmoothTwoForm IF F} (hσ : σ.IsClosed)
    {μ : F → Module.Dual ℝ (GroupLieAlgebra IG G)} (hμ : σ.IsEquivariantMomentMap fun v ↦ -μ v)
    (hσG : ∀ g : G, SmoothForm.mpullback (fun v : F ↦ g • v)
      (ContMDiffSMul.contMDiff_const_smul (I := IG) g) σ = σ)
    {hμs : ∀ ξ, ContMDiff IF 𝓘(ℝ) ∞ fun v ↦ μ v ξ}
    {A : SmoothForm (IB.prod IG) (ManifoldTotalSpace G P) EG 1}
    (hA : IsConnectionForm A) :
    ∃ τ : SmoothForm (IB.prod IF) (ManifoldTotalSpace F (AssociatedBundle G P F)) ℝ 2,
      τ.IsClosed ∧
      SmoothForm.mpullback (AssociatedBundle.chartedMk G F P)
        (AssociatedBundle.contMDiff_chartedMk ∞ IB IG IF) τ = weinsteinForm σ μ hμs A ∧
      (∀ x : ManifoldTotalSpace G P,
        SmoothForm.mpullback (fun v : F ↦ AssociatedBundle.chartedMk G F P (x, v))
          (AssociatedBundle.contMDiff_chartedMk_right ∞ IB IG IF x) τ = σ) ∧
      ∀ (p : ManifoldTotalSpace G P × F) (w₁ w₂ : TangentSpace ((IB.prod IG).prod IF) p),
        (weinsteinForm σ μ hμs A).val p ![w₁, w₂] =
          σ.val p.2 ![(Manifold.tangentSpaceProdEquiv p w₁).2 +
                fundamentalVectorField (I := IG) (G := G) IF
                  (A.val p.1 ![(Manifold.tangentSpaceProdEquiv p w₁).1])
                  p.2,
              (Manifold.tangentSpaceProdEquiv p w₂).2 +
                fundamentalVectorField (I := IG) (G := G) IF
                  (A.val p.1 ![(Manifold.tangentSpaceProdEquiv p w₂).1])
                  p.2] +
            μ p.2 ((gaugeCurvature (GroupLieAlgebra.bracketL IG G) A).val p.1
              ![(Manifold.tangentSpaceProdEquiv p w₁).1,
                (Manifold.tangentSpaceProdEquiv p w₂).1]) :=
  ⟨associatedForm σ hμ hσG hA, isClosed_associatedForm hσ hμ hσG hA,
    mpullback_chartedMk_associatedForm hμ hσG hA, mpullback_associatedForm_fiber hμ hσG hA,
    weinsteinForm_apply hμ A⟩

end SymplecticGeometry

end
