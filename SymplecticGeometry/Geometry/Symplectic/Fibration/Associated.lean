/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.ContMDiff.Dual
public import SymplecticGeometry.Geometry.Manifold.FiberBundle.Associated.PullbackPrincipal
public import SymplecticGeometry.Geometry.Manifold.FiberBundle.Principal.Connection.Basic
public import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.ContMDiff
public import TauCeti.Geometry.Manifold.DifferentialForm.Closed
public import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Smooth.Basic
public import TauCeti.Geometry.Symplectic.Hamiltonian.EquivariantMomentMap.Basic

/-!
# Weinstein's form on `P × F`

Let `P` be a smooth principal `G`-bundle over `B` with a connection form `A`, and let `G` act on
the left on a manifold `F` with a closed invariant two-form `σ` and a moment map `μ : F → 𝔤*`, in
the sign convention `⟨dμ, ξ⟩ = -ι_{X_ξ} σ` (so that `-μ` is a moment map in Tau Ceti's sense,
`TauCeti.SmoothTwoForm.IsEquivariantMomentMap`). On the product `P × F`, pairing `μ` with `A`
gives a real one-form `⟨μ, A⟩`, and **Weinstein's form** is the closed two-form

  `σ + d ⟨μ, A⟩`,

where `σ` stands for its pull-back along the projection to `F`. It is invariant under the diagonal
action `(x, v) ↦ (x · g, g⁻¹ • v)` of `G`, the action whose orbits are the fibres of the quotient
map `P × F → P ×_G F` (`TauCeti.AssociatedBundle.chartedMk`). So it is one of the two hypotheses
of the descent theorem `TauCeti.AssociatedBundle.existsUnique_mpullback_chartedMk_eq`.

## Main definitions

* `SymplecticGeometry.momentMapCLM μ hμs`: a map `μ : F → 𝔤*` with smooth components, as a smooth
  map to the continuous dual `𝔤 →L[ℝ] ℝ`.
* `SymplecticGeometry.momentPairing μ hμs A`: the one-form `⟨μ, A⟩` on `P × F`, the paired wedge
  of the zero-form `μ` with the pull-back of `A`, along the evaluation of `𝔤 →L[ℝ] ℝ` on `𝔤`.
* `SymplecticGeometry.weinsteinForm σ μ hμs A`: the two-form `σ + d ⟨μ, A⟩` on `P × F`.

## Main results

* `SymplecticGeometry.momentPairing_apply`: `⟨μ, A⟩_{(x, v)}(a, b) = μ(v)(A_x a)`.
* `SymplecticGeometry.isClosed_weinsteinForm`: Weinstein's form is closed.
* `SymplecticGeometry.mpullback_smul_momentPairing`: `⟨μ, A⟩` is invariant under the diagonal
  action when `A` is equivariant and `μ` is coadjoint-equivariant.
* `SymplecticGeometry.mpullback_smul_weinsteinForm`: Weinstein's form is invariant under the
  diagonal action of `G`.

## Implementation notes

The definitions take the smoothness of the components of `μ` as the argument `hμs`, which is all
they need; the theorems take it as an implicit argument, so that it is never asked for beside the
moment map hypothesis, from which it follows
(`TauCeti.SmoothTwoForm.IsMomentMap.contMDiff_of_neg`). The pairing turns `μ` into a map to
`𝔤 →L[ℝ] ℝ`, which is smooth since `𝔤` is finite-dimensional
(`SymplecticGeometry.contMDiff_toContinuousLinearMap_of_contMDiff_apply`).
Closedness needs only that `σ` is closed; invariance needs the
equivariance of `A` and of `μ`, and the invariance of `σ`, which Tau Ceti's moment maps
do not include. The norm on `𝔤` is the scoped one of
`SymplecticGeometry.Geometry.Lie.GroupLieAlgebra.Normed`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §6.3
  (Theorem 6.3.3 and the form (6.3.1)).
* [A. Weinstein, *A universal phase space for particles in Yang–Mills fields*][Weinstein1978].
-/

public section

noncomputable section

open Bundle Manifold MulOpposite TauCeti TauCeti.Lie
open scoped Manifold ContDiff GroupLieAlgebra

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
`𝔤 →L[ℝ] ℝ`: the Lie algebra is finite-dimensional, so every linear form on it is continuous. -/
def momentMapCLM (μ : F → Module.Dual ℝ (GroupLieAlgebra IG G))
    (hμs : ∀ ξ, ContMDiff IF 𝓘(ℝ) ∞ fun v ↦ μ v ξ) :
    C^∞⟮IF, F; 𝓘(ℝ, GroupLieAlgebra IG G →L[ℝ] ℝ), GroupLieAlgebra IG G →L[ℝ] ℝ⟯ where
  val v := LinearMap.toContinuousLinearMap (μ v)
  property := contMDiff_toContinuousLinearMap_of_contMDiff_apply hμs

@[simp]
theorem momentMapCLM_apply (μ : F → Module.Dual ℝ (GroupLieAlgebra IG G))
    (hμs : ∀ ξ, ContMDiff IF 𝓘(ℝ) ∞ fun v ↦ μ v ξ) (v : F) (ξ : GroupLieAlgebra IG G) :
    momentMapCLM μ hμs v ξ = μ v ξ :=
  (rfl)

variable [IsManifold IF ∞ F] [LieGroup IG ∞ G] [ContMDiffFiberBundle ∞ G P IB IG]

/-- The **pairing** `⟨μ, A⟩` of a map `μ : F → 𝔤*` with smooth components and a `𝔤`-valued
one-form `A` on the total space of `P`: the real one-form on `P × F` whose value at `(x, v)` on a
tangent vector `(a, b)` is `μ(v)(A_x a)` (`momentPairing_apply`). It is the paired wedge, along
the evaluation of `𝔤 →L[ℝ] ℝ` on `𝔤`, of the zero-form `(x, v) ↦ μ(v)` with the pull-back of `A`
along the first projection. -/
def momentPairing (μ : F → Module.Dual ℝ (GroupLieAlgebra IG G))
    (hμs : ∀ ξ, ContMDiff IF 𝓘(ℝ) ∞ fun v ↦ μ v ξ)
    (A : SmoothForm (IB.prod IG) (ManifoldTotalSpace G P) (GroupLieAlgebra IG G) 1) :
    SmoothForm ((IB.prod IG).prod IF) (ManifoldTotalSpace G P × F) ℝ 1 :=
  SmoothForm.wedgeWith (ContinuousLinearMap.id ℝ (GroupLieAlgebra IG G →L[ℝ] ℝ))
    (SmoothForm.mpullback Prod.snd contMDiff_snd (SmoothForm.ofFunction (momentMapCLM μ hμs)))
    (SmoothForm.mpullback Prod.fst contMDiff_fst A)

theorem momentPairing_def (μ : F → Module.Dual ℝ (GroupLieAlgebra IG G))
    (hμs : ∀ ξ, ContMDiff IF 𝓘(ℝ) ∞ fun v ↦ μ v ξ)
    (A : SmoothForm (IB.prod IG) (ManifoldTotalSpace G P) (GroupLieAlgebra IG G) 1) :
    momentPairing μ hμs A =
      SmoothForm.wedgeWith (ContinuousLinearMap.id ℝ (GroupLieAlgebra IG G →L[ℝ] ℝ))
        (SmoothForm.mpullback Prod.snd contMDiff_snd (SmoothForm.ofFunction (momentMapCLM μ hμs)))
        (SmoothForm.mpullback Prod.fst contMDiff_fst A) :=
  (rfl)

/-- The pairing `⟨μ, A⟩` at `(x, v)` on a tangent vector `(a, b)` is `μ(v)(A_x a)`. -/
theorem momentPairing_apply (μ : F → Module.Dual ℝ (GroupLieAlgebra IG G))
    (hμs : ∀ ξ, ContMDiff IF 𝓘(ℝ) ∞ fun v ↦ μ v ξ)
    (A : SmoothForm (IB.prod IG) (ManifoldTotalSpace G P) (GroupLieAlgebra IG G) 1)
    (p : ManifoldTotalSpace G P × F) (w : TangentSpace ((IB.prod IG).prod IF) p) :
    (momentPairing μ hμs A).val p ![w] = μ p.2 (A.val p.1 ![w.1]) := by
  rw [momentPairing_def, SmoothForm.wedgeWith_flip, SmoothForm.wedgeWith_apply_zero_right]
  simp only [Nat.zero_mul, pow_zero, one_smul, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.id_apply, SmoothForm.mpullback_apply, SmoothForm.coe_ofFunction,
    RoughForm.ofFunction_apply, Function.comp_apply, mfderiv_fst, momentMapCLM_apply]
  congr 2
  funext i
  fin_cases i
  -- The tangent space of the product is the product of the tangent spaces by definition.
  rfl

/-! ### Weinstein's form -/

/-- **Weinstein's form** `σ + d ⟨μ, A⟩` on `P × F`, for a two-form `σ` on `F`, a map `μ : F → 𝔤*`
with smooth components and a `𝔤`-valued one-form `A` on the total space of `P`; here `σ` stands
for its pull-back along the projection to `F`. -/
def weinsteinForm (σ : SmoothTwoForm IF F) (μ : F → Module.Dual ℝ (GroupLieAlgebra IG G))
    (hμs : ∀ ξ, ContMDiff IF 𝓘(ℝ) ∞ fun v ↦ μ v ξ)
    (A : SmoothForm (IB.prod IG) (ManifoldTotalSpace G P) (GroupLieAlgebra IG G) 1) :
    SmoothForm ((IB.prod IG).prod IF) (ManifoldTotalSpace G P × F) ℝ 2 :=
  SmoothForm.mpullback Prod.snd contMDiff_snd σ +
    mextDerivₗ ((IB.prod IG).prod IF) 1 (momentPairing μ hμs A)

theorem weinsteinForm_def (σ : SmoothTwoForm IF F)
    (μ : F → Module.Dual ℝ (GroupLieAlgebra IG G))
    (hμs : ∀ ξ, ContMDiff IF 𝓘(ℝ) ∞ fun v ↦ μ v ξ)
    (A : SmoothForm (IB.prod IG) (ManifoldTotalSpace G P) (GroupLieAlgebra IG G) 1) :
    weinsteinForm σ μ hμs A =
      SmoothForm.mpullback Prod.snd contMDiff_snd σ +
        mextDerivₗ ((IB.prod IG).prod IF) 1 (momentPairing μ hμs A) :=
  (rfl)

/-- **Weinstein's form is closed** when `σ` is. -/
theorem isClosed_weinsteinForm {σ : SmoothTwoForm IF F} (hσ : σ.IsClosed)
    {μ : F → Module.Dual ℝ (GroupLieAlgebra IG G)} {hμs : ∀ ξ, ContMDiff IF 𝓘(ℝ) ∞ fun v ↦ μ v ξ}
    (A : SmoothForm (IB.prod IG) (ManifoldTotalSpace G P) (GroupLieAlgebra IG G) 1) :
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
    {A : SmoothForm (IB.prod IG) (ManifoldTotalSpace G P) (GroupLieAlgebra IG G) 1}
    (hA : ∀ g : G, SmoothForm.mpullback (fun x : ManifoldTotalSpace G P ↦ op g • x)
      (contMDiff_const_smul (op g)) A = SmoothForm.mapCoeff (adjointContinuousLinearMap g⁻¹) A)
    (g : G) :
    SmoothForm.mpullback (fun x : ManifoldTotalSpace G P × F ↦ (op g • x.1, g⁻¹ • x.2))
      (AssociatedBundle.contMDiff_op_smul_inv_smul g) (momentPairing μ hμs A) =
      momentPairing μ hμs A := by
  have h1 : SmoothForm.mpullback (fun x : ManifoldTotalSpace G P × F ↦ (op g • x.1, g⁻¹ • x.2))
      (AssociatedBundle.contMDiff_op_smul_inv_smul (IB := IB) (IG := IG) (IF := IF) g)
      (SmoothForm.mpullback Prod.fst contMDiff_fst A) =
      SmoothForm.mpullback Prod.fst contMDiff_fst
        (SmoothForm.mapCoeff (adjointContinuousLinearMap g⁻¹) A) := by
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
    (ContinuousLinearMap.id ℝ (GroupLieAlgebra IG G →L[ℝ] ℝ)) _
    (AssociatedBundle.contMDiff_op_smul_inv_smul (IB := IB) (IG := IG) (IF := IF) (P := P)
      (F := F) g) _ _).trans ?_
  rw [h1, h2]
  apply Subtype.ext
  funext p
  ext w
  rw [SmoothForm.wedgeWith_flip, SmoothForm.wedgeWith_apply_zero_right,
    SmoothForm.wedgeWith_flip, SmoothForm.wedgeWith_apply_zero_right]
  simp only [Nat.zero_mul, pow_zero, one_smul, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.id_apply, SmoothForm.mpullback_apply, SmoothForm.coe_ofFunction,
    RoughForm.ofFunction_apply, SmoothForm.coe_mapCoeff, RoughForm.mapCoeff_apply,
    momentMapCLM_apply, hμG, adjointContinuousLinearMap_adjointContinuousLinearMap_inv]

/-- **Weinstein's form is invariant** under the diagonal action `(x, v) ↦ (x · g, g⁻¹ • v)` of `G`
on `P × F`, for a connection form `A`, a two-form `σ` invariant under `G` and an equivariant moment
map `μ` (in the sign convention where `-μ` is a moment map in Tau Ceti's sense). -/
theorem mpullback_smul_weinsteinForm [CompleteSpace EF] {σ : SmoothTwoForm IF F}
    {μ : F → Module.Dual ℝ (GroupLieAlgebra IG G)} (hμ : σ.IsEquivariantMomentMap fun v ↦ -μ v)
    (hσG : ∀ g : G, SmoothForm.mpullback (fun v : F ↦ g • v)
      (ContMDiffSMul.contMDiff_const_smul (I := IG) g) σ = σ)
    {hμs : ∀ ξ, ContMDiff IF 𝓘(ℝ) ∞ fun v ↦ μ v ξ}
    {A : SmoothForm (IB.prod IG) (ManifoldTotalSpace G P) (GroupLieAlgebra IG G) 1}
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

end SymplecticGeometry

end
