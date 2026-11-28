/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.KempfNess.Basic
public import TauCeti.Geometry.Lie.FundamentalVectorField.Isotropy
public import Mathlib.Analysis.InnerProductSpace.Orthogonal
public import TauCeti.Geometry.Manifold.GroupAction.TangentRepresentation
public import TauCeti.LinearAlgebra.TotallyReal.Basic
public import TauCeti.RepresentationTheory.Continuous.Unitary.Basic
public import SymplecticGeometry.Geometry.Manifold.GroupAction.OrbitTube
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Geometry.Manifold.VectorField.Pullback
import SymplecticGeometry.Analysis.Normed.Operator.FinrankKer
import SymplecticGeometry.Geometry.Lie.FundamentalVectorField
import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.KempfNess.HolomorphicChart
import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.KempfNess.Stabilizer
import TauCeti.RepresentationTheory.Continuous.InvariantComplement
import SymplecticGeometry.Geometry.Manifold.GroupAction.TangentRepresentation.AlmostComplex

/-!
# The normal space of the complex orbit and the slice operator at a zero of the moment map

Suppose that `G` is a Lie group acting on `M`, which carries a two-form `σ`, an almost complex
structure `J` and a metric with `g(u, w) = σ(u, J w)`, and let `W = 𝔤 · x` be the orbit
tangent space at `x` (`TauCeti.InfinitesimalAction.orbitTangent`). This file studies the
**complex orbit tangent space** `T = W + J x W` (`SymplecticGeometry.complexOrbitTangent`)
and its orthogonal complement `S = Tᗮ` for `g`, the **complex orbit normal space**
(`SymplecticGeometry.complexOrbitNormal`).
These are the linear objects of the holomorphic slice at a zero of the moment map in the proof
of Theorem 12.5 of [GeorgoulasRobbinSalamon2021] (Steps 2–5 there), in the spirit of the
holomorphic slice theorem of Sjamaar (§1 of his paper below); the later steps read `S` in a
linearizing chart at `x`, whose derivative at `x` is the identity of `E' = T_x M`.

For a complexified action of a complexification `Gc` of `G`, `T` is the orbit tangent space of
`Gc` at `x` (`SymplecticGeometry.IsComplexifiedAction.orbitTangent_eq_complexOrbitTangent`),
since `X_ζ = X_{re ζ} + J X_{im ζ}`. If `-μ` is an equivariant moment map and `μ x = 0`, the
orbit through `x` is isotropic, `σ_x(X_ξ, X_η) = -μ x ⁅ξ, η⁆ = 0`, so `W` and `J x W` are
orthogonal for `g`
(`SymplecticGeometry.inner_fundamentalVectorField_almostComplex_eq_zero_of_moment_eq_zero`, in
`KempfNess/Basic.lean`), and in particular `W` is totally real for `J x`: it meets
`J x W` only in `0`
(`SymplecticGeometry.isTotallyReal_orbitTangent_of_moment_eq_zero`).

The space `S` is a complement of `T` (`SymplecticGeometry.isCompl_complexOrbitTangent`) and is
invariant under `J x` (`SymplecticGeometry.apply_mem_complexOrbitNormal`), since `J x` preserves
`T` and `g`. If the stabilizer `H` of `x` preserves `σ` and `J`, then each `dh_x` preserves `W`
and `g`: the tangent representation of `H` is unitary
(`SymplecticGeometry.isUnitary_tangentRepresentation`), so `S` is invariant under `dh_x`
(`SymplecticGeometry.mfderiv_smul_apply_mem_complexOrbitNormal`, through Tau Ceti's
`TauCeti.ContRepresentation.IsUnitary.apply_mem_orthogonal`), and, differentiating along
`exp (t ξ)`, under the linearized isotropy action `A_ξ` for `ξ` in the isotropy algebra
(`SymplecticGeometry.isotropyLinearization_apply_mem_complexOrbitNormal`), through Tau Ceti's
`TauCeti.isotropyLinearization_apply_mem_of_forall_mem`, as in Tau Ceti's
`TauCeti.SmoothTwoForm.IsNondegenerate.isotropyLinearization_apply_mem_orthogonal`. This is the
invariance that equation (12.6) of [GeorgoulasRobbinSalamon2021] gives,
`A_ξ (X_η x) = X_⁅ξ, η⁆ x` with `A_ξ` skew.

Tau Ceti's symplectic slice `TauCeti.SmoothTwoForm.IsNondegenerate.SymplecticSlice` is the
quotient `W^σ ⧸ (W ∩ W^σ)` of the `σ_x`-orthogonal of `W`, which `J x` does not preserve; the
later steps of the proof need a `J x`-invariant subspace of `T_x M` on which `H` acts, which is
why `S` is taken as the `g`-orthogonal complement of `T` instead.

In a linearizing chart `e` at `x` (`SymplecticGeometry.LinearizingChart`), the **slice operator**
at `v` (`SymplecticGeometry.sliceOperator`) is `(Z, w) ↦ X_Z (e.symm v) - d(e.symm)_v w` on the
product of the Lie algebra of `Gc` and `S`. Step 2 of the proof of Theorem 12.5 of
[GeorgoulasRobbinSalamon2021] computes its kernel for `v ∈ S` near `0`, when `J` is constant in
`e` (`SymplecticGeometry.ker_sliceOperator_eq`): it consists of the pairs
`(C.lieMap ξ + C.cplx (C.lieMap η), A_ξ v + J x (A_η v))` with `ξ, η` in the isotropy algebra
`𝔥` of `x`. These pairs lie in the kernel by `SymplecticGeometry.fundamentalVectorField_chart_symm`
(`SymplecticGeometry.sliceOperator_apply_eq_zero`) and form a space of dimension `2 dim 𝔥`. At
`v = 0` they make up the whole kernel, since `S` meets `T` only in `0` and the isotropy algebra of
`x` in `Gc` is `C.lieMap 𝔥 ⊕ C.cplx (C.lieMap 𝔥)`
(`SymplecticGeometry.mem_ker_sliceOperator_zero_iff`, through
`TauCeti.InfinitesimalAction.apply_add_eq_zero_iff`). The source argues that the operator
is onto near `0`; here the same count is made through the kernel: read through the inverse of
`d(e.symm)_v`, which is invertible on the target of `e`
(`SymplecticGeometry.LinearizingChart.isInvertible_mfderiv_chart_symm`), the operator is
`(Z, w) ↦ Y_Z v - w` with `Y_Z` the pull-back of `X_Z` by `e.symm`, which depends continuously on
`v`, so the dimension of its kernel can only go down near `0`
(`SymplecticGeometry.eventually_finrank_ker_sliceOperator_le`, through
`LinearMap.eventually_finrank_ker_le`).

At a zero of the moment map, for a complement `K` of the isotropy algebra `𝔥` of `x` (such as
its orthogonal complement `𝔥ᗮ` for a positive definite symmetric form `B`,
`LinearMap.BilinForm.isCompl_orthogonal_of_anisotropic`), the linear map
`(α, β, v) ↦ J x (X_α x) + X_β x + v` from `K × K × S` to `T_x M`
(`SymplecticGeometry.complexOrbitSliceMap`) is bijective
(`SymplecticGeometry.bijective_complexOrbitSliceMap`). For a complexified action it is the
derivative at `0` of `(α, β, v) ↦ C.expI α * C.toHom (mulInvariantExp β) • e.symm v` in a
linearizing chart `e`, since `X_{i ξ} = J X_ξ`; this is the linear part of Step 3 of the proof of
Theorem 12.5 of [GeorgoulasRobbinSalamon2021]. Injectivity uses that `W` is totally real and
that `T` meets `S` only in `0`; surjectivity, that `K` maps onto `W`.

## Main definitions

* `SymplecticGeometry.complexOrbitTangent I G J x`: the subspace `W + J x W` of `T_x M`.
* `SymplecticGeometry.complexOrbitNormal I G J x`: its orthogonal complement for the metric.
* `SymplecticGeometry.sliceOperator IC Gc e S v`: the slice operator of a linearizing chart.
* `SymplecticGeometry.complexOrbitSliceMap I G J x K`: the linear map
  `(α, β, v) ↦ J x (X_α x) + X_β x + v` on `K × K × S`.
* `SymplecticGeometry.complexOrbitSliceEquiv`: the same map as a linear equivalence, at a zero of
  the moment map and for a complement `K` of the isotropy algebra.

## Main results

* `SymplecticGeometry.IsComplexifiedAction.orbitTangent_eq_complexOrbitTangent`: for a
  complexified action, the orbit tangent space of `Gc` is `W + J x W`.
* `SymplecticGeometry.isTotallyReal_orbitTangent_of_moment_eq_zero`: at a zero of the moment map,
  `W` is totally real for `J x`.
* `SymplecticGeometry.isCompl_complexOrbitTangent`: `T` and `S` are complementary.
* `SymplecticGeometry.apply_mem_complexOrbitNormal`: `S` is `J x`-invariant.
* `SymplecticGeometry.isUnitary_tangentRepresentation`: the stabilizer acts on `T_x M` by
  isometries.
* `SymplecticGeometry.mfderiv_smul_apply_mem_complexOrbitNormal`: `S` is invariant under the
  differentials at `x` of the elements of the stabilizer.
* `SymplecticGeometry.isotropyLinearization_apply_mem_complexOrbitNormal`: `S` is invariant under
  the linearized isotropy action.
* `SymplecticGeometry.ker_sliceOperator_eq`: the kernel of the slice operator near `0`.
* `SymplecticGeometry.bijective_complexOrbitSliceMap`: at a zero of the moment map, the map
  `(α, β, v) ↦ J x (X_α x) + X_β x + v` is bijective for every complement `K` of the isotropy
  algebra.

## References

* [V. Georgoulas, J. W. Robbin and D. A. Salamon, *The moment-weight inequality and the
  Hilbert–Mumford criterion*][GeorgoulasRobbinSalamon2021], arXiv v2, proof of Theorem 12.5.
* R. Sjamaar, *Holomorphic slices, symplectic reduction and multiplicities of
  representations*, Ann. of Math. (2) 141 (1995), 87–129, §1.
-/

public section

noncomputable section

open Set Manifold MulAction TauCeti _root_.Bundle
open scoped Manifold ContDiff RealInnerProductSpace Topology

namespace SymplecticGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M]
  [MulAction G M] [ContMDiffSMul I I' ∞ G M]

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

/-! ### The complex orbit tangent space -/

omit [CompleteSpace E'] in
/-- A vector lies in the image of a subspace `W` of `T_x M` under `J x` exactly when it is `J x w`
for some `w ∈ W`. -/
theorem _root_.TauCeti.SmoothAlmostComplexStructure.mem_map_toEndomorphism_iff
    {J : SmoothAlmostComplexStructure I' M} {x : M} {W : Submodule ℝ (TangentSpace I' x)}
    {v : TangentSpace I' x} :
    v ∈ W.map (J.toEndomorphism x).toLinearMap ↔ ∃ w ∈ W, J x w = v :=
  Submodule.mem_map

variable (I G) in
/-- The **complex orbit tangent space** at `x`: the sum `W + J x W` of the orbit tangent space
`W = 𝔤 · x` of the action of `G` and its image under `J x`. For a complexified action it is the
orbit tangent space of the complexification
(`SymplecticGeometry.IsComplexifiedAction.orbitTangent_eq_complexOrbitTangent`). -/
def complexOrbitTangent (J : SmoothAlmostComplexStructure I' M) (x : M) :
    Submodule ℝ (TangentSpace I' x) :=
  (InfinitesimalAction.fundamental I G I' M).orbitTangent x ⊔
    ((InfinitesimalAction.fundamental I G I' M).orbitTangent x).map (J.toEndomorphism x).toLinearMap

theorem complexOrbitTangent_def (J : SmoothAlmostComplexStructure I' M) (x : M) :
    complexOrbitTangent I G J x =
      (InfinitesimalAction.fundamental I G I' M).orbitTangent x ⊔
        ((InfinitesimalAction.fundamental I G I' M).orbitTangent x).map
          (J.toEndomorphism x).toLinearMap :=
  (rfl)

/-- A vector lies in the complex orbit tangent space at `x` exactly when it is
`X_ξ x + J x (X_η x)` for some `ξ, η` in the Lie algebra of `G`. -/
theorem mem_complexOrbitTangent_iff {J : SmoothAlmostComplexStructure I' M} {x : M}
    {v : TangentSpace I' x} :
    v ∈ complexOrbitTangent I G J x ↔ ∃ ξ η : GroupLieAlgebra I G,
      fundamentalVectorField I' ξ x + J x (fundamentalVectorField I' η x) = v := by
  simp only [complexOrbitTangent_def, Submodule.mem_sup,
    SmoothAlmostComplexStructure.mem_map_toEndomorphism_iff,
    InfinitesimalAction.orbitTangent_eq_range, LinearMap.mem_range,
    InfinitesimalAction.eval_apply, InfinitesimalAction.fundamental_apply]
  constructor
  · rintro ⟨_, ⟨ξ, rfl⟩, _, ⟨_, ⟨η, rfl⟩, rfl⟩, rfl⟩
    exact ⟨ξ, η, rfl⟩
  · rintro ⟨ξ, η, rfl⟩
    exact ⟨_, ⟨ξ, rfl⟩, _, ⟨_, ⟨η, rfl⟩, rfl⟩, rfl⟩

/-- The complex orbit tangent space is invariant under `J x`. -/
theorem apply_mem_complexOrbitTangent {J : SmoothAlmostComplexStructure I' M} {x : M}
    {v : TangentSpace I' x} (hv : v ∈ complexOrbitTangent I G J x) :
    J x v ∈ complexOrbitTangent I G J x := by
  obtain ⟨ξ, η, rfl⟩ := mem_complexOrbitTangent_iff.1 hv
  refine mem_complexOrbitTangent_iff.2 ⟨-η, ξ, ?_⟩
  -- `J x` is the coercion of the continuous linear map `J.toEndomorphism x`, whose `map_add`
  -- applies once the coercion is unfolded: Tau Ceti states no `map_add` for `J x` itself.
  have h1 : J x (fundamentalVectorField I' ξ x + J x (fundamentalVectorField I' η x)) =
      J x (fundamentalVectorField I' ξ x) + J x (J x (fundamentalVectorField I' η x)) :=
    map_add (J.toEndomorphism x) _ _
  rw [h1, SmoothAlmostComplexStructure.apply_apply, fundamentalVectorField_neg,
    Pi.neg_apply]
  abel

section Complexification

variable {EC : Type*} [NormedAddCommGroup EC] [NormedSpace ℝ EC] [CompleteSpace EC]
  {HC : Type*} [TopologicalSpace HC] {IC : ModelWithCorners ℝ EC HC}
  {Gc : Type*} [TopologicalSpace Gc] [ChartedSpace HC Gc] [Group Gc] [LieGroup IC ∞ Gc]
  [T2Space Gc] [MulAction Gc M] [ContMDiffSMul IC I' ∞ Gc M]

/-- **The orbit tangent space of a complexified action.** For a complexified action of `Gc`, the
orbit tangent space of `Gc` at `x` is the complex orbit tangent space `W + J x W` of `G`: the
fundamental vector field of `ζ` is `X_{C.re ζ} + J X_{C.im ζ}`, and that of
`C.lieMap ξ + C.cplx (C.lieMap η)` is `X_ξ + J X_η`. -/
theorem IsComplexifiedAction.orbitTangent_eq_complexOrbitTangent [FiniteDimensional ℝ E]
    {C : LieComplexification I G IC Gc} {J : SmoothAlmostComplexStructure I' M}
    (h : IsComplexifiedAction C J) (x : M) :
    (InfinitesimalAction.fundamental IC Gc I' M).orbitTangent x = complexOrbitTangent I G J x := by
  ext v
  simp only [InfinitesimalAction.orbitTangent_eq_range, LinearMap.mem_range,
    InfinitesimalAction.eval_apply, InfinitesimalAction.fundamental_apply,
    mem_complexOrbitTangent_iff]
  constructor
  · rintro ⟨ζ, rfl⟩
    exact ⟨C.re ζ, C.im ζ, (h.fundamentalVectorField_eq_re_add_im ζ x).symm⟩
  · rintro ⟨ξ, η, rfl⟩
    refine ⟨C.lieMap ξ + C.cplx (C.lieMap η), ?_⟩
    rw [fundamentalVectorField_add, Pi.add_apply, h.fundamentalVectorField_cplx_lieMap,
      congrFun (h.fundamentalVectorField_lieMap ξ) x]

end Complexification

/-! ### The complex orbit normal space -/

variable [RiemannianBundle (fun x : M ↦ TangentSpace I' x)]

variable (I G) in
/-- The **complex orbit normal space** at `x`: the orthogonal complement, for the metric, of the
complex orbit tangent space `W + J x W` (`SymplecticGeometry.complexOrbitTangent`). At a zero of
the moment map it is the linear slice of the holomorphic slice theorem: a `J x`-invariant
complement of `W + J x W`, invariant under the stabilizer of `x`. -/
def complexOrbitNormal (J : SmoothAlmostComplexStructure I' M) (x : M) :
    Submodule ℝ (TangentSpace I' x) :=
  (complexOrbitTangent I G J x)ᗮ

theorem complexOrbitNormal_def (J : SmoothAlmostComplexStructure I' M) (x : M) :
    complexOrbitNormal I G J x = (complexOrbitTangent I G J x)ᗮ :=
  (rfl)

theorem mem_complexOrbitNormal_iff {J : SmoothAlmostComplexStructure I' M} {x : M}
    {v : TangentSpace I' x} :
    v ∈ complexOrbitNormal I G J x ↔ ∀ u ∈ complexOrbitTangent I G J x, ⟪u, v⟫ = 0 := by
  rw [complexOrbitNormal_def, Submodule.mem_orthogonal]

variable [FiniteDimensional ℝ E]

/-- **The orbit tangent space is totally real at a zero of the moment map**: if `-μ` is an
equivariant moment map for `σ`, the metric is `g(u, w) = σ(u, J w)` and `μ x = 0`, then the
orbit tangent space `W` meets its image under `J x` only in `0`. -/
theorem isTotallyReal_orbitTangent_of_moment_eq_zero {σ : SmoothTwoForm I' M}
    {J : SmoothAlmostComplexStructure I' M} {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)}
    (hμ : σ.IsEquivariantMomentMap fun x ↦ -μ x)
    (hg : ∀ x (u w : TangentSpace I' x), ⟪u, w⟫ = σ.eval₂ x u (J x w)) {x : M} (hx : μ x = 0) :
    IsTotallyReal (J.toEndomorphism x).toLinearMap
      ((InfinitesimalAction.fundamental I G I' M).orbitTangent x) := by
  rw [isTotallyReal_iff, Submodule.disjoint_def]
  simp only [SmoothAlmostComplexStructure.mem_map_toEndomorphism_iff,
    InfinitesimalAction.orbitTangent_eq_range, LinearMap.mem_range,
    InfinitesimalAction.eval_apply, InfinitesimalAction.fundamental_apply]
  rintro v ⟨ξ, rfl⟩ ⟨_, ⟨η, rfl⟩, hv⟩
  have h := inner_fundamentalVectorField_almostComplex_eq_zero_of_moment_eq_zero hμ hg hx ξ η
  simp only [hv] at h
  exact inner_self_eq_zero.1 h

instance (J : SmoothAlmostComplexStructure I' M) (x : M) :
    FiniteDimensional ℝ (complexOrbitTangent I G J x) := by
  rw [complexOrbitTangent_def, InfinitesimalAction.orbitTangent_eq_range]
  infer_instance

/-- The complex orbit tangent space and the complex orbit normal space are complementary. -/
theorem isCompl_complexOrbitTangent (J : SmoothAlmostComplexStructure I' M) (x : M) :
    IsCompl (complexOrbitTangent I G J x) (complexOrbitNormal I G J x) :=
  Submodule.isCompl_orthogonal _

omit [FiniteDimensional ℝ E] in
/-- The complex orbit normal space is closed. -/
theorem isClosed_complexOrbitNormal (J : SmoothAlmostComplexStructure I' M) (x : M) :
    IsClosed (complexOrbitNormal I G J x : Set (TangentSpace I' x)) :=
  Submodule.isClosed_orthogonal _

omit [FiniteDimensional ℝ E] in
/-- **The complex orbit normal space is `J x`-invariant**, for a metric with
`g(u, w) = σ(u, J w)`: `J x` preserves the complex orbit tangent space and the metric. -/
theorem apply_mem_complexOrbitNormal {σ : SmoothTwoForm I' M}
    {J : SmoothAlmostComplexStructure I' M}
    (hg : ∀ x (u w : TangentSpace I' x), ⟪u, w⟫ = σ.eval₂ x u (J x w)) {x : M}
    {v : TangentSpace I' x} (hv : v ∈ complexOrbitNormal I G J x) :
    J x v ∈ complexOrbitNormal I G J x := by
  rw [mem_complexOrbitNormal_iff] at hv ⊢
  intro u hu
  have h := hv _ (apply_mem_complexOrbitTangent hu)
  rw [← SmoothAlmostComplexStructure.inner_apply_apply_of_inner_eq hg x u,
    SmoothAlmostComplexStructure.apply_apply, inner_neg_right, h, neg_zero]

omit [CompleteSpace E] [LieGroup I ∞ G] [CompleteSpace E'] [FiniteDimensional ℝ E] in
/-- **The stabilizer acts by isometries.** Let the stabilizer of `x` preserve the two-form `σ`
and the almost complex structure `J`, and let the metric be `g(u, w) = σ(u, J w)`. Then the
tangent representation of the stabilizer on `T_x M` is unitary for the metric. -/
theorem isUnitary_tangentRepresentation {σ : SmoothTwoForm I' M}
    {J : SmoothAlmostComplexStructure I' M} {x : M}
    (hd : ∀ g ∈ stabilizer G x, MDifferentiableAt I' I' (fun y : M ↦ g • y) x)
    (hσG : ∀ g ∈ stabilizer G x, SmoothForm.mpullback (fun y : M ↦ g • y)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ)
    (hJG : ∀ g ∈ stabilizer G x, ∀ v : TangentSpace I' x,
      mfderiv I' I' (fun y : M ↦ g • y) x (J x v) =
        J (g • x) (mfderiv I' I' (fun y : M ↦ g • y) x v))
    (hg : ∀ x (u w : TangentSpace I' x), ⟪u, w⟫ = σ.eval₂ x u (J x w)) :
    (tangentRepresentation hd).IsUnitary := by
  -- `IsUnitary` asks that each action map preserve the inner product. Its body is not exposed to
  -- this file, so the goal is reached through Tau Ceti's equivalent statement for norms.
  refine (ContRepresentation.isUnitary_iff_norm_map _).2 fun k ↦
    (LinearMap.norm_map_iff_inner_map_map (tangentRepresentation hd k)).2 fun u w ↦ ?_
  have hkx : (k : G) • x = x := k.property
  have hJ := tangentRepresentation_apply_almostComplex hd (hJG k k.property) w
  have h := SmoothForm.eval₂_mpullback (fun y : M ↦ (k : G) • y)
    (ContMDiffSMul.contMDiff_const_smul (I := I) (k : G)) σ x u (J x w)
  rw [hσG k k.property, hkx] at h
  rw [hg, hg, ← hJ, h, tangentRepresentation_apply]

omit [FiniteDimensional ℝ E] in
/-- **The complex orbit normal space is invariant under the stabilizer.** Let the stabilizer of
`x` preserve the two-form `σ` and the almost complex structure `J`, and let the metric be
`g(u, w) = σ(u, J w)`. Then for `g` in the stabilizer, the differential `dg_x` maps the complex
orbit normal space at `x` into itself: it preserves the orbit tangent space, commutes with `J x`,
and preserves the metric. -/
theorem mfderiv_smul_apply_mem_complexOrbitNormal {σ : SmoothTwoForm I' M}
    {J : SmoothAlmostComplexStructure I' M} {x : M}
    (hσG : ∀ g ∈ stabilizer G x, SmoothForm.mpullback (fun y : M ↦ g • y)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ)
    (hJG : ∀ g ∈ stabilizer G x, ∀ v : TangentSpace I' x,
      mfderiv I' I' (fun y : M ↦ g • y) x (J x v) =
        J (g • x) (mfderiv I' I' (fun y : M ↦ g • y) x v))
    (hg : ∀ x (u w : TangentSpace I' x), ⟪u, w⟫ = σ.eval₂ x u (J x w))
    {g : G} (hgx : g ∈ stabilizer G x) {v : TangentSpace I' x}
    (hv : v ∈ complexOrbitNormal I G J x) :
    ((mfderiv I' I' (fun y : M ↦ g • y) x : E' →L[ℝ] E') v : TangentSpace I' x) ∈
      complexOrbitNormal I G J x := by
  have hd : ∀ g ∈ stabilizer G x, MDifferentiableAt I' I' (fun y : M ↦ g • y) x :=
    fun g _ ↦ ContMDiffSMul.mdifferentiable_const_smul (I := I) (n := ∞) (by simp) g x
  set ρ := tangentRepresentation hd
  -- Each `ρ k = dk_x` commutes with `J x`.
  have hJ (k : stabilizer G x) (u : TangentSpace I' x) : ρ k (J x u) = J x (ρ k u) :=
    tangentRepresentation_apply_almostComplex hd (hJG k k.property) u
  -- Each `ρ k` preserves the complex orbit tangent space.
  have hT (k : stabilizer G x) {u : TangentSpace I' x} (hu : u ∈ complexOrbitTangent I G J x) :
      (ρ k u : TangentSpace I' x) ∈ complexOrbitTangent I G J x := by
    rw [complexOrbitTangent_def, Submodule.mem_sup] at hu ⊢
    obtain ⟨a, ha, _, ⟨b, hb, rfl⟩, rfl⟩ := hu
    refine ⟨ρ k a, tangentRepresentation_mem_orbitTangent_fundamental hd k ha, _,
      ⟨ρ k b, tangentRepresentation_mem_orbitTangent_fundamental hd k hb, (hJ k b).symm⟩,
      (map_add (ρ k) a _).symm⟩
  have hρ : (mfderiv I' I' (fun y : M ↦ g • y) x : E' →L[ℝ] E') = ρ ⟨g, hgx⟩ :=
    (tangentRepresentation_apply hd ⟨g, hgx⟩).symm
  rw [hρ]
  rw [complexOrbitNormal_def] at hv ⊢
  exact (isUnitary_tangentRepresentation (I := I) hd hσG hJG hg).apply_mem_orthogonal
    (fun k _ hu ↦ hT k hu) ⟨g, hgx⟩ hv

omit [FiniteDimensional ℝ E] in
/-- **The complex orbit normal space is invariant under the isotropy algebra.** Under the
hypotheses of `SymplecticGeometry.mfderiv_smul_apply_mem_complexOrbitNormal`, for `ξ` in the
isotropy algebra of `x`, the linearized isotropy action `A_ξ` (`TauCeti.isotropyLinearization`)
maps the complex orbit normal space at `x` into itself. -/
theorem isotropyLinearization_apply_mem_complexOrbitNormal [T2Space G] [T2Space M]
    [I'.Boundaryless] {σ : SmoothTwoForm I' M} {J : SmoothAlmostComplexStructure I' M} {x : M}
    (hσG : ∀ g ∈ stabilizer G x, SmoothForm.mpullback (fun y : M ↦ g • y)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ)
    (hJG : ∀ g ∈ stabilizer G x, ∀ v : TangentSpace I' x,
      mfderiv I' I' (fun y : M ↦ g • y) x (J x v) =
        J (g • x) (mfderiv I' I' (fun y : M ↦ g • y) x v))
    (hg : ∀ x (u w : TangentSpace I' x), ⟪u, w⟫ = σ.eval₂ x u (J x w))
    (ξ : (InfinitesimalAction.fundamental I G I' M).isotropy x) {v : TangentSpace I' x}
    (hv : v ∈ complexOrbitNormal I G J x) :
    isotropyLinearization I' x ξ v ∈ complexOrbitNormal I G J x :=
  isotropyLinearization_apply_mem_of_forall_mem ξ (S := complexOrbitNormal I G J x)
    (isClosed_complexOrbitNormal J x) fun t ↦
      mfderiv_smul_apply_mem_complexOrbitNormal hσG hJG hg
        (mulInvariantExp_smul_mem_stabilizer ξ t) hv

/-! ### The slice operator -/

section SliceOperator

variable {EC : Type*} [NormedAddCommGroup EC] [NormedSpace ℝ EC] [CompleteSpace EC]
  {HC : Type*} [TopologicalSpace HC] {IC : ModelWithCorners ℝ EC HC}
  {Gc : Type*} [TopologicalSpace Gc] [ChartedSpace HC Gc] [Group Gc] [LieGroup IC ∞ Gc]
  [MulAction Gc M] [ContMDiffSMul IC I' ∞ Gc M]

omit [FiniteDimensional ℝ E] [RiemannianBundle (fun x : M ↦ TangentSpace I' x)] in
variable (IC Gc) in
/-- The **slice operator** of a linearizing chart `e` at `x` and a subspace `S` of `T_x M` at
`v : E'`: the linear map `(Z, w) ↦ X_Z (e.symm v) - d(e.symm)_v w` from the product of the Lie
algebra of `Gc` and `S` to the tangent space of `M` at `e.symm v`, where `X_Z` is the
fundamental vector field of `Z` and `S` is read in the model space `E' = T_x M` of `e`. Its
kernel consists of the infinitesimal motions along the orbit of `Gc` through `e.symm v` that
the chart reads as motions in `S`. -/
def sliceOperator {x : M} (e : LinearizingChart G I' x) (S : Submodule ℝ (TangentSpace I' x))
    (v : E') : GroupLieAlgebra IC Gc × S →ₗ[ℝ] TangentSpace I' (e.chart.symm v) :=
  ((InfinitesimalAction.fundamental IC Gc I' M).eval (e.chart.symm v)).coprod
    (-((mfderiv 𝓘(ℝ, E') I' e.chart.symm v).toLinearMap ∘ₗ S.subtype))

omit [TopologicalSpace G] [FiniteDimensional ℝ E]
  [RiemannianBundle (fun x : M ↦ TangentSpace I' x)] in
theorem sliceOperator_def {x : M} (e : LinearizingChart G I' x)
    (S : Submodule ℝ (TangentSpace I' x)) (v : E') :
    sliceOperator IC Gc e S v =
      ((InfinitesimalAction.fundamental IC Gc I' M).eval (e.chart.symm v)).coprod
        (-((mfderiv 𝓘(ℝ, E') I' e.chart.symm v).toLinearMap ∘ₗ S.subtype)) :=
  (rfl)

omit [TopologicalSpace G] [FiniteDimensional ℝ E]
  [RiemannianBundle (fun x : M ↦ TangentSpace I' x)] in
@[simp]
theorem sliceOperator_apply {x : M} (e : LinearizingChart G I' x)
    (S : Submodule ℝ (TangentSpace I' x)) (v : E') (p : GroupLieAlgebra IC Gc × S) :
    sliceOperator IC Gc e S v p =
      fundamentalVectorField I' p.1 (e.chart.symm v) -
        mfderiv 𝓘(ℝ, E') I' e.chart.symm v (p.2 : TangentSpace I' x) := by
  simp only [sliceOperator_def, LinearMap.coprod_apply, InfinitesimalAction.eval_apply,
    InfinitesimalAction.fundamental_apply, LinearMap.neg_apply, sub_eq_add_neg]
  -- The composition of `d(e.symm)_v` with the inclusion of `S`, applied to `p.2`:
  -- `LinearMap.comp_apply` does not rewrite it, since `S` lies in `T_x M` and `d(e.symm)_v`
  -- acts on the model space.
  rfl

omit [TopologicalSpace G] [FiniteDimensional ℝ E]
  [RiemannianBundle (fun x : M ↦ TangentSpace I' x)] in
/-- **The dimension of the kernel of the slice operator is upper semicontinuous.** For a
linearizing chart `e` at `x`, a subspace `S` of `T_x M` and `v₀` in the target of `e`, the kernel
of the slice operator at `v` has dimension at most that at `v₀`, for every `v` near `v₀`. -/
theorem eventually_finrank_ker_sliceOperator_le [FiniteDimensional ℝ E'] [FiniteDimensional ℝ EC]
    {x : M} (e : LinearizingChart G I' x) (S : Submodule ℝ (TangentSpace I' x)) {v₀ : E'}
    (hv₀ : v₀ ∈ e.chart.target) :
    ∀ᶠ v in 𝓝 v₀, Module.finrank ℝ (LinearMap.ker (sliceOperator IC Gc e S v)) ≤
      Module.finrank ℝ (LinearMap.ker (sliceOperator IC Gc e S v₀)) := by
  set L := sliceOperator IC Gc e S
  -- On the target of `e`, composing `L v` with the inverse of the differential of `e.symm` does
  -- not change the kernel.
  let L' (v : E') : (GroupLieAlgebra IC Gc × S) →ₗ[ℝ] E' :=
    (mfderiv 𝓘(ℝ, E') I' e.chart.symm v).inverse.toLinearMap ∘ₗ L v
  have hker (v : E') (hv : v ∈ e.chart.target) : LinearMap.ker (L' v) = LinearMap.ker (L v) :=
    LinearMap.ker_comp_of_ker_eq_bot _ (LinearMap.ker_eq_bot.2 (Function.LeftInverse.injective
      (e.isInvertible_mfderiv_chart_symm hv).self_apply_inverse))
  -- `L' v p` is `Y v - c`, with `Y` the pull-back of a fundamental vector field by `e.symm`.
  have hcont (p : GroupLieAlgebra IC Gc × S) : ContinuousAt (fun v ↦ L' v p) v₀ := by
    let Y : E' → E' :=
      VectorField.mpullback 𝓘(ℝ, E') I' e.chart.symm (fundamentalVectorField I' p.1)
    have hY : ContinuousAt Y v₀ := by
      have h := ContMDiffAt.mpullback_vectorField_preimage (m := 0) (n := ∞)
        ((contMDiff_fundamentalVectorField (I := IC) (n := ∞) (by simp) p.1) _)
        (e.contMDiffOn_chart_symm.contMDiffAt (e.chart.open_target.mem_nhds hv₀))
        (e.isInvertible_mfderiv_chart_symm hv₀) (by simp)
      exact (contMDiffAt_vectorSpace_iff_contDiffAt.1 h).continuousAt
    let c : E' := (p.2 : TangentSpace I' x)
    have hL' (v : E') (hv : v ∈ e.chart.target) : L' v p = Y v - c := by
      -- `L' v p` is the inverse of the differential applied to `L v p`: `LinearMap.comp_apply`
      -- does not rewrite it, since the inverse lands in `T_v E'`, a type synonym of `E'`.
      change (mfderiv 𝓘(ℝ, E') I' e.chart.symm v).inverse (L v p) = _
      simp only [L, Y, sliceOperator_apply, map_sub, VectorField.mpullback_apply]
      exact congrArg (_ - ·) ((e.isInvertible_mfderiv_chart_symm hv).inverse_apply_self
        (c : TangentSpace 𝓘(ℝ, E') v))
    refine (hY.sub (continuousAt_const (y := c))).congr ?_
    filter_upwards [e.chart.open_target.mem_nhds hv₀] with v hv
    exact (hL' v hv).symm
  filter_upwards [LinearMap.eventually_finrank_ker_le hcont,
    e.chart.open_target.mem_nhds hv₀] with v hv hvt
  rwa [← hker v hvt, ← hker v₀ hv₀]

variable [T2Space Gc] [T2Space M] [I'.Boundaryless] [FiniteDimensional ℝ E']

omit [FiniteDimensional ℝ E'] [RiemannianBundle (fun x : M ↦ TangentSpace I' x)] in
/-- In a linearizing chart `e` at `x` in which `J` is constant, equal to `J x`, the slice
operator at a point `v` of the target of `e` vanishes on the pair
`(C.lieMap ξ + C.cplx (C.lieMap η), A_ξ v + J x (A_η v))` for `ξ, η` in the isotropy algebra of
`x`, where `A` is the linearized isotropy action (`TauCeti.isotropyLinearization`). -/
theorem sliceOperator_apply_eq_zero {C : LieComplexification I G IC Gc}
    {J : SmoothAlmostComplexStructure I' M} (hC : IsComplexifiedAction C J) {x : M}
    (e : LinearizingChart G I' x)
    (hJ : ∀ z ∈ e.chart.source, ∀ v : TangentSpace I' z,
      mfderiv I' 𝓘(ℝ, E') e.chart z (J z v) = J x (mfderiv I' 𝓘(ℝ, E') e.chart z v))
    (S : Submodule ℝ (TangentSpace I' x))
    (ξ η : (InfinitesimalAction.fundamental I G I' M).isotropy x) {v : E'}
    (hv : v ∈ e.chart.target) (w : S)
    (hw : (w : TangentSpace I' x) = isotropyLinearization I' x ξ v +
      (J.toEndomorphism x ∘L isotropyLinearization I' x η : E' →L[ℝ] E') v) :
    sliceOperator IC Gc e S v (C.lieMap ξ + C.cplx (C.lieMap η), w) = 0 := by
  rw [sliceOperator_apply, hw, fundamentalVectorField_chart_symm hC e hJ ξ η hv]
  exact sub_eq_zero.2 (map_add (mfderiv 𝓘(ℝ, E') I' e.chart.symm v) _ _).symm

omit [T2Space M] [I'.Boundaryless] in
/-- **The kernel of the slice operator at `0`.** For a complexified action, with `-μ` an
equivariant moment map for `σ`, the metric `g(u, w) = σ(u, J w)` and `μ x = 0`, the kernel of
the slice operator of a linearizing chart at `x` and the complex orbit normal space `S`, at `0`,
consists of the pairs `(C.lieMap ξ + C.cplx (C.lieMap η), 0)` with `ξ, η` in the isotropy algebra
of `x`. -/
theorem mem_ker_sliceOperator_zero_iff {C : LieComplexification I G IC Gc}
    {σ : SmoothTwoForm I' M} {J : SmoothAlmostComplexStructure I' M}
    {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)} (hC : IsComplexifiedAction C J)
    (hμ : σ.IsEquivariantMomentMap fun x ↦ -μ x)
    (hg : ∀ x (u w : TangentSpace I' x), ⟪u, w⟫ = σ.eval₂ x u (J x w)) {x : M} (hx : μ x = 0)
    (e : LinearizingChart G I' x) (p : GroupLieAlgebra IC Gc × complexOrbitNormal I G J x) :
    p ∈ LinearMap.ker (sliceOperator IC Gc e (complexOrbitNormal I G J x) 0) ↔
      ∃ ξ η : (InfinitesimalAction.fundamental I G I' M).isotropy x,
        p.1 = C.lieMap ξ + C.cplx (C.lieMap η) ∧ p.2 = 0 := by
  obtain ⟨Z, w⟩ := p
  -- `w ↦ -w`, the inclusion of `S` in `T_x M` followed by negation.
  let L : complexOrbitNormal I G J x →ₗ[ℝ] TangentSpace I' x :=
    -(complexOrbitNormal I G J x).subtype
  have hL : Function.Injective L := fun a b h ↦
    (complexOrbitNormal I G J x).injective_subtype (neg_injective h)
  have hdisj : Disjoint ((InfinitesimalAction.fundamental IC Gc I' M).orbitTangent x)
      (LinearMap.range L) := by
    rw [LinearMap.range_neg, Submodule.range_subtype, hC.orbitTangent_eq_complexOrbitTangent x]
    exact (isCompl_complexOrbitTangent J x).disjoint
  have h := (InfinitesimalAction.fundamental IC Gc I' M).apply_add_eq_zero_iff hL hdisj
    (Z := Z) (p := w)
  rw [InfinitesimalAction.fundamental_apply, ← LieSubalgebra.mem_toSubmodule,
    hC.isotropy_eq_map_lieMap_sup_of_moment_eq_zero hμ hg hx] at h
  simp only [L, LinearMap.neg_apply, Submodule.subtype_apply, ← sub_eq_add_neg] at h
  rw [LinearMap.mem_ker, sliceOperator_apply, e.mfderiv_chart_symm_zero, e.symm_zero]
  -- `ContinuousLinearMap.id_apply` does not rewrite once the identity of `E'` is applied to a
  -- vector of `T_x M`; the identity applied to `w` is `w` by definition.
  change fundamentalVectorField I' Z x - (w : TangentSpace I' x) = 0 ↔ _
  rw [h]
  constructor
  · rintro ⟨hZ, rfl⟩
    obtain ⟨_, ⟨a, ha, rfl⟩, _, ⟨_, ⟨b, hb, rfl⟩, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hZ
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, rfl, rfl⟩
  · rintro ⟨ξ, η, rfl, rfl⟩
    exact ⟨Submodule.add_mem_sup ⟨ξ, ξ.property, rfl⟩ ⟨_, ⟨η, η.property, rfl⟩, rfl⟩, rfl⟩

/-- **The kernel of the slice operator** (Step 2 of the proof of Theorem 12.5 of
[GeorgoulasRobbinSalamon2021]). Let the action of the complexification `Gc` on `M` be a
complexified action of that of `G` for `C` and `J`, let `-μ` be an equivariant moment map for
`σ`, let the metric be `g(u, w) = σ(u, J w)`, let the stabilizer of `x` preserve `σ` and `J`,
and let `μ x = 0`. Let `e` be a linearizing chart at `x` in which `J` is constant, equal to
`J x`, and `S` the complex orbit normal space at `x`. Then for every `v ∈ S` near `0`, the
kernel of the slice operator `(Z, w) ↦ X_Z (e.symm v) - d(e.symm)_v w` on the product of the
Lie algebra of `Gc` and `S` is the set of pairs
`(C.lieMap ξ + C.cplx (C.lieMap η), A_ξ v + J x (A_η v))` with `ξ, η` in the isotropy algebra
of `x`, where `A` is the linearized isotropy action (`TauCeti.isotropyLinearization`). -/
theorem ker_sliceOperator_eq {C : LieComplexification I G IC Gc} {σ : SmoothTwoForm I' M}
    {J : SmoothAlmostComplexStructure I' M} {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)}
    (hC : IsComplexifiedAction C J) (hμ : σ.IsEquivariantMomentMap fun x ↦ -μ x)
    (hg : ∀ x (u w : TangentSpace I' x), ⟪u, w⟫ = σ.eval₂ x u (J x w)) {x : M}
    (hσG : ∀ g ∈ stabilizer G x, SmoothForm.mpullback (fun y : M ↦ g • y)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ)
    (hJG : ∀ g ∈ stabilizer G x, ∀ v : TangentSpace I' x,
      mfderiv I' I' (fun y : M ↦ g • y) x (J x v) =
        J (g • x) (mfderiv I' I' (fun y : M ↦ g • y) x v))
    (hx : μ x = 0) (e : LinearizingChart G I' x)
    (hJ : ∀ z ∈ e.chart.source, ∀ v : TangentSpace I' z,
      mfderiv I' 𝓘(ℝ, E') e.chart z (J z v) = J x (mfderiv I' 𝓘(ℝ, E') e.chart z v)) :
    ∀ᶠ v in 𝓝 (0 : E'), v ∈ complexOrbitNormal I G J x →
      (LinearMap.ker (sliceOperator IC Gc e (complexOrbitNormal I G J x) v) :
          Set (GroupLieAlgebra IC Gc × complexOrbitNormal I G J x)) =
        {p | ∃ ξ η : (InfinitesimalAction.fundamental I G I' M).isotropy x,
          p.1 = C.lieMap ξ + C.cplx (C.lieMap η) ∧
          (p.2 : TangentSpace I' x) = isotropyLinearization I' x ξ v +
            (J.toEndomorphism x ∘L isotropyLinearization I' x η : E' →L[ℝ] E') v} := by
  have : T2Space G := I.t2Space_of_lieGroup ∞
  have := C.finiteDimensional
  set S := complexOrbitNormal I G J x
  set 𝔥 := (InfinitesimalAction.fundamental I G I' M).isotropy x
  set A : 𝔥 →ₗ[ℝ] E' →L[ℝ] E' := isotropyLinearization I' x
  set Jx : E' →L[ℝ] E' := J.toEndomorphism x
  -- The parametrization `(ξ, η) ↦ (C.lieMap ξ + C.cplx (C.lieMap η), A_ξ v + J x (A_η v))` of
  -- the claimed kernel, an injective linear map into the domain of the slice operator.
  let a (v : E') : 𝔥 →ₗ[ℝ] E' := (ContinuousLinearMap.apply ℝ E' v).toLinearMap ∘ₗ A
  have hAS (v : E') (hv : v ∈ S) (q : 𝔥 × 𝔥) : (a v).coprod (Jx.toLinearMap ∘ₗ a v) q ∈ S :=
    S.add_mem (isotropyLinearization_apply_mem_complexOrbitNormal hσG hJG hg q.1 hv)
      (apply_mem_complexOrbitNormal hg
        (isotropyLinearization_apply_mem_complexOrbitNormal hσG hJG hg q.2 hv))
  let Φ (v : E') (hv : v ∈ S) : (𝔥 × 𝔥) →ₗ[ℝ] GroupLieAlgebra IC Gc × S :=
    ((C.lieMap.toLinearMap ∘ₗ 𝔥.toSubmodule.subtype).coprod
        (C.cplx.toLinearMap ∘ₗ C.lieMap.toLinearMap ∘ₗ 𝔥.toSubmodule.subtype)).prod
      (((a v).coprod (Jx.toLinearMap ∘ₗ a v)).codRestrict S (hAS v hv))
  have hΦ (v : E') (hv : v ∈ S) (p : GroupLieAlgebra IC Gc × S) :
      p ∈ LinearMap.range (Φ v hv) ↔ ∃ ξ η : 𝔥, p.1 = C.lieMap ξ + C.cplx (C.lieMap η) ∧
        (p.2 : TangentSpace I' x) = A ξ v + (Jx ∘L A η) v := by
    simp only [LinearMap.mem_range, Prod.exists, Φ, a, Prod.ext_iff, Subtype.ext_iff,
      LinearMap.prod_apply, LinearMap.coprod_apply, LinearMap.comp_apply, LieHom.coe_toLinearMap,
      ContinuousLinearMap.comp_apply, Function.prod_apply, Submodule.coe_subtype]
    constructor
    · rintro ⟨ξ, η, h1, h2⟩
      exact ⟨ξ, η, h1.symm, h2.symm⟩
    · rintro ⟨ξ, η, h1, h2⟩
      exact ⟨ξ, η, h1.symm, h2.symm⟩
  have hfin (v : E') (hv : v ∈ S) :
      Module.finrank ℝ (LinearMap.range (Φ v hv)) = Module.finrank ℝ (𝔥 × 𝔥) := by
    refine LinearMap.finrank_range_of_inj fun q q' hq ↦ ?_
    have h1 := congrArg Prod.fst hq
    have hre := congrArg C.re h1
    have him := congrArg C.im h1
    simp only [Φ, LinearMap.prod_apply, Function.prod_apply, LinearMap.coprod_apply,
      LinearMap.comp_apply, LieHom.coe_toLinearMap, Submodule.coe_subtype, map_add, C.re_lieMap,
      C.re_cplx_lieMap, C.im_lieMap, C.im_cplx_lieMap, add_zero, zero_add] at hre him
    exact Prod.ext (Subtype.ext hre) (Subtype.ext him)
  -- At `v = 0` the kernel lies in the range of the parametrization.
  have hker0 : LinearMap.ker (sliceOperator IC Gc e S 0) ≤ LinearMap.range (Φ 0 S.zero_mem) := by
    intro p hp
    obtain ⟨ξ, η, h1, h2⟩ := (mem_ker_sliceOperator_zero_iff hC hμ hg hx e p).1 hp
    refine (hΦ 0 S.zero_mem p).2 ⟨ξ, η, h1, ?_⟩
    -- The zero of `T_x M` on the left, that of `E'` on the right.
    simp only [h2, ZeroMemClass.coe_zero, map_zero, add_zero]
    rfl
  filter_upwards [eventually_finrank_ker_sliceOperator_le (IC := IC) (Gc := Gc) e S
    e.zero_mem_target,
    e.chart.open_target.mem_nhds e.zero_mem_target] with v hvle hvt hv
  have hrange : LinearMap.range (Φ v hv) ≤ LinearMap.ker (sliceOperator IC Gc e S v) := by
    intro p hp
    obtain ⟨ξ, η, h1, h2⟩ := (hΦ v hv p).1 hp
    obtain ⟨Z, w⟩ := p
    obtain rfl : Z = _ := h1
    exact sliceOperator_apply_eq_zero hC e hJ S ξ η hvt w h2
  have heq := Submodule.eq_of_le_of_finrank_le hrange (by
    rw [hfin v hv, ← hfin 0 S.zero_mem]
    exact hvle.trans (Submodule.finrank_mono hker0))
  ext p
  -- Membership in the set-builder set is the condition of `hΦ`, by definition.
  rw [SetLike.mem_coe, ← heq]
  exact hΦ v hv p

end SliceOperator

/-! ### The derivative of the slice map -/

variable (I G) in
/-- For a subspace `K` of the Lie algebra of `G`, the linear map
`(α, β, v) ↦ J x (X_α x) + X_β x + v` from `K × K × S` to `T_x M`, where `S` is the complex
orbit normal space at `x`. For a complexified action, it is the derivative at `0` of
`(α, β, v) ↦ C.expI α * C.toHom (mulInvariantExp β) • e.symm v` read in a chart `e` at `x`
whose derivative at `x` is the identity. It is bijective when `K` is a complement of the
isotropy algebra and `x` is a zero of the moment map
(`SymplecticGeometry.bijective_complexOrbitSliceMap`). -/
def complexOrbitSliceMap (J : SmoothAlmostComplexStructure I' M) (x : M)
    (K : Submodule ℝ (GroupLieAlgebra I G)) :
    K × K × complexOrbitNormal I G J x →ₗ[ℝ] TangentSpace I' x :=
  ((J.toEndomorphism x).toLinearMap ∘ₗ (InfinitesimalAction.fundamental I G I' M).eval x ∘ₗ
      K.subtype).coprod
    (((InfinitesimalAction.fundamental I G I' M).eval x ∘ₗ K.subtype).coprod
      (complexOrbitNormal I G J x).subtype)

omit [FiniteDimensional ℝ E] in
theorem complexOrbitSliceMap_def (J : SmoothAlmostComplexStructure I' M) (x : M)
    (K : Submodule ℝ (GroupLieAlgebra I G)) :
    complexOrbitSliceMap I G J x K =
      ((J.toEndomorphism x).toLinearMap ∘ₗ (InfinitesimalAction.fundamental I G I' M).eval x ∘ₗ
          K.subtype).coprod
        (((InfinitesimalAction.fundamental I G I' M).eval x ∘ₗ K.subtype).coprod
          (complexOrbitNormal I G J x).subtype) :=
  (rfl)

omit [FiniteDimensional ℝ E] in
@[simp]
theorem complexOrbitSliceMap_apply (J : SmoothAlmostComplexStructure I' M) (x : M)
    (K : Submodule ℝ (GroupLieAlgebra I G)) (a : K × K × complexOrbitNormal I G J x) :
    complexOrbitSliceMap I G J x K a =
      J x (fundamentalVectorField I' (a.1 : GroupLieAlgebra I G) x) +
        fundamentalVectorField I' (a.2.1 : GroupLieAlgebra I G) x + a.2.2 := by
  rw [add_assoc, complexOrbitSliceMap_def]
  simp only [LinearMap.coprod_apply, LinearMap.comp_apply, Submodule.coe_subtype,
    InfinitesimalAction.eval_apply, InfinitesimalAction.fundamental_apply,
    ContinuousLinearMap.coe_coe]

/-- **The derivative of the slice map is bijective.** Let `-μ` be an equivariant moment map for
`σ`, let the metric be `g(u, w) = σ(u, J w)`, let `μ x = 0`, and let `K` be a complement of the
isotropy algebra `𝔥` of `x` in the Lie algebra of `G`. Then
`(α, β, v) ↦ J x (X_α x) + X_β x + v` is a bijection from `K × K × S` onto `T_x M`, where `S`
is the complex orbit normal space at `x`. -/
theorem bijective_complexOrbitSliceMap {σ : SmoothTwoForm I' M}
    {J : SmoothAlmostComplexStructure I' M} {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)}
    (hμ : σ.IsEquivariantMomentMap fun x ↦ -μ x)
    (hg : ∀ x (u w : TangentSpace I' x), ⟪u, w⟫ = σ.eval₂ x u (J x w)) {x : M} (hx : μ x = 0)
    {K : Submodule ℝ (GroupLieAlgebra I G)}
    (hK : IsCompl ((InfinitesimalAction.fundamental I G I' M).isotropy x).toSubmodule K) :
    Function.Bijective (complexOrbitSliceMap I G J x K) := by
  have hTS := isCompl_complexOrbitTangent (I := I) (G := G) J x
  have hW (ξ : GroupLieAlgebra I G) : fundamentalVectorField I' ξ x ∈
      (InfinitesimalAction.fundamental I G I' M).orbitTangent x := by
    rw [← InfinitesimalAction.fundamental_apply]
    exact InfinitesimalAction.mem_orbitTangent _ x ξ
  -- `α ↦ X_α x` identifies `K` with the orbit tangent space, through `𝔤 ⧸ 𝔥`.
  let eK := (Submodule.quotientEquivOfIsCompl _ K hK).symm.trans
    ((InfinitesimalAction.fundamental I G I' M).quotIsotropyEquivOrbitTangent x)
  have heK (α : K) :
      (eK α : TangentSpace I' x) = fundamentalVectorField I' (α : GroupLieAlgebra I G) x := by
    simp [eK, InfinitesimalAction.fundamental_apply]
  have hKX {α : K} (h : fundamentalVectorField I' (α : GroupLieAlgebra I G) x = 0) : α = 0 :=
    eK.map_eq_zero_iff.1 (Subtype.ext ((heK α).trans h))
  have hXK (ξ : GroupLieAlgebra I G) :
      ∃ α : K, fundamentalVectorField I' (α : GroupLieAlgebra I G) x =
        fundamentalVectorField I' ξ x := by
    obtain ⟨α, hα⟩ := eK.surjective ⟨_, hW ξ⟩
    exact ⟨α, (heK α).symm.trans (congrArg Subtype.val hα)⟩
  refine ⟨?_, fun u ↦ ?_⟩
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨α, β, v⟩ h0
    rw [complexOrbitSliceMap_apply] at h0
    set w := J x (fundamentalVectorField I' (α : GroupLieAlgebra I G) x) +
      fundamentalVectorField I' (β : GroupLieAlgebra I G) x with hw_def
    have hwT : w ∈ complexOrbitTangent I G J x :=
      mem_complexOrbitTangent_iff.2 ⟨β, α, add_comm _ _⟩
    have hwS : w ∈ complexOrbitNormal I G J x := by
      rw [eq_neg_of_add_eq_zero_left h0]
      exact (complexOrbitNormal I G J x).neg_mem v.property
    have hw : w = 0 :=
      Submodule.disjoint_def.1 hTS.disjoint w hwT hwS
    have hv : (v : TangentSpace I' x) = 0 := by
      rw [hw, zero_add] at h0
      exact h0
    -- `J x (X_α x) = -X_β x` lies in `W ∩ J x W`, which is `0`.
    have hJα : J x (fundamentalVectorField I' (α : GroupLieAlgebra I G) x) = 0 := by
      refine Submodule.disjoint_def.1
        (isTotallyReal_orbitTangent_of_moment_eq_zero hμ hg hx).disjoint _ ?_
        (SmoothAlmostComplexStructure.mem_map_toEndomorphism_iff.2
          ⟨_, hW (α : GroupLieAlgebra I G), rfl⟩)
      rw [eq_neg_of_add_eq_zero_left hw]
      exact Submodule.neg_mem _ (hW (β : GroupLieAlgebra I G))
    have hXα : fundamentalVectorField I' (α : GroupLieAlgebra I G) x = 0 :=
      J.injective x (hJα.trans (map_zero (J.toEndomorphism x)).symm)
    have hXβ : fundamentalVectorField I' (β : GroupLieAlgebra I G) x = 0 := by
      rw [hw_def, hJα, zero_add] at hw
      exact hw
    obtain rfl := hKX hXα
    obtain rfl := hKX hXβ
    obtain rfl : v = 0 := Subtype.ext hv
    simp only [Prod.mk_zero_zero]
  · obtain ⟨t, s, ht, hs, rfl⟩ :=
      Submodule.codisjoint_iff_exists_add_eq.1 hTS.codisjoint u
    obtain ⟨ξ, η, hξη⟩ := mem_complexOrbitTangent_iff.1 ht
    obtain ⟨α, hα⟩ := hXK η
    obtain ⟨β, hβ⟩ := hXK ξ
    refine ⟨(α, β, ⟨s, hs⟩), ?_⟩
    rw [complexOrbitSliceMap_apply, hα, hβ, add_comm (J x _), hξη]

/-- The linear equivalence `(α, β, v) ↦ J x (X_α x) + X_β x + v` from `K × K × S` onto `T_x M`
(`SymplecticGeometry.complexOrbitSliceMap`), for `K` a complement of the isotropy algebra of a
zero `x` of the moment map (`SymplecticGeometry.bijective_complexOrbitSliceMap`). -/
def complexOrbitSliceEquiv {σ : SmoothTwoForm I' M}
    {J : SmoothAlmostComplexStructure I' M} {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)}
    (hμ : σ.IsEquivariantMomentMap fun x ↦ -μ x)
    (hg : ∀ x (u w : TangentSpace I' x), ⟪u, w⟫ = σ.eval₂ x u (J x w)) {x : M} (hx : μ x = 0)
    {K : Submodule ℝ (GroupLieAlgebra I G)}
    (hK : IsCompl ((InfinitesimalAction.fundamental I G I' M).isotropy x).toSubmodule K) :
    (K × K × complexOrbitNormal I G J x) ≃ₗ[ℝ] TangentSpace I' x :=
  LinearEquiv.ofBijective _ (bijective_complexOrbitSliceMap hμ hg hx hK)

@[simp]
theorem complexOrbitSliceEquiv_apply {σ : SmoothTwoForm I' M}
    {J : SmoothAlmostComplexStructure I' M} {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)}
    (hμ : σ.IsEquivariantMomentMap fun x ↦ -μ x)
    (hg : ∀ x (u w : TangentSpace I' x), ⟪u, w⟫ = σ.eval₂ x u (J x w)) {x : M} (hx : μ x = 0)
    {K : Submodule ℝ (GroupLieAlgebra I G)}
    (hK : IsCompl ((InfinitesimalAction.fundamental I G I' M).isotropy x).toSubmodule K)
    (a : K × K × complexOrbitNormal I G J x) :
    complexOrbitSliceEquiv hμ hg hx hK a = complexOrbitSliceMap I G J x K a :=
  LinearEquiv.ofBijective_apply _ a

end SymplecticGeometry

end
