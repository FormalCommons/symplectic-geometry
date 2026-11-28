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
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import TauCeti.RepresentationTheory.Continuous.InvariantComplement
import SymplecticGeometry.Geometry.Manifold.GroupAction.TangentRepresentation.AlmostComplex

/-!
# The normal space of the complex orbit at a zero of the moment map

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
open scoped Manifold ContDiff RealInnerProductSpace

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
  -- An element of `K` whose fundamental vector field vanishes at `x` is `0`.
  have hKX {α : K} (h : fundamentalVectorField I' (α : GroupLieAlgebra I G) x = 0) : α = 0 := by
    have hα : (α : GroupLieAlgebra I G) ∈
        ((InfinitesimalAction.fundamental I G I' M).isotropy x).toSubmodule := by
      rw [LieSubalgebra.mem_toSubmodule, InfinitesimalAction.mem_isotropy_iff,
        InfinitesimalAction.fundamental_apply]
      exact h
    exact Subtype.ext (Submodule.disjoint_def.1 hK.disjoint _ hα α.property)
  -- Every fundamental vector field at `x` is that of an element of `K`.
  have hXK (ξ : GroupLieAlgebra I G) :
      ∃ α : K, fundamentalVectorField I' (α : GroupLieAlgebra I G) x =
        fundamentalVectorField I' ξ x := by
    obtain ⟨h, α, hh, hα, rfl⟩ := Submodule.codisjoint_iff_exists_add_eq.1 hK.codisjoint ξ
    rw [LieSubalgebra.mem_toSubmodule, InfinitesimalAction.mem_isotropy_iff,
      InfinitesimalAction.fundamental_apply] at hh
    refine ⟨⟨α, hα⟩, ?_⟩
    rw [fundamentalVectorField_add, Pi.add_apply, hh, zero_add]
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
