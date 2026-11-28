/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.KempfNess.Basic
public import TauCeti.Geometry.Lie.FundamentalVectorField.Isotropy
public import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import TauCeti.Geometry.Manifold.GroupAction.TangentRepresentation

/-!
# The normal space of the complex orbit at a zero of the moment map

Let a Lie group `G` act on a manifold `M` with a two-form `σ`, an almost complex structure `J`
and a metric with `g(u, w) = σ(u, J w)`, and let `W = 𝔤 · x` be the orbit tangent space at `x`
(`TauCeti.InfinitesimalAction.orbitTangent`). This file studies the **complex orbit tangent
space** `T = W + J x W` (`SymplecticGeometry.complexOrbitTangent`) and its orthogonal complement
`S = Tᗮ` for `g`, the **complex orbit normal space** (`SymplecticGeometry.complexOrbitNormal`).
These are the linear objects of the holomorphic slice at a zero of the moment map in the proof
of Theorem 12.5 of [GeorgoulasRobbinSalamon2021] (Steps 2–5 there), in the spirit of the
holomorphic slice theorem of Sjamaar (§1 of his paper below); the later steps read `S` in a
linearizing chart at `x`, whose derivative at `x` is the identity of `E' = T_x M`.

For a complexified action of a complexification `Gc` of `G`, `T` is the orbit tangent space of
`Gc` at `x` (`SymplecticGeometry.IsComplexifiedAction.orbitTangent_eq_complexOrbitTangent`),
since `X_ζ = X_{re ζ} + J X_{im ζ}`. If `-μ` is an equivariant moment map and `μ x = 0`, the
orbit through `x` is isotropic, `σ_x(X_ξ, X_η) = -μ x ⁅ξ, η⁆ = 0`, so `W` and `J x W` are
orthogonal for `g`, and in particular they meet only in `0`
(`SymplecticGeometry.disjoint_orbitTangent_map_orbitTangent`).

The space `S` is a complement of `T` (`SymplecticGeometry.isCompl_complexOrbitTangent`) and is
invariant under `J x` (`SymplecticGeometry.apply_mem_complexOrbitNormal`), since `J x` preserves
`T` and `g`. If the stabilizer `H` of `x` preserves `σ` and `J`, then each `dh_x` preserves `W`
and `g`, so `S` is invariant under `dh_x`
(`SymplecticGeometry.mfderiv_smul_apply_mem_complexOrbitNormal`), and, differentiating along
`exp (t ξ)`, under the linearized isotropy action `A_ξ` for `ξ` in the isotropy algebra
(`SymplecticGeometry.isotropyLinearization_apply_mem_complexOrbitNormal`), through Tau Ceti's
`TauCeti.isotropyLinearization_apply_mem_of_forall_mem`. This is the invariance that equation
(12.6) of [GeorgoulasRobbinSalamon2021] gives, `A_ξ (X_η x) = X_⁅ξ, η⁆ x` with `A_ξ` skew.

Tau Ceti's symplectic slice `TauCeti.SmoothTwoForm.IsNondegenerate.SymplecticSlice` is the
quotient `W^σ ⧸ (W ∩ W^σ)` of the `σ_x`-orthogonal of `W`, which `J x` does not preserve; the
later steps of the proof need a `J x`-invariant subspace of `T_x M` on which `H` acts, which is
why `S` is taken as the `g`-orthogonal complement of `T` instead.

## Main definitions

* `SymplecticGeometry.complexOrbitTangent I G J x`: the subspace `W + J x W` of `T_x M`.
* `SymplecticGeometry.complexOrbitNormal I G J x`: its orthogonal complement for the metric.

## Main results

* `SymplecticGeometry.IsComplexifiedAction.orbitTangent_eq_complexOrbitTangent`: for a
  complexified action, the orbit tangent space of `Gc` is `W + J x W`.
* `SymplecticGeometry.disjoint_orbitTangent_map_orbitTangent`: at a zero of the moment map, `W`
  and `J x W` meet only in `0`.
* `SymplecticGeometry.isCompl_complexOrbitTangent`: `T` and `S` are complementary.
* `SymplecticGeometry.apply_mem_complexOrbitNormal`: `S` is `J x`-invariant.
* `SymplecticGeometry.mfderiv_smul_apply_mem_complexOrbitNormal`: `S` is invariant under the
  differentials at `x` of the elements of the stabilizer.
* `SymplecticGeometry.isotropyLinearization_apply_mem_complexOrbitNormal`: `S` is invariant under
  the linearized isotropy action.

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
  simp only [complexOrbitTangent_def, Submodule.mem_sup, Submodule.mem_map,
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

/-- **The orbit through a zero of the moment map is isotropic.** If `-μ` is an equivariant moment
map for `σ`, the metric is `g(u, w) = σ(u, J w)` and `μ x = 0`, then `X_ξ x` and `J x (X_η x)`
are orthogonal for all `ξ, η`. -/
theorem inner_fundamentalVectorField_apply_eq_zero {σ : SmoothTwoForm I' M}
    {J : SmoothAlmostComplexStructure I' M} {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)}
    (hμ : σ.IsEquivariantMomentMap fun x ↦ -μ x)
    (hg : ∀ x (u w : TangentSpace I' x), ⟪u, w⟫ = σ.eval₂ x u (J x w)) {x : M} (hx : μ x = 0)
    (ξ η : GroupLieAlgebra I G) :
    ⟪fundamentalVectorField I' ξ x, J x (fundamentalVectorField I' η x)⟫ = 0 := by
  have hcoc := SmoothTwoForm.momentCocycle_eq_zero_iff.1 (hμ.momentCocycle_eq_zero x) η ξ
  simp only [InfinitesimalAction.fundamental_apply, hx, neg_zero, LinearMap.zero_apply] at hcoc
  rw [real_inner_comm, SmoothAlmostComplexStructure.inner_apply_left_of_inner_eq hg]
  exact hcoc

/-- **The two halves of the complex orbit tangent space meet only in `0`** at a zero of the
moment map: if `-μ` is an equivariant moment map for `σ`, the metric is `g(u, w) = σ(u, J w)`
and `μ x = 0`, then the orbit tangent space `W` and its image under `J x` are disjoint. -/
theorem disjoint_orbitTangent_map_orbitTangent {σ : SmoothTwoForm I' M}
    {J : SmoothAlmostComplexStructure I' M} {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)}
    (hμ : σ.IsEquivariantMomentMap fun x ↦ -μ x)
    (hg : ∀ x (u w : TangentSpace I' x), ⟪u, w⟫ = σ.eval₂ x u (J x w)) {x : M} (hx : μ x = 0) :
    Disjoint ((InfinitesimalAction.fundamental I G I' M).orbitTangent x)
      (((InfinitesimalAction.fundamental I G I' M).orbitTangent x).map
        (J.toEndomorphism x).toLinearMap) := by
  rw [Submodule.disjoint_def]
  simp only [Submodule.mem_map, InfinitesimalAction.orbitTangent_eq_range, LinearMap.mem_range,
    InfinitesimalAction.eval_apply, InfinitesimalAction.fundamental_apply]
  rintro v ⟨ξ, rfl⟩ ⟨_, ⟨η, rfl⟩, hv⟩
  have h := inner_fundamentalVectorField_apply_eq_zero hμ hg hx ξ η
  rw [show J x (fundamentalVectorField I' η x) = fundamentalVectorField I' ξ x from hv] at h
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
  have hJ (k : stabilizer G x) (u : TangentSpace I' x) : ρ k (J x u) = J x (ρ k u) := by
    have h := hJG k k.property u
    rw [show (k : G) • x = x from k.property] at h
    rw [tangentRepresentation_apply]
    exact h
  -- Each `ρ k` preserves the metric, since it preserves `σ` and commutes with `J x`.
  have hinner (k : stabilizer G x) (u w : TangentSpace I' x) :
      ⟪(ρ k u : TangentSpace I' x), ρ k w⟫ = ⟪u, w⟫ := by
    have h := SmoothForm.eval₂_mpullback (fun y : M ↦ (k : G) • y)
      (ContMDiffSMul.contMDiff_const_smul (I := I) (k : G)) σ x u (J x w)
    rw [hσG k k.property] at h
    rw [hg, hg, ← hJ, h, tangentRepresentation_apply, show (k : G) • x = x from k.property]
  -- Each `ρ k` preserves the complex orbit tangent space.
  have hT (k : stabilizer G x) {u : TangentSpace I' x} (hu : u ∈ complexOrbitTangent I G J x) :
      (ρ k u : TangentSpace I' x) ∈ complexOrbitTangent I G J x := by
    rw [complexOrbitTangent_def, Submodule.mem_sup] at hu ⊢
    obtain ⟨a, ha, _, ⟨b, hb, rfl⟩, rfl⟩ := hu
    refine ⟨ρ k a, tangentRepresentation_mem_orbitTangent_fundamental hd k ha, _,
      ⟨ρ k b, tangentRepresentation_mem_orbitTangent_fundamental hd k hb, (hJ k b).symm⟩,
      (map_add (ρ k) a _).symm⟩
  let k : stabilizer G x := ⟨g, hgx⟩
  have hρ : (mfderiv I' I' (fun y : M ↦ g • y) x : E' →L[ℝ] E') = ρ k :=
    (tangentRepresentation_apply hd k).symm
  rw [hρ]
  rw [mem_complexOrbitNormal_iff] at hv
  -- The membership is stated at the type `TangentSpace I' (g • x)` of the value of `dg_x`, which
  -- is `TangentSpace I' x` only up to unfolding, so the lemma is applied rather than rewritten.
  refine mem_complexOrbitNormal_iff.2 fun u hu ↦ ?_
  have hu' : (ρ k (ρ k⁻¹ u) : TangentSpace I' x) = u := by
    have h := congrArg (fun m ↦ ρ m u) (mul_inv_cancel k)
    simpa only [map_mul, map_one, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply,
      one_apply_eq_self] using h
  rw [← hu']
  exact (hinner k _ v).trans (hv _ (hT _ hu))

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

end SymplecticGeometry

end
