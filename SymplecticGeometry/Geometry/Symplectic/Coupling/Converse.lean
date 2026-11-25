/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Lie.FundamentalVectorField
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.SmoothFamily.Basic
public import SymplecticGeometry.Geometry.Manifold.Flow.Basic
public import SymplecticGeometry.Geometry.Manifold.GroupAction.RegularLevel
public import SymplecticGeometry.Geometry.Symplectic.Coupling.Basic
public import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.Circle
public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap

/-!
# The converse of minimal coupling: the band as a product

Let `v` be a complete smooth vector field on a Hausdorff boundaryless manifold `M`, with maximal
flow `φ` (`TauCeti.flowOf`), and `e : Q → M` a map from a manifold `Q`. The **band map**
`SymplecticGeometry.bandMap v e a b : Q × [a, b] → M` sends `(q, s)` to `φ_{s - a} (e q)`. This
file proves that

* it is smooth, for the product of the model of `Q` with Mathlib's model `𝓡∂ 1` of the interval,
  when `e` is: the flow runs on the boundaryless `M`, out of `e q`, for the time `s - a`, which
  depends smoothly on `s` through the inclusion of `Set.Icc a b` into `ℝ`
  (`TauCeti.contMDiffAt_flowOf_comp`);
* if `f : M → ℝ` is continuous, `df(v) = 1` on an open set containing the band `f⁻¹([a, b])`,
  and `e` takes values in the level `f = a`, then `f` reads off the second coordinate,
  `f (bandMap v e a b (q, s)) = s`; the band map is injective when `e` is, and its range is the
  band when the range of `e` is the level. These are `TauCeti.apply_flowOf_sub_eq`,
  `TauCeti.flowOf_sub_level_injective` and `TauCeti.range_flowOf_sub_level` read through `e`;
* if a group `G` acts on `M` and on the right on `Q`, `v` is invariant and
  `e (q • g) = g • e q`, then `bandMap v e a b (q • g, s) = g • bandMap v e a b (q, s)`, since the
  flow commutes with the action (`TauCeti.smul_flowOf`); a map with this equivariance sends the
  field `(ξ♯, 0)` on `Q × [a, b]` to the fundamental vector field of `ξ` on `M`, by
  `TauCeti.mfderiv_rightFundamentalVectorField_of_map_op_smul_eq_smul` applied to its
  restriction `q ↦ bandMap v e a b (q, s)`.

In the converse of minimal coupling (McDuff–Salamon, Proposition 5.1.9), `M` carries a free
circle action on the band `H⁻¹([a, b])` of an invariant function `H`, `v` is the invariant field
of `SymplecticGeometry.exists_invariant_vectorField_mfderiv_eq_one`, and `e` is the
diffeomorphism `TauCeti.MapFiber.Atlas.totalSpaceDiffeomorph` from the total space of the circle
bundle of the level `H⁻¹(a)` (`GroupAction/RegularLevel.lean`) onto that level, followed by the
inclusion. The band map then identifies `P × [a, b]` with the band, equivariantly, with `H` as
the coordinate of the interval, and it sends `SymplecticGeometry.couplingField` to the
fundamental vector field of `SymplecticGeometry.circlePeriodOneGenerator` on `M`
(`SymplecticGeometry.mfderiv_bandMap_couplingField`).

The last section turns these properties into those of a coupling form. Let the circle action
preserve a closed two-form `σ` on `M`, with moment map `-μ` (`ι_{X_M} σ = -dH` for
`H = ⟨μ, circlePeriodOneGenerator⟩`). For any smooth `ψ : P × [a, b] → M` that is equivariant,
has `H ∘ ψ` the coordinate of the interval and sends `couplingField` to `X_M`, the form
`ψ^* σ` is closed (`TauCeti.SmoothForm.IsClosed.mpullback`), invariant (the composition law of
pull-backs), and has `ι_{(X, 0)} ψ^* σ = -dt`: `X_M` is a Hamiltonian vector field of `-H`,
and pulling back along `ψ` gives one of `-H ∘ ψ` for `ψ^* σ`
(`TauCeti.SmoothTwoForm.IsHamiltonianVectorField.mpullback`). Its slice at `t` is the
pull-back of `σ` along `ψ (·, t)`.

A point that the circle does not fix is not critical for `H` where `σ` is nondegenerate: the
moment map of `σ` is `-μ`, whose component `-H` has the critical points of `H`, and these are the
fixed points of the action
(`TauCeti.SmoothTwoForm.IsMomentMap.mem_criticalPoints_circlePeriodOneGenerator_iff`).

The file also proves that the family `τ` of a coupling form is smooth: its pull-backs along the
projection of `P` are the slices of the coupling form, and the projection has smooth local
sections (`TauCeti.ManifoldTotalSpace.exists_contMDiffOn_section`), so
`SymplecticGeometry.IsSmoothFamily.of_mpullback_prodMk_eq` applies.

## Main definitions

* `SymplecticGeometry.bandMap v e a b`: the map `(q, s) ↦ φ_{s - a} (e q)`.

## Main results

* `SymplecticGeometry.contMDiff_bandMap`: it is smooth.
* `SymplecticGeometry.apply_bandMap`, `SymplecticGeometry.bandMap_injective`,
  `SymplecticGeometry.range_bandMap`: the function `f` is the coordinate of the interval, and the
  band map is a bijection onto the band.
* `SymplecticGeometry.bandMap_op_smul`: it is equivariant.
* `SymplecticGeometry.mfderiv_bandMap_couplingField`: for a principal circle bundle `P`, the band
  map sends `couplingField` to the fundamental vector field of `circlePeriodOneGenerator`.
* `SymplecticGeometry.bandMap_orbitFiber`: all of these for the circle bundle of a regular level
  of an invariant function, with `e` the inclusion of the level after
  `TauCeti.MapFiber.Atlas.totalSpaceDiffeomorph`.
* `SymplecticGeometry.mpullback_op_smul_mpullback`,
  `SymplecticGeometry.interior_couplingField_mpullback`: for `σ` invariant with moment map
  `-μ` and `ψ` as above, `ψ^* σ` is invariant and `ι_{(X, 0)} ψ^* σ = -dt`.
* `SymplecticGeometry.mfderiv_ne_zero_of_notMem_fixedPoints`: for `σ` with moment map `-μ`,
  nondegenerate at a point that the circle does not fix, `dH` does not vanish there.
* `SymplecticGeometry.isCouplingForm_mpullback`: such a `ψ^* σ` is a coupling form for every
  family `τ` whose pull-backs `π^* (τ t)` are the pull-backs of `σ` along `ψ (·, t)`.
* `SymplecticGeometry.IsCouplingForm.isSmoothFamily`: the family of a coupling form is smooth.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Proposition 5.1.9 (the band of a free Hamiltonian circle action as a product).
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 9 (flows) and Chapter 20 (infinitesimal generators of actions).
-/

public section

noncomputable section

open Bundle Function Manifold MulOpposite Set TauCeti
open scoped ContDiff Manifold

namespace SymplecticGeometry

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {Q : Type*}
  {v : (x : M) → TangentSpace I x} {e : Q → M} {a b : ℝ}

variable (v e a b) in
/-- The **band map** `(q, s) ↦ φ_{s - a} (e q)` from `Q × [a, b]` to `M`, where `φ` is the
maximal flow of the vector field `v`: it flows the point `e q` for the time `s - a`. -/
def bandMap (x : Q × Icc a b) : M :=
  flowOf v ((x.2 : ℝ) - a) (e x.1)

theorem bandMap_def (x : Q × Icc a b) : bandMap v e a b x = flowOf v ((x.2 : ℝ) - a) (e x.1) :=
  (rfl)

/-- At the bottom of the interval, the band map is `e`. -/
@[simp]
theorem bandMap_left (q : Q) (h : a ∈ Icc a b) : bandMap v e a b (q, ⟨a, h⟩) = e q := by
  rw [bandMap_def, sub_self, flowOf_zero]

variable [T2Space M] [BoundarylessManifold I M]

/-- **The band map is smooth.** For a complete smooth vector field `v` on a Hausdorff
boundaryless manifold modelled on a complete space, and a smooth map `e`, the band map is smooth
for the product of the model of `Q` with the model `𝓡∂ 1` of the interval. -/
theorem contMDiff_bandMap [Fact (a < b)] [CompleteSpace E] [IsManifold I ∞ M]
    {EQ HQ : Type*} [NormedAddCommGroup EQ] [NormedSpace ℝ EQ] [TopologicalSpace HQ]
    {IQ : ModelWithCorners ℝ EQ HQ} [TopologicalSpace Q] [ChartedSpace HQ Q]
    (hv : ContMDiff I I.tangent ∞ (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)))
    (hcomplete : IsCompleteVectorField v) (he : ContMDiff IQ I ∞ e) :
    ContMDiff (IQ.prod (𝓡∂ 1)) I ∞ (bandMap v e a b) := fun _ ↦
  contMDiffAt_flowOf_comp (n := ⊤) le_top hv
    ((contMDiff_subtypeVal_Icc.comp contMDiff_snd).sub contMDiff_const).contMDiffAt
    (he.comp contMDiff_fst).contMDiffAt (hcomplete.mem_flowDomain _ _)

/-- **Equivariance of the band map.** Let a group `G` act `C¹` on `M`, and on the right on `Q`.
If the `C¹` field `v` is invariant and `e (q • g) = g • e q`, then the band map satisfies
`bandMap v e a b (q • g, s) = g • bandMap v e a b (q, s)`. -/
theorem bandMap_op_smul [IsManifold I 1 M] {G : Type*} [Group G] [MulAction G M]
    [ContMDiffConstSMul I 1 G M]
    [MulAction Gᵐᵒᵖ Q]
    (hv : ContMDiff I I.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)))
    (hinv : ∀ (g : G) (x : M), mfderiv I I (g • ·) x (v x) = v (g • x))
    (he : ∀ (g : G) (q : Q), e (op g • q) = g • e q) (g : G) (x : Q × Icc a b) :
    bandMap v e a b (op g • x.1, x.2) = g • bandMap v e a b x := by
  rw [bandMap_def, bandMap_def, he, smul_flowOf hv hinv]

omit [T2Space M] [BoundarylessManifold I M] in
/-- If `e` takes values in the level `f = a`, the band map is the map `(x, s) ↦ φ_{s - a} x` on
`{x // f x = a} × [a, b]`, composed with `e` on the first factor. -/
theorem bandMap_eq_comp {f : M → ℝ} (he : ∀ q, f (e q) = a) :
    bandMap v e a b = (fun p : {x : M // f x = a} × Icc a b ↦ flowOf v (p.2 - a) p.1) ∘
      Prod.map (fun q ↦ ⟨e q, he q⟩) id :=
  funext fun x ↦ bandMap_def x

section Band

variable [IsManifold I 1 M]
  (hv : ContMDiff I I.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)))
  (hcomplete : IsCompleteVectorField v) {f : M → ℝ} (hf : Continuous f) {W : Set M}
  (hW : IsOpen W) (hfv : ∀ y ∈ W, mfderiv I 𝓘(ℝ) f y (v y) = 1)
  (hband : f ⁻¹' Icc a b ⊆ W)
include hv hcomplete hf hW hfv hband

/-- **The function is the coordinate of the interval.** Let `v` be a complete `C¹` vector field
and `f` a continuous function with `df(v) = 1` on an open set containing the band `f⁻¹([a, b])`.
If `e` takes values in the level `f = a`, then `f (bandMap v e a b (q, s)) = s`. -/
theorem apply_bandMap (he : ∀ q, f (e q) = a) (x : Q × Icc a b) :
    f (bandMap v e a b x) = x.2 :=
  apply_flowOf_sub_eq hv hcomplete hf hW hfv hband (he x.1) x.2.property

/-- **The band map is injective** when `e` is, under the hypotheses of
`SymplecticGeometry.apply_bandMap`. -/
theorem bandMap_injective (he : ∀ q, f (e q) = a) (he' : Injective e) :
    Injective (bandMap v e a b) := by
  rw [bandMap_eq_comp he]
  exact (flowOf_sub_level_injective hv hcomplete hf hW hfv hband).comp
    (Injective.prodMap (fun q q' h ↦ he' (congrArg Subtype.val h)) injective_id)

/-- **The band map sweeps out the band.** Under the hypotheses of
`SymplecticGeometry.apply_bandMap`, if the range of `e` is the level `f = a`, then the range of
the band map is the band `f⁻¹([a, b])`. -/
theorem range_bandMap (he : range e = {x | f x = a}) :
    range (bandMap v e a b) = f ⁻¹' Icc a b := by
  have he' (q : Q) : f (e q) = a := (he.le (mem_range_self q) :)
  have hsurj : Surjective
      (Prod.map (fun q ↦ (⟨e q, he' q⟩ : {x : M // f x = a})) (id : Icc a b → Icc a b)) := by
    refine Surjective.prodMap (fun x ↦ ?_) surjective_id
    obtain ⟨q, hq⟩ := he.ge x.property
    exact ⟨q, Subtype.ext hq⟩
  rw [bandMap_eq_comp he', hsurj.range_comp, range_flowOf_sub_level hv hcomplete hf hW hfv hband]

end Band

variable [Fact (a < b)] [IsManifold I ∞ M] [MulAction Circle M]

/-! ### The coupling field -/

section CouplingField

variable {EB HB B : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  {IB : ModelWithCorners ℝ EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  {P : B → Type*} [TopologicalSpace (TotalSpace Circle P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle Circle P] [∀ b, MulAction Circleᵐᵒᵖ (P b)]
  [PrincipalBundle Circle P] [CompleteSpace E] [ContMDiffConstSMul I 1 Circle M]

/-- **The band map relates the fundamental fields.** Let a circle act on `M`, and let `P` be a
principal circle bundle. If the complete smooth field `v` is invariant and the smooth map
`e` from the total space of `P` to `M` satisfies `e (p • z) = z • e p`, then the band map sends
the field `couplingField IB P a b` on `P × [a, b]` to the fundamental vector field of
`circlePeriodOneGenerator` on `M`. -/
theorem mfderiv_bandMap_couplingField {e : ManifoldTotalSpace Circle P → M}
    (hv : ContMDiff I I.tangent ∞ (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)))
    (hcomplete : IsCompleteVectorField v)
    (hinv : ∀ (g : Circle) (x : M), mfderiv I I (g • ·) x (v x) = v (g • x))
    (he : ContMDiff (IB.prod (𝓡 1)) I ∞ e)
    (he' : ∀ (g : Circle) (p : ManifoldTotalSpace Circle P), e (op g • p) = g • e p)
    (x : ManifoldTotalSpace Circle P × Icc a b) :
    mfderiv ((IB.prod (𝓡 1)).prod (𝓡∂ 1)) I (bandMap v e a b) x (couplingField IB P a b x) =
      fundamentalVectorField I circlePeriodOneGenerator (bandMap v e a b x) := by
  have hψ := (contMDiff_bandMap hv hcomplete he x).mdifferentiableAt (by simp)
  have hk : MDifferentiableAt (IB.prod (𝓡 1)) ((IB.prod (𝓡 1)).prod (𝓡∂ 1))
      (fun q ↦ (q, x.2)) x.1 :=
    mdifferentiableAt_id.prodMk mdifferentiableAt_const
  have hk' : mfderiv (IB.prod (𝓡 1)) ((IB.prod (𝓡 1)).prod (𝓡∂ 1)) (fun q ↦ (q, x.2)) x.1
      (rightFundamentalVectorField (IB.prod (𝓡 1)) circlePeriodOneGenerator x.1) =
      couplingField IB P a b x := by
    rw [mfderiv_prod_left, couplingField_def]
    -- The tangent space of `P × [a, b]` at `x` is by definition the product of the tangent
    -- spaces, in which `ContinuousLinearMap.inl` sends `w` to `(w, 0)`.
    rfl
  rw [← hk', ← mfderiv_comp_apply_of_eq x.1 hψ hk rfl]
  exact mfderiv_rightFundamentalVectorField_of_map_op_smul_eq_smul
    (f := bandMap v e a b ∘ fun q ↦ (q, x.2)) (hψ.comp x.1 hk)
    (PrincipalBundle.mdifferentiableAt_orbit (n := ∞) (by simp) x.1 1)
    (bandMap_op_smul (hv.of_le (by simp)) hinv he' · x) circlePeriodOneGenerator

end CouplingField

/-! ### The pull-back of an invariant form by an equivariant map -/

section Pullback

variable {EB HB B : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  {IB : ModelWithCorners ℝ EB HB} [TopologicalSpace B] [ChartedSpace HB B] [IsManifold IB ∞ B]
  {P : B → Type*} [TopologicalSpace (TotalSpace Circle P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle Circle P] [∀ b, MulAction Circleᵐᵒᵖ (P b)]
  [PrincipalBundle Circle P] [ContMDiffFiberBundle ∞ Circle P IB (𝓡 1)]
  [CompleteSpace E] [ContMDiffSMul (𝓡 1) I ∞ Circle M]
  {ψ : ManifoldTotalSpace Circle P × Icc a b → M}
  (hψ : ContMDiff ((IB.prod (𝓡 1)).prod (𝓡∂ 1)) I ∞ ψ) {σ : SmoothTwoForm I M}

omit [T2Space M] [BoundarylessManifold I M] [CompleteSpace E] in
/-- **Invariance of the pull-back.** If the two-form `σ` on `M` is invariant under the circle
action and `ψ : P × [a, b] → M` is equivariant, `ψ (p • z, t) = z • ψ (p, t)`, then `ψ^* σ` is
invariant under the circle action `(p, t) ↦ (p • z, t)` on the first factor. -/
theorem mpullback_op_smul_mpullback
    (hσ : ∀ g : Circle, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := 𝓡 1) (I' := I) g) σ = σ)
    (hψs : ∀ (z : Circle) (x : ManifoldTotalSpace Circle P × Icc a b),
      ψ (op z • x.1, x.2) = z • ψ x) (z : Circle) :
    SmoothForm.mpullback (fun x : ManifoldTotalSpace Circle P × Icc a b ↦ (op z • x.1, x.2))
        (((contMDiff_const_smul (op z)).comp contMDiff_fst).prodMk contMDiff_snd)
        (SmoothForm.mpullback ψ hψ σ) =
      SmoothForm.mpullback ψ hψ σ := by
  conv_rhs => rw [← hσ z]
  exact SmoothForm.mpullback_mpullback_of_comp_eq _ hψ hψ _ (funext (hψs z)) σ

omit [T2Space M] [BoundarylessManifold I M] [PrincipalBundle Circle P] in
/-- **The Hamiltonian identity of the pull-back.** Let a circle act smoothly on `M`, and let
`-μ` be a moment map of the action for the two-form `σ`, so that `ι_{X_M} σ = -d H` with
`H = ⟨μ, circlePeriodOneGenerator⟩` and `X_M` the fundamental vector field of
`circlePeriodOneGenerator`. If `ψ : P × [a, b] → M` sends the field `couplingField IB P a b` to
`X_M` and `H (ψ (p, t)) = t`, then the contraction of `ψ^* σ` with `couplingField IB P a b` is
`-dt`. -/
theorem interior_couplingField_mpullback
    {μ : M → Module.Dual ℝ (GroupLieAlgebra (𝓡 1) Circle)}
    (hμ : σ.IsMomentMap (InfinitesimalAction.fundamental (𝓡 1) Circle I M) fun x ↦ -μ x)
    (hH : ∀ x, μ (ψ x) circlePeriodOneGenerator = x.2)
    (hX : ∀ x, mfderiv ((IB.prod (𝓡 1)).prod (𝓡∂ 1)) I ψ x (couplingField IB P a b x) =
      fundamentalVectorField I circlePeriodOneGenerator (ψ x)) :
    RoughForm.interior (couplingField IB P a b) (SmoothForm.mpullback ψ hψ σ).val =
      -mextDeriv (RoughForm.ofFunction ((IB.prod (𝓡 1)).prod (𝓡∂ 1))
        fun x : ManifoldTotalSpace Circle P × Icc a b ↦ (x.2 : ℝ)) := by
  have h := (hμ.isHamiltonianVectorField circlePeriodOneGenerator).mpullback hψ
    (fun x ↦ hμ.mdifferentiableAt _ (ψ x)) (by simpa only [InfinitesimalAction.fundamental_apply])
  have hcomp : ((fun x ↦ (-μ x) circlePeriodOneGenerator) ∘ ψ) =
      (-1 : ℝ) • fun x : ManifoldTotalSpace Circle P × Icc a b ↦ (x.2 : ℝ) :=
    funext fun x ↦ by simp [hH]
  rwa [hcomp, SmoothTwoForm.isHamiltonianVectorField_iff_interior_eq, RoughForm.ofFunction_smul,
    mextDeriv_smul, neg_one_smul] at h

omit [T2Space M] [BoundarylessManifold I M] in
/-- **The pull-back of an invariant form with a moment map is a coupling form.** Let a circle act
smoothly on `M`, preserving the closed two-form `σ`, with moment map `-μ`, and let
`H = ⟨μ, circlePeriodOneGenerator⟩`. Let `ψ : P × [a, b] → M` be smooth and equivariant,
`ψ (p • z, t) = z • ψ (p, t)`, with `H (ψ (p, t)) = t`, sending the field
`couplingField IB P a b` to the fundamental vector field of `circlePeriodOneGenerator`. If, for
each `t`, the pull-back of `σ` along `ψ (·, t)` is `π^* (τ t)`, then `ψ^* σ` is a coupling form
for `τ`. -/
theorem isCouplingForm_mpullback (hσc : σ.IsClosed)
    (hσ : ∀ g : Circle, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := 𝓡 1) (I' := I) g) σ = σ)
    {μ : M → Module.Dual ℝ (GroupLieAlgebra (𝓡 1) Circle)}
    (hμ : σ.IsMomentMap (InfinitesimalAction.fundamental (𝓡 1) Circle I M) fun x ↦ -μ x)
    (hψs : ∀ (z : Circle) (x : ManifoldTotalSpace Circle P × Icc a b),
      ψ (op z • x.1, x.2) = z • ψ x)
    (hH : ∀ x, μ (ψ x) circlePeriodOneGenerator = x.2)
    (hX : ∀ x, mfderiv ((IB.prod (𝓡 1)).prod (𝓡∂ 1)) I ψ x (couplingField IB P a b x) =
      fundamentalVectorField I circlePeriodOneGenerator (ψ x))
    {τ : Icc a b → SmoothTwoForm IB B}
    (hτ : ∀ t, SmoothForm.mpullback (fun p : ManifoldTotalSpace Circle P ↦ ψ (p, t))
        (hψ.comp (contMDiff_id.prodMk contMDiff_const)) σ =
      SmoothForm.mpullback (ManifoldTotalSpace.projContMDiffMap ∞ Circle P IB (𝓡 1))
        (ManifoldTotalSpace.projContMDiffMap ∞ Circle P IB (𝓡 1)).contMDiff (τ t)) :
    IsCouplingForm (SmoothForm.mpullback ψ hψ σ) τ where
  isClosed := hσc.mpullback ψ hψ
  mpullback_smul := mpullback_op_smul_mpullback hψ hσ hψs
  interior_eq := interior_couplingField_mpullback hψ hμ hH hX
  mpullback_slice t := by
    simpa only [SmoothForm.mpullback_mpullback, Function.comp_def,
      ManifoldTotalSpace.coe_projContMDiffMap] using hτ t

end Pullback

/-! ### Points off the fixed set are regular for the Hamiltonian -/

section Regular

variable [CompleteSpace E] [ContMDiffSMul (𝓡 1) I ∞ Circle M]

/-- **A point off the fixed set is not critical for the Hamiltonian.** Let a circle act smoothly
on a Hausdorff boundaryless manifold `M`, with moment map `-μ` for a two-form `σ`, and let
`H = ⟨μ, circlePeriodOneGenerator⟩`. If `σ` is nondegenerate at `x` and some element of the
circle moves `x`, then `dH` does not vanish at `x`. -/
theorem mfderiv_ne_zero_of_notMem_fixedPoints {σ : SmoothTwoForm I M}
    {μ : M → Module.Dual ℝ (GroupLieAlgebra (𝓡 1) Circle)}
    (hμ : σ.IsMomentMap (InfinitesimalAction.fundamental (𝓡 1) Circle I M) fun x ↦ -μ x)
    {x : M} (hσ : (σ.bilinFormAt x).Nondegenerate) (hx : x ∉ MulAction.fixedPoints Circle M) :
    mfderiv I 𝓘(ℝ) (fun y ↦ μ y circlePeriodOneGenerator) x ≠ 0 := by
  have hneg : (fun y ↦ (-μ y) circlePeriodOneGenerator) = -fun y ↦ μ y circlePeriodOneGenerator :=
    funext fun _ ↦ LinearMap.neg_apply _ _
  rwa [← hμ.mem_criticalPoints_circlePeriodOneGenerator_iff hσ, hneg, criticalPoints_neg,
    mem_criticalPoints_iff_mfderiv_eq_zero] at hx

end Regular

/-! ### The band of a circle action -/

section RegularLevel

attribute [local instance] MulOpposite.chartedSpace

variable [FiniteDimensional ℝ E] [I.Boundaryless] [ContMDiffSMul (𝓡 1) I ∞ Circle M]
  {f : M → ℝ} {n : ℕ}

omit [BoundarylessManifold I M] in
/-- **The band of a circle action as a product.** Let a circle act smoothly on a Hausdorff
boundaryless finite-dimensional manifold `M`, let `f : M → ℝ` be smooth and invariant, with
regular value `a`, and let the action be free on the level `P₀ = f⁻¹(a)`. Let `P` be the circle
bundle `orbitFiber` of `P₀`, built with the local instances of `GroupAction/RegularLevel.lean`, and
`e` the diffeomorphism `TauCeti.MapFiber.Atlas.totalSpaceDiffeomorph` from its total space onto
`P₀`, followed by the inclusion into `M`. Let `v` be a complete, smooth, invariant vector field
with `df(v) = 1` on an open set containing the band `f⁻¹([a, b])`. Then the band map
`ψ = bandMap v e a b : P × [a, b] → M`
* is smooth;
* is equivariant: `ψ (p • z, s) = z • ψ (p, s)`;
* satisfies `f (ψ (p, s)) = s`;
* is injective, with the band `f⁻¹([a, b])` as its range;
* sends `couplingField` to the fundamental vector field of `circlePeriodOneGenerator`. -/
theorem bandMap_orbitFiber (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hreg : IsRegularValue I 𝓘(ℝ) f a)
    (hn : Module.finrank ℝ E - Module.finrank ℝ ℝ = n)
    (hinv : ∀ (g : Circle) (x : M), f (g • x) = f x)
    (hfree : ∀ x, f x = a → MulAction.stabilizer Circle x = ⊥)
    (hv : ContMDiff I I.tangent ∞ (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)))
    (hcomplete : IsCompleteVectorField v)
    (hvinv : ∀ (g : Circle) (x : M), mfderiv I I (g • ·) x (v x) = v (g • x)) {W : Set M}
    (hW : IsOpen W) (hfv : ∀ y ∈ W, mfderiv I 𝓘(ℝ) f y (v y) = 1)
    (hband : f ⁻¹' Icc a b ⊆ W) :
    letI := regularLevelChartedSpace (fun x _ ↦ hf.contMDiffAt.of_le (by simp)) hreg hn
    letI := levelOpMulAction a hinv
    haveI := isManifold_regularLevel (by simp) (fun x _ ↦ hf.contMDiffAt) hreg hn
    haveI := contMDiffSMul_levelOpMulAction (by simp) (fun x _ ↦ hf.contMDiffAt) hreg hn hinv
      (IG := 𝓡 1)
    haveI := ContMDiffSMul.continuousSMul (I := 𝓡 1) (I' := I) (G := Circle) (M := M) ∞
    haveI := properSMul_levelOpMulAction (c := a) hinv
    haveI := isCancelSMul_levelOpMulAction hinv hfree
    letI := ProperSMul.orbitRelQuotientChartedSpace (𝓡 1) Circleᵐᵒᵖ 𝓘(ℝ, Fin n → ℝ)
      {x : M // f x = a}
    letI := (orbitFiber.atlas (𝓡 1) Circle 𝓘(ℝ, Fin n → ℝ) {x : M // f x = a}).fiberBundle
    haveI := orbitFiber.principalBundle (𝓡 1) Circle 𝓘(ℝ, Fin n → ℝ) {x : M // f x = a}
    haveI := (orbitFiber.atlas (𝓡 1) Circle 𝓘(ℝ, Fin n → ℝ) {x : M // f x = a})
      |>.contMDiffFiberBundle
      (orbitFiber.isContMDiff_atlas (𝓡 1) Circle 𝓘(ℝ, Fin n → ℝ) {x : M // f x = a})
    let IB := 𝓘(ℝ, ProperSMul.QuotientModelSpace (EuclideanSpace ℝ (Fin 1)) (Fin n → ℝ))
    let P := orbitFiber Circleᵐᵒᵖ {x : M // f x = a}
    let e : ManifoldTotalSpace Circle P → M := fun p ↦
      ((orbitFiber.atlas (𝓡 1) Circle 𝓘(ℝ, Fin n → ℝ) {x : M // f x = a}).totalSpaceDiffeomorph
        (orbitFiber.isContMDiff_atlas (𝓡 1) Circle 𝓘(ℝ, Fin n → ℝ) {x : M // f x = a}) p : M)
    ContMDiff ((IB.prod (𝓡 1)).prod (𝓡∂ 1)) I ∞ (bandMap v e a b) ∧
      (∀ (g : Circle) (x : ManifoldTotalSpace Circle P × Icc a b),
        bandMap v e a b (op g • x.1, x.2) = g • bandMap v e a b x) ∧
      (∀ x, f (bandMap v e a b x) = x.2) ∧ Injective (bandMap v e a b) ∧
      range (bandMap v e a b) = f ⁻¹' Icc a b ∧
      ∀ x, mfderiv ((IB.prod (𝓡 1)).prod (𝓡∂ 1)) I (bandMap v e a b) x
          (couplingField IB P a b x) =
        fundamentalVectorField I circlePeriodOneGenerator (bandMap v e a b x) := by
  let := regularLevelChartedSpace (fun x _ ↦ hf.contMDiffAt.of_le (by simp)) hreg hn
  let := levelOpMulAction a hinv
  have := isManifold_regularLevel (by simp) (fun x _ ↦ hf.contMDiffAt) hreg hn
  have := contMDiffSMul_levelOpMulAction (by simp) (fun x _ ↦ hf.contMDiffAt) hreg hn hinv
    (IG := 𝓡 1)
  have := ContMDiffSMul.continuousSMul (I := 𝓡 1) (I' := I) (G := Circle) (M := M) ∞
  have := properSMul_levelOpMulAction (c := a) hinv
  have := isCancelSMul_levelOpMulAction hinv hfree
  let := ProperSMul.orbitRelQuotientChartedSpace (𝓡 1) Circleᵐᵒᵖ 𝓘(ℝ, Fin n → ℝ)
    {x : M // f x = a}
  let := (orbitFiber.atlas (𝓡 1) Circle 𝓘(ℝ, Fin n → ℝ) {x : M // f x = a}).fiberBundle
  have := orbitFiber.principalBundle (𝓡 1) Circle 𝓘(ℝ, Fin n → ℝ) {x : M // f x = a}
  have := (orbitFiber.atlas (𝓡 1) Circle 𝓘(ℝ, Fin n → ℝ) {x : M // f x = a})
    |>.contMDiffFiberBundle
    (orbitFiber.isContMDiff_atlas (𝓡 1) Circle 𝓘(ℝ, Fin n → ℝ) {x : M // f x = a})
  have : ContMDiffConstSMul I 1 Circle M := ContMDiffSMul.contMDiffConstSMul (𝓡 1) (n := 1)
  set D := (orbitFiber.atlas (𝓡 1) Circle 𝓘(ℝ, Fin n → ℝ) {x : M // f x = a})
    |>.totalSpaceDiffeomorph
    (orbitFiber.isContMDiff_atlas (𝓡 1) Circle 𝓘(ℝ, Fin n → ℝ) {x : M // f x = a})
  have heq (g : Circle)
      (p : ManifoldTotalSpace Circle (orbitFiber Circleᵐᵒᵖ {x : M // f x = a})) :
      (D (op g • p) : M) = g • (D p : M) := by
    rw [MapFiber.Atlas.totalSpaceDiffeomorph_smul (a := op g) (x := p)
      (hproj := fun _ _ ↦ MulAction.orbitRel.Quotient.quotient_smul_eq) _,
      coe_levelOpMulAction_smul, unop_op]
  have hesmooth : ContMDiff _ I ∞ fun p ↦ (D p : M) :=
    (isSmoothEmbedding_coe_regularLevel (by simp) (fun x _ ↦ hf.contMDiffAt) hreg hn).contMDiff
      |>.comp D.contMDiff
  have hlev (p) : f (D p : M) = a := (D p).property
  refine ⟨contMDiff_bandMap hv hcomplete hesmooth,
    bandMap_op_smul (hv.of_le (by simp)) hvinv heq,
    apply_bandMap (hv.of_le (by simp)) hcomplete hf.continuous hW hfv hband hlev,
    bandMap_injective (hv.of_le (by simp)) hcomplete hf.continuous hW hfv hband hlev
      (Subtype.val_injective.comp D.injective),
    range_bandMap (hv.of_le (by simp)) hcomplete hf.continuous hW hfv hband ?_,
    mfderiv_bandMap_couplingField hv hcomplete hvinv hesmooth heq⟩
  exact (D.surjective.range_comp Subtype.val).trans Subtype.range_coe_subtype

end RegularLevel

/-! ### Smoothness of the family of reduced forms -/

section SmoothFamily

variable {EB HB B : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  {IB : ModelWithCorners ℝ EB HB} [TopologicalSpace B] [ChartedSpace HB B] [IsManifold IB ∞ B]
  {P : B → Type*} [TopologicalSpace (TotalSpace Circle P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle Circle P] [ContMDiffFiberBundle ∞ Circle P IB (𝓡 1)]
  {σ : SmoothTwoForm ((IB.prod (𝓡 1)).prod (𝓡∂ 1)) (ManifoldTotalSpace Circle P × Icc a b)}
  {τ : Icc a b → SmoothTwoForm IB B}

/-- **The family of a coupling form is smooth.** If `σ` is a coupling form for a family `τ` of
two-forms on the base, then `τ` is a smooth family. -/
theorem IsCouplingForm.isSmoothFamily [∀ b, MulAction Circleᵐᵒᵖ (P b)] [PrincipalBundle Circle P]
    (hσ : IsCouplingForm σ τ) : IsSmoothFamily (𝓡∂ 1) τ :=
  IsSmoothFamily.of_mpullback_prodMk_eq
    (ManifoldTotalSpace.projContMDiffMap ∞ Circle P IB (𝓡 1)).contMDiff
    (ManifoldTotalSpace.exists_contMDiffOn_section ∞ Circle P IB (𝓡 1)) hσ.mpullback_slice

end SmoothFamily

end SymplecticGeometry

end
