/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Analysis.Complex.Circle
public import SymplecticGeometry.Geometry.Lie.FundamentalVectorField
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.SmoothFamily.Basic
public import SymplecticGeometry.Geometry.Manifold.Flow.Basic
public import SymplecticGeometry.Geometry.Manifold.GroupAction.RegularLevel
public import SymplecticGeometry.Geometry.Manifold.GroupAction.TranslatingField
public import SymplecticGeometry.Geometry.Symplectic.Coupling.Basic
public import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.Circle
public import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.ContMDiff
public import SymplecticGeometry.GroupTheory.GroupAction.FixedPoints
public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap.ReducedForm
import SymplecticGeometry.Geometry.Manifold.MFDeriv.Prod

/-!
# The converse of minimal coupling

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
* each slice `q ↦ bandMap v e a b (q, t)` is `φ_{t - a} ∘ e`, so it has injective differential
  exactly where `e` does, since the time-`(t - a)` map is a diffeomorphism
  (`TauCeti.globalFlowDiffeomorph`, `Diffeomorph.mfderiv_diffeomorph_comp_injective_iff`).
  Under the hypotheses of the second item, `f` is constant on the slice and `df(v) = 1` makes
  its points regular, so if `e` comes from a model space of dimension `dim M - 1`, the tangent
  image of the slice is `ker df`
  (`TauCeti.IsRegularPoint.range_mfderiv_eq_ker_mfderiv`).

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

For the reduced forms, let `σ` be symplectic. A smooth map `φ` from the total space of a
principal circle bundle `P` to `M`, equivariant, with values in a level `H = t`, injective
differential and tangent images `ker dH`, is level data for Tau Ceti's reduction of a level of a
moment map (`TauCeti.SmoothTwoForm.IsMomentMap.existsUnique_isSymplectic_mpullback_eq_mpullback`),
with the right circle action on the total space: the cocycle of `-μ` vanishes and
`ker d(-μ) = ker dH`, since the Lie algebra of `Circle` is one-dimensional, the vertical vectors of
`P` are the multiples of its fundamental field, which `dφ` sends to the orbit directions of `M`,
and the fibres of `P` are orbits. So `φ^* σ` is the pull-back of a unique symplectic form on the
base. The invariance of `φ^* σ` under the action on the total space is proved as in Tau Ceti's
`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.existsUnique_isSymplectic_mpullback_eq_mpullback`.
The slices of the band map of a circle action are such maps.

The last section puts these together into the converse of minimal coupling
(`SymplecticGeometry.exists_isCouplingForm_comp_eq`). Let the circle preserve a symplectic form
`σ` with moment map `-μ`, and let the band `K = H⁻¹([a, b])` be compact with the action free on
it. Then `H` has no critical point on `K`, so `a` is a regular value of `H` and
`SymplecticGeometry.exists_invariant_vectorField_mfderiv_eq_one` gives the field `v`; `H` is
invariant (`TauCeti.SmoothTwoForm.IsMomentMap.apply_smul_circle`). The band map of `v` and of the
circle bundle of `H⁻¹(a)` is the map `ψ`, the reduced forms of its slices are the family `τ`, and
`ψ^* σ` is a coupling form for `τ`, whose classes then move as
`SymplecticGeometry.IsCouplingForm.mk_sub_mk_eq_neg_smul_realFirstChernClass` says.

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
* `SymplecticGeometry.injective_mfderiv_bandMap_slice_iff`,
  `SymplecticGeometry.range_mfderiv_bandMap_slice`: the slices of the band map have injective
  differential exactly where `e` does, with tangent images `ker df`.
* `SymplecticGeometry.bandMap_orbitFiber_slice`: in the setting of `bandMap_orbitFiber`, each
  slice has injective differential with range `ker df`.
* `SymplecticGeometry.mpullback_op_smul_mpullback`,
  `SymplecticGeometry.interior_couplingField_mpullback`: for `σ` invariant with moment map
  `-μ` and `ψ` as above, `ψ^* σ` is invariant and `ι_{(X, 0)} ψ^* σ = -dt`.
* `SymplecticGeometry.mfderiv_ne_zero_of_notMem_fixedPoints`: for `σ` with moment map `-μ`,
  nondegenerate at a point that the circle does not fix, `dH` does not vanish there.
* `SymplecticGeometry.isCouplingForm_mpullback`: such a `ψ^* σ` is a coupling form for every
  family `τ` whose pull-backs `π^* (τ t)` are the pull-backs of `σ` along `ψ (·, t)`.
* `SymplecticGeometry.existsUnique_isSymplectic_mpullback_projContMDiffMap_eq`: for `σ` symplectic,
  an equivariant map `φ` from the total space of `P` into a level of `H`, with injective
  differential and tangent images `ker dH`, has `φ^* σ = π^* τ` for a unique symplectic `τ`.
* `SymplecticGeometry.existsUnique_isSymplectic_mpullback_eq_mpullback_bandMap`: in the setting of
  `bandMap_orbitFiber`, with `f = H`, each slice of the band map pulls `σ` back to the pull-back
  of a unique symplectic form on the base.
* `SymplecticGeometry.IsCouplingForm.isSmoothFamily`: the family of a coupling form is smooth.
* `SymplecticGeometry.isRegularValue_of_notMem_fixedPoints`: a level that contains no fixed
  point of the action is a regular value of `H`.
* `SymplecticGeometry.exists_isCouplingForm_comp_eq`: the converse of minimal coupling.

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

variable [T2Space M]

/-- **The band map is smooth.** For a complete smooth vector field `v` on a Hausdorff
boundaryless manifold modelled on a complete space, and a smooth map `e`, the band map is smooth
for the product of the model of `Q` with the model `𝓡∂ 1` of the interval. -/
theorem contMDiff_bandMap [Fact (a < b)] [CompleteSpace E] [BoundarylessManifold I M]
    [IsManifold I ∞ M]
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
theorem bandMap_op_smul [BoundarylessManifold I M] [IsManifold I 1 M] {G : Type*} [Group G]
    [MulAction G M] [ContMDiffConstSMul I 1 G M]
    [MulAction Gᵐᵒᵖ Q]
    (hv : ContMDiff I I.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)))
    (hinv : ∀ (g : G) (x : M), mfderiv I I (g • ·) x (v x) = v (g • x))
    (he : ∀ (g : G) (q : Q), e (op g • q) = g • e q) (g : G) (x : Q × Icc a b) :
    bandMap v e a b (op g • x.1, x.2) = g • bandMap v e a b x := by
  rw [bandMap_def, bandMap_def, he, smul_flowOf hv hinv]

omit [T2Space M] in
/-- If `e` takes values in the level `f = a`, the band map is the map `(x, s) ↦ φ_{s - a} x` on
`{x // f x = a} × [a, b]`, composed with `e` on the first factor. -/
theorem bandMap_eq_comp {f : M → ℝ} (he : ∀ q, f (e q) = a) :
    bandMap v e a b = (fun p : {x : M // f x = a} × Icc a b ↦ flowOf v (p.2 - a) p.1) ∘
      Prod.map (fun q ↦ ⟨e q, he q⟩) id :=
  funext fun x ↦ bandMap_def x

omit [T2Space M] in
/-- The slice `q ↦ bandMap v e a b (q, t)` of the band map is the time-`(t - a)` map of the flow
after `e`. -/
theorem bandMap_slice (t : Icc a b) :
    (fun q ↦ bandMap v e a b (q, t)) = flowOf v ((t : ℝ) - a) ∘ e :=
  funext fun q ↦ bandMap_def (q, t)

section Slice

variable [BoundarylessManifold I M] [IsManifold I 1 M] [CompleteSpace E]
  {EQ HQ : Type*} [NormedAddCommGroup EQ] [NormedSpace ℝ EQ] [TopologicalSpace HQ]
  {IQ : ModelWithCorners ℝ EQ HQ} [TopologicalSpace Q] [ChartedSpace HQ Q]
  (hv : ContMDiff I I.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)))
  (hcomplete : IsCompleteVectorField v) {q : Q}
include hv hcomplete

/-- **The slices of the band map have injective differential exactly where `e` does.** For a
complete `C¹` vector field `v` on a Hausdorff boundaryless manifold modelled on a complete space,
the slice `q ↦ bandMap v e a b (q, t)` has injective differential at `q` if and only if `e` does,
since it is `e` followed by a diffeomorphism. -/
theorem injective_mfderiv_bandMap_slice_iff (t : Icc a b) :
    Injective (mfderiv IQ I (fun q ↦ bandMap v e a b (q, t)) q) ↔
      Injective (mfderiv IQ I e q) := by
  rw [bandMap_slice, flowOf_eq_globalFlow hv hcomplete,
    ← coe_globalFlowDiffeomorph hcomplete le_rfl hv]
  exact Diffeomorph.mfderiv_diffeomorph_comp_injective_iff _ one_ne_zero

end Slice

section Band

variable [BoundarylessManifold I M] [IsManifold I 1 M]
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

/-- **The slices of the band map have tangent images `ker df`.** Under the hypotheses of
`SymplecticGeometry.apply_bandMap`, on a finite-dimensional manifold,
let `e` have injective differential at `q`, from a model space of dimension one less than
that of `M`. Then the range of the differential at `q` of the slice
`q ↦ bandMap v e a b (q, t)` is the kernel of `df` at its image. -/
theorem range_mfderiv_bandMap_slice [FiniteDimensional ℝ E]
    {EQ HQ : Type*} [NormedAddCommGroup EQ] [NormedSpace ℝ EQ] [TopologicalSpace HQ]
    {IQ : ModelWithCorners ℝ EQ HQ} [TopologicalSpace Q] [ChartedSpace HQ Q]
    (he : ∀ q, f (e q) = a) {q : Q} (he' : Injective (mfderiv IQ I e q))
    (hdim : Module.finrank ℝ EQ = Module.finrank ℝ E - 1) (t : Icc a b) :
    LinearMap.range (mfderiv IQ I (fun q ↦ bandMap v e a b (q, t)) q).toLinearMap =
      LinearMap.ker (mfderiv I 𝓘(ℝ) f (bandMap v e a b (q, t))).toLinearMap := by
  set y := bandMap v e a b (q, t)
  have hy : y ∈ W := hband (by simp [y, apply_bandMap hv hcomplete hf hW hfv hband he])
  -- `df (v y) = 1`, so `y` is a regular point of `f`.
  have hreg : IsRegularPoint I 𝓘(ℝ) f y := isRegularPoint_iff.mpr fun (r : ℝ) ↦
    ⟨r • v y, by rw [ContinuousLinearMap.map_smul, hfv y hy]; exact mul_one r⟩
  have hker := hreg.finrank_ker_mfderiv_add_finrank
  rw [Module.finrank_self] at hker
  exact hreg.range_mfderiv_eq_ker_mfderiv
    (Filter.Eventually.of_forall (p := fun q ↦ f (bandMap v e a b (q, t)) = t)
      fun q ↦ apply_bandMap hv hcomplete hf hW hfv hband he (q, t))
    ((injective_mfderiv_bandMap_slice_iff hv hcomplete t).mpr he')
    (by rw [Module.finrank_self]; omega)

end Band

variable [Fact (a < b)] [IsManifold I ∞ M] [MulAction Circle M]

/-! ### The coupling field -/

section CouplingField

variable {EB HB B : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  {IB : ModelWithCorners ℝ EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  {P : B → Type*} [TopologicalSpace (TotalSpace Circle P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle Circle P] [∀ b, MulAction Circleᵐᵒᵖ (P b)]
  [PrincipalBundle Circle P] [CompleteSpace E] [ContMDiffConstSMul I 1 Circle M]
  [BoundarylessManifold I M]

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
    rw [couplingField_def]
    exact mfderiv_prodMk_left_apply _
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

omit [T2Space M] [CompleteSpace E] in
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

omit [T2Space M] [PrincipalBundle Circle P] in
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

omit [T2Space M] in
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

variable [BoundarylessManifold I M] [CompleteSpace E] [ContMDiffSMul (𝓡 1) I ∞ Circle M]

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

/-- **A level without fixed points is a regular value of the Hamiltonian.** Let a circle act
smoothly on a Hausdorff boundaryless manifold `M`, with moment map `-μ` for a nondegenerate
two-form `σ`, and let `H = ⟨μ, circlePeriodOneGenerator⟩`. If no point of the level `H = c` is
fixed by the whole circle, then `c` is a regular value of `H`. -/
theorem isRegularValue_of_notMem_fixedPoints {σ : SmoothTwoForm I M}
    {μ : M → Module.Dual ℝ (GroupLieAlgebra (𝓡 1) Circle)}
    (hμ : σ.IsMomentMap (InfinitesimalAction.fundamental (𝓡 1) Circle I M) fun x ↦ -μ x)
    (hσ : σ.IsNondegenerate) {c : ℝ}
    (hfix : ∀ x, μ x circlePeriodOneGenerator = c → x ∉ MulAction.fixedPoints Circle M) :
    IsRegularValue I 𝓘(ℝ) (fun y ↦ μ y circlePeriodOneGenerator) c := by
  refine isRegularValue_iff.2 fun x hx ↦ ?_
  rw [isRegularPoint_iff_notMem_criticalPoints, mem_criticalPoints_iff_mfderiv_eq_zero]
  exact mfderiv_ne_zero_of_notMem_fixedPoints hμ (hσ.nondegenerate_bilinFormAt x) (hfix x hx)

end Regular

/-! ### The reduced forms of an equivariant map into a level -/

section Reduced

variable [FiniteDimensional ℝ E] [ContMDiffSMul (𝓡 1) I ∞ Circle M]
  {EB HB B : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  {IB : ModelWithCorners ℝ EB HB} [IB.Boundaryless] [TopologicalSpace B] [ChartedSpace HB B]
  [IsManifold IB ∞ B]
  {P : B → Type*} [TopologicalSpace (TotalSpace Circle P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle Circle P] [∀ b, MulAction Circleᵐᵒᵖ (P b)]
  [PrincipalBundle Circle P] [ContMDiffFiberBundle ∞ Circle P IB (𝓡 1)]

omit [T2Space M] in
/-- **The pull-back of a symplectic form to a level descends to the base.** Let a circle act
smoothly on a finite-dimensional manifold `M`, preserving the symplectic form `σ`, with moment
map `-μ`, and let `H = ⟨μ, circlePeriodOneGenerator⟩`. Let `P` be a smooth principal circle
bundle over a boundaryless base `B`, and `φ` a smooth map from its total space to `M` with
`φ (p • z) = z • φ p`, taking values in the level `H = t`, with injective differential whose
range is `ker dH`. Then there is a unique symplectic form `τ` on `B` whose pull-back along the
projection is `φ^* σ`. -/
theorem existsUnique_isSymplectic_mpullback_projContMDiffMap_eq {σ : SmoothTwoForm I M}
    (hσ : σ.IsSymplectic)
    (hσs : ∀ g : Circle, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := 𝓡 1) (I' := I) g) σ = σ)
    {μ : M → Module.Dual ℝ (GroupLieAlgebra (𝓡 1) Circle)}
    (hμ : σ.IsMomentMap (InfinitesimalAction.fundamental (𝓡 1) Circle I M) fun x ↦ -μ x)
    {φ : ManifoldTotalSpace Circle P → M} (hφ : ContMDiff (IB.prod (𝓡 1)) I ∞ φ)
    (hφs : ∀ (g : Circle) p, φ (op g • p) = g • φ p) {t : ℝ}
    (ht : ∀ p, μ (φ p) circlePeriodOneGenerator = t)
    (hinj : ∀ p, Injective (mfderiv (IB.prod (𝓡 1)) I φ p))
    (hrange : ∀ p, LinearMap.range (mfderiv (IB.prod (𝓡 1)) I φ p).toLinearMap =
      LinearMap.ker (mfderiv I 𝓘(ℝ) (fun x ↦ μ x circlePeriodOneGenerator) (φ p)).toLinearMap) :
    ∃! τ : SmoothTwoForm IB B, τ.IsSymplectic ∧
      SmoothForm.mpullback (ManifoldTotalSpace.projContMDiffMap ∞ Circle P IB (𝓡 1))
        (ManifoldTotalSpace.projContMDiffMap ∞ Circle P IB (𝓡 1)).contMDiff τ =
      SmoothForm.mpullback φ hφ σ := by
  -- `-μ` is constant on the image of `φ`, since the Lie algebra is spanned by
  -- `circlePeriodOneGenerator`.
  obtain ⟨c, hc⟩ : ∃ c, ∀ p, -μ (φ p) = c := by
    rcases isEmpty_or_nonempty (ManifoldTotalSpace Circle P) with hZ | ⟨⟨p₀⟩⟩
    · exact ⟨0, fun p ↦ isEmptyElim p⟩
    · exact ⟨-μ (φ p₀), fun p ↦ congrArg Neg.neg
        (linearMap_ext_of_ne_zero_circle circlePeriodOneGenerator_ne_zero
          ((ht p).trans (ht p₀).symm))⟩
  have hneg : (fun x ↦ (-μ x) circlePeriodOneGenerator) = -fun x ↦ μ x circlePeriodOneGenerator :=
    funext fun _ ↦ LinearMap.neg_apply _ _
  -- `dφ` sends the fundamental fields of the bundle to those of `M`.
  have hX (p : ManifoldTotalSpace Circle P) :
      (mfderiv (IB.prod (𝓡 1)) I φ p).toLinearMap ∘ₗ
          PrincipalBundle.rightFundamentalLinearMap IB (𝓡 1) p =
        (InfinitesimalAction.fundamental (𝓡 1) Circle I M).eval (φ p) :=
    LinearMap.ext fun ξ ↦ by
      rw [LinearMap.comp_apply, PrincipalBundle.rightFundamentalLinearMap_apply,
        ContinuousLinearMap.coe_coe, InfinitesimalAction.eval_apply,
        InfinitesimalAction.fundamental_apply]
      exact mfderiv_rightFundamentalVectorField_of_map_op_smul_eq_smul
        ((hφ p).mdifferentiableAt (by simp))
        (PrincipalBundle.mdifferentiableAt_orbit (n := ∞) (by simp) p 1) (hφs · p) ξ
  have hann : lieAnnihilator ℝ (GroupLieAlgebra (𝓡 1) Circle) c = ⊤ := by
    simp
  refine hμ.existsUnique_isSymplectic_mpullback_eq_mpullback (K := Circleᵐᵒᵖ) hσ hφ hc
    (fun _ ↦ SmoothTwoForm.momentCocycle_circle_eq_zero _ _ _ _) (fun p ↦ ?_)
    (ManifoldTotalSpace.isSubmersion_projContMDiffMap ∞ Circle P IB (𝓡 1))
    (ManifoldTotalSpace.surjective_projContMDiffMap ∞ Circle P IB (𝓡 1)) (fun p ↦ ?_)
    (fun k ↦ contMDiff_const_smul k) (fun k p ↦ ?_) (fun p p' hpp' ↦ ?_) fun k ↦ ?_
  · -- The level tangent space of `-μ` is `ker dH`.
    rw [hμ.ker_differential_circle, hrange, hneg, mfderiv_neg, ContinuousLinearMap.toLinearMap_neg]
    exact (LinearMap.ker_neg _).symm
  · -- The vertical vectors are the fundamental fields, which `dφ` sends to the orbit
    -- directions; `dφ` is injective.
    rw [hann, LieSubalgebra.top_toSubmodule, Submodule.map_top, ← hX, LinearMap.range_comp,
      Submodule.comap_map_eq_of_injective (hinj p),
      PrincipalBundle.range_rightFundamentalLinearMap_eq_ker_mfderiv_proj,
      ManifoldTotalSpace.coe_projContMDiffMap]
  · simp
  · obtain ⟨g, hg⟩ := PrincipalBundle.exists_op_smul_eq_of_proj_eq hpp'.symm
    exact ⟨op g, hg⟩
  · conv_rhs => rw [← hσs k.unop]
    exact SmoothForm.mpullback_mpullback_of_comp_eq _ hφ hφ _
      (funext fun p ↦ by simpa using hφs k.unop p) σ

end Reduced

/-! ### The band of a circle action -/

section RegularLevel

attribute [local instance] MulOpposite.chartedSpace

variable [FiniteDimensional ℝ E] [I.Boundaryless] [ContMDiffSMul (𝓡 1) I ∞ Circle M]
  {f : M → ℝ} {n : ℕ}

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

omit [Fact (a < b)] in
/-- **The slices of the band of a circle action have tangent images `ker df`.** In the setting of
`SymplecticGeometry.bandMap_orbitFiber`, for each `t ∈ [a, b]` the slice
`ψₜ = fun p ↦ bandMap v e a b (p, t)` from the total space of `P` to `M` has, at each point `p`,
injective differential, and the range of that differential is the kernel of `df` at `ψₜ p`. -/
theorem bandMap_orbitFiber_slice (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hreg : IsRegularValue I 𝓘(ℝ) f a)
    (hn : Module.finrank ℝ E - Module.finrank ℝ ℝ = n)
    (hinv : ∀ (g : Circle) (x : M), f (g • x) = f x)
    (hfree : ∀ x, f x = a → MulAction.stabilizer Circle x = ⊥)
    (hv : ContMDiff I I.tangent ∞ (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)))
    (hcomplete : IsCompleteVectorField v) {W : Set M}
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
    let IB := 𝓘(ℝ, ProperSMul.QuotientModelSpace (EuclideanSpace ℝ (Fin 1)) (Fin n → ℝ))
    let P := orbitFiber Circleᵐᵒᵖ {x : M // f x = a}
    let e : ManifoldTotalSpace Circle P → M := fun p ↦
      ((orbitFiber.atlas (𝓡 1) Circle 𝓘(ℝ, Fin n → ℝ) {x : M // f x = a}).totalSpaceDiffeomorph
        (orbitFiber.isContMDiff_atlas (𝓡 1) Circle 𝓘(ℝ, Fin n → ℝ) {x : M // f x = a}) p : M)
    ∀ (t : Icc a b) (p : ManifoldTotalSpace Circle P),
      LinearMap.ker (mfderiv (IB.prod (𝓡 1)) I (fun p ↦ bandMap v e a b (p, t)) p).toLinearMap =
          ⊥ ∧
        LinearMap.range
            (mfderiv (IB.prod (𝓡 1)) I (fun p ↦ bandMap v e a b (p, t)) p).toLinearMap =
          LinearMap.ker (mfderiv I 𝓘(ℝ) f (bandMap v e a b (p, t))).toLinearMap := by
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
  set D := (orbitFiber.atlas (𝓡 1) Circle 𝓘(ℝ, Fin n → ℝ) {x : M // f x = a})
    |>.totalSpaceDiffeomorph
    (orbitFiber.isContMDiff_atlas (𝓡 1) Circle 𝓘(ℝ, Fin n → ℝ) {x : M // f x = a})
  intro IB P e t p
  have hι := isSmoothEmbedding_coe_regularLevel (by simp) (fun x _ ↦ hf.contMDiffAt) hreg hn
  have hd : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have hιi := hι.isImmersion.mfderiv_injective hd (D p)
  -- The slice is that of the band map of the inclusion of the level, after `D`.
  have hslice : (fun p ↦ bandMap v e a b (p, t)) =
      (fun x : {x : M // f x = a} ↦ bandMap v Subtype.val a b (x, t)) ∘ D := by
    -- Both sides are `flowOf v (t - a) ∘ Subtype.val ∘ D`, with `e` unfolded.
    rw [bandMap_slice, bandMap_slice]
    rfl
  rw [hslice, LinearMap.ker_eq_bot]
  exact ⟨(D.mfderiv_comp_diffeomorph_injective_iff hd).mpr
      ((injective_mfderiv_bandMap_slice_iff (hv.of_le (by simp)) hcomplete t).mpr hιi),
    (D.range_mfderiv_comp_diffeomorph hd _ p).trans <|
      range_mfderiv_bandMap_slice (hv.of_le (by simp)) hcomplete hf.continuous hW hfv hband
        (fun x ↦ x.property) hιi (by simpa using hn.symm) t⟩

/-- **The slices of the band of a circle action descend to symplectic forms.** In the setting of
`SymplecticGeometry.bandMap_orbitFiber`, let the action preserve a symplectic form `σ`, with moment
map `-μ` such that `f = ⟨μ, circlePeriodOneGenerator⟩`. Then for each `t ∈ [a, b]` there is a
unique symplectic form `τ` on the base of `P` whose pull-back along the projection is the
pull-back of `σ` along the slice `ψₜ = fun p ↦ bandMap v e a b (p, t)`. The smoothness of the
band map, which `SymplecticGeometry.bandMap_orbitFiber` gives, is taken as an argument so that the
pull-back along `ψₜ` can be written. -/
theorem existsUnique_isSymplectic_mpullback_eq_mpullback_bandMap (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hreg : IsRegularValue I 𝓘(ℝ) f a)
    (hn : Module.finrank ℝ E - Module.finrank ℝ ℝ = n)
    (hinv : ∀ (g : Circle) (x : M), f (g • x) = f x)
    (hfree : ∀ x, f x = a → MulAction.stabilizer Circle x = ⊥)
    (hv : ContMDiff I I.tangent ∞ (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)))
    (hcomplete : IsCompleteVectorField v)
    (hvinv : ∀ (g : Circle) (x : M), mfderiv I I (g • ·) x (v x) = v (g • x)) {W : Set M}
    (hW : IsOpen W) (hfv : ∀ y ∈ W, mfderiv I 𝓘(ℝ) f y (v y) = 1)
    (hband : f ⁻¹' Icc a b ⊆ W) {σ : SmoothTwoForm I M} (hσ : σ.IsSymplectic)
    (hσs : ∀ g : Circle, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := 𝓡 1) (I' := I) g) σ = σ)
    {μ : M → Module.Dual ℝ (GroupLieAlgebra (𝓡 1) Circle)}
    (hμ : σ.IsMomentMap (InfinitesimalAction.fundamental (𝓡 1) Circle I M) fun x ↦ -μ x)
    (hμf : ∀ x, μ x circlePeriodOneGenerator = f x) :
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
    ∀ (hψ : ContMDiff ((IB.prod (𝓡 1)).prod (𝓡∂ 1)) I ∞ (bandMap v e a b)) (t : Icc a b),
      ∃! τ : SmoothTwoForm IB (MulAction.orbitRel.Quotient Circleᵐᵒᵖ {x : M // f x = a}),
        τ.IsSymplectic ∧
        SmoothForm.mpullback (ManifoldTotalSpace.projContMDiffMap ∞ Circle P IB (𝓡 1))
            (ManifoldTotalSpace.projContMDiffMap ∞ Circle P IB (𝓡 1)).contMDiff τ =
          SmoothForm.mpullback (fun p ↦ bandMap v e a b (p, t))
            (hψ.comp (contMDiff_id.prodMk contMDiff_const)) σ := by
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
  intro IB P e hψ t
  obtain ⟨-, hψs, hψf, -⟩ :=
    bandMap_orbitFiber hf hreg hn hinv hfree hv hcomplete hvinv hW hfv hband (b := b)
  have hs := bandMap_orbitFiber_slice hf hreg hn hinv hfree hv hcomplete hW hfv hband (b := b)
  refine existsUnique_isSymplectic_mpullback_projContMDiffMap_eq hσ hσs hμ _
    (fun g p ↦ hψs g (p, t)) (t := t) (fun p ↦ (hμf _).trans (hψf (p, t)))
    (fun p ↦ LinearMap.ker_eq_bot.mp (hs t p).1) fun p ↦ ?_
  rw [funext hμf]
  exact (hs t p).2

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

/-! ### The converse of minimal coupling -/

section Converse

attribute [local instance] MulOpposite.chartedSpace

variable [FiniteDimensional ℝ E] [I.Boundaryless] [ContMDiffSMul (𝓡 1) I ∞ Circle M]
  [SigmaCompactSpace M] {σ : SmoothTwoForm I M}
  {μ : M → Module.Dual ℝ (GroupLieAlgebra (𝓡 1) Circle)}

/-- **The converse of minimal coupling.** Let a circle act smoothly on a Hausdorff, σ-compact,
boundaryless finite-dimensional manifold `M`, preserving a symplectic form `σ`, with moment map
`-μ`, and let `H = ⟨μ, circlePeriodOneGenerator⟩`, so that `ι_{X_M} σ = -dH`. Let `a < b`, let
the band `K = H⁻¹([a, b])` be compact, and let the action be free on `K`. Let `P` be the circle
bundle `orbitFiber` of the level `H⁻¹(a)`, a regular level, over the orbit space `B`, built with
the local instances of `GroupAction/RegularLevel.lean`. Then there are a map
`ψ : P × [a, b] → M` and a family `τ` of two-forms on `B` such that

* `ψ` is smooth and equivariant, `ψ (p • z, t) = z • ψ (p, t)`;
* `ψ` is injective, with range `K`, and `H (ψ (p, t)) = t`;
* `τ` is a smooth family of symplectic forms;
* `ψ^* σ` is a coupling form for `τ`;
* the de Rham classes of the forms `τ t` move linearly in `t`, with slope minus the real first
  Chern class of `P`: `[τ t] - [τ s] = -(t - s) c₁(P)`.

The base `B` is compact, since the level `H⁻¹(a)` is closed in the compact band. The action is
not assumed to be free off `K`, and `H(K) = [a, b]` is not assumed.

Milestone: *Minimal coupling*. -/
theorem exists_isCouplingForm_comp_eq (hσ : σ.IsSymplectic)
    (hσs : ∀ g : Circle, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := 𝓡 1) (I' := I) g) σ = σ)
    (hμ : σ.IsMomentMap (InfinitesimalAction.fundamental (𝓡 1) Circle I M) fun x ↦ -μ x)
    (hK : IsCompact ((fun x ↦ μ x circlePeriodOneGenerator) ⁻¹' Icc a b))
    (hfree : ∀ x, μ x circlePeriodOneGenerator ∈ Icc a b → MulAction.stabilizer Circle x = ⊥) :
    let H : M → ℝ := fun x ↦ μ x circlePeriodOneGenerator
    haveI hf : ContMDiff I 𝓘(ℝ) ∞ H := hμ.contMDiff_of_neg circlePeriodOneGenerator
    haveI hlevel : ∀ x, H x = a → H x ∈ Icc a b := fun x hx ↦ by
      rw [hx]; exact left_mem_Icc.2 (Fact.out : a < b).le
    haveI hfreea : ∀ x, H x = a → MulAction.stabilizer Circle x = ⊥ := fun x hx ↦
      hfree x (hlevel x hx)
    haveI hreg : IsRegularValue I 𝓘(ℝ) H a :=
      isRegularValue_of_notMem_fixedPoints hμ hσ.isNondegenerate fun x hx ↦
        MulAction.notMem_fixedPoints_of_stabilizer_eq_bot (hfreea x hx)
    haveI hn : Module.finrank ℝ E - Module.finrank ℝ ℝ = Module.finrank ℝ E - 1 := by
      rw [Module.finrank_self]
    haveI hinv : ∀ (g : Circle) (x : M), H (g • x) = H x := fun g x ↦
      congrArg (· circlePeriodOneGenerator) (neg_injective (hμ.apply_smul_circle g x))
    letI := regularLevelChartedSpace (fun x _ ↦ hf.contMDiffAt.of_le (by simp)) hreg hn
    letI := levelOpMulAction a hinv
    haveI := isManifold_regularLevel (by simp) (fun x _ ↦ hf.contMDiffAt) hreg hn
    haveI := contMDiffSMul_levelOpMulAction (by simp) (fun x _ ↦ hf.contMDiffAt) hreg hn hinv
      (IG := 𝓡 1)
    haveI := ContMDiffSMul.continuousSMul (I := 𝓡 1) (I' := I) (G := Circle) (M := M) ∞
    haveI := properSMul_levelOpMulAction (c := a) hinv
    haveI := isCancelSMul_levelOpMulAction hinv hfreea
    letI := ProperSMul.orbitRelQuotientChartedSpace (𝓡 1) Circleᵐᵒᵖ
      𝓘(ℝ, Fin (Module.finrank ℝ E - 1) → ℝ) {x : M // H x = a}
    letI := (orbitFiber.atlas (𝓡 1) Circle 𝓘(ℝ, Fin (Module.finrank ℝ E - 1) → ℝ)
      {x : M // H x = a}).fiberBundle
    haveI := orbitFiber.principalBundle (𝓡 1) Circle 𝓘(ℝ, Fin (Module.finrank ℝ E - 1) → ℝ)
      {x : M // H x = a}
    haveI := (orbitFiber.atlas (𝓡 1) Circle 𝓘(ℝ, Fin (Module.finrank ℝ E - 1) → ℝ)
      {x : M // H x = a}).contMDiffFiberBundle
      (orbitFiber.isContMDiff_atlas (𝓡 1) Circle 𝓘(ℝ, Fin (Module.finrank ℝ E - 1) → ℝ)
        {x : M // H x = a})
    haveI : CompactSpace {x : M // H x = a} := isCompact_iff_compactSpace.1 <|
      hK.of_isClosed_subset (isClosed_eq hf.continuous continuous_const) hlevel
    let IB := 𝓘(ℝ, ProperSMul.QuotientModelSpace (EuclideanSpace ℝ (Fin 1))
      (Fin (Module.finrank ℝ E - 1) → ℝ))
    let B := MulAction.orbitRel.Quotient Circleᵐᵒᵖ {x : M // H x = a}
    let P := orbitFiber Circleᵐᵒᵖ {x : M // H x = a}
    ∃ (ψ : ManifoldTotalSpace Circle P × Icc a b → M)
      (hψ : ContMDiff ((IB.prod (𝓡 1)).prod (𝓡∂ 1)) I ∞ ψ) (τ : Icc a b → SmoothTwoForm IB B)
      (hτ : ∀ t, (τ t).IsSymplectic),
      (∀ (g : Circle) (x : ManifoldTotalSpace Circle P × Icc a b), ψ (op g • x.1, x.2) = g • ψ x) ∧
      Injective ψ ∧ range ψ = H ⁻¹' Icc a b ∧ (∀ x, H (ψ x) = x.2) ∧
      IsSmoothFamily (𝓡∂ 1) τ ∧ IsCouplingForm (SmoothForm.mpullback ψ hψ σ) τ ∧
      ∀ t s : Icc a b,
        deRhamCohomology.mk IB 2 ⟨τ t, (hτ t).isClosed.mem_closedForms⟩ -
            deRhamCohomology.mk IB 2 ⟨τ s, (hτ s).isClosed.mem_closedForms⟩ =
          -((t : ℝ) - s) • realFirstChernClass IB P := by
  intro H
  have hf : ContMDiff I 𝓘(ℝ) ∞ H := hμ.contMDiff_of_neg circlePeriodOneGenerator
  have hlevel : ∀ x, H x = a → H x ∈ Icc a b := fun x hx ↦ by
    rw [hx]; exact left_mem_Icc.2 (Fact.out : a < b).le
  have hfreea : ∀ x, H x = a → MulAction.stabilizer Circle x = ⊥ := fun x hx ↦
    hfree x (hlevel x hx)
  have hreg : IsRegularValue I 𝓘(ℝ) H a :=
    isRegularValue_of_notMem_fixedPoints hμ hσ.isNondegenerate fun x hx ↦
      MulAction.notMem_fixedPoints_of_stabilizer_eq_bot (hfreea x hx)
  have hn : Module.finrank ℝ E - Module.finrank ℝ ℝ = Module.finrank ℝ E - 1 := by
    rw [Module.finrank_self]
  have hinv : ∀ (g : Circle) (x : M), H (g • x) = H x := fun g x ↦
    congrArg (· circlePeriodOneGenerator) (neg_injective (hμ.apply_smul_circle g x))
  let := regularLevelChartedSpace (fun x _ ↦ hf.contMDiffAt.of_le (by simp)) hreg hn
  let := levelOpMulAction a hinv
  have := isManifold_regularLevel (by simp) (fun x _ ↦ hf.contMDiffAt) hreg hn
  have := contMDiffSMul_levelOpMulAction (by simp) (fun x _ ↦ hf.contMDiffAt) hreg hn hinv
    (IG := 𝓡 1)
  have := ContMDiffSMul.continuousSMul (I := 𝓡 1) (I' := I) (G := Circle) (M := M) ∞
  have := properSMul_levelOpMulAction (c := a) hinv
  have := isCancelSMul_levelOpMulAction hinv hfreea
  let := ProperSMul.orbitRelQuotientChartedSpace (𝓡 1) Circleᵐᵒᵖ
    𝓘(ℝ, Fin (Module.finrank ℝ E - 1) → ℝ) {x : M // H x = a}
  let := (orbitFiber.atlas (𝓡 1) Circle 𝓘(ℝ, Fin (Module.finrank ℝ E - 1) → ℝ)
    {x : M // H x = a}).fiberBundle
  have := orbitFiber.principalBundle (𝓡 1) Circle 𝓘(ℝ, Fin (Module.finrank ℝ E - 1) → ℝ)
    {x : M // H x = a}
  have := (orbitFiber.atlas (𝓡 1) Circle 𝓘(ℝ, Fin (Module.finrank ℝ E - 1) → ℝ)
    {x : M // H x = a}).contMDiffFiberBundle
    (orbitFiber.isContMDiff_atlas (𝓡 1) Circle 𝓘(ℝ, Fin (Module.finrank ℝ E - 1) → ℝ)
      {x : M // H x = a})
  have : CompactSpace {x : M // H x = a} := isCompact_iff_compactSpace.1 <|
    hK.of_isClosed_subset (isClosed_eq hf.continuous continuous_const) hlevel
  intro IB B P
  -- An invariant complete field `v` with `dH(v) = 1` near the band, where `dH ≠ 0`.
  obtain ⟨v, W, hv, -, hvc, hvinv, hW, hKW, -, hvf⟩ :=
    exists_invariant_vectorField_mfderiv_eq_one (𝓡 1) (G := Circle) hf hinv hK fun x hx ↦
      mfderiv_ne_zero_of_notMem_fixedPoints hμ (hσ.isNondegenerate.nondegenerate_bilinFormAt x)
        (MulAction.notMem_fixedPoints_of_stabilizer_eq_bot (hfree x hx))
  obtain ⟨hψ, hψs, hψf, hinj, hrange, hX⟩ :=
    bandMap_orbitFiber hf hreg hn hinv hfreea hv hvc hvinv hW hvf hKW (b := b)
  have hτ := existsUnique_isSymplectic_mpullback_eq_mpullback_bandMap hf hreg hn hinv hfreea hv
    hvc hvinv hW hvf hKW hσ hσs hμ (fun _ ↦ rfl) hψ
  choose τ hτs hτ using fun t ↦ (hτ t).exists
  have hc := isCouplingForm_mpullback hψ hσ.isClosed hσs hμ hψs hψf hX fun t ↦ (hτ t).symm
  exact ⟨_, hψ, τ, hτs, hψs, hinj, hrange, hψf, hc.isSmoothFamily, hc,
    hc.mk_sub_mk_eq_neg_smul_realFirstChernClass⟩

end Converse

end SymplecticGeometry

end
