/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Complex.Integrable
public import SymplecticGeometry.Geometry.Manifold.GroupAction.OrbitTube
public import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.KempfNess.Basic
import SymplecticGeometry.Geometry.Manifold.GroupAction.EquivariantAverage
import TauCeti.Geometry.Lie.Subgroup.Embedded
import TauCeti.Geometry.Manifold.GroupAction.TangentRepresentation
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import SymplecticGeometry.Geometry.Symplectic.Manifold.AlmostComplex.Chart
import TauCeti.RepresentationTheory.Compact.Haar
import TauCeti.RepresentationTheory.Continuous.Average
import TauCeti.Topology.Algebra.ConstMulAction

/-!
# Equivariant holomorphic charts at points with compact stabilizer

Let a Lie group `G` act smoothly on a manifold `M` with an integrable almost complex structure
`J` that every `g • ·` preserves, and let the stabilizer `H` of `x : M` be compact. This file
proves that there is a linearizing chart `e` at `x` (`SymplecticGeometry.LinearizingChart`: a
chart sending `x` to `0` with derivative the identity there, in which each `h ∈ H` acts by its
differential `dh_x`) in which `J` is constant, equal to `J x`
(`SymplecticGeometry.exists_equivariant_holomorphic_chart`).

In a linearizing chart the fundamental vector field of an element `ξ` of the isotropy algebra
`𝔥` of `x` is `X_ξ (e.symm v) = d(e.symm)_v (A_ξ v)`, where `A_ξ` is the linearized isotropy
action (`TauCeti.isotropyLinearization`); this is
`SymplecticGeometry.LinearizingChart.fundamentalVectorField_symm`, in
`SymplecticGeometry.Geometry.Manifold.GroupAction.OrbitTube`. For a complexified action of
a complexification `Gc` of `G`, `X_{iη} = J X_η`, and `J` is `J x` in the chart, so the
fundamental vector field of `C.lieMap ξ + C.cplx (C.lieMap η)` at `e.symm v` is
`d(e.symm)_v (A_ξ v) + d(e.symm)_v (J x (A_η v))`
(`SymplecticGeometry.fundamentalVectorField_chart_symm`), as in the proof of Theorem 12.5 of
[GeorgoulasRobbinSalamon2021].

The proof averages a chart in which `J` is constant over `H`. Integrability gives a chart `ψ`
with `ψ x = 0`, derivative the identity at `x` and `dψ ∘ J = J x ∘ dψ` on its source
(`TauCeti.SmoothAlmostComplexStructure.IsIntegrable.exists_partialDiffeomorph_mfderiv_apply_eq`).
With `H` the compact Lie group of the closed-subgroup theorem and `σ h = dh_x` its tangent
representation, the average `A y = ∫ h, σ h (ψ (h⁻¹ • y)) dh` against normalized Haar measure is
smooth and `H`-equivariant, has derivative the identity at `x`, and its derivative at `y` is the
integral of `σ h ∘ dψ_{h⁻¹ • y} ∘ d(h⁻¹ • ·)_y`
(`ContMDiffOn.hasMFDerivAt_integral_apply_inv_smul`). Each of these three maps intertwines the
values of `J`: the first because `J` is invariant and `x` is fixed, the second by the choice of
`ψ`, the third because `J` is invariant, at every point `y` and not only at `x`. So `dA_y`
intertwines `J y` with `J x` (`ContMDiffOn.mfderiv_integral_apply_inv_smul_apply_eq`). The
inverse function theorem makes `A` a chart, which is then restricted to an `H`-invariant domain.

The construction of the chart follows the proof of Tau Ceti's
`TauCeti.exists_equivariant_contMDiff_chart_of_compactSpace`, applied, as in Tau Ceti's
`TauCeti.exists_equivariant_contMDiff_chart_of_isCompact_stabilizer`, to the stabilizer with
its closed-subgroup Lie group structure; here the averaged map is the chart `ψ` instead of a
chart of the atlas, and the derivative of the average is computed at every point of the domain.

## Main results

* `SymplecticGeometry.exists_equivariant_holomorphic_chart`: at a point with compact stabilizer,
  an invariant integrable almost complex structure is constant in some linearizing chart.
* `SymplecticGeometry.fundamentalVectorField_chart_symm`: in a linearizing chart in which `J` is
  constant, the fundamental vector field of `C.lieMap ξ + C.cplx (C.lieMap η)`, for `ξ, η` in the
  isotropy algebra, is `v ↦ A_ξ v + J x (A_η v)`.
* `ContMDiffOn.mfderiv_integral_apply_inv_smul_apply_eq`: the equivariant average of a map whose
  derivatives carry an almost complex structure `J` to a fixed linear map `J₀`, commuting with
  the representation, has the same property at each point where the action preserves `J`.

## References

* [V. Georgoulas, J. W. Robbin and D. A. Salamon, *The moment-weight inequality and the
  Hilbert–Mumford criterion*][GeorgoulasRobbinSalamon2021], arXiv v2, proof of Theorem 12.5.
* S. Bochner, *Compact groups of differentiable transformations*, Ann. of Math. (2) 46 (1945),
  372–381.
-/

public section

noncomputable section

open Set Filter Function Manifold MulAction MeasureTheory TauCeti
open scoped Topology Manifold ContDiff

namespace SymplecticGeometry

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M]

section Average

variable [I'.Boundaryless] {EK : Type*} [NormedAddCommGroup EK] [NormedSpace ℝ EK]
  {HK : Type*} [TopologicalSpace HK] {IK : ModelWithCorners ℝ EK HK} [IK.Boundaryless]
  {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
  [ChartedSpace HK K] [MeasurableSpace K] [BorelSpace K] [MulAction K M] {n : ℕ∞}
  [IsManifold I' n M] [IsManifold IK n K] [ContMDiffSMul IK I' n K M]
  {μ : Measure K} [IsFiniteMeasure μ] {σ : ContRepresentation ℝ K E'} {φ : M → E'} {U : Set M}

include IK in
/-- **Averages of holomorphic maps.** Let a compact Lie group `K` act smoothly on a manifold `M`
without boundary with an almost complex structure `J`, let `σ` be a continuous representation
of `K` on `E'` commuting with a linear map `J₀`, let `μ` be a finite measure on `K`, and let
`φ : M → E'` be `C^n`, `1 ≤ n`, on an open set `U`, with `dφ_z ∘ J z = J₀ ∘ dφ_z` for `z ∈ U`.
Let `y` be a point whose orbit lies in `U`, such that `d(k • ·)_y ∘ J y = J (k • y) ∘ d(k • ·)_y`
for every `k`. Then the equivariant average `A y = ∫ k, σ k (φ (k⁻¹ • y)) ∂μ` satisfies
`dA_y ∘ J y = J₀ ∘ dA_y`. -/
theorem _root_.ContMDiffOn.mfderiv_integral_apply_inv_smul_apply_eq
    {J : SmoothAlmostComplexStructure I' M}
    {J₀ : E' →L[ℝ] E'} (hσ : Continuous σ) (hU : IsOpen U) (hφ : ContMDiffOn I' 𝓘(ℝ, E') n φ U)
    (hn : 1 ≤ n)
    (hφJ : ∀ y ∈ U, ∀ v : TangentSpace I' y,
      mfderiv I' 𝓘(ℝ, E') φ y (J y v) = J₀ (mfderiv I' 𝓘(ℝ, E') φ y v))
    (hσJ : ∀ (k : K) (w : E'), σ k (J₀ w) = J₀ (σ k w)) {y : M}
    (hJK : ∀ (k : K) (v : TangentSpace I' y),
      mfderiv I' I' (fun z : M ↦ k • z) y (J y v) =
        J (k • y) (mfderiv I' I' (fun z : M ↦ k • z) y v))
    (hy : ∀ k : K, k • y ∈ U) (v : TangentSpace I' y) :
    mfderiv I' 𝓘(ℝ, E') (fun y ↦ ∫ k, σ k (φ (k⁻¹ • y)) ∂μ) y (J y v) =
      J₀ (mfderiv I' 𝓘(ℝ, E') (fun y ↦ ∫ k, σ k (φ (k⁻¹ • y)) ∂μ) y v) := by
  rw [(hφ.hasMFDerivAt_integral_apply_inv_smul (IG := IK) (μ := μ) hσ hU hn hy).mfderiv]
  set L : K → E' →L[ℝ] E' := fun k ↦ (σ k).comp ((mfderiv I' 𝓘(ℝ, E') φ (k⁻¹ • y)).comp
    (mfderiv I' I' (fun z : M ↦ k⁻¹ • z) y))
  -- `J y` as an endomorphism of the model space `E'`, where the integral lives.
  let Jy : E' →L[ℝ] E' := J.toEndomorphism y
  -- Each of the three factors of `L k` intertwines the values of `J`.
  have hL (k : K) (w : E') : L k (Jy w) = J₀ (L k w) := by
    have h₁ : mfderiv I' I' (fun z : M ↦ k⁻¹ • z) y (J y w) =
        J (k⁻¹ • y) (mfderiv I' I' (fun z : M ↦ k⁻¹ • z) y w) := hJK k⁻¹ w
    -- `L k` composes maps between tangent spaces, which `ContinuousLinearMap.comp_apply`
    -- does not rewrite once they are read on `E'`; unfold the composition by hand.
    change σ k (mfderiv I' 𝓘(ℝ, E') φ (k⁻¹ • y) (mfderiv I' I' (fun z : M ↦ k⁻¹ • z) y
        (J y w))) =
      J₀ (σ k (mfderiv I' 𝓘(ℝ, E') φ (k⁻¹ • y) (mfderiv I' I' (fun z : M ↦ k⁻¹ • z) y w)))
    rw [h₁, hφJ _ (hy k⁻¹)]
    exact hσJ k _
  suffices key : (∫ k, L k ∂μ) (Jy v) = J₀ ((∫ k, L k ∂μ) v) from key
  by_cases hint : Integrable L μ
  · calc (∫ k, L k ∂μ) (Jy v) = ∫ k, L k (Jy v) ∂μ := ContinuousLinearMap.integral_apply hint _
      _ = ∫ k, J₀ (L k v) ∂μ := integral_congr_ae (.of_forall fun k ↦ hL k v)
      _ = J₀ (∫ k, L k v ∂μ) := J₀.integral_comp_comm (hint.apply_continuousLinearMap v)
      _ = J₀ ((∫ k, L k ∂μ) v) := congrArg J₀ (ContinuousLinearMap.integral_apply hint v).symm
  · rw [integral_undef hint]
    exact (map_zero J₀).symm

end Average

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  [I'.Boundaryless] [MulAction G M] [ContMDiffSMul I I' ∞ G M]

variable (I) in
include I in
/-- **Equivariant holomorphic charts.** Let a finite-dimensional Lie group `G` act smoothly on a
manifold `M` without boundary, modelled on a complete space, and let `J` be an integrable almost
complex structure on `M` preserved by every `g • ·`. If the stabilizer of `x` is compact, there
is a linearizing chart `e` at `x`, in which every element `h` of the stabilizer acts by `dh_x`,
such that `J` is constant in `e`, equal to `J x`: `de_z ∘ J z = J x ∘ de_z` at every point `z` of
the source of `e`. -/
theorem exists_equivariant_holomorphic_chart {J : SmoothAlmostComplexStructure I' M}
    (hJi : J.IsIntegrable)
    (hJG : ∀ (g : G) (y : M) (v : TangentSpace I' y),
      mfderiv I' I' (fun z : M ↦ g • z) y (J y v) =
        J (g • y) (mfderiv I' I' (fun z : M ↦ g • z) y v))
    {x : M} (hx : IsCompact (stabilizer G x : Set G)) :
    ∃ e : LinearizingChart G I' x, ∀ z ∈ e.chart.source, ∀ v : TangentSpace I' z,
      mfderiv I' 𝓘(ℝ, E') e.chart z (J z v) = J x (mfderiv I' 𝓘(ℝ, E') e.chart z v) := by
  have : T2Space G := ModelWithCorners.t2Space_of_lieGroup (I := I) ∞
  have : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  -- The stabilizer `K` is a compact Lie group, with the structure of the closed-subgroup theorem.
  let K := stabilizer G x
  let d := Lie.EmbeddedLieSubgroupData.ofIsClosed (I := I) hx.isClosed
  let _ := d.chartedSpace
  have := d.lieGroup
  have : CompactSpace K := isCompact_iff_compactSpace.mp hx
  let IK := 𝓘(ℝ, (Lie.lieSubalgebraOfSubgroup (I := I) (stabilizer G x)).toSubmodule)
  have : ContMDiffSMul IK I' ∞ K M := d.contMDiffSMul
  have : ContinuousSMul K M := ContMDiffSMul.continuousSMul (I := IK) (I' := I') ∞
  borelize ↥(stabilizer G x)
  let μ : Measure K := haarProb K
  have hfix (k : K) : k • x = x := k.property
  -- The tangent representation `σ k = dk_x` of `K`, which commutes with `J x`, by the
  -- invariance of `J` at the fixed point `x`.
  have hd : ∀ g ∈ stabilizer G x, MDifferentiableAt I' I' (fun y : M ↦ g • y) x :=
    fun g _ ↦ ((ContMDiffSMul.contMDiff_const_smul (I := I) (n := ∞) g) x).mdifferentiableAt
      (by simp)
  let σ : ContRepresentation ℝ K E' := tangentRepresentation hd
  have hσk (k : K) : σ k = mfderiv I' I' (fun y : M ↦ (k : G) • y) x :=
    tangentRepresentation_apply hd k
  have hσ : Continuous σ := by
    have h1 : (1 : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
    have : IsManifold I 1 G := .of_le (n := ∞) h1
    have : ContMDiffSMul I I' 1 G M := .of_le (m := ∞) h1
    exact continuous_tangentRepresentation I hd
  let Jx : E' →L[ℝ] E' := J.toEndomorphism x
  have hσJ (k : K) (w : E') : σ k (Jx w) = Jx (σ k w) := by
    have h := hJG k x w
    rw [show (k : G) • x = x from k.property] at h
    rw [hσk k]
    exact h
  -- The chart `ψ` in which `J` is constant, equal to `J x`, and its average `A`.
  obtain ⟨ψ, hxψ, hψx, hψd, hψJ⟩ := hJi.exists_partialDiffeomorph_mfderiv_apply_eq x
  let A : M → E' := fun y ↦ ∫ k, σ k (ψ (k⁻¹ • y)) ∂μ
  let S : Set M := {y | ∀ k : K, k • y ∈ ψ.source}
  have hS : IsOpen S := isOpen_setOf_forall_smul_mem ψ.open_source
  have hxS : x ∈ S := fun k ↦ by rw [hfix k]; exact hxψ
  have hψs : ContMDiffOn I' 𝓘(ℝ, E') (⊤ : ℕ∞) ψ ψ.source := ψ.contMDiffOn
  have hAx : HasMFDerivAt I' 𝓘(ℝ, E') A x (ContinuousLinearMap.id ℝ E') :=
    hψs.hasMFDerivAt_integral_apply_inv_smul_of_smul_eq (IG := IK) (μ := μ) hσ ψ.open_source
      le_top hfix hxψ (fun k ↦ (hσk k).symm) hψd.mfderiv
  -- The inverse function theorem makes `A` a chart `e₀` near `x`.
  have hA : ContMDiffOn I' 𝓘(ℝ, E') ∞ A S :=
    hψs.integral_apply_inv_smul (IG := IK) (μ := μ) hσ ψ.open_source
  obtain ⟨Φ, hxe₀, he₀S, hAΦ⟩ := (isLocalDiffeomorphAt_of_mfderiv_eq hA hS hxS
    BoundarylessManifold.isInteriorPoint (by exact_mod_cast le_top)
    (e := ContinuousLinearEquiv.refl ℝ E') hAx.mfderiv.symm).exists_partialDiffeomorph_eqOn hS hxS
  let e₀ := Φ.toOpenPartialHomeomorph
  have he₀ : EqOn e₀ A e₀.source := fun y hy ↦ (hAΦ hy).symm
  have he₀smooth : ContMDiffOn I' 𝓘(ℝ, E') ∞ e₀ e₀.source := Φ.contMDiffOn
  have he₀symm : ContMDiffOn 𝓘(ℝ, E') I' ∞ e₀.symm e₀.target := Φ.symm.contMDiffOn
  -- Restrict `e₀` to the largest `K`-invariant open subset of its source.
  let S' : Set M := {y | ∀ k : K, k • y ∈ e₀.source}
  have hS' : IsOpen S' := isOpen_setOf_forall_smul_mem e₀.open_source
  let e := e₀.restrOpen S' hS'
  have hee₀ : ⇑e = e₀ := e₀.coe_restrOpen hS'
  have hS'source {y : M} (hy : y ∈ S') : y ∈ e₀.source := by simpa using hy 1
  have hesource {y : M} : y ∈ e.source ↔ y ∈ S' := by
    simp only [e, OpenPartialHomeomorph.restrOpen_source, mem_inter_iff]
    exact ⟨And.right, fun h ↦ ⟨hS'source h, h⟩⟩
  have hetarget : e.target ⊆ e₀.target := by
    simp only [e, OpenPartialHomeomorph.restrOpen_toPartialEquiv, PartialEquiv.restr_target]
    exact inter_subset_left
  have hxS' : x ∈ S' := fun k ↦ by rw [hfix k]; exact hxe₀
  have hS'smul {g : G} (hg : g ∈ stabilizer G x) {z : M} (hz : z ∈ S') : g • z ∈ S' := by
    intro k
    have h := hz (k * ⟨g, hg⟩)
    rw [mul_smul] at h
    exact h
  -- Near each point of its source, `e` is the average `A`.
  have heA {y : M} (hy : y ∈ e.source) : e =ᶠ[𝓝 y] A := by
    filter_upwards [e.open_source.mem_nhds hy] with z hz
    rw [hee₀, he₀ (hS'source (hesource.1 hz))]
  refine ⟨⟨e, hesource.2 hxS', ?_, ?_, ?_, ?_, fun g hg z hz ↦ ?_, fun g hg z hz ↦ ?_⟩,
    fun z hz v ↦ ?_⟩
  · rw [hee₀, he₀ (hS'source hxS')]
    simp [A, hfix, hψx]
  · rw [hee₀]
    exact he₀smooth.mono fun y hy ↦ hS'source (hesource.1 hy)
  · rw [e₀.coe_restrOpen_symm hS']
    exact he₀symm.mono hetarget
  · exact hAx.congr_of_eventuallyEq (heA (hesource.2 hxS'))
  · exact hesource.2 (hS'smul hg (hesource.1 hz))
  · have hz' := hesource.1 hz
    rw [hee₀, he₀ (hS'source (hS'smul hg hz')), he₀ (hS'source hz'), ← hσk ⟨g, hg⟩]
    exact σ.integral_apply_inv_smul_smul μ ψ ⟨g, hg⟩ z
  · -- The derivative of `A` intertwines `J z` with `J x`, as each term of its integral does.
    rw [(heA hz).mfderiv_eq]
    exact hψs.mfderiv_integral_apply_inv_smul_apply_eq (IK := IK) hσ ψ.open_source le_top hψJ
      hσJ (fun k v ↦ hJG k z v) (he₀S (hS'source (hesource.1 hz))) v

/-! ### Fundamental vector fields in the chart -/

section FundamentalVectorField

variable {EC : Type*} [NormedAddCommGroup EC] [NormedSpace ℝ EC] [CompleteSpace EC]
  {HC : Type*} [TopologicalSpace HC] {IC : ModelWithCorners ℝ EC HC}
  {Gc : Type*} [TopologicalSpace Gc] [ChartedSpace HC Gc] [Group Gc] [LieGroup IC ∞ Gc]
  [T2Space Gc] [MulAction Gc M] [ContMDiffSMul IC I' ∞ Gc M] [T2Space M]

/-- **Fundamental vector fields in a holomorphic linearizing chart.** Let the action of the
complexification `Gc` on `M` be a complexified action of that of `G` for `C` and `J`, and let `e`
be a linearizing chart at `x` for the action of `G` in which `J` is constant, equal to `J x` (as
given by `SymplecticGeometry.exists_equivariant_holomorphic_chart`). For `ξ, η` in the isotropy
algebra of `x`, `Z = C.lieMap ξ + C.cplx (C.lieMap η)` and `v` in the target of `e`, the
fundamental vector field of `Z` at `e.symm v` is the image under the differential of `e.symm` at
`v` of `A_ξ v`, plus that of `J x (A_η v)`, where `A` is the linearized isotropy action
(`TauCeti.isotropyLinearization`). -/
theorem fundamentalVectorField_chart_symm {C : LieComplexification I G IC Gc}
    {J : SmoothAlmostComplexStructure I' M} (hC : IsComplexifiedAction C J) {x : M}
    (e : LinearizingChart G I' x)
    (hJ : ∀ z ∈ e.chart.source, ∀ v : TangentSpace I' z,
      mfderiv I' 𝓘(ℝ, E') e.chart z (J z v) = J x (mfderiv I' 𝓘(ℝ, E') e.chart z v))
    (ξ η : (InfinitesimalAction.fundamental I G I' M).isotropy x) {v : E'}
    (hv : v ∈ e.chart.target) :
    fundamentalVectorField I' (C.lieMap ξ + C.cplx (C.lieMap η)) (e.chart.symm v) =
      mfderiv 𝓘(ℝ, E') I' e.chart.symm v (isotropyLinearization I' x ξ v) +
        mfderiv 𝓘(ℝ, E') I' e.chart.symm v (J x (isotropyLinearization I' x η v)) := by
  have hz : e.chart.symm v ∈ e.chart.source := e.chart.map_target hv
  have hv' : v ∈ e.toPartialDiffeomorph.target := by
    rwa [LinearizingChart.toPartialDiffeomorph_target]
  -- `J` at `e.symm v` corresponds to `J x` under the differential of `e.symm`.
  have hJs (w : E') : J (e.chart.symm v) (mfderiv 𝓘(ℝ, E') I' e.chart.symm v w) =
      mfderiv 𝓘(ℝ, E') I' e.chart.symm v (J x w) := by
    have h := J.mfderiv_symm_apply_chartPushforward_apply e.toPartialDiffeomorph hv' w
    have hinv := e.toPartialDiffeomorph.mfderiv_apply_mfderiv_symm_apply (by simp) hv' w
    rw [LinearizingChart.toOpenPartialHomeomorph_toPartialDiffeomorph,
      LinearizingChart.coe_toPartialDiffeomorph_symm] at h
    rw [LinearizingChart.coe_toPartialDiffeomorph,
      LinearizingChart.coe_toPartialDiffeomorph_symm] at hinv
    rw [J.chartPushforward_apply, hJ _ hz, hinv] at h
    exact h.symm
  rw [fundamentalVectorField_add, Pi.add_apply, hC.fundamentalVectorField_cplx_lieMap,
    congrFun (hC.fundamentalVectorField_lieMap _) _, e.fundamentalVectorField_symm ξ hv,
    e.fundamentalVectorField_symm η hv, hJs]

end FundamentalVectorField

end SymplecticGeometry

end
