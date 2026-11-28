/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Lie.GroupLieAlgebra.Normed
public import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.WeightModel.Basic
public import TauCeti.Analysis.Convex.LocalToGlobal
public import TauCeti.Geometry.Symplectic.Hamiltonian.WeightModel.NormalForm
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import SymplecticGeometry.Analysis.Calculus.Implicit
import SymplecticGeometry.Geometry.Lie.Exponential.CommutativeGroup.Character
import SymplecticGeometry.Geometry.Lie.FundamentalVectorField
import SymplecticGeometry.Geometry.Lie.Subgroup.IdentityComponent
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.Basic
import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.Chart
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import TauCeti.Geometry.Symplectic.Hamiltonian.EquivariantMomentMap.Restrict
import TauCeti.Geometry.Symplectic.Hamiltonian.WeightModel.Slice
import TauCeti.Topology.Algebra.ConstMulAction

/-!
# Local convexity of a torus moment map

Let a compact commutative Lie group `G` act smoothly on a symplectic manifold `(M, σ)` without
boundary, preserving `σ`, with moment map `μ`, and let `x : M`. The point `x` need not be fixed by
`G`, but it is fixed by the identity component `K` of its stabilizer `G_x`, a torus whose Lie
algebra is the isotropy algebra `𝔤_x = {ξ | ξ_M(x) = 0}`.

## Main results

* `TauCeti.SmoothTwoForm.IsMomentMap.exists_weightModelChart_isotropy`: the weight chart of `K`
  at `x`, with its weights read on the isotropy algebra `𝔤_x ⊆ 𝔤`. There is a chart of `M` at `x`
  onto a round ball of `ℂⁿ = ℝⁿ × ℝⁿ`, sending `x` to `0`, and weights `αₖ ∈ 𝔤_x*` such that `K`
  acts in the chart by rotations through characters `χₖ` (trivial exactly when `αₖ = 0`), the
  chart is symplectic, it carries `ξ_M` to the model generator for `ξ ∈ 𝔤_x`, and
  `μ^ξ = μ^ξ(x) - ½ Σₖ αₖ(ξ) (qₖ² + pₖ²)` on its source for `ξ ∈ 𝔤_x`.

The proof applies Tau Ceti's `TauCeti.SmoothTwoForm.IsMomentMap.exists_weightModelChart` to the
torus `K`, with the moment map restricted along the inclusion
(`TauCeti.SmoothTwoForm.IsMomentMap.comp_monoidHom`), and carries the weights from the Lie algebra
of `K` to `𝔤_x` by the differential of the inclusion, a linear equivalence onto `𝔤_x`
(`TauCeti.Lie.EmbeddedLieSubgroupData.groupLieAlgebraEquivIsotropy`). A character is trivial
exactly when its weight vanishes by `ContinuousMonoidHom.eq_one_iff_of_forall_mulInvariantExp`.

This is the local model from which the local convexity of `μ` follows.

The file then reads the orbit directions and the derivative of `μ` in such a chart. The
statements take the properties of the chart as hypotheses, so that they apply to the chart of
`exists_weightModelChart_isotropy` and to any other with the same properties.

* `TauCeti.mfderiv_fundamentalVectorField_apply_eq_zero_of_ne_one`: the image of `ξ_M(x)` under
  the chart's differential has zero coordinates at every index `k` with `χₖ ≠ 1`. The
  differential of each `g ∈ K` at `x` fixes `ξ_M(x)` since `G` is commutative, and in the chart it
  is a rotation that fixes only vectors with zero coordinates where `χₖ(g) ≠ 1`.
* `TauCeti.SmoothTwoForm.IsMomentMap.fderiv_comp_symm_apply_eq_zero`: in the weight chart, the
  derivative of `μ^ξ` read in the chart vanishes on the vectors supported on the indices with
  `χₖ ≠ 1`. It is `ω₀(dchart (ξ_M), ·)` by
  `TauCeti.SmoothTwoForm.IsMomentMap.fderiv_comp_symm_apply` (in `MomentMap/Chart.lean`), in Tau
  Ceti's sign `σ(ξ_M, ·) = dμ^ξ`.
* `TauCeti.SmoothTwoForm.IsMomentMap.exists_fderiv_comp_symm_apply_eq`: for a subspace `𝔮` of the
  Lie algebra meeting the isotropy algebra only in `0`, every linear form on `𝔮` is
  `ξ ↦ d(μ^ξ ∘ chart⁻¹)(w)` for a vector `w` supported on the indices with `χₖ = 1`. That is, the
  derivative of the `𝔮*`-part of `μ` is onto from the weight-zero coordinates: `ξ ↦ ξ_M(x)` is
  injective on `𝔮`, and the vectors supported on those indices form a subspace stable under the
  complex structure, on which `ω₀` is nondegenerate by
  `TauCeti.SymplecticForm.Tames.isSymplectic_of_mem_invtSubmodule`.
* `TauCeti.SmoothTwoForm.IsMomentMap.contDiffAt_comp_symm_sub_comp_subtype` and
  `TauCeti.SmoothTwoForm.IsMomentMap.fderiv_comp_symm_sub_comp_subtype_apply_apply`: in any
  chart, the `𝔮*`-part `z ↦ (μ (chart⁻¹ z) - μ x)|_𝔮` of `μ` is smooth, since its components
  are (`TauCeti.SmoothTwoForm.IsMomentMap.contMDiff`), and its derivative is taken componentwise.
* `IsMomentMap.exists_fderiv_comp_symm_sub_comp_subtype_weightModelSplit_symm_eq`
  states the previous surjectivity for the `𝔮*`-part, with the coordinates split by
  `TauCeti.weightModelSplit`.

Finally, the product form:

* `TauCeti.SmoothTwoForm.IsMomentMap.exists_openPartialHomeomorph_weightMomentMap_prod`: for a
  subspace `𝔮` meeting `𝔤_x` only in `0`, there is a homeomorphism `Θ` from a neighbourhood
  of `x` onto an open subset of `𝔮* × W × ℂ^ι`, for a finite-dimensional normed space `W`,
  sending `x` to `0`, and nonzero weights `βₖ ∈ 𝔤_x*`, such that the `𝔤_x*`-part of
  `μ - μ(x)` is the weight-model moment map of `β` at the last component of `Θ` and the
  `𝔮*`-part is its first component. In the weight chart, the `𝔤_x*`-part depends only on the
  coordinates of nonzero weight (`TauCeti.weightMomentMap_eq_weightMomentMap_weightModelSplit_fst`),
  while the `𝔮*`-part has a derivative onto from those of zero weight
  (`exists_fderiv_comp_symm_sub_comp_subtype_weightModelSplit_symm_eq`); the implicit function
  theorem, in the form `HasStrictFDerivAt.exists_openPartialHomeomorph_fst_eq_snd_snd_eq` (in
  `Analysis/Calculus/Implicit.lean`), turns the `𝔮*`-part into coordinates. The factor `W` is
  the kernel of the derivative of `(z₀, z₊) ↦ (u, z₊)`, with `u` the `𝔮*`-part.

And the local convexity itself:

* `TauCeti.SmoothTwoForm.IsMomentMap.exists_isConvexChart`: every point of `M` lies in a
  convexity chart (`TauCeti.IsConvexChart`) of `e ∘ μ`, for any linear equivalence `e` of `𝔤*`
  onto a real normed space. With `𝔮` a complement of `𝔤_x`, extend the weights `β` by zero on
  `𝔮` to covectors `αₖ` of `𝔤`, and let `A ⊆ 𝔤*` be the covectors that vanish on `𝔤_x`, which
  meets the span of the `αₖ` only in `0`. Reordering the coordinates `Θ` of the product form as
  `(w, u ∘ π_𝔮, z) ∈ W × A × ℂ^ι`, with `π_𝔮` the projection onto `𝔮` along `𝔤_x`, the map
  `μ` reads `μ(x) + a + Φ_α(z)`, the slice model of Tau Ceti's
  `TauCeti.Geometry.Symplectic.Hamiltonian.WeightModel.Slice`. Its convexity charts at the points
  of the zero section are `TauCeti.exists_isConvexChart_of_eqOn_add_weightMomentMap`, and they
  are carried to `e ∘ μ` by `TauCeti.IsConvexChart.continuousLinearEquiv_comp`.

## Implementation notes

The isotropy algebra `𝔤_x` and the subspaces `𝔮` are submodules of `GroupLieAlgebra I G` itself,
so that `μ y` applies to their elements directly. Their duals `StrongDual ℝ 𝔤_x` and
`StrongDual ℝ 𝔮` use the norm that `open scoped GroupLieAlgebra` puts on the Lie algebra
(`GroupLieAlgebra.instNormedAddCommGroup`).

## References

* [C. Bjorndahl and Y. Karshon, *Revisiting Tietze–Nakajima: local and global convexity for
  maps*][BjorndahlKarshon2010], Proposition 29.
* [M. F. Atiyah, *Convexity and commuting Hamiltonians*][Atiyah1982], §2.
-/

public section

noncomputable section

open scoped ContDiff GroupLieAlgebra Manifold Topology

namespace TauCeti

section WeightCoordinates

variable {ι : Type*} [Fintype ι]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I 1 G]
  [IsMulCommutative G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [MulAction G M] [ContMDiffSMul I I' 1 G M]

/-- **Orbit directions lie in the weight-zero coordinates.** Let a commutative Lie group `G` act
on `M`, let `K` be a subgroup fixing `x`, and let `f : M → ℂ^ι`, differentiable at `x`, turn
the action of each `g ∈ K` near `x` into the rotation `zₖ ↦ χₖ(g) zₖ`. Then for every `ξ` in the
Lie algebra of `G`, the vector `df_x (ξ_M(x))` has both coordinates zero at each index `k` with
`χₖ ≠ 1`. -/
theorem mfderiv_fundamentalVectorField_apply_eq_zero_of_ne_one {K : Subgroup G}
    {χ : ι → K →ₜ* Circle} {f : M → EuclideanSpace ℝ ι × EuclideanSpace ℝ ι} {x : M}
    (hf : MDifferentiableAt I' 𝓘(ℝ, EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) f x)
    (hK : ∀ g : K, (g : G) • x = x)
    (hχ : ∀ g : K, ∀ᶠ y in 𝓝 x,
      f ((g : G) • y) = weightRotation (fun k ↦ Complex.arg (χ k g)) (f y))
    (ξ : GroupLieAlgebra I G) {k : ι} (hk : χ k ≠ 1) :
    (mfderiv I' 𝓘(ℝ, EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) f x
        (fundamentalVectorField I' ξ x)).1 k = 0 ∧
      (mfderiv I' 𝓘(ℝ, EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) f x
        (fundamentalVectorField I' ξ x)).2 k = 0 := by
  obtain ⟨g, hg⟩ : ∃ g, χ k g ≠ 1 := by
    by_contra! h
    exact hk (ContinuousMonoidHom.ext fun g ↦ by simpa using h g)
  set v := mfderiv I' 𝓘(ℝ, EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) f x
    (fundamentalVectorField I' ξ x)
  have hR := mfderiv_fundamentalVectorField_eq_of_eventually_smul_eq hf (hK g) _ (hχ g) ξ
  by_contra hne
  exact hg ((weightRotation_arg_apply_eq_self_iff (fun k ↦ χ k g) v).1 hR k (by tauto))

end WeightCoordinates

end TauCeti

namespace TauCeti.SmoothTwoForm.IsMomentMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G] [T2Space G]
  [IsTopologicalGroup G] [IsMulCommutative G] [CompactSpace G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M] [T2Space M]
  [MulAction G M] [ContMDiffSMul I I' ∞ G M]
  {σ : SmoothTwoForm I' M} {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)}

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

open scoped IsMulCommutative in
/-- **The weight chart of the identity component of a stabilizer, on the isotropy algebra.** Let a
compact commutative Lie group `G` act smoothly on a finite-dimensional symplectic manifold
`(M, σ)` without boundary, preserving `σ`, with moment map `μ`, and let `x : M`. Let `K` be the
identity component of the stabilizer `G_x` and `𝔤_x = {ξ | ξ_M(x) = 0}` the isotropy algebra.
Then there are continuous characters `χₖ : K → S¹`, `k < n`, weights `αₖ ∈ 𝔤_x*` with `χₖ = 1`
exactly when `αₖ = 0`, and a smooth chart of `M` at `x` with values in `ℂⁿ = ℝⁿ × ℝⁿ`, sending
`x` to `0`, whose image is the ball `‖q‖² + ‖p‖² < r²`, such that

* its source is `K`-invariant and `g ∈ K` acts in it by the rotation `zₖ ↦ χₖ(g) zₖ`;
* it pulls the standard symplectic form back to `σ`;
* for `ξ ∈ 𝔤_x`, its differential sends `ξ_M` to `weightInfinitesimalAction α · ξ`, the
  generator of the rotation by the angles `αₖ(ξ)`;
* for `ξ ∈ 𝔤_x`, `μ^ξ = μ^ξ(x) - ½ Σₖ αₖ(ξ) (qₖ² + pₖ²)` on its source. -/
theorem exists_weightModelChart_isotropy
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ) (hσ : σ.IsSymplectic)
    (hG : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ) (x : M) :
    let 𝔤ₓ : Submodule ℝ (GroupLieAlgebra I G) :=
      ((InfinitesimalAction.fundamental I G I' M).isotropy x).toSubmodule
    let K : Subgroup G := (MulAction.stabilizer G x).ambientConnectedComponentOfOne
    ∃ (n : ℕ) (χ : Fin n → K →ₜ* Circle)
      (α : Fin n → StrongDual ℝ 𝔤ₓ)
      (chart : PartialDiffeomorph I' 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))
        M (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ∞) (r : ℝ),
      (∀ k, χ k = 1 ↔ α k = 0) ∧
      x ∈ chart.source ∧ chart x = 0 ∧ 0 < r ∧
      chart.target = {z | ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 < r ^ 2} ∧
      (∀ g : K, ∀ y ∈ chart.source, (g : G) • y ∈ chart.source ∧
        chart ((g : G) • y) = weightRotation (fun k ↦ Complex.arg (χ k g)) (chart y)) ∧
      (∀ y ∈ chart.source, ∀ v w : TangentSpace I' y,
        σ.eval₂ y v w = stdSymplecticForm (mvfderiv I' chart y v) (mvfderiv I' chart y w)) ∧
      (∀ y ∈ chart.source, ∀ ξ : 𝔤ₓ,
        mfderiv I' 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) chart y
          (fundamentalVectorField I' (ξ : GroupLieAlgebra I G) y) =
            weightInfinitesimalAction α (chart y) ξ) ∧
      ∀ y ∈ chart.source, ∀ ξ : 𝔤ₓ,
        μ y ξ = μ x ξ + weightMomentMap α (chart y) ξ := by
  intro 𝔤ₓ K
  set S := MulAction.stabilizer G x
  have hS : IsClosed (S : Set G) := isClosed_stabilizer
    (ContMDiffSMul.contMDiff_smul_const (I := I) (I' := I') (n := ∞) x).continuous
  refine (Lie.isTorus_ambientConnectedComponentOfOne (S := S) hS.isCompact).elim (I := I)
    fun d ↦ ?_
  intro _ _ _ _ _ _ _
  let F := (Lie.lieSubalgebraOfSubgroup (I := I) K).toSubmodule
  let _ : ContMDiffSMul 𝓘(ℝ, F) I' ∞ K M := d.contMDiffSMul
  have hφ : MDifferentiableAt 𝓘(ℝ, F) I K.subtype 1 :=
    d.contMDiff_subtypeVal.mdifferentiableAt (by simp)
  have hK := h.comp_monoidHom K.subtype hφ fun _ _ ↦ rfl
  obtain ⟨n, χ, α, chart, r, hα, -, hx, h0, hr, htarget, hequiv, hform, hgen, hμ⟩ :=
    hK.exists_weightModelChart hσ (fun g ↦ hG g) (p := x)
      fun g ↦ Subgroup.ambientConnectedComponentOfOne_le _ g.property
  -- The differential of the inclusion `K → G` identifies the Lie algebra of `K` with `𝔤ₓ`.
  let e : GroupLieAlgebra 𝓘(ℝ, F) K ≃ₗ[ℝ] 𝔤ₓ := d.groupLieAlgebraEquivIsotropy (I' := I')
  have he (ξ : 𝔤ₓ) :
      K.subtype.groupLieAlgebraMap 𝓘(ℝ, F) I (e.symm ξ) = (ξ : GroupLieAlgebra I G) :=
    d.groupLieAlgebraMap_subtype_groupLieAlgebraEquivIsotropy_symm ξ
  -- The weights `α k`, functionals on the model `F` of `K`, read on its Lie algebra through
  -- Tau Ceti's identification `groupLieAlgebraEquivModelVectorSpace` of the Lie algebra with
  -- `F`. Tau Ceti's `exists_weightModelChart` applies `α k` to elements of the Lie algebra
  -- directly, so `hβ` states `β k η` in that form.
  let c : GroupLieAlgebra 𝓘(ℝ, F) K ≃ₗ[ℝ] F :=
    groupLieAlgebraEquivModelVectorSpace (I := 𝓘(ℝ, F)) (G := K)
  let β (k : Fin n) : Module.Dual ℝ (GroupLieAlgebra 𝓘(ℝ, F) K) :=
    (α k : F →ₗ[ℝ] ℝ) ∘ₗ c.toLinearMap
  have hβ (k : Fin n) (η : GroupLieAlgebra 𝓘(ℝ, F) K) : β k η = α k η := by
    simp only [β, c, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      ContinuousLinearMap.coe_coe]
    -- Tau Ceti defines `groupLieAlgebraEquivModelVectorSpace` as `LinearEquiv.refl` and gives it
    -- no evaluation lemma, so this step is by definition.
    rfl
  let α' : Fin n → StrongDual ℝ 𝔤ₓ := fun k ↦
    LinearMap.toContinuousLinearMap (β k ∘ₗ e.symm.toLinearMap)
  have hα' (k : Fin n) (ξ : 𝔤ₓ) : α' k ξ = α k (e.symm ξ) := by
    rw [← hβ]
    simp [α']
  refine ⟨n, χ, α', chart, r, fun k ↦ ?_, hx, h0, hr, htarget, hequiv, hform, fun y hy ξ ↦ ?_,
    fun y hy ξ ↦ ?_⟩
  · rw [ContinuousMonoidHom.eq_one_iff_of_forall_mulInvariantExp (α := β k)
      fun η ↦ by rw [hα, hβ]]
    refine ⟨fun h0 ↦ ContinuousLinearMap.ext fun ξ ↦ by simp [α', h0],
      fun h0 ↦ LinearMap.ext fun η ↦ by simpa [α'] using congr($h0 (e η))⟩
  · have hξ := hgen y hy (e.symm ξ)
    rw [← K.subtype.fundamentalVectorField_groupLieAlgebraMap hφ fun _ _ ↦ rfl, he] at hξ
    rw [hξ, weightInfinitesimalAction_apply α']
    exact (weightInfinitesimalAction_apply (𝔱 := F) α _ (e.symm ξ)).trans (by simp only [hα'])
  · have hξ := hμ y hy (e.symm ξ)
    rw [LinearMap.comp_apply, LinearMap.comp_apply, ContinuousLinearMap.coe_coe, he] at hξ
    rw [hξ, weightMomentMap_apply α']
    exact congrArg _ ((weightMomentMap_apply (𝔱 := F) α _ (e.symm ξ)).trans (by simp only [hα']))

end TauCeti.SmoothTwoForm.IsMomentMap

namespace TauCeti.SmoothTwoForm.IsMomentMap

section WeightChart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  [IsMulCommutative G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M]
  [MulAction G M] [ContMDiffSMul I I' ∞ G M]
  {σ : SmoothTwoForm I' M} {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)}
  {ι : Type*} [Fintype ι] {K : Subgroup G} {χ : ι → K →ₜ* Circle}
  {chart : PartialDiffeomorph I' 𝓘(ℝ, EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) M
    (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) ∞} {x : M}

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

/-- **The moment map in a weight chart is flat in the nontrivial weight directions.** Let a
commutative Lie group `G` act on `M` with moment map `μ` for `σ`, let `K ≤ G` fix `x`, and let
`chart` be a chart at `x` into `ℂ^ι` that carries `σ` at `x` to the standard form and in which
each `g ∈ K` acts near `x` by the rotation `zₖ ↦ χₖ(g) zₖ`. Then for every `ξ`, the derivative at
`chart x` of `μ^ξ` read in the chart vanishes on every vector whose coordinates are zero at each
index `k` with `χₖ = 1`. -/
theorem fderiv_comp_symm_apply_eq_zero
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ) (hx : x ∈ chart.source)
    (hform : ∀ v w : TangentSpace I' x,
      σ.eval₂ x v w = stdSymplecticForm (mvfderiv I' chart x v) (mvfderiv I' chart x w))
    (hK : ∀ g : K, (g : G) • x = x)
    (hχ : ∀ g : K, ∀ᶠ y in 𝓝 x,
      chart ((g : G) • y) = weightRotation (fun k ↦ Complex.arg (χ k g)) (chart y))
    (ξ : GroupLieAlgebra I G) {w : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι}
    (hw : ∀ k, χ k = 1 → w.1 k = 0 ∧ w.2 k = 0) :
    fderiv ℝ (fun z ↦ μ (chart.symm z) ξ) (chart x) w = 0 := by
  rw [h.fderiv_comp_symm_apply chart hx hform, InfinitesimalAction.fundamental_apply]
  refine stdSymplecticForm_eq_zero_of_forall fun k ↦ ?_
  by_cases hk : χ k = 1
  · exact Or.inr (hw k hk)
  · exact Or.inl (mfderiv_fundamentalVectorField_apply_eq_zero_of_ne_one
      (chart.mdifferentiableAt (by simp) hx) hK hχ ξ hk)

/-- **The derivative of the transverse part of the moment map is onto from the weight-zero
coordinates.** In the setting of `fderiv_comp_symm_apply_eq_zero`, with `G` finite-dimensional, let
`𝔮` be a subspace of the Lie algebra of `G` that meets the isotropy algebra `𝔤ₓ = {ξ | ξ_M(x) = 0}`
only in `0`, for instance a linear complement of it. Then every linear form `φ` on `𝔮` is
`ξ ↦ d(μ^ξ ∘ chart⁻¹)_{chart x} w` for some vector `w` whose coordinates vanish at each index `k`
with `χₖ ≠ 1`. -/
theorem exists_fderiv_comp_symm_apply_eq [FiniteDimensional ℝ E]
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ) (hx : x ∈ chart.source)
    (hform : ∀ v w : TangentSpace I' x,
      σ.eval₂ x v w = stdSymplecticForm (mvfderiv I' chart x v) (mvfderiv I' chart x w))
    (hK : ∀ g : K, (g : G) • x = x)
    (hχ : ∀ g : K, ∀ᶠ y in 𝓝 x,
      chart ((g : G) • y) = weightRotation (fun k ↦ Complex.arg (χ k g)) (chart y))
    {𝔮 : Submodule ℝ (GroupLieAlgebra I G)}
    (h𝔮 : Disjoint 𝔮 ((InfinitesimalAction.fundamental I G I' M).isotropy x).toSubmodule)
    (φ : Module.Dual ℝ 𝔮) :
    ∃ w : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι, (∀ k, χ k ≠ 1 → w.1 k = 0 ∧ w.2 k = 0) ∧
      ∀ ξ : 𝔮, fderiv ℝ (fun z ↦ μ (chart.symm z) ξ) (chart x) w = φ ξ := by
  set D := mfderiv I' 𝓘(ℝ, EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) chart x
  -- The vectors with zero coordinates at the nontrivial weights, and `ξ ↦ D (ξ_M x)`.
  let W : Submodule ℝ (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :=
    { carrier := {w | ∀ k, χ k ≠ 1 → w.1 k = 0 ∧ w.2 k = 0}
      add_mem' := fun ha hb k hk ↦ by simp [(ha k hk).1, (ha k hk).2, (hb k hk).1, (hb k hk).2]
      zero_mem' := fun k _ ↦ by simp
      smul_mem' := fun c a ha k hk ↦ by simp [(ha k hk).1, (ha k hk).2] }
  let v : GroupLieAlgebra I G →ₗ[ℝ] EuclideanSpace ℝ ι × EuclideanSpace ℝ ι :=
    D.toLinearMap ∘ₗ (InfinitesimalAction.fundamental I G I' M).eval x
  have hv (ξ : GroupLieAlgebra I G) : v ξ = D (fundamentalVectorField I' ξ x) :=
    congrArg D ((InfinitesimalAction.eval_apply _ x ξ).trans
      (congrFun (InfinitesimalAction.fundamental_apply ξ) x))
  have hvW (ξ : GroupLieAlgebra I G) : v ξ ∈ W := fun k hk ↦ hv ξ ▸
    mfderiv_fundamentalVectorField_apply_eq_zero_of_ne_one (chart.mdifferentiableAt (by simp) hx)
      hK hχ ξ hk
  -- `W` is `J₀`-stable, so `ω₀` is nondegenerate on it, and the pairing
  -- `(ξ, w) ↦ ω₀(D (ξ_M x), w)` on `𝔮 × W` is injective in `ξ`.
  have hWs : (stdSymplecticForm (V := EuclideanSpace ℝ ι)).IsSymplectic W :=
    stdSymplecticForm_tames_product.isSymplectic_of_mem_invtSubmodule <|
      (Module.End.mem_invtSubmodule _).2 fun u hu k hk ↦ by simp [(hu k hk).1, (hu k hk).2]
  let B : 𝔮 →ₗ[ℝ] W →ₗ[ℝ] ℝ :=
    (stdSymplecticForm (V := EuclideanSpace ℝ ι)).toBilinForm.compl₁₂ (v ∘ₗ 𝔮.subtype) W.subtype
  have hB (ξ : 𝔮) (w : W) : B ξ w = stdSymplecticForm (v ξ) w := rfl
  have hBinj : Function.Injective B := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro ξ hξ
    have hv0 : v ξ = 0 := Submodule.disjoint_def.1 (SymplecticForm.isSymplectic_iff_disjoint.1 hWs)
      _ (hvW ξ) (SymplecticForm.mem_orthogonal_iff'.2 fun w hw ↦
        LinearMap.congr_fun (LinearMap.mem_ker.1 hξ) ⟨w, hw⟩)
    have hfund : fundamentalVectorField I' (ξ : GroupLieAlgebra I G) x = 0 := by
      rw [← chart.mfderiv_symm_apply_mfderiv_apply (by simp) hx
        (fundamentalVectorField I' (ξ : GroupLieAlgebra I G) x), ← hv, hv0]
      exact map_zero _
    have hiso : (ξ : GroupLieAlgebra I G) ∈
        ((InfinitesimalAction.fundamental I G I' M).isotropy x).toSubmodule := by
      rw [LieSubalgebra.mem_toSubmodule, InfinitesimalAction.mem_isotropy_iff,
        InfinitesimalAction.fundamental_apply, hfund]
    exact Subtype.ext (Submodule.disjoint_def.1 h𝔮 _ ξ.property hiso)
  obtain ⟨w, hw⟩ := LinearMap.flip_surjective_iff₁.2 hBinj φ
  refine ⟨w, w.property, fun ξ ↦ ?_⟩
  rw [h.fderiv_comp_symm_apply chart hx hform, InfinitesimalAction.fundamental_apply, ← hv, ← hB,
    ← LinearMap.flip_apply, hw]

omit [IsMulCommutative G] in
/-- **The transverse part of the moment map is smooth in a chart.** Let `μ` be a moment map on
`M`, with `G` finite-dimensional, `chart` a chart at `x`, and `𝔮` a subspace of the Lie algebra of
`G`. Then the map `z ↦ (μ (chart⁻¹ z) - μ x)|_𝔮` into `𝔮*` is smooth at `chart x`. -/
theorem contDiffAt_comp_symm_sub_comp_subtype [FiniteDimensional ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {chart : PartialDiffeomorph I' 𝓘(ℝ, F) M F ∞}
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ) (hx : x ∈ chart.source)
    (𝔮 : Submodule ℝ (GroupLieAlgebra I G)) :
    ContDiffAt ℝ ∞
      (fun z ↦ LinearMap.toContinuousLinearMap ((μ (chart.symm z) - μ x) ∘ₗ 𝔮.subtype))
      (chart x) := by
  have hxt : chart x ∈ chart.target := chart.map_source hx
  rw [← contDiffWithinAt_univ, contDiffWithinAt_clm_apply]
  refine fun ξ ↦ ContDiffAt.contDiffWithinAt ?_
  simp only [LinearMap.coe_toContinuousLinearMap']
  refine ContDiffAt.sub ?_ contDiffAt_const
  rw [← contMDiffAt_iff_contDiffAt]
  exact (h.contMDiff (ξ : GroupLieAlgebra I G)).contMDiffAt.comp _
    (chart.symm.contMDiffAt hxt)

omit [IsMulCommutative G] in
/-- The derivative of the transverse part `z ↦ (μ (chart⁻¹ z) - μ x)|_𝔮` of the moment map at
`chart x`, evaluated at `ξ ∈ 𝔮`, is the derivative of `μ^ξ ∘ chart⁻¹`. -/
theorem fderiv_comp_symm_sub_comp_subtype_apply_apply [FiniteDimensional ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {chart : PartialDiffeomorph I' 𝓘(ℝ, F) M F ∞}
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ) (hx : x ∈ chart.source)
    (𝔮 : Submodule ℝ (GroupLieAlgebra I G)) (w : F) (ξ : 𝔮) :
    fderiv ℝ (fun z ↦ LinearMap.toContinuousLinearMap ((μ (chart.symm z) - μ x) ∘ₗ 𝔮.subtype))
        (chart x) w ξ =
      fderiv ℝ (fun z ↦ μ (chart.symm z) ξ) (chart x) w := by
  set Fq : F → StrongDual ℝ 𝔮 := fun z ↦
    LinearMap.toContinuousLinearMap ((μ (chart.symm z) - μ x) ∘ₗ 𝔮.subtype)
  have hFq (z) (ξ : 𝔮) : Fq z ξ = μ (chart.symm z) ξ - μ x ξ := by simp [Fq]
  have hd : DifferentiableAt ℝ Fq (chart x) :=
    (contDiffAt_comp_symm_sub_comp_subtype h hx 𝔮).differentiableAt (by simp)
  calc fderiv ℝ Fq (chart x) w ξ = fderiv ℝ (fun z ↦ Fq z ξ) (chart x) w := by
        rw [fderiv_clm_apply hd (differentiableAt_const ξ)]
        simp
    _ = _ := by simp only [hFq, fderiv_sub_const]

/-- **The derivative of the transverse part of the moment map is onto from the weight-zero block.**
In the setting of `exists_fderiv_comp_symm_apply_eq`, split the coordinates of `ℂ^ι` by
`weightModelSplit p` along a predicate `p` that holds only at indices with `χₖ ≠ 1`. Then every
continuous linear form `φ` on `𝔮` is the derivative at `chart x` of the `𝔮*`-part
`z ↦ (μ (chart⁻¹ z) - μ x)|_𝔮` of `μ`, applied to `(weightModelSplit p)⁻¹ (0, b)` for some `b` in
the coordinates where `p` fails. -/
theorem exists_fderiv_comp_symm_sub_comp_subtype_weightModelSplit_symm_eq [FiniteDimensional ℝ E]
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ) (hx : x ∈ chart.source)
    (hform : ∀ v w : TangentSpace I' x,
      σ.eval₂ x v w = stdSymplecticForm (mvfderiv I' chart x v) (mvfderiv I' chart x w))
    (hK : ∀ g : K, (g : G) • x = x)
    (hχ : ∀ g : K, ∀ᶠ y in 𝓝 x,
      chart ((g : G) • y) = weightRotation (fun k ↦ Complex.arg (χ k g)) (chart y))
    {𝔮 : Submodule ℝ (GroupLieAlgebra I G)}
    (h𝔮 : Disjoint 𝔮 ((InfinitesimalAction.fundamental I G I' M).isotropy x).toSubmodule)
    {p : ι → Prop} [DecidablePred p] (hp : ∀ k, p k → χ k ≠ 1) (φ : StrongDual ℝ 𝔮) :
    ∃ b : EuclideanSpace ℝ {k // ¬p k} × EuclideanSpace ℝ {k // ¬p k},
      fderiv ℝ (fun z ↦ LinearMap.toContinuousLinearMap ((μ (chart.symm z) - μ x) ∘ₗ 𝔮.subtype))
        (chart x) ((weightModelSplit p).symm (0, b)) = φ := by
  obtain ⟨w, hw, hwq⟩ :=
    exists_fderiv_comp_symm_apply_eq h hx hform hK hχ (𝔮 := 𝔮) h𝔮 (φ : 𝔮 →ₗ[ℝ] ℝ)
  refine ⟨(weightModelSplit p w).2, ContinuousLinearMap.ext fun ξ ↦ ?_⟩
  have h1 : (weightModelSplit p w).1 = 0 := by
    have hw' (i : {k // p k}) := hw i (hp i i.property)
    exact Prod.ext (by ext i; simp [(hw' i).1]) (by ext i; simp [(hw' i).2])
  rw [← h1, Prod.mk.eta, ContinuousLinearEquiv.symm_apply_apply,
    fderiv_comp_symm_sub_comp_subtype_apply_apply h hx]
  exact hwq ξ

end WeightChart

end TauCeti.SmoothTwoForm.IsMomentMap

namespace TauCeti.SmoothTwoForm.IsMomentMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G] [T2Space G]
  [IsTopologicalGroup G] [IsMulCommutative G] [CompactSpace G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M] [T2Space M]
  [MulAction G M] [ContMDiffSMul I I' ∞ G M]
  {σ : SmoothTwoForm I' M} {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)}

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

open scoped IsMulCommutative in
/-- **The product form of a torus moment map near a point.** In the setting of
`exists_weightModelChart_isotropy`, let `𝔮` be a subspace of the Lie algebra meeting the isotropy
algebra `𝔤_x` only in `0`, for instance a linear complement of it. Then there are weights
`βₖ ∈ 𝔤_x*`, all nonzero, indexed by a finite type, and an open partial homeomorphism `Θ` of `M`
onto an open subset of `𝔮* × W × ℂ^ι`, for a finite-dimensional normed space `W`, defined at
`x` with `Θ x = 0`, in which `μ` reads as a product: on the source of `Θ`,
`μ^ξ = μ^ξ(x) + Φ_β(z)(ξ)` for `ξ ∈ 𝔤_x`, with `z` the last component of `Θ` and `Φ_β` the
moment map of the weight model, and `μ^ξ = μ^ξ(x) + u(ξ)` for `ξ ∈ 𝔮`, with `u` the first
component of `Θ`. -/
theorem exists_openPartialHomeomorph_weightMomentMap_prod
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ) (hσ : σ.IsSymplectic)
    (hG : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ) (x : M)
    {𝔮 : Submodule ℝ (GroupLieAlgebra I G)}
    (h𝔮 : Disjoint 𝔮 ((InfinitesimalAction.fundamental I G I' M).isotropy x).toSubmodule) :
    let 𝔤ₓ : Submodule ℝ (GroupLieAlgebra I G) :=
      ((InfinitesimalAction.fundamental I G I' M).isotropy x).toSubmodule
    ∃ (ι : Type) (_ : Fintype ι) (β : ι → StrongDual ℝ 𝔤ₓ) (W : Type) (_ : NormedAddCommGroup W)
      (_ : NormedSpace ℝ W) (_ : FiniteDimensional ℝ W)
      (Θ : OpenPartialHomeomorph M
        (StrongDual ℝ 𝔮 × W × (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι))),
      (∀ k, β k ≠ 0) ∧ x ∈ Θ.source ∧ Θ x = 0 ∧
      (∀ y ∈ Θ.source, ∀ ξ : 𝔤ₓ, μ y ξ = μ x ξ + weightMomentMap β (Θ y).2.2 ξ) ∧
      ∀ y ∈ Θ.source, ∀ ξ : 𝔮, μ y ξ = μ x ξ + (Θ y).1 ξ := by
  intro 𝔤ₓ
  classical
  obtain ⟨n, χ, α, chart, -, hα, hx, h0, -, -, hequiv, hform, -, hμ⟩ :=
    exists_weightModelChart_isotropy h hσ hG x
  set p : Fin n → Prop := fun k ↦ α k ≠ 0
  -- Coordinates `(a, b)`: `a` those of zero weight, `b` the others.
  let T : ((EuclideanSpace ℝ {k // ¬p k} × EuclideanSpace ℝ {k // ¬p k}) ×
      (EuclideanSpace ℝ {k // p k} × EuclideanSpace ℝ {k // p k})) ≃L[ℝ]
      EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) :=
    (ContinuousLinearEquiv.prodComm ℝ _ _).trans (weightModelSplit p).symm
  -- The `𝔮*`-part of `μ - μ x`, read in the chart.
  set Fq : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → StrongDual ℝ 𝔮 := fun z ↦
    LinearMap.toContinuousLinearMap ((μ (chart.symm z) - μ x) ∘ₗ 𝔮.subtype)
  have hFq (z) (ξ : 𝔮) : Fq z ξ = μ (chart.symm z) ξ - μ x ξ := by simp [Fq]
  have hFqd : ContDiffAt ℝ 1 Fq (T 0) := by
    rw [map_zero T, ← h0]
    exact (contDiffAt_comp_symm_sub_comp_subtype h hx 𝔮).of_le (by simp)
  have hFc : ContDiffAt ℝ 1 (Fq ∘ T) 0 := hFqd.comp 0 T.contDiff.contDiffAt
  have hF := hFc.hasStrictFDerivAt (hFc.differentiableAt one_ne_zero).hasFDerivAt one_ne_zero
  obtain ⟨Φ, hΦ0, hΦa, hΦ⟩ := hF.exists_openPartialHomeomorph_fst_eq_snd_snd_eq <|
    LinearMap.range_eq_top.2 fun q ↦ by
      obtain ⟨b, hb⟩ := exists_fderiv_comp_symm_sub_comp_subtype_weightModelSplit_symm_eq h hx
        (hform x hx) (fun g ↦ Subgroup.ambientConnectedComponentOfOne_le _ g.property)
        (fun g ↦ Filter.eventually_of_mem (chart.open_source.mem_nhds hx)
          fun y hy ↦ (hequiv g y hy).2) h𝔮 (p := p) (fun k hk ↦ by rwa [Ne, hα]) q
      refine ⟨b, ?_⟩
      rw [ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.inl_apply, fderiv_comp _ (hFqd.differentiableAt one_ne_zero)
          T.differentiableAt, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.fderiv,
        ContinuousLinearEquiv.coe_coe, map_zero T, ← h0]
      exact hb
  set Θ := (chart.toOpenPartialHomeomorph.transHomeomorph T.symm.toHomeomorph).trans Φ
  -- The topologies of `T` and of `Φ` on the split coordinates agree only up to unfolding, so
  -- `simp` does not see through `Θ`: its source and values are rewritten by hand.
  have hΘs {y : M} : y ∈ Θ.source ↔ y ∈ chart.source ∧ T.symm (chart y) ∈ Φ.source := by
    rw [OpenPartialHomeomorph.trans_source, Set.mem_inter_iff, Set.mem_preimage,
      OpenPartialHomeomorph.transHomeomorph_source,
      OpenPartialHomeomorph.transHomeomorph_apply, Function.comp_apply,
      ContinuousLinearEquiv.coe_toHomeomorph, PartialDiffeomorph.toFun'_toOpenPartialHomeomorph,
      PartialDiffeomorph.toOpenPartialHomeomorph_source]
  have hΘ (y : M) : Θ y = Φ (T.symm (chart y)) := by
    rw [OpenPartialHomeomorph.trans_apply, OpenPartialHomeomorph.transHomeomorph_apply,
      Function.comp_apply, ContinuousLinearEquiv.coe_toHomeomorph,
      PartialDiffeomorph.toFun'_toOpenPartialHomeomorph]
  refine ⟨{k // p k}, inferInstance, fun k ↦ α k, _, inferInstance, inferInstance, inferInstance, Θ,
    fun k ↦ k.property, hΘs.2 ⟨hx, by simpa [h0] using hΦ0⟩, ?_, ?_, ?_⟩
  · have hsymm0 : chart.symm 0 = x := by rw [← h0]; exact chart.left_inv hx
    have hFq0 : Fq 0 = 0 := ContinuousLinearMap.ext fun ξ ↦ by
      rw [hFq, hsymm0, sub_self, zero_apply]
    rw [hΘ, h0, map_zero, hΦa]
    simp only [Function.comp_apply, map_zero, hFq0, Prod.snd_zero, Prod.mk_eq_zero, and_self]
  · intro y hy ξ
    rw [hμ y (hΘs.1 hy).1 ξ, weightMomentMap_eq_weightMomentMap_weightModelSplit_fst (𝔱 := 𝔤ₓ)
      (p := p) fun k hk ↦ not_not.1 hk, hΘ, (hΦ _).2]
    simp [T]
  · intro y hy ξ
    rw [hΘ, (hΦ _).1]
    simp [hFq, chart.toPartialEquiv.left_inv (hΘs.1 hy).1]

open scoped IsMulCommutative in
/-- **Local convexity of a torus moment map.** Let a compact commutative Lie group `G` act smoothly
on a finite-dimensional Hausdorff symplectic manifold `(M, σ)` without boundary, preserving `σ`,
with moment map `μ`, and read `μ` in a real normed space `V` through a linear equivalence
`e : 𝔤* ≃ V`. Then every point `x : M` lies in a convexity chart of `e ∘ μ`: an open set `U ∋ x`
on which `e ∘ μ` is open onto a convex image, with preconnected fibres. -/
theorem exists_isConvexChart
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ) (hσ : σ.IsSymplectic)
    (hG : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ)
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (e : Module.Dual ℝ (GroupLieAlgebra I G) ≃ₗ[ℝ] V) (x : M) :
    ∃ U, x ∈ U ∧ IsConvexChart (e ∘ μ) U := by
  set 𝔤ₓ : Submodule ℝ (GroupLieAlgebra I G) :=
    ((InfinitesimalAction.fundamental I G I' M).isotropy x).toSubmodule
  obtain ⟨𝔮, h𝔮⟩ := Submodule.exists_isCompl 𝔤ₓ
  obtain ⟨ι, _, β, W, _, _, _, Θ, -, hx, h0, hμk, hμq⟩ :=
    exists_openPartialHomeomorph_weightMomentMap_prod h hσ hG x h𝔮.symm.disjoint
  -- The projections of `𝔤` onto `𝔤ₓ` along `𝔮` and onto `𝔮` along `𝔤ₓ`.
  set P₁ : GroupLieAlgebra I G →L[ℝ] 𝔤ₓ :=
    LinearMap.toContinuousLinearMap (𝔤ₓ.projectionOnto 𝔮 h𝔮)
  set P₂ : GroupLieAlgebra I G →L[ℝ] 𝔮 :=
    LinearMap.toContinuousLinearMap (𝔮.projectionOnto 𝔤ₓ h𝔮.symm)
  -- The weights `β` extended by zero on `𝔮`, and the covectors `A` vanishing on `𝔤ₓ`, which are
  -- the covectors of `𝔮` read through `P₂`.
  set α : ι → StrongDual ℝ (GroupLieAlgebra I G) := fun k ↦ (β k).comp P₁ with hα
  set R : StrongDual ℝ 𝔮 →L[ℝ] StrongDual ℝ (GroupLieAlgebra I G) :=
    ContinuousLinearMap.precomp ℝ P₂
  have hR (u : StrongDual ℝ 𝔮) (ξ : 𝔮) : R u ξ = u ξ := by
    simp [R, P₂, Submodule.projectionOnto_apply_left]
  have hRi : Function.Injective R := fun u v huv ↦
    ContinuousLinearMap.ext fun ξ ↦ by rw [← hR, huv, hR]
  set A := LinearMap.range (R : StrongDual ℝ 𝔮 →ₗ[ℝ] StrongDual ℝ (GroupLieAlgebra I G))
  let T : StrongDual ℝ 𝔮 ≃L[ℝ] A :=
    LinearEquiv.toContinuousLinearEquiv (E := StrongDual ℝ 𝔮) (F := A)
      (LinearEquiv.ofInjective _ hRi)
  have hT (u : StrongDual ℝ 𝔮) : (T u : StrongDual ℝ (GroupLieAlgebra I G)) = u.comp P₂ := by
    rw [LinearEquiv.coe_toContinuousLinearEquiv', LinearEquiv.ofInjective_apply,
      ContinuousLinearMap.coe_coe, ContinuousLinearMap.precomp_apply]
  -- The span of the weights vanishes on `𝔮`, and `A` on `𝔤ₓ`, so they meet only in `0`.
  have hspan : ∀ ψ ∈ Submodule.span ℝ (Set.range α), ∀ ξ : 𝔮, ψ ξ = 0 := by
    intro ψ hψ ξ
    induction hψ using Submodule.span_induction with
    | mem _ hψ =>
      obtain ⟨k, rfl⟩ := hψ
      simp [α, P₁, Submodule.projectionOnto_apply_right]
    | zero => rfl
    | add _ _ _ _ h₁ h₂ => rw [add_apply, h₁, h₂, add_zero]
    | smul _ _ _ h => rw [smul_apply, h, smul_zero]
  have hA : Disjoint A (Submodule.span ℝ (Set.range α)) := by
    rw [Submodule.disjoint_def]
    rintro _ ⟨u, rfl⟩ hu
    rw [ContinuousLinearMap.coe_coe] at hu ⊢
    have hu0 : u = 0 := ContinuousLinearMap.ext fun ξ ↦ by rw [← hR, hspan _ hu ξ, zero_apply]
    rw [hu0, map_zero]
  -- The coordinates `Θ`, reordered as `(w, T u, z)`.
  let Φ : (StrongDual ℝ 𝔮 × W × (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)) ≃ₜ
      (W × (A × (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι))) :=
    { toFun q := (q.2.1, (T q.1, q.2.2))
      invFun q := (T.symm q.2.1, (q.1, q.2.2))
      left_inv q := Prod.ext (T.symm_apply_apply q.1) rfl
      right_inv q := Prod.ext rfl (Prod.ext (T.apply_symm_apply q.2.1) rfl)
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  set e' := Θ.transHomeomorph Φ
  have he's : e'.source = Θ.source := OpenPartialHomeomorph.transHomeomorph_source Θ Φ
  have he' (y : M) : e' y = ((Θ y).2.1, (T (Θ y).1, (Θ y).2.2)) := by
    -- `Φ` is the local structure above, so its value unfolds.
    rw [OpenPartialHomeomorph.transHomeomorph_apply, Function.comp_apply]
    rfl
  -- Read `μ` as a map to `StrongDual ℝ 𝔤`; on the source of `Θ` it is the slice model.
  set f : M → StrongDual ℝ (GroupLieAlgebra I G) := fun y ↦ LinearMap.toContinuousLinearMap (μ y)
  have hf : Set.EqOn f ((fun q ↦ f x + ((q.2.1 : StrongDual ℝ (GroupLieAlgebra I G)) +
      weightMomentMap α q.2.2)) ∘ e') e'.source := by
    intro y hy
    rw [he's] at hy
    ext ξ
    have hξ : ξ = (P₁ ξ : GroupLieAlgebra I G) + (P₂ ξ : GroupLieAlgebra I G) := by
      simp only [P₁, P₂, LinearMap.coe_toContinuousLinearMap',
        Submodule.coe_projectionOnto_apply]
      exact (Submodule.projection_add_projection_eq_self h𝔮 ξ).symm
    have hy₁ := hμk y hy (P₁ ξ)
    have hy₂ := hμq y hy (P₂ ξ)
    simp only [f, Function.comp_apply, he', hT, add_apply,
      LinearMap.coe_toContinuousLinearMap', ContinuousLinearMap.comp_apply, weightMomentMap_apply,
      hα] at hy₁ ⊢
    rw [hξ, map_add, map_add, hy₁, hy₂, ← hξ]
    ring
  obtain ⟨U, hxU, hU⟩ := exists_isConvexChart_of_eqOn_add_weightMomentMap hA hf (he's ▸ hx)
    (by rw [he', h0, Prod.snd_zero, Prod.snd_zero])
  refine ⟨U, hxU, ?_⟩
  convert hU.continuousLinearEquiv_comp
    (LinearMap.toContinuousLinearMap.symm.trans e).toContinuousLinearEquiv using 1
  funext y
  simp [f]

end TauCeti.SmoothTwoForm.IsMomentMap
