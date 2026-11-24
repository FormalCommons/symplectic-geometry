/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.WeightModel.NormalForm
import SymplecticGeometry.Geometry.Lie.Exponential.CommutativeGroup.Character
import SymplecticGeometry.Geometry.Lie.FundamentalVectorField
import SymplecticGeometry.Geometry.Lie.Subgroup.IdentityComponent
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import TauCeti.Geometry.Symplectic.Hamiltonian.EquivariantMomentMap.Restrict
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
  the chart's differential has zero coordinates at every index `k` with `χₖ ≠ 1`. Each `g ∈ K`
  fixes `ξ_M(x)` since `G` is commutative, and acts in the chart by a rotation that fixes only
  vectors with zero coordinates where `χₖ(g) ≠ 1`.
* `TauCeti.SmoothTwoForm.IsMomentMap.fderiv_comp_symm_apply`: in a chart that carries `σ` to the
  standard form `ω₀` of `V × V`, the derivative of `μ^ξ` read in the chart is
  `ω₀(dchart (ξ_M), ·)`, in Tau Ceti's sign `σ(ξ_M, ·) = dμ^ξ`.
* `TauCeti.SmoothTwoForm.IsMomentMap.fderiv_comp_symm_apply_eq_zero`: so in the weight chart that
  derivative vanishes on the vectors supported on the indices with `χₖ ≠ 1`.
* `TauCeti.SmoothTwoForm.IsMomentMap.exists_fderiv_comp_symm_apply_eq`: for a subspace `𝔮` of the
  Lie algebra meeting the isotropy algebra only in `0`, every linear form on `𝔮` is
  `ξ ↦ d(μ^ξ ∘ chart⁻¹)(w)` for a vector `w` supported on the indices with `χₖ = 1`. That is, the
  derivative of the `𝔮*`-part of `μ` is onto from the weight-zero coordinates: `ξ ↦ ξ_M(x)` is
  injective on `𝔮`, and `ω₀` pairs a vector supported on those indices with its image under the
  complex structure to a positive number.

## References

* [C. Bjorndahl and Y. Karshon, *Revisiting Tietze–Nakajima: local and global convexity for
  maps*][BjorndahlKarshon2010], Proposition 29.
* [M. F. Atiyah, *Convexity and commuting Hamiltonians*][Atiyah1982], §2.
-/

public section

noncomputable section

open scoped ContDiff Manifold Topology

namespace TauCeti

section WeightCoordinates

variable {ι : Type*} [Fintype ι]

/-- The standard symplectic form of `ℂ^ι = ℝ^ι × ℝ^ι` vanishes on two vectors that have, at each
index, one of them with both coordinates zero. -/
theorem stdSymplecticForm_eq_zero_of_forall {v w : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι}
    (h : ∀ k, v.1 k = 0 ∧ v.2 k = 0 ∨ w.1 k = 0 ∧ w.2 k = 0) : stdSymplecticForm v w = 0 := by
  rw [stdSymplecticForm_apply, PiLp.inner_apply, PiLp.inner_apply, ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun k _ ↦ ?_
  rcases h k with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2]

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
  have hv := (weightRotation_apply_eq_self_iff_apply _ v k).1
    ⟨congrArg (fun z ↦ z.1 k) hR, congrArg (fun z ↦ z.2 k) hR⟩
  by_contra hne
  -- The rotation angle `arg (χₖ g)` lies in `(-π, π]` and in `2πℤ`, so it is `0` and `χₖ g = 1`.
  obtain ⟨m, hm⟩ := hv (by tauto)
  have h1 := Complex.neg_pi_lt_arg (χ k g)
  have h2 := Complex.arg_le_pi (χ k g)
  rw [← hm] at h1 h2
  have hm0 : m = 0 := by
    have hlt : (m : ℝ) < (1 : ℤ) := by push_cast; nlinarith [Real.pi_pos]
    have hgt : ((-1 : ℤ) : ℝ) < m := by push_cast; nlinarith [Real.pi_pos]
    have := Int.cast_lt.mp hlt
    have := Int.cast_lt.mp hgt
    omega
  apply hg
  rw [← Circle.exp_arg (χ k g), ← hm, hm0]
  simp

end WeightCoordinates

namespace SmoothTwoForm.IsMomentMap

section Chart

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℝ 𝔤] {σ : SmoothTwoForm I' M}
  {a : InfinitesimalAction 𝔤 I' M} {μ : M → Module.Dual ℝ 𝔤}

/-- **The derivative of a moment map in a symplectic chart.** Let `μ` be a moment map of an
infinitesimal action `Z ↦ Z_M` for `σ`, and let `chart` be a partial diffeomorphism of `M` onto
an open subset of `V × V` that carries `σ` at `y` to the standard symplectic form `ω₀`. Then the
derivative at `chart y` of the component `μ^Z` read in the chart is `ω₀(dchart_y (Z_M(y)), ·)`. -/
theorem fderiv_comp_symm_apply (h : σ.IsMomentMap a μ)
    (chart : PartialDiffeomorph I' 𝓘(ℝ, V × V) M (V × V) ∞) {y : M} (hy : y ∈ chart.source)
    (hform : ∀ v w : TangentSpace I' y,
      σ.eval₂ y v w = stdSymplecticForm (mvfderiv I' chart y v) (mvfderiv I' chart y w))
    (Z : 𝔤) (w : V × V) :
    fderiv ℝ (fun z ↦ μ (chart.symm z) Z) (chart y) w =
      stdSymplecticForm (mfderiv I' 𝓘(ℝ, V × V) chart y (a Z y)) w := by
  obtain ⟨z, hz, rfl⟩ : ∃ z ∈ chart.target, chart.symm z = y :=
    ⟨chart y, chart.map_source hy, chart.left_inv hy⟩
  -- Rewriting `chart (chart.symm z) = z` everywhere would leave a vector of the tangent space at
  -- `chart (chart.symm z)` where one at `z` is expected, so only the left side is rewritten.
  conv_lhs => erw [chart.right_inv hz]
  set u := mfderiv 𝓘(ℝ, V × V) I' chart.symm z w
  have h1 := (mvfderiv_eq_fderiv_apply (𝕜 := ℝ) ((fun x ↦ μ x Z) ∘ chart.symm) z w).symm
  have h2 := mvfderiv_apply_eq_mfderiv_apply (𝕜 := ℝ) (I := 𝓘(ℝ, V × V))
    ((fun x ↦ μ x Z) ∘ chart.symm) z w
  have h3 := mfderiv_comp_apply_of_eq z (h.mdifferentiableAt Z _)
    (chart.symm.mdifferentiableAt (by simp) hz) rfl w
  have h4 := mvfderiv_apply_eq_mfderiv_apply (𝕜 := ℝ) (I := I') (fun x ↦ μ x Z) (chart.symm z) u
  have h5 := h.eval₂_apply Z (chart.symm z) u
  have h6 := hform (a Z (chart.symm z)) u
  have h7 : mvfderiv I' chart (chart.symm z) u = w := by
    rw [mvfderiv_apply_eq_mfderiv_apply]
    exact chart.mfderiv_apply_mfderiv_symm_apply (by simp) hz w
  rw [h7, mvfderiv_apply_eq_mfderiv_apply] at h6
  exact h1.trans (h2.trans (h3.trans (h4.symm.trans (h5.symm.trans h6))))

end Chart

end SmoothTwoForm.IsMomentMap

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
    let 𝔤ₓ : Submodule ℝ E := ((InfinitesimalAction.fundamental I G I' M).isotropy x).toSubmodule
    let K : Subgroup G := (Subgroup.connectedComponentOfOne (MulAction.stabilizer G x)).map
      (MulAction.stabilizer G x).subtype
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
          (fundamentalVectorField I' (show GroupLieAlgebra I G from (ξ : E)) y) =
            weightInfinitesimalAction α (chart y) ξ) ∧
      ∀ y ∈ chart.source, ∀ ξ : 𝔤ₓ,
        μ y (ξ : E) = μ x (ξ : E) + weightMomentMap α (chart y) ξ := by
  intro 𝔤ₓ K
  set S := MulAction.stabilizer G x
  have hS : IsClosed (S : Set G) := isClosed_stabilizer
    (ContMDiffSMul.contMDiff_smul_const (I := I) (I' := I') (n := ∞) x).continuous
  refine (Lie.isTorus_map_connectedComponentOfOne (S := S) hS.isCompact).elim (I := I)
    fun d ↦ ?_
  intro _ _ _ _ _ _ _
  let F := (Lie.lieSubalgebraOfSubgroup (I := I) K).toSubmodule
  let _ : ContMDiffSMul 𝓘(ℝ, F) I' ∞ K M := d.contMDiffSMul
  have hφ : MDifferentiableAt 𝓘(ℝ, F) I K.subtype 1 :=
    d.contMDiff_subtypeVal.mdifferentiableAt (by simp)
  have hK := h.comp_monoidHom K.subtype hφ fun _ _ ↦ rfl
  obtain ⟨n, χ, α, chart, r, hα, -, hx, h0, hr, htarget, hequiv, hform, hgen, hμ⟩ :=
    hK.exists_weightModelChart hσ (fun g ↦ hG g) (p := x)
      fun g ↦ Subgroup.map_subtype_le _ g.property
  -- The differential of the inclusion `K → G` identifies the Lie algebra of `K` with `𝔤ₓ`, which
  -- the statement reads as a submodule of `E`, the model of `GroupLieAlgebra I G`.
  let e : GroupLieAlgebra 𝓘(ℝ, F) K ≃ₗ[ℝ] 𝔤ₓ := d.groupLieAlgebraEquivIsotropy (I' := I')
  have he (ξ : 𝔤ₓ) : K.subtype.groupLieAlgebraMap 𝓘(ℝ, F) I (e.symm ξ) = (ξ : E) :=
    d.groupLieAlgebraMap_subtype_groupLieAlgebraEquivIsotropy_symm ξ
  -- The weights `α k`, functionals on the model `F` of `K`, read on its Lie algebra.
  let β (k : Fin n) : Module.Dual ℝ (GroupLieAlgebra 𝓘(ℝ, F) K) := (α k : F →ₗ[ℝ] ℝ)
  have hβ (k : Fin n) (η : GroupLieAlgebra 𝓘(ℝ, F) K) : β k η = α k η :=
    congrFun (ContinuousLinearMap.coe_coe (α k)) η
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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
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
  have : LieGroup I 1 G := LieGroup.of_le ENat.LEInfty.out
  have : ContMDiffSMul I I' 1 G M := ContMDiffSMul.of_le (M := M) ENat.LEInfty.out
  rw [h.fderiv_comp_symm_apply chart hx hform, InfinitesimalAction.fundamental_apply]
  refine stdSymplecticForm_eq_zero_of_forall fun k ↦ ?_
  by_cases hk : χ k = 1
  · exact Or.inr (hw k hk)
  · exact Or.inl (mfderiv_fundamentalVectorField_apply_eq_zero_of_ne_one
      (chart.mdifferentiableAt (by simp) hx) hK hχ ξ hk)

/-- **The derivative of the transverse part of the moment map is onto from the weight-zero
coordinates.** In the setting of `fderiv_comp_symm_apply_eq_zero`, let `𝔮` be a subspace of the
Lie algebra of `G` that meets the isotropy algebra `𝔤ₓ = {ξ | ξ_M(x) = 0}` only in `0`, for
instance a linear complement of it. Then every linear form `φ` on `𝔮` is
`ξ ↦ d(μ^ξ ∘ chart⁻¹)_{chart x} w` for some vector `w` whose coordinates vanish at each index `k`
with `χₖ ≠ 1`. -/
theorem exists_fderiv_comp_symm_apply_eq
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
  have : LieGroup I 1 G := LieGroup.of_le ENat.LEInfty.out
  have : ContMDiffSMul I I' 1 G M := ContMDiffSMul.of_le (M := M) ENat.LEInfty.out
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
  -- The pairing `(ξ, w) ↦ ω₀(D (ξ_M x), w)` on `𝔮 × W` is injective in `ξ`: take `w = J₀ (v ξ)`.
  let B : 𝔮 →ₗ[ℝ] W →ₗ[ℝ] ℝ :=
    (stdSymplecticForm (V := EuclideanSpace ℝ ι)).toBilinForm.compl₁₂ (v ∘ₗ 𝔮.subtype) W.subtype
  have hB (ξ : 𝔮) (w : W) : B ξ w = stdSymplecticForm (v ξ) w := rfl
  have hBinj : Function.Injective B := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro ξ hξ
    have hJ : AlmostComplexStructure.product _ (v ξ) ∈ W := fun k hk ↦ by
      simp [(hvW ξ k hk).1, (hvW ξ k hk).2]
    have h0 := LinearMap.congr_fun (LinearMap.mem_ker.1 hξ) ⟨_, hJ⟩
    rw [LinearMap.zero_apply, hB, stdSymplecticForm_apply_product_self] at h0
    have hz := (add_eq_zero_iff_of_nonneg real_inner_self_nonneg real_inner_self_nonneg).1 h0
    have hv0 : v ξ = 0 := Prod.ext (inner_self_eq_zero.1 hz.1) (inner_self_eq_zero.1 hz.2)
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

end WeightChart

end TauCeti.SmoothTwoForm.IsMomentMap
