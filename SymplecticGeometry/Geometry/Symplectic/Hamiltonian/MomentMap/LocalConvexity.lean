/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.WeightModel.NormalForm
import SymplecticGeometry.Geometry.Lie.Exponential.CommutativeGroup.Character
import SymplecticGeometry.Geometry.Lie.Subgroup.IdentityComponent
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

## References

* [C. Bjorndahl and Y. Karshon, *Revisiting Tietze–Nakajima: local and global convexity for
  maps*][BjorndahlKarshon2010], Proposition 29.
-/

public section

noncomputable section

open scoped ContDiff Manifold

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
