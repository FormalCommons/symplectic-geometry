/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Lie.Complexification
public import TauCeti.Geometry.Lie.Adjoint.Exponential.Formula
import TauCeti.Analysis.InnerProductSpace.Spectral.Relative
import TauCeti.Analysis.Normed.Operator.Exponential
import TauCeti.Geometry.Lie.Adjoint.Exponential.Basic
import TauCeti.Geometry.Lie.Adjoint.InvariantForm
import TauCeti.Geometry.Lie.Exponential.Smoothness

/-!
# The parabolic subgroup of a direction

Let `C : LieComplexification I G IC Gc` be a complexification and `ξ` an element of the Lie
algebra of `G`. Following Georgoulas–Robbin–Salamon, the parabolic subgroup `P(ξ)` is the set of
`g : Gc` whose conjugates `exp (i t ξ) g exp (-i t ξ)` converge as `t → ∞`. This file defines it
together with its limit map and the corresponding subspace of the Lie algebra of `Gc`, gives their
API, and shows that the subspace and the image of the Lie algebra of `G` span the Lie algebra of
`Gc` when `G` is compact.

## Main definitions

* `SymplecticGeometry.LieComplexification.parabolic`: the subgroup `C.parabolic ξ` of the `g` for
  which `t ↦ C.expI (t • ξ) * g * C.expI (-(t • ξ))` converges as `t → ∞`.
* `SymplecticGeometry.LieComplexification.parabolicLimit`: the homomorphism
  `C.parabolic ξ →* Gc` that sends `g` to that limit.
* `SymplecticGeometry.LieComplexification.parabolicSubspace`: the submodule of the Lie algebra of
  `Gc` of the `x` for which `t ↦ Ad (C.expI (t • ξ)) x` converges as `t → ∞`.

## Main results

* `SymplecticGeometry.LieComplexification.parabolic_zero`: `C.parabolic 0 = ⊤`.
* `SymplecticGeometry.LieComplexification.parabolic_eq_top`,
  `SymplecticGeometry.LieComplexification.circle_parabolic`: if `Gc` is commutative, as in the
  circle example, every parabolic subgroup is `⊤`.
* `SymplecticGeometry.LieComplexification.tendsto_parabolicLimit`: the conjugates converge to
  `C.parabolicLimit ξ g`, and `parabolicLimit_eq_of_tendsto` identifies the limit.
* `SymplecticGeometry.LieComplexification.expI_mul_parabolicLimit_mul_expI_neg`: the limit
  commutes with every `C.expI (s • ξ)`.
* `SymplecticGeometry.LieComplexification.expI_smul_mem_parabolic`,
  `SymplecticGeometry.LieComplexification.parabolicLimit_expI_smul`: `C.expI (s • ξ)` lies in
  `C.parabolic ξ` and is its own limit.
* `SymplecticGeometry.LieComplexification.tangentAd_expI_smul`: `Ad (C.expI (t • ξ))` is the
  operator exponential of `t • ad (cplx (lieMap ξ))`, from Tau Ceti's
  `TauCeti.Lie.tangentAd_mulInvariantExp_apply`.
* `SymplecticGeometry.LieComplexification.mulInvariantExp_mem_parabolic`: the exponential maps
  `C.parabolicSubspace ξ` into `C.parabolic ξ`, by Tau Ceti's `TauCeti.Lie.conj_mulInvariantExp`
  and the continuity of the exponential.
* `SymplecticGeometry.LieComplexification.tangentAd_expI_smul_of_lie_eq_smul`,
  `SymplecticGeometry.LieComplexification.mem_parabolicSubspace_of_lie_eq_smul`: on an eigenvector
  of `ad (cplx (lieMap ξ))` with eigenvalue `μ`, `Ad (C.expI (t • ξ))` is multiplication by
  `Real.exp (t * μ)`, so the eigenvectors with `μ ≤ 0` lie in `C.parabolicSubspace ξ`.
* `SymplecticGeometry.LieComplexification.parabolicSubspace_sup_range_lieMap`: for compact `G`,
  `C.parabolicSubspace ξ ⊔ range C.lieMap = ⊤`. The operator `ad (cplx (lieMap ξ))` is
  self-adjoint for the form `complexifyForm B` of an invariant inner product `B`, so Tau Ceti's
  `LinearMap.IsSelfAdjoint.iSup_eigenspace_eq_top` spans the Lie algebra by its eigenspaces;
  `conj` exchanges the eigenvalues `μ` and `-μ`, and `x = -conj x + 2 • lieMap (re x)`.

## References

* [V. Georgoulas, J. W. Robbin and D. A. Salamon, *The Moment-Weight Inequality and the
  Hilbert–Mumford Criterion*][GeorgoulasRobbinSalamon2021], arXiv v2, Appendices D and E.
-/

public section

noncomputable section

open Filter Topology Manifold TauCeti
open scoped Manifold ContDiff

namespace SymplecticGeometry

namespace LieComplexification

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {EC : Type*} [NormedAddCommGroup EC] [NormedSpace ℝ EC] [CompleteSpace EC]
  {HC : Type*} [TopologicalSpace HC] {IC : ModelWithCorners ℝ EC HC}
  {Gc : Type*} [TopologicalSpace Gc] [ChartedSpace HC Gc] [Group Gc] [LieGroup IC ∞ Gc]
  [T2Space Gc] [BoundarylessManifold IC Gc]
  (C : LieComplexification I G IC Gc)

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

/-- The parabolic subgroup of `ξ`: the `g : Gc` for which the conjugates
`C.expI (t • ξ) * g * C.expI (-(t • ξ))` converge as `t → ∞`. -/
def parabolic (ξ : GroupLieAlgebra I G) : Subgroup Gc :=
  have := topologicalGroup_of_lieGroup IC ∞ (G := Gc)
  { carrier := {g | ∃ a, Tendsto (fun t : ℝ ↦ C.expI (t • ξ) * g * C.expI (-(t • ξ))) atTop (𝓝 a)}
    mul_mem' := by
      rintro g h ⟨a, ha⟩ ⟨b, hb⟩
      refine ⟨a * b, (ha.mul hb).congr fun t ↦ ?_⟩
      rw [C.expI_neg]
      group
    one_mem' := ⟨1, tendsto_const_nhds.congr fun t ↦ by rw [C.expI_neg]; group⟩
    inv_mem' := by
      rintro g ⟨a, ha⟩
      refine ⟨a⁻¹, ha.inv.congr fun t ↦ ?_⟩
      rw [C.expI_neg]
      group }

theorem mem_parabolic_iff {ξ : GroupLieAlgebra I G} {g : Gc} :
    g ∈ C.parabolic ξ ↔
      ∃ a, Tendsto (fun t : ℝ ↦ C.expI (t • ξ) * g * C.expI (-(t • ξ))) atTop (𝓝 a) :=
  Iff.rfl

/-- Every element is parabolic for the direction `0`. -/
@[simp]
theorem parabolic_zero : C.parabolic (0 : GroupLieAlgebra I G) = ⊤ := by
  refine eq_top_iff.2 fun g _ ↦ C.mem_parabolic_iff.2 ⟨g, tendsto_const_nhds.congr fun t ↦ ?_⟩
  rw [smul_zero, neg_zero, C.expI_zero, one_mul, mul_one]

/-- If `Gc` is commutative, every element is parabolic for every direction. -/
theorem parabolic_eq_top [IsMulCommutative Gc] (ξ : GroupLieAlgebra I G) :
    C.parabolic ξ = ⊤ := by
  refine eq_top_iff.2 fun g _ ↦ C.mem_parabolic_iff.2 ⟨g, tendsto_const_nhds.congr fun t ↦ ?_⟩
  rw [C.expI_neg, mul_comm' (C.expI (t • ξ)), mul_inv_cancel_right]

/-- In the circle example, where `ℂˣ` is commutative, every direction has parabolic subgroup
`⊤`. -/
theorem circle_parabolic (ξ : GroupLieAlgebra (𝓡 1) Circle) : circle.parabolic ξ = ⊤ :=
  circle.parabolic_eq_top ξ

/-- `C.expI (s • ξ)` lies in the parabolic subgroup of `ξ`: its conjugates are constant. -/
theorem expI_smul_mem_parabolic (ξ : GroupLieAlgebra I G) (s : ℝ) :
    C.expI (s • ξ) ∈ C.parabolic ξ :=
  C.mem_parabolic_iff.2 ⟨C.expI (s • ξ), tendsto_const_nhds.congr fun t ↦ by
    rw [(C.commute_expI_smul ξ t s).eq, C.expI_neg, mul_inv_cancel_right]⟩

/-- The limit of the conjugates `C.expI (t • ξ) * g * C.expI (-(t • ξ))` of an element `g` of
the parabolic subgroup, as a homomorphism `C.parabolic ξ →* Gc`. -/
def parabolicLimit (ξ : GroupLieAlgebra I G) : C.parabolic ξ →* Gc :=
  have := topologicalGroup_of_lieGroup IC ∞ (G := Gc)
  { toFun := fun g ↦ limUnder atTop fun t : ℝ ↦ C.expI (t • ξ) * g * C.expI (-(t • ξ))
    map_one' := by
      refine tendsto_nhds_unique (tendsto_nhds_limUnder (C.mem_parabolic_iff.1 (one_mem _)))
        (tendsto_const_nhds.congr fun t ↦ ?_)
      rw [C.expI_neg, mul_one, mul_inv_cancel]
    map_mul' := fun g h ↦ by
      refine tendsto_nhds_unique (tendsto_nhds_limUnder (C.mem_parabolic_iff.1 (g * h).property))
        (((tendsto_nhds_limUnder (C.mem_parabolic_iff.1 g.property)).mul
          (tendsto_nhds_limUnder (C.mem_parabolic_iff.1 h.property))).congr fun t ↦ ?_)
      rw [Subgroup.coe_mul, C.expI_neg]
      group }

theorem parabolicLimit_apply (ξ : GroupLieAlgebra I G) (g : C.parabolic ξ) :
    C.parabolicLimit ξ g = limUnder atTop fun t : ℝ ↦ C.expI (t • ξ) * g * C.expI (-(t • ξ)) :=
  (rfl)

/-- The conjugates of an element `g` of the parabolic subgroup converge to
`C.parabolicLimit ξ g`. -/
theorem tendsto_parabolicLimit (ξ : GroupLieAlgebra I G) (g : C.parabolic ξ) :
    Tendsto (fun t : ℝ ↦ C.expI (t • ξ) * g * C.expI (-(t • ξ))) atTop
      (𝓝 (C.parabolicLimit ξ g)) := by
  rw [parabolicLimit_apply]
  exact tendsto_nhds_limUnder (C.mem_parabolic_iff.1 g.property)

/-- `C.parabolicLimit ξ g` is any limit of the conjugates of `g`. -/
theorem parabolicLimit_eq_of_tendsto {ξ : GroupLieAlgebra I G} (g : C.parabolic ξ) {a : Gc}
    (h : Tendsto (fun t : ℝ ↦ C.expI (t • ξ) * g * C.expI (-(t • ξ))) atTop (𝓝 a)) :
    C.parabolicLimit ξ g = a :=
  tendsto_nhds_unique (C.tendsto_parabolicLimit ξ g) h

/-- `C.expI (s • ξ)` is its own limit. -/
@[simp]
theorem parabolicLimit_expI_smul (ξ : GroupLieAlgebra I G) (s : ℝ) :
    C.parabolicLimit ξ ⟨C.expI (s • ξ), C.expI_smul_mem_parabolic ξ s⟩ = C.expI (s • ξ) :=
  C.parabolicLimit_eq_of_tendsto _ (tendsto_const_nhds.congr fun t ↦ by
    rw [(C.commute_expI_smul ξ t s).eq, C.expI_neg, mul_inv_cancel_right])

/-- The limit `C.parabolicLimit ξ g` commutes with every `C.expI (s • ξ)`: conjugating the
conjugates at time `t` by `C.expI (s • ξ)` gives those at time `s + t`. -/
theorem expI_mul_parabolicLimit_mul_expI_neg (ξ : GroupLieAlgebra I G) (s : ℝ)
    (g : C.parabolic ξ) :
    C.expI (s • ξ) * C.parabolicLimit ξ g * C.expI (-(s • ξ)) = C.parabolicLimit ξ g := by
  have := topologicalGroup_of_lieGroup IC ∞ (G := Gc)
  have h := C.tendsto_parabolicLimit ξ g
  have hc : Continuous fun a : Gc ↦ C.expI (s • ξ) * a * C.expI (-(s • ξ)) := by fun_prop
  refine tendsto_nhds_unique ((hc.tendsto _).comp h)
    ((h.comp (tendsto_atTop_add_const_left atTop s tendsto_id)).congr fun t ↦ ?_)
  simp only [Function.comp_apply, id, C.expI_neg, C.expI_add_smul, mul_inv_rev]
  group

/-- The parabolic subspace of `ξ`: the `x` in the Lie algebra of `Gc` for which
`Ad (C.expI (t • ξ)) x` converges as `t → ∞`. -/
def parabolicSubspace (ξ : GroupLieAlgebra I G) : Submodule ℝ (GroupLieAlgebra IC Gc) where
  carrier := {x | ∃ y, Tendsto (fun t : ℝ ↦ Lie.tangentAd (I := IC) (C.expI (t • ξ)) x) atTop
    (𝓝 y)}
  add_mem' := by
    rintro x y ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨a + b, (ha.add hb).congr fun t ↦ (map_add _ x y).symm⟩
  zero_mem' := ⟨0, tendsto_const_nhds.congr fun t ↦ (map_zero _).symm⟩
  smul_mem' := by
    rintro c x ⟨a, ha⟩
    exact ⟨c • a, (ha.const_smul c).congr fun t ↦ (map_smul _ c x).symm⟩

theorem mem_parabolicSubspace_iff {ξ : GroupLieAlgebra I G} {x : GroupLieAlgebra IC Gc} :
    x ∈ C.parabolicSubspace ξ ↔
      ∃ y, Tendsto (fun t : ℝ ↦ Lie.tangentAd (I := IC) (C.expI (t • ξ)) x) atTop (𝓝 y) :=
  Iff.rfl

variable [FiniteDimensional ℝ EC]

/-- `Ad (C.expI (t • ξ))` is the operator exponential of `t • A`, where `A` is `ad` of
`cplx (lieMap ξ)`, read as an operator on the model space `EC`. -/
theorem tangentAd_expI_smul (ξ : GroupLieAlgebra I G) (t : ℝ) (x : GroupLieAlgebra IC Gc) :
    (show EC from Lie.tangentAd (I := IC) (C.expI (t • ξ)) x) =
      NormedSpace.exp (t • (Module.End.toContinuousLinearMap EC)
        ((groupLieAlgebraEquivModelVectorSpace (I := IC) (G := Gc)).conj
          (LieAlgebra.ad ℝ (GroupLieAlgebra IC Gc) (C.cplx (C.lieMap ξ)))))
        (show EC from x) := by
  have h := Lie.tangentAd_mulInvariantExp_apply (I := IC) (G := Gc)
    (t • C.cplx (C.lieMap ξ)) x
  dsimp only at h
  rw [C.expI_smul, h, map_smul, map_smul, map_smul]

/-- The exponential maps the parabolic subspace of `ξ` into the parabolic subgroup: the
conjugates of `exp x` are the exponentials of `Ad (C.expI (t • ξ)) x`. -/
theorem mulInvariantExp_mem_parabolic {ξ : GroupLieAlgebra I G} {x : GroupLieAlgebra IC Gc}
    (hx : x ∈ C.parabolicSubspace ξ) :
    mulInvariantExp x ∈ C.parabolic ξ := by
  obtain ⟨y, hy⟩ := C.mem_parabolicSubspace_iff.1 hx
  have hc : Continuous (mulInvariantExp : GroupLieAlgebra IC Gc → Gc) :=
    (contMDiff_mulInvariantExp (I := IC) (G := Gc)).continuous
  refine C.mem_parabolic_iff.2 ⟨mulInvariantExp y, ((hc.tendsto y).comp hy).congr fun t ↦ ?_⟩
  rw [Function.comp_apply, C.expI_neg, Lie.conj_mulInvariantExp]

/-- On an eigenvector `x` of `ad (cplx (lieMap ξ))` with eigenvalue `μ`, the operator
`Ad (C.expI (t • ξ))` acts as multiplication by `Real.exp (t * μ)`. -/
theorem tangentAd_expI_smul_of_lie_eq_smul {ξ : GroupLieAlgebra I G} {x : GroupLieAlgebra IC Gc}
    {μ : ℝ} (hx : ⁅C.cplx (C.lieMap ξ), x⁆ = μ • x) (t : ℝ) :
    Lie.tangentAd (I := IC) (C.expI (t • ξ)) x = Real.exp (t * μ) • x := by
  have h := C.tangentAd_expI_smul ξ t x
  rw [ContinuousLinearMap.exp_apply_of_apply_eq_smul _ (μ := t * μ) ?_,
    ← Real.exp_eq_exp_ℝ] at h
  · exact h
  · rw [smul_apply, mul_smul]
    exact congrArg (t • ·) hx

/-- An eigenvector of `ad (cplx (lieMap ξ))` with eigenvalue `μ ≤ 0` lies in the parabolic
subspace of `ξ`. -/
theorem mem_parabolicSubspace_of_lie_eq_smul {ξ : GroupLieAlgebra I G}
    {x : GroupLieAlgebra IC Gc} {μ : ℝ} (hx : ⁅C.cplx (C.lieMap ξ), x⁆ = μ • x) (hμ : μ ≤ 0) :
    x ∈ C.parabolicSubspace ξ := by
  have hexp : ∃ c, Tendsto (fun t : ℝ ↦ Real.exp (t * μ)) atTop (𝓝 c) := by
    rcases hμ.lt_or_eq with hμ | rfl
    · exact ⟨0, Real.tendsto_exp_atBot.comp (tendsto_id.atTop_mul_const_of_neg hμ)⟩
    · exact ⟨1, by simp⟩
  obtain ⟨c, hc⟩ := hexp
  exact C.mem_parabolicSubspace_iff.2 ⟨c • x, (hc.smul_const x).congr fun t ↦
    (C.tangentAd_expI_smul_of_lie_eq_smul hx t).symm⟩

omit [FiniteDimensional ℝ EC] in
/-- For a compact group `G` with finite-dimensional Lie algebra, the parabolic subspace of `ξ`
and the image of the Lie algebra of `G` together span the Lie algebra of `Gc`. -/
theorem parabolicSubspace_sup_range_lieMap [FiniteDimensional ℝ E] [CompactSpace G]
    (ξ : GroupLieAlgebra I G) :
    C.parabolicSubspace ξ ⊔ LinearMap.range C.lieMap.toLinearMap = ⊤ := by
  have := C.finiteDimensional
  have : T2Space G := I.t2Space_of_lieGroup ∞
  obtain ⟨b, -, hpos, hinv⟩ :=
    Lie.exists_isSymm_posDef_continuousBilinearMap_adjoint_invariant (I := I) (G := G)
  have htop := LinearMap.IsSelfAdjoint.iSup_eigenspace_eq_top
    (C.complexifyForm_apply_self_pos (B := b.toBilinForm) hpos)
    (C.isSelfAdjoint_ad_cplx_lieMap (Lie.lieInvariant_of_adjoint_invariant hinv) ξ)
  refine eq_top_iff.2 (htop ▸ iSup_le fun μ x hx ↦ ?_)
  have hx : ⁅C.cplx (C.lieMap ξ), x⁆ = μ • x := Module.End.mem_eigenspace_iff.1 hx
  have hconj : ⁅C.cplx (C.lieMap ξ), C.conj x⁆ = (-μ) • C.conj x := by
    rw [neg_smul, ← map_smul, ← hx, C.conj_lie_cplx_lieMap, neg_neg]
  have hsplit : x = -C.conj x + (2 : ℝ) • C.lieMap (C.re x) := by
    conv_lhs => rw [← C.lieMap_re_add_cplx_lieMap_im x]
    rw [conj_apply]
    module
  rcases le_total μ 0 with hμ | hμ
  · exact Submodule.mem_sup_left (C.mem_parabolicSubspace_of_lie_eq_smul hx hμ)
  · rw [hsplit]
    exact Submodule.add_mem _
      (Submodule.mem_sup_left (Submodule.neg_mem _
        (C.mem_parabolicSubspace_of_lie_eq_smul hconj (neg_nonpos.2 hμ))))
      (Submodule.mem_sup_right (Submodule.smul_mem _ _ (LinearMap.mem_range_self _ _)))

end LieComplexification

end SymplecticGeometry

end
