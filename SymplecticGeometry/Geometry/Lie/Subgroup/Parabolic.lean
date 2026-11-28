/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Lie.Complexification
public import TauCeti.Geometry.Lie.Adjoint.Exponential.Formula
import SymplecticGeometry.Geometry.Lie.Adjoint.Eigenvector
import TauCeti.Analysis.InnerProductSpace.Spectral.Relative
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
`Gc` when `G` is compact. From this it proves the decomposition `Gc = P(ξ) G` for compact `G`.

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
  `Real.exp (t * μ)`, by `TauCeti.Lie.tangentAd_mulInvariantExp_of_lie_eq_smul`, so the
  eigenvectors with `μ ≤ 0` lie in `C.parabolicSubspace ξ`.
* `SymplecticGeometry.LieComplexification.parabolicSubspace_sup_range_lieMap`: for compact `G`,
  `C.parabolicSubspace ξ ⊔ range C.lieMap = ⊤`. The operator `ad (cplx (lieMap ξ))` is
  self-adjoint for the form `complexifyForm B` of an invariant inner product `B`, so Tau Ceti's
  `LinearMap.IsSelfAdjoint.iSup_eigenspace_eq_top` spans the Lie algebra by its eigenspaces;
  `conj` exchanges the eigenvalues `μ` and `-μ`, and `x + conj x = 2 • lieMap (re x)`
  (`self_add_conj`).
* `SymplecticGeometry.LieComplexification.parabolic_mul_range_toHom_mem_nhds_one`: for compact
  `G`, the set `C.parabolic ξ * Set.range C.toHom` is a neighbourhood of `1`. In the chart
  `extChartAt IC 1`, the map `(x, y) ↦ exp x * C.toHom (exp y)` on
  `C.parabolicSubspace ξ × E` has derivative `(x, y) ↦ x + C.lieMap y` at `0`, which is onto by
  `parabolicSubspace_sup_range_lieMap`, so Mathlib's `HasStrictFDerivAt.map_nhds_eq_of_surj`
  applies.
* `SymplecticGeometry.LieComplexification.parabolic_mul_range_toHom_eq_univ`: for compact `G`,
  `Gc = C.parabolic ξ * Set.range C.toHom` ([GeorgoulasRobbinSalamon2021], Theorem D.3), since
  that set is open, closed (by `IsClosed.mul_right_of_isCompact`) and contains every curve
  `t ↦ C.polar (t • η, u)`; its two forms `exists_mem_parabolic_mul_toHom` and
  `exists_toHom_mul_mem_parabolic` write every `g` as `q * C.toHom u` and as `C.toHom u * q`.

## References

* [V. Georgoulas, J. W. Robbin and D. A. Salamon, *The Moment-Weight Inequality and the
  Hilbert–Mumford Criterion*][GeorgoulasRobbinSalamon2021], arXiv v2, Appendices D and E.
-/

public section

noncomputable section

open Filter Topology Manifold TauCeti
open scoped Pointwise
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
  rw [C.expI_smul, Lie.tangentAd_mulInvariantExp_of_lie_eq_smul (by rw [smul_lie, hx, smul_smul])]

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
    rw [← C.self_add_conj]
    abel
  rcases le_total μ 0 with hμ | hμ
  · exact Submodule.mem_sup_left (C.mem_parabolicSubspace_of_lie_eq_smul hx hμ)
  · rw [hsplit]
    exact Submodule.add_mem _
      (Submodule.mem_sup_left (Submodule.neg_mem _
        (C.mem_parabolicSubspace_of_lie_eq_smul hconj (neg_nonpos.2 hμ))))
      (Submodule.mem_sup_right (Submodule.smul_mem _ _ (LinearMap.mem_range_self _ _)))

omit [FiniteDimensional ℝ EC] in
/-- For a compact group `G` with finite-dimensional Lie algebra, the products `q * C.toHom u` of
an element `q` of the parabolic subgroup of `ξ` and an element of the image of `G` form a
neighbourhood of `1`. -/
theorem parabolic_mul_range_toHom_mem_nhds_one [FiniteDimensional ℝ E] [CompactSpace G]
    (ξ : GroupLieAlgebra I G) :
    (C.parabolic ξ : Set Gc) * Set.range C.toHom ∈ 𝓝 (1 : Gc) := by
  have := C.finiteDimensional
  have : T2Space G := I.t2Space_of_lieGroup ∞
  have : BoundarylessManifold I G := ContMDiffMul.boundarylessManifold
  let P : Submodule ℝ EC := C.parabolicSubspace ξ
  let g : P × E → Gc := fun p ↦ mulInvariantExp (I := IC) (G := Gc) (p.1 : EC) *
    C.toHom (mulInvariantExp (I := I) (G := G) p.2)
  let φ := extChartAt IC (1 : Gc)
  -- `mulInvariantExp_zero` at the zeros of the model spaces, which are those of the Lie
  -- algebras after unfolding `TangentSpace`.
  have he : mulInvariantExp (I := IC) (G := Gc) (0 : EC) = 1 := mulInvariantExp_zero
  have he' : mulInvariantExp (I := I) (G := G) (0 : E) = 1 := mulInvariantExp_zero
  have hg0 : g 0 = 1 := by
    simp only [g, Prod.fst_zero, Prod.snd_zero, Submodule.coe_zero, he, he', map_one, mul_one]
  have hg : ContMDiff 𝓘(ℝ, P × E) IC ∞ g := by
    refine ContMDiff.mul ?_ ?_
    · exact (contMDiff_mulInvariantExp (I := IC) (G := Gc)).comp
        (P.subtypeL.comp (ContinuousLinearMap.fst ℝ P E)).contDiff.contMDiff
    · exact C.toHom.contMDiff_toFun.comp ((contMDiff_mulInvariantExp (I := I) (G := G)).comp
        (ContinuousLinearMap.snd ℝ P E).contDiff.contMDiff)
  have hF : ContDiffAt ℝ ∞ (φ ∘ g) 0 := by
    have h := (contMDiffAt_iff_target_of_mem_source (x := 0) (y := (1 : Gc))
      (by rw [hg0]; exact mem_chart_source HC 1)).1 (hg 0)
    exact contMDiffAt_iff_contDiffAt.1 h.2
  set L := fderiv ℝ (φ ∘ g) 0
  have hL : HasFDerivAt (φ ∘ g) L 0 := (hF.differentiableAt (by simp)).hasFDerivAt
  have hexp := hasFDerivAt_extChartAt_mulInvariantExp_zero (I := IC) (G := Gc)
  have h₁ (x : P) : L (x, 0) = x := by
    have h : HasFDerivAt (fun x : P ↦ φ (mulInvariantExp (I := IC) (G := Gc) (x : EC)))
        (L.comp (ContinuousLinearMap.inl ℝ P E)) 0 := by
      refine (hL.comp (0 : P) (ContinuousLinearMap.inl ℝ P E).hasFDerivAt).congr_of_eventuallyEq
        (Eventually.of_forall fun x ↦ ?_)
      simp only [Function.comp_apply, g, ContinuousLinearMap.inl_apply, he', map_one, mul_one]
    have h' := hexp.comp (0 : P) P.subtypeL.hasFDerivAt
    exact congrArg (· x) (h.unique h')
  have h₂ (y : E) : L (0, y) = C.lieMap y := by
    let l : E →L[ℝ] EC := LinearMap.toContinuousLinearMap C.lieMap.toLinearMap
    have h : HasFDerivAt (fun y : E ↦ φ (mulInvariantExp (I := IC) (G := Gc) (l y)))
        (L.comp (ContinuousLinearMap.inr ℝ P E)) 0 := by
      refine (hL.comp (0 : E) (ContinuousLinearMap.inr ℝ P E).hasFDerivAt).congr_of_eventuallyEq
        (Eventually.of_forall fun y ↦ ?_)
      simp only [Function.comp_apply, g, Submodule.coe_zero, he, one_mul]
      exact congrArg φ (C.toHom_mulInvariantExp y).symm
    have h' := (map_zero l ▸ hexp).comp (0 : E) l.hasFDerivAt
    exact congrArg (· y) (h.unique h')
  have hrange : L.range = ⊤ := by
    refine eq_top_iff.2 ((C.parabolicSubspace_sup_range_lieMap ξ).symm.le.trans
      (sup_le (fun x hx ↦ ⟨(⟨x, hx⟩, 0), h₁ _⟩) ?_))
    rintro _ ⟨y, rfl⟩
    exact ⟨(0, y), h₂ y⟩
  have hmap := (hF.hasStrictFDerivAt hL (by simp)).map_nhds_eq_of_surj hrange
  have hU : g ⁻¹' φ.source ∈ 𝓝 (0 : P × E) :=
    hg.continuous.continuousAt.preimage_mem_nhds
      (by rw [hg0]; exact extChartAt_source_mem_nhds (I := IC) (1 : Gc))
  have himg : (φ ∘ g) '' (g ⁻¹' φ.source) ∈ 𝓝 (φ 1) := by
    rw [← hg0, ← Function.comp_apply (f := φ), ← hmap]
    exact image_mem_map hU
  refine mem_of_superset
    (inter_mem ((continuousAt_extChartAt (I := IC) (1 : Gc)).preimage_mem_nhds himg)
    (extChartAt_source_mem_nhds (I := IC) (1 : Gc))) ?_
  rintro h ⟨⟨p, hp, hph⟩, hh⟩
  rw [← φ.injOn hp hh hph]
  exact Set.mul_mem_mul (C.mulInvariantExp_mem_parabolic p.1.property) ⟨_, rfl⟩

omit [FiniteDimensional ℝ EC] in
/-- For a compact group `G` with finite-dimensional Lie algebra, every element of `Gc` is a
product `q * C.toHom u` of an element `q` of the parabolic subgroup of `ξ` and an element of the
image of `G`. -/
theorem parabolic_mul_range_toHom_eq_univ [FiniteDimensional ℝ E] [CompactSpace G]
    (ξ : GroupLieAlgebra I G) :
    (C.parabolic ξ : Set Gc) * Set.range C.toHom = Set.univ := by
  have := topologicalGroup_of_lieGroup IC ∞ (G := Gc)
  set S := (C.parabolic ξ : Set Gc) * Set.range C.toHom
  have hV := C.parabolic_mul_range_toHom_mem_nhds_one ξ
  have hmem : ∀ q ∈ C.parabolic ξ, ∀ s ∈ S, ∀ u, q * s * C.toHom u ∈ S := by
    rintro q hq _ ⟨p, hp, _, ⟨v, rfl⟩, rfl⟩ u
    exact ⟨q * p, mul_mem hq hp, C.toHom (v * u), ⟨_, rfl⟩, by rw [map_mul]; group⟩
  have hopen : IsOpen S := by
    refine isOpen_iff_mem_nhds.2 ?_
    rintro _ ⟨q, hq, _, ⟨u, rfl⟩, rfl⟩
    have hc : Continuous fun h : Gc ↦ q⁻¹ * h * (C.toHom u)⁻¹ := by fun_prop
    have h1 : q⁻¹ * (q * C.toHom u) * (C.toHom u)⁻¹ = 1 := by group
    refine mem_of_superset (hc.continuousAt.preimage_mem_nhds (h1 ▸ hV)) fun h hh ↦ ?_
    simpa only [mul_assoc, mul_inv_cancel_left, inv_mul_cancel, mul_one] using hmem q hq _ hh u
  have hsub : closure (C.parabolic ξ : Set Gc) * Set.range C.toHom ⊆ S := by
    rintro _ ⟨k, hk, _, ⟨u, rfl⟩, rfl⟩
    have hc : Continuous fun p : Gc ↦ p⁻¹ * k := by fun_prop
    have hN : (fun p : Gc ↦ p⁻¹ * k) ⁻¹' S ∈ 𝓝 k :=
      hc.continuousAt.preimage_mem_nhds (by rwa [inv_mul_cancel])
    obtain ⟨p, hpS, hp⟩ := mem_closure_iff_nhds.1 hk _ hN
    simpa only [mul_inv_cancel_left] using hmem p hp _ hpS u
  have hclosed : IsClosed S := by
    rw [← hsub.antisymm (Set.mul_subset_mul_right subset_closure)]
    exact isClosed_closure.mul_right_of_isCompact
      (isCompact_range C.toHom.contMDiff_toFun.continuous)
  refine Set.eq_univ_of_forall fun g ↦ ?_
  -- `S` is clopen and contains `C.toHom u`, so it contains the curve
  -- `t ↦ C.polar (t • η, u)` from `C.toHom u` to `g = C.polar (η, u)`.
  have hc : Continuous fun t : ℝ ↦ C.polar (t • (C.polar.symm g).1, (C.polar.symm g).2) :=
    C.polar.continuous.comp (by fun_prop)
  have h0 : (0 : ℝ) ∈ (fun t : ℝ ↦ C.polar (t • (C.polar.symm g).1, (C.polar.symm g).2)) ⁻¹' S := by
    rw [Set.mem_preimage, zero_smul, C.polar_zero_apply]
    exact ⟨1, one_mem _, _, ⟨_, rfl⟩, one_mul _⟩
  have h1 : (1 : ℝ) ∈ _ := (IsClopen.preimage ⟨hclosed, hopen⟩ hc).eq_univ ⟨0, h0⟩ ▸ Set.mem_univ 1
  simpa only [Set.mem_preimage, one_smul, Prod.mk.eta, Diffeomorph.apply_symm_apply] using h1

omit [FiniteDimensional ℝ EC] in
/-- For a compact group `G` with finite-dimensional Lie algebra, every `g : Gc` is
`q * C.toHom u` with `q` in the parabolic subgroup of `ξ` and `u : G`. -/
theorem exists_mem_parabolic_mul_toHom [FiniteDimensional ℝ E] [CompactSpace G]
    (ξ : GroupLieAlgebra I G) (g : Gc) : ∃ q ∈ C.parabolic ξ, ∃ u, g = q * C.toHom u := by
  have hg : g ∈ (C.parabolic ξ : Set Gc) * Set.range C.toHom := by
    rw [C.parabolic_mul_range_toHom_eq_univ ξ]
    exact Set.mem_univ g
  obtain ⟨q, hq, _, ⟨u, rfl⟩, h⟩ := hg
  exact ⟨q, hq, u, h.symm⟩

omit [FiniteDimensional ℝ EC] in
/-- For a compact group `G` with finite-dimensional Lie algebra, every `g : Gc` is
`C.toHom u * q` with `u : G` and `q` in the parabolic subgroup of `ξ`. -/
theorem exists_toHom_mul_mem_parabolic [FiniteDimensional ℝ E] [CompactSpace G]
    (ξ : GroupLieAlgebra I G) (g : Gc) : ∃ u, ∃ q ∈ C.parabolic ξ, g = C.toHom u * q := by
  obtain ⟨q, hq, u, h⟩ := C.exists_mem_parabolic_mul_toHom ξ g⁻¹
  exact ⟨u⁻¹, q⁻¹, inv_mem hq, by rw [map_inv, ← mul_inv_rev, ← h, inv_inv]⟩

end LieComplexification

end SymplecticGeometry

end
