/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.GroupAction.OrbitTube

/-!
# The tube map of an orbit along a linear fibre

Let a Lie group `G` act smoothly on a manifold `M`, let `x : M` have stabilizer `H`, and let
`e` be a linearizing chart at `x` (`SymplecticGeometry.LinearizingChart`). Let `H` act on a
normed space `P`, and let `L : P →L[ℝ] T_x M` intertwine this action with the differentials:
`L (k • p) = dk_x (L p)` for `k ∈ H`. Typically `P` is the fibre of a local model and `L` a linear
identification of `P` with a complement of the orbit tangent space `𝔤 · x`.

The set of `p` with `L p` in the target of `e` is `H`-invariant, so `p ↦ e.symm (L p)` there and
`p ↦ x` elsewhere is an `H`-equivariant map `P → M`
(`SymplecticGeometry.LinearizingChart.linearSliceMap`). Its lift
`TauCeti.BalancedProduct.liftRightTranslation` to the balanced product `G ×_H P` is the map
`[g, p] ↦ g • e.symm (L p)` (`SymplecticGeometry.LinearizingChart.linearTubeMap`). For the manifold
structure `TauCeti.BalancedProduct.rightTranslationChartedSpace` on `G ×_H P`:

* it is `G`-equivariant and sends `[g, 0]` to `g • x`;
* it is smooth on the open `G`-invariant set `N` of classes `[g, p]` with `L p` in the target of
  `e` (`SymplecticGeometry.LinearizingChart.linearTubeDomain`), since its composite with the
  projection `π : G × P → G ×_H P`, a submersion, is `(g, p) ↦ g • e.symm (L p)` near each point
  over `N` (Tau Ceti's `IsSubmersionAt.contMDiffAt_comp_iff`);
* composed with `dπ` at `(1, 0)`, its differential at `[1, 0]` is `(ξ, p) ↦ ξ_M(x) + L p`.

This generalizes `SymplecticGeometry.LinearizingChart.SliceDomain.tubeMap`, the case of the
inclusion of a slice domain. Smoothness on the domain adapts the proof of Tau Ceti's
`TauCeti.BalancedProduct.contMDiff_liftRightTranslation` to an open set, and the differential
follows the proof of
`SymplecticGeometry.LinearizingChart.SliceDomain.mfderiv_tubeMap_mfderiv_quotientMk`.

## Main definitions

* `SymplecticGeometry.LinearizingChart.linearSliceMap`: the equivariant map `p ↦ e.symm (L p)`,
  extended by `x`.
* `SymplecticGeometry.LinearizingChart.linearTubeMap`: the map `[g, p] ↦ g • e.symm (L p)` out of
  `G ×_H P`.
* `SymplecticGeometry.LinearizingChart.linearTubeDomain`: the classes `[g, p]` with `L p` in the
  target of `e`.

## Main results

* `SymplecticGeometry.LinearizingChart.linearTubeMap_smul`,
  `SymplecticGeometry.LinearizingChart.linearTubeMap_mk_zero`: the map is `G`-equivariant and
  sends `[g, 0]` to `g • x`.
* `SymplecticGeometry.LinearizingChart.isOpen_linearTubeDomain`,
  `SymplecticGeometry.LinearizingChart.smul_mem_linearTubeDomain_iff`: the domain is open and
  `G`-invariant.
* `SymplecticGeometry.LinearizingChart.contMDiffOn_linearTubeMap`: the map is smooth on the
  domain.
* `SymplecticGeometry.LinearizingChart.mfderiv_linearTubeMap_mfderiv_quotientMk`: its differential
  at `[1, 0]`, composed with that of the projection, is `(ξ, p) ↦ ξ_M(x) + L p`.

## References

* [V. Guillemin and S. Sternberg, *Symplectic Techniques in Physics*][GuilleminSternberg1990],
  the tube `G ×_H V` around an orbit in the local normal form.
-/

public section

noncomputable section

open Function Set Manifold MulAction TauCeti Filter Topology
open scoped ContDiff Manifold

namespace SymplecticGeometry

namespace LinearizingChart

variable {G : Type*} [Group G] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [MulAction G M]
  {x : M} (e : LinearizingChart G I' x)
  {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [MulAction (stabilizer G x) P]
  {L : P →L[ℝ] E'}

/-- For a map `L` that intertwines the action of the stabilizer on `P` with the differentials,
`L (k • p)` lies in the target of a linearizing chart exactly when `L p` does. -/
theorem apply_smul_mem_target_iff
    (hL : ∀ (k : stabilizer G x) (p : P),
      L (k • p) = mfderiv I' I' (fun y : M ↦ (k : G) • y) x (L p))
    (k : stabilizer G x) (p : P) : L (k • p) ∈ e.chart.target ↔ L p ∈ e.chart.target := by
  refine ⟨fun h ↦ ?_, fun h ↦ hL k p ▸ e.mfderiv_smul_mem_target k.property h⟩
  have hk := hL k⁻¹ (k • p)
  rw [inv_smul_smul] at hk
  rw [hk]
  exact e.mfderiv_smul_mem_target k⁻¹.property h

open scoped Classical in
/-- The **slice map along a linear fibre** `P`, for a map `L : P → T_x M` that intertwines the
action of the stabilizer of `x` on `P` with the differentials: the map `p ↦ e.symm (L p)` where
`L p` lies in the target of `e`, and `p ↦ x` elsewhere. It is equivariant for the inclusion of the
stabilizer into `G`. -/
def linearSliceMap
    (hL : ∀ (k : stabilizer G x) (p : P),
      L (k • p) = mfderiv I' I' (fun y : M ↦ (k : G) • y) x (L p)) :
    P →ₑ[((↑) : stabilizer G x → G)] M where
  toFun p := if L p ∈ e.chart.target then e.chart.symm (L p) else x
  map_smul' k p := by
    by_cases h : L p ∈ e.chart.target
    · rw [ite_eq_left ((e.apply_smul_mem_target_iff hL k p).2 h), ite_eq_left h, hL,
        e.symm_mfderiv_smul k.property h]
    · rw [ite_eq_right (mt (e.apply_smul_mem_target_iff hL k p).1 h), ite_eq_right h]
      exact (mem_stabilizer_iff.1 k.property).symm

variable (hL : ∀ (k : stabilizer G x) (p : P),
  L (k • p) = mfderiv I' I' (fun y : M ↦ (k : G) • y) x (L p))

open scoped Classical in
theorem linearSliceMap_def (p : P) :
    e.linearSliceMap hL p = if L p ∈ e.chart.target then e.chart.symm (L p) else x :=
  (rfl)

/-- Where `L p` is in the target of `e`, the slice map along a linear fibre is `e.symm (L p)`. -/
theorem linearSliceMap_apply_of_mem {p : P} (hp : L p ∈ e.chart.target) :
    e.linearSliceMap hL p = e.chart.symm (L p) := by
  rw [linearSliceMap_def, ite_eq_left hp]

/-- Where `L p` is not in the target of `e`, the slice map along a linear fibre is `x`. -/
theorem linearSliceMap_apply_of_notMem {p : P} (hp : L p ∉ e.chart.target) :
    e.linearSliceMap hL p = x := by
  rw [linearSliceMap_def, ite_eq_right hp]

/-- The slice map along a linear fibre sends `0` to `x`. -/
@[simp]
theorem linearSliceMap_zero : e.linearSliceMap hL 0 = x := by
  rw [e.linearSliceMap_apply_of_mem hL (by rw [map_zero]; exact e.zero_mem_target), map_zero,
    e.symm_zero]

/-- The **tube map along a linear fibre** `P`: the map `[g, p] ↦ g • e.symm (L p)` out of the
balanced product `G ×_H P` over the stabilizer `H` of `x`, extended by `[g, p] ↦ g • x` where
`L p` is not in the target of `e`. -/
def linearTubeMap : BalancedProduct (stabilizer G x) (stabilizer G x).RightTranslation P → M :=
  BalancedProduct.liftRightTranslation (e.linearSliceMap hL)

theorem linearTubeMap_def :
    e.linearTubeMap hL = BalancedProduct.liftRightTranslation (e.linearSliceMap hL) :=
  (rfl)

/-- The tube map along a linear fibre sends `[g, p]` to `g` applied to the slice map at `p`. -/
@[simp]
theorem linearTubeMap_mk (g : G) (p : P) :
    e.linearTubeMap hL (BalancedProduct.mk _ ((stabilizer G x).toRightTranslation g) p) =
      g • e.linearSliceMap hL p := by
  rw [linearTubeMap_def, BalancedProduct.liftRightTranslation_mk]

/-- On its domain, the tube map along a linear fibre is `[g, p] ↦ g • e.symm (L p)`. -/
theorem linearTubeMap_mk_of_mem (g : G) {p : P} (hp : L p ∈ e.chart.target) :
    e.linearTubeMap hL (BalancedProduct.mk _ ((stabilizer G x).toRightTranslation g) p) =
      g • e.chart.symm (L p) := by
  rw [linearTubeMap_mk, e.linearSliceMap_apply_of_mem hL hp]

/-- The tube map along a linear fibre is `G`-equivariant. -/
@[simp]
theorem linearTubeMap_smul (g : G)
    (y : BalancedProduct (stabilizer G x) (stabilizer G x).RightTranslation P) :
    e.linearTubeMap hL (g • y) = g • e.linearTubeMap hL y :=
  BalancedProduct.liftRightTranslation_smul _ g y

/-- The tube map along a linear fibre sends the class `[g, 0]` to `g • x`. -/
theorem linearTubeMap_mk_zero (g : G) :
    e.linearTubeMap hL (BalancedProduct.mk _ ((stabilizer G x).toRightTranslation g) 0) =
      g • x := by
  rw [linearTubeMap_mk, linearSliceMap_zero]

/-! ### The domain of the tube map -/

variable (L) in
/-- The **domain of the tube map along a linear fibre**: the classes `[g, p]` of `G ×_H P` with
`L p` in the target of `e`. -/
def linearTubeDomain :
    Set (BalancedProduct (stabilizer G x) (stabilizer G x).RightTranslation P) :=
  (fun q : G × P ↦ BalancedProduct.mk _ ((stabilizer G x).toRightTranslation q.1) q.2) ''
    (univ ×ˢ (L ⁻¹' e.chart.target))

theorem linearTubeDomain_def :
    e.linearTubeDomain L =
      (fun q : G × P ↦ BalancedProduct.mk _ ((stabilizer G x).toRightTranslation q.1) q.2) ''
        (univ ×ˢ (L ⁻¹' e.chart.target)) :=
  (rfl)

include hL in
/-- A class `[g, p]` lies in the domain of the tube map exactly when `L p` lies in the target
of `e`. -/
theorem mk_mem_linearTubeDomain_iff {g : G} {p : P} :
    BalancedProduct.mk _ ((stabilizer G x).toRightTranslation g) p ∈ e.linearTubeDomain L ↔
      L p ∈ e.chart.target := by
  refine ⟨?_, fun hp ↦ ⟨(g, p), ⟨mem_univ g, hp⟩, rfl⟩⟩
  rintro ⟨⟨g', p'⟩, ⟨-, hp'⟩, hq⟩
  obtain ⟨k, -, rfl⟩ :=
    BalancedProduct.mk_toRightTranslation_eq_mk_toRightTranslation_iff.1 hq.symm
  exact (e.apply_smul_mem_target_iff hL k p').2 hp'

include hL in
/-- The domain of the tube map along a linear fibre is `G`-invariant. -/
theorem smul_mem_linearTubeDomain_iff (g : G)
    {y : BalancedProduct (stabilizer G x) (stabilizer G x).RightTranslation P} :
    g • y ∈ e.linearTubeDomain L ↔ y ∈ e.linearTubeDomain L := by
  induction y using BalancedProduct.induction_on_toRightTranslation with
  | h g' p =>
    rw [BalancedProduct.smul_mk_toRightTranslation, e.mk_mem_linearTubeDomain_iff hL,
      e.mk_mem_linearTubeDomain_iff hL]

/-- The domain of the tube map along a linear fibre is open, when the stabilizer acts on `P` by
homeomorphisms. -/
theorem isOpen_linearTubeDomain [TopologicalSpace G] [IsTopologicalGroup G]
    [ContinuousConstSMul (stabilizer G x) P] : IsOpen (e.linearTubeDomain L) :=
  BalancedProduct.isOpenQuotientMap_mk_toRightTranslation.isOpenMap _
    (isOpen_univ.prod (e.chart.open_target.preimage L.continuous))

/-! ### Smoothness and the differential at `[1, 0]` -/

/-- Near a point `p` with `L p` in the target of `e`, the slice map along a linear fibre is
`p ↦ e.symm (L p)`. -/
theorem linearSliceMap_eventuallyEq {p : P} (hp : L p ∈ e.chart.target) :
    e.linearSliceMap hL =ᶠ[𝓝 p] fun p' ↦ e.chart.symm (L p') :=
  eventually_of_mem ((e.chart.open_target.preimage L.continuous).mem_nhds hp)
    fun _ hp' ↦ e.linearSliceMap_apply_of_mem hL hp'

/-- The slice map along a linear fibre is smooth at every point `p` with `L p` in the target
of `e`. -/
theorem contMDiffAt_linearSliceMap {p : P} (hp : L p ∈ e.chart.target) :
    ContMDiffAt 𝓘(ℝ, P) I' ∞ (e.linearSliceMap hL) p := by
  refine ContMDiffAt.congr_of_eventuallyEq ?_ (e.linearSliceMap_eventuallyEq hL hp)
  exact (e.contMDiffOn_symm.contMDiffAt (e.chart.open_target.mem_nhds hp)).comp p
    L.contMDiff.contMDiffAt

/-- At `0`, the slice map along a linear fibre has derivative `L`. -/
theorem hasMFDerivAt_linearSliceMap :
    HasMFDerivAt 𝓘(ℝ, P) I' (e.linearSliceMap hL) 0 L := by
  have h0 : L 0 ∈ e.chart.target := by rw [map_zero]; exact e.zero_mem_target
  have hs : HasMFDerivAt 𝓘(ℝ, E') I' e.chart.symm (L 0) (ContinuousLinearMap.id ℝ E') := by
    rw [map_zero]
    exact e.hasMFDerivAt_symm
  have h := hs.comp (0 : P) L.hasMFDerivAt
  exact (h.congr_mfderiv (ContinuousLinearMap.id_comp _)).congr_of_eventuallyEq
    (e.linearSliceMap_eventuallyEq hL h0)

section Smooth

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace G] [ChartedSpace H G] [LieGroup I ∞ G] [ContMDiffSMul I I' ∞ G M]
  [IsClosed (stabilizer G x : Set G)] [FiniteDimensional ℝ P]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [ChartedSpace F (stabilizer G x)] [LieGroup 𝓘(ℝ, F) ∞ (stabilizer G x)]
  [ContMDiffSMul 𝓘(ℝ, F) I ∞ (stabilizer G x) G]
  [ContMDiffSMul 𝓘(ℝ, F) 𝓘(ℝ, P) ∞ (stabilizer G x) P]

/-- **The tube map along a linear fibre is smooth on its domain**, for the manifold structure
`TauCeti.BalancedProduct.rightTranslationChartedSpace` on `G ×_H P`. Here `G` is a
finite-dimensional real Lie group acting smoothly on `M`, the stabilizer `H` of `x` is closed,
and `H` carries a Lie group structure for which it acts smoothly on `G` and on `P`. -/
theorem contMDiffOn_linearTubeMap :
    letI := BalancedProduct.rightTranslationChartedSpace (stabilizer G x) P I 𝓘(ℝ, P) F
    ContMDiffOn 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × P)) I' ∞ (e.linearTubeMap hL)
      (e.linearTubeDomain L) := by
  let _ := BalancedProduct.rightTranslationChartedSpace (stabilizer G x) P I 𝓘(ℝ, P) F
  rintro _ ⟨⟨g, p⟩, ⟨-, hp⟩, rfl⟩
  refine ContMDiffAt.contMDiffWithinAt ?_
  have hπ := (BalancedProduct.isSubmersion_quotientMk_rightTranslation (K := stabilizer G x)
    (Z := P) (I := I) (IZ := 𝓘(ℝ, P)) (F := F)).isSubmersionAt
      ((stabilizer G x).toRightTranslation g, p)
  refine (hπ.contMDiffAt_comp_iff le_rfl).1 ?_
  rw [linearTubeMap_def, BalancedProduct.liftRightTranslation_comp_quotientMk]
  exact ((Subgroup.RightTranslation.contMDiff_toRightTranslation_symm (I := I) ∞).comp
    (contMDiff_fst (J := 𝓘(ℝ, P)) (N := P))).contMDiffAt.smul
      ((e.contMDiffAt_linearSliceMap hL hp).comp _ contMDiffAt_snd)

variable (F) in
/-- **The differential of the tube map along a linear fibre at `[1, 0]`.** Composed with the
differential at `(1, 0)` of the projection `π : G × P → G ×_H P`, a submersion
(`TauCeti.BalancedProduct.isSubmersion_quotientMk_rightTranslation`), the differential of the tube
map at `[1, 0]` sends `(ξ, p)` to `ξ_M(x) + L p`. The hypotheses are those of
`contMDiffOn_linearTubeMap`. -/
theorem mfderiv_linearTubeMap_mfderiv_quotientMk (ξ : GroupLieAlgebra I G) (p : P) :
    letI := BalancedProduct.rightTranslationChartedSpace (stabilizer G x) P I 𝓘(ℝ, P) F
    mfderiv 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × P)) I' (e.linearTubeMap hL)
        (Quotient.mk _ ((stabilizer G x).toRightTranslation 1, 0))
        (mfderiv (I.prod 𝓘(ℝ, P)) 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × P))
          (Quotient.mk (orbitRel (stabilizer G x) ((stabilizer G x).RightTranslation × P)))
          ((stabilizer G x).toRightTranslation 1, 0) (ξ, p)) =
      HAdd.hAdd (α := TangentSpace I' x) (β := TangentSpace I' x)
        (fundamentalVectorField I' ξ x) (L p) := by
  let _ := BalancedProduct.rightTranslationChartedSpace (stabilizer G x) P I 𝓘(ℝ, P) F
  -- The class `[1, 0]`, written as the image of `(1, 0)` under the projection.
  have h0 : Quotient.mk (orbitRel (stabilizer G x) ((stabilizer G x).RightTranslation × P))
      ((stabilizer G x).toRightTranslation 1, 0) ∈ e.linearTubeDomain L :=
    (e.mk_mem_linearTubeDomain_iff hL).2 ((map_zero L).symm ▸ e.zero_mem_target)
  have hπ := (BalancedProduct.isSubmersion_quotientMk_rightTranslation (K := stabilizer G x)
    (Z := P) (I := I) (IZ := 𝓘(ℝ, P)) (F := F)).contMDiff.mdifferentiableAt
      (x := ((stabilizer G x).toRightTranslation 1, (0 : P))) (by simp)
  have := topologicalGroup_of_lieGroup I ∞ (G := G)
  have : ContinuousSMul (stabilizer G x) P :=
    ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, F)) (I' := 𝓘(ℝ, P)) ∞
  have hΦ := ((e.contMDiffOn_linearTubeMap hL (I := I) (F := F)).contMDiffAt
    ((e.isOpen_linearTubeDomain (L := L)).mem_nhds h0)).mdifferentiableAt (by simp)
  have : ContMDiffSMul I I' 1 G M := ContMDiffSMul.of_le (M := M) ENat.LEInfty.out
  have hσ := e.hasMFDerivAt_linearSliceMap hL
  refine (mfderiv_comp_apply _ hΦ hπ _).symm.trans ?_
  rw [linearTubeMap_def, BalancedProduct.liftRightTranslation_comp_quotientMk]
  -- `(stabilizer G x).RightTranslation` is `G` with the same charts, and `toRightTranslation` is
  -- the identity, so this is the differential of `(g, p) ↦ g • σ p` on `G × P` at `(1, 0)`.
  refine (mfderiv_smul_slice_apply (σ := e.linearSliceMap hL) hσ.mdifferentiableAt ξ p).trans ?_
  rw [hσ.mfderiv, linearSliceMap_zero]
  -- The sides differ only in how `L p` is typed: as a map between the tangent spaces at `0` and
  -- at `x`, or between `P` and `E'`, of which those tangent spaces are type synonyms.
  rfl

end Smooth

end LinearizingChart

end SymplecticGeometry

end
