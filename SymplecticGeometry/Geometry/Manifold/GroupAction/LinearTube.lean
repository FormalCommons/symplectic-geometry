/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Lie.Subgroup.BalancedProduct
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
  `e` (`SymplecticGeometry.LinearizingChart.linearTubeDomain`), since the slice map is smooth
  at each `p` with `L p` in the target of `e`;
* composed with the differential at `(1, 0)` of the projection `π : G × P → G ×_H P`, its
  differential at `[1, 0]` is `(ξ, p) ↦ ξ_M(x) + L p`;
* when `L` is injective with range a complement of the orbit tangent space `𝔤 · x`, and `M` is
  boundaryless and Hausdorff, it is a local diffeomorphism at `[1, 0]`, and at every `[g, p]`
  with `p` in some open `H`-invariant neighbourhood `Z` of `0` with `L '' Z` in the target of
  `e`.

For the last point, `(ξ, p) ↦ ξ_M(x) + L p` is onto `T_x M` since `𝔤 · x + range L = T_x M`
(`SymplecticGeometry.LinearizingChart.surjective_mfderiv_linearTubeMap_mfderiv_quotientMk`), and
vanishes only on `𝔤_x × 0` since the two subspaces meet in `0` and `L` is injective
(`SymplecticGeometry.LinearizingChart.mfderiv_linearTubeMap_mfderiv_quotientMk_eq_zero_iff`),
the first by Tau Ceti's `LinearMap.surjective_coprod_iff` and the second by
`TauCeti.InfinitesimalAction.apply_add_eq_zero_iff`; and
the stabilizer fixes `0 ∈ P` since `L` is injective
(`SymplecticGeometry.LinearizingChart.smul_zero_eq_zero_of_injective`). The rest is shared with
the tube map of a slice domain: the inverse function theorem for the lift of an equivariant map,
`TauCeti.BalancedProduct.isLocalDiffeomorphAt_liftRightTranslation_mk_one`, and the invariance of
local diffeomorphy along orbits,
`TauCeti.BalancedProduct.isLocalDiffeomorphAt_liftRightTranslation_mk_iff` and
`TauCeti.BalancedProduct.isLocalDiffeomorphAt_liftRightTranslation_mk_one_smul_iff`.

The local diffeomorphy at `[1, 0]` parallels Tau Ceti's slice theorem
`TauCeti.BalancedProduct.isLocalDiffeomorphAt_liftRightTranslation_one`, with `L` in place of the
differential of the slice map, and its surjectivity step follows the surjectivity step of that
proof. It departs from it in two ways: the slice map is smooth only near `0`, where `L p` lies in
the target of `e`, rather than everywhere; and in place of the dimension count
`dim H = dim 𝔤_x`, which need not hold for an arbitrary Lie group structure on `H`, injectivity
comes from a kernel argument.

The construction parallels `SymplecticGeometry.LinearizingChart.SliceDomain.tubeMap`, with the
linear fibre `P` in place of a slice domain. Both results follow from the corresponding facts
about any lift of an equivariant map, `TauCeti.BalancedProduct.contMDiffAt_liftRightTranslation`
and `TauCeti.BalancedProduct.mfderiv_liftRightTranslation_mfderiv_quotientMk`.

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
* `SymplecticGeometry.LinearizingChart.surjective_mfderiv_linearTubeMap_mfderiv_quotientMk`,
  `SymplecticGeometry.LinearizingChart.mfderiv_linearTubeMap_mfderiv_quotientMk_eq_zero_iff`: for
  an injective `L` with range a complement of `𝔤 · x`, this composite is onto and vanishes
  exactly on `𝔤_x × 0`.
* `SymplecticGeometry.LinearizingChart.isLocalDiffeomorphAt_linearTubeMap_mk_one`,
  `SymplecticGeometry.LinearizingChart.exists_isLocalDiffeomorphAt_linearTubeMap`: for a complement
  of `𝔤 · x`, the map is a local diffeomorphism at `[1, 0]`, and at every `[g, p]` with `p` near
  `0`.

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

/-- An injective map `L` that intertwines the action of the stabilizer of `x` on `P` with the
differentials at `x` forces the stabilizer to fix `0 ∈ P`, since the differentials fix `0`. -/
theorem smul_zero_eq_zero_of_injective
    (hL : ∀ (k : stabilizer G x) (p : P),
      L (k • p) = mfderiv I' I' (fun y : M ↦ (k : G) • y) x (L p))
    (hLi : Injective L) (k : stabilizer G x) : k • (0 : P) = 0 :=
  hLi (by rw [hL, map_zero]; exact (mfderiv I' I' (fun y : M ↦ (k : G) • y) x).map_zero)

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
  rw [linearTubeMap_def]
  exact (BalancedProduct.contMDiffAt_liftRightTranslation
    (e.contMDiffAt_linearSliceMap hL hp) g).contMDiffWithinAt

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
  rw [linearTubeMap_def]
  have : ContMDiffSMul I I' 1 G M := ContMDiffSMul.of_le (M := M) ENat.LEInfty.out
  have hσ := e.hasMFDerivAt_linearSliceMap hL
  refine (BalancedProduct.mfderiv_liftRightTranslation_mfderiv_quotientMk hσ.mdifferentiableAt
    ξ p).trans ?_
  rw [hσ.mfderiv, linearSliceMap_zero]
  -- The sides differ only in how `L p` is typed: as a map between the tangent spaces at `0` and
  -- at `x`, or between `P` and `E'`, of which those tangent spaces are type synonyms.
  rfl

variable (F) in
/-- For a map `L` whose range spans `T_x M` together with the orbit tangent space `𝔤 · x`, the
composite of the differentials of the tube map along a linear fibre at `[1, 0]` and of the
projection `G × P → G ×_H P` at `(1, 0)` is onto `T_x M`. -/
theorem surjective_mfderiv_linearTubeMap_mfderiv_quotientMk [CompleteSpace E']
    [IsManifold I' ∞ M]
    (hV : (InfinitesimalAction.fundamental I G I' M).orbitTangent x ⊔ (L : P →ₗ[ℝ] E').range =
      ⊤) :
    letI := BalancedProduct.rightTranslationChartedSpace (stabilizer G x) P I 𝓘(ℝ, P) F
    Surjective fun q : GroupLieAlgebra I G × P ↦
      mfderiv 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × P)) I' (e.linearTubeMap hL)
        (Quotient.mk _ ((stabilizer G x).toRightTranslation 1, 0))
        (mfderiv (I.prod 𝓘(ℝ, P)) 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × P))
          (Quotient.mk (orbitRel (stabilizer G x) ((stabilizer G x).RightTranslation × P)))
          ((stabilizer G x).toRightTranslation 1, 0) q) := by
  -- `L` read as a map into `T_x M`, a type synonym of `E'`.
  let ι : P →ₗ[ℝ] TangentSpace I' x := (L : P →ₗ[ℝ] E')
  intro (w : TangentSpace I' x)
  obtain ⟨⟨ξ, p⟩, hp⟩ :=
    (LinearMap.surjective_coprod_iff ((InfinitesimalAction.fundamental I G I' M).eval x) ι).2
      (by rw [← InfinitesimalAction.orbitTangent_eq_range]; exact hV) w
  refine ⟨(ξ, p), (e.mfderiv_linearTubeMap_mfderiv_quotientMk hL F ξ p).trans ?_⟩
  rwa [LinearMap.coprod_apply, InfinitesimalAction.eval_apply,
    InfinitesimalAction.fundamental_apply] at hp

variable (F) in
/-- For an injective map `L` whose range meets the orbit tangent space `𝔤 · x` only in `0`, the
composite of the differentials of the tube map along a linear fibre at `[1, 0]` and of the
projection `G × P → G ×_H P` at `(1, 0)` vanishes exactly on `𝔤_x × 0`, where `𝔤_x` is the
isotropy algebra of `x`. -/
theorem mfderiv_linearTubeMap_mfderiv_quotientMk_eq_zero_iff [CompleteSpace E']
    [IsManifold I' ∞ M] (hLi : Injective L)
    (hV : Disjoint ((InfinitesimalAction.fundamental I G I' M).orbitTangent x)
      (L : P →ₗ[ℝ] E').range)
    (ξ : GroupLieAlgebra I G) (p : P) :
    letI := BalancedProduct.rightTranslationChartedSpace (stabilizer G x) P I 𝓘(ℝ, P) F
    mfderiv 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × P)) I' (e.linearTubeMap hL)
        (Quotient.mk _ ((stabilizer G x).toRightTranslation 1, 0))
        (mfderiv (I.prod 𝓘(ℝ, P)) 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × P))
          (Quotient.mk (orbitRel (stabilizer G x) ((stabilizer G x).RightTranslation × P)))
          ((stabilizer G x).toRightTranslation 1, 0) (ξ, p)) = 0 ↔
      ξ ∈ (InfinitesimalAction.fundamental I G I' M).isotropy x ∧ p = 0 := by
  rw [e.mfderiv_linearTubeMap_mfderiv_quotientMk hL F ξ p, ← InfinitesimalAction.fundamental_apply]
  -- `L` read as a map into `T_x M`, a type synonym of `E'`.
  let ι : P →ₗ[ℝ] TangentSpace I' x := (L : P →ₗ[ℝ] E')
  exact (InfinitesimalAction.fundamental I G I' M).apply_add_eq_zero_iff (L := ι) hLi hV

/-! ### Local diffeomorphy near the zero section -/

variable (F) in
/-- **The tube map along a linear fibre is a local diffeomorphism at `[1, 0]`** when `L` is
injective and its range is a complement of the orbit tangent space `𝔤 · x` in `T_x M`. Composed
with the differential of the projection `π : G × P → G ×_H P`, its differential at `[1, 0]` is
onto `T_x M` and vanishes only on `𝔤_x × 0`, a set that `dπ` kills. -/
theorem isLocalDiffeomorphAt_linearTubeMap_mk_one [CompleteSpace E'] [IsManifold I' ∞ M] [T2Space M]
    [I'.Boundaryless]
    (hLi : Injective L)
    (hV : IsCompl ((InfinitesimalAction.fundamental I G I' M).orbitTangent x)
      (L : P →ₗ[ℝ] E').range) :
    letI := BalancedProduct.rightTranslationChartedSpace (stabilizer G x) P I 𝓘(ℝ, P) F
    IsLocalDiffeomorphAt 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × P)) I' ∞ (e.linearTubeMap hL)
      (Quotient.mk _ ((stabilizer G x).toRightTranslation 1, 0)) := by
  let _ := BalancedProduct.rightTranslationChartedSpace (stabilizer G x) P I 𝓘(ℝ, P) F
  have : T2Space G := I.t2Space_of_lieGroup ∞
  have h0 : (0 : P) ∈ L ⁻¹' e.chart.target := by
    rw [mem_preimage, map_zero]
    exact e.zero_mem_target
  have hsurj := e.surjective_mfderiv_linearTubeMap_mfderiv_quotientMk hL F hV.codisjoint.eq_top
  rw [linearTubeMap_def] at hsurj ⊢
  refine BalancedProduct.isLocalDiffeomorphAt_liftRightTranslation_mk_one F
    (e.chart.open_target.preimage L.continuous) h0
    (fun p hp ↦ (e.contMDiffAt_linearSliceMap hL hp).contMDiffWithinAt)
    (smul_zero_eq_zero_of_injective hL hLi) hsurj fun ξ p hp ↦ ?_
  rw [← linearTubeMap_def] at hp
  obtain ⟨hξ, rfl⟩ :=
    (e.mfderiv_linearTubeMap_mfderiv_quotientMk_eq_zero_iff hL F hLi hV.disjoint ξ p).1 hp
  exact ⟨TauCeti.Lie.mem_isotropy_fundamental_iff.1 hξ, rfl⟩

variable (F) in
/-- **The tube map along a linear fibre is a local diffeomorphism near the zero section.** When
`L` is injective and its range is a complement of the orbit tangent space `𝔤 · x` in `T_x M`,
there is an open neighbourhood `Z` of `0` in `P`, invariant under the stabilizer `H` of `x` and
mapped by `L` into the target of `e`, such that the tube map is a local diffeomorphism at every
class `[g, p]` with `p ∈ Z`. -/
theorem exists_isLocalDiffeomorphAt_linearTubeMap [CompleteSpace E'] [IsManifold I' ∞ M] [T2Space M]
    [I'.Boundaryless]
    (hLi : Injective L)
    (hV : IsCompl ((InfinitesimalAction.fundamental I G I' M).orbitTangent x)
      (L : P →ₗ[ℝ] E').range) :
    letI := BalancedProduct.rightTranslationChartedSpace (stabilizer G x) P I 𝓘(ℝ, P) F
    ∃ Z : Set P, IsOpen Z ∧ (0 : P) ∈ Z ∧ (∀ (k : stabilizer G x) {p : P}, p ∈ Z → k • p ∈ Z) ∧
      L '' Z ⊆ e.chart.target ∧ ∀ (g : G) {p : P}, p ∈ Z →
        IsLocalDiffeomorphAt 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × P)) I' ∞
          (e.linearTubeMap hL)
          (BalancedProduct.mk _ ((stabilizer G x).toRightTranslation g) p) := by
  let _ := BalancedProduct.rightTranslationChartedSpace (stabilizer G x) P I 𝓘(ℝ, P) F
  -- `Z` is the set of `p` with `L p` in the target of `e` at whose class `[1, p]` the tube map is
  -- a local diffeomorphism.
  refine ⟨L ⁻¹' e.chart.target ∩ {p | IsLocalDiffeomorphAt
    𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × P)) I' ∞ (e.linearTubeMap hL)
      (BalancedProduct.mk _ ((stabilizer G x).toRightTranslation 1) p)}, ?_, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [linearTubeMap_def]
    exact (e.chart.open_target.preimage L.continuous).inter
      (BalancedProduct.isOpen_setOfPred_isLocalDiffeomorphAt_liftRightTranslation_mk_one F)
  · rw [mem_preimage, map_zero]
    exact e.zero_mem_target
  · exact e.isLocalDiffeomorphAt_linearTubeMap_mk_one hL F hLi hV
  · rintro k p ⟨hp, hp'⟩
    refine ⟨(e.apply_smul_mem_target_iff hL k p).2 hp, ?_⟩
    simp only [mem_ofPred_eq, linearTubeMap_def] at hp' ⊢
    exact (BalancedProduct.isLocalDiffeomorphAt_liftRightTranslation_mk_one_smul_iff F k p).2 hp'
  · rintro _ ⟨p, ⟨hp, -⟩, rfl⟩
    exact hp
  · rintro g p ⟨-, hp⟩
    rw [linearTubeMap_def, BalancedProduct.isLocalDiffeomorphAt_liftRightTranslation_mk_iff F g]
    exact hp

end Smooth

end LinearizingChart

end SymplecticGeometry

end
