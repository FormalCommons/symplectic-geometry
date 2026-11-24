/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.LocallyConvex.HahnBanach
public import SymplecticGeometry.Geometry.Manifold.ContMDiff.Submodule
public import TauCeti.Geometry.Lie.Subgroup.BalancedProduct
public import TauCeti.Geometry.Manifold.GroupAction.EquivariantSlice

/-!
# The tube map of an orbit

Let a Lie group `G` act smoothly on a manifold `M`, and let `x : M` have stabilizer
`H = stabilizer G x`. A *linearizing chart* at `x` (`SymplecticGeometry.LinearizingChart`) is a
smooth chart `e : M → T_x M` at `x`, with smooth inverse, `e x = 0` and derivative the identity at
`x`, whose domain is `H`-invariant and in which every `h ∈ H` acts by its differential `dh_x`.
When `H` is compact and `G`, `M` are finite-dimensional, such a chart exists by Bochner's
linearization theorem, as Tau Ceti proves in
`TauCeti.exists_equivariant_contMDiff_chart_of_isCompact_stabilizer`
(`SymplecticGeometry.LinearizingChart.nonempty`).

For a linear subspace `V` of `T_x M`, typically an `H`-invariant complement of the orbit
tangent space `𝔤 · x`, a *slice domain* (`SymplecticGeometry.LinearizingChart.SliceDomain`) is
an open subset `U` of `V` inside the target of `e` that is invariant under every `dh_x`, such as
`V ∩ e.target` when `V` is invariant
(`SymplecticGeometry.LinearizingChart.SliceDomain.interTarget`). Then:

* `H` acts on `U` by `h • v = dh_x v`; when `V` is finite-dimensional, smoothly for any
  manifold structure on `H` for which `H` acts smoothly on `M`, such as the closed-subgroup
  structure `TauCeti.Lie.EmbeddedLieSubgroupData.ofIsClosed`: in the chart,
  `dh_x v = e (h • e.symm v)`;
* the slice map `v ↦ e.symm v` is a smooth `H`-equivariant map `U → M`
  (`SymplecticGeometry.LinearizingChart.SliceDomain.sliceMap`);
* the *tube map* `[g, v] ↦ g • e.symm v` on the balanced product `G ×_H U`, Tau Ceti's
  `TauCeti.BalancedProduct.liftRightTranslation` of the slice map
  (`SymplecticGeometry.LinearizingChart.SliceDomain.tubeMap`), is smooth for the manifold
  structure `TauCeti.BalancedProduct.rightTranslationChartedSpace`, `G`-equivariant, and sends
  `[1, 0]` to `x`.

The equivariance `e.symm (dh_x v) = h • e.symm v` of the slice map
(`SymplecticGeometry.LinearizingChart.symm_mfderiv_smul`) adapts a step of the
proof of Tau Ceti's `TauCeti.exists_equivariant_slice_of_isCompact_stabilizer`, stated on its own.

Nothing here asks `U` to be small or `V` to be a complement of `𝔤 · x`; those are needed for the
tube map to be a local diffeomorphism.

## Main definitions

* `SymplecticGeometry.LinearizingChart`: a chart at `x` in which the stabilizer acts linearly.
* `SymplecticGeometry.LinearizingChart.SliceDomain`: an invariant open subset of a subspace
  inside the target of the chart, with the action of the stabilizer.
* `SymplecticGeometry.LinearizingChart.SliceDomain.sliceMap`: the equivariant map
  `v ↦ e.symm v`.
* `SymplecticGeometry.LinearizingChart.SliceDomain.tubeMap`: the map `[g, v] ↦ g • e.symm v`
  out of `G ×_H U`.

## Main results

* `SymplecticGeometry.LinearizingChart.nonempty`: linearizing charts exist at points with
  compact stabilizer.
* `SymplecticGeometry.LinearizingChart.SliceDomain.instContMDiffSMul`: the stabilizer acts
  smoothly on a slice domain.
* `SymplecticGeometry.LinearizingChart.SliceDomain.contMDiff_tubeMap`,
  `SymplecticGeometry.LinearizingChart.SliceDomain.tubeMap_smul`,
  `SymplecticGeometry.LinearizingChart.SliceDomain.tubeMap_mk_one_zero`: the tube map is smooth,
  `G`-equivariant, and sends `[1, 0]` to `x`.

## References

* [V. Guillemin and S. Sternberg, *Symplectic Techniques in Physics*][GuilleminSternberg1990],
  the tube `G ×_H V` around an orbit in the local normal form.
* J. J. Duistermaat and J. A. C. Kolk, *Lie Groups*, Universitext, Springer, 2000, Section 2.4.
-/

public section

noncomputable section

open Function Set Manifold MulAction TauCeti TopologicalSpace
open scoped ContDiff Manifold

namespace SymplecticGeometry

variable {G : Type*} [Group G] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [MulAction G M]

variable (G I') in
/-- A **linearizing chart** at `x` for the action of `G` on `M`: a chart `e` of `M` with values
in the model space `E' = T_x M`, smooth with smooth inverse, with `e x = 0` and derivative the
identity at `x`, whose source is invariant under the stabilizer of `x` and in which every `g` of
the stabilizer acts by its differential: `e (g • z) = dg_x (e z)`. -/
@[ext]
structure LinearizingChart (x : M) where
  /-- the chart -/
  chart : OpenPartialHomeomorph M E'
  mem_source : x ∈ chart.source
  apply_self : chart x = 0
  contMDiffOn : ContMDiffOn I' 𝓘(ℝ, E') ∞ chart chart.source
  contMDiffOn_symm : ContMDiffOn 𝓘(ℝ, E') I' ∞ chart.symm chart.target
  hasMFDerivAt : HasMFDerivAt I' 𝓘(ℝ, E') chart x (ContinuousLinearMap.id ℝ E')
  smul_mem_source : ∀ g ∈ stabilizer G x, ∀ z ∈ chart.source, g • z ∈ chart.source
  apply_smul : ∀ g ∈ stabilizer G x, ∀ z ∈ chart.source,
    chart (g • z) = mfderiv I' I' (fun y : M ↦ g • y) x (chart z)

namespace LinearizingChart

variable {x : M} (e : LinearizingChart G I' x)

/-- The origin lies in the target of a linearizing chart. -/
theorem zero_mem_target : (0 : E') ∈ e.chart.target :=
  e.apply_self ▸ e.chart.map_source e.mem_source

/-- The inverse of a linearizing chart at `x` sends `0` to `x`. -/
@[simp]
theorem symm_zero : e.chart.symm 0 = x := by
  rw [← e.apply_self, e.chart.left_inv e.mem_source]

/-- In a linearizing chart, the differential of `g` at `x` is `v ↦ e (g • e.symm v)` on the
target. -/
theorem mfderiv_smul_eq {g : G} (hg : g ∈ stabilizer G x) {v : E'} (hv : v ∈ e.chart.target) :
    mfderiv I' I' (fun y : M ↦ g • y) x v = e.chart (g • e.chart.symm v) := by
  rw [e.apply_smul g hg _ (e.chart.map_target hv), e.chart.right_inv hv]

/-- The target of a linearizing chart is invariant under the differentials of the stabilizer. -/
theorem mfderiv_smul_mem_target {g : G} (hg : g ∈ stabilizer G x) {v : E'}
    (hv : v ∈ e.chart.target) : mfderiv I' I' (fun y : M ↦ g • y) x v ∈ e.chart.target := by
  rw [e.mfderiv_smul_eq hg hv]
  exact e.chart.map_source (e.smul_mem_source g hg _ (e.chart.map_target hv))

/-- The inverse of a linearizing chart intertwines `dg_x` with `g`. -/
theorem symm_mfderiv_smul {g : G} (hg : g ∈ stabilizer G x) {v : E'}
    (hv : v ∈ e.chart.target) :
    e.chart.symm (mfderiv I' I' (fun y : M ↦ g • y) x v) = g • e.chart.symm v := by
  rw [e.mfderiv_smul_eq hg hv,
    e.chart.left_inv (e.smul_mem_source g hg _ (e.chart.map_target hv))]

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField in
/-- **Linearizing charts exist at points with compact stabilizer**, for a smooth action of a
finite-dimensional real Lie group on a boundaryless manifold modelled on a complete space: this
is Tau Ceti's `TauCeti.exists_equivariant_contMDiff_chart_of_isCompact_stabilizer`. -/
theorem nonempty {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [TopologicalSpace G]
    [ChartedSpace H G] [LieGroup I ∞ G] [CompleteSpace E'] [I'.Boundaryless] [IsManifold I' ∞ M]
    [ContMDiffSMul I I' ∞ G M] (hx : IsCompact (stabilizer G x : Set G)) :
    Nonempty (LinearizingChart G I' x) := by
  obtain ⟨e, h₁, h₂, h₃, h₄, h₅, h₆⟩ :=
    exists_equivariant_contMDiff_chart_of_isCompact_stabilizer (I' := I') I hx
  exact ⟨⟨e, h₁, h₂, h₃, h₄, h₅, fun g hg z hz ↦ (h₆ g hg z hz).1,
    fun g hg z hz ↦ (h₆ g hg z hz).2⟩⟩

/-! ### Slice domains -/

/-- A **slice domain** for a linearizing chart `e` at `x` and a linear subspace `V` of `E'`: a
subset `U` of `V`, open in `V`, contained in the target of `e`, and invariant under the
differential `dg_x` of every `g` of the stabilizer of `x`. -/
@[ext]
structure SliceDomain (V : Submodule ℝ E') where
  /-- the subset of `E'` -/
  carrier : Set E'
  subset_slice : carrier ⊆ V
  isOpen : IsOpen ((↑) ⁻¹' carrier : Set V)
  subset_target : carrier ⊆ e.chart.target
  mfderiv_smul_mem : ∀ g ∈ stabilizer G x, ∀ v ∈ carrier,
    mfderiv I' I' (fun y : M ↦ g • y) x v ∈ carrier

namespace SliceDomain

variable {e} {V : Submodule ℝ E'} (U : SliceDomain e V)

/-- A slice domain as an open subset of `V`. -/
def toOpens : Opens V :=
  ⟨(↑) ⁻¹' U.carrier, U.isOpen⟩

instance : CoeSort (SliceDomain e V) (Type _) :=
  ⟨fun U ↦ U.toOpens⟩

@[simp]
theorem mem_toOpens_iff {v : V} : v ∈ U.toOpens ↔ (v : E') ∈ U.carrier :=
  Iff.rfl

theorem coe_mem (z : U) : ((z : V) : E') ∈ U.carrier :=
  z.property

theorem coe_mem_target (z : U) : ((z : V) : E') ∈ e.chart.target :=
  U.subset_target (U.coe_mem z)

variable (e) in
/-- For a subspace `V` invariant under the differentials of the stabilizer, `V ∩ e.target` is a
slice domain. -/
def interTarget
    (hV : ∀ g ∈ stabilizer G x, ∀ v ∈ V, mfderiv I' I' (fun y : M ↦ g • y) x v ∈ V) :
    SliceDomain e V where
  carrier := (V : Set E') ∩ e.chart.target
  subset_slice := inter_subset_left
  isOpen := by
    rw [preimage_inter, Subtype.coe_preimage_self, univ_inter]
    exact e.chart.open_target.preimage continuous_subtypeVal
  subset_target := inter_subset_right
  mfderiv_smul_mem g hg v hv := ⟨hV g hg v hv.1, e.mfderiv_smul_mem_target hg hv.2⟩

@[simp]
theorem carrier_interTarget
    (hV : ∀ g ∈ stabilizer G x, ∀ v ∈ V, mfderiv I' I' (fun y : M ↦ g • y) x v ∈ V) :
    (interTarget e hV).carrier = (V : Set E') ∩ e.chart.target :=
  (rfl)

theorem zero_mem_interTarget
    (hV : ∀ g ∈ stabilizer G x, ∀ v ∈ V, mfderiv I' I' (fun y : M ↦ g • y) x v ∈ V) :
    (0 : E') ∈ (interTarget e hV).carrier := by
  rw [carrier_interTarget]
  exact ⟨V.zero_mem, e.zero_mem_target⟩

/-- The stabilizer of `x` acts on a slice domain by `g • v = dg_x v`. -/
instance instSMul : SMul (stabilizer G x) U where
  smul g z := ⟨⟨mfderiv I' I' (fun y : M ↦ (g : G) • y) x ((z : V) : E'),
    U.subset_slice (U.mfderiv_smul_mem g g.property _ (U.coe_mem z))⟩,
    U.mem_toOpens_iff.2 (U.mfderiv_smul_mem g g.property _ (U.coe_mem z))⟩

@[simp]
theorem coe_smul (g : stabilizer G x) (z : U) :
    (((g • z : U) : V) : E') = mfderiv I' I' (fun y : M ↦ (g : G) • y) x ((z : V) : E') :=
  (rfl)

/-- In the chart, the action on a slice domain is `g • v = e (g • e.symm v)`. -/
theorem coe_smul_eq_chart (g : stabilizer G x) (z : U) :
    (((g • z : U) : V) : E') = e.chart ((g : G) • e.chart.symm ((z : V) : E')) := by
  rw [coe_smul, e.mfderiv_smul_eq g.property (U.coe_mem_target z)]

instance instMulAction : MulAction (stabilizer G x) U where
  one_smul z := by
    refine Subtype.ext (Subtype.ext ?_)
    rw [coe_smul_eq_chart, OneMemClass.coe_one, one_smul, e.chart.right_inv (U.coe_mem_target z)]
  mul_smul g h z := by
    refine Subtype.ext (Subtype.ext ?_)
    rw [coe_smul_eq_chart, coe_smul_eq_chart, coe_smul_eq_chart, Subgroup.coe_mul, mul_smul,
      e.chart.left_inv (e.smul_mem_source h h.property _ (e.chart.map_target (U.coe_mem_target z)))]

/-- The **slice map** `v ↦ e.symm v` of a slice domain, an equivariant map for the inclusion
of the stabilizer into `G`. -/
def sliceMap : U →ₑ[((↑) : stabilizer G x → G)] M where
  toFun z := e.chart.symm ((z : V) : E')
  map_smul' g z := by
    rw [coe_smul, e.symm_mfderiv_smul g.property (U.coe_mem_target z)]

@[simp]
theorem sliceMap_apply (z : U) : U.sliceMap z = e.chart.symm ((z : V) : E') :=
  (rfl)

/-- The inclusion of a slice domain into `E'` is smooth. -/
theorem contMDiff_coe : ContMDiff 𝓘(ℝ, V) 𝓘(ℝ, E') ∞ fun z : U ↦ ((z : V) : E') :=
  V.subtypeL.contMDiff.comp contMDiff_subtypeVal

/-- The slice map is smooth. -/
theorem contMDiff_sliceMap : ContMDiff 𝓘(ℝ, V) I' ∞ U.sliceMap :=
  e.contMDiffOn_symm.comp_contMDiff U.contMDiff_coe U.coe_mem_target

/-- **The stabilizer acts smoothly on a slice domain** of a finite-dimensional subspace `V`, for
any manifold structure on the stabilizer for which its action on `M` is smooth. -/
instance instContMDiffSMul [TopologicalSpace G] [FiniteDimensional ℝ V] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {HF : Type*} [TopologicalSpace HF]
    {IF : ModelWithCorners ℝ F HF} [ChartedSpace HF (stabilizer G x)]
    [ContMDiffSMul IF I' ∞ (stabilizer G x) M] :
    ContMDiffSMul IF 𝓘(ℝ, V) ∞ (stabilizer G x) U where
  contMDiff_smul := by
    rw [← ContMDiff.subtypeVal_comp_iff,
      (Submodule.ClosedComplemented.of_finiteDimensional V).contMDiff_iff_subtypeL_comp]
    -- In the chart the action is `(g, z) ↦ e (g • e.symm z)`.
    simp only [comp_apply, Submodule.subtypeL_apply, coe_smul_eq_chart]
    refine e.contMDiffOn.comp_contMDiff
      (contMDiff_fst.smul (U.contMDiff_sliceMap.comp contMDiff_snd)) fun q ↦ ?_
    exact e.smul_mem_source _ q.1.property _ (e.chart.map_target (U.coe_mem_target q.2))

/-! ### The tube map -/

/-- The **tube map** `[g, v] ↦ g • e.symm v` of a slice domain `U`, out of the balanced product
`G ×_H U` of `G` with `U` over the stabilizer `H` of `x`. -/
def tubeMap : BalancedProduct (stabilizer G x) (stabilizer G x).RightTranslation U → M :=
  BalancedProduct.liftRightTranslation U.sliceMap

theorem tubeMap_def : U.tubeMap = BalancedProduct.liftRightTranslation U.sliceMap :=
  (rfl)

@[simp]
theorem tubeMap_mk (g : G) (z : U) :
    U.tubeMap (BalancedProduct.mk _ ((stabilizer G x).toRightTranslation g) z) =
      g • e.chart.symm ((z : V) : E') := by
  rw [tubeMap_def, BalancedProduct.liftRightTranslation_mk, sliceMap_apply]

/-- The tube map is `G`-equivariant. -/
@[simp]
theorem tubeMap_smul (g : G)
    (y : BalancedProduct (stabilizer G x) (stabilizer G x).RightTranslation U) :
    U.tubeMap (g • y) = g • U.tubeMap y :=
  BalancedProduct.liftRightTranslation_smul _ g y

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField in
/-- **The tube map is smooth**, for the manifold structure
`TauCeti.BalancedProduct.rightTranslationChartedSpace` on `G ×_H U`. Here `G` is a
finite-dimensional real Lie group acting smoothly on `M`, the stabilizer `H` of `x` is closed,
and `H` carries a Lie group structure for which it acts smoothly on `G` and on `M`; Tau Ceti's
closed-subgroup structure `TauCeti.Lie.EmbeddedLieSubgroupData.ofIsClosed` is one
(`TauCeti.Lie.EmbeddedLieSubgroupData.contMDiffSMul`). -/
theorem contMDiff_tubeMap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [I.Boundaryless] [TopologicalSpace G] [ChartedSpace H G] [LieGroup I ∞ G]
    [ContMDiffSMul I I' ∞ G M] [IsClosed (stabilizer G x : Set G)] [FiniteDimensional ℝ V]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [ChartedSpace F (stabilizer G x)] [LieGroup 𝓘(ℝ, F) ∞ (stabilizer G x)]
    [ContMDiffSMul 𝓘(ℝ, F) I ∞ (stabilizer G x) G]
    [ContMDiffSMul 𝓘(ℝ, F) I' ∞ (stabilizer G x) M] :
    letI := BalancedProduct.rightTranslationChartedSpace (stabilizer G x) U I 𝓘(ℝ, V) F
    ContMDiff 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × V)) I' ∞ U.tubeMap :=
  BalancedProduct.contMDiff_liftRightTranslation U.contMDiff_sliceMap

/-- The tube map sends `[1, 0]` to `x`. -/
theorem tubeMap_mk_one_zero (h0 : (0 : E') ∈ U.carrier) :
    U.tubeMap (BalancedProduct.mk _ ((stabilizer G x).toRightTranslation 1)
      (⟨0, (U.mem_toOpens_iff).2 h0⟩ : U)) = x := by
  rw [tubeMap_mk, one_smul]
  exact e.symm_zero

end SliceDomain

end LinearizingChart

end SymplecticGeometry

end
