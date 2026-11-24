/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.LocallyConvex.HahnBanach
public import SymplecticGeometry.Geometry.Manifold.ContMDiff.Submodule
public import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.Basic
public import TauCeti.Geometry.Lie.Subgroup.BalancedProduct
public import TauCeti.Geometry.Lie.Subgroup.Stabilizer
public import TauCeti.Geometry.Manifold.GroupAction.EquivariantSlice
public import TauCeti.Geometry.Manifold.GroupAction.TransverseSlice
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
public import TauCeti.Geometry.Manifold.Submersion.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic

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
  structure `TauCeti.BalancedProduct.rightTranslationChartedSpace`, is `G`-equivariant and
  sends `[1, 0]` to `x`;
* composed with the differential at `(1, 0)` of the projection `π : G × U → G ×_H U`, a
  submersion, the differential of the tube map at `[1, 0]` is `(ξ, v) ↦ ξ_M(x) + v`. This is
  the differential at `(1, 0)` of `(g, v) ↦ g • e.symm v` on `G × V`, so Tau Ceti's
  `TauCeti.surjective_mfderiv_smul_slice` and `TauCeti.mfderiv_smul_slice_eq_zero_iff` give that
  it is onto `T_x M` when `V + 𝔤 · x = T_x M`, and that it vanishes exactly on `𝔤_x × 0` when
  `V ∩ 𝔤 · x = 0`.

The equivariance `e.symm (dh_x v) = h • e.symm v` of the slice map
(`SymplecticGeometry.LinearizingChart.symm_mfderiv_smul`) and the derivative of `e.symm` at `0`
(`SymplecticGeometry.LinearizingChart.hasMFDerivAt_symm`) adapt steps of the proof of Tau Ceti's
`TauCeti.exists_equivariant_slice_of_isCompact_stabilizer`, stated on their own.

When `V` is a complement of `𝔤 · x`, the tube map is a local diffeomorphism at `[1, 0]`: its
differential there is onto by the above, and injective because `dπ` is onto and kills `𝔤_x × 0`,
along which `t ↦ (exp (t ξ), 0)` stays in the class `[1, 0]`. The inverse function theorem
(Tau Ceti's `TauCeti.isLocalDiffeomorphAt_iff_exists_mfderiv_eq`) applies. Local diffeomorphy of
the equivariant tube map is `G`-invariant (`SymplecticGeometry.isLocalDiffeomorphAt_smul_iff`),
so it holds at every `[g, v]` with `v` in a smaller slice domain `U'` around `0`; `U` itself
need not be small.

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
* `SymplecticGeometry.LinearizingChart.SliceDomain.mfderiv_tubeMap_mfderiv_quotientMk`: the
  differential of the tube map at `[1, 0]`, composed with that of the projection, is
  `(ξ, v) ↦ ξ_M(x) + v`.
* `SymplecticGeometry.LinearizingChart.SliceDomain.surjective_mfderiv_tubeMap_mfderiv_quotientMk`,
  `SymplecticGeometry.LinearizingChart.SliceDomain.mfderiv_tubeMap_mfderiv_quotientMk_eq_zero_iff`:
  this composite is onto `T_x M`, and has kernel `𝔤_x × 0`, for suitable `V`.
* `SymplecticGeometry.LinearizingChart.SliceDomain.isLocalDiffeomorphAt_tubeMap_mk_one`: for a
  complement `V` of `𝔤 · x`, the tube map is a local diffeomorphism at `[1, 0]`.
* `SymplecticGeometry.LinearizingChart.SliceDomain.exists_sliceDomain_isLocalDiffeomorphAt_tubeMap`:
  the tube map is a local diffeomorphism at every `[g, v]` with `v` in some slice domain around
  `0`.

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

/-- The inverse of a linearizing chart at `x` has derivative the identity at `0`. -/
theorem hasMFDerivAt_symm :
    HasMFDerivAt 𝓘(ℝ, E') I' e.chart.symm 0 (ContinuousLinearMap.id ℝ E') := by
  have hsd : MDifferentiableAt 𝓘(ℝ, E') I' e.chart.symm 0 :=
    (e.contMDiffOn_symm.contMDiffAt (e.chart.open_target.mem_nhds e.zero_mem_target))
      |>.mdifferentiableAt (by simp)
  have hed : MDifferentiableAt I' 𝓘(ℝ, E') e.chart (e.chart.symm 0) :=
    by rw [e.symm_zero]; exact e.hasMFDerivAt.mdifferentiableAt
  refine hsd.hasMFDerivAt.congr_mfderiv (ContinuousLinearMap.ext fun w ↦ ?_)
  -- `de_x` is the identity, and it undoes the derivative of `e.symm` at `0`.
  have h := e.chart.mfderiv_apply_mfderiv_symm_apply e.zero_mem_target hed hsd w
  rwa [e.symm_zero, e.hasMFDerivAt.mfderiv] at h

/-- The inverse of a linearizing chart at `x`, restricted to a subspace `V`, has derivative the
inclusion of `V` at `0`. -/
theorem hasMFDerivAt_symm_comp_subtype (V : Submodule ℝ E') :
    HasMFDerivAt 𝓘(ℝ, V) I' (fun v : V ↦ e.chart.symm (v : E')) 0 V.subtypeL := by
  have h := e.hasMFDerivAt_symm.comp (0 : V) V.subtypeL.hasMFDerivAt
  exact h.congr_mfderiv (ContinuousLinearMap.id_comp _)

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

/-- At a point `z` of a slice domain of `V` with `z = 0` in `V`, the slice map has derivative the
inclusion of `V`. -/
theorem hasMFDerivAt_sliceMap {z : U} (hz : (z : V) = 0) :
    HasMFDerivAt 𝓘(ℝ, V) I' U.sliceMap z V.subtypeL := by
  have h := e.hasMFDerivAt_symm_comp_subtype V
  rw [← hz] at h
  refine (U.contMDiff_sliceMap z |>.mdifferentiableAt (by simp)).hasMFDerivAt.congr_mfderiv
    (ContinuousLinearMap.ext fun v ↦ ?_)
  -- The slice map is the restriction of `v ↦ e.symm v` to the open subset `U` of `V`.
  rw [← h.mfderiv]
  exact Manifold.mfderiv_comp_subtype_val_apply (f := fun v : V ↦ e.chart.symm (v : E')) v

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

/-- On representatives, the tube map is the slice map `(g, v) ↦ g • e.symm v`: its composite with
the projection `G × U → G ×_H U`. -/
theorem tubeMap_comp_quotientMk :
    U.tubeMap ∘ Quotient.mk (orbitRel (stabilizer G x) ((stabilizer G x).RightTranslation × U)) =
      fun p ↦ (stabilizer G x).toRightTranslation.symm p.1 • e.chart.symm ((p.2 : V) : E') :=
  funext fun p ↦ by
    rw [comp_apply, BalancedProduct.quotientMk_eq_mk_toRightTranslation, tubeMap_mk]

/-! ### The differential of the tube map at `[1, 0]` -/

section Differential

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace G] [ChartedSpace H G] [LieGroup I ∞ G] [ContMDiffSMul I I' ∞ G M]
  [IsClosed (stabilizer G x : Set G)] [FiniteDimensional ℝ V]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [ChartedSpace F (stabilizer G x)] [LieGroup 𝓘(ℝ, F) ∞ (stabilizer G x)]
  [ContMDiffSMul 𝓘(ℝ, F) I ∞ (stabilizer G x) G]
  [ContMDiffSMul 𝓘(ℝ, F) I' ∞ (stabilizer G x) M] {z : U}

variable (F) in
/-- **The differential of the tube map at `[1, 0]`.** Composed with the differential at `(1, 0)`
of the projection `π : G × U → G ×_H U`, a submersion
(`TauCeti.BalancedProduct.isSubmersion_quotientMk_rightTranslation`), the differential of the tube
map at `[1, 0]` sends `(ξ, v)` to `ξ_M(x) + v`. Here `0` is any point `z` of `U` that is `0` in
`V`, and the hypotheses are those of `contMDiff_tubeMap`. -/
theorem mfderiv_tubeMap_mfderiv_quotientMk (hz : (z : V) = 0) (ξ : GroupLieAlgebra I G)
    (v : V) :
    letI := BalancedProduct.rightTranslationChartedSpace (stabilizer G x) U I 𝓘(ℝ, V) F
    mfderiv 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × V)) I' U.tubeMap
        (Quotient.mk _ ((stabilizer G x).toRightTranslation 1, z))
        (mfderiv (I.prod 𝓘(ℝ, V)) 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × V))
          (Quotient.mk (orbitRel (stabilizer G x) ((stabilizer G x).RightTranslation × U)))
          ((stabilizer G x).toRightTranslation 1, z) (ξ, v)) =
      HAdd.hAdd (α := TangentSpace I' x) (β := TangentSpace I' x)
        (fundamentalVectorField I' ξ x) (v : E') := by
  let _ := BalancedProduct.rightTranslationChartedSpace (stabilizer G x) U I 𝓘(ℝ, V) F
  have hπ := (BalancedProduct.isSubmersion_quotientMk_rightTranslation (K := stabilizer G x)
    (Z := U) (I := I) (IZ := 𝓘(ℝ, V)) (F := F)).contMDiff.mdifferentiableAt
      (x := ((stabilizer G x).toRightTranslation 1, z)) (by simp)
  have hΦ := (U.contMDiff_tubeMap (I := I) (F := F)).mdifferentiableAt
    (x := Quotient.mk _ ((stabilizer G x).toRightTranslation 1, z)) (by simp)
  have : ContMDiffSMul I I' 1 G M := ContMDiffSMul.of_le (M := M) ENat.LEInfty.out
  have hσ := U.hasMFDerivAt_sliceMap hz
  refine (mfderiv_comp_apply _ hΦ hπ _).symm.trans ?_
  rw [U.tubeMap_comp_quotientMk]
  -- `(stabilizer G x).RightTranslation` is `G` with the same charts, and `toRightTranslation` is
  -- the identity, so this is the differential of `(g, v) ↦ g • e.symm v` on `G × U` at `(1, z)`.
  refine (mfderiv_smul_slice_apply (σ := U.sliceMap) hσ.mdifferentiableAt ξ v).trans ?_
  rw [hσ.mfderiv, sliceMap_apply, hz, ZeroMemClass.coe_zero, e.symm_zero]
  exact congrArg (fundamentalVectorField I' ξ x + ·) (V.subtypeL_apply v)

variable (F) in
/-- The composite of the differentials of the tube map at `[1, 0]` and of the projection
`G × U → G ×_H U` at `(1, 0)` is the differential at `(1, 0)` of the map
`(g, v) ↦ g • e.symm v` on `G × V`. -/
theorem mfderiv_tubeMap_mfderiv_quotientMk_eq_mfderiv_smul_symm (hz : (z : V) = 0)
    (ξ : GroupLieAlgebra I G) (v : V) :
    letI := BalancedProduct.rightTranslationChartedSpace (stabilizer G x) U I 𝓘(ℝ, V) F
    mfderiv 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × V)) I' U.tubeMap
        (Quotient.mk _ ((stabilizer G x).toRightTranslation 1, z))
        (mfderiv (I.prod 𝓘(ℝ, V)) 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × V))
          (Quotient.mk (orbitRel (stabilizer G x) ((stabilizer G x).RightTranslation × U)))
          ((stabilizer G x).toRightTranslation 1, z) (ξ, v)) =
      mfderiv (I.prod 𝓘(ℝ, V)) I' (fun p : G × V ↦ p.1 • e.chart.symm (p.2 : E')) (1, 0)
        (ξ, v) := by
  have : ContMDiffSMul I I' 1 G M := ContMDiffSMul.of_le (M := M) ENat.LEInfty.out
  have hσ := e.hasMFDerivAt_symm_comp_subtype V
  refine (U.mfderiv_tubeMap_mfderiv_quotientMk F hz ξ v).trans
    (Eq.trans ?_ (mfderiv_smul_slice_apply hσ.mdifferentiableAt ξ v).symm)
  rw [hσ.mfderiv, ZeroMemClass.coe_zero, e.symm_zero]
  exact congrArg (fundamentalVectorField I' ξ x + ·) (V.subtypeL_apply v).symm

variable (F) in
/-- For a subspace `V` that spans `T_x M` together with the orbit tangent space `𝔤 · x`, the
composite of the differentials of the tube map at `[1, 0]` and of the projection
`G × U → G ×_H U` at `(1, 0)` is onto `T_x M`. -/
theorem surjective_mfderiv_tubeMap_mfderiv_quotientMk [CompleteSpace E'] [IsManifold I' ∞ M]
    (hV : (InfinitesimalAction.fundamental I G I' M).orbitTangent x ⊔ V = ⊤)
    (hz : (z : V) = 0) :
    letI := BalancedProduct.rightTranslationChartedSpace (stabilizer G x) U I 𝓘(ℝ, V) F
    Surjective fun p : GroupLieAlgebra I G × V ↦
      mfderiv 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × V)) I' U.tubeMap
        (Quotient.mk _ ((stabilizer G x).toRightTranslation 1, z))
        (mfderiv (I.prod 𝓘(ℝ, V)) 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × V))
          (Quotient.mk (orbitRel (stabilizer G x) ((stabilizer G x).RightTranslation × U)))
          ((stabilizer G x).toRightTranslation 1, z) p) := by
  have hσ := e.hasMFDerivAt_symm_comp_subtype V
  intro w
  obtain ⟨p, hp⟩ := surjective_mfderiv_smul_slice hV hσ.mdifferentiableAt
    (by rw [ZeroMemClass.coe_zero, e.symm_zero])
    (fun v ↦ (DFunLike.congr_fun hσ.mfderiv v).trans (V.subtypeL_apply v)) w
  exact ⟨p, (U.mfderiv_tubeMap_mfderiv_quotientMk_eq_mfderiv_smul_symm F hz p.1 p.2).trans hp⟩

variable (F) in
/-- For a subspace `V` that meets the orbit tangent space `𝔤 · x` only in `0`, the composite of
the differentials of the tube map at `[1, 0]` and of the projection `G × U → G ×_H U` at `(1, 0)`
vanishes exactly on `𝔤_x × 0`, where `𝔤_x` is the isotropy algebra of `x`. -/
theorem mfderiv_tubeMap_mfderiv_quotientMk_eq_zero_iff [CompleteSpace E'] [IsManifold I' ∞ M]
    (hV : Disjoint ((InfinitesimalAction.fundamental I G I' M).orbitTangent x) V)
    (hz : (z : V) = 0) (ξ : GroupLieAlgebra I G) (v : V) :
    letI := BalancedProduct.rightTranslationChartedSpace (stabilizer G x) U I 𝓘(ℝ, V) F
    mfderiv 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × V)) I' U.tubeMap
        (Quotient.mk _ ((stabilizer G x).toRightTranslation 1, z))
        (mfderiv (I.prod 𝓘(ℝ, V)) 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × V))
          (Quotient.mk (orbitRel (stabilizer G x) ((stabilizer G x).RightTranslation × U)))
          ((stabilizer G x).toRightTranslation 1, z) (ξ, v)) = 0 ↔
      ξ ∈ (InfinitesimalAction.fundamental I G I' M).isotropy x ∧ v = 0 := by
  have hσ := e.hasMFDerivAt_symm_comp_subtype V
  rw [U.mfderiv_tubeMap_mfderiv_quotientMk_eq_mfderiv_smul_symm F hz ξ v]
  exact mfderiv_smul_slice_eq_zero_iff hV hσ.mdifferentiableAt
    (by rw [ZeroMemClass.coe_zero, e.symm_zero])
    (fun v ↦ (DFunLike.congr_fun hσ.mfderiv v).trans (V.subtypeL_apply v)) ξ v

variable (F) in
/-- **The projection is constant along the isotropy directions.** For `ξ` in the isotropy algebra
`𝔤_x`, the differential at `(1, 0)` of the projection `G × U → G ×_H U` vanishes on `(ξ, 0)`: the
curve `t ↦ (exp (t ξ), 0)` stays in the class `[1, 0]`, since `exp (t ξ)` lies in the stabilizer
of `x`, whose differentials fix `0`. -/
theorem mfderiv_quotientMk_apply_eq_zero_of_mem_isotropy [CompleteSpace E'] [IsManifold I' ∞ M]
    [T2Space M] [I'.Boundaryless] (hz : (z : V) = 0)
    {ξ : GroupLieAlgebra I G} (hξ : ξ ∈ (InfinitesimalAction.fundamental I G I' M).isotropy x) :
    letI := BalancedProduct.rightTranslationChartedSpace (stabilizer G x) U I 𝓘(ℝ, V) F
    mfderiv (I.prod 𝓘(ℝ, V)) 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × V))
      (Quotient.mk (orbitRel (stabilizer G x) ((stabilizer G x).RightTranslation × U)))
      ((stabilizer G x).toRightTranslation 1, z) (ξ, 0) = 0 := by
  let _ := BalancedProduct.rightTranslationChartedSpace (stabilizer G x) U I 𝓘(ℝ, V) F
  have : T2Space G := I.t2Space_of_lieGroup ∞
  have hπ := (BalancedProduct.isSubmersion_quotientMk_rightTranslation (K := stabilizer G x)
    (Z := U) (I := I) (IZ := 𝓘(ℝ, V)) (F := F)).contMDiff.mdifferentiableAt
      (x := ((stabilizer G x).toRightTranslation 1, z)) (by simp)
  -- The curve `γ t = (exp (t ξ), z)` in `G × U`, with velocity `(ξ, 0)` at `0`.
  let γ : ℝ → (stabilizer G x).RightTranslation × U :=
    fun t ↦ ((stabilizer G x).toRightTranslation (mulInvariantExp (I := I) (t • ξ)), z)
  have hγ : HasMFDerivAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, V)) γ 0
      (((1 : ℝ →L[ℝ] ℝ).smulRight ξ).prod 0) :=
    (hasMFDerivAt_mulInvariantExp_smul_zero (I := I) (G := G) ξ).prodMk
      (hasMFDerivAt_const (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, V)) z 0)
  -- It stays in the class `[1, z]`.
  have hconst : Quotient.mk (orbitRel (stabilizer G x) ((stabilizer G x).RightTranslation × U)) ∘
      γ = fun _ ↦ Quotient.mk _ ((stabilizer G x).toRightTranslation 1, z) := by
    funext t
    have hk : mulInvariantExp (I := I) (t • ξ) ∈ stabilizer G x :=
      (TauCeti.Lie.mem_isotropy_fundamental_iff.1 hξ) t
    have hkz : (⟨_, hk⟩ : stabilizer G x) • z = z := by
      refine Subtype.ext (Subtype.ext ?_)
      rw [coe_smul, hz, ZeroMemClass.coe_zero]
      exact (mfderiv I' I' (fun y : M ↦ mulInvariantExp (I := I) (t • ξ) • y) x).map_zero
    simp only [comp_apply, γ]
    rw [BalancedProduct.quotientMk_eq_mk_toRightTranslation,
      BalancedProduct.quotientMk_eq_mk_toRightTranslation, Equiv.symm_apply_apply,
      Equiv.symm_apply_apply, ← one_mul (mulInvariantExp (t • ξ))]
    exact (BalancedProduct.mk_toRightTranslation_mul 1 ⟨_, hk⟩ z).trans (congrArg _ hkz)
  have hγ0 : γ 0 = ((stabilizer G x).toRightTranslation 1, z) := by
    simp only [γ, zero_smul, mulInvariantExp_zero]
  have hπ' := hπ.hasMFDerivAt
  rw [← hγ0] at hπ'
  have h := (hπ'.comp 0 hγ).mfderiv
  rw [hconst, mfderiv_const] at h
  have h1 := DFunLike.congr_fun h (1 : ℝ)
  rw [hγ0] at h1
  convert h1.symm using 1
  -- The composite applied to `1` is `dπ (1 • ξ, 0)`.
  exact congrArg _ (Prod.ext (one_smul ℝ ξ).symm rfl)

variable (F) in
/-- **The tube map is a local diffeomorphism at `[1, 0]`** when `V` is a complement of the orbit
tangent space `𝔤 · x` in `T_x M`. Its differential there is onto, since its composite with the
differential of the projection `π : G × U → G ×_H U` is; and it is injective, since `dπ` is onto
and the composite vanishes only on `𝔤_x × 0`, which `dπ` kills. The inverse function theorem then
applies. Here `0` is any point `z` of `U` that is `0` in `V`. -/
theorem isLocalDiffeomorphAt_tubeMap_mk_one [CompleteSpace E'] [IsManifold I' ∞ M] [T2Space M]
    [I'.Boundaryless] (hV : IsCompl ((InfinitesimalAction.fundamental I G I' M).orbitTangent x) V)
    (hz : (z : V) = 0) :
    letI := BalancedProduct.rightTranslationChartedSpace (stabilizer G x) U I 𝓘(ℝ, V) F
    IsLocalDiffeomorphAt 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × V)) I' ∞ U.tubeMap
      (Quotient.mk _ ((stabilizer G x).toRightTranslation 1, z)) := by
  let _ := BalancedProduct.rightTranslationChartedSpace (stabilizer G x) U I 𝓘(ℝ, V) F
  have := BalancedProduct.isManifold_rightTranslation (K := stabilizer G x) (Z := U) (I := I)
    (IZ := 𝓘(ℝ, V)) (F := F)
  have hπ := (BalancedProduct.isSubmersion_quotientMk_rightTranslation (K := stabilizer G x)
    (Z := U) (I := I) (IZ := 𝓘(ℝ, V)) (F := F)).surjective_mfderiv (by simp)
      ((stabilizer G x).toRightTranslation 1, z)
  set L := mfderiv 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × V)) I' U.tubeMap
    (Quotient.mk _ ((stabilizer G x).toRightTranslation 1, z))
  have hsurj : Surjective L := fun w ↦ by
    obtain ⟨p, hp⟩ := U.surjective_mfderiv_tubeMap_mfderiv_quotientMk F hV.codisjoint.eq_top hz w
    exact ⟨_, hp⟩
  have hinj : Injective L := by
    refine (injective_iff_map_eq_zero L).2 fun w hw ↦ ?_
    obtain ⟨⟨ξ, v⟩, rfl⟩ := hπ w
    obtain ⟨hξ, rfl⟩ :=
      (U.mfderiv_tubeMap_mfderiv_quotientMk_eq_zero_iff F hV.disjoint hz ξ v).1 hw
    exact U.mfderiv_quotientMk_apply_eq_zero_of_mem_isotropy F hz hξ
  refine (isLocalDiffeomorphAt_iff_exists_mfderiv_eq
    (U.contMDiff_tubeMap (I := I) (F := F)).contMDiffOn isOpen_univ (mem_univ _)
    BoundarylessManifold.isInteriorPoint (by simp)).2
    ⟨(LinearEquiv.ofBijective L.toLinearMap ⟨hinj, hsurj⟩).toContinuousLinearEquiv, ?_⟩
  ext w
  -- `LinearEquiv.ofBijective_apply` does not match here, as the tangent spaces are type synonyms
  -- of the model spaces; the equivalence applies `L` by definition.
  rfl

variable (F) in
/-- **The tube map is a local diffeomorphism near the orbit.** For a complement `V` of the orbit
tangent space `𝔤 · x` in `T_x M` and a slice domain `U` of `V` containing `0`, there is a smaller
slice domain `U'`, again containing `0`, such that the tube map of `U` is a local diffeomorphism at
every class `[g, v]` with `v ∈ U'`. Indeed it is one at `[1, 0]`
(`isLocalDiffeomorphAt_tubeMap_mk_one`), hence at `[1, v]` for `v` near `0`, and the set of such
`v` is invariant under the stabilizer because `[1, h • v] = h • [1, v]` and local diffeomorphy of
the equivariant tube map is `G`-invariant (`SymplecticGeometry.isLocalDiffeomorphAt_smul_iff`);
the same invariance then moves `[1, v]` to `[g, v] = g • [1, v]`. -/
theorem exists_sliceDomain_isLocalDiffeomorphAt_tubeMap [CompleteSpace E'] [IsManifold I' ∞ M]
    [T2Space M] [I'.Boundaryless]
    (hV : IsCompl ((InfinitesimalAction.fundamental I G I' M).orbitTangent x) V)
    (h0 : (0 : E') ∈ U.carrier) :
    letI := BalancedProduct.rightTranslationChartedSpace (stabilizer G x) U I 𝓘(ℝ, V) F
    ∃ U' : SliceDomain e V, U'.carrier ⊆ U.carrier ∧ (0 : E') ∈ U'.carrier ∧
      ∀ (g : G) (z : U), ((z : V) : E') ∈ U'.carrier →
        IsLocalDiffeomorphAt 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × V)) I' ∞ U.tubeMap
          (BalancedProduct.mk _ ((stabilizer G x).toRightTranslation g) z) := by
  let _ := BalancedProduct.rightTranslationChartedSpace (stabilizer G x) U I 𝓘(ℝ, V) F
  have := BalancedProduct.contMDiffSMul_rightTranslation (K := stabilizer G x) (Z := U) (I := I)
    (IZ := 𝓘(ℝ, V)) (F := F)
  -- The points `z` of `U` at whose class `[1, z]` the tube map is a local diffeomorphism.
  let W : Set U := {z | IsLocalDiffeomorphAt 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × V)) I' ∞
    U.tubeMap (BalancedProduct.mk _ ((stabilizer G x).toRightTranslation 1) z)}
  have hW : IsOpen W := by
    refine isOpen_iff_mem_nhds.2 fun z hz ↦ ?_
    have hc : Continuous fun z : U ↦
        BalancedProduct.mk (stabilizer G x) ((stabilizer G x).toRightTranslation 1) z :=
      continuous_quotient_mk'.comp (continuous_const.prodMk continuous_id)
    exact hc.continuousAt.preimage_mem_nhds (IsLocalDiffeomorphAt.eventually hz)
  have hmem : ∀ {g : G} {z : U}, z ∈ W →
      IsLocalDiffeomorphAt 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × V)) I' ∞ U.tubeMap
        (BalancedProduct.mk _ ((stabilizer G x).toRightTranslation g) z) := fun {g z} hz ↦ by
    have h := (isLocalDiffeomorphAt_smul_iff (IG := I) U.tubeMap_smul g).2 hz
    rwa [BalancedProduct.smul_mk_toRightTranslation, mul_one] at h
  have hinj : Injective fun z : U ↦ ((z : V) : E') :=
    Subtype.val_injective.comp Subtype.val_injective
  refine ⟨⟨(fun z : U ↦ ((z : V) : E')) '' W, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rintro _ ⟨z, -, rfl⟩
    exact (z : V).property
  · -- In `V`, this set is the image of the open subset `W` of the open set `U`.
    have h : ((↑) : V → E') ⁻¹' ((fun z : U ↦ ((z : V) : E')) '' W) = (↑) '' W := by
      ext v
      refine ⟨fun ⟨z, hz, hzv⟩ ↦ ⟨z, hz, Subtype.val_injective hzv⟩, ?_⟩
      rintro ⟨z, hz, rfl⟩
      exact ⟨z, hz, rfl⟩
    rw [h]
    exact U.toOpens.isOpen.isOpenMap_subtypeVal W hW
  · rintro _ ⟨z, -, rfl⟩
    exact U.coe_mem_target z
  · rintro g hg _ ⟨z, hz, rfl⟩
    have h := (isLocalDiffeomorphAt_smul_iff (IG := I) U.tubeMap_smul g).2 hz
    rw [← Subgroup.coe_mk (stabilizer G x) g hg,
      ← BalancedProduct.mk_toRightTranslation_one_smul] at h
    -- Membership in `W` is local diffeomorphy at the class `[1, z]`.
    have h' := mem_image_of_mem (fun z : U ↦ ((z : V) : E')) (show _ ∈ W from h)
    rwa [U.coe_smul ⟨g, hg⟩ z] at h'
  · rintro _ ⟨z, -, rfl⟩
    exact U.coe_mem z
  · refine ⟨⟨0, U.mem_toOpens_iff.2 h0⟩, ?_, rfl⟩
    exact U.isLocalDiffeomorphAt_tubeMap_mk_one F hV rfl
  · rintro g z ⟨w, hw, hwz⟩
    obtain rfl := hinj hwz
    exact hmem hw

end Differential

end SliceDomain

end LinearizingChart

end SymplecticGeometry

end
