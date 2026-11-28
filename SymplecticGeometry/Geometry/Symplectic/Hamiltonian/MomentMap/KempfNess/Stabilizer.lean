/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.KempfNess.Basic
public import SymplecticGeometry.Geometry.Lie.Subgroup.IdentityComponent
public import SymplecticGeometry.Geometry.Lie.Subgroup.Restrict
public import SymplecticGeometry.Geometry.Lie.Exponential.Periods
public import SymplecticGeometry.Topology.Algebra.GroupAction.Stabilizer
import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic
import SymplecticGeometry.Topology.Connected.Basic
import SymplecticGeometry.Topology.Algebra.Group.Connected

/-!
# The stabilizer in the complexification of a zero of the moment map

Let the action of the complexification `Gc` of `G` on `M` be a complexified action, with `-μ` an
equivariant moment map for `σ` and the metric `g(u, w) = σ(u, J w)`. At a zero `x` of `μ`, the
stabilizer of `x` in `Gc` is read off from the polar decomposition `g = expI η * toHom u`: `g`
fixes `x` exactly when `u` fixes `x` and the fundamental vector field of `η` vanishes at `x`. In
other words, the polar decomposition maps the product of the isotropy algebra and the stabilizer
of `x` in `G` onto the stabilizer of `x` in `Gc`.

Being a homeomorphism that sends `(0, 1)` to `1`, the polar decomposition then carries the
connected component of `(0, 1)` in that product, which is the product of the isotropy algebra and
the identity component `H₀` of the stabilizer in `G`, onto the identity component `Gc₀` of the
stabilizer in `Gc`. With the Lie group structures that `H₀` and `Gc₀` get as closed subgroups,
this restriction is a diffeomorphism from the product of the Lie algebra of `H₀` and `H₀` onto
`Gc₀`: a polar decomposition of `Gc₀`.

The isotropy algebra of `x` in the Lie algebra of `Gc` is `C.lieMap 𝔥 ⊔ C.cplx (C.lieMap 𝔥)`, `𝔥`
that of `x` in the Lie algebra of `G`, so it is stable under `C.cplx`. As it is the image of the
Lie algebra of `Gc₀`, `C.cplx` gives that Lie algebra a complex structure which commutes with
brackets, and for which the Lie algebra of `H₀`, mapped by the restriction `H₀ → Gc₀` of
`C.toHom`, is maximal totally real. These are the complex structure and the maximal totally real
image of a complexification of `H₀` by `Gc₀`. Together with the restricted polar decomposition
they make `Gc₀` a complexification of `H₀`, whose exponential of imaginary directions and whose
nonzero periods are those of `C` and of `G`, read through the inclusions.

## Main results

* `SymplecticGeometry.IsComplexifiedAction.mem_stabilizer_iff_of_moment_eq_zero`: if `μ x = 0`,
  then `g` fixes `x` exactly when, for `(η, u) = C.polar.symm g`, the fundamental vector field of
  `η` vanishes at `x` and `u` fixes `x`.
* `SymplecticGeometry.IsComplexifiedAction.image_polar_isotropy_prod_stabilizer`: if `μ x = 0`,
  then `C.polar` maps `𝔤_x × G_x` onto `Gc_x`.
* `SymplecticGeometry.IsComplexifiedAction.image_polar_isotropy_prod_ambientConnectedComponentOfOne`
  (`H₀` and `Gc₀` being the identity components): it maps `𝔤_x × H₀` onto `Gc₀`.
* `SymplecticGeometry.IsComplexifiedAction.stabilizerPolar`: the restriction of `C.polar`, as a
  diffeomorphism from the product of the Lie algebra of `H₀` and `H₀` onto `Gc₀`, and
  `SymplecticGeometry.IsComplexifiedAction.coe_stabilizerPolar_apply`, its value.
* `SymplecticGeometry.IsComplexifiedAction.isotropy_eq_map_lieMap_sup_of_moment_eq_zero` and
  `SymplecticGeometry.IsComplexifiedAction.range_groupLieAlgebraMap_subtype_stabilizer_eq_sup`:
  the isotropy algebra of `x` in `Gc`, which is the image of the Lie algebra of `Gc₀`, is
  `C.lieMap 𝔥 ⊔ C.cplx (C.lieMap 𝔥)`.
* `SymplecticGeometry.IsComplexifiedAction.stabilizerCplx`: the complex structure of the Lie
  algebra of `Gc₀` that the inclusion intertwines with `C.cplx`
  (`SymplecticGeometry.IsComplexifiedAction.groupLieAlgebraMap_subtype_stabilizerCplx`); it
  commutes with brackets (`SymplecticGeometry.IsComplexifiedAction.stabilizerCplx_lie`).
* `SymplecticGeometry.IsComplexifiedAction.isMaximalTotallyReal_range_restrict`: the image of the
  Lie algebra of `H₀` under the restriction of `C.toHom` is maximal totally real for it.
* `SymplecticGeometry.IsComplexifiedAction.stabilizerComplexification`: `Gc₀` as a
  complexification of `H₀`, built from the restriction of `C.toHom`, `stabilizerCplx` and
  `stabilizerPolar`.
* `SymplecticGeometry.IsComplexifiedAction.stabilizerComplexification_expI`: its `expI`, read in
  `Gc`, is `C.expI` of the image in the Lie algebra of `G`; and
  `SymplecticGeometry.mem_nonzeroPeriods_of_stabilizer`: a nonzero period of `H₀` maps to one of
  `G`.

## Implementation notes

The proof follows [GeorgoulasRobbinSalamon2021], Lemma 2.3. If `g` fixes `x`, then
`y = toHom u • x` is again a zero of `μ` (`IsComplexifiedAction.moment_toHom_smul`), and
`expI η • y = x`; so `⟨μ, η⟩` takes the same value `0` at `y` and at `expI η • y`, and
`expI_smul_eq_self_of_moment_apply_le` gives `expI η • y = y`, that is `y = x`. Then `expI η`
fixes `x`, so does `expI (-η)`, and `moment_expI_neg_smul_apply_pos` rules out a nonzero
fundamental vector field of `η` at `x`. Conversely `expI η` fixes the zeros of the fundamental
vector field of `η` (`IsComplexifiedAction.expI_smul_smul_eq_self_iff`).

The restriction to the identity components, as a polar decomposition of `Gc₀`, follows
[GeorgoulasRobbinSalamon2021], proof of Theorem 12.5, Step 1 (arXiv v2). It is smooth in both
directions because its composites with the inclusions of the closed subgroups are
(`TauCeti.Lie.EmbeddedLieSubgroupData.isSmoothEmbedding_subtypeVal`,
`Manifold.IsSmoothEmbedding.contMDiff_iff_comp`). The first coordinate is read in the Lie algebra
of `G` through the differential at `1` of the inclusion `H₀ → G`, whose range is the isotropy
algebra (`TauCeti.Lie.EmbeddedLieSubgroupData.groupLieAlgebraEquivIsotropy`); a linear left
inverse of that differential makes the inverse map smooth in it.

The isotropy algebra in `Gc` is read off from
`IsComplexifiedAction.fundamentalVectorField_eq_zero_iff_of_moment_eq_zero`: the fundamental
vector field of `ζ` vanishes at `x` exactly when those of `C.re ζ` and `C.im ζ` do. The structures
on `Gc₀` and `H₀` are taken for any embedded Lie subgroup structures, those of
`TauCeti.Lie.EmbeddedLieSubgroupData.ofIsClosed` being one choice. The complex structure is
`C.cplx` carried through `TauCeti.Lie.EmbeddedLieSubgroupData.groupLieAlgebraEquivIsotropy` by
`TauCeti.AlmostComplexStructure.transport`; its
compatibility with brackets, and maximal total reality, are tested after the injective
differential of the inclusion `Gc₀ → Gc`, which preserves brackets
(`TauCeti.Lie.EmbeddedLieSubgroupData.groupLieAlgebraLieHom_subtypeVal`), using the commuting
square of `ContMDiffMonoidMorphism.groupLieAlgebraMap_subtype_groupLieAlgebraLieHom_restrict`.

The complexification of `H₀` uses the structures of
`TauCeti.Lie.EmbeddedLieSubgroupData.ofIsClosed` on both identity components. `C.toHom` maps `H₀`
into `Gc₀` because it is continuous and maps the stabilizer into the stabilizer. Its exponential
and its periods are compared with those of `C` and `G` through
`TauCeti.Lie.EmbeddedLieSubgroupData.coe_mulInvariantExp` and the injectivity of the differential
of the inclusion (`TauCeti.Lie.EmbeddedLieSubgroupData.injective_groupLieAlgebraMap_subtype`).

## References

* [V. Georgoulas, J. W. Robbin and D. A. Salamon, *The Moment-Weight Inequality and the
  Hilbert–Mumford Criterion*][GeorgoulasRobbinSalamon2021], Lemma 2.3, and the proof of
  Theorem 12.5, Step 1 (arXiv v2).
-/

public section

open _root_.Bundle Manifold TauCeti
open scoped Manifold ContDiff RealInnerProductSpace

namespace SymplecticGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {EC : Type*} [NormedAddCommGroup EC] [NormedSpace ℝ EC] [CompleteSpace EC]
  {HC : Type*} [TopologicalSpace HC] {IC : ModelWithCorners ℝ EC HC}
  {Gc : Type*} [TopologicalSpace Gc] [ChartedSpace HC Gc] [Group Gc] [LieGroup IC ∞ Gc]
  [T2Space Gc] [BoundarylessManifold IC Gc]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M]
  [MulAction G M] [MulAction Gc M] [ContMDiffSMul I I' ∞ G M] [ContMDiffSMul IC I' ∞ Gc M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I' x)]
  {σ : SmoothTwoForm I' M} {J : SmoothAlmostComplexStructure I' M}
  {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)} {C : LieComplexification I G IC Gc}

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

/-- **The stabilizer in `Gc` of a zero of the moment map.** For a complexified action on a
Hausdorff manifold without boundary, with `-μ` an equivariant moment map for `σ` and the metric
`g(u, w) = σ(u, J w)`, let `μ x = 0`. Then `g : Gc` fixes `x` exactly when, writing
`(η, u) = C.polar.symm g`, so that `g = C.expI η * C.toHom u`, the fundamental vector field of `η`
for the action of `G` vanishes at `x` and `u` fixes `x`. -/
theorem IsComplexifiedAction.mem_stabilizer_iff_of_moment_eq_zero [T2Space M]
    [BoundarylessManifold I' M] (h : IsComplexifiedAction C J)
    (hμ : σ.IsEquivariantMomentMap fun x ↦ -μ x)
    (hg : ∀ x (u w : TangentSpace I' x), ⟪u, w⟫ = σ.eval₂ x u (J x w)) {x : M} (hx : μ x = 0)
    (g : Gc) :
    g ∈ MulAction.stabilizer Gc x ↔
      fundamentalVectorField (I := I) (G := G) I' (C.polar.symm g).1 x = 0 ∧
        (C.polar.symm g).2 ∈ MulAction.stabilizer G x := by
  conv_lhs => rw [← C.expI_mul_toHom_polar_symm g]
  generalize C.polar.symm g = p
  -- The polar coordinates live in `E × G`; read the first as an element of the Lie algebra, as
  -- the lemmas on `C.expI` take it.
  obtain ⟨η, u⟩ : GroupLieAlgebra I G × G := p
  simp only [MulAction.mem_stabilizer_iff, mul_smul, h.toHom_smul]
  refine ⟨fun hfix ↦ ?_, fun ⟨hX, hu⟩ ↦ ?_⟩
  · -- `u • x` is a zero of `μ` that `expI η` carries to the zero `x`.
    have hy : μ (u • x) = 0 := by
      rw [← h.toHom_smul, h.moment_toHom_smul hμ, hx, map_zero]
    have hux : u • x = x :=
      (expI_smul_eq_self_of_moment_apply_le h hμ.toIsMomentMap hg
        (by rw [hfix, hy, hx])).symm.trans hfix
    rw [hux] at hfix
    refine ⟨not_not.1 fun hne ↦ ?_, hux⟩
    -- `expI (-η)` fixes `x`, so `⟨μ, η⟩` would be positive at `x`.
    have hpos := moment_expI_neg_smul_apply_pos h hμ.toIsMomentMap hg hx hne
    rw [C.expI_neg, inv_smul_eq_iff.2 hfix.symm, hx, LinearMap.zero_apply] at hpos
    exact lt_irrefl 0 hpos
  · simpa [hu] using h.expI_smul_smul_eq_self_iff.2 hX 1

/-- **The polar decomposition of the stabilizer of a zero of the moment map.** In the setting of
`IsComplexifiedAction.mem_stabilizer_iff_of_moment_eq_zero`, `C.polar` maps the product of the
isotropy algebra `𝔤_x` and the stabilizer `G_x` onto the stabilizer `Gc_x`. -/
theorem IsComplexifiedAction.image_polar_isotropy_prod_stabilizer [T2Space M]
    [BoundarylessManifold I' M] (h : IsComplexifiedAction C J)
    (hμ : σ.IsEquivariantMomentMap fun x ↦ -μ x)
    (hg : ∀ x (u w : TangentSpace I' x), ⟪u, w⟫ = σ.eval₂ x u (J x w)) {x : M} (hx : μ x = 0) :
    C.polar '' (((InfinitesimalAction.fundamental I G I' M).isotropy x : Set (GroupLieAlgebra I G))
      ×ˢ (MulAction.stabilizer G x : Set G) : Set (E × G)) = MulAction.stabilizer Gc x := by
  ext g
  refine ⟨?_, fun hgx ↦ ⟨C.polar.symm g, ?_, C.polar.apply_symm_apply g⟩⟩
  · rintro ⟨p, ⟨hp₁, hp₂⟩, rfl⟩
    rw [SetLike.mem_coe, h.mem_stabilizer_iff_of_moment_eq_zero hμ hg hx, C.polar.symm_apply_apply]
    exact ⟨by simpa using hp₁, hp₂⟩
  · rw [SetLike.mem_coe, h.mem_stabilizer_iff_of_moment_eq_zero hμ hg hx] at hgx
    exact ⟨by simpa using hgx.1, hgx.2⟩

/-- **The polar decomposition of the identity component of the stabilizer of a zero of the
moment map.** In the setting of `IsComplexifiedAction.mem_stabilizer_iff_of_moment_eq_zero`,
`C.polar` maps the product of the isotropy algebra `𝔤_x` and the identity component of `G_x` onto
the identity component of `Gc_x`. -/
theorem IsComplexifiedAction.image_polar_isotropy_prod_ambientConnectedComponentOfOne
    [IsTopologicalGroup G] [IsTopologicalGroup Gc] [T2Space M]
    [BoundarylessManifold I' M] (h : IsComplexifiedAction C J)
    (hμ : σ.IsEquivariantMomentMap fun x ↦ -μ x)
    (hg : ∀ x (u w : TangentSpace I' x), ⟪u, w⟫ = σ.eval₂ x u (J x w)) {x : M} (hx : μ x = 0) :
    C.polar '' (((InfinitesimalAction.fundamental I G I' M).isotropy x : Set (GroupLieAlgebra I G))
      ×ˢ ((MulAction.stabilizer G x).ambientConnectedComponentOfOne : Set G) : Set (E × G)) =
        (MulAction.stabilizer Gc x).ambientConnectedComponentOfOne := by
  have h0 : ((0 : E), (1 : G)) ∈
      (((InfinitesimalAction.fundamental I G I' M).isotropy x : Set (GroupLieAlgebra I G)) ×ˢ
        (MulAction.stabilizer G x : Set G) : Set (E × G)) :=
    ⟨zero_mem _, one_mem _⟩
  have h𝔥 : connectedComponentIn
      (((InfinitesimalAction.fundamental I G I' M).isotropy x : Set (GroupLieAlgebra I G)))
        (0 : GroupLieAlgebra I G) = (InfinitesimalAction.fundamental I G I' M).isotropy x :=
    (((InfinitesimalAction.fundamental I G I' M).isotropy x).toSubmodule.convex).isPreconnected
      |>.connectedComponentIn (zero_mem _)
  have key := C.polar.toHomeomorph.image_connectedComponentIn h0
  rw [Diffeomorph.coe_toHomeomorph, h.image_polar_isotropy_prod_stabilizer hμ hg hx,
    C.polar_zero_apply, map_one] at key
  rw [Subgroup.coe_ambientConnectedComponentOfOne, Subgroup.coe_ambientConnectedComponentOfOne,
    ← key]
  refine congrArg (C.polar '' ·) ?_
  exact ((connectedComponentIn_prod _ (MulAction.stabilizer G x : Set G) _ 1).trans
    (congrArg (· ×ˢ connectedComponentIn (MulAction.stabilizer G x : Set G) 1) h𝔥)).symm

section StabilizerPolar

open Lie

attribute [local instance] ContMDiffMul.boundarylessManifold

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ EC] [T2Space G] [IsTopologicalGroup G]
  [IsTopologicalGroup Gc] [I.Boundaryless] [IC.Boundaryless] [T2Space M]
  [BoundarylessManifold I' M]

/-- **The polar decomposition of the identity component of the stabilizer of a zero of the moment
map.** In the setting of `IsComplexifiedAction.mem_stabilizer_iff_of_moment_eq_zero`, let `H₀` and
`Gc₀` be the identity components of the stabilizers of `x` in `G` and in `Gc`, each with the Lie
group structure of a closed subgroup (`TauCeti.Lie.EmbeddedLieSubgroupData.ofIsClosed`), modelled
on its Lie algebra. Then `C.polar` restricts to a diffeomorphism from the product of the Lie
algebra `E₀` of `H₀` and `H₀` onto `Gc₀`, sending `(ξ, u)` to `C.expI ξ * C.toHom u`, where `ξ` is
read in the Lie algebra of `G` through the differential at `1` of the inclusion `H₀ → G`
(`IsComplexifiedAction.coe_stabilizerPolar_apply`). -/
noncomputable def IsComplexifiedAction.stabilizerPolar (h : IsComplexifiedAction C J)
    (hμ : σ.IsEquivariantMomentMap fun x ↦ -μ x)
    (hg : ∀ x (u w : TangentSpace I' x), ⟪u, w⟫ = σ.eval₂ x u (J x w)) {x : M} (hx : μ x = 0) :
    let H₀ := (MulAction.stabilizer G x).ambientConnectedComponentOfOne
    let Gc₀ := (MulAction.stabilizer Gc x).ambientConnectedComponentOfOne
    let E₀ := (lieSubalgebraOfSubgroup (I := I) H₀).toSubmodule
    let EC₀ := (lieSubalgebraOfSubgroup (I := IC) Gc₀).toSubmodule
    let _ := (EmbeddedLieSubgroupData.ofIsClosed (I := I)
      (MulAction.isClosed_ambientConnectedComponentOfOne_stabilizer
        (ContMDiffSMul.contMDiff_smul_const (I := I) (I' := I') (n := ∞) (G := G)
          x).continuous)).chartedSpace
    let _ := (EmbeddedLieSubgroupData.ofIsClosed (I := IC)
      (MulAction.isClosed_ambientConnectedComponentOfOne_stabilizer
        (ContMDiffSMul.contMDiff_smul_const (I := IC) (I' := I') (n := ∞) (G := Gc)
          x).continuous)).chartedSpace
    (E₀ × H₀) ≃ₘ⟮𝓘(ℝ, E₀).prod 𝓘(ℝ, E₀), 𝓘(ℝ, EC₀)⟯ Gc₀ :=
  let dH := EmbeddedLieSubgroupData.ofIsClosed (I := I)
    (MulAction.isClosed_ambientConnectedComponentOfOne_stabilizer
      (ContMDiffSMul.contMDiff_smul_const (I := I) (I' := I') (n := ∞) (G := G) x).continuous)
  let dK := EmbeddedLieSubgroupData.ofIsClosed (I := IC)
    (MulAction.isClosed_ambientConnectedComponentOfOne_stabilizer
      (ContMDiffSMul.contMDiff_smul_const (I := IC) (I' := I') (n := ∞) (G := Gc) x).continuous)
  let _ := dH.chartedSpace
  let _ := dK.chartedSpace
  haveI := dH.lieGroup
  haveI := dK.lieGroup
  let e := dH.groupLieAlgebraEquivIsotropy (I' := I')
  let ι := (MulAction.stabilizer G x).ambientConnectedComponentOfOne.subtype.groupLieAlgebraMap
    𝓘(ℝ, (lieSubalgebraOfSubgroup (I := I)
      (MulAction.stabilizer G x).ambientConnectedComponentOfOne).toSubmodule) I
  have himg := h.image_polar_isotropy_prod_ambientConnectedComponentOfOne hμ hg hx
  have hmem (g : (MulAction.stabilizer Gc x).ambientConnectedComponentOfOne) :
      C.polar.symm g ∈
        (((InfinitesimalAction.fundamental I G I' M).isotropy x : Set (GroupLieAlgebra I G)) ×ˢ
          ((MulAction.stabilizer G x).ambientConnectedComponentOfOne : Set G) : Set (E × G)) := by
    have hg₀ := g.property
    rw [← SetLike.mem_coe, ← himg] at hg₀
    obtain ⟨p, hp, hpg⟩ := hg₀
    rw [← hpg, C.polar.symm_apply_apply]
    exact hp
  { toFun p := ⟨C.polar ((e p.1 : GroupLieAlgebra I G), p.2), by
      rw [← SetLike.mem_coe, ← himg]
      exact Set.mem_image_of_mem _ ⟨(e p.1).property, p.2.property⟩⟩
    invFun g := (e.symm ⟨(C.polar.symm g).1, (hmem g).1⟩, ⟨(C.polar.symm g).2, (hmem g).2⟩)
    left_inv p := by
      refine Prod.ext ((LinearEquiv.symm_apply_eq e).2 (Subtype.ext ?_)) (Subtype.ext ?_) <;>
        simp only [Diffeomorph.symm_apply_apply]
    right_inv g := Subtype.ext <| by
      simp only [LinearEquiv.apply_symm_apply, Prod.mk.eta, Diffeomorph.apply_symm_apply]
    contMDiff_toFun := by
      refine dK.isSmoothEmbedding_subtypeVal.contMDiff_iff_comp.2 ?_
      refine (C.polar.contMDiff.comp ((ι.contMDiff.comp contMDiff_fst).prodMk
        (dH.contMDiff_subtypeVal.comp contMDiff_snd))).congr fun p ↦ ?_
      exact congrArg (fun v ↦ C.polar (v, (p.2 : G)))
        (dH.coe_groupLieAlgebraEquivIsotropy (I' := I') p.1)
    contMDiff_invFun := by
      -- A linear left inverse of `ι` reads off the first component.
      obtain ⟨L, hL⟩ := ι.toLinearMap.exists_leftInverse_of_injective
        (LinearMap.ker_eq_bot.2 dH.injective_groupLieAlgebraMap_subtype)
      refine ContMDiff.prodMk ?_ ?_
      · refine (L.toContinuousLinearMap.contMDiff.comp (contMDiff_fst.comp
          (C.polar.symm.contMDiff.comp dK.contMDiff_subtypeVal))).congr fun g ↦ ?_
        exact (LinearMap.congr_fun hL _).symm.trans (congrArg L
          (dH.groupLieAlgebraMap_subtype_groupLieAlgebraEquivIsotropy_symm (I' := I')
            ⟨_, (hmem g).1⟩))
      · refine dH.isSmoothEmbedding_subtypeVal.contMDiff_iff_comp.2 ?_
        exact contMDiff_snd.comp (C.polar.symm.contMDiff.comp dK.contMDiff_subtypeVal) }

/-- The value of `IsComplexifiedAction.stabilizerPolar` at `(ξ, u)`, read in `Gc`, is
`C.expI ξ' * C.toHom u`, where `ξ'` is the image of `ξ` in the Lie algebra of `G` under the
differential at `1` of the inclusion `H₀ → G`. -/
theorem IsComplexifiedAction.coe_stabilizerPolar_apply (h : IsComplexifiedAction C J)
    (hμ : σ.IsEquivariantMomentMap fun x ↦ -μ x)
    (hg : ∀ x (u w : TangentSpace I' x), ⟪u, w⟫ = σ.eval₂ x u (J x w)) {x : M} (hx : μ x = 0) :
    let H₀ := (MulAction.stabilizer G x).ambientConnectedComponentOfOne
    let E₀ := (lieSubalgebraOfSubgroup (I := I) H₀).toSubmodule
    let _ := (EmbeddedLieSubgroupData.ofIsClosed (I := I)
      (MulAction.isClosed_ambientConnectedComponentOfOne_stabilizer
        (ContMDiffSMul.contMDiff_smul_const (I := I) (I' := I') (n := ∞) (G := G)
          x).continuous)).chartedSpace
    ∀ (ξ : E₀) (u : H₀), (h.stabilizerPolar hμ hg hx (ξ, u) : Gc) =
      C.expI (H₀.subtype.groupLieAlgebraMap 𝓘(ℝ, E₀) I ξ) * C.toHom u := by
  intro H₀ E₀ _ ξ u
  exact (C.polar_apply _ _).trans (congrArg (C.expI · * C.toHom u)
    (EmbeddedLieSubgroupData.coe_groupLieAlgebraEquivIsotropy (I' := I') _ ξ))

end StabilizerPolar

/-! ### The complex structure of the Lie algebra of the identity component of `Gc_x` -/

section StabilizerCplx

open Lie

attribute [local instance] ContMDiffMul.boundarylessManifold

variable [FiniteDimensional ℝ E]

/-- **The isotropy algebra in `Gc` of a zero of the moment map.** In the setting of
`IsComplexifiedAction.mem_stabilizer_iff_of_moment_eq_zero`, the isotropy algebra of `x` for the
action of `Gc` is `C.lieMap 𝔥 ⊔ C.cplx (C.lieMap 𝔥)`, where `𝔥` is the isotropy algebra of `x`
for the action of `G`. -/
theorem IsComplexifiedAction.isotropy_eq_map_lieMap_sup_of_moment_eq_zero
    (h : IsComplexifiedAction C J) (hμ : σ.IsEquivariantMomentMap fun x ↦ -μ x)
    (hg : ∀ x (u w : TangentSpace I' x), ⟪u, w⟫ = σ.eval₂ x u (J x w)) {x : M} (hx : μ x = 0) :
    ((InfinitesimalAction.fundamental IC Gc I' M).isotropy x).toSubmodule =
      ((InfinitesimalAction.fundamental I G I' M).isotropy x).toSubmodule.map
          C.lieMap.toLinearMap ⊔
        (((InfinitesimalAction.fundamental I G I' M).isotropy x).toSubmodule.map
          C.lieMap.toLinearMap).map C.cplx.toLinearMap := by
  ext ζ
  simp only [LieSubalgebra.mem_toSubmodule, InfinitesimalAction.mem_isotropy_iff,
    InfinitesimalAction.fundamental_apply, Submodule.mem_sup, Submodule.mem_map,
    LieHom.coe_toLinearMap]
  rw [h.fundamentalVectorField_eq_zero_iff_of_moment_eq_zero hμ hg hx]
  constructor
  · rintro ⟨hre, him⟩
    exact ⟨_, ⟨C.re ζ, hre, rfl⟩, _, ⟨C.lieMap (C.im ζ), ⟨C.im ζ, him, rfl⟩, rfl⟩,
      C.lieMap_re_add_cplx_lieMap_im ζ⟩
  · rintro ⟨_, ⟨a, ha, rfl⟩, _, ⟨_, ⟨b, hb, rfl⟩, rfl⟩, rfl⟩
    rw [map_add, map_add, C.re_lieMap, C.im_lieMap, C.re_cplx_lieMap, C.im_cplx_lieMap, add_zero,
      zero_add]
    exact ⟨ha, hb⟩

/-- In the setting of `IsComplexifiedAction.mem_stabilizer_iff_of_moment_eq_zero`, the isotropy
algebra of `x` for the action of `Gc` is stable under `C.cplx`. -/
theorem IsComplexifiedAction.cplx_mem_isotropy_of_moment_eq_zero (h : IsComplexifiedAction C J)
    (hμ : σ.IsEquivariantMomentMap fun x ↦ -μ x)
    (hg : ∀ x (u w : TangentSpace I' x), ⟪u, w⟫ = σ.eval₂ x u (J x w)) {x : M} (hx : μ x = 0)
    {ζ : GroupLieAlgebra IC Gc} (hζ : ζ ∈ (InfinitesimalAction.fundamental IC Gc I' M).isotropy x) :
    C.cplx ζ ∈ (InfinitesimalAction.fundamental IC Gc I' M).isotropy x := by
  rw [InfinitesimalAction.mem_isotropy_iff, InfinitesimalAction.fundamental_apply,
    h.fundamentalVectorField_eq_zero_iff_of_moment_eq_zero hμ hg hx] at hζ ⊢
  rw [C.re_cplx, C.im_cplx, ← InfinitesimalAction.fundamental_apply, map_neg,
    InfinitesimalAction.fundamental_apply, Pi.neg_apply, neg_eq_zero]
  exact hζ.symm

variable [T2Space M] [BoundarylessManifold I' M] [IsTopologicalGroup Gc] [FiniteDimensional ℝ EC]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- **The tangent space at `1` of the identity component of `Gc_x`.** In the setting of
`IsComplexifiedAction.mem_stabilizer_iff_of_moment_eq_zero`, for any embedded Lie subgroup
structure on the identity component `Gc₀` of the stabilizer of `x` in `Gc`, the differential at
`1` of the inclusion `Gc₀ → Gc` has range `C.lieMap 𝔥 ⊔ C.cplx (C.lieMap 𝔥)`, where `𝔥` is the
isotropy algebra of `x` for the action of `G`. -/
theorem IsComplexifiedAction.range_groupLieAlgebraMap_subtype_stabilizer_eq_sup
    (h : IsComplexifiedAction C J) (hμ : σ.IsEquivariantMomentMap fun x ↦ -μ x)
    (hg : ∀ x (u w : TangentSpace I' x), ⟪u, w⟫ = σ.eval₂ x u (J x w)) {x : M} (hx : μ x = 0)
    (d : EmbeddedLieSubgroupData IC (MulAction.stabilizer Gc x).ambientConnectedComponentOfOne F) :
    let _ := d.chartedSpace
    LinearMap.range
        ((MulAction.stabilizer Gc x).ambientConnectedComponentOfOne.subtype.groupLieAlgebraMap
          𝓘(ℝ, F) IC).toLinearMap =
      ((InfinitesimalAction.fundamental I G I' M).isotropy x).toSubmodule.map
          C.lieMap.toLinearMap ⊔
        (((InfinitesimalAction.fundamental I G I' M).isotropy x).toSubmodule.map
          C.lieMap.toLinearMap).map C.cplx.toLinearMap :=
  (d.range_groupLieAlgebraMap_subtype_stabilizer (I' := I')).trans
    (h.isotropy_eq_map_lieMap_sup_of_moment_eq_zero hμ hg hx)

/-- **The complex structure of the Lie algebra of the identity component of `Gc_x`.** In the
setting of `IsComplexifiedAction.mem_stabilizer_iff_of_moment_eq_zero`, let `Gc₀` be the identity
component of the stabilizer of `x` in `Gc`, with an embedded Lie subgroup structure `d`. The
differential at `1` of the inclusion `Gc₀ → Gc` identifies the tangent space of `Gc₀` at `1` with
the isotropy algebra of `x` in the Lie algebra of `Gc`, which `C.cplx` preserves; this is `C.cplx`
read through that identification
(`IsComplexifiedAction.groupLieAlgebraMap_subtype_stabilizerCplx`). -/
noncomputable def IsComplexifiedAction.stabilizerCplx (h : IsComplexifiedAction C J)
    (hμ : σ.IsEquivariantMomentMap fun x ↦ -μ x)
    (hg : ∀ x (u w : TangentSpace I' x), ⟪u, w⟫ = σ.eval₂ x u (J x w)) {x : M} (hx : μ x = 0)
    (d : EmbeddedLieSubgroupData IC (MulAction.stabilizer Gc x).ambientConnectedComponentOfOne F) :
    let _ := d.chartedSpace
    AlmostComplexStructure
      (GroupLieAlgebra 𝓘(ℝ, F) (MulAction.stabilizer Gc x).ambientConnectedComponentOfOne) :=
  let _ := d.chartedSpace
  (C.cplx.restrict _ fun _ hζ ↦ h.cplx_mem_isotropy_of_moment_eq_zero hμ hg hx hζ).transport
    (d.groupLieAlgebraEquivIsotropy (I' := I')).symm

/-- The inclusion of the identity component `Gc₀` of `Gc_x` intertwines
`IsComplexifiedAction.stabilizerCplx` with `C.cplx`: the differential at `1` of `Gc₀ → Gc` sends
`stabilizerCplx ζ` to `C.cplx` of the image of `ζ`. -/
theorem IsComplexifiedAction.groupLieAlgebraMap_subtype_stabilizerCplx
    (h : IsComplexifiedAction C J) (hμ : σ.IsEquivariantMomentMap fun x ↦ -μ x)
    (hg : ∀ x (u w : TangentSpace I' x), ⟪u, w⟫ = σ.eval₂ x u (J x w)) {x : M} (hx : μ x = 0)
    (d : EmbeddedLieSubgroupData IC (MulAction.stabilizer Gc x).ambientConnectedComponentOfOne F) :
    let _ := d.chartedSpace
    ∀ ζ, (MulAction.stabilizer Gc x).ambientConnectedComponentOfOne.subtype.groupLieAlgebraMap
        𝓘(ℝ, F) IC (h.stabilizerCplx hμ hg hx d ζ) =
      C.cplx ((MulAction.stabilizer Gc x).ambientConnectedComponentOfOne.subtype.groupLieAlgebraMap
        𝓘(ℝ, F) IC ζ) := by
  let _ := d.chartedSpace
  dsimp only
  intro ζ
  rw [← d.coe_groupLieAlgebraEquivIsotropy (I' := I'),
    ← d.coe_groupLieAlgebraEquivIsotropy (I' := I')]
  simp only [stabilizerCplx, AlmostComplexStructure.transport_apply, LinearEquiv.symm_symm,
    LinearEquiv.apply_symm_apply, AlmostComplexStructure.coe_restrict_apply]

/-- `IsComplexifiedAction.stabilizerCplx` commutes with brackets:
`stabilizerCplx ⁅ζ, ζ'⁆ = ⁅ζ, stabilizerCplx ζ'⁆`, as `C.cplx` does
(`LieComplexification.cplx_lie`). -/
theorem IsComplexifiedAction.stabilizerCplx_lie (h : IsComplexifiedAction C J)
    (hμ : σ.IsEquivariantMomentMap fun x ↦ -μ x)
    (hg : ∀ x (u w : TangentSpace I' x), ⟪u, w⟫ = σ.eval₂ x u (J x w)) {x : M} (hx : μ x = 0)
    (d : EmbeddedLieSubgroupData IC (MulAction.stabilizer Gc x).ambientConnectedComponentOfOne F) :
    let _ := d.chartedSpace
    let _ := d.lieGroup
    ∀ ζ ζ' : GroupLieAlgebra 𝓘(ℝ, F) (MulAction.stabilizer Gc x).ambientConnectedComponentOfOne,
      h.stabilizerCplx hμ hg hx d ⁅ζ, ζ'⁆ = ⁅ζ, h.stabilizerCplx hμ hg hx d ζ'⁆ := by
  let _ := d.chartedSpace
  let _ := d.lieGroup
  dsimp only
  intro ζ ζ'
  have hι := d.groupLieAlgebraLieHom_subtypeVal
  apply d.injective_groupLieAlgebraMap_subtype
  rw [h.groupLieAlgebraMap_subtype_stabilizerCplx, ← hι, ← hι, LieHom.map_lie, LieHom.map_lie,
    hι, hι, hι, h.groupLieAlgebraMap_subtype_stabilizerCplx, C.cplx_lie]

variable [T2Space G] [IsTopologicalGroup G] [IC.Boundaryless]
  {F₀ : Type*} [NormedAddCommGroup F₀] [NormedSpace ℝ F₀] [FiniteDimensional ℝ F₀]

/-- **The Lie algebra of `H₀` is maximal totally real in that of `Gc₀`.** In the setting of
`IsComplexifiedAction.mem_stabilizer_iff_of_moment_eq_zero`, let `H₀` and `Gc₀` be the identity
components of the stabilizers of `x` in `G` and in `Gc`, with embedded Lie subgroup structures `dH`
and `d`, and let `C.toHom` map `H₀` into `Gc₀`. Then the range of the Lie algebra map of the
restriction `H₀ → Gc₀` of `C.toHom` is maximal totally real for
`IsComplexifiedAction.stabilizerCplx`. -/
theorem IsComplexifiedAction.isMaximalTotallyReal_range_restrict (h : IsComplexifiedAction C J)
    (hμ : σ.IsEquivariantMomentMap fun x ↦ -μ x)
    (hg : ∀ x (u w : TangentSpace I' x), ⟪u, w⟫ = σ.eval₂ x u (J x w)) {x : M} (hx : μ x = 0)
    (dH : EmbeddedLieSubgroupData I (MulAction.stabilizer G x).ambientConnectedComponentOfOne F₀)
    (d : EmbeddedLieSubgroupData IC (MulAction.stabilizer Gc x).ambientConnectedComponentOfOne F)
    (hmaps : Set.MapsTo C.toHom (MulAction.stabilizer G x).ambientConnectedComponentOfOne
      (MulAction.stabilizer Gc x).ambientConnectedComponentOfOne) :
    let _ := dH.chartedSpace
    let _ := d.chartedSpace
    let _ := dH.lieGroup
    let _ := d.lieGroup
    IsMaximalTotallyReal (h.stabilizerCplx hμ hg hx d).toLinearMap
      (LinearMap.range (C.toHom.restrict dH d hmaps).groupLieAlgebraLieHom.toLinearMap) := by
  let _ := dH.chartedSpace
  let _ := d.chartedSpace
  let _ := dH.lieGroup
  let _ := d.lieGroup
  dsimp only
  set 𝔥 := ((InfinitesimalAction.fundamental I G I' M).isotropy x).toSubmodule
  set R := LinearMap.range (C.toHom.restrict dH d hmaps).groupLieAlgebraLieHom.toLinearMap
  set ι := ((MulAction.stabilizer Gc x).ambientConnectedComponentOfOne.subtype.groupLieAlgebraMap
    𝓘(ℝ, F) IC).toLinearMap
  have hι : Function.Injective ι := d.injective_groupLieAlgebraMap_subtype
  -- Through the inclusion, `R` is `C.lieMap 𝔥`, by the commuting square of the restriction.
  have hR : R.map ι = 𝔥.map C.lieMap.toLinearMap := by
    have hsq : ι ∘ₗ (C.toHom.restrict dH d hmaps).groupLieAlgebraLieHom.toLinearMap =
        C.lieMap.toLinearMap ∘ₗ
          ((MulAction.stabilizer G x).ambientConnectedComponentOfOne.subtype.groupLieAlgebraMap
            𝓘(ℝ, F₀) I).toLinearMap :=
      LinearMap.ext fun ζ ↦
        (C.toHom.groupLieAlgebraMap_subtype_groupLieAlgebraLieHom_restrict dH d hmaps ζ).trans
          (by
            simp only [C.lieMap_def, ContMDiffMonoidMorphism.toLinearMap_groupLieAlgebraLieHom,
              ContMDiffMonoidMorphism.coe_groupLieAlgebraLieHom, LinearMap.coe_comp,
              ContinuousLinearMap.coe_coe, Function.comp_apply])
    rw [← LinearMap.range_comp, hsq, LinearMap.range_comp,
      dH.range_groupLieAlgebraMap_subtype_stabilizer (I' := I')]
  have hJ : ι ∘ₗ (h.stabilizerCplx hμ hg hx d).toLinearMap = C.cplx.toLinearMap ∘ₗ ι :=
    LinearMap.ext (h.groupLieAlgebraMap_subtype_stabilizerCplx hμ hg hx d)
  have hRJ : (R.map (h.stabilizerCplx hμ hg hx d).toLinearMap).map ι =
      (𝔥.map C.lieMap.toLinearMap).map C.cplx.toLinearMap := by
    rw [← Submodule.map_comp, hJ, Submodule.map_comp, hR]
  have hle : 𝔥.map C.lieMap.toLinearMap ≤ LinearMap.range C.lieMap.toLinearMap :=
    LinearMap.map_le_range
  refine (isMaximalTotallyReal_iff _ _).2
    ⟨disjoint_iff.2 (Submodule.map_injective_of_injective hι ?_),
      codisjoint_iff.2 (Submodule.map_injective_of_injective hι ?_)⟩
  · rw [Submodule.map_inf _ hι, hR, hRJ, Submodule.map_bot]
    exact (C.isMaximalTotallyReal_range_lieMap.disjoint.mono hle (Submodule.map_mono hle)).eq_bot
  · rw [Submodule.map_sup, hR, hRJ, Submodule.map_top,
      h.range_groupLieAlgebraMap_subtype_stabilizer_eq_sup hμ hg hx d]

end StabilizerCplx

/-! ### The complexification of the identity component of `G_x` -/

section StabilizerComplexification

open Lie

attribute [local instance] ContMDiffMul.boundarylessManifold

omit [FiniteDimensional ℝ E'] [ContMDiffSMul I I' ∞ G M] [ContMDiffSMul IC I' ∞ Gc M]
  [RiemannianBundle fun x : M ↦ TangentSpace I' x] in
/-- For a complexified action, `C.toHom` maps the identity component of the stabilizer of `x` in
`G` into that of the stabilizer of `x` in `Gc`: it is continuous, sends `1` to `1`, and maps the
one stabilizer into the other. -/
theorem IsComplexifiedAction.mapsTo_toHom_ambientConnectedComponentOfOne_stabilizer
    [IsTopologicalGroup G] [IsTopologicalGroup Gc] (h : IsComplexifiedAction C J) (x : M) :
    Set.MapsTo C.toHom (MulAction.stabilizer G x).ambientConnectedComponentOfOne
      (MulAction.stabilizer Gc x).ambientConnectedComponentOfOne := by
  refine Subgroup.mapsTo_ambientConnectedComponentOfOne_of_mapsTo
    C.toHom.contMDiff_toFun.continuous (fun u hu ↦ ?_) (map_one C.toHom)
  rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff, h.toHom_smul]
  exact hu

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ EC] [T2Space G] [IsTopologicalGroup G]
  [IsTopologicalGroup Gc] [I.Boundaryless] [IC.Boundaryless] [T2Space M]
  [BoundarylessManifold I' M]

/-- **The complexification of the identity component of the stabilizer of a zero of the moment
map.** In the setting of `IsComplexifiedAction.mem_stabilizer_iff_of_moment_eq_zero`, let `H₀` and
`Gc₀` be the identity components of the stabilizers of `x` in `G` and in `Gc`, each with the Lie
group structure of a closed subgroup (`TauCeti.Lie.EmbeddedLieSubgroupData.ofIsClosed`), modelled
on its Lie algebra. Then `Gc₀` is a complexification of `H₀`: its inclusion is the restriction of
`C.toHom`, its complex structure is `C.cplx` read on the Lie algebra of `Gc₀`
(`IsComplexifiedAction.stabilizerCplx`), and its polar decomposition is the restriction of
`C.polar` (`IsComplexifiedAction.stabilizerPolar`). -/
noncomputable def IsComplexifiedAction.stabilizerComplexification (h : IsComplexifiedAction C J)
    (hμ : σ.IsEquivariantMomentMap fun x ↦ -μ x)
    (hg : ∀ x (u w : TangentSpace I' x), ⟪u, w⟫ = σ.eval₂ x u (J x w)) {x : M} (hx : μ x = 0) :
    let H₀ := (MulAction.stabilizer G x).ambientConnectedComponentOfOne
    let Gc₀ := (MulAction.stabilizer Gc x).ambientConnectedComponentOfOne
    let E₀ := (lieSubalgebraOfSubgroup (I := I) H₀).toSubmodule
    let EC₀ := (lieSubalgebraOfSubgroup (I := IC) Gc₀).toSubmodule
    let dH := EmbeddedLieSubgroupData.ofIsClosed (I := I)
      (MulAction.isClosed_ambientConnectedComponentOfOne_stabilizer
        (ContMDiffSMul.contMDiff_smul_const (I := I) (I' := I') (n := ∞) (G := G) x).continuous)
    let dK := EmbeddedLieSubgroupData.ofIsClosed (I := IC)
      (MulAction.isClosed_ambientConnectedComponentOfOne_stabilizer
        (ContMDiffSMul.contMDiff_smul_const (I := IC) (I' := I') (n := ∞) (G := Gc) x).continuous)
    let _ := dH.chartedSpace
    let _ := dK.chartedSpace
    let _ := dH.lieGroup
    let _ := dK.lieGroup
    LieComplexification 𝓘(ℝ, E₀) H₀ 𝓘(ℝ, EC₀) Gc₀ :=
  let dH := EmbeddedLieSubgroupData.ofIsClosed (I := I)
    (MulAction.isClosed_ambientConnectedComponentOfOne_stabilizer
      (ContMDiffSMul.contMDiff_smul_const (I := I) (I' := I') (n := ∞) (G := G) x).continuous)
  let dK := EmbeddedLieSubgroupData.ofIsClosed (I := IC)
    (MulAction.isClosed_ambientConnectedComponentOfOne_stabilizer
      (ContMDiffSMul.contMDiff_smul_const (I := IC) (I' := I') (n := ∞) (G := Gc) x).continuous)
  let _ := dH.chartedSpace
  let _ := dK.chartedSpace
  let _ := dH.lieGroup
  let _ := dK.lieGroup
  have hmaps := h.mapsTo_toHom_ambientConnectedComponentOfOne_stabilizer x
  { toHom := C.toHom.restrict dH dK hmaps
    toHom_injective := ContMDiffMonoidMorphism.restrict_injective C.toHom_injective dH dK hmaps
    cplx := h.stabilizerCplx hμ hg hx dK
    cplx_lie := h.stabilizerCplx_lie hμ hg hx dK
    isMaximalTotallyReal_range := h.isMaximalTotallyReal_range_restrict hμ hg hx dH dK hmaps
    polar := h.stabilizerPolar hμ hg hx
    polar_apply' ξ u := Subtype.ext <| by
      rw [h.coe_stabilizerPolar_apply, Subgroup.coe_mul, dK.coe_mulInvariantExp,
        h.groupLieAlgebraMap_subtype_stabilizerCplx, C.expI_def, C.lieMap_def]
      congr 3
      · exact (C.toHom.groupLieAlgebraMap_subtype_groupLieAlgebraLieHom_restrict dH dK hmaps ξ).symm
      · exact (C.toHom.coe_restrict_apply dH dK hmaps u).symm }


/-- The inclusion of `IsComplexifiedAction.stabilizerComplexification` is the restriction of
`C.toHom` to the identity components of the stabilizers. -/
theorem IsComplexifiedAction.stabilizerComplexification_toHom (h : IsComplexifiedAction C J)
    (hμ : σ.IsEquivariantMomentMap fun x ↦ -μ x)
    (hg : ∀ x (u w : TangentSpace I' x), ⟪u, w⟫ = σ.eval₂ x u (J x w)) {x : M} (hx : μ x = 0) :
    let dH := EmbeddedLieSubgroupData.ofIsClosed (I := I)
      (MulAction.isClosed_ambientConnectedComponentOfOne_stabilizer
        (ContMDiffSMul.contMDiff_smul_const (I := I) (I' := I') (n := ∞) (G := G) x).continuous)
    let dK := EmbeddedLieSubgroupData.ofIsClosed (I := IC)
      (MulAction.isClosed_ambientConnectedComponentOfOne_stabilizer
        (ContMDiffSMul.contMDiff_smul_const (I := IC) (I' := I') (n := ∞) (G := Gc) x).continuous)
    let _ := dH.chartedSpace
    let _ := dK.chartedSpace
    let _ := dH.lieGroup
    let _ := dK.lieGroup
    (h.stabilizerComplexification hμ hg hx).toHom =
      C.toHom.restrict dH dK (h.mapsTo_toHom_ambientConnectedComponentOfOne_stabilizer x) :=
  (rfl)

/-- The complex structure of `IsComplexifiedAction.stabilizerComplexification` is
`IsComplexifiedAction.stabilizerCplx`. -/
theorem IsComplexifiedAction.stabilizerComplexification_cplx (h : IsComplexifiedAction C J)
    (hμ : σ.IsEquivariantMomentMap fun x ↦ -μ x)
    (hg : ∀ x (u w : TangentSpace I' x), ⟪u, w⟫ = σ.eval₂ x u (J x w)) {x : M} (hx : μ x = 0) :
    let dH := EmbeddedLieSubgroupData.ofIsClosed (I := I)
      (MulAction.isClosed_ambientConnectedComponentOfOne_stabilizer
        (ContMDiffSMul.contMDiff_smul_const (I := I) (I' := I') (n := ∞) (G := G) x).continuous)
    let dK := EmbeddedLieSubgroupData.ofIsClosed (I := IC)
      (MulAction.isClosed_ambientConnectedComponentOfOne_stabilizer
        (ContMDiffSMul.contMDiff_smul_const (I := IC) (I' := I') (n := ∞) (G := Gc) x).continuous)
    let _ := dH.chartedSpace
    let _ := dK.chartedSpace
    let _ := dH.lieGroup
    let _ := dK.lieGroup
    (h.stabilizerComplexification hμ hg hx).cplx = h.stabilizerCplx hμ hg hx dK :=
  (rfl)

/-- The polar decomposition of `IsComplexifiedAction.stabilizerComplexification` is
`IsComplexifiedAction.stabilizerPolar`. -/
theorem IsComplexifiedAction.stabilizerComplexification_polar (h : IsComplexifiedAction C J)
    (hμ : σ.IsEquivariantMomentMap fun x ↦ -μ x)
    (hg : ∀ x (u w : TangentSpace I' x), ⟪u, w⟫ = σ.eval₂ x u (J x w)) {x : M} (hx : μ x = 0) :
    let dH := EmbeddedLieSubgroupData.ofIsClosed (I := I)
      (MulAction.isClosed_ambientConnectedComponentOfOne_stabilizer
        (ContMDiffSMul.contMDiff_smul_const (I := I) (I' := I') (n := ∞) (G := G) x).continuous)
    let dK := EmbeddedLieSubgroupData.ofIsClosed (I := IC)
      (MulAction.isClosed_ambientConnectedComponentOfOne_stabilizer
        (ContMDiffSMul.contMDiff_smul_const (I := IC) (I' := I') (n := ∞) (G := Gc) x).continuous)
    let _ := dH.chartedSpace
    let _ := dK.chartedSpace
    let _ := dH.lieGroup
    let _ := dK.lieGroup
    (h.stabilizerComplexification hμ hg hx).polar = h.stabilizerPolar hμ hg hx :=
  (rfl)

/-- **The imaginary exponential of the complexified stabilizer.** Through the inclusions of the
identity components `H₀ → G` and `Gc₀ → Gc`, the exponential `expI` of
`IsComplexifiedAction.stabilizerComplexification` is that of `C`: for `ξ` in the Lie algebra of
`H₀`, `expI ξ`, read in `Gc`, is `C.expI` of the image of `ξ` under the differential at `1` of the
inclusion `H₀ → G`. -/
theorem IsComplexifiedAction.stabilizerComplexification_expI (h : IsComplexifiedAction C J)
    (hμ : σ.IsEquivariantMomentMap fun x ↦ -μ x)
    (hg : ∀ x (u w : TangentSpace I' x), ⟪u, w⟫ = σ.eval₂ x u (J x w)) {x : M} (hx : μ x = 0) :
    let H₀ := (MulAction.stabilizer G x).ambientConnectedComponentOfOne
    let E₀ := (lieSubalgebraOfSubgroup (I := I) H₀).toSubmodule
    let dH := EmbeddedLieSubgroupData.ofIsClosed (I := I)
      (MulAction.isClosed_ambientConnectedComponentOfOne_stabilizer
        (ContMDiffSMul.contMDiff_smul_const (I := I) (I' := I') (n := ∞) (G := G) x).continuous)
    let dK := EmbeddedLieSubgroupData.ofIsClosed (I := IC)
      (MulAction.isClosed_ambientConnectedComponentOfOne_stabilizer
        (ContMDiffSMul.contMDiff_smul_const (I := IC) (I' := I') (n := ∞) (G := Gc) x).continuous)
    let _ := dH.chartedSpace
    let _ := dK.chartedSpace
    let _ := dH.lieGroup
    let _ := dK.lieGroup
    ∀ ξ : GroupLieAlgebra 𝓘(ℝ, E₀) H₀,
      ((h.stabilizerComplexification hμ hg hx).expI ξ : Gc) =
        C.expI (H₀.subtype.groupLieAlgebraMap 𝓘(ℝ, E₀) I ξ) := by
  intro H₀ E₀ dH dK _ _ _ _ ξ
  rw [LieComplexification.expI_def, dK.coe_mulInvariantExp, h.stabilizerComplexification_cplx,
    h.groupLieAlgebraMap_subtype_stabilizerCplx, LieComplexification.expI_def,
    LieComplexification.lieMap_def, LieComplexification.lieMap_def,
    h.stabilizerComplexification_toHom,
    C.toHom.groupLieAlgebraMap_subtype_groupLieAlgebraLieHom_restrict]

omit [TopologicalSpace M] [I.Boundaryless] [T2Space M] in
/-- **A nonzero period of the identity component of `G_x` is one of `G`.** For any embedded Lie
subgroup structure on the identity component `H₀` of the stabilizer of `x` in `G`, the
differential at `1` of the inclusion `H₀ → G` maps `nonzeroPeriods` of `H₀` into those of `G`. -/
theorem mem_nonzeroPeriods_of_stabilizer {x : M} {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (d : EmbeddedLieSubgroupData I (MulAction.stabilizer G x).ambientConnectedComponentOfOne F) :
    let _ := d.chartedSpace
    let _ := d.lieGroup
    ∀ {ξ}, ξ ∈ nonzeroPeriods 𝓘(ℝ, F) (MulAction.stabilizer G x).ambientConnectedComponentOfOne →
      (MulAction.stabilizer G x).ambientConnectedComponentOfOne.subtype.groupLieAlgebraMap
        𝓘(ℝ, F) I ξ ∈ nonzeroPeriods I G := by
  intro _ _ ξ hξ
  rw [mem_nonzeroPeriods] at hξ ⊢
  refine ⟨(map_ne_zero_iff _ d.injective_groupLieAlgebraMap_subtype).2 hξ.1, ?_⟩
  rw [← d.coe_mulInvariantExp, hξ.2, OneMemClass.coe_one]
end StabilizerComplexification

end SymplecticGeometry
