/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Analysis.Calculus.IteratedFDeriv.CompContinuousLinearEquiv
import TauCeti.Analysis.InnerProductSpace.RangeProjection
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Injective
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Topology.Compactness.Compact
import SymplecticGeometry.Analysis.Calculus.TangentGraphChart
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.Basic
import SymplecticGeometry.Geometry.Manifold.MFDeriv.Chart

/-!
# Tangent projection charts

Let `e : M → F` be a smooth map from a boundaryless manifold into a real inner product space, with
injective differentials, and let `T` be the range of the differential of `e` at `x : M`. Near `x`,
the orthogonal projection `z ↦ P (e z - e x)` of `e` onto `T` is a chart of `M` with values in
`T`, which presents the image of `e` near `e x` as a graph over its tangent space. For a compact
`M` embedded in a Euclidean space, these are the local graph charts with which Weil builds convex
covers [Weil1952, §1, pp. 120–122].

## Main definitions

* `SymplecticGeometry.tangentProjectionChart`: for a `C^n` map `e` (`1 ≤ n`) with injective
  differential at `x`, a partial diffeomorphism around `x` onto an open subset of `T`, given on
  its source by `z ↦ P (e z - e x)` (`tangentProjectionChart_apply`).

## Main results

* `SymplecticGeometry.isLocalDiffeomorphAt_orthogonalProjectionOnto_sub`: for a subspace `V` of
  the dimension of `E`, `z ↦ P_V (e z - a)` is a local diffeomorphism where its differential is
  injective.
* `SymplecticGeometry.orthogonalProjectionOnto_comp_fderiv_comp_symm` and
  `SymplecticGeometry.norm_le_norm_fderiv_comp_symm_apply`: for a partial diffeomorphism `Φ`
  given by `z ↦ P_V (e z - a)`, the differential of `e ∘ Φ⁻¹` followed by `P_V` is the identity,
  so that differential does not shrink vectors.
* `SymplecticGeometry.exists_uniform_tangentProjectionChart`: for a compact `M` and a smooth
  injective `e`, one radius `r > 0` such that for every `x` such a chart is defined on all `z`
  with `‖e z - e x‖ < r` and reaches the ball of radius `r` in `T`, and one bound for the
  derivatives of each order of the composite of `e` with the inverses of these charts.

## Implementation notes

The chart at a single point comes from Tau Ceti's inverse function theorem on manifolds,
`TauCeti.isLocalDiffeomorphAt_of_injective_mfderiv`: the chart is the inverse of
`IsLocalDiffeomorphAt.localInverse`, which the map agrees with by
`IsLocalDiffeomorphAt.eqOn_localInverse_symm`. It adapts the argument of Tau Ceti's
`ContDiffOn.exists_openPartialHomeomorph_starProjection`, which builds the same graph chart on an
open subset of `E`: the projection fixes the tangent space, so its differential is an isomorphism
onto it. For the uniform statement, the projection is read in the extended chart at a point `x₀`,
where `e` becomes a map `g` on an open subset of `E`, and
`ContDiffOn.exists_uniform_inverse_starProjection` gives, for all `x` near `x₀` at once, local
inverses of the charts on one ball, with uniform derivative bounds. Since `M` is compact and `e`
is injective, `e` is a closed embedding, so the points `z` with `e z` close to `e x` stay in that
ball. Tau Ceti's `IsCompact.exists_forall_of_forall_exists_eventually` then gives one radius
and one bound for all of `M`.

## References

* [A. Weil, *Sur les théorèmes de de Rham*][Weil1952], §1, pp. 120–122
-/

public section

open Set Function Filter Topology Metric
open scoped Manifold ContDiff

namespace SymplecticGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {n : WithTop ℕ∞} {e : M → F} {x : M}

/-! ### The chart at a point -/

section Pointwise

variable [IsManifold I n M] [BoundarylessManifold I M]

/-- Let `V` be a finite-dimensional subspace of `F` of the dimension of `E`, and `a : F`. At a
point `z` where the differential of `e` followed by the orthogonal projection onto `V` is
injective, the map `y ↦ P_V (e y - a)` is a local diffeomorphism. -/
theorem isLocalDiffeomorphAt_orthogonalProjectionOnto_sub (V : Submodule ℝ F)
    [FiniteDimensional ℝ V] (a : F) {z : M} (hn : 1 ≤ n) (he : ContMDiff I 𝓘(ℝ, F) n e)
    (hz : Injective (V.orthogonalProjectionOnto ∘L mvfderiv I e z))
    (hdim : Module.finrank ℝ E = Module.finrank ℝ V) :
    IsLocalDiffeomorphAt I 𝓘(ℝ, V) n (fun y ↦ V.orthogonalProjectionOnto (e y - a)) z := by
  have hn0 : n ≠ 0 := by rintro rfl; exact absurd hn (by simp)
  have hf : ContMDiff I 𝓘(ℝ, V) n (fun y ↦ V.orthogonalProjectionOnto (e y - a)) :=
    (V.orthogonalProjectionOnto.contDiff.comp (contDiff_id.sub contDiff_const)).contMDiff.comp he
  refine TauCeti.isLocalDiffeomorphAt_of_injective_mfderiv hf.contMDiffOn isOpen_univ
    (mem_univ z) BoundarylessManifold.isInteriorPoint hn ?_ hdim
  -- The differential at `z` is the projection onto `V` after that of `e`.
  have hP := (V.orthogonalProjectionOnto.hasFDerivAt (x := e z)).sub_const
    (V.orthogonalProjectionOnto a)
  simp_rw [← map_sub] at hP
  have hmf : HasMFDerivAt I 𝓘(ℝ, V) (fun y ↦ V.orthogonalProjectionOnto (e y - a)) z
      (V.orthogonalProjectionOnto ∘L mvfderiv I e z) :=
    hP.hasMFDerivAt.comp z (he.mdifferentiableAt hn0).hasMFDerivAt
  rwa [hmf.mfderiv]

/-- The orthogonal projection of `e z - e x` onto the range of the differential of `e` at `x` is a
local diffeomorphism at `x`. -/
private theorem isLocalDiffeomorphAt_orthogonalProjectionOnto_range_sub (hn : 1 ≤ n)
    (he : ContMDiff I 𝓘(ℝ, F) n e) (hx : Injective (mfderiv I 𝓘(ℝ, F) e x)) :
    IsLocalDiffeomorphAt I 𝓘(ℝ, (mvfderiv I e x).range) n
      (fun z ↦ (mvfderiv I e x).range.orthogonalProjectionOnto (e z - e x)) x := by
  have hx' : Injective (mvfderiv I e x) := TauCeti.injective_mvfderiv_iff.2 hx
  set V := (mvfderiv I e x).range
  refine isLocalDiffeomorphAt_orthogonalProjectionOnto_sub V (e x) hn he ?_
    (LinearMap.finrank_range_of_inj hx').symm
  -- The projection fixes `V`, so it does not change the differential of `e` at `x`.
  have key : ∀ u, ((V.orthogonalProjectionOnto ∘L mvfderiv I e x) u : F) = mvfderiv I e x u :=
    fun u ↦ congrArg Subtype.val
      (V.orthogonalProjectionOnto_mem_subspace_eq_self ⟨_, LinearMap.mem_range_self _ u⟩)
  intro v w hvw
  exact hx' ((key v).symm.trans ((congrArg Subtype.val hvw).trans (key w)))

/-- The **tangent projection chart** of `e : M → F` at `x`: for a `C^n` map `e` (`1 ≤ n`) with
injective differential at `x`, a partial diffeomorphism from a neighbourhood of `x` onto an open
subset of the range `T` of the differential of `e` at `x`, given there by `z ↦ P (e z - e x)`,
where `P` is the orthogonal projection of `F` onto `T` (`tangentProjectionChart_apply`). It
exists by the inverse function theorem, since its differential at `x` is `P` composed with the
differential of `e`, an isomorphism onto `T`. -/
noncomputable def tangentProjectionChart (hn : 1 ≤ n) (he : ContMDiff I 𝓘(ℝ, F) n e) (x : M)
    (hx : Injective (mfderiv I 𝓘(ℝ, F) e x)) :
    PartialDiffeomorph I 𝓘(ℝ, (mvfderiv I e x).range) M (mvfderiv I e x).range n :=
  (isLocalDiffeomorphAt_orthogonalProjectionOnto_range_sub hn he hx).localInverse.symm

variable {hn : 1 ≤ n} {he : ContMDiff I 𝓘(ℝ, F) n e} {hx : Injective (mfderiv I 𝓘(ℝ, F) e x)}

/-- The source of the tangent projection chart at `x` contains `x`. -/
theorem mem_tangentProjectionChart_source : x ∈ (tangentProjectionChart hn he x hx).source := by
  simpa [tangentProjectionChart] using
    (isLocalDiffeomorphAt_orthogonalProjectionOnto_range_sub hn he hx).localInverse_mem_target

/-- On its source, the tangent projection chart at `x` is the orthogonal projection of
`e z - e x` onto the range of the differential of `e` at `x`. -/
theorem tangentProjectionChart_apply {z : M} (hz : z ∈ (tangentProjectionChart hn he x hx).source) :
    tangentProjectionChart hn he x hx z =
      (mvfderiv I e x).range.orthogonalProjectionOnto (e z - e x) :=
  ((isLocalDiffeomorphAt_orthogonalProjectionOnto_range_sub hn he hx).eqOn_localInverse_symm
    (by simpa [tangentProjectionChart] using hz)).symm

/-- The tangent projection chart at `x` sends `x` to `0`. -/
@[simp]
theorem tangentProjectionChart_self : tangentProjectionChart hn he x hx x = 0 := by
  rw [tangentProjectionChart_apply mem_tangentProjectionChart_source, sub_self, map_zero]

end Pointwise

/-! ### Differentials of the inverse of a projection chart -/

section Deriv

omit [FiniteDimensional ℝ E] in
/-- Let `Φ` be a partial diffeomorphism from `M` to a subspace `V` of `F` that is given on its
source by `z ↦ P (e z - a)`, for `P` the orthogonal projection onto `V` and `e` a `C^n` map with
`1 ≤ n`, as `tangentProjectionChart` is. At each point of the target of `Φ`, the differential of
`e ∘ Φ⁻¹` followed by `P` is the identity of `V`. -/
theorem orthogonalProjectionOnto_comp_fderiv_comp_symm (V : Submodule ℝ F)
    [V.HasOrthogonalProjection] {a : F} (hn : 1 ≤ n) (he : ContMDiff I 𝓘(ℝ, F) n e)
    {Φ : PartialDiffeomorph I 𝓘(ℝ, V) M V n}
    (hΦ : ∀ z ∈ Φ.source, Φ z = V.orthogonalProjectionOnto (e z - a)) {u : V}
    (hu : u ∈ Φ.target) :
    V.orthogonalProjectionOnto ∘L fderiv ℝ (e ∘ Φ.symm) u = ContinuousLinearMap.id ℝ V := by
  have hψ : ContDiffOn ℝ n (e ∘ Φ.symm) Φ.target :=
    contMDiffOn_iff_contDiffOn.1 (he.comp_contMDiffOn Φ.symm.contMDiffOn)
  have hd : DifferentiableAt ℝ (e ∘ Φ.symm) u :=
    (hψ.contDiffAt (Φ.open_target.mem_nhds hu)).differentiableAt
      (by rintro rfl; exact absurd hn (by simp))
  -- Near `u`, projecting `e ∘ Φ⁻¹ - a` onto `V` gives back the identity.
  have hproj : (fun w ↦ V.orthogonalProjectionOnto ((e ∘ Φ.symm) w - a)) =ᶠ[𝓝 u] id :=
    eventually_of_mem (Φ.open_target.mem_nhds hu) fun w hw ↦ by
      simpa [Φ.right_inv hw] using (hΦ _ (Φ.map_target hw)).symm
  exact (V.orthogonalProjectionOnto.hasFDerivAt.comp u (hd.hasFDerivAt.sub_const a)).unique
    ((hasFDerivAt_id u).congr_of_eventuallyEq hproj)

omit [FiniteDimensional ℝ E] in
/-- Under the hypotheses of `orthogonalProjectionOnto_comp_fderiv_comp_symm`, the differential of
`e ∘ Φ⁻¹` does not shrink vectors: `‖v‖ ≤ ‖D(e ∘ Φ⁻¹) v‖` at each point of the target of `Φ`. -/
theorem norm_le_norm_fderiv_comp_symm_apply (V : Submodule ℝ F) [V.HasOrthogonalProjection]
    {a : F} (hn : 1 ≤ n) (he : ContMDiff I 𝓘(ℝ, F) n e)
    {Φ : PartialDiffeomorph I 𝓘(ℝ, V) M V n}
    (hΦ : ∀ z ∈ Φ.source, Φ z = V.orthogonalProjectionOnto (e z - a)) {u : V}
    (hu : u ∈ Φ.target) (v : V) :
    ‖v‖ ≤ ‖fderiv ℝ (e ∘ Φ.symm) u v‖ := by
  calc ‖v‖ = ‖V.orthogonalProjectionOnto (fderiv ℝ (e ∘ Φ.symm) u v)‖ := by
        rw [← ContinuousLinearMap.comp_apply,
          orthogonalProjectionOnto_comp_fderiv_comp_symm V hn he hΦ hu,
          ContinuousLinearMap.id_apply]
    _ ≤ ‖fderiv ℝ (e ∘ Φ.symm) u v‖ := V.norm_orthogonalProjectionOnto_apply_le _

end Deriv

/-! ### Uniform charts on a compact manifold -/

section Uniform

variable [IsManifold I ∞ M] [BoundarylessManifold I M]

/-- **The chart at a point near `x₀`.** Read in the extended chart at `x₀`, where `e` becomes `g`,
the coordinate data of `ContDiffOn.exists_uniform_inverse_starProjection` at
`w' = extChartAt I x₀ x` give a tangent projection chart at `x` whose source is the preimage of
the ball of radius `ε`, whose target contains a ball of radius `η / (‖S‖ + 1)`, and whose inverse
has derivatives bounded in terms of `S` and `C`. -/
private theorem exists_partialDiffeomorph_of_uniformInverse (he : ContMDiff I 𝓘(ℝ, F) ∞ e)
    (hinj : ∀ x, Injective (mfderiv I 𝓘(ℝ, F) e x)) {x₀ x : M} {g : E → F}
    (hgdef : g = e ∘ (extChartAt I x₀).symm) {S : F →L[ℝ] E} {ε η : ℝ} {C : ℕ → ℝ}
    {h : E → E → E} (hεU : ball (extChartAt I x₀ x₀) ε ⊆ interior (extChartAt I x₀).target)
    (hx : x ∈ (extChartAt I x₀).source)
    (hxε : extChartAt I x₀ x ∈ ball (extChartAt I x₀ x₀) ε)
    (hmain : ∀ w ∈ ball (extChartAt I x₀ x₀) ε,
      Injective (S ∘L (fderiv ℝ g (extChartAt I x₀ x)).range.starProjection ∘L fderiv ℝ g w) ∧
      h (extChartAt I x₀ x) (S ((fderiv ℝ g (extChartAt I x₀ x)).range.starProjection
        (g w - g (extChartAt I x₀ x)))) = w ∧
      ∀ j, ‖iteratedFDeriv ℝ j (g ∘ h (extChartAt I x₀ x))
        (S ((fderiv ℝ g (extChartAt I x₀ x)).range.starProjection
          (g w - g (extChartAt I x₀ x))))‖ ≤ C j)
    (hsurj : ∀ v ∈ ball (0 : E) η, ∃ w ∈ ball (extChartAt I x₀ x₀) ε,
      S ((fderiv ℝ g (extChartAt I x₀ x)).range.starProjection
        (g w - g (extChartAt I x₀ x))) = v) :
    ∃ Φ : PartialDiffeomorph I 𝓘(ℝ, (mvfderiv I e x).range) M (mvfderiv I e x).range ∞,
      (∀ z ∈ Φ.source, Φ z = (mvfderiv I e x).range.orthogonalProjectionOnto (e z - e x)) ∧
      Φ.source = (extChartAt I x₀).source ∩ extChartAt I x₀ ⁻¹' ball (extChartAt I x₀ x₀) ε ∧
      ball 0 (η / (‖S‖ + 1)) ⊆ Φ.target ∧
      ∀ u ∈ Φ.target, ∀ j,
        ‖iteratedFDeriv ℝ j (e ∘ Φ.symm) u‖ ≤ (‖S‖ + 1) ^ j * max (C j) 0 := by
  subst hgdef
  set c := extChartAt I x₀
  set w' := c x
  set s := c.source ∩ c ⁻¹' ball (c x₀) ε
  have hs : IsOpen s :=
    (continuousOn_extChartAt x₀).isOpen_inter_preimage (isOpen_extChartAt_source x₀) isOpen_ball
  have hgd : ∀ z ∈ s, DifferentiableAt ℝ (e ∘ c.symm) (c z) := fun z hz ↦
    (((he.contDiffOn_comp_extChartAt_symm x₀).mono interior_subset).contDiffAt
      (isOpen_interior.mem_nhds (hεU hz.2))).differentiableAt (by simp)
  have hgx : ∀ z ∈ c.source, (e ∘ c.symm) (c z) = e z := fun z hz ↦ by
    rw [comp_apply, c.left_inv hz]
  -- The range `V` of the differential of `e` at `x` is that of `e ∘ c.symm` at `w'`, so the
  -- orthogonal projection onto it is `Q'`.
  set V := (mvfderiv I e x).range
  set Q' := (fderiv ℝ (e ∘ c.symm) w').range.starProjection
  have hxs : x ∈ s := ⟨hx, hxε⟩
  have hV : V = (fderiv ℝ (e ∘ c.symm) w').range :=
    range_mvfderiv_eq_range_fderiv_comp_extChartAt_symm_of_mem_source hx (hgd x hxs)
  -- The subspaces agree by `hV`; the projection instances are propositions.
  have hVQ : V.starProjection = Q' := by
    congr 1
  have hPV : ∀ y, (V.orthogonalProjectionOnto y : F) = Q' y := fun y ↦ by
    rw [← V.starProjection_apply, hVQ]
  -- `S` restricts to an isomorphism `T` from `V` onto `E`.
  have hSinj : Injective (S ∘L V.subtypeL) := by
    rintro ⟨u₁, hu₁⟩ ⟨u₂, hu₂⟩ h12
    rw [hV] at hu₁ hu₂
    obtain ⟨a₁, rfl⟩ := hu₁
    obtain ⟨a₂, rfl⟩ := hu₂
    have h := (hmain w' hxε).1 (a₁ := a₁) (a₂ := a₂) (by simpa [Q'] using h12)
    subst h
    rfl
  have hdim : Module.finrank ℝ V = Module.finrank ℝ E :=
    LinearMap.finrank_range_of_inj (TauCeti.injective_mvfderiv_iff.2 (hinj x))
  let T : V ≃L[ℝ] E :=
    (LinearMap.linearEquivOfInjective (S ∘L V.subtypeL : V →ₗ[ℝ] E) hSinj hdim)
      |>.toContinuousLinearEquiv
  have hT : ∀ u : V, T u = S u := fun u ↦ by
    rw [LinearEquiv.coe_toContinuousLinearEquiv', LinearMap.linearEquivOfInjective_apply,
      ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
  have hTn : ∀ u : V, ‖T u‖ ≤ (‖S‖ + 1) * ‖u‖ := fun u ↦ by
    rw [hT]
    calc ‖S u‖ ≤ ‖S‖ * ‖u‖ := S.le_opNorm _
      _ ≤ (‖S‖ + 1) * ‖u‖ := by gcongr; linarith
  -- The chart `φ`, read through `T`, is the map `Ψ w'` of the coordinate data.
  set φ : M → V := fun z ↦ V.orthogonalProjectionOnto (e z - e x)
  have hkey : ∀ z ∈ c.source, T (φ z) = S (Q' ((e ∘ c.symm) (c z) - (e ∘ c.symm) w')) :=
    fun z hz ↦ by
      rw [hT, hgx z hz, hgx x hx]
      exact congrArg S (hPV _)
  have hinjOn : InjOn φ s := fun z₁ hz₁ z₂ hz₂ h12 ↦ by
    have h' := congrArg T h12
    rw [hkey z₁ hz₁.1, hkey z₂ hz₂.1] at h'
    have h'' := congrArg (h w') h'
    rw [(hmain _ hz₁.2).2.1, (hmain _ hz₂.2).2.1] at h''
    exact c.injOn hz₁.1 hz₂.1 h''
  have hloc : IsLocalDiffeomorphOn I 𝓘(ℝ, V) ∞ φ s := by
    rw [isLocalDiffeomorphOn_iff]
    rintro ⟨z, hz⟩
    refine isLocalDiffeomorphAt_orthogonalProjectionOnto_sub V (e x) (by simp) he ?_ hdim.symm
    -- Read in the chart, the differential is injective by `hmain`.
    obtain ⟨Lc, hLc⟩ := isInvertible_mfderiv_extChartAt hz.1
    -- Tau Ceti's equation is about `mfderiv`; the ascription reads it as one about `mvfderiv`.
    have hD : mvfderiv I e z = _ :=
      TauCeti.mfderiv_eq_fderiv_comp_mfderiv_extChartAt hz.1 (hgd z hz)
    intro a b hab
    have hPa : ∀ a', S ((V.orthogonalProjectionOnto ∘L mvfderiv I e z) a' : F) =
        S (Q' (fderiv ℝ (e ∘ c.symm) (c z) (mfderiv I 𝓘(ℝ, E) c z a'))) := fun a' ↦ by
      rw [ContinuousLinearMap.comp_apply, hPV, DFunLike.congr_fun hD a']
      exact congrArg (fun y ↦ S (Q' y)) (ContinuousLinearMap.comp_apply _ _ _)
    have h' : S (Q' (fderiv ℝ (e ∘ c.symm) (c z) (mfderiv I 𝓘(ℝ, E) c z a))) =
        S (Q' (fderiv ℝ (e ∘ c.symm) (c z) (mfderiv I 𝓘(ℝ, E) c z b))) := by
      rw [← hPa, ← hPa, hab]
    have h'' := (hmain (c z) hz.2).1 (a₁ := mfderiv I 𝓘(ℝ, E) c z a)
      (a₂ := mfderiv I 𝓘(ℝ, E) c z b) h'
    rw [← hLc] at h''
    exact Lc.injective h''
  -- The chart is `φ` on `s`, as a partial diffeomorphism onto its image.
  have : Nonempty M := ⟨x⟩
  set Φ := hloc.partialDiffeomorphOfInjOn hs hinjOn
  have hΦ : ∀ z, Φ z = φ z := fun z ↦
    congrFun (IsLocalDiffeomorphOn.coe_partialDiffeomorphOfInjOn hloc hs hinjOn) z
  have hΦt : Φ.target = φ '' s :=
    IsLocalDiffeomorphOn.partialDiffeomorphOfInjOn_target hloc hs hinjOn
  have hΦsymm : ∀ y, Φ.symm y = invFunOn φ s y :=
    IsLocalDiffeomorphOn.partialDiffeomorphOfInjOn_symm_apply hloc hs hinjOn
  refine ⟨Φ, fun z _ ↦ hΦ z, IsLocalDiffeomorphOn.partialDiffeomorphOfInjOn_source hloc hs hinjOn,
    fun u hu ↦ hΦt ▸ ?_, hΦt ▸ ?_⟩
  · -- The target contains a ball around `0`: its points come from `hsurj`.
    have hTu : T u ∈ ball (0 : E) η := by
      rw [mem_ball_zero_iff]
      calc ‖T u‖ ≤ (‖S‖ + 1) * ‖u‖ := hTn u
        _ < (‖S‖ + 1) * (η / (‖S‖ + 1)) := by gcongr; exact mem_ball_zero_iff.1 hu
        _ = η := by field_simp
    obtain ⟨w, hw, hwu⟩ := hsurj (T u) hTu
    have hwt : w ∈ c.target := interior_subset (hεU hw)
    refine ⟨c.symm w, ⟨c.map_target hwt, ?_⟩, T.injective ?_⟩
    · rw [mem_preimage, c.right_inv hwt]
      exact hw
    · rw [hkey _ (c.map_target hwt), c.right_inv hwt, hwu]
  · -- On the target, `e ∘ Φ⁻¹ = ((e ∘ c.symm) ∘ h w') ∘ T`, whose derivatives `hmain` bounds.
    rintro _ ⟨z₀, hz₀, rfl⟩ j
    have heq : EqOn (e ∘ Φ.symm) (((e ∘ c.symm) ∘ h w') ∘ T) (φ '' s) := by
      rintro _ ⟨z, hz, rfl⟩
      simp only [comp_apply]
      rw [← comp_apply (f := e) (g := c.symm), hkey z hz.1, (hmain _ hz.2).2.1, hgx z hz.1,
        hΦsymm]
      exact congrArg e (hinjOn.leftInvOn_invFunOn hz)
    have hmem : φ z₀ ∈ φ '' s := ⟨z₀, hz₀, rfl⟩
    rw [((heq.eventuallyEq_of_mem ((hΦt ▸ Φ.open_target).mem_nhds hmem)).iteratedFDeriv ℝ
      j).eq_of_nhds]
    refine (T.norm_iteratedFDeriv_comp_right_le _ _ j).trans ?_
    rw [hkey z₀ hz₀.1]
    have hTn' : ‖(T : V →L[ℝ] E)‖ ≤ ‖S‖ + 1 :=
      ContinuousLinearMap.opNorm_le_bound _ (by positivity) hTn
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hTn' j)
      (((hmain _ hz₀.2).2.2 j).trans (le_max_left _ _)) (norm_nonneg _) (by positivity)

/-- **Tangent projection charts near a point.** Near each point `x₀`, the charts of
`exists_uniform_tangentProjectionChart` exist with constants uniform in `x`. -/
private theorem exists_uniform_tangentProjectionChart_nhds [CompactSpace M]
    (he : ContMDiff I 𝓘(ℝ, F) ∞ e) (hinj : ∀ x, Injective (mfderiv I 𝓘(ℝ, F) e x))
    (he' : Injective e) (x₀ : M) :
    ∃ W ∈ 𝓝 x₀, ∃ r > 0, ∃ C : ℕ → ℝ, ∀ x ∈ W,
      ∃ Φ : PartialDiffeomorph I 𝓘(ℝ, (mvfderiv I e x).range) M (mvfderiv I e x).range ∞,
        (∀ z ∈ Φ.source, Φ z = (mvfderiv I e x).range.orthogonalProjectionOnto (e z - e x)) ∧
        {z | dist (e z) (e x) < r} ⊆ Φ.source ∧ ball 0 r ⊆ Φ.target ∧
        ∀ u ∈ Φ.target, ∀ j, ‖iteratedFDeriv ℝ j (e ∘ Φ.symm) u‖ ≤ C j := by
  -- Work in the extended chart `c` at `x₀`, where `e` reads as `g`.
  set c := extChartAt I x₀
  set g : E → F := e ∘ c.symm with hgdef
  have hw₀ : c x₀ ∈ interior c.target :=
    ModelWithCorners.isInteriorPoint_iff.mp (BoundarylessManifold.isInteriorPoint (x := x₀))
  have hg : ContDiffOn ℝ ∞ g (interior c.target) :=
    (he.contDiffOn_comp_extChartAt_symm x₀).mono interior_subset
  have hinjg : Injective (fderiv ℝ g (c x₀)) := by
    have hw' := interior_subset hw₀
    have h := TauCeti.fderiv_comp_extChartAt_symm_injective (c.map_target hw')
      (by rw [c.right_inv hw']
          exact (hg.contDiffAt (isOpen_interior.mem_nhds hw₀)).differentiableAt (by simp))
      (hinj _)
    rwa [c.right_inv hw'] at h
  obtain ⟨S, ε, hε, η, hη, C, h, hηε, hεU, hmain⟩ :=
    hg.exists_uniform_inverse_starProjection isOpen_interior hw₀ hinjg
  have hcont : ContinuousOn c c.source := continuousOn_extChartAt x₀
  have hsrc : IsOpen c.source := isOpen_extChartAt_source x₀
  set s := c.source ∩ c ⁻¹' ball (c x₀) ε
  have hs : IsOpen s := hcont.isOpen_inter_preimage hsrc isOpen_ball
  have hx₀s : x₀ ∈ s := ⟨mem_extChartAt_source x₀, mem_ball_self hε⟩
  -- Points whose images are close to that of a point near `x₀` lie in `s`.
  obtain ⟨W, hW, r, hr, hWr⟩ :
      ∃ W ∈ 𝓝 x₀, ∃ r > 0, ∀ x ∈ W, ∀ z, dist (e z) (e x) < r → z ∈ s := by
    -- `e` is a closed embedding, so `s` contains the preimage of a ball around `e x₀`.
    have hsn : s ∈ comap e (𝓝 (e x₀)) :=
      (he.continuous.isClosedEmbedding he').isInducing.nhds_eq_comap x₀ ▸ hs.mem_nhds hx₀s
    obtain ⟨δ, hδ, hδs⟩ := (nhds_basis_ball.comap e).mem_iff.1 hsn
    refine ⟨e ⁻¹' ball (e x₀) (δ / 2), he.continuous.continuousAt.preimage_mem_nhds
      (ball_mem_nhds _ (half_pos hδ)), δ / 2, half_pos hδ, fun x hx z hz ↦ hδs ?_⟩
    rw [mem_preimage, mem_ball] at hx ⊢
    linarith [dist_triangle (e z) (e x) (e x₀)]
  have hρ : 0 < η / (‖S‖ + 1) := div_pos hη (by positivity)
  refine ⟨W ∩ (c.source ∩ c ⁻¹' ball (c x₀) η),
    inter_mem hW ((hcont.isOpen_inter_preimage hsrc isOpen_ball).mem_nhds
      ⟨mem_extChartAt_source x₀, mem_ball_self hη⟩),
    min r (η / (‖S‖ + 1)), lt_min hr hρ, fun j ↦ (‖S‖ + 1) ^ j * max (C j) 0,
    fun x ⟨hxW, hxc, hxη⟩ ↦ ?_⟩
  obtain ⟨hmain', hsurj⟩ := hmain (c x) hxη
  obtain ⟨Φ, h₁, h₂, h₃, h₄⟩ := exists_partialDiffeomorph_of_uniformInverse he hinj hgdef
    hεU hxc (ball_subset_ball hηε hxη) hmain' hsurj
  exact ⟨Φ, h₁, fun z hz ↦ h₂ ▸ hWr x hxW z (lt_of_lt_of_le hz (min_le_left _ _)),
    (ball_subset_ball (min_le_right _ _)).trans h₃, h₄⟩

/-- **Uniform tangent projection charts.** Let `e : M → F` be a smooth injective map with injective
differentials from a compact boundaryless manifold into a real inner product space. There are
`r > 0` and `C : ℕ → ℝ` such that, for every `x : M`, some partial diffeomorphism `Φ` from `M`
onto an open subset of the range `T` of the differential of `e` at `x`

* is given on its source by `z ↦ P (e z - e x)`, for `P` the orthogonal projection onto `T`, as
  `tangentProjectionChart` is;
* has a source containing every `z` with `‖e z - e x‖ < r`, and a target containing the ball of
  radius `r` around `0`;
* has an inverse whose composite with `e` has iterated derivatives of order `j` bounded by `C j`
  on the target, for every `j`. -/
theorem exists_uniform_tangentProjectionChart [CompactSpace M]
    (he : ContMDiff I 𝓘(ℝ, F) ∞ e) (hinj : ∀ x, Injective (mfderiv I 𝓘(ℝ, F) e x))
    (he' : Injective e) :
    ∃ r > 0, ∃ C : ℕ → ℝ, ∀ x : M,
      ∃ Φ : PartialDiffeomorph I 𝓘(ℝ, (mvfderiv I e x).range) M (mvfderiv I e x).range ∞,
        (∀ z ∈ Φ.source, Φ z = (mvfderiv I e x).range.orthogonalProjectionOnto (e z - e x)) ∧
        {z | dist (e z) (e x) < r} ⊆ Φ.source ∧ ball 0 r ⊆ Φ.target ∧
        ∀ u ∈ Φ.target, ∀ j, ‖iteratedFDeriv ℝ j (e ∘ Φ.symm) u‖ ≤ C j := by
  -- The constants `(r, C)` are ordered so that larger means a smaller radius and larger bounds;
  -- the charts at `x` for some constants serve for every larger ones.
  obtain ⟨⟨r, C⟩, h⟩ := isCompact_univ.exists_forall_of_forall_exists_eventually
    (α := {r : ℝ // 0 < r}ᵒᵈ × (ℕ → ℝ)) (r := (· ≤ ·))
    (p := fun a x ↦
      ∃ Φ : PartialDiffeomorph I 𝓘(ℝ, (mvfderiv I e x).range) M (mvfderiv I e x).range ∞,
        (∀ z ∈ Φ.source, Φ z = (mvfderiv I e x).range.orthogonalProjectionOnto (e z - e x)) ∧
        {z | dist (e z) (e x) < (OrderDual.ofDual a.1).val} ⊆ Φ.source ∧
        ball 0 (OrderDual.ofDual a.1).val ⊆ Φ.target ∧
        ∀ u ∈ Φ.target, ∀ j, ‖iteratedFDeriv ℝ j (e ∘ Φ.symm) u‖ ≤ a.2 j)
    (fun a b hab x ⟨Φ, h₁, h₂, h₃, h₄⟩ ↦
      have hr : (OrderDual.ofDual b.1).val ≤ (OrderDual.ofDual a.1).val :=
        Subtype.coe_le_coe.2 (OrderDual.ofDual_le_ofDual.2 hab.1)
      ⟨Φ, h₁, fun z hz ↦ h₂ (lt_of_lt_of_le hz hr), (ball_subset_ball hr).trans h₃,
        fun u hu j ↦ (h₄ u hu j).trans (hab.2 j)⟩)
    fun x₀ _ ↦ by
      obtain ⟨W, hW, r, hr, C, hC⟩ := exists_uniform_tangentProjectionChart_nhds he hinj he' x₀
      exact ⟨(OrderDual.toDual ⟨r, hr⟩, C), nhdsWithin_univ x₀ ▸ Filter.mem_of_superset hW hC⟩
  exact ⟨_, (OrderDual.ofDual r).property, C, fun x ↦ h x (mem_univ x)⟩

end Uniform

end SymplecticGeometry

end
