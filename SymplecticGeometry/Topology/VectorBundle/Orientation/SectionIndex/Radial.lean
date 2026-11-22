/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Analysis.Normed.Module.Ball.Radial.Cone
public import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.CoordinateDisc
public import SymplecticGeometry.Topology.VectorBundle.Orientation.SectionIndex.FiberwiseEquiv
public import SymplecticGeometry.Topology.VectorBundle.Orientation.SectionIndex.Trivial
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Winding
public import TauCeti.Analysis.Complex.Circle
public import TauCeti.Geometry.Manifold.ModelTransport.Finrank
public import TauCeti.Topology.Algebra.Module.Equiv.RestrictScalars
public import TauCeti.Topology.Circle.Normalize
public import TauCeti.Topology.VectorBundle.Orientation.Complex.Basic
public import TauCeti.Topology.VectorBundle.Smul

/-!
# The local index of a section extended radially into a coordinate disc

Let `M` be a surface with a homological orientation `o`, `φ` a coordinate disc of `M`
(`SymplecticGeometry.CoordinateDisc`), and `L` a complex line bundle over `M`. Let `σ` be a frame
of `L` along `φ` on the open unit disc: a nowhere-zero section `z ↦ σ z ∈ L (φ z)`, continuous on
total spaces. A map `u : S¹ → ℂ` extends radially to the plane by Tau Ceti's cone
`TauCeti.sphereCone`, `r ζ ↦ r u(ζ)` for `r ≥ 0` (read on `S¹` through
`Circle.homeomorphSphere`). Multiplying a frame by that extension gives a section of `L` along `φ`
that is continuous wherever the frame is
(`SymplecticGeometry.CoordinateDisc.continuousOn_sphereCone_smul`), equals `u ζ • σ ζ` on the unit
circle (`TauCeti.sphereCone_coe`), and, if `u` vanishes nowhere, vanishes only at the centre
(`TauCeti.sphereCone_eq_zero_iff`).

The main result computes the local index of such a section at the centre
(`SymplecticGeometry.CoordinateDisc.sectionIndex_eq_degree_sphereCone`): if a continuous section
`s` of `L` is the radial extension of `u` times `σ` on the open unit disc, then its local index
`TauCeti.VectorBundleOrientation.sectionIndex` at `φ 0`, for the orientation of `L` as a complex
line, is the degree of the loop `u / ‖u‖` around the circle. The radial extension is not
differentiable at the centre, so the index is computed by local homology rather than by a
Jacobian.

## Proof

Shrink `φ` to the open embedding `ψ w = φ (w / 2)` of the ball into the open unit disc, which
still carries the canonical orientation of the ball to `o`. The frame `σ` identifies the pull-back
of `L` along `ψ` with the trivial bundle `ball × ℂ`, complex-linearly, so preserving the complex
orientations (`TauCeti.VectorBundleOrientation.map_complex`), and it carries the section
`g w = sphereCone u (w / 2)` of the trivial bundle to `s` along `ψ`. So the two sections have the
same local index (`TauCeti.VectorBundleOrientation.sectionIndex_comap_eq_of_fiberwise`). In the
trivial bundle the local index of a section is the local index of the map to `ℂ` it defines
(`TauCeti.VectorBundleOrientation.sectionIndex_trivial_eq_localIndex`), here that of `g` for the
canonical orientations of the ball and of `ℂ`. The map `g` is the restriction of the map
`z ↦ sphereCone u (z / 2)` on `ℂ`, whose only zero is the origin
(`TauCeti.HomologicalOrientation.localIndex_comap`), so its local index is the local degree of
that map at the origin (`TauCeti.HomologicalOrientation.localDegree_eq_localIndex`), which is the
degree of its boundary loop on the circle of radius `2`, the loop `u / ‖u‖`
(`TauCeti.HomologicalOrientation.localDegree_eq_degree_toBasedLoop`).

## Main results

* `SymplecticGeometry.CoordinateDisc.continuousOn_sphereCone_smul`: the radial extension of `u`
  times a frame is continuous wherever the frame is.
* `SymplecticGeometry.CoordinateDisc.sectionIndex_eq_degree_sphereCone`: the local index at the
  centre of a section extended radially into a coordinate disc is the degree of its boundary
  values read in the frame.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.7,
  where the first Chern number of a bundle over a surface is computed from trivializations over a
  disc and over its complement.
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §11 (the Euler class and indices of sections at isolated zeros).
-/

public section

noncomputable section

open Bundle Module Set Topology TauCeti

namespace SymplecticGeometry

namespace CoordinateDisc

variable {M : Type} [TopologicalSpace M] [T2Space M] {E : Type} [NormedAddCommGroup E]
  [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M] {o : HomologicalOrientation M E 2}
  {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedSpace ℂ G] [IsScalarTower ℝ ℂ G]
  [FiniteDimensional ℂ G]
  {L : M → Type} [TopologicalSpace (TotalSpace G L)] [∀ x, AddCommGroup (L x)]
  [∀ x, Module ℝ (L x)] [∀ x, Module ℂ (L x)] [∀ x, IsScalarTower ℝ ℂ (L x)]
  [∀ x, TopologicalSpace (L x)] [FiberBundle G L] [VectorBundle ℂ G L]

omit [NormedSpace ℝ G] [IsScalarTower ℝ ℂ G] [FiniteDimensional ℂ G] [∀ x, Module ℝ (L x)]
  [∀ x, IsScalarTower ℝ ℂ (L x)] in
/-- **The radial extension of boundary values is continuous.** Let `σ` be a section of `L` along a
coordinate disc `φ`, continuous on total spaces on a set `S` of the ball, and `u : S¹ → ℂ`
continuous. Then the section `z ↦ c z • σ z` along `φ`, for `c` the radial extension
`r ζ ↦ r u(ζ)` of `u`, is continuous on `S`. -/
theorem continuousOn_sphereCone_smul (φ : CoordinateDisc o) {σ : ∀ z : ball, L (φ z)}
    {S : Set ball} (hσ : ContinuousOn (fun z ↦ TotalSpace.mk' G (φ z) (σ z)) S)
    (u : C(Circle, ℂ)) :
    ContinuousOn (fun z ↦ TotalSpace.mk' G (φ z)
      (sphereCone (u ∘ Circle.homeomorphSphere.symm) z • σ z)) S := by
  rw [continuousOn_iff_continuous_domRestrict] at hσ ⊢
  exact Continuous.smul_totalSpace
    (c := fun z : S ↦ sphereCone (u ∘ Circle.homeomorphSphere.symm) (z : ball))
    ((continuous_sphereCone (u.continuous.comp Circle.homeomorphSphere.symm.continuous)
      fun _ ↦ u.norm_coe_le_norm _).comp (continuous_subtypeVal.comp continuous_subtypeVal)) hσ

omit [T2Space M] [NormedSpace ℝ G] [IsScalarTower ℝ ℂ G] [∀ x, Module ℝ (L x)]
  [∀ x, IsScalarTower ℝ ℂ (L x)] in
/-- For a nonzero vector `v` of a fibre of a complex line bundle, the map `c ↦ c • v`, as a
continuous complex-linear equivalence from `ℂ`. -/
private def smulRightEquiv (hG : finrank ℂ G = 1) {x : M} (v : L x) (hv : v ≠ 0) :
    ℂ ≃L[ℂ] L x :=
  let eL := (trivializationAt G L x).continuousLinearEquivAt ℂ x
    (FiberBundle.mem_baseSet_trivializationAt' x)
  have hg : eL v ≠ 0 := (map_ne_zero_iff _ eL.injective).2 hv
  have hinj : Function.Injective (LinearMap.toSpanSingleton ℂ G (eL v)) := fun a b h ↦
    smul_left_injective ℂ hg h
  (LinearEquiv.ofBijective (LinearMap.toSpanSingleton ℂ G (eL v))
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [finrank_self, hG])).1 hinj⟩).toContinuousLinearEquiv.trans eL.symm

omit [T2Space M] [NormedSpace ℝ G] [IsScalarTower ℝ ℂ G] [∀ x, Module ℝ (L x)]
  [∀ x, IsScalarTower ℝ ℂ (L x)] in
private theorem smulRightEquiv_apply (hG : finrank ℂ G = 1) {x : M} (v : L x) (hv : v ≠ 0)
    (c : ℂ) : smulRightEquiv hG v hv c = c • v := by
  simp only [smulRightEquiv, ContinuousLinearEquiv.trans_apply,
    LinearEquiv.coe_toContinuousLinearEquiv']
  -- `LinearEquiv.ofBijective f _ c` is `f c = c • eL v` by definition.
  exact (map_smul _ c _).trans (congrArg (c • ·) (ContinuousLinearEquiv.symm_apply_apply _ v))

local instance : VectorBundle ℝ G L := VectorBundle.restrictScalars ℝ ℂ G L

/-- **The local index of a radially extended section.** Let `φ` be a coordinate disc of a surface
`M` with homological orientation `o`, `L` a complex line bundle over `M`, and `σ` a frame of `L`
along `φ` on the open unit disc: a section `z ↦ σ z ∈ L (φ z)`, nowhere zero and continuous on
total spaces there. Let `u : S¹ → ℂ` vanish nowhere, and let `s` be a continuous section of `L`
which at `φ z`, for `‖z‖ < 1`, is `c z • σ z`, for `c` the radial extension `r ζ ↦ r u(ζ)` of `u`.
Then the local index of `s` at the centre `φ 0`, for the orientation of `L` as a complex line, is
the degree of the loop `u / ‖u‖` around the circle. -/
theorem sectionIndex_eq_degree_sphereCone (hn : finrank ℝ E = 2) (hG : finrank ℂ G = 1)
    (φ : CoordinateDisc o) {σ : ∀ z : ball, L (φ z)}
    (hσ : ContinuousOn (fun z ↦ TotalSpace.mk' G (φ z) (σ z)) {z | ‖(z : ℂ)‖ < 1})
    (hσ0 : ∀ z : ball, ‖(z : ℂ)‖ < 1 → σ z ≠ 0) {u : C(Circle, ℂ)} (hu : ∀ ζ, u ζ ≠ 0)
    {s : ∀ x, L x} (hs : Continuous fun x ↦ TotalSpace.mk' G x (s x))
    (hsσ : ∀ z : ball, ‖(z : ℂ)‖ < 1 →
      s (φ z) = sphereCone (u ∘ Circle.homeomorphSphere.symm) z • σ z) :
    (VectorBundleOrientation.reindex (finCongr (by rw [hG]))
        (VectorBundleOrientation.complex G L)).sectionIndex
        (by rw [finrank_real_eq_two_mul_finrank_complex, hG]) o hs (φ 0) =
      Circle.degree (u.normalizeToCircle hu).toBasedLoop := by
  -- The open embedding `j w = φ (w / 2)` of the ball into the open unit disc of `φ`.
  have hr : (0 : ℝ) < 1 / 2 := by norm_num
  have hr2 : ‖(0 : ℂ)‖ + 2 * (1 / 2 : ℝ) ≤ 2 := by norm_num
  set f := affineBall 0 hr hr2 with hf_def
  have hfe : IsOpenEmbedding f := isOpenEmbedding_affineBall 0 hr hr2
  have hf : ∀ w : ball, (f w : ℂ) = ((1 / 2 : ℝ) : ℂ) * w := fun w ↦ by
    rw [hf_def, coe_affineBall_apply, zero_add]
  have hf1 : ∀ w : ball, ‖(f w : ℂ)‖ < 1 := fun w ↦ by
    rw [hf, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.le]
    linarith [mem_ball_iff.1 w.property]
  have hf0 : f 0 = 0 := by
    ext1
    rw [hf, coe_zero, mul_zero]
  let j : C(ball, M) := ⟨fun w ↦ φ (f w), φ.continuous.comp hfe.continuous⟩
  have hj : IsOpenEmbedding j := φ.isOpenEmbedding.comp hfe
  let _ : ChartedSpace E ball :=
    ChartedSpace.ofFinrankEq (𝕜 := ℝ) (E := ℂ) (E' := E) ball
      (Complex.finrank_real_complex.trans hn.symm)
  -- The frame `σ` along `j`, as an isomorphism of the trivial bundle `ball × ℂ` with `j^* L`.
  have hσj : ∀ w : ball, σ (f w) ≠ 0 := fun w ↦ hσ0 (f w) (hf1 w)
  let Φ : ∀ w : ball, Bundle.Trivial ball ℂ w ≃L[ℝ] L (j w) := fun w ↦
    (smulRightEquiv hG (σ (f w)) (hσj w)).restrictScalars' ℝ
  have hΦ : ∀ w c, Φ w c = c • σ (f w) := fun w c ↦
    (congrFun (ContinuousLinearEquiv.coe_restrictScalars' ℝ _) c).trans
      (smulRightEquiv_apply hG _ _ c)
  have hΦc : Continuous fun v : TotalSpace ℂ (Bundle.Trivial ball ℂ) ↦
      TotalSpace.mk' G (j v.proj) (Φ v.proj v.snd) := by
    simp only [hΦ]
    exact Continuous.smul_totalSpace (c := fun v : TotalSpace ℂ (Bundle.Trivial ball ℂ) ↦ v.snd)
      (continuous_snd.comp (Bundle.Trivial.isInducing_toProd ball ℂ).continuous)
      (hσ.comp_continuous (hfe.continuous.comp (FiberBundle.continuous_proj ℂ _))
        fun v ↦ hf1 v.proj)
  have ho : ∀ w, Orientation.map (Fin 2) (Φ w).toLinearEquiv
      (VectorBundleOrientation.trivial ball Complex.orientation w) =
      VectorBundleOrientation.reindex (finCongr (by rw [hG]))
        (VectorBundleOrientation.complex G L) (j w) := by
    intro w
    -- `Φ w` is complex-linear, so it carries the canonical orientation of `ℂ` to that of `L`.
    have h := VectorBundleOrientation.map_complex (F := G) (E := L) (F' := ℂ)
      (E' := Bundle.Trivial ball ℂ) (b' := w) (b := j w)
      (smulRightEquiv hG (σ (f w)) (hσj w)).toLinearEquiv
    rw [VectorBundleOrientation.complex_trivial, VectorBundleOrientation.trivial_apply] at h
    rw [VectorBundleOrientation.trivial_apply, ← reindex_complexOrientation_complex,
      ContinuousLinearEquiv.restrictScalars'_toLinearEquiv, Orientation.map_reindex, h,
      VectorBundleOrientation.reindex_apply, Orientation.reindex_finCongr_reindex_finCongr]
  -- The map `F z = c (z / 2)` on `ℂ`, for `c` the radial extension of `u`, whose only zero is the
  -- origin, and its restriction `g` to the ball, a section of the trivial bundle carried to `s`
  -- by `Φ`.
  set c := sphereCone (u ∘ Circle.homeomorphSphere.symm) with hc_def
  have hc : Continuous c := continuous_sphereCone
    (u.continuous.comp Circle.homeomorphSphere.symm.continuous) fun _ ↦ u.norm_coe_le_norm _
  let F : C(ℂ, ℂ) := ⟨fun z ↦ c (((1 / 2 : ℝ) : ℂ) * z), hc.comp (by fun_prop)⟩
  have hF : ∀ z, F z = c (((1 / 2 : ℝ) : ℂ) * z) := fun _ ↦ rfl
  have hF0 : ∀ z, F z = 0 ↔ z = 0 := fun z ↦ by
    rw [hF, hc_def, sphereCone_eq_zero_iff (f := u ∘ Circle.homeomorphSphere.symm) fun _ ↦ hu _,
      mul_eq_zero, or_iff_right]
    exact Complex.ofReal_ne_zero.2 hr.ne'
  let g : C(ball, ℂ) := F.comp ⟨Subtype.val, continuous_subtypeVal⟩
  have hg : ∀ w, g w = c (f w) := fun w ↦
    (hF w).trans (congrArg _ (hf w).symm)
  have hs₁ : Continuous fun w ↦ TotalSpace.mk' ℂ (E := Bundle.Trivial ball ℂ) w (g w) :=
    (Bundle.Trivial.isInducing_toProd ball ℂ).continuous_iff.2 (continuous_id.prodMk g.continuous)
  have hss : ∀ w, Φ w (g w) = s (j w) := fun w ↦ by
    rw [hΦ, hg]
    exact (hsσ (f w) (hf1 w)).symm
  have h1 := VectorBundleOrientation.sectionIndex_comap_eq_of_fiberwise
    (VectorBundleOrientation.reindex (finCongr (by rw [hG])) (VectorBundleOrientation.complex G L))
    (by rw [finrank_real_eq_two_mul_finrank_complex, hG]) o
    (VectorBundleOrientation.trivial ball Complex.orientation) Complex.finrank_real_complex
    hj hΦc ho hs₁ hs hss 0
  have hj0 : j 0 = φ 0 := congrArg φ hf0
  rw [← hj0, ← h1]
  have hg0 : ∀ w, g w = 0 → w = 0 := fun w h ↦ Subtype.ext ((hF0 w).1 h)
  -- `j` carries the canonical orientation of the ball to `o`.
  have hor : (o.comap hj) 0 = complexHomologicalOrientation ball 0 := by
    rw [← comap_affineBall_complexHomologicalOrientation 0 hr hr2,
      HomologicalOrientation.comap_apply, HomologicalOrientation.comap_apply,
      φ.complexHomologicalOrientation_apply, ← Equiv.symm_trans_apply,
      IsOpenEmbedding.localOrientationEquiv_trans]
    -- `j` is `φ ∘ f` by definition, and its point `j 0` is `φ (f 0)`; the type of a local
    -- orientation depends on its point, so this cannot be rewritten.
    rfl
  -- In the trivial bundle, the local index of the section `g` is that of the map `g`, for the
  -- canonical orientations of the ball and of `ℂ`.
  have h3 := VectorBundleOrientation.sectionIndex_trivial_eq_localIndex (o.comap hj)
    (complexHomologicalOrientation ball) hor g (z := 0) hs₁ ((hF0 _).2 coe_zero) isOpen_univ
    (mem_univ 0) (fun x _ ↦ hg0 x)
  have h4 := HomologicalOrientation.localIndex_comap Complex.finrank_real_complex
    (complexHomologicalOrientation ℂ)
    (complexHomologicalOrientation ℂ) ball.isOpenEmbedding' IsOpenEmbedding.id (f := g) (g := F)
    (x := 0) (Filter.Eventually.of_forall fun _ ↦ rfl)
  rw [comap_subtypeVal_complexHomologicalOrientation, HomologicalOrientation.comap_id, ← h3,
    coe_zero] at h4
  have hF1 : F ⁻¹' {0} = {0} := Set.ext fun z ↦ hF0 z
  rw [h4, ← HomologicalOrientation.localDegree_eq_localIndex _ _ Complex.finrank_real_complex
      Complex.finrank_real_complex F hF1]
  refine HomologicalOrientation.localDegree_eq_degree_toBasedLoop _ two_pos
    (fun z hz ↦ (hF0 z).not.2 (by rintro rfl; norm_num at hz)) fun ζ ↦ ?_
  have hcζ : c ζ = u ζ := by
    rw [hc_def, ← Circle.coe_homeomorphSphere_apply ζ, sphereCone_coe, Function.comp_apply,
      Homeomorph.symm_apply_apply]
  rw [ContinuousMap.coe_normalizeToCircle_apply, hF, ← mul_assoc, ← Complex.ofReal_mul,
    show (1 / 2 : ℝ) * 2 = 1 by norm_num, Complex.ofReal_one, one_mul, hcζ]

end CoordinateDisc

end SymplecticGeometry
