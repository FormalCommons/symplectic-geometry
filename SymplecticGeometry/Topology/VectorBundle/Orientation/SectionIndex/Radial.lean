/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Analysis.Normed.Module.Ball.Radial.Cone
public import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.CoordinateDisc
public import SymplecticGeometry.Topology.VectorBundle.Orientation.SectionIndex.Frame
public import SymplecticGeometry.Topology.VectorBundle.Section
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Winding
public import TauCeti.Analysis.Complex.Circle.Basic
public import TauCeti.Topology.Circle.Normalize
public import TauCeti.Topology.VectorBundle.Orientation.Complex.Basic
public import SymplecticGeometry.Topology.VectorBundle.Complex.RestrictScalars

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
circle (`TauCeti.sphereCone_comp_homeomorphSphere_symm_coe`), and, if `u` vanishes nowhere,
vanishes only at the centre (`TauCeti.sphereCone_eq_zero_iff`).

The main result computes the local index of such a section at the centre
(`SymplecticGeometry.CoordinateDisc.sectionIndex_eq_degree_sphereCone`): if a continuous section
`s` of `L` is the radial extension of `u` times `σ` on the open unit disc, then its local index
`TauCeti.VectorBundleOrientation.sectionIndex` at `φ 0`, for the orientation of `L` as a complex
line, is the degree of the loop `u / ‖u‖` around the circle. The radial extension is not
differentiable at the centre, so the index is computed by local homology rather than by a
Jacobian.

## Proof

Shrink `φ` to the coordinate disc `ψ w = φ (w / 2)` (`SymplecticGeometry.CoordinateDisc.comp`),
whose image lies in the open unit disc, so that `w ↦ σ (w / 2)` is a frame along `ψ` over the
whole ball. In it `s` reads `g w = sphereCone u (w / 2)`, so the local index of `s` at `φ 0` is
the local index of `g` at the origin, for the canonical orientations of the ball and of `ℂ`
(`SymplecticGeometry.CoordinateDisc.sectionIndex_eq_localIndex_of_eq_smul`). The map `g` is the
restriction of the map `z ↦ sphereCone u (z / 2)` on `ℂ`, whose only zero is the origin
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

section Continuity

variable {M : Type} [TopologicalSpace M] {G : Type} [NormedAddCommGroup G] [NormedSpace ℂ G]
  {L : M → Type} [TopologicalSpace (TotalSpace G L)] [∀ x, AddCommGroup (L x)]
  [∀ x, Module ℂ (L x)] [∀ x, TopologicalSpace (L x)] [FiberBundle G L] [VectorBundle ℂ G L]

/-- **The radial extension of boundary values is continuous.** Let `φ` map the ball to `M`, `σ` a
section of `L` along `φ` that is continuous on total spaces on a set `S` of the ball, and
`u : S¹ → ℂ` continuous. Then the section `z ↦ c z • σ z` along `φ`, for `c` the radial extension
`r ζ ↦ r u(ζ)` of `u`, is continuous on `S`. -/
theorem continuousOn_sphereCone_smul {φ : ball → M} {σ : ∀ z : ball, L (φ z)} {S : Set ball}
    (hσ : ContinuousOn (fun z ↦ TotalSpace.mk' G (φ z) (σ z)) S) (u : C(Circle, ℂ)) :
    ContinuousOn (fun z ↦ TotalSpace.mk' G (φ z)
      (sphereCone (u ∘ Circle.homeomorphSphere.symm) z • σ z)) S :=
  ((continuous_sphereCone_comp_homeomorphSphere_symm u.continuous).comp
    continuous_subtypeVal).continuousOn.smul_totalSpace hσ

end Continuity

variable {M : Type} [TopologicalSpace M] [T2Space M] {E : Type} [NormedAddCommGroup E]
  [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M] {o : HomologicalOrientation M E 2}
  {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedSpace ℂ G] [IsScalarTower ℝ ℂ G]
  [FiniteDimensional ℂ G]
  {L : M → Type} [TopologicalSpace (TotalSpace G L)] [∀ x, AddCommGroup (L x)]
  [∀ x, Module ℝ (L x)] [∀ x, Module ℂ (L x)] [∀ x, IsScalarTower ℝ ℂ (L x)]
  [∀ x, TopologicalSpace (L x)] [FiberBundle G L] [VectorBundle ℂ G L]

open scoped VectorBundle.ComplexToReal

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
  -- The coordinate disc `ψ w = φ (w / 2)`, whose image lies in the open unit disc of `φ`.
  have hr : (0 : ℝ) < 1 / 2 := by norm_num
  have hr2 : ‖(0 : ℂ)‖ + 2 * (1 / 2 : ℝ) ≤ 2 := by norm_num
  have hmem := add_mul_mem_ball hr hr2
  set f := affineBall 0 hmem
  let ψ := φ.comp f (isOpenEmbedding_affineBall 0 hmem hr.ne')
    (comap_affineBall_complexHomologicalOrientation 0 hmem hr.ne')
  have hf : ∀ w : ball, (f w : ℂ) = ((1 / 2 : ℝ) : ℂ) * w := fun w ↦ by
    rw [coe_affineBall_apply, zero_add]
  have hf1 : ∀ w : ball, ‖(f w : ℂ)‖ < 1 := fun w ↦ by
    rw [hf, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.le]
    linarith [mem_ball_iff.1 w.property]
  have hψ : ⇑ψ = fun w ↦ φ (f w) := funext fun w ↦ comp_apply _ _ _ _ w
  have hf0 : f 0 = 0 := by
    ext1
    rw [hf, coe_zero, mul_zero]
  -- The map `F z = c (z / 2)` on `ℂ`, for `c` the radial extension of `u`, whose only zero is the
  -- origin, and its restriction `g` to the ball, the coefficient of `s` in the frame along `ψ`.
  set c := sphereCone (u ∘ Circle.homeomorphSphere.symm) with hc_def
  let F : C(ℂ, ℂ) := ⟨fun z ↦ c (((1 / 2 : ℝ) : ℂ) * z),
    (continuous_sphereCone_comp_homeomorphSphere_symm u.continuous).comp (by fun_prop)⟩
  have hF : ∀ z, F z = c (((1 / 2 : ℝ) : ℂ) * z) := fun _ ↦ rfl
  have hF0 : ∀ z, F z = 0 ↔ z = 0 := fun z ↦ by
    rw [hF, hc_def, sphereCone_eq_zero_iff (f := u ∘ Circle.homeomorphSphere.symm) fun _ ↦ hu _,
      mul_eq_zero, or_iff_right]
    exact Complex.ofReal_ne_zero.2 hr.ne'
  let g : C(ball, ℂ) := F.comp ⟨Subtype.val, continuous_subtypeVal⟩
  have hg : ∀ w, g w = c (f w) := fun w ↦
    (hF w).trans (congrArg _ (hf w).symm)
  -- In the frame `w ↦ σ (f w)` along `ψ`, the local index of `s` is the local index of `g`.
  have h3 := sectionIndex_eq_localIndex_of_eq_smul hn hG ψ hψ (σ := fun w ↦ σ (f w))
    (hσ.comp_continuous (isOpenEmbedding_affineBall 0 hmem hr.ne').continuous hf1)
    (fun w ↦ hσ0 (f w) (hf1 w)) g hs (fun w ↦ (hsσ (f w) (hf1 w)).trans (by rw [hg]))
    ((hF0 _).2 coe_zero) isOpen_univ (mem_univ 0) fun w _ h ↦ Subtype.ext ((hF0 w).1 h)
  rw [hf0] at h3
  rw [h3]
  -- The local index of `g` is that of `F`, which is a local degree.
  have h4 := HomologicalOrientation.localIndex_comap (complexHomologicalOrientation ℂ)
    (complexHomologicalOrientation ℂ) Complex.finrank_real_complex
    ball.isOpenEmbedding' IsOpenEmbedding.id (f := g) (g := F) (x := 0)
    (Filter.Eventually.of_forall fun _ ↦ rfl)
  rw [comap_subtypeVal_complexHomologicalOrientation, HomologicalOrientation.comap_id,
    coe_zero] at h4
  have hF1 : F ⁻¹' {0} = {0} := Set.ext fun z ↦ hF0 z
  rw [h4, ← HomologicalOrientation.localDegree_eq_localIndex _ _ Complex.finrank_real_complex
      Complex.finrank_real_complex F hF1]
  refine HomologicalOrientation.localDegree_eq_degree_toBasedLoop _ two_pos
    (fun z hz ↦ (hF0 z).not.2 (by rintro rfl; norm_num at hz)) fun ζ ↦ ?_
  rw [ContinuousMap.coe_normalizeToCircle_apply, hF, ← mul_assoc, ← Complex.ofReal_mul,
    show (1 / 2 : ℝ) * 2 = 1 by norm_num, Complex.ofReal_one, one_mul, hc_def,
    sphereCone_comp_homeomorphSphere_symm_coe]

end CoordinateDisc

end SymplecticGeometry
