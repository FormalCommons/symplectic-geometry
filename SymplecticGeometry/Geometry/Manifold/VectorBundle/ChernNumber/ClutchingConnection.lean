/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.CoordinateDisc
public import SymplecticGeometry.Geometry.Manifold.DeRham.RadialAngularForm
public import SymplecticGeometry.Geometry.Manifold.FiberBundle.Principal.Connection.Circle
import SymplecticGeometry.Analysis.Complex.RadialProjection
import SymplecticGeometry.Geometry.Manifold.DeRham.Circle
import SymplecticGeometry.Geometry.Manifold.FiberBundle.Basic
import SymplecticGeometry.Topology.Sets.Annulus
import TauCeti.Geometry.Manifold.Algebra.LieGroup
import TauCeti.Topology.Separation.Basic

/-!
# A connection built from clutching frames, and its curvature

Let `P` be a smooth principal `Circle`-bundle over a surface `M`, and let `φ i` be finitely many
coordinate discs of `M` with pairwise disjoint images. Suppose that `P` has sections `σ i`,
smooth on the image of `φ i`, and a section `σout`, smooth off the centres `φ i 0`, whose
transitions on the punctured unit discs are exactly `(z / ‖z‖) ^ k i`:
`σout (φ i z) = σ i (φ i z) • (z / ‖z‖) ^ k i` for `0 < ‖z‖ < 1`. Such sections exist for the
circle bundle of a Hermitian line bundle over a closed surface, with `∑ i, k i` its first Chern
number (`SymplecticGeometry.Bundle.exists_coordinateDisc_unitSection_eq_phase_zpow_smul`).

Fix a smooth cut-off `β`, `0` on `(-∞, a]` and `1` on `[b, ∞)` with `0 < a` and `b < 1`. This
file builds a connection form `α` on `P` that is flat for `σout` (`σout^* α = 0`) away from the
discs of radius `b`, and reads `σ i ^* α = -k i β(‖z‖) dθ` in the `i`-th unit disc. Its curvature
vanishes off the closed discs of radius `b`, and on the `i`-th disc it is `-k i d(β(‖z‖) dθ)` in
the coordinate `z` (`SymplecticGeometry.exists_isCircleConnectionForm_of_collar_eq_zpow_smul`).
With `SymplecticGeometry.CoordinateDisc.integralTopForm_eq_of_mpullback_ofChart_eq` each disc then
contributes `-2π k i` to the integral of the curvature.

The construction: start from any connection form `α₀` (`exists_isCircleConnectionForm`) and add
the pull-back of the `1`-form `a` on `M` that is `-σout^* α₀` off the discs of radius `b` and
`-σ i ^* α₀ - k i β(‖z‖) dθ` on the `i`-th unit disc. The two agree on the collars
`b < ‖z‖ < 1`: there `β = 1`, and by the change of section formula
(`SymplecticGeometry.IsCircleConnectionForm.mpullback_apply_eq_mpullback_division_add`),
`σout^* α₀ = σ i ^* α₀ + g^* dθ` for the transition `g = (z / ‖z‖) ^ k i`, whose pull-back of the
angular form is `k i dθ` (`TauCeti.mpullback_div_norm_zpow_planeAngularForm_apply`). The
curvature is then read off a local section
(`SymplecticGeometry.IsCircleConnectionForm.curvature_apply_eq_mextDeriv_mpullback`).

## Main results

* `SymplecticGeometry.exists_isCircleConnectionForm_of_collar_eq_zpow_smul`: a connection form
  whose curvature vanishes off the closed discs of radius `b` and pulls back along `φ i` to
  `-k i d(β(‖z‖) dθ)`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.7 (the
  first Chern number as the integral of the curvature of a connection built from trivializations
  over discs and over their complement).
-/

public section

noncomputable section

open Bundle Manifold MulOpposite Set TauCeti
open scoped Manifold ContDiff Topology

namespace SymplecticGeometry

attribute [local instance] finrank_real_complex_fact'

variable {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
  [IsManifold (𝓡 2) ∞ M] [T2Space M]
  {o : HomologicalOrientation M (EuclideanSpace ℝ (Fin 2)) 2}

omit [IsManifold (𝓡 2) ∞ M] in
/-- Let `φ` be a coordinate disc whose coordinate is smooth on its image, and `D` a map to the
circle, equal near a point `x` of the image off the centre to the `k`-th power of the angular
coordinate. If `β (‖φ.coord x‖) = 1`, then at `x` the pull-back of the angular form along `D` is
`k` times the pull-back of `β(‖z‖) dθ` along the coordinate. -/
private theorem mpullback_circleAngularForm_eq_of_eventuallyEq_phase_zpow
    (φ : CoordinateDisc o) (hcoord : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℂ) ∞ φ.coord (range φ))
    {x : M} (hx : x ∈ range φ) (hx0 : φ.coord x ≠ 0) {k : ℤ} {D : M → Circle}
    (hDk : D =ᶠ[𝓝 x] fun y ↦ φ.phase y ^ k) {β : ℝ → ℝ} (hβ : β ‖φ.coord x‖ = 1) :
    mpullback (𝓡 2) (𝓡 1) D circleAngularForm x =
      (k : ℝ) • mpullback (𝓡 2) 𝓘(ℝ, ℂ) φ.coord (radialAngularForm β) x := by
  set w := φ.coord x
  have hrange : IsOpen (range φ) := φ.isOpenEmbedding.isOpen_range
  have hcx : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℂ) φ.coord x :=
    (hcoord.contMDiffAt (hrange.mem_nhds hx)).mdifferentiableAt (by simp)
  have hpow : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun z : ℂ ↦ (z / ‖z‖) ^ k) w :=
    (Complex.differentiableAt_div_norm_zpow hx0 k).mdifferentiableAt
  have hW : IsOpen {y ∈ range φ | φ.coord y ≠ 0} :=
    φ.continuousOn_coord.isOpen_inter_preimage hrange isOpen_compl_singleton
  -- `D` is differentiable at `x`, since near `x` it is a power of the smooth angular coordinate.
  have hD : MDifferentiableAt (𝓡 2) (𝓡 1) D x :=
    ((((TauCeti.contMDiff_zpow k).contMDiffAt).comp x ((φ.contMDiffOn_phase hcoord).contMDiffAt
      (hW.mem_nhds ⟨hx, hx0⟩))).mdifferentiableAt (by simp)).congr_of_eventuallyEq hDk
  -- Near `x`, `D`, read in `ℂ`, is `(z / ‖z‖) ^ k` in the coordinate `z`.
  have hcomp : (fun y ↦ (D y : ℂ)) =ᶠ[𝓝 x] (fun z : ℂ ↦ (z / ‖z‖) ^ k) ∘ φ.coord := by
    filter_upwards [hDk, hW.mem_nhds ⟨hx, hx0⟩] with y hy hy'
    rw [hy, Function.comp_apply, Circle.coe_zpow, φ.coe_phase hy'.2]
  have hρ : mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun z : ℂ ↦ (z / ‖z‖) ^ k) planeAngularForm w =
      (k : ℝ) • radialAngularForm β w := by
    rw [mpullback_div_norm_zpow_planeAngularForm_apply hx0, radialAngularForm_def]
    dsimp only
    rw [hβ, one_div, smul_smul]
  have hcoe : MDifferentiableAt (𝓡 1) 𝓘(ℝ, ℂ) (fun z : Circle ↦ (z : ℂ)) (D x) :=
    (contMDiff_coe_sphere (n := 1) (D x)).mdifferentiableAt one_ne_zero
  rw [circleAngularForm_def, ← mpullback_comp_at hD hcoe, Function.comp_def, hcomp.mpullback_eq,
    mpullback_comp_at hcx hpow]
  rw [mpullback_apply_congr (η := (k : ℝ) • radialAngularForm β) hρ, mpullback_smul,
    Pi.smul_apply]

omit [IsManifold (𝓡 2) ∞ M] in
/-- A `2`-form on `M` that is `c` times `d(β(‖z‖) dθ)`, read in the coordinate, on the unit disc of
a coordinate disc `φ`, and that vanishes at the other points of the image of `φ`, pulls back along
`φ` to `c • d(β(‖z‖) dθ)` on the ball of radius `2`. -/
private theorem mpullback_eq_smul_of_eqOn_openDisc (φ : CoordinateDisc o)
    (hφ : MDifferentiable 𝓘(ℝ, ℂ) (𝓡 2) φ)
    (hcoord : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℂ) ∞ φ.coord (range φ)) {β : ℝ → ℝ} {a b : ℝ}
    (hβ : Differentiable ℝ β) (ha : 0 < a) (hb : b < 1) (hβa : ∀ t ≤ a, β t = 0)
    (hβb : ∀ t ≥ b, β t = 1) {f : RoughForm (𝓡 2) M ℝ 2} {c : ℝ}
    (hdisc : ∀ x ∈ φ.openDisc,
      f x = c • mpullback (𝓡 2) 𝓘(ℝ, ℂ) φ.coord (mextDeriv (radialAngularForm β)) x)
    (hout : ∀ z : CoordinateDisc.ball, 1 ≤ ‖(z : ℂ)‖ → f (φ z) = 0) :
    mpullback 𝓘(ℝ, ℂ) (𝓡 2) φ f =
      c • mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : CoordinateDisc.ball → ℂ)
        (mextDeriv (radialAngularForm β)) := by
  funext z
  rw [Pi.smul_apply]
  by_cases hz : ‖(z : ℂ)‖ < 1
  · have hcomp : φ.coord ∘ φ = Subtype.val := funext φ.coord_apply
    have hcx : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℂ) φ.coord (φ z) :=
      (hcoord.contMDiffAt (φ.isOpenEmbedding.isOpen_range.mem_nhds
        (mem_range_self z))).mdifferentiableAt (by simp)
    have h : mpullback 𝓘(ℝ, ℂ) (𝓡 2) φ f z = mpullback 𝓘(ℝ, ℂ) (𝓡 2) φ
        (c • mpullback (𝓡 2) 𝓘(ℝ, ℂ) φ.coord (mextDeriv (radialAngularForm β))) z :=
      mpullback_apply_congr (hdisc _ (φ.apply_mem_openDisc_iff.2 hz))
    rw [h, mpullback_smul, Pi.smul_apply, ← mpullback_comp_at (hφ z) hcx, hcomp]
  · -- outside the unit disc both sides vanish
    have hd : mextDeriv (radialAngularForm β) (z : ℂ) = 0 :=
      image_eq_zero_of_notMem_tsupport fun h ↦
        hz (lt_of_le_of_lt (tsupport_mextDeriv_radialAngularForm_subset hβ ha hβa hβb h).2 hb)
    rw [mpullback_apply_eq_zero (hout z (not_lt.1 hz)), mpullback_apply_eq_zero hd, smul_zero]

variable {P : M → Type*} [TopologicalSpace (TotalSpace Circle P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle Circle P] [∀ b, MulAction Circleᵐᵒᵖ (P b)] [PrincipalBundle Circle P]
  [ContMDiffFiberBundle ∞ Circle P (𝓡 2) (𝓡 1)]

/-- On the collar of a coordinate disc `φ`, where `β = 1` and where `σout = σ • (z / ‖z‖) ^ k`,
the pull-back of a connection form `α` along `σout` is its pull-back along `σ` plus `k` times
`β(‖z‖) dθ` read in the coordinate. -/
private theorem mpullback_apply_eq_add_of_collar
    {α : SmoothForm ((𝓡 2).prod (𝓡 1)) (ManifoldTotalSpace Circle P) ℝ 1}
    (hα : IsCircleConnectionForm α) (φ : CoordinateDisc o)
    (hcoord : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℂ) ∞ φ.coord (range φ)) {k : ℤ} {σ σout : ∀ x, P x}
    (hσ : ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 1)) ∞
      (fun x ↦ ManifoldTotalSpace.homeomorph Circle P ⟨x, σ x⟩) (range φ))
    (hrel : ∀ z : CoordinateDisc.ball, 0 < ‖(z : ℂ)‖ → ‖(z : ℂ)‖ < 1 →
      σout (φ z) = op (φ.phase (φ z) ^ k) • σ (φ z))
    {β : ℝ → ℝ} {b : ℝ} (hβb : ∀ t ≥ b, β t = 1) {z : CoordinateDisc.ball} (hz0 : (z : ℂ) ≠ 0)
    (hbz : b ≤ ‖(z : ℂ)‖) (hz1 : ‖(z : ℂ)‖ < 1)
    (hσout : ContMDiffAt (𝓡 2) ((𝓡 2).prod (𝓡 1)) ∞
      (fun x ↦ ManifoldTotalSpace.homeomorph Circle P ⟨x, σout x⟩) (φ z)) :
    mpullback (𝓡 2) ((𝓡 2).prod (𝓡 1))
        (fun x ↦ ManifoldTotalSpace.homeomorph Circle P ⟨x, σout x⟩) α.val (φ z) =
      mpullback (𝓡 2) ((𝓡 2).prod (𝓡 1))
          (fun x ↦ ManifoldTotalSpace.homeomorph Circle P ⟨x, σ x⟩) α.val (φ z) +
        (k : ℝ) • mpullback (𝓡 2) 𝓘(ℝ, ℂ) φ.coord (radialAngularForm β) (φ z) := by
  have hrange : IsOpen (range φ) := φ.isOpenEmbedding.isOpen_range
  -- near `φ z`, the transition from `σ` to `σout` is the `k`-th power of the phase
  set W := φ '' ((↑) ⁻¹' (annulus ℂ 0 1 : Set ℂ) : Set CoordinateDisc.ball)
  have hWo : IsOpen W := φ.isOpenEmbedding.isOpenMap _ <|
    (annulus ℂ 0 1).isOpen.preimage continuous_subtypeVal
  have hDk : (fun y ↦ PrincipalBundle.division Circle (σ y) (σout y)) =ᶠ[𝓝 (φ z)]
      fun y ↦ φ.phase y ^ k := by
    filter_upwards [hWo.mem_nhds ⟨z, mem_annulus.2 ⟨norm_pos_iff.2 hz0, hz1⟩, rfl⟩] with y hy
    obtain ⟨z', hz', rfl⟩ := hy
    obtain ⟨hz'0, hz'1⟩ := mem_annulus.1 hz'
    exact PrincipalBundle.division_eq_iff.2 (hrel z' hz'0 hz'1).symm
  rw [hα.mpullback_apply_eq_mpullback_division_add hrange hσ (mem_range_self z)
      (hσout.mdifferentiableAt (by simp)),
    mpullback_circleAngularForm_eq_of_eventuallyEq_phase_zpow φ hcoord
      (mem_range_self z) (by rwa [CoordinateDisc.coord_apply]) hDk
      (by rw [CoordinateDisc.coord_apply]; exact hβb _ hbz), add_comm]

variable [SigmaCompactSpace M]

/-- **A connection form built from clutching frames.** Let `P` be a smooth principal
`Circle`-bundle over a surface `M`, and `φ i` finitely many coordinate discs with pairwise
disjoint images, differentiable and with coordinates smooth on their images. Let `σ i` be
sections of `P` smooth on the image of `φ i`, and `σout` a section smooth off the centres
`φ i 0`, with `σout (φ i z) = σ i (φ i z) • (φ i).phase (φ i z) ^ k i` for `0 < ‖z‖ < 1`. Let
`β` be smooth, `0` on `(-∞, a]` and `1` on `[b, ∞)`, with `0 < a` and `b < 1`.

Then `P` has a connection form whose curvature vanishes off the images under the `φ i` of the
closed disc of radius `b`, and whose pull-back along `φ i` is `-k i d(β(‖z‖) dθ)`
(`SymplecticGeometry.radialAngularForm`) on the ball of radius `2`. -/
theorem exists_isCircleConnectionForm_of_collar_eq_zpow_smul {ι : Type*} [Finite ι]
    {φ : ι → CoordinateDisc o} (hφ : ∀ i, MDifferentiable 𝓘(ℝ, ℂ) (𝓡 2) (φ i))
    (hcoord : ∀ i, ContMDiffOn (𝓡 2) 𝓘(ℝ, ℂ) ∞ (φ i).coord (range (φ i)))
    (hdisj : Pairwise fun i j ↦ Disjoint (range (φ i)) (range (φ j)))
    (k : ι → ℤ) {σ : ι → ∀ x, P x} {σout : ∀ x, P x}
    (hσ : ∀ i, ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 1)) ∞
      (fun x ↦ ManifoldTotalSpace.homeomorph Circle P ⟨x, σ i x⟩) (range (φ i)))
    (hσout : ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 1)) ∞
      (fun x ↦ ManifoldTotalSpace.homeomorph Circle P ⟨x, σout x⟩) {x | ∀ i, x ≠ φ i 0})
    (hrel : ∀ i (z : CoordinateDisc.ball), 0 < ‖(z : ℂ)‖ → ‖(z : ℂ)‖ < 1 →
      σout (φ i z) = op ((φ i).phase (φ i z) ^ k i) • σ i (φ i z))
    {β : ℝ → ℝ} {a b : ℝ} (hβ : ContDiff ℝ ∞ β) (ha : 0 < a) (hb : b < 1)
    (hβa : ∀ t ≤ a, β t = 0) (hβb : ∀ t ≥ b, β t = 1) :
    ∃ (α : SmoothForm ((𝓡 2).prod (𝓡 1)) (ManifoldTotalSpace Circle P) ℝ 1)
      (hα : IsCircleConnectionForm α),
      (∀ x, (∀ i, x ∉ φ i '' {z | ‖(z : ℂ)‖ ≤ b}) → hα.curvature.val x = 0) ∧
      ∀ i, mpullback 𝓘(ℝ, ℂ) (𝓡 2) (φ i) hα.curvature.val =
        (-(k i : ℝ)) • mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : CoordinateDisc.ball → ℂ)
          (mextDeriv (radialAngularForm β)) := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  have hab : a ≤ b := by
    by_contra h
    have := hβa b (not_le.1 h).le
    rw [hβb b le_rfl] at this
    exact one_ne_zero this
  obtain ⟨α₀, hα₀⟩ := exists_isCircleConnectionForm (P := P) (IB := 𝓡 2)
  -- notation: sections as maps into the total space, their pull-backs of `α₀`, and the
  -- forms `β(‖z‖) dθ` read in the discs
  set s : (∀ x, P x) → M → ManifoldTotalSpace Circle P :=
    fun τ x ↦ ManifoldTotalSpace.homeomorph Circle P ⟨x, τ x⟩ with hs
  set A : (∀ x, P x) → RoughForm (𝓡 2) M ℝ 1 :=
    fun τ ↦ mpullback (𝓡 2) ((𝓡 2).prod (𝓡 1)) (s τ) α₀.val with hA
  set η : ι → RoughForm (𝓡 2) M ℝ 1 :=
    fun i ↦ mpullback (𝓡 2) 𝓘(ℝ, ℂ) (φ i).coord (radialAngularForm β) with hη
  have hρ : IsSmoothForm 𝓘(ℝ, ℂ) ∞ (radialAngularForm β) :=
    isSmoothForm_radialAngularForm le_rfl hβ ha hβa
  have hrange (i : ι) : IsOpen (range (φ i)) := (φ i).isOpenEmbedding.isOpen_range
  -- the open set off the centres, where `σout` is smooth
  set C := {x : M | ∀ i, x ≠ φ i 0}
  have hCo : IsOpen C := TauCeti.isOpen_forall_ne continuous_id
  -- the closed discs of radius `b`, and the open set `U` off them
  set K : ι → Set M := fun i ↦ φ i '' {z | ‖(z : ℂ)‖ ≤ b}
  set U := ⋂ i, (K i)ᶜ with hU
  have hUo : IsOpen U := isOpen_iInter_of_finite fun i ↦
    ((φ i).isCompact_image_closedBall (hb.trans one_lt_two)).isClosed.isOpen_compl
  have hUC : U ⊆ C := fun x hx i h ↦ by
    refine (mem_iInter.1 hx i) ⟨0, ?_, h.symm⟩
    simpa [CoordinateDisc.coe_zero] using ha.le.trans hab
  have hKD (i : ι) : K i ⊆ (φ i).openDisc := by
    rintro _ ⟨z, hz, rfl⟩
    exact (φ i).apply_mem_openDisc_iff.2 (lt_of_le_of_lt hz hb)
  have hcover (x : M) (hx : x ∉ U) : ∃ i, x ∈ (φ i).openDisc := by
    simp only [hU, mem_iInter, mem_compl_iff, not_forall, not_not] at hx
    obtain ⟨i, hi⟩ := hx
    exact ⟨i, hKD i hi⟩
  have hDr (i : ι) : (φ i).openDisc ⊆ range (φ i) :=
    (φ i).openDisc_subset_disc.trans (φ i).disc_subset_range
  have huniq {i j : ι} {x : M} (hi : x ∈ range (φ i)) (hj : x ∈ range (φ j)) : i = j := by
    by_contra h
    exact (hdisj h).ne_of_mem hi hj rfl
  -- smoothness of the local pieces
  have hsσ (i : ι) {x : M} (hx : x ∈ range (φ i)) :
      ContMDiffAt (𝓡 2) ((𝓡 2).prod (𝓡 1)) ∞ (s (σ i)) x :=
    (hσ i).contMDiffAt ((hrange i).mem_nhds hx)
  have hsout {x : M} (hx : x ∈ C) : ContMDiffAt (𝓡 2) ((𝓡 2).prod (𝓡 1)) ∞ (s σout) x :=
    hσout.contMDiffAt (hCo.mem_nhds hx)
  have hAs {τ : ∀ x, P x} {x : M} (hτ : ContMDiffAt (𝓡 2) ((𝓡 2).prod (𝓡 1)) ∞ (s τ) x) :
      ContMDiffAt (𝓡 2) ((𝓡 2).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) [⋀^Fin 1]→L[ℝ] ℝ)) ∞
        (fun y ↦ TotalSpace.mk' (EuclideanSpace ℝ (Fin 2) [⋀^Fin 1]→L[ℝ] ℝ) y (A τ y)) x :=
    (α₀.isSmoothForm.contMDiff _).mpullback_form hτ (by simp)
  have hηs (i : ι) {x : M} (hx : x ∈ range (φ i)) :
      ContMDiffAt (𝓡 2) ((𝓡 2).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) [⋀^Fin 1]→L[ℝ] ℝ)) ∞
        (fun y ↦ TotalSpace.mk' (EuclideanSpace ℝ (Fin 2) [⋀^Fin 1]→L[ℝ] ℝ) y (η i y)) x :=
    (hρ.contMDiff _).mpullback_form ((hcoord i).contMDiffAt ((hrange i).mem_nhds hx)) (by simp)
  -- on the collars, `σout^* α₀ = σ i ^* α₀ + k i β(‖z‖) dθ`
  have hcollar (i : ι) (z : CoordinateDisc.ball) (hbz : b < ‖(z : ℂ)‖) (hz1 : ‖(z : ℂ)‖ < 1) :
      A σout (φ i z) = A (σ i) (φ i z) + (k i : ℝ) • η i (φ i z) := by
    have hz0 : (z : ℂ) ≠ 0 := norm_pos_iff.1 ((ha.trans_le hab).trans hbz)
    have hxC : φ i z ∈ C := fun j h ↦ by
      obtain rfl := huniq (mem_range_self z) ⟨0, h.symm⟩
      exact hz0 (by rw [(φ i).injective h, CoordinateDisc.coe_zero])
    simp only [hA, hs, hη]
    exact mpullback_apply_eq_add_of_collar hα₀ (φ i) (hcoord i) (hσ i) (hrel i) hβb hz0 hbz.le hz1
      (hsout hxC)
  -- the glued `1`-form `a` on `M`
  let a : RoughForm (𝓡 2) M ℝ 1 := fun x ↦
    if h : ∃ i, x ∈ (φ i).openDisc then -A (σ h.choose) x - (k h.choose : ℝ) • η h.choose x
    else -A σout x
  have ha_disc {i : ι} {x : M} (hx : x ∈ (φ i).openDisc) :
      a x = -A (σ i) x - (k i : ℝ) • η i x := by
    have h : ∃ i, x ∈ (φ i).openDisc := ⟨i, hx⟩
    have hi : h.choose = i := huniq (hDr _ h.choose_spec) (hDr i hx)
    simp only [a, h, dite_true, hi]
  have ha_out {x : M} (hx : x ∈ U) : a x = -A σout x := by
    by_cases h : ∃ i, x ∈ (φ i).openDisc
    · obtain ⟨i, hi⟩ := h
      obtain ⟨z, hz1, rfl⟩ := (φ i).mem_openDisc_iff.1 hi
      have hbz : b < ‖(z : ℂ)‖ := not_le.1 fun h ↦ mem_iInter.1 hx i ⟨z, h, rfl⟩
      rw [ha_disc hi, hcollar i z hbz hz1, neg_add, sub_eq_add_neg]
    · simp only [a, h, dite_false]
  have hasmooth : IsSmoothForm (𝓡 2) ∞ a := by
    rw [isSmoothForm_def]
    intro x
    by_cases hx : x ∈ U
    · refine ((hAs (hsout (hUC hx))).neg_section).congr_of_eventuallyEq ?_
      filter_upwards [hUo.mem_nhds hx] with y hy
      rw [ha_out hy]
      rfl
    · obtain ⟨i, hi⟩ := hcover x hx
      refine ((hAs (hsσ i (hDr i hi))).neg_section.sub_section
        ((hηs i (hDr i hi)).const_smul_section (a := (k i : ℝ)))).congr_of_eventuallyEq ?_
      filter_upwards [(φ i).isOpen_openDisc.mem_nhds hi] with y hy
      rw [ha_disc hy]
      rfl
  set a' : SmoothForm (𝓡 2) M ℝ 1 := ⟨a, hasmooth.mem_smoothBundleForms⟩
  have hα := hα₀.add_mpullback a'
  refine ⟨_, hα, ?_⟩
  -- the pull-back of the new connection form along a section
  have hpull {τ : ∀ x, P x} {y : M}
      (hτ : ContMDiffAt (𝓡 2) ((𝓡 2).prod (𝓡 1)) ∞ (s τ) y) :
      mpullback (𝓡 2) ((𝓡 2).prod (𝓡 1)) (s τ) (α₀ + SmoothForm.mpullback
        (ManifoldTotalSpace.projContMDiffMap ∞ Circle P (𝓡 2) (𝓡 1))
        (ManifoldTotalSpace.projContMDiffMap ∞ Circle P (𝓡 2) (𝓡 1)).contMDiff a').val y =
        A τ y + a y :=
    ManifoldTotalSpace.mpullback_add_mpullback_proj_apply α₀ a' (hτ.mdifferentiableAt (by simp))
  -- off the discs of radius `b` the curvature vanishes
  have hcurv_out {x : M} (hx : x ∈ U) : hα.curvature.val x = 0 := by
    rw [hα.curvature_apply_eq_mextDeriv_mpullback (hsout (hUC hx)),
      mextDeriv_congr_of_eventuallyEq (η := 0) ?_, mextDeriv_zero]
    · rfl
    filter_upwards [hUo.mem_nhds hx] with y hy
    rw [hpull (hsout (hUC hy)), ha_out hy, add_neg_cancel]
    rfl
  -- on the `i`-th unit disc it is `-k i d(β(‖z‖) dθ)` in the coordinate
  have hcurv_disc {i : ι} {x : M} (hx : x ∈ (φ i).openDisc) :
      hα.curvature.val x = (-(k i : ℝ)) • mpullback (𝓡 2) 𝓘(ℝ, ℂ) (φ i).coord
        (mextDeriv (radialAngularForm β)) x := by
    rw [hα.curvature_apply_eq_mextDeriv_mpullback (hsσ i (hDr i hx)),
      mextDeriv_congr_of_eventuallyEq (η := (-(k i : ℝ)) • η i) ?_, mextDeriv_smul,
      Pi.smul_apply, hη, mpullback_mextDeriv_at
        (((hcoord i).contMDiffAt ((hrange i).mem_nhds (hDr i hx))).of_le (by simp))
        ((hρ.contMDiff _).of_le (by simp))]
    filter_upwards [(φ i).isOpen_openDisc.mem_nhds hx] with y hy
    rw [hpull (hsσ i (hDr i hy)), ha_disc hy, Pi.smul_apply]
    abel_nf
    exact (smul_assoc _ _ _).symm
  refine ⟨fun x hx ↦ hcurv_out (mem_iInter.2 hx),
    fun i ↦ mpullback_eq_smul_of_eqOn_openDisc (φ i) (hφ i) (hcoord i)
      (hβ.differentiable (by simp)) ha hb hβa hβb (fun x hx ↦ hcurv_disc hx) fun z hz ↦
        hcurv_out (mem_iInter.2 fun j hj ↦ ?_)⟩
  -- the points of the image of `φ i` outside its unit disc lie off the discs of radius `b`
  obtain ⟨z', hz', h⟩ := hj
  obtain rfl := huniq ⟨z', h⟩ (mem_range_self z)
  exact (lt_of_le_of_lt ((φ j).injective h ▸ hz') hb).not_ge hz

end SymplecticGeometry
