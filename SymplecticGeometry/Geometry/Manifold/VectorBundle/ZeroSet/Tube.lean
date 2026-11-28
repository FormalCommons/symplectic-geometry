/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import Mathlib.Topology.Homotopy.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Linearization

import TauCeti.Geometry.Manifold.Morse.Bott.DiscBundle
import TauCeti.Geometry.Manifold.Morse.Bott.Index.Zero
import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.Metric
import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Basic
import TauCeti.Topology.Order.Sublevel
import SymplecticGeometry.Geometry.Manifold.VectorBundle.ZeroSet.MorseBott

/-!
# A thin tube around the zero set of a transverse section retracts onto it

Let `E' → X` be a smooth real vector bundle of finite rank with a smooth bundle metric over a
compact, Hausdorff, second-countable, boundaryless manifold `X`, and let `s` be a smooth section
transverse to the zero section. We show that for some `ε₀ > 0` and every `0 < ε ≤ ε₀`, the zero
set `Z = {s = 0}` is a strong deformation retract of the tube `T_ε = {‖s‖² ≤ ε}`: there is a
retraction `r : C(T_ε, Z)` fixing `Z`, and the inclusion composed with `r` is homotopic to the
identity of `T_ε` relative to `Z`
(`SymplecticGeometry.exists_pos_forall_retraction_sublevel_norm_sq`).

The zero set, embedded by `TauCeti.SmoothEmbedding.ofTransverseSection`, is a Morse–Bott critical
submanifold of `‖s‖²` of index `0` on the level `0`
(`TauCeti.SmoothEmbedding.isNondegenerateCriticalSubmanifold_norm_sq_ofTransverseSection`,
`TauCeti.SmoothEmbedding.manifoldMorseIndex_norm_sq_ofTransverseSection`), and for small `ε` the
band `{‖s‖² ≤ ε}` has no other critical points
(`SymplecticGeometry.exists_pos_forall_notMem_criticalPoints_norm_sq`). Tau Ceti's
`IsNondegenerateCriticalSubmanifold.exists_sublevel_union_negativeDiscBundle_deformation`
(namespace `TauCeti.SmoothEmbedding`), at the level `0`, retracts `{‖s‖² ≤ ε}` onto
`{‖s‖² ≤ -ε} ∪ Θ(D_ε)`. The first set is empty since `‖s‖² ≥ 0`, and in index `0` the image of
the negative disc bundle is the zero set (Tau Ceti's
`image_negativeDiscBundle_eq_range_of_manifoldMorseIndex_eq_zero`, in the same namespace).
The use of these two results, with a fibre metric from
`TauCeti.SmoothEmbedding.nonempty_contMDiffRiemannianMetric_normalSpace`, follows the private
`exists_isIso_singularHomologyMap_union_range` of Tau Ceti's
`TauCeti/Geometry/Manifold/Morse/Bott/Index/Zero.lean`. Tau Ceti's theorem needs a nonempty zero
set; when the zero set is empty, so is the tube for small `ε`, by compactness.

## Main results

* `SymplecticGeometry.exists_pos_forall_retraction_sublevel_norm_sq`: thin tubes `{‖s‖² ≤ ε}`
  strongly deformation retract onto the zero set of a transverse section.

## References

* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
* [D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*][McDuffSalamon2012],
  Appendix A.3
-/

public section

open Bundle Function Module Set
open scoped ContDiff Manifold

variable {V G X F' : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace G] {J : ModelWithCorners ℝ V G} [J.Boundaryless]
  [TopologicalSpace X] [ChartedSpace G X] [IsManifold J ∞ X]
  [NormedAddCommGroup F'] [NormedSpace ℝ F'] [FiniteDimensional ℝ F']
  {E' : X → Type*} [TopologicalSpace (TotalSpace F' E')] [∀ x, NormedAddCommGroup (E' x)]
  [∀ x, InnerProductSpace ℝ (E' x)] [FiberBundle F' E'] [VectorBundle ℝ F' E']
  [ContMDiffVectorBundle ∞ F' E' J] [IsContMDiffRiemannianBundle J ∞ F' E']
  {s : ∀ x, E' x}

namespace SymplecticGeometry

open TauCeti

/-- **Thin tubes around the zero set of a transverse section retract onto it.** Let `s` be a
smooth section of a smooth real vector bundle with a smooth bundle metric over a compact,
Hausdorff, second-countable, boundaryless manifold, transverse to the zero section. Then there is
`ε₀ > 0` such that for every `0 < ε ≤ ε₀` the zero set `{s = 0}` is a strong deformation retract
of the tube `{‖s‖² ≤ ε}`: it lies in the tube, and there is a retraction `r` of the tube onto it
such that the inclusion composed with `r` is homotopic to the identity of the tube relative to the
zero set. -/
theorem exists_pos_forall_retraction_sublevel_norm_sq [CompactSpace X] [T2Space X]
    [SecondCountableTopology X]
    (hsm : ContMDiff J (J.prod 𝓘(ℝ, F')) ∞ fun x ↦ TotalSpace.mk' F' x (s x))
    (hs : ∀ x, s x = 0 → Surjective (sectionLinearization (F := F') J _root_.id s x)) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε, 0 < ε → ε ≤ ε₀ →
      ∃ (hZT : {x : X | s x = 0} ⊆ {x | ‖s x‖ ^ 2 ≤ ε})
        (r : C({x : X | ‖s x‖ ^ 2 ≤ ε}, {x : X | s x = 0})),
        (∀ z, r (ContinuousMap.inclusion hZT z) = z) ∧
        ((ContinuousMap.inclusion hZT).comp r).HomotopicRel (ContinuousMap.id _)
          {y | s y = 0} := by
  have hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  have hf := (contMDiff_norm_sq_bundle J ∞ F' E').comp hsm
  have hZT (ε : ℝ) (hε : 0 < ε) : {x : X | s x = 0} ⊆ {x | ‖s x‖ ^ 2 ≤ ε} :=
    fun x (hx : s x = 0) ↦ by simp [hx, hε.le]
  by_cases hZ : ∃ x, s x = 0
  swap
  · -- With no zeros, the tube is empty for small `ε`, so the identity is a retraction.
    push Not at hZ
    obtain ⟨δ, hδ, hδZ⟩ := exists_pos_sublevel_subset_of_mem_nhdsSet hf.continuous
      (A := ∅) (W := ∅) (fun x _ ↦ pow_pos (norm_pos_iff.2 (hZ x)) 2) (by simp)
    refine ⟨δ, hδ, fun ε hε hεδ ↦ ⟨hZT ε hε, ?_⟩⟩
    have hTZ : {x : X | ‖s x‖ ^ 2 ≤ ε} ⊆ {x | s x = 0} :=
      fun x hx ↦ (hδZ (le_trans hx hεδ :)).elim
    have hid : (ContinuousMap.inclusion (hZT ε hε)).comp (ContinuousMap.inclusion hTZ) =
        ContinuousMap.id _ := by
      ext
      simp
    refine ⟨ContinuousMap.inclusion hTZ, fun z ↦ Subtype.ext (by simp), ⟨?_⟩⟩
    rw [hid]
    exact .refl _ _
  obtain ⟨x₀, hx₀⟩ := hZ
  -- Transversality at a zero bounds the rank of the bundle by the dimension of `X`.
  have hk : finrank ℝ F' ≤ finrank ℝ V := by
    have := VectorBundle.finiteDimensional ℝ F' E' x₀
    have := LinearMap.finrank_le_finrank_of_surjective
      (f := (sectionLinearization (F := F') J _root_.id s x₀).toLinearMap) (hs x₀ hx₀)
    exact (VectorBundle.finrank_eq ℝ F' E' x₀).symm.le.trans this
  let E := EuclideanSpace ℝ (Fin (finrank ℝ V - finrank ℝ F'))
  have hE : finrank ℝ E + finrank ℝ F' = finrank ℝ V := by
    rw [finrank_euclideanSpace_fin]
    omega
  have hdim : finrank ℝ F' = finrank ℝ V - finrank ℝ E := by omega
  let := transverseZeroSetChartedSpace hn hsm hs hE
  have := isManifold_transverseZeroSet hn hsm hs hE
  let i := SmoothEmbedding.ofTransverseSection hn hsm hs hE
  have hi : range i = {x | s x = 0} := SmoothEmbedding.range_ofTransverseSection hn hsm hs hE
  have : CompactSpace ↥{x : X | s x = 0} :=
    isCompact_iff_compactSpace.1 (hi ▸ (SmoothEmbedding.isClosed_range_ofTransverseSection hn hsm hs
      hE)).isCompact
  have : Nonempty ↥{x : X | s x = 0} := ⟨⟨x₀, hx₀⟩⟩
  have hcrit := SmoothEmbedding.isNondegenerateCriticalSubmanifold_norm_sq_ofTransverseSection
    hn hsm hs hE (by simp)
  have hidx := SmoothEmbedding.manifoldMorseIndex_norm_sq_ofTransverseSection hn hsm hs hE
  have hc (z : ↥{x : X | s x = 0}) : ‖s (i z)‖ ^ 2 = 0 := by
    simp [i, SmoothEmbedding.ofTransverseSection_apply_eq_zero hn hsm hs hE z]
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  obtain ⟨g⟩ := i.nonempty_contMDiffRiemannianMetric_normalSpace hn hdim
  obtain ⟨Θ, -, hΘi, -, ε₀, hε₀, hmain⟩ :=
    hcrit.exists_sublevel_union_negativeDiscBundle_deformation hn hf hc hdim g
  obtain ⟨ε₁, hε₁, hε₁crit⟩ := exists_pos_forall_notMem_criticalPoints_norm_sq hsm hs (by simp)
  refine ⟨min (ε₀ / 2) ε₁, lt_min (half_pos hε₀) hε₁, fun ε hε hεε₀ ↦ ⟨hZT ε hε, ?_⟩⟩
  have hband : criticalPoints J (fun y ↦ ‖s y‖ ^ 2) ∩
      (fun y ↦ ‖s y‖ ^ 2) ⁻¹' Icc (0 - ε) (0 + ε) ⊆ range i := by
    rintro x ⟨hx, -, hxε⟩
    rw [hi]
    by_contra hsx
    exact hε₁crit x (pow_pos (norm_pos_iff.2 hsx) 2)
      (by linarith [min_le_right (ε₀ / 2) ε₁]) hx
  obtain ⟨-, hr⟩ := hmain ε ⟨hε, by linarith [min_le_left (ε₀ / 2) ε₁]⟩
    ((isClosed_Icc.preimage hf.continuous).isCompact) hband
  -- Below the level `0` the sublevel is empty, and in index `0` the disc bundle is the zero set.
  have hset : {y | ‖s y‖ ^ 2 ≤ 0 - ε} ∪
      Θ '' hcrit.negativeDiscBundle hn F' g.toRiemannianMetric ε = {x | s x = 0} := by
    rw [hcrit.image_negativeDiscBundle_eq_range_of_manifoldMorseIndex_eq_zero hn hidx
      g.toRiemannianMetric hΘi hε.le, hi, union_eq_right]
    intro y (hy : ‖s y‖ ^ 2 ≤ 0 - ε)
    nlinarith [sq_nonneg ‖s y‖]
  rw [hset, zero_add] at hr
  obtain ⟨r, hr, ⟨H⟩⟩ := hr
  refine ⟨(ContinuousMap.inclusion inter_subset_right).comp r, fun z ↦ ?_, ⟨?_⟩⟩
  · have hz : ContinuousMap.inclusion (hZT ε hε) z =
        ContinuousMap.inclusion (inter_subset_left :
          {x : X | ‖s x‖ ^ 2 ≤ ε} ∩ {x | s x = 0} ⊆ _) ⟨z, hZT ε hε z.property, z.property⟩ :=
      Subtype.ext (by simp)
    rw [ContinuousMap.comp_apply, hz, hr]
    exact Subtype.ext (by simp)
  · rwa [← ContinuousMap.comp_assoc, ContinuousMap.inclusion_comp_inclusion]

end SymplecticGeometry

end
