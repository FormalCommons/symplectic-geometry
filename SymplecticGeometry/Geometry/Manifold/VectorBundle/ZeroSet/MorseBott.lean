/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import TauCeti.Geometry.Manifold.Morse.Bott.Basic
public import TauCeti.Geometry.Manifold.Morse.Index
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.ZeroSet.Embedding

import TauCeti.Geometry.Manifold.Riemannian.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Basic
import SymplecticGeometry.Geometry.Manifold.Morse.Hessian
import SymplecticGeometry.Topology.VectorBundle.Riemannian

/-!
# The zero set of a transverse section is a Morse–Bott minimum of `‖s‖²`

Let `E' → X` be a `C^m` real vector bundle, `2 ≤ m`, with a `C^m` bundle metric, over a
boundaryless manifold `X`, and let `s` be a `C^m` section. The function `y ↦ ‖s y‖ ^ 2` is then
`C^m` (`(TauCeti.contMDiff_norm_sq_bundle J m F' E').comp hsm`) and nonnegative, so each zero of
`s` is a local minimum of it: a critical point of Morse index `0`.

At a zero `z`, every vector in the kernel of the critical Hessian of `‖s‖²` lies in the kernel of
the linearization `L = TauCeti.sectionLinearization J id s z`
(`TauCeti.ker_criticalHessian_norm_sq_le_ker_sectionLinearization`). Indeed, in the
trivialization at `z` the section has fibre coordinates `φ`, and near `z` the bundle norm
dominates `‖A ∘ φ‖` for a suitable injective linear map `A` into a Euclidean space
(`exists_injective_norm_trivializationAt_le`). So
`‖s‖² - ‖A ∘ φ‖²` has a local minimum at `z`, and its Hessian there is positive semidefinite,
while the Hessian of `‖A ∘ φ‖²` at `z` is `2 ⟪A (dφ u), A (dφ w)⟫`
(`TauCeti.criticalHessian_norm_sq_continuousLinearMap_comp_apply_of_eq_zero`). A vector `u` in
the kernel of the Hessian of `‖s‖²` therefore has `A (dφ u) = 0`, so `dφ u = 0` and `L u = 0`.

For `s` transverse to the zero section, the kernel of `L` is the tangent space of the zero set
(`SymplecticGeometry.range_mfderiv_coe_transverseZeroSet`), so the zero set, embedded by
`TauCeti.SmoothEmbedding.ofTransverseSection`, is a nondegenerate critical submanifold of
`‖s‖²` (`TauCeti.SmoothEmbedding.isNondegenerateCriticalSubmanifold_norm_sq_ofTransverseSection`)
of Morse index `0` (`TauCeti.SmoothEmbedding.manifoldMorseIndex_norm_sq_ofTransverseSection`).

## Main results

* `TauCeti.ker_criticalHessian_norm_sq_le_ker_sectionLinearization`: at a zero of a `C^m`
  section, `2 ≤ m`, the kernel of the Hessian of `‖s‖²` lies in the kernel of the linearization
  of `s`.
* `TauCeti.SmoothEmbedding.isNondegenerateCriticalSubmanifold_norm_sq_ofTransverseSection`: the
  zero set of a transverse section is a Morse–Bott critical submanifold of `‖s‖²`.
* `TauCeti.SmoothEmbedding.manifoldMorseIndex_norm_sq_ofTransverseSection`: its Morse index is
  `0` at every point.

## References

* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
* [D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*][McDuffSalamon2012],
  Appendix A.3
-/

public section

open Bundle Filter Function Module Set
open scoped ContDiff Manifold Topology

variable {V G X F' E : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace G] {J : ModelWithCorners ℝ V G} [J.Boundaryless]
  [TopologicalSpace X] [ChartedSpace G X]
  [NormedAddCommGroup F'] [NormedSpace ℝ F'] [FiniteDimensional ℝ F']
  {E' : X → Type*} [TopologicalSpace (TotalSpace F' E')] [∀ x, NormedAddCommGroup (E' x)]
  [∀ x, InnerProductSpace ℝ (E' x)] [FiberBundle F' E'] [VectorBundle ℝ F' E']
  {m : ℕ∞ω} [ContMDiffVectorBundle m F' E' J] [IsContMDiffRiemannianBundle J m F' E']
  {s : ∀ x, E' x}

namespace TauCeti

/-- **The Hessian of `‖s‖²` at a zero of a section.** On a boundaryless manifold, let `s` be a
section of a `C^m` real vector bundle with a `C^m` bundle metric, `2 ≤ m`, which is `C^m` at a
zero `z`. Then every vector in the kernel of the critical Hessian of `y ↦ ‖s y‖ ^ 2` at `z` lies
in the kernel of the linearization of `s` at `z`. -/
theorem ker_criticalHessian_norm_sq_le_ker_sectionLinearization (hm2 : 2 ≤ m) {z : X}
    (hsm : ContMDiffAt J (J.prod 𝓘(ℝ, F')) m (fun x ↦ TotalSpace.mk' F' x (s x)) z)
    (hz : s z = 0) :
    (criticalHessian J (fun y ↦ ‖s y‖ ^ 2) z).ker ≤
      (sectionLinearization (F := F') J _root_.id s z).ker := by
  intro u hu
  have := IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := J) (n := m)
    (F := F') (V := E')
  set e := trivializationAt F' E' z
  have hzb : z ∈ e.baseSet := mem_baseSet_trivializationAt F' E' z
  set φ : X → F' := fun y ↦ (e ⟨y, s y⟩).2 with hφ_def
  have hφm : ContMDiffAt J 𝓘(ℝ, F') m φ z :=
    ((e.contMDiffAt_iff (n := m) (IM := J) (IB := J)
      (f := fun x ↦ TotalSpace.mk' F' x (s x)) (x₀ := z) (e.mem_source.2 hzb)).1 hsm).2
  have hφ2 : ContMDiffAt J 𝓘(ℝ, F') 2 φ z := hφm.of_le hm2
  have hφz : φ z = 0 := by
    simp only [hφ_def, hz, ← e.continuousLinearMapAt_apply_of_mem (R := ℝ) hzb, map_zero]
  -- An injective linear map `A` into a Euclidean space with `‖A (φ y)‖ ≤ ‖s y‖` near `z`.
  obtain ⟨A, hAinj, hAev⟩ := exists_injective_norm_trivializationAt_le F' E' z
  have hbound : ∀ᶠ y in 𝓝 z, ‖A (φ y)‖ ≤ ‖s y‖ := hAev.mono fun y hy ↦ hy (s y)
  -- The difference `h = ‖s‖² - ‖A ∘ φ‖²` has a local minimum at `z`.
  set q : X → ℝ := fun y ↦ ‖A (φ y)‖ ^ 2
  set h : X → ℝ := fun y ↦ ‖s y‖ ^ 2 - q y
  have hg : ContMDiffAt J 𝓘(ℝ) 2 (fun y ↦ ‖s y‖ ^ 2) z :=
    (((contMDiff_norm_sq_bundle J m F' E').contMDiffAt.comp z hsm).of_le hm2)
  have hq : ContMDiffAt J 𝓘(ℝ) 2 q z :=
    ((contDiff_norm_sq ℝ).comp A.contDiff).contMDiff.contMDiffAt.comp z hφ2
  have hh : ContMDiffAt J 𝓘(ℝ) 2 h z := hg.sub hq
  have hmin : IsLocalMin h z := by
    filter_upwards [hbound] with y hy
    simp only [h, q, hz, hφz, map_zero, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, sub_zero, sub_nonneg]
    exact pow_le_pow_left₀ (norm_nonneg _) hy 2
  have hint : J.IsInteriorPoint z := BoundarylessManifold.isInteriorPoint
  have hH : criticalHessian J (fun y ↦ ‖s y‖ ^ 2) z u u =
      criticalHessian J h z u u + criticalHessian J q z u u := by
    rw [show (fun y ↦ ‖s y‖ ^ 2) = h + q from funext fun y ↦ (sub_add_cancel _ _).symm,
      criticalHessian_add hh hq hint, add_apply, add_apply]
  have hu0 : criticalHessian J (fun y ↦ ‖s y‖ ^ 2) z u = 0 := by
    simpa using LinearMap.mem_ker.1 hu
  rw [hu0,
    zero_apply,
    criticalHessian_norm_sq_continuousLinearMap_comp_apply_of_eq_zero hφ2
      (by rw [hφz, map_zero])] at hH
  have hnn := (hh.of_le one_le_two).criticalHessian_self_nonneg_of_isLocalMin hint hmin u
  -- Hence `A (dφ u) = 0`, so `dφ u = 0`, and `L u = 0`.
  have hA : A (mfderiv J 𝓘(ℝ, F') φ z u) = 0 := by
    have : inner ℝ (A (mfderiv J 𝓘(ℝ, F') φ z u)) (A (mfderiv J 𝓘(ℝ, F') φ z u)) ≤ 0 := by
      linarith
    exact real_inner_self_nonpos.1 this
  have hdφ : mfderiv J 𝓘(ℝ, F') (fun y ↦ (e ⟨y, s y⟩).2) z u = 0 :=
    (injective_iff_map_eq_zero A).1 hAinj _ hA
  rw [LinearMap.mem_ker, sectionLinearization_eq_symmL_comp continuousAt_id hzb
    (hφ2.mdifferentiableAt two_ne_zero) hz]
  simp [mvfderiv, hdφ]

end TauCeti

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [FiniteDimensional ℝ V] [IsManifold J m X]

variable (hm : m ≠ 0) (hsm : ContMDiff J (J.prod 𝓘(ℝ, F')) m fun x ↦ TotalSpace.mk' F' x (s x))
  (hs : ∀ x, s x = 0 → Surjective (TauCeti.sectionLinearization (F := F') J _root_.id s x))
  (hE : finrank ℝ E + finrank ℝ F' = finrank ℝ V)

namespace TauCeti.SmoothEmbedding

open SymplecticGeometry

/-- **The zero set of a transverse section is a Morse–Bott critical submanifold of `‖s‖²`.** For a
`C^m` section `s`, `2 ≤ m`, of a real vector bundle with a `C^m` bundle metric over a boundaryless
manifold, transverse to the zero section, the zero set, embedded by
`TauCeti.SmoothEmbedding.ofTransverseSection`, is a nondegenerate critical submanifold of
`y ↦ ‖s y‖ ^ 2`. -/
theorem isNondegenerateCriticalSubmanifold_norm_sq_ofTransverseSection (hm2 : 2 ≤ m) :
    letI := transverseZeroSetChartedSpace hm hsm hs hE
    (ofTransverseSection hm hsm hs hE).IsNondegenerateCriticalSubmanifold
      fun y ↦ ‖s y‖ ^ 2 := by
  let := transverseZeroSetChartedSpace hm hsm hs hE
  have hg : ContMDiff J 𝓘(ℝ) 2 fun y ↦ ‖s y‖ ^ 2 :=
    ((contMDiff_norm_sq_bundle J m F' E').comp hsm).of_le hm2
  refine ⟨⟨fun z ↦ hg _, fun z ↦ ?_⟩, fun z ↦ ?_⟩
  · exact mem_criticalPoints_norm_sq_of_eq_zero
      (ofTransverseSection_apply_eq_zero hm hsm hs hE z) BoundarylessManifold.isInteriorPoint
  · rw [coe_ofTransverseSection, range_mfderiv_coe_transverseZeroSet hm hsm hs hE z]
    exact ker_criticalHessian_norm_sq_le_ker_sectionLinearization hm2 (hsm _) z.property

/-- **The zero set of a transverse section has Morse index `0` for `‖s‖²`.** For a `C^m` section
`s`, `m ≠ 0`, of a real vector bundle with a `C^m` bundle metric over a boundaryless manifold,
transverse to the zero section, the Morse index of `y ↦ ‖s y‖ ^ 2` vanishes at every point of the
zero set: each is a local minimum. -/
theorem manifoldMorseIndex_norm_sq_ofTransverseSection (z : ↥{x : X | s x = 0}) :
    letI := transverseZeroSetChartedSpace hm hsm hs hE
    manifoldMorseIndex J (fun y ↦ ‖s y‖ ^ 2) (ofTransverseSection hm hsm hs hE z) = 0 := by
  let := transverseZeroSetChartedSpace hm hsm hs hE
  exact manifoldMorseIndex_eq_zero_of_isLocalMin
    ((((contMDiff_norm_sq_bundle J m F' E').comp hsm).of_le
      (ENat.one_le_iff_ne_zero_withTop.2 hm)) _)
    BoundarylessManifold.isInteriorPoint
    (isLocalMin_norm_sq_of_eq_zero (ofTransverseSection_apply_eq_zero hm hsm hs hE z))

end TauCeti.SmoothEmbedding

end
