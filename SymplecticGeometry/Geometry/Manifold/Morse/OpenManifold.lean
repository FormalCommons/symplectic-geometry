/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Geometry.Manifold.ContMDiffMap
public import TauCeti.Geometry.Manifold.Morse.Hessian
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic
import Mathlib.Geometry.Manifold.Algebra.Monoid
import SymplecticGeometry.Analysis.Calculus.Morse.HalfCylinder
import SymplecticGeometry.Geometry.Manifold.ContMDiff.Indicator
import SymplecticGeometry.Geometry.Manifold.Morse.Hessian
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Injective
import TauCeti.Geometry.Manifold.SmoothEmbedding.LocalDiffeomorph

/-!
# Morse functions on open manifolds: raising a function inside tubes

Let `M` be a boundaryless manifold of dimension `dim V + 1`, and let `Φ i : ℝ × V → M` be smooth
embeddings whose half-cylinders `Φ i '' S`, `S = [-1, ∞) × closedBall 0 1`, are closed, pairwise
disjoint and locally finite. If a smooth `g₀ : M → ℝ` has, in each half-cylinder, no critical
point other than `Φ i 0`, then `g₀` can be raised inside the half-cylinders to a smooth `g₁` at
whose critical points in them the critical Hessian is positive on some vector, so none of these
critical points is a nondegenerate local maximum.

## Main results

* `TauCeti.exists_le_criticalHessian_pos_of_tubes`: the function `g₁`.

## Construction

For each `i`, `SymplecticGeometry.exists_nonneg_halfCylinder_hessian_pos` applied to `g₀ ∘ Φ i`
gives `μ i ≥ 0` supported in `S`. Since `Φ i` is a local diffeomorphism between manifolds of the
same dimension (`TauCeti.SmoothEmbedding.isLocalDiffeomorph`), its inverse is smooth on its open
range (`IsLocalDiffeomorphOn.contMDiffOn_invFunOn`), so `μ i ∘ (Φ i)⁻¹`, extended by zero off the
range, is smooth on `M`; and `g₁ := g₀ + ∑ᶠ i, μ i ∘ (Φ i)⁻¹`. Near a point of `Φ i '' S` the
other half-cylinders are absent, so there `g₁ ∘ Φ i = g₀ ∘ Φ i + μ i`, and critical points and
positive Hessian directions are read through `Φ i`
(`TauCeti.SmoothEmbedding.mem_criticalPoints_iff_fderiv_comp_eq_zero_prod`,
`TauCeti.SmoothEmbedding.exists_criticalHessian_pos_iff_fderiv_fderiv_comp_prod`).

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Theorem 7.3.1.
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963.
-/

public section

open Set Filter Function
open scoped Manifold Topology ContDiff

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

omit [I.Boundaryless] in
/-- The modification inside one tube: a smooth `ν ≥ 0` on `M`, supported in `Φ '' S`, which reads
through `Φ` as a function `μ` at whose critical points in `S` the second derivative of
`g₀ ∘ Φ + μ` is positive on some vector. -/
private lemma exists_tube_bump {g₀ : M → ℝ} (hg₀ : ContMDiff I 𝓘(ℝ) ∞ g₀)
    (Φ : SmoothEmbedding (𝓘(ℝ).prod 𝓘(ℝ, V)) I ∞ (ℝ × V) M)
    (hdim : Module.finrank ℝ (ℝ × V) = Module.finrank ℝ E)
    (hS : IsClosed (Φ '' Ici (-1 : ℝ) ×ˢ Metric.closedBall (0 : V) 1))
    (hcrit : ∀ z ∈ Ici (-1 : ℝ) ×ˢ Metric.closedBall (0 : V) 1,
      Φ z ∈ criticalPoints I g₀ → z = 0) :
    ∃ (ν : M → ℝ) (μ : ℝ × V → ℝ), ContMDiff I 𝓘(ℝ) ∞ ν ∧ 0 ≤ ν ∧
      support ν ⊆ Φ '' Ici (-1 : ℝ) ×ˢ Metric.closedBall (0 : V) 1 ∧ (∀ z, ν (Φ z) = μ z) ∧
      ∀ z, fderiv ℝ (g₀ ∘ Φ + μ) z = 0 → z ∈ Ici (-1 : ℝ) ×ˢ Metric.closedBall (0 : V) 1 →
        ∃ v, 0 < fderiv ℝ (fderiv ℝ (g₀ ∘ Φ + μ)) z v v := by
  set S := Ici (-1 : ℝ) ×ˢ Metric.closedBall (0 : V) 1
  -- Read on `ℝ × V`, the product model is the model of the normed space `ℝ × V`.
  have hcd (f : ℝ × V → ℝ) : ContMDiff (𝓘(ℝ).prod 𝓘(ℝ, V)) 𝓘(ℝ) ∞ f ↔ ContDiff ℝ ∞ f := by
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    exact contMDiff_iff_contDiff
  have hf : ContDiff ℝ ∞ (g₀ ∘ Φ) := (hcd _).1 (hg₀.comp Φ.contMDiff)
  obtain ⟨μ, hμ, hμ0, hμS, hμcrit⟩ := SymplecticGeometry.exists_nonneg_halfCylinder_hessian_pos
    (hf.of_le (WithTop.coe_le_coe.2 le_top)) fun z hz h ↦ hcrit z hz
      (((Φ.mem_criticalPoints_iff_fderiv_comp_eq_zero_prod (by simp) hdim
        (hg₀.mdifferentiableAt (by simp))).2 h))
  have hμ' : ContMDiff (𝓘(ℝ).prod 𝓘(ℝ, V)) 𝓘(ℝ) ∞ μ := (hcd μ).2 hμ
  have hloc := Φ.isLocalDiffeomorph hdim (by simp)
  have hinj : InjOn Φ univ := Φ.isSmoothEmbedding.isEmbedding.injective.injOn
  have hleft (z : ℝ × V) : invFunOn Φ univ (Φ z) = z := hinj.leftInvOn_invFunOn (mem_univ z)
  have hinv := (hloc.isLocalDiffeomorphOn univ).contMDiffOn_invFunOn isOpen_univ hinj
  rw [image_univ] at hinv
  refine ⟨(range Φ).indicator (μ ∘ invFunOn Φ univ), μ,
    (hμ'.comp_contMDiffOn hinv).contMDiff_indicator hloc.isOpen_range hS
      (image_subset_range _ _) ?_, indicator_nonneg fun _ _ ↦ hμ0 _, fun x hx ↦ ?_,
    fun z ↦ ?_, hμcrit⟩
  · rintro _ ⟨z, rfl⟩ hz
    rw [comp_apply, hleft]
    exact image_eq_zero_of_notMem_tsupport fun h ↦ hz (mem_image_of_mem _ (hμS h))
  · have hxr : x ∈ range Φ := by
      by_contra h
      exact hx (indicator_of_notMem h _)
    obtain ⟨z, rfl⟩ := hxr
    rw [mem_support, indicator_of_mem (mem_range_self z), comp_apply, hleft] at hx
    exact mem_image_of_mem _ (hμS (subset_tsupport _ hx))
  · rw [indicator_of_mem (mem_range_self z), comp_apply, hleft]

/-- **Raising a function inside locally finite tubes.** Let `M` be a boundaryless manifold of
dimension `dim V + 1`, `S = [-1, ∞) × closedBall 0 1 ⊆ ℝ × V`, and `Φ i : ℝ × V → M` smooth
embeddings for which the sets `Φ i '' S` are closed, pairwise disjoint and locally finite. If a
smooth `g₀ : M → ℝ` has no critical point in any `Φ i '' S` other than `Φ i 0`, then there is a
smooth `g₁ ≥ g₀` with `g₁ - g₀` supported in `⋃ i, Φ i '' S` such that at every critical point
of `g₁` in `⋃ i, Φ i '' S` the critical Hessian of `g₁` is positive on some tangent vector. -/
theorem exists_le_criticalHessian_pos_of_tubes (g₀ : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯) {ι : Type*}
    (Φ : ι → SmoothEmbedding (𝓘(ℝ).prod 𝓘(ℝ, V)) I ∞ (ℝ × V) M)
    (hV : Module.finrank ℝ V + 1 = Module.finrank ℝ E)
    (hS : ∀ i, IsClosed (Φ i '' Ici (-1 : ℝ) ×ˢ Metric.closedBall (0 : V) 1))
    (hlf : LocallyFinite fun i ↦ Φ i '' Ici (-1 : ℝ) ×ˢ Metric.closedBall (0 : V) 1)
    (hdisj : Pairwise (Disjoint on fun i ↦ Φ i '' Ici (-1 : ℝ) ×ˢ Metric.closedBall (0 : V) 1))
    (hcrit : ∀ i, ∀ z ∈ Ici (-1 : ℝ) ×ˢ Metric.closedBall (0 : V) 1,
      Φ i z ∈ criticalPoints I g₀ → z = 0) :
    ∃ g₁ : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯, (∀ x, g₀ x ≤ g₁ x) ∧
      tsupport (fun x ↦ g₁ x - g₀ x) ⊆ ⋃ i, Φ i '' Ici (-1 : ℝ) ×ˢ Metric.closedBall (0 : V) 1 ∧
      ∀ x ∈ ⋃ i, Φ i '' Ici (-1 : ℝ) ×ˢ Metric.closedBall (0 : V) 1,
        x ∈ criticalPoints I g₁ → ∃ v, 0 < criticalHessian I g₁ x v v := by
  set S := Ici (-1 : ℝ) ×ˢ Metric.closedBall (0 : V) 1
  have hdim : Module.finrank ℝ (ℝ × V) = Module.finrank ℝ E := by
    rw [Module.finrank_prod, Module.finrank_self, add_comm, hV]
  choose ν μ hν hν0 hνS hνμ hμ using fun i ↦
    exists_tube_bump g₀.contMDiff (Φ i) hdim (hS i) (hcrit i)
  set g₁ : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯ :=
    ⟨fun x ↦ g₀ x + ∑ᶠ i, ν i x, g₀.contMDiff.add (contMDiff_finsum hν (hlf.subset hνS))⟩
  have hg₁ (x : M) : g₁ x = g₀ x + ∑ᶠ i, ν i x := by rw [ContMDiffMap.coeFn_mk]
  refine ⟨g₁, fun x ↦ ?_, ?_, ?_⟩
  · rw [hg₁]
    exact le_add_of_nonneg_right (finsum_nonneg fun i ↦ hν0 i x)
  · rw [← (hlf.isClosed_iUnion hS).closure_eq]
    refine closure_mono fun x hx ↦ ?_
    rw [mem_support, hg₁, add_sub_cancel_left] at hx
    obtain ⟨i, hi⟩ : ∃ i, ν i x ≠ 0 := by
      by_contra! h
      exact hx (finsum_eq_zero_of_forall_eq_zero h)
    exact mem_iUnion.2 ⟨i, hνS i hi⟩
  · intro x hx hx₁
    obtain ⟨i, z, hz, rfl⟩ := mem_iUnion.1 hx
    -- Away from the other tubes, `g₁` is `g₀ + ν i`.
    have hW : IsClosed (⋃ j : {j // j ≠ i}, Φ j '' S) :=
      (hlf.comp_injective Subtype.val_injective).isClosed_iUnion fun j ↦ hS j
    have hzW : Φ i z ∉ ⋃ j : {j // j ≠ i}, Φ j '' S := by
      simp only [mem_iUnion, not_exists]
      exact fun j hj ↦ disjoint_left.1 (hdisj j.property) hj (mem_image_of_mem _ hz)
    have hloc : ⇑g₁ ∘ Φ i =ᶠ[𝓝 z] g₀ ∘ Φ i + μ i := by
      filter_upwards [(Φ i).contMDiff.continuous.continuousAt.preimage_mem_nhds
        (hW.isOpen_compl.mem_nhds hzW)] with w hw
      rw [comp_apply, hg₁, finsum_eq_single _ i fun j hj ↦ ?_, hνμ, Pi.add_apply, comp_apply]
      rw [mem_preimage, mem_compl_iff] at hw
      by_contra h
      exact hw (mem_iUnion.2 ⟨⟨j, hj⟩, hνS j h⟩)
    have hcrit₁ := ((Φ i).mem_criticalPoints_iff_fderiv_comp_eq_zero_prod (by simp) hdim
      (g₁.contMDiff.mdifferentiableAt (by simp))).1 hx₁
    rw [hloc.fderiv_eq] at hcrit₁
    obtain ⟨v, hv⟩ := hμ i z hcrit₁ hz
    refine ((Φ i).exists_criticalHessian_pos_iff_fderiv_fderiv_comp_prod
      (WithTop.coe_le_coe.2 le_top) hdim
      (g₁.contMDiff.of_le (WithTop.coe_le_coe.2 le_top)).contMDiffAt hx₁).2 ⟨v, ?_⟩
    rwa [hloc.fderiv.fderiv_eq]

end TauCeti

end
