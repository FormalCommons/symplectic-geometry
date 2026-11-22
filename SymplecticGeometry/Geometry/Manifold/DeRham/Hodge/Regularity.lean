/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.DeRham.Hodge.L2
public import SymplecticGeometry.Geometry.Manifold.DeRham.Hodge.LocalLaplacian
import SymplecticGeometry.Analysis.Calculus.ContDiff.Matrix
import SymplecticGeometry.Analysis.Distribution.SecondOrderSystem
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.ChartCover
import SymplecticGeometry.Geometry.Manifold.Riemannian.PartialDiffeomorph
import Mathlib.Geometry.Manifold.PartitionOfUnity
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# Regularity of weak solutions of `Δu = f`

Let `M` be a closed oriented Riemannian manifold and `Δ` its Hodge Laplacian on real `k`-forms.
An `L²` form `u` is a weak solution of `Δu = f` if `⟪u, Δφ⟫ = ⟪f, φ⟫` for every smooth `k`-form
`φ` (`SymplecticGeometry.L2Form.IsWeakSolution`). This file shows that a weak solution with a
smooth right side `f` is a smooth form `α` with `Δα = f`
(`SymplecticGeometry.L2Form.exists_eq_ofSmooth_of_isWeakSolution`).

The argument is local. In a chart `ψ` with a cutoff `χ` supported in its source, the `L²` inner
product of `u` with a smooth form `β` supported where `χ = 1` is the integral over `E` of the
inner product in the chart (`SymplecticGeometry.formInnerInChart`) of the localizations of `u`
and `β`, weighted by the density of the Riemannian volume read in the chart
(`SymplecticGeometry.L2Form.inner_ofSmooth_eq_integral_localize`, in
`SymplecticGeometry.Geometry.Manifold.DeRham.Hodge.L2`). Taking for `β` the Hodge Laplacian of
the extension by zero of a flat form `a`, which the chart reads as the operator `P a` of
`SymplecticGeometry.exists_mpullback_symm_hodgeLaplacian_eq`
(`SymplecticGeometry.L2Form.inner_ofSmooth_hodgeLaplacian_extendByZeroAlong_eq_integral`), the
weak equation becomes `∫ w (P a) = ∫ h a`, with `w` the localization of `u` multiplied by the
inner product in the chart and the density, and `h` the same for `f`. The principal part of `P`
is `-∑ i j, G⁻¹ i j ∂ᵢ ∂ⱼ` with `G` the Gram matrix of the metric in the chart, so
`SymplecticGeometry.exists_contDiffOn_ae_eq_of_forall_integral_apply_eq` makes `w` smooth, and
inverting the Gram matrix of the inner product of forms in the chart makes the localization of `u`
smooth (`SymplecticGeometry.L2Form.IsWeakSolution.exists_contDiffOn_ae_eq_localize`).

To glue, take the finitely many charts and the partition of unity `ρ` of
`TauCeti.exists_finite_partialDiffeomorph_cover`. For each `i`, a second cutoff `θ` equal to `1`
near the support of `ρ i` gives the regularity of the localization with `θ` near the support of
`ρ i`, and the localization with `ρ i` is that with `θ` multiplied by `ρ i ∘ ψ.symm`
(`SymplecticGeometry.L2Form.localize_ae_eq_indicator_smul_localize`), so it is smooth with
compact support (`SymplecticGeometry.L2Form.IsWeakSolution.exists_contDiff_ae_eq_localize`).
Then `SymplecticGeometry.L2Form.eq_ofSmooth_of_localize` gives `u = ofSmooth α`, and `Δα = f`
because the Hodge Laplacian is formally self-adjoint
(`SymplecticGeometry.L2Form.isWeakSolution_ofSmooth_iff`, from Tau Ceti's
`TauCeti.SmoothForm.integralTopForm_inner_hodgeLaplacian_eq_inner_hodgeLaplacian`).

## Main definitions and results

* `SymplecticGeometry.L2Form.IsWeakSolution o hkl u f`: `u` is a weak solution of `Δu = f`, with
  `isWeakSolution_iff`, its linearity (`IsWeakSolution.add`, `IsWeakSolution.smul`, …) and
  `isWeakSolution_ofSmooth_iff`: a smooth form is a weak solution exactly when it is a solution.
* `SymplecticGeometry.L2Form.inner_ofSmooth_hodgeLaplacian_extendByZeroAlong_eq_integral`: the
  inner product of an `L²` form with the Hodge Laplacian of a test form supported in a chart, read
  in the chart.
* `SymplecticGeometry.L2Form.IsWeakSolution.exists_contDiffOn_ae_eq_localize`: regularity in a
  chart.
* `SymplecticGeometry.L2Form.exists_eq_ofSmooth_of_isWeakSolution`: weak solutions of `Δu = f`
  with smooth `f` are smooth.

## References

* [P. Griffiths, J. Harris, *Principles of Algebraic Geometry*][GriffithsHarris1978],
  Chapter 0, §6 (regularity of weak solutions of elliptic equations, and the Hodge theorem).
* F. W. Warner, *Foundations of Differentiable Manifolds and Lie Groups*, Graduate Texts in
  Mathematics 94, Springer, 1983, Chapter 6.
-/

public section

noncomputable section

open Bundle MeasureTheory Set Filter TauCeti
open scoped Manifold ContDiff InnerProductSpace Topology Matrix

namespace SymplecticGeometry

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {m k l : ℕ}

/-- The Riemannian volume measure needs only a continuous metric. -/
local instance [IsManifold I ∞ M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] :
    IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
  IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle
    (IB := I) (n := ∞) (F := E) (V := fun x : M ↦ TangentSpace I x)

/-! ### Weak solutions -/

namespace L2Form

variable [IsManifold I ∞ M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] [CompactSpace M]
  {o : Manifold.Orientation I M (Fin m)} {hkl : k + l = m}

variable (o hkl) in
/-- An `L²` form `u` is a **weak solution of `Δu = f`** if `⟪u, Δφ⟫ = ⟪f, φ⟫` for every smooth
`k`-form `φ`, with `Δ` the Hodge Laplacian and `⟪·, ·⟫` the `L²` inner product. -/
def IsWeakSolution (u f : L2Form o k) : Prop :=
  ∀ φ : SmoothForm I M ℝ k,
    ⟪u, ofSmooth (SmoothForm.hodgeLaplacian o hkl φ)⟫_ℝ = ⟪f, ofSmooth φ⟫_ℝ

theorem isWeakSolution_iff {u f : L2Form o k} : IsWeakSolution o hkl u f ↔ ∀ φ : SmoothForm I M ℝ k,
    ⟪u, ofSmooth (SmoothForm.hodgeLaplacian o hkl φ)⟫_ℝ = ⟪f, ofSmooth φ⟫_ℝ :=
  Iff.rfl

theorem isWeakSolution_zero : IsWeakSolution o hkl (0 : L2Form o k) 0 := fun φ ↦ by
  simp

theorem IsWeakSolution.add {u f v g : L2Form o k} (hu : IsWeakSolution o hkl u f)
    (hv : IsWeakSolution o hkl v g) : IsWeakSolution o hkl (u + v) (f + g) := fun φ ↦ by
  rw [inner_add_left, inner_add_left, hu φ, hv φ]

theorem IsWeakSolution.smul {u f : L2Form o k} (hu : IsWeakSolution o hkl u f) (c : ℝ) :
    IsWeakSolution o hkl (c • u) (c • f) := fun φ ↦ by
  rw [real_inner_smul_left, real_inner_smul_left, hu φ]

theorem IsWeakSolution.neg {u f : L2Form o k} (hu : IsWeakSolution o hkl u f) :
    IsWeakSolution o hkl (-u) (-f) := fun φ ↦ by
  rw [inner_neg_left, inner_neg_left, hu φ]

theorem IsWeakSolution.sub {u f v g : L2Form o k} (hu : IsWeakSolution o hkl u f)
    (hv : IsWeakSolution o hkl v g) : IsWeakSolution o hkl (u - v) (f - g) := by
  simpa only [sub_eq_add_neg] using hu.add hv.neg

/-- A smooth form `α` is a weak solution of `Δu = f`, for a smooth `f`, exactly when `Δα = f`. -/
theorem isWeakSolution_ofSmooth_iff [BoundarylessManifold I M] [T2Space M]
    {α f : SmoothForm I M ℝ k} :
    IsWeakSolution o hkl (ofSmooth α) (ofSmooth f) ↔ SmoothForm.hodgeLaplacian o hkl α = f := by
  have hsa (φ : SmoothForm I M ℝ k) : SmoothForm.l2Inner o α (SmoothForm.hodgeLaplacian o hkl φ) =
      SmoothForm.l2Inner o (SmoothForm.hodgeLaplacian o hkl α) φ := by
    simp only [SmoothForm.l2Inner_def]
    exact (SmoothForm.integralTopForm_inner_hodgeLaplacian_eq_inner_hodgeLaplacian o hkl α φ
      (Or.inl (by simp [compactlySupportedForms_eq_top]))).symm
  refine ⟨fun h ↦ ?_, fun h φ ↦ by rw [inner_ofSmooth, inner_ofSmooth, hsa, h]⟩
  have h0 (φ : SmoothForm I M ℝ k) :
      SmoothForm.l2Inner o (SmoothForm.hodgeLaplacian o hkl α - f) φ = 0 := by
    rw [SmoothForm.l2Inner_sub_left, ← hsa, ← inner_ofSmooth, ← inner_ofSmooth, h φ, sub_self]
  exact sub_eq_zero.1 ((SmoothForm.l2Inner_self_eq_zero_iff o).1 (h0 _))

end L2Form

/-! ### Regularity in a chart -/

section Chart

variable [IsManifold I ∞ M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] [CompactSpace M] [T2Space M]
  [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]
  {o : Manifold.Orientation I M (Fin m)} {hkl : k + l = m}

omit [CompactSpace M] [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure] in
/-- Read in a chart `ψ` with a cutoff `χ`, the Hodge Laplacian of the extension by zero of a flat
form `a` supported where `χ ∘ ψ.symm = 1` is the second-order operator
`P a = -∑ i j, G⁻¹ i j ∂_{b j} ∂_{b i} a + ∑ i, B i (∂_{b i} a) + C a` of
`exists_mpullback_symm_hodgeLaplacian_eq`, at every point of `E`. -/
private theorem localize_hodgeLaplacian_extendByZeroAlong (o : Manifold.Orientation I M (Fin m))
    (hkl : k + l = m) (ψ : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞) (b : Module.Basis (Fin m) ℝ E)
    {B : Fin m → E → (E [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] E [⋀^Fin k]→L[ℝ] ℝ}
    {C : E → (E [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] E [⋀^Fin k]→L[ℝ] ℝ}
    (hΔ : ∀ (α : SmoothForm I M ℝ k), ∀ y ∈ ψ.target,
        (mpullback 𝓘(ℝ, E) I ψ.symm (SmoothForm.hodgeLaplacian o hkl α).val y :
            E [⋀^Fin k]→L[ℝ] ℝ) =
          -∑ i, ∑ j, (Matrix.of fun i j ↦ gramInChart ψ y (b i) (b j))⁻¹ i j •
              fderiv ℝ (F := E [⋀^Fin k]→L[ℝ] ℝ) (fun z ↦ fderiv ℝ
                (mpullback 𝓘(ℝ, E) I ψ.symm α.val : E → E [⋀^Fin k]→L[ℝ] ℝ) z (b i)) y (b j) +
            ∑ i, B i y (fderiv ℝ (mpullback 𝓘(ℝ, E) I ψ.symm α.val : E → E [⋀^Fin k]→L[ℝ] ℝ) y
              (b i)) +
            C y (mpullback 𝓘(ℝ, E) I ψ.symm α.val y : E [⋀^Fin k]→L[ℝ] ℝ))
    {χ : M → ℝ} {a : E → E [⋀^Fin k]→L[ℝ] ℝ} (ha : ContDiff ℝ ∞ a) (hac : HasCompactSupport a)
    (hat : tsupport a ⊆ ψ.target) (haχ : ∀ y ∈ tsupport a, χ (ψ.symm y) = 1) (y : E) :
    (SmoothForm.hodgeLaplacian o hkl (SmoothForm.extendByZeroAlong ψ a ha hac hat)).localize ψ χ y
      = -∑ i, ∑ j, (Matrix.of fun i j ↦ gramInChart ψ y (b i) (b j))⁻¹ i j •
          fderiv ℝ (fun z ↦ fderiv ℝ a z (b i)) y (b j) +
        ∑ i, B i y (fderiv ℝ a y (b i)) + C y (a y) := by
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  set φ := SmoothForm.extendByZeroAlong ψ a ha hac hat
  let P : E → E [⋀^Fin k]→L[ℝ] ℝ := fun y ↦
    -∑ i, ∑ j, (Matrix.of fun i j ↦ gramInChart ψ y (b i) (b j))⁻¹ i j •
      fderiv ℝ (fun z ↦ fderiv ℝ a z (b i)) y (b j) + ∑ i, B i y (fderiv ℝ a y (b i)) + C y (a y)
  -- Off the support of `a`, the operator vanishes.
  have hP : Function.support P ⊆ tsupport a := fun y hPy ↦ by
    by_contra hy
    have h0 : a =ᶠ[𝓝 y] 0 := notMem_tsupport_iff_eventuallyEq.1 hy
    have h1 : ∀ᶠ z in 𝓝 y, fderiv ℝ a z = 0 := h0.eventually_nhds.mono fun z (hz : a =ᶠ[𝓝 z] 0) ↦ by
      rw [hz.fderiv_eq, fderiv_zero, Pi.zero_apply]
    have h2 (i : Fin m) : fderiv ℝ (fun z ↦ fderiv ℝ a z (b i)) y = 0 := by
      have h3 : (fun z ↦ fderiv ℝ a z (b i)) =ᶠ[𝓝 y] fun _ ↦ 0 :=
        Filter.Eventually.mono h1 fun z hz ↦ by simp [hz]
      rw [Filter.EventuallyEq.fderiv_eq h3, fderiv_const_apply]
    exact hPy (by simp [P, h2, h1.self_of_nhds, h0.self_of_nhds])
  -- On the target, the reading of `φ` agrees with `a` near every point.
  have hφa (y : E) (hy : y ∈ ψ.target) :
      (mpullback 𝓘(ℝ, E) I ψ.symm φ.val : E → E [⋀^Fin k]→L[ℝ] ℝ) =ᶠ[𝓝 y] a :=
    Filter.eventually_of_mem (ψ.open_target.mem_nhds hy) fun z hz ↦ by
      rw [SmoothForm.coe_extendByZeroAlong, mpullback_symm_extendByZeroAlong ψ _ hn hz]
  refine congrFun (SmoothForm.localize_eq_of_mpullback_symm_eq ψ _ (g := P) (fun y hy ↦ ?_)
    (hP.trans hat) fun y hy ↦ haχ y (hP hy)) y
  have e2 (v : E) : fderiv ℝ (fun z ↦ fderiv ℝ (mpullback 𝓘(ℝ, E) I ψ.symm φ.val :
      E → E [⋀^Fin k]→L[ℝ] ℝ) z v) y = fderiv ℝ (fun z ↦ fderiv ℝ a z v) y :=
    Filter.EventuallyEq.fderiv_eq (Filter.eventually_of_mem (ψ.open_target.mem_nhds hy)
      fun z hz ↦ by beta_reduce; rw [Filter.EventuallyEq.fderiv_eq (hφa z hz)])
  rw [hΔ φ y hy, Filter.EventuallyEq.fderiv_eq (hφa y hy),
    Filter.EventuallyEq.eq_of_nhds (hφa y hy)]
  simp only [e2]
  -- What remains is `P y` with the derivatives of `a` taken with values in the forms on the
  -- tangent spaces of `E`, which are those on `E` by definition.
  rfl

/-- **The weak equation read in a chart.** Let `ψ` be a chart, `χ` a smooth cutoff supported in
its source, and `a` a smooth flat form with compact support in `ψ.target` on which
`χ ∘ ψ.symm = 1`. For every `L²` form `u`, the inner product of `u` with the Hodge Laplacian of
the extension by zero of `a` along `ψ` is the integral over `E` of the inner product in the chart
of the localization of `u` with the operator `P a` of `exists_mpullback_symm_hodgeLaplacian_eq`,
weighted by the density of the Riemannian volume read in the chart. -/
theorem L2Form.inner_ofSmooth_hodgeLaplacian_extendByZeroAlong_eq_integral
    (hkl : k + l = m) (ψ : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞) (b : Module.Basis (Fin m) ℝ E)
    {B : Fin m → E → (E [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] E [⋀^Fin k]→L[ℝ] ℝ}
    {C : E → (E [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] E [⋀^Fin k]→L[ℝ] ℝ}
    (hΔ : ∀ (α : SmoothForm I M ℝ k), ∀ y ∈ ψ.target,
        (mpullback 𝓘(ℝ, E) I ψ.symm (SmoothForm.hodgeLaplacian o hkl α).val y :
            E [⋀^Fin k]→L[ℝ] ℝ) =
          -∑ i, ∑ j, (Matrix.of fun i j ↦ gramInChart ψ y (b i) (b j))⁻¹ i j •
              fderiv ℝ (F := E [⋀^Fin k]→L[ℝ] ℝ) (fun z ↦ fderiv ℝ
                (mpullback 𝓘(ℝ, E) I ψ.symm α.val : E → E [⋀^Fin k]→L[ℝ] ℝ) z (b i)) y (b j) +
            ∑ i, B i y (fderiv ℝ (mpullback 𝓘(ℝ, E) I ψ.symm α.val : E → E [⋀^Fin k]→L[ℝ] ℝ) y
              (b i)) +
            C y (mpullback 𝓘(ℝ, E) I ψ.symm α.val y : E [⋀^Fin k]→L[ℝ] ℝ))
    (χ : C^∞⟮I, M; ℝ⟯) (hχ : tsupport χ ⊆ ψ.source) {a : E → E [⋀^Fin k]→L[ℝ] ℝ}
    (ha : ContDiff ℝ ∞ a) (hac : HasCompactSupport a) (hat : tsupport a ⊆ ψ.target)
    (haχ : ∀ y ∈ tsupport a, χ (ψ.symm y) = 1) (u : L2Form o k) :
    ⟪u, ofSmooth (SmoothForm.hodgeLaplacian o hkl
      (SmoothForm.extendByZeroAlong ψ a ha hac hat))⟫_ℝ =
      ∫ y, (b.addHaar.addHaarScalarFactor volume : ℝ) * riemannianJacobian (I := I) b ψ.symm y *
        formInnerInChart ψ y (L2Form.localize ψ χ hχ u y)
          (-∑ i, ∑ j, (Matrix.of fun i j ↦ gramInChart ψ y (b i) (b j))⁻¹ i j •
              fderiv ℝ (fun z ↦ fderiv ℝ a z (b i)) y (b j) +
            ∑ i, B i y (fderiv ℝ a y (b i)) + C y (a y)) := by
  -- `χ = 1` on the support of the Hodge Laplacian of the extension by zero of `a`.
  have hΔχ (x : M) (hx : x ∈ tsupport (α := E [⋀^Fin k]→L[ℝ] ℝ)
      (SmoothForm.hodgeLaplacian o hkl (SmoothForm.extendByZeroAlong ψ a ha hac hat)).val) :
      χ x = 1 := by
    have hx' := SmoothForm.tsupport_hodgeLaplacian_subset o hkl _ hx
    rw [SmoothForm.coe_extendByZeroAlong] at hx'
    obtain ⟨y, hy, rfl⟩ := RoughForm.tsupport_extendByZeroAlong_subset a hac hat hx'
    exact haχ y hy
  rw [L2Form.inner_ofSmooth_eq_integral_localize ψ χ hχ b hΔχ u]
  simp only [localize_hodgeLaplacian_extendByZeroAlong o hkl ψ b hΔ ha hac hat haχ]

/-- **Regularity of weak solutions in a chart.** Let `u` be a weak solution of `Δu = f` with `f`
smooth, `ψ` a chart and `χ` a smooth cutoff supported in its source. On an open set `V` of the
target of `ψ` on which `χ ∘ ψ.symm = 1`, the localization of `u` to `ψ` with the cutoff `χ` is
almost everywhere a function smooth on `V`. -/
theorem L2Form.IsWeakSolution.exists_contDiffOn_ae_eq_localize {u : L2Form o k}
    {f : SmoothForm I M ℝ k} (hu : IsWeakSolution o hkl u (ofSmooth f))
    (ψ : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞) (χ : C^∞⟮I, M; ℝ⟯) (hχ : tsupport χ ⊆ ψ.source)
    {V : Set E} (hV : IsOpen V) (hVt : V ⊆ ψ.target) (hVχ : ∀ y ∈ V, χ (ψ.symm y) = 1) :
    ∃ g : E → E [⋀^Fin k]→L[ℝ] ℝ, ContDiffOn ℝ ∞ g V ∧
      L2Form.localize ψ χ hχ u =ᵐ[volume.restrict V] g := by
  classical
  rcases V.eq_empty_or_nonempty with rfl | ⟨y₀, -⟩
  · refine ⟨0, contDiffOn_const, ?_⟩
    rw [Measure.restrict_empty, ae_zero]
    exact Filter.eventually_bot
  have hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  have hm := o.fact_finrank_tangentSpace (ψ.symm y₀)
  let b : Module.Basis (Fin m) ℝ E := Module.finBasisOfFinrankEq ℝ E hm.out
  obtain ⟨B, C, hB, hC, hΔ⟩ := exists_mpullback_symm_hodgeLaplacian_eq o ψ hkl b
  -- The density of the Riemannian volume read in the chart, for `volume`.
  set D : E → ℝ := fun y ↦ (b.addHaar.addHaarScalarFactor volume : ℝ) *
    riemannianJacobian (I := I) b ψ.symm y
  have hD : ContDiffOn ℝ ∞ D ψ.target :=
    contDiffOn_const.mul (ψ.contDiffOn_riemannianJacobian_symm b)
  have hDpos (y : E) (hy : y ∈ ψ.target) : 0 < D y :=
    mul_pos (NNReal.coe_pos.2 (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _))
      (ψ.riemannianJacobian_symm_pos hn b hy)
  set U := ⇑(L2Form.localize ψ χ hχ u)
  let e := Module.finBasis ℝ (E [⋀^Fin k]→L[ℝ] ℝ)
  let L (p : Fin (Module.finrank ℝ (E [⋀^Fin k]→L[ℝ] ℝ))) :
      (E [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ := LinearMap.toContinuousLinearMap (e.coord p)
  -- The unknown `w = D • formInnerInChart ψ · U`, written in the basis `e`, and the right side.
  let w : E → (E [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ := fun y ↦
    ∑ p, L p (U y) • (D y • formInnerInChart ψ y (e p))
  have hw (y : E) (γ : E [⋀^Fin k]→L[ℝ] ℝ) : w y γ = D y * formInnerInChart ψ y (U y) γ := by
    conv_rhs => rw [← e.sum_repr (U y)]
    simp only [w, L, map_sum, map_smul, _root_.sum_apply, _root_.smul_apply, smul_eq_mul,
      LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ ↦ by ring
  let h : E → (E [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ := fun y ↦
    D y • formInnerInChart ψ y (mpullback 𝓘(ℝ, E) I ψ.symm f.val y)
  -- The principal symbol `∑ i j, G⁻¹ i j ξ i ξ j` is positive definite.
  have hell (y : E) (hy : y ∈ V) (ξ : Fin m → ℝ) (hξ : ξ ≠ 0) :
      ∑ i, ∑ j, (Matrix.of fun i j ↦ gramInChart ψ y (b i) (b j))⁻¹ i j * ξ i * ξ j ≠ 0 := by
    have := (posDef_gramInChart ψ b (hVt hy)).inv.dotProduct_mulVec_pos hξ
    refine ne_of_gt ?_
    convert this using 1
    simp only [dotProduct, Matrix.mulVec, star_trivial, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring
  -- The weak equation in the chart.
  have hweak (a : E → E [⋀^Fin k]→L[ℝ] ℝ) (ha : ContDiff ℝ ∞ a) (hac : HasCompactSupport a)
      (haV : tsupport a ⊆ V) :
      ∫ y, w y (-∑ i, ∑ j, (Matrix.of fun i j ↦ gramInChart ψ y (b i) (b j))⁻¹ i j •
          fderiv ℝ (fun z ↦ fderiv ℝ a z (b i)) y (b j) +
        ∑ i, B i y (fderiv ℝ a y (b i)) + C y (a y)) = ∫ y, h y (a y) := by
    have hat : tsupport a ⊆ ψ.target := haV.trans hVt
    have haχ (y : E) (hy : y ∈ tsupport a) : χ (ψ.symm y) = 1 := hVχ y (haV hy)
    set φ := SmoothForm.extendByZeroAlong ψ a ha hac hat
    have hφχ (x : M) (hx : x ∈ tsupport (α := E [⋀^Fin k]→L[ℝ] ℝ) φ.val) : χ x = 1 := by
      rw [SmoothForm.coe_extendByZeroAlong] at hx
      obtain ⟨y, hy, rfl⟩ := RoughForm.tsupport_extendByZeroAlong_subset a hac hat hx
      exact haχ y hy
    have hweakφ := hu φ
    rw [L2Form.inner_ofSmooth_hodgeLaplacian_extendByZeroAlong_eq_integral hkl ψ b hΔ χ hχ ha hac
      hat haχ u, L2Form.inner_ofSmooth,
      SmoothForm.l2Inner_eq_integral_formInnerInChart ψ o b hχ hφχ,
      SmoothForm.localize_extendByZeroAlong ψ ha hac hat haχ] at hweakφ
    convert hweakφ using 1
    · simp only [hw, U, D]
    · refine integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
      simp only [h, _root_.smul_apply, smul_eq_mul]
      by_cases hya : y ∈ tsupport a
      · have e : f.localize ψ χ y = χ (ψ.symm y) •
            (mpullback 𝓘(ℝ, E) I ψ.symm f.val y : E [⋀^Fin k]→L[ℝ] ℝ) :=
          SmoothForm.localize_of_mem _ _ _ (hat hya)
        rw [e, haχ y hya, one_smul]
      · simp [image_eq_zero_of_notMem_tsupport hya]
  obtain ⟨g', hg', hwg⟩ := exists_contDiffOn_ae_eq_of_forall_integral_apply_eq (μ := volume) hV b
    (A := fun i j y ↦ (Matrix.of fun i j ↦ gramInChart ψ y (b i) (b j))⁻¹ i j) (B := B) (C := C)
    (fun i j ↦ (contDiffOn_inv_gramInChart_apply ψ b i j).mono hVt) (fun i ↦ (hB i).mono hVt)
    (hC.mono hVt) hell (w := w) (h := h)
    (locallyIntegrableOn_finsetSum _ fun p _ ↦
      ((((L p).comp_memLp' (Lp.memLp (L2Form.localize ψ χ hχ u))).locallyIntegrable
        one_le_two |>.locallyIntegrableOn V).smul_continuousOn hV.isLocallyClosed
          (continuousOn_clm_apply.2 fun γ ↦ ((hD.mul (contDiffOn_formInnerInChart ψ subset_rfl
            contDiffOn_const contDiffOn_const)).mono hVt).continuousOn.congr fun y _ ↦ rfl)))
    (contDiffOn_clm_apply.2 fun γ ↦ ((hD.mul (contDiffOn_formInnerInChart ψ subset_rfl
      (fun y hy ↦ (f.contDiffAt_mpullback_symm ψ hy).contDiffWithinAt)
      contDiffOn_const)).mono hVt).congr fun y _ ↦ rfl) hweak
  -- Recover the localization from `g' / D`, through the inverse Gram matrix of `e`.
  set G : E → Matrix _ _ ℝ := fun y ↦ Matrix.of fun p q ↦ formInnerInChart ψ y (e p) (e q)
  refine ⟨fun y ↦ ∑ p, ((G y)⁻¹ *ᵥ fun q ↦ g' y (e q) / D y) p • e p, ?_, ?_⟩
  · refine ContDiffOn.sum fun p _ ↦ ?_
    refine ContDiffOn.smul (f := fun y ↦ ((G y)⁻¹ *ᵥ fun q ↦ g' y (e q) / D y) p) ?_
      contDiffOn_const
    simp only [Matrix.mulVec, dotProduct]
    refine ContDiffOn.sum fun q _ ↦ ContDiffOn.mul ?_ ?_
    · exact (ContDiffOn.matrix_inv_apply (fun p q ↦ (contDiffOn_formInnerInChart_apply ψ (e p)
        (e q)).mono hVt) (fun y hy ↦ (posDef_formInnerInChart ψ e (hVt hy)).det_pos.ne') p q)
    · exact (hg'.clm_apply contDiffOn_const).div (hD.mono hVt) fun y hy ↦ (hDpos y (hVt hy)).ne'
  · filter_upwards [hwg, ae_restrict_mem hV.measurableSet] with y hy hyV
    have hz : (fun q ↦ g' y (e q) / D y) = fun q ↦ formInnerInChart ψ y (U y) (e q) := by
      ext q
      rw [← hy, hw, mul_div_cancel_left₀ _ (hDpos y (hVt hyV)).ne']
    rw [hz]
    exact eq_sum_inv_mulVec_formInnerInChart ψ e (hVt hyV) (U y)

/-- The localization of a weak solution of `Δu = f`, with `f` smooth, to a chart `ψ` with a smooth
cutoff `ρ` supported in its source, is almost everywhere a smooth flat form with compact support
in `ψ.target`. -/
theorem L2Form.IsWeakSolution.exists_contDiff_ae_eq_localize {u : L2Form o k}
    {f : SmoothForm I M ℝ k} (hu : IsWeakSolution o hkl u (ofSmooth f))
    (ψ : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞) (ρ : C^∞⟮I, M; ℝ⟯) (hρ : tsupport ρ ⊆ ψ.source) :
    ∃ F : E → E [⋀^Fin k]→L[ℝ] ℝ, ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧
      tsupport F ⊆ ψ.target ∧ L2Form.localize ψ ρ hρ u =ᵐ[volume] F := by
  -- A cutoff `θ` equal to `1` on an open `U₁ ⊇ tsupport ρ` and supported in `ψ.source`.
  obtain ⟨U₂, hU₂, hρU₂, hU₂s⟩ := normal_exists_closure_subset (isClosed_tsupport _)
    ψ.open_source hρ
  obtain ⟨U₁, hU₁, hρU₁, hU₁₂⟩ := normal_exists_closure_subset (isClosed_tsupport _) hU₂
    hρU₂
  obtain ⟨θ, hθ0, hθ1, -⟩ := exists_contMDiffMap_zero_one_of_isClosed I (n := ⊤)
    hU₂.isClosed_compl isClosed_closure (Set.disjoint_compl_left_iff_subset.2 hU₁₂)
  have hθ : tsupport θ ⊆ ψ.source :=
    (closure_mono (Function.support_subset_iff'.2 fun x hx ↦ hθ0 hx)).trans hU₂s
  have hρθ (x : M) (hx : x ∈ tsupport ρ) : θ x = 1 := hθ1 (subset_closure (hρU₁ hx))
  -- The open set of the chart where `θ ∘ ψ.symm = 1`.
  set V := ψ.target ∩ ψ.symm ⁻¹' U₁
  have hV : IsOpen V := ψ.contMDiffOn_invFun.continuousOn.isOpen_inter_preimage ψ.open_target hU₁
  obtain ⟨g, hg, hug⟩ := hu.exists_contDiffOn_ae_eq_localize ψ θ hθ hV Set.inter_subset_left
    fun y hy ↦ hθ1 (subset_closure hy.2)
  set r : E → ℝ := ψ.target.indicator fun y ↦ ρ (ψ.symm y)
  have hK : IsCompact (ψ '' tsupport ρ) := (isClosed_tsupport _).isCompact.image_of_continuousOn
    (ψ.contMDiffOn.continuousOn.mono hρ)
  have hKV : ψ '' tsupport ρ ⊆ V := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨ψ.map_source (hρ hx), by simpa [ψ.left_inv (hρ hx)] using hρU₁ hx⟩
  have hr0 (y : E) (hy : y ∉ V) : r y = 0 :=
    Function.notMem_support.1 fun h ↦ hy (hKV (ψ.support_indicator_comp_symm_subset ρ h))
  set F := fun y ↦ r y • g y
  have hFs : tsupport F ⊆ ψ '' tsupport ρ :=
    closure_minimal ((Function.support_smul_subset_left r g).trans
      (ψ.support_indicator_comp_symm_subset ρ)) hK.isClosed
  have hFV : ContDiffOn ℝ ∞ F V := by
    have hρψ : ContDiffOn ℝ ∞ (fun y ↦ ρ (ψ.symm y)) V :=
      contMDiffOn_iff_contDiffOn.1 ((ρ.contMDiff.comp_contMDiffOn ψ.symm.contMDiffOn).mono
        Set.inter_subset_left)
    exact (hρψ.smul hg).congr fun y hy ↦ by simp [F, r, Set.indicator_of_mem hy.1]
  refine ⟨F, contDiff_iff_contDiffAt.2 fun y ↦ ?_, hK.of_isClosed_subset (isClosed_tsupport _) hFs,
    hFs.trans (hKV.trans Set.inter_subset_left), ?_⟩
  · by_cases hy : y ∈ V
    · exact hFV.contDiffAt (hV.mem_nhds hy)
    · exact contDiffAt_const.congr_of_eventuallyEq
        (notMem_tsupport_iff_eventuallyEq.1 fun h ↦ hy (hKV (hFs h)))
  · filter_upwards [L2Form.localize_ae_eq_indicator_smul_localize ψ hρ hθ hρθ u,
      (ae_restrict_iff' hV.measurableSet).1 hug] with y h1 h2
    rw [h1]
    by_cases hy : y ∈ V
    · rw [h2 hy]
    · -- Fold the indicator back into `r`, which vanishes off `V`.
      change r y • _ = r y • g y
      rw [hr0 y hy, zero_smul, zero_smul]

omit [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure] in
/-- **Weak solutions of `Δu = f` with smooth `f` are smooth.** On a closed oriented Riemannian
manifold, if the `L²` form `u` is a weak solution of `Δu = f` for a smooth form `f`, then `u` is a
smooth form `α`, and `Δα = f`. -/
theorem L2Form.exists_eq_ofSmooth_of_isWeakSolution [BoundarylessManifold I M] {u : L2Form o k}
    {f : SmoothForm I M ℝ k} (hu : IsWeakSolution o hkl u (ofSmooth f)) :
    ∃ α : SmoothForm I M ℝ k, u = ofSmooth α ∧ SmoothForm.hodgeLaplacian o hkl α = f := by
  -- The localizations are taken in `L²` for a Haar measure on `E`.
  borelize E
  let _ : MeasureSpace E := ⟨Measure.addHaar⟩
  have : (volume : Measure E).IsAddHaarMeasure := by
    -- `volume` is by definition the Haar measure just chosen.
    change (Measure.addHaar : Measure E).IsAddHaarMeasure
    infer_instance
  obtain ⟨N, c, ρ, hρ⟩ := exists_finite_partialDiffeomorph_cover (I := I) (M := M)
  choose F hF hFc hFs hFu using fun i ↦
    hu.exists_contDiff_ae_eq_localize (extChartPartialDiffeomorph I ∞ (c i)) (ρ i) (hρ i)
  have hα := L2Form.eq_ofSmooth_of_localize _ ρ hρ hF hFc hFs hFu
  refine ⟨_, hα, ?_⟩
  rw [← L2Form.isWeakSolution_ofSmooth_iff, ← hα]
  exact hu

end Chart

end SymplecticGeometry

end
