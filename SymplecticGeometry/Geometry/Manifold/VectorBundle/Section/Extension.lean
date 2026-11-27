/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Covector
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension
public import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
public import TauCeti.Geometry.Manifold.VectorBundle.Submersion
public import TauCeti.Geometry.Manifold.VectorBundle.Trivialization
import SymplecticGeometry.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Global sections with a prescribed value and derivative

Tau Ceti's `FiberBundle.contMDiffExtend` gives a global smooth section of a vector bundle through
any vector. This file adds sections whose derivative at the base point is also partly prescribed.

The differential at `b` of a section `s` of a fibre bundle, read in the preferred chart at `s b`,
sends a tangent vector `u` to `(u, D u)`, where `D` is the derivative at `b` of `s` read in the
trivialization at `b` (`Bundle.mfderiv_section_apply`). In a smooth real vector bundle with fibre
`F` over a Hausdorff manifold with finite-dimensional model `E`, for every vector `p` over `q`,
every covector `ξ : E →L[ℝ] ℝ` and every `b : F` there is a global smooth section `s` through `p`
with `D u = ξ u • b` (`ContMDiffSection.exists_mfderiv_eq`). It is `s₀ + (f - f q) • s₁`, where
`s₀` and `s₁` are the sections `FiberBundle.contMDiffExtend` through `p` and through the vector
with coordinate `b`, and `f` is a smooth function with differential `ξ` at `q`
(`SmoothBumpFunction.bumpCovector`).

## Main results

* `Bundle.mfderiv_section_apply`: the differential of a section of a fibre bundle, in the preferred
  chart at its value.
* `ContMDiffSection.exists_mfderiv_eq`: smooth sections of a vector bundle with a prescribed value
  and a prescribed derivative of the form `u ↦ ξ u • b` at a point.
-/

public section

noncomputable section

open Bundle Filter
open scoped Manifold Topology ContDiff

namespace Bundle

variable {𝕜 B F : Type*} {V : B → Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace (TotalSpace F V)]
  [∀ x, TopologicalSpace (V x)] {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B]
  [ChartedSpace HB B] [FiberBundle F V]

/-- **The differential of a section.** Let `s` be a section of a fibre bundle, differentiable at
`b`. Tangent vectors at `s b` are read in the preferred chart at `s b`, as pairs of a base and a
fibre coordinate. Then the differential of `s` at `b` sends `u` to `u` itself and the derivative
at `b` of `s` read in the trivialization at `b`, applied to `u`. The second component is also the
fibre part of the first jet of `s` at `b` (`TauCeti.FirstJetBundle.jet_snd_eq_mfderiv`). -/
theorem mfderiv_section_apply {s : ∀ b, V b} {b : B}
    (hs : MDifferentiableAt IB (IB.prod 𝓘(𝕜, F)) (fun y ↦ TotalSpace.mk' F y (s y)) b)
    (u : TangentSpace IB b) :
    mfderiv IB (IB.prod 𝓘(𝕜, F)) (fun y ↦ TotalSpace.mk' F y (s y)) b u =
      (u, mfderiv IB 𝓘(𝕜, F) (fun y ↦ (trivializationAt F V b ⟨y, s y⟩).2) b u) := by
  refine Prod.ext ?_ ?_
  · -- The derivative of the projection is the first coordinate, and `π ∘ s = id`.
    have h := congrArg (· u) (mfderiv_proj_comp_mfderiv_of_proj_comp_eq_id hs rfl)
    simp only [mfderiv_proj] at h
    exact h
  · -- The derivative of the fibre coordinate is the second coordinate; apply the chain rule.
    have h := mfderiv_comp_apply (I' := IB.prod 𝓘(𝕜, F)) b
      ((TotalSpace.contMDiffAt_trivializationAt_snd (n := 1) (IB := IB)
        (TotalSpace.mk' F b (s b))).mdifferentiableAt one_ne_zero) hs u
    rw [TotalSpace.mfderiv_trivializationAt_snd] at h
    exact h.symm

end Bundle

namespace ContMDiffSection

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {V : M → Type*}
  [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V I]

/-- **Sections with a prescribed value and derivative.** In a smooth real vector bundle `V` with
fibre `F` over a Hausdorff manifold with finite-dimensional model `E`, let `p` be a vector over
`q`, `ξ : E →L[ℝ] ℝ` a covector of the model and `b : F`. There is a smooth section `s` with
`s q = p` whose differential at `q`, read in the preferred chart at `p`, sends `u` to
`(u, ξ u • b)`. The finite dimension and the Hausdorff property give the bump functions. -/
theorem exists_mfderiv_eq (q : M) (p : V q) (ξ : E →L[ℝ] ℝ) (b : F) :
    ∃ s : ContMDiffSection I F ∞ V, s q = p ∧ ∀ u : TangentSpace I q,
      mfderiv I (I.prod 𝓘(ℝ, F)) (fun y ↦ TotalSpace.mk' F y (s y)) q u = (u, ξ u • b) := by
  set e := trivializationAt F V q with he
  have hq : q ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt _ _ q
  -- A function with differential `ξ` at `q`, and global sections through `p` and `e.symm q b`
  -- that are constant in the trivialization `e` near `q`.
  set f : M → ℝ := ⇑((Classical.arbitrary (SmoothBumpFunction I q)).bumpCovector (n := ⊤) ξ)
  have hf : ContMDiff I 𝓘(ℝ) ∞ f := ContMDiffMap.contMDiff _
  set s₀ := FiberBundle.contMDiffExtend I F p
  set s₁ := FiberBundle.contMDiffExtend I F (e.symm q b)
  let s : ContMDiffSection I F ∞ V :=
    ⟨fun y ↦ s₀ y + (f y - f q) • s₁ y,
      (FiberBundle.contMDiff_contMDiffExtend I F p).add_section
        ((hf.sub contMDiff_const).smul_section
          (FiberBundle.contMDiff_contMDiffExtend I F (e.symm q b)))⟩
  refine ⟨s, by simp [s, s₀], fun u ↦ ?_⟩
  rw [Bundle.mfderiv_section_apply ((s.contMDiff q).mdifferentiableAt (by simp))]
  congr 1
  -- Near `q`, the section read in `e` is `y ↦ e p + (f y - f q) • b`.
  have hev : (fun y ↦ (e ⟨y, s y⟩).2) =ᶠ[𝓝 q] fun y ↦ (e ⟨q, p⟩).2 + (f y - f q) • b := by
    filter_upwards [e.open_baseSet.mem_nhds hq,
      FiberBundle.eventually_contMDiffExtend_eq_extend I F p,
      FiberBundle.eventually_contMDiffExtend_eq_extend I F (e.symm q b)] with y hy h₀ h₁
    have hlin := e.linear ℝ hy
    -- The section `s` is `s₀ + (f - f q) • s₁` by definition.
    change (e ⟨y, s₀ y + (f y - f q) • s₁ y⟩).2 = _
    rw [hlin.map_add, hlin.map_smul, show s₀ y = _ from h₀, show s₁ y = _ from h₁]
    simp only [FiberBundle.extend, ← he, e.apply_mk_symm hy, e.apply_mk_symm hq]
  have hfd : MDifferentiableAt I 𝓘(ℝ) (fun y ↦ f y - f q) q :=
    ((hf.sub contMDiff_const) q).mdifferentiableAt (by simp)
  have hd : mvfderiv I (fun y ↦ (e ⟨q, p⟩).2 + (f y - f q) • b) q u = ξ u • b := by
    rw [TauCeti.mvfderiv_const_add, mvfderiv_fun_smul hfd mdifferentiableAt_const, mvfderiv_const,
      mvfderiv_sub_const, SmoothBumpFunction.mvfderiv_bumpCovector, smul_zero, zero_add]
    -- `ξ` is a covector on the model space, read on the tangent space `TangentSpace I q = E`.
    exact ContinuousLinearMap.smulRight_apply (M₁ := E) (c := ξ) (f := b) (x := u)
  rw [← hev.mvfderiv_eq] at hd
  rw [← mvfderiv_apply_eq_mfderiv_apply]
  exact hd

end ContMDiffSection

end
