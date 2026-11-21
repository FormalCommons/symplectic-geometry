/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Covector
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension
public import TauCeti.Geometry.Manifold.VectorBundle.Trivialization
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Liouville

/-!
# Uniqueness of the Liouville form

Let `L` be a smooth manifold and `λ` the Liouville form of its cotangent bundle `T*L`
(`TauCeti.CotangentBundle.liouvilleForm`). Tau Ceti proves that `λ` is tautological: for every
smooth one-form `σ` on `L`, read as a section `σ : L → T*L`, the pullback `σ^* λ` is `σ`
(`TauCeti.CotangentBundle.mpullback_liouvilleForm`). This file proves the converse: a smooth
one-form `μ` on `T*L` with `σ^* μ = σ` for every `σ` is `λ`
(`TauCeti.CotangentBundle.eq_liouvilleForm_of_forall_mpullback_eq`). So `λ` is the unique one-form
with this property (`TauCeti.CotangentBundle.existsUnique_forall_mpullback_eq`).

The proof tests `μ - λ` against sections with a prescribed value and derivative at a point. Read in
the preferred chart at a covector `z = (q, p)`, the differential at `q` of a section `s` through
`z` sends `u` to `(u, D u)`, where `D` is the derivative at `q` of `s` read in the trivialization at
`q` (`Bundle.mfderiv_section_apply`). For every pair of model covectors `ξ` and `b` there is a
global smooth section through `z` with `D u = ξ u • b`
(`TauCeti.CotangentBundle.exists_contMDiffSection_mfderiv_eq`): the section through `p` constant in
the trivialization at `q`, plus a function with differential `ξ` at `q` and vanishing at `q` times
the section with constant coordinate `b`, both cut off by a bump function. Since `σ^* μ = σ^* λ`
for each such section, `μ - λ` vanishes at `z` on all vectors `(u, ξ u • b)`; these span
`E × (E →L[ℝ] ℝ)`.

The bump functions need a finite-dimensional model and a Hausdorff manifold, and the test sections
are smooth, so `L` is a `C^∞` manifold. Its boundary may be nonempty.

## Main results

* `Bundle.mfderiv_section_apply`: the differential of a section of a fibre bundle, in the preferred
  chart at its value.
* `TauCeti.CotangentBundle.exists_contMDiffSection_mfderiv_eq`: smooth sections of `T*L` with a
  prescribed value and a prescribed derivative of the form `u ↦ ξ u • b` at a point.
* `TauCeti.CotangentBundle.eq_liouvilleForm_of_forall_mpullback_eq`: a one-form whose pullback by
  every section `σ` is `σ` is the Liouville form.
* `TauCeti.CotangentBundle.existsUnique_forall_mpullback_eq`: the Liouville form is the unique
  such one-form.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Proposition 3.1.18.
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
at `b` of `s` read in the trivialization at `b`, applied to `u`. -/
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

namespace TauCeti.CotangentBundle

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {L : Type*} [TopologicalSpace L]
  [ChartedSpace H L] [T2Space L] [IsManifold I ∞ L]

/-- **Sections with a prescribed value and derivative.** For a covector `p` at `q` and model
covectors `ξ` and `b`, there is a smooth section `s` of the cotangent bundle with `s q = p` whose
differential at `q`, read in the preferred chart at `p`, sends `u` to `(u, ξ u • b)`. -/
theorem exists_contMDiffSection_mfderiv_eq (q : L) (p : TangentSpace I q →L[ℝ] ℝ)
    (ξ b : E →L[ℝ] ℝ) :
    ∃ s : ContMDiffSection I (E →L[ℝ] ℝ) ∞ (fun x : L ↦ TangentSpace I x →L[ℝ] ℝ),
      s q = p ∧ ∀ u : TangentSpace I q,
        mfderiv I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (fun y ↦ TotalSpace.mk' (E →L[ℝ] ℝ) y (s y)) q u =
          (u, ξ u • b) := by
  set e := trivializationAt (E →L[ℝ] ℝ) (fun x : L ↦ TangentSpace I x →L[ℝ] ℝ) q with he
  have hq : q ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt _ _ q
  -- A function with differential `ξ` at `q`, and global sections through `p` and `e.symm q b`
  -- that are constant in the trivialization `e` near `q`.
  set f : L → ℝ := ⇑((Classical.arbitrary (SmoothBumpFunction I q)).bumpCovector (n := ⊤) ξ)
  have hf : ContMDiff I 𝓘(ℝ) ∞ f := ContMDiffMap.contMDiff _
  set s₀ := FiberBundle.contMDiffExtend I (E →L[ℝ] ℝ)
    (V := fun x : L ↦ TangentSpace I x →L[ℝ] ℝ) p
  set s₁ := FiberBundle.contMDiffExtend I (E →L[ℝ] ℝ)
    (V := fun x : L ↦ TangentSpace I x →L[ℝ] ℝ) (e.symm q b)
  let s : ContMDiffSection I (E →L[ℝ] ℝ) ∞ (fun x : L ↦ TangentSpace I x →L[ℝ] ℝ) :=
    ⟨fun y ↦ s₀ y + (f y - f q) • s₁ y,
      (FiberBundle.contMDiff_contMDiffExtend I _ (V := fun x : L ↦ TangentSpace I x →L[ℝ] ℝ)
        p).add_section ((hf.sub contMDiff_const).smul_section
          (FiberBundle.contMDiff_contMDiffExtend I _
            (V := fun x : L ↦ TangentSpace I x →L[ℝ] ℝ) (e.symm q b)))⟩
  refine ⟨s, by simp [s, s₀], fun u ↦ ?_⟩
  rw [Bundle.mfderiv_section_apply ((s.contMDiff q).mdifferentiableAt (by simp))]
  congr 1
  -- Near `q`, the section read in `e` is `y ↦ e p + (f y - f q) • b`.
  have hev : (fun y ↦ (e ⟨y, s y⟩).2) =ᶠ[𝓝 q] fun y ↦ (e ⟨q, p⟩).2 + (f y - f q) • b := by
    filter_upwards [e.open_baseSet.mem_nhds hq,
      FiberBundle.eventually_contMDiffExtend_eq_extend I (E →L[ℝ] ℝ)
        (V := fun x : L ↦ TangentSpace I x →L[ℝ] ℝ) p,
      FiberBundle.eventually_contMDiffExtend_eq_extend I (E →L[ℝ] ℝ)
        (V := fun x : L ↦ TangentSpace I x →L[ℝ] ℝ) (e.symm q b)] with y hy h₀ h₁
    have hlin := e.linear ℝ hy
    -- The section `s` is `s₀ + (f - f q) • s₁` by definition.
    change (e ⟨y, s₀ y + (f y - f q) • s₁ y⟩).2 = _
    rw [hlin.map_add, hlin.map_smul, show s₀ y = _ from h₀, show s₁ y = _ from h₁]
    simp only [FiberBundle.extend, ← he, e.apply_mk_symm hy, e.apply_mk_symm hq]
  have hfd : MDifferentiableAt I 𝓘(ℝ) (fun y ↦ f y - f q) q :=
    ((hf.sub contMDiff_const) q).mdifferentiableAt (by simp)
  have hfb : MDifferentiableAt I 𝓘(ℝ, E →L[ℝ] ℝ) (fun y ↦ (f y - f q) • b) q :=
    hfd.smul mdifferentiableAt_const
  have hd : mvfderiv I (fun y ↦ (e ⟨q, p⟩).2 + (f y - f q) • b) q u = ξ u • b := by
    rw [mvfderiv_fun_add mdifferentiableAt_const hfb,
      mvfderiv_fun_smul hfd mdifferentiableAt_const, mvfderiv_const, mvfderiv_const,
      mvfderiv_fun_sub (hf q |>.mdifferentiableAt (by simp)) mdifferentiableAt_const,
      mvfderiv_const, sub_zero, SmoothBumpFunction.mvfderiv_bumpCovector, smul_zero, zero_add,
      zero_add]
    -- `ξ` is a covector on the model space, read on the tangent space `TangentSpace I q = E`.
    exact ContinuousLinearMap.smulRight_apply (M₁ := E) (c := ξ) (f := b) (x := u)
  rw [← hev.mvfderiv_eq] at hd
  rw [← mvfderiv_apply_eq_mfderiv_apply]
  exact hd

/-- **Uniqueness of the Liouville form.** A smooth one-form `μ` on the cotangent bundle `T*L`
whose pullback by every smooth one-form `σ` on `L`, read as a section `L → T*L`, is `σ` itself is
the Liouville form `TauCeti.CotangentBundle.liouvilleForm`. The model of `L` is
finite-dimensional and `L` is Hausdorff, so that bump functions exist; `L` may have boundary. -/
theorem eq_liouvilleForm_of_forall_mpullback_eq
    {μ : SmoothForm (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (CotangentBundle I L) ℝ 1}
    (h : ∀ σ : SmoothForm I L ℝ 1,
      SmoothForm.mpullback (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ) x (SmoothForm.degreeOneEquiv σ x))
        (SmoothForm.degreeOneEquiv σ).contMDiff μ = σ) :
    μ = liouvilleForm I L := by
  -- Along every smooth section, `μ` and `λ` pull back to the same form.
  have key : ∀ (s : ContMDiffSection I (E →L[ℝ] ℝ) ∞ (fun x : L ↦ TangentSpace I x →L[ℝ] ℝ))
      (x : L) (u : TangentSpace I x),
      SmoothForm.degreeOneEquiv μ ⟨x, s x⟩
          (mfderiv I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (fun y ↦ TotalSpace.mk' (E →L[ℝ] ℝ) y (s y)) x u) =
        SmoothForm.degreeOneEquiv (liouvilleForm I L) ⟨x, s x⟩
          (mfderiv I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (fun y ↦ TotalSpace.mk' (E →L[ℝ] ℝ) y (s y)) x
            u) := by
    intro s x u
    obtain ⟨σ, rfl⟩ := SmoothForm.degreeOneEquiv.surjective s
    rw [← SmoothForm.degreeOneEquiv_mpullback_apply (SmoothForm.degreeOneEquiv σ).contMDiff,
      ← SmoothForm.degreeOneEquiv_mpullback_apply (SmoothForm.degreeOneEquiv σ).contMDiff, h σ,
      mpullback_liouvilleForm]
  apply SmoothForm.degreeOneEquiv.injective
  ext ⟨q, p⟩ w
  rw [← sub_eq_zero, ← sub_apply]
  -- Tangent vectors of `T*L` at `⟨q, p⟩` are pairs in the model space `E × (E →L[ℝ] ℝ)`.
  let D : E × (E →L[ℝ] ℝ) →L[ℝ] ℝ :=
    SmoothForm.degreeOneEquiv μ ⟨q, p⟩ - SmoothForm.degreeOneEquiv (liouvilleForm I L) ⟨q, p⟩
  change D w = 0
  have hD (ξ b : E →L[ℝ] ℝ) (u : E) : D (u, ξ u • b) = 0 := by
    obtain ⟨s, rfl, hs⟩ := exists_contMDiffSection_mfderiv_eq q p ξ b
    have h₁ := key s q u
    rw [hs u] at h₁
    exact sub_eq_zero.2 h₁
  have h₀ (u : E) : D (u, 0) = 0 := by simpa using hD 0 0 u
  obtain ⟨a, c⟩ := w
  have hc : D (0, c) = 0 := by
    rcases subsingleton_or_nontrivial E with hE | hE
    · obtain rfl : c = 0 := ContinuousLinearMap.ext fun u ↦ by
        rw [Subsingleton.elim u 0, map_zero, zero_apply]
      exact h₀ 0
    · obtain ⟨u, hu⟩ := exists_ne (0 : E)
      obtain ⟨ξ, hξ⟩ := SeparatingDual.exists_eq_one (R := ℝ) hu
      have h₁ := hD ξ c u
      rw [hξ, one_smul] at h₁
      rw [show ((0 : E), c) = (u, c) - (u, 0) by simp, map_sub, h₁, h₀, sub_zero]
  rw [show (a, c) = (a, 0) + ((0 : E), c) by simp, map_add, h₀, hc, add_zero]

/-- **The Liouville form is the unique tautological one-form.** On the cotangent bundle `T*L` of a
Hausdorff manifold with finite-dimensional model, there is exactly one smooth one-form `μ` whose
pullback by every smooth one-form `σ` on `L`, read as a section `L → T*L`, is `σ`: the Liouville
form `TauCeti.CotangentBundle.liouvilleForm`. -/
theorem existsUnique_forall_mpullback_eq :
    ∃! μ : SmoothForm (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (CotangentBundle I L) ℝ 1,
      ∀ σ : SmoothForm I L ℝ 1,
        SmoothForm.mpullback
          (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ) x (SmoothForm.degreeOneEquiv σ x))
          (SmoothForm.degreeOneEquiv σ).contMDiff μ = σ :=
  ⟨liouvilleForm I L, mpullback_liouvilleForm, fun _ ↦ eq_liouvilleForm_of_forall_mpullback_eq⟩

end TauCeti.CotangentBundle

end
