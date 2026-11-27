/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Liouville
import SymplecticGeometry.Geometry.Manifold.VectorBundle.Section.Extension

/-!
# Uniqueness of the Liouville form

Let `L` be a smooth manifold and `λ` the Liouville form of its cotangent bundle `T*L`
(`TauCeti.CotangentBundle.liouvilleForm`). Tau Ceti proves that `λ` is tautological: for every
smooth one-form `σ` on `L`, read as a section `σ : L → T*L`, the pullback `σ^* λ` is `σ`
(`TauCeti.CotangentBundle.mpullback_liouvilleForm`). This file proves the converse: a smooth
one-form `μ` on `T*L` with `σ^* μ = σ` for every `σ` is `λ`
(`TauCeti.CotangentBundle.eq_liouvilleForm_of_forall_mpullback_eq`). So `λ` is the unique one-form
with this property (`TauCeti.CotangentBundle.existsUnique_forall_mpullback_eq`).

The proof tests `μ - λ` against sections with a prescribed value and derivative at a point. For a
covector `z = (q, p)` and model covectors `ξ` and `b`, `ContMDiffSection.exists_mfderiv_eq` gives
a global smooth section through `z` whose differential at `q`, in the preferred chart at `z`, sends
`u` to `(u, ξ u • b)`. Since `σ^* μ = σ^* λ` for each such section, `μ - λ` vanishes at `z` on all
these vectors, and they span `E × (E →L[ℝ] ℝ)`.

The test sections are built from bump functions, which need a finite-dimensional model and a
Hausdorff manifold, and they are smooth, so `L` is a `C^∞` manifold. Its boundary may be
nonempty.

## Main results

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

namespace TauCeti.CotangentBundle

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {L : Type*} [TopologicalSpace L]
  [ChartedSpace H L] [T2Space L] [IsManifold I ∞ L]

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
    obtain ⟨s, rfl, hs⟩ := ContMDiffSection.exists_mfderiv_eq
      (I := I) (V := fun x : L ↦ TangentSpace I x →L[ℝ] ℝ) q p ξ b
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
