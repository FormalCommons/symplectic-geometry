/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Contact.Darboux.Strict
import TauCeti.Geometry.Contact.Darboux.Manifold
import SymplecticGeometry.Geometry.Contact.Pullback
import SymplecticGeometry.Geometry.Contact.Standard
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.MFDeriv

/-!
# Contact Darboux charts for the form `Σᵢ pᵢ dqᵢ - dz`

Tau Ceti's Darboux theorem for contact forms
(`TauCeti.SmoothForm.IsContactForm.exists_strictDarbouxChart_of_finrank_eq`) gives, around every
point of a boundaryless contact manifold of dimension `2 n + 1`, a chart into `ℝⁿ × ℝⁿ × ℝ` that
pulls `dz - Σᵢ pᵢ dqᵢ` (`TauCeti.innerProductContactForm`) back to the contact form. McDuff and
Salamon write the standard contact form with the other sign, as `Σᵢ pᵢ dqᵢ - dz`. The linear
involution `σ (q, p, z) = (q, -p, -z)`, which is
`(ContinuousLinearEquiv.refl ℝ V).prodCongr (ContinuousLinearEquiv.neg ℝ)` on `V × (V × ℝ)`,
pulls the one form back to the other, so following Tau Ceti's chart by `σ` gives a chart in which
the contact form is `Σᵢ pᵢ dqᵢ - dz`. The statements write `σ` out and introduce no name for the
form `Σᵢ pᵢ dqᵢ - dz`.

Tau Ceti's chart carries the Reeb field of the contact form to the Reeb field `∂_z` of
`dz - Σᵢ pᵢ dqᵢ` (`TauCeti.reebVectorField_innerProductContactForm`, through
`TauCeti.SmoothForm.IsContactForm.mfderiv_reebVectorField_of_eventuallyEq_mpullback`), and `σ`
sends `∂_z` to `-∂_z`, so in the new chart the Reeb field is `-∂_z`.

## Main results

* `TauCeti.SmoothForm.IsContactForm.exists_strictDarbouxChart_reebVectorField_of_finrank_eq`: the
  contact Darboux theorem for `Σᵢ pᵢ dqᵢ - dz`, with the Reeb field `-∂_z` and the kernels.
* `TauCeti.IsContactDistribution.exists_darbouxChart_comap_of_finrank_eq`: a contact structure,
  with or without a global defining form, is locally the kernel of `Σᵢ pᵢ dqᵢ - dz`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §3.5, (3.5.3) on p. 126 and Exercise 3.5.20 on p. 136.
* H. Geiges, *An Introduction to Contact Topology*, Cambridge Studies in Advanced Mathematics
  109, Cambridge University Press, 2008, §2.5 (cited by Tau Ceti's Darboux files, on which this
  file builds).
-/

public section

open Filter Module
open scoped Manifold ContDiff Topology

namespace TauCeti

section Darboux

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M] {n : ℕ}

/-- **The contact Darboux theorem, in the coordinates of `Σᵢ pᵢ dqᵢ - dz`.** Let `α` be a contact
form on a boundaryless manifold of dimension `2 n + 1`, and write `σ (q, p, z) = (q, -p, -z)` on
`ℝⁿ × ℝⁿ × ℝ`, so that `σ` pulls `dz - Σᵢ pᵢ dqᵢ` (`TauCeti.innerProductContactForm`) back to
`Σᵢ pᵢ dqᵢ - dz`. Around every point `x₀` there is a smooth partial diffeomorphism `chart` from
`M` to `ℝⁿ × ℝⁿ × ℝ` with `x₀ ∈ chart.source` and `chart x₀ = 0` such that, on `chart.source`,
* `chart` pulls `Σᵢ pᵢ dqᵢ - dz` back to `α`;
* the differential of `chart` sends the Reeb vector field of `α` to `-∂_z = (0, 0, -1)`;
* the differential of `chart` identifies `ker α` with the kernel of `Σᵢ pᵢ dqᵢ - dz`.

Milestone: *Contact Darboux theorem*. -/
theorem SmoothForm.IsContactForm.exists_strictDarbouxChart_reebVectorField_of_finrank_eq
    {α : SmoothForm I M ℝ 1} (hα : α.IsContactForm) (hn : finrank ℝ E = 2 * n + 1) (x₀ : M) :
    ∃ chart : PartialDiffeomorph I
        𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) M
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) ∞,
      x₀ ∈ chart.source ∧ chart x₀ = 0 ∧
      (∀ x ∈ chart.source, ∀ v : TangentSpace I x,
        (innerProductContactForm (EuclideanSpace ℝ (Fin n))).val
            ((ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin n))).prodCongr
              (ContinuousLinearEquiv.neg ℝ) (chart x))
            ![(ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin n))).prodCongr
              (ContinuousLinearEquiv.neg ℝ) (mvfderiv I chart x v)] =
          α.val x ![v]) ∧
      (∀ x ∈ chart.source, mvfderiv I chart x (α.reebVectorField x) = (0, 0, -1)) ∧
      ∀ x ∈ chart.source, α.kerDistribution x =
        ((innerProductContactForm (EuclideanSpace ℝ (Fin n))).kerDistribution
            ((ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin n))).prodCongr
              (ContinuousLinearEquiv.neg ℝ) (chart x))).comap
          (((ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin n))).prodCongr
              (ContinuousLinearEquiv.neg ℝ)).toLinearMap ∘ₗ
            (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) chart
              x).toLinearMap) := by
  set V := EuclideanSpace ℝ (Fin n)
  obtain ⟨φ, hx₀, hφ₀, hpb⟩ := hα.exists_strictDarbouxChart_of_finrank_eq hn x₀
  set σ : (V × V × ℝ) ≃L[ℝ] V × V × ℝ :=
    (ContinuousLinearEquiv.refl ℝ V).prodCongr (ContinuousLinearEquiv.neg ℝ)
  set chart := φ.trans σ.toDiffeomorph.toPartialDiffeomorph
  have hsrc : chart.source = φ.source := by simp [chart]
  have hcoe (x : M) : chart x = σ (φ x) := by simp [chart]
  have hd : ∀ x ∈ φ.source, ∀ v : TangentSpace I x, mvfderiv I chart x v = σ (mvfderiv I φ x v) :=
    fun x hx v ↦ by
      rw [φ.mvfderiv_trans_toDiffeomorph σ hx, ContinuousLinearMap.comp_apply,
        ContinuousLinearEquiv.coe_coe]
  have hσσ (y : V × V × ℝ) : σ (σ y) = y := by simp [σ]
  have hform : ∀ x ∈ chart.source, ∀ v : TangentSpace I x,
      (innerProductContactForm V).val
          ((ContinuousLinearEquiv.refl ℝ V).prodCongr (ContinuousLinearEquiv.neg ℝ) (chart x))
          ![(ContinuousLinearEquiv.refl ℝ V).prodCongr (ContinuousLinearEquiv.neg ℝ)
            (mvfderiv I chart x v)] =
        α.val x ![v] := by
    intro x hx v
    rw [hsrc] at hx
    rw [hd x hx, hcoe, hσσ, hσσ, ← hpb x hx]
  refine ⟨chart, hsrc ▸ hx₀, by rw [hcoe, hφ₀, map_zero], hform, fun x hx ↦ ?_, fun x hx ↦ ?_⟩
  · rw [hsrc] at hx
    -- Near `x`, the chart `φ` pulls the standard form back to `α`.
    have hpb' : ∀ᶠ y in 𝓝 x, α.val y = TauCeti.mpullback I 𝓘(ℝ, V × V × ℝ) φ
        (innerProductContactForm V).val y := by
      filter_upwards [φ.open_source.mem_nhds hx] with y hy
      refine ContinuousAlternatingMap.ext fun v ↦ ?_
      obtain ⟨w, rfl⟩ : ∃ w, v = ![w] := ⟨v 0, funext fun i ↦ by fin_cases i; simp⟩
      rw [← hpb y hy, mvfderiv_apply_eq_mfderiv_apply, TauCeti.mpullback_apply]
      congr 1
      funext i
      fin_cases i
      rfl
    have hR := hα.mfderiv_reebVectorField_of_eventuallyEq_mpullback
      (isContactForm_innerProductContactForm V)
      (((φ.contMDiffOn x hx).contMDiffAt (φ.open_source.mem_nhds hx)).of_le (by simp))
      (φ.isInvertible_mfderiv (by simp) hx).surjective hpb'
    rw [hd x hx, mvfderiv_apply_eq_mfderiv_apply, hR, reebVectorField_innerProductContactForm]
    simp [σ]
  · ext v
    rw [SmoothForm.mem_kerDistribution, ← hform x hx v]
    exact (Submodule.mem_comap.trans SmoothForm.mem_kerDistribution).symm

omit [T2Space M] in
/-- **The contact Darboux theorem for contact structures, in the coordinates of
`Σᵢ pᵢ dqᵢ - dz`.** Let `D` be a smooth contact distribution on a boundaryless manifold of
dimension `2 n + 1`, and write `σ (q, p, z) = (q, -p, -z)` on `ℝⁿ × ℝⁿ × ℝ`. Around every point
`x₀` there is a smooth partial diffeomorphism `chart` from `M` to `ℝⁿ × ℝⁿ × ℝ` with
`x₀ ∈ chart.source` and `chart x₀ = 0` whose differential, followed by `σ`, carries `D x` onto the
kernel of `dz - Σᵢ pᵢ dqᵢ` at `σ (chart x)` for each `x ∈ chart.source`; that is, `chart`
identifies `D` with the kernel of `Σᵢ pᵢ dqᵢ - dz`. -/
theorem IsContactDistribution.exists_darbouxChart_comap_of_finrank_eq
    {D : Π x : M, Submodule ℝ (TangentSpace I x)} (hD : IsContactDistribution I ∞ D)
    (hn : finrank ℝ E = 2 * n + 1) (x₀ : M) :
    ∃ chart : PartialDiffeomorph I
        𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) M
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) ∞,
      x₀ ∈ chart.source ∧ chart x₀ = 0 ∧
      ∀ x ∈ chart.source, D x =
        ((innerProductContactForm (EuclideanSpace ℝ (Fin n))).kerDistribution
            ((ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin n))).prodCongr
              (ContinuousLinearEquiv.neg ℝ) (chart x))).comap
          (((ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin n))).prodCongr
              (ContinuousLinearEquiv.neg ℝ)).toLinearMap ∘ₗ
            (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) chart
              x).toLinearMap) := by
  set V := EuclideanSpace ℝ (Fin n)
  obtain ⟨φ, hx₀, hφ₀, hφD⟩ := hD.exists_darbouxChart_of_finrank_eq hn x₀
  set σ : (V × V × ℝ) ≃L[ℝ] V × V × ℝ :=
    (ContinuousLinearEquiv.refl ℝ V).prodCongr (ContinuousLinearEquiv.neg ℝ)
  set chart := φ.trans σ.toDiffeomorph.toPartialDiffeomorph
  have hsrc : chart.source = φ.source := by simp [chart]
  have hcoe (x : M) : chart x = σ (φ x) := by simp [chart]
  have hd : ∀ x ∈ φ.source, ∀ v : TangentSpace I x, mvfderiv I chart x v = σ (mvfderiv I φ x v) :=
    fun x hx v ↦ by
      rw [φ.mvfderiv_trans_toDiffeomorph σ hx, ContinuousLinearMap.comp_apply,
        ContinuousLinearEquiv.coe_coe]
  have hσσ (y : V × V × ℝ) : σ (σ y) = y := by simp [σ]
  refine ⟨chart, hsrc ▸ hx₀, by rw [hcoe, hφ₀, map_zero], fun x hx ↦ ?_⟩
  rw [hsrc] at hx
  rw [hφD x hx]
  ext v
  -- The statement composes `σ` with `mfderiv chart x`, whose values lie in a tangent space of
  -- `ℝⁿ × ℝⁿ × ℝ`; `LinearMap.comp_apply` applies since that is the space itself by definition.
  have hcomp : (σ.toLinearMap ∘ₗ
      (mfderiv I 𝓘(ℝ, V × V × ℝ) chart x).toLinearMap) v = σ (mvfderiv I chart x v) := by
    rw [mvfderiv_apply_eq_mfderiv_apply]
    exact LinearMap.comp_apply _ _ _
  refine (Submodule.mem_comap.trans SmoothForm.mem_kerDistribution).trans
    (Iff.trans ?_ (Submodule.mem_comap.trans SmoothForm.mem_kerDistribution).symm)
  simp only [ContinuousLinearMap.coe_coe, ← mvfderiv_apply_eq_mfderiv_apply]
  have hR : (innerProductContactForm (EuclideanSpace ℝ (Fin n))).val (σ (chart x))
      ![(σ.toLinearMap ∘ₗ (mfderiv I 𝓘(ℝ, V × V × ℝ) chart x).toLinearMap) v] =
      (innerProductContactForm (EuclideanSpace ℝ (Fin n))).val (φ x) ![mvfderiv I φ x v] := by
    rw [hcomp, hd x hx, hcoe, hσσ, hσσ]
  -- The two sides now differ only in the type at which `![·]` is formed: the tangent space of
  -- `ℝⁿ × ℝⁿ × ℝ` at a point, or the space itself, which are the same type by definition.
  exact iff_of_eq (congrArg (· = 0) hR.symm)

end Darboux

end TauCeti

end
