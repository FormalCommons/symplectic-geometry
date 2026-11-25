/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Contact.Darboux.Strict
public import SymplecticGeometry.Topology.Algebra.Module.Alternating.Basic
import SymplecticGeometry.Geometry.Contact.Pullback
import SymplecticGeometry.Geometry.Contact.Standard
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv

/-!
# Contact Darboux charts for the form `Σᵢ pᵢ dqᵢ - dz`

Tau Ceti's Darboux theorem for contact forms
(`TauCeti.SmoothForm.IsContactForm.exists_strictDarbouxChart_of_finrank_eq`) gives, around every
point of a boundaryless contact manifold of dimension `2 n + 1`, a chart into `ℝⁿ × ℝⁿ × ℝ` that
pulls `dz - Σᵢ pᵢ dqᵢ` (`TauCeti.innerProductContactForm`) back to the contact form. McDuff and
Salamon write the standard contact form with the other sign, as `Σᵢ pᵢ dqᵢ - dz`, which is
`-innerProductContactForm`; the statements write it so, with no new name. The linear involution
`σ (q, p, z) = (q, -p, -z)`, which is
`(ContinuousLinearEquiv.refl ℝ V).prodCongr (ContinuousLinearEquiv.neg ℝ)` on `V × (V × ℝ)`,
pulls `innerProductContactForm` back to its negative (as in Tau Ceti's
`TauCeti.mpullback_innerProductContactForm_neg`), so following Tau Ceti's chart by `σ` gives a
chart that pulls `-innerProductContactForm` back to the contact form.

That chart then carries the Reeb field of the contact form to the Reeb field of
`-innerProductContactForm`
(`TauCeti.SmoothForm.IsContactForm.mfderiv_reebVectorField_of_eventuallyEq_mpullback`), which is
`-∂_z` (`TauCeti.SmoothForm.IsContactForm.reebVectorField_neg` and
`TauCeti.reebVectorField_innerProductContactForm`).

For a contact structure without a defining form, Tau Ceti's
`TauCeti.IsContactDistribution.exists_darbouxChart_of_finrank_eq` already identifies it locally
with the kernel of `innerProductContactForm`, which is that of `-innerProductContactForm`
(`TauCeti.SmoothForm.kerDistribution_neg`), so this file adds nothing for that case.

## Main results

* `TauCeti.SmoothForm.IsContactForm.exists_strictDarbouxChart_reebVectorField_of_finrank_eq`: the
  contact Darboux theorem for `Σᵢ pᵢ dqᵢ - dz`, with the Reeb field `-∂_z` and the kernels.

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
form on a boundaryless manifold of dimension `2 n + 1`. Around every point `x₀` there is a smooth
partial diffeomorphism `chart` from `M` to `ℝⁿ × ℝⁿ × ℝ` with `x₀ ∈ chart.source` and
`chart x₀ = 0` such that, on `chart.source`,
* `chart` pulls `Σᵢ pᵢ dqᵢ - dz`, which is `-innerProductContactForm`, back to `α`;
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
        (-innerProductContactForm (EuclideanSpace ℝ (Fin n))).val (chart x)
            ![mvfderiv I chart x v] = α.val x ![v]) ∧
      (∀ x ∈ chart.source, mvfderiv I chart x (α.reebVectorField x) = (0, 0, -1)) ∧
      ∀ x ∈ chart.source, α.kerDistribution x =
        ((-innerProductContactForm (EuclideanSpace ℝ (Fin n))).kerDistribution (chart x)).comap
          (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) chart
            x).toLinearMap := by
  set V := EuclideanSpace ℝ (Fin n)
  obtain ⟨φ, hx₀, hφ₀, hpb⟩ := hα.exists_strictDarbouxChart_of_finrank_eq hn x₀
  set σ : (V × V × ℝ) ≃L[ℝ] V × V × ℝ :=
    (ContinuousLinearEquiv.refl ℝ V).prodCongr (ContinuousLinearEquiv.neg ℝ)
  set chart := φ.trans σ.toDiffeomorph.toPartialDiffeomorph
  have hsrc : chart.source = φ.source := by simp [chart]
  have hcoe (x : M) : chart x = σ (φ x) := by simp [chart]
  -- `σ` pulls `innerProductContactForm` back to its negative.
  have hneg (y w : V × V × ℝ) :
      (innerProductContactForm V).val (σ y) ![σ w] = -(innerProductContactForm V).val y ![w] :=
    (innerProductContactForm_apply V (σ y) (σ w)).trans <|
      Eq.trans (by simp [σ]; ring) (congrArg Neg.neg (innerProductContactForm_apply V y w)).symm
  have hform : ∀ x ∈ chart.source, ∀ v : TangentSpace I x,
      (-innerProductContactForm V).val (chart x) ![mvfderiv I chart x v] = α.val x ![v] := by
    intro x hx v
    have hd : mvfderiv I chart x v = σ (mvfderiv I φ x v) := by
      rw [show ⇑chart = ⇑σ ∘ ⇑φ from funext hcoe, σ.mvfderiv_comp_apply]
    rw [hsrc] at hx
    rw [hd, hcoe, ← hpb x hx, Submodule.coe_neg, Pi.neg_apply,
      ContinuousAlternatingMap.neg_apply]
    -- The vectors here lie in `V × V × ℝ` rather than in its tangent spaces, which are the same
    -- type by definition, so `hneg` and `neg_neg` are applied by `exact` rather than by `rw`.
    exact (congrArg Neg.neg (hneg _ _)).trans (neg_neg _)
  refine ⟨chart, hsrc ▸ hx₀, by rw [hcoe, hφ₀, map_zero], hform, fun x hx ↦ ?_, fun x hx ↦ ?_⟩
  · -- Near `x`, the chart pulls `-innerProductContactForm` back to `α`.
    have hpb' : ∀ᶠ y in 𝓝 x, α.val y = TauCeti.mpullback I 𝓘(ℝ, V × V × ℝ) chart
        (-innerProductContactForm V).val y := by
      filter_upwards [chart.open_source.mem_nhds hx] with y hy
      refine ContinuousAlternatingMap.ext_fin_one fun w ↦ ?_
      rw [← hform y hy, mvfderiv_apply_eq_mfderiv_apply, TauCeti.mpullback_apply]
      congr 1
      -- The outer `Eq.symm` makes Lean read the vector off the goal's right side.
      exact Eq.symm (FinVec.etaExpand_eq _).symm
    have hR := hα.mfderiv_reebVectorField_of_eventuallyEq_mpullback
      (SmoothForm.isContactForm_neg_iff.2 (isContactForm_innerProductContactForm V))
      (((chart.contMDiffOn x hx).contMDiffAt (chart.open_source.mem_nhds hx)).of_le (by simp))
      (chart.isInvertible_mfderiv (by simp) hx).surjective hpb'
    rw [mvfderiv_apply_eq_mfderiv_apply, hR,
      (isContactForm_innerProductContactForm V).reebVectorField_neg,
      reebVectorField_innerProductContactForm]
    -- The tangent space of `V × V × ℝ` at a point is `V × V × ℝ` itself, by definition.
    exact (by simp : -((0, 0, 1) : V × V × ℝ) = (0, 0, -1))
  · ext v
    rw [SmoothForm.mem_kerDistribution, ← hform x hx v]
    exact (Submodule.mem_comap.trans SmoothForm.mem_kerDistribution).symm

end Darboux

end TauCeti

end
