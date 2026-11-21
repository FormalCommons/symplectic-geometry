/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Contact.Flat
public import TauCeti.Geometry.Contact.StableHamiltonian
public import TauCeti.Geometry.Contact.Volume
public import TauCeti.Geometry.Manifold.DifferentialForm.Flow
import TauCeti.Geometry.Manifold.VectorBundle.Bilinear.SmulRight
import TauCeti.Geometry.Manifold.VectorBundle.Hom
import TauCeti.Geometry.Manifold.VectorBundle.Translate
import TauCeti.Topology.Algebra.Module.BilinearForm

/-!
# Stable Hamiltonian structures: wedge criterion, smoothness and invariance

For a one-form `α` and a two-form `σ` on a manifold `M`, Tau Ceti's
`TauCeti.SmoothForm.IsStableHamiltonian α σ` is the stable Hamiltonian condition, with the
one-form first: McDuff–Salamon's pair `(Ω, λ)` is `IsStableHamiltonian λ Ω`. This file extends
Tau Ceti's `TauCeti.Geometry.Contact.StableHamiltonian` with the following.

* **The wedge criterion.** On a manifold of dimension `2 m + 1`, the pointwise condition on
  `(α, σ)` says that `α ∧ σ ^ m` vanishes nowhere
  (`TauCeti.SmoothForm.isStableHamiltonian_iff_wedge_wedgePow_apply_ne_zero`); in the book's
  dimension `2 n - 1` this is `λ ∧ Ω ^ (n - 1) ≠ 0`.
* **Smoothness of the characteristic vector field** `R`
  (`TauCeti.SmoothForm.contMDiff_characteristicVectorField`). Pointwise, `v ↦ ι_v σ + α(v) α` is
  an invertible map to the cotangent space, and `R` is the preimage of `α`.
* **Invariance.** `L_R σ = 0` and `L_R α = 0`, by Cartan's formula, and so the maximal flow of `R`
  pulls `σ` and `α` back to themselves wherever it is defined.
* **The contact case, in the book's signs.** For a contact form `α`, the pair `(α, -dα)` is a
  stable Hamiltonian structure, and its characteristic field is the Reeb field of `α`. Both
  follow from the general facts that multiplying `σ` by a nonzero constant changes neither the
  stable Hamiltonian condition (`TauCeti.SmoothForm.isStableHamiltonian_smul_iff`) nor the
  characteristic field (`TauCeti.SmoothForm.characteristicVectorField_smul`).

The proof of `contMDiff_characteristicVectorField` adapts Tau Ceti's proof of
`TauCeti.SmoothForm.IsContactForm.contMDiff_reebVectorField`, through the inverse of the contact
flat map (`TauCeti.SmoothForm.IsContactForm.contactFlatEquiv`), with `σ` in place of `dα`. The
pointwise step of the wedge criterion,
`TauCeti.SmoothForm.isContact_iff_wedge_wedgePow_apply_ne_zero`, adapts Tau Ceti's
`TauCeti.SmoothForm.isContactFormAt_iff_wedge_wedgePow_apply_ne_zero` in the same way.

## Main results

* `TauCeti.SmoothForm.isStableHamiltonian_iff_wedge_wedgePow_apply_ne_zero`
* `TauCeti.SmoothForm.contMDiff_characteristicVectorField`
* `TauCeti.SmoothForm.IsStableHamiltonian.mlieDerivForm_characteristicVectorField_twoForm`,
  `TauCeti.SmoothForm.IsStableHamiltonian.mlieDerivForm_characteristicVectorField_oneForm`
* `TauCeti.SmoothForm.IsStableHamiltonian.mpullback_flowOf_characteristicVectorField_twoForm`,
  `TauCeti.SmoothForm.IsStableHamiltonian.mpullback_flowOf_characteristicVectorField_oneForm`
* `TauCeti.SmoothForm.IsContactForm.isStableHamiltonian_neg`,
  `TauCeti.SmoothForm.characteristicVectorField_neg_mextDerivₗ`

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Exercise 3.5.37
-/

public section

noncomputable section

open Bundle Module
open scoped ContDiff Manifold

namespace TauCeti

namespace SmoothForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

section Basic

variable [IsManifold I 2 M] {α : SmoothForm I M ℝ 1} {σ : SmoothForm I M ℝ 2}

/-- The bilinear form of a scalar multiple of a two-form is the same multiple of its bilinear
form. -/
@[simp]
theorem bilinFormAt_smul (c : ℝ) (σ : SmoothForm I M ℝ 2) (x : M) :
    (c • σ).bilinFormAt x = c • σ.bilinFormAt x := by
  ext v w
  simp [SmoothBundleForm.eval₂_apply]

/-- The bilinear form of the negative of a two-form is the negative of its bilinear form. -/
@[simp]
theorem bilinFormAt_neg (σ : SmoothForm I M ℝ 2) (x : M) :
    (-σ).bilinFormAt x = -σ.bilinFormAt x := by
  ext v w
  simp [SmoothBundleForm.eval₂_apply]

/-- Multiplying the two-form by a nonzero constant does not change the characteristic vector
field. -/
theorem characteristicVectorField_smul {c : ℝ} (hc : c ≠ 0) (α : SmoothForm I M ℝ 1)
    (σ : SmoothForm I M ℝ 2) :
    α.characteristicVectorField (c • σ) = α.characteristicVectorField σ := by
  funext x
  rw [characteristicVectorField_def, characteristicVectorField_def, bilinFormAt_smul,
    Module.Dual.reebVector_smul_bilinForm hc]

/-- Negating the two-form does not change the characteristic vector field. -/
@[simp]
theorem characteristicVectorField_neg (α : SmoothForm I M ℝ 1) (σ : SmoothForm I M ℝ 2) :
    α.characteristicVectorField (-σ) = α.characteristicVectorField σ := by
  rw [← neg_one_smul ℝ σ, characteristicVectorField_smul (by norm_num)]

/-- Multiplying the two-form by a nonzero constant preserves stable Hamiltonian structures. -/
theorem IsStableHamiltonian.smul {c : ℝ} (hc : c ≠ 0) (h : α.IsStableHamiltonian σ) :
    α.IsStableHamiltonian (c • σ) where
  isClosed := h.isClosed.smul c
  isContact x := by
    rw [bilinFormAt_smul, Module.Dual.isContact_smul_bilinForm_iff hc]
    exact h.isContact x
  ker_le_ker x := by
    rw [bilinFormAt_smul, LinearMap.ker_smul _ _ hc]
    exact h.ker_le_ker x

/-- For `c ≠ 0`, `(α, c • σ)` is a stable Hamiltonian structure exactly when `(α, σ)` is. -/
theorem isStableHamiltonian_smul_iff {c : ℝ} (hc : c ≠ 0) :
    α.IsStableHamiltonian (c • σ) ↔ α.IsStableHamiltonian σ :=
  ⟨fun h ↦ by simpa [smul_smul, hc] using h.smul (inv_ne_zero hc), IsStableHamiltonian.smul hc⟩

/-- Negating the two-form preserves stable Hamiltonian structures. -/
theorem IsStableHamiltonian.neg (h : α.IsStableHamiltonian σ) : α.IsStableHamiltonian (-σ) := by
  rw [← neg_one_smul ℝ σ]
  exact h.smul (by norm_num)

/-- `(α, -σ)` is a stable Hamiltonian structure exactly when `(α, σ)` is. -/
@[simp]
theorem isStableHamiltonian_neg_iff : α.IsStableHamiltonian (-σ) ↔ α.IsStableHamiltonian σ := by
  rw [← neg_one_smul ℝ σ, isStableHamiltonian_smul_iff (by norm_num)]

/-- **The contact case.** For a contact form `α`, the pair `(α, -dα)` is a stable Hamiltonian
structure. -/
theorem IsContactForm.isStableHamiltonian_neg (hα : α.IsContactForm) :
    α.IsStableHamiltonian (-mextDerivₗ I 1 α) :=
  hα.isStableHamiltonian.neg

/-- The characteristic vector field of `(α, -dα)` is the Reeb vector field of `α`. -/
@[simp]
theorem characteristicVectorField_neg_mextDerivₗ (α : SmoothForm I M ℝ 1) :
    α.characteristicVectorField (-mextDerivₗ I 1 α) = α.reebVectorField := by
  rw [characteristicVectorField_neg, characteristicVectorField_mextDerivₗ]

/-- At a point, `α_x` is contact for `σ_x` exactly when `α ∧ σ ^ m` does not vanish there, on a
manifold of dimension `2 m + 1`. -/
theorem isContact_iff_wedge_wedgePow_apply_ne_zero [FiniteDimensional ℝ E] {m : ℕ}
    (hm : finrank ℝ E = 2 * m + 1) (α : SmoothForm I M ℝ 1) (σ : SmoothForm I M ℝ 2) (x : M) :
    Module.Dual.IsContact (degreeOneEquiv α x : TangentSpace I x →ₗ[ℝ] ℝ) (σ.bilinFormAt x) ↔
      (wedge α (σ.wedgePow m)).val x ≠ 0 := by
  have key := ContinuousAlternatingMap.pairedWedge_wedgePow_ne_zero_iff hm (α.val x) (σ.val x)
  rw [coe_wedge, RoughForm.wedge_def, RoughForm.wedgeWith_apply', wedgePow_apply,
    Module.Dual.isContact_iff_of_isRefl (isAlt_bilinFormAt _ x).isRefl]
  refine Iff.trans ?_ key.symm
  simp only [ne_eq, degreeOneEquiv_coe_eq_zero_iff, degreeOneEquiv_coe_apply, bilinFormAt_apply,
    SmoothBundleForm.eval₂_apply]
  -- The two sides differ only in writing the tangent space `TangentSpace I x` or its model `E`.
  exact Iff.rfl

/-- **The wedge criterion.** On a manifold of dimension `2 m + 1`, `(α, σ)` is a stable
Hamiltonian structure exactly when `σ` is closed, `α ∧ σ ^ m` vanishes nowhere, and the kernel of
`σ` lies in the kernel of `dα` at every point. -/
theorem isStableHamiltonian_iff_wedge_wedgePow_apply_ne_zero [FiniteDimensional ℝ E] {m : ℕ}
    (hm : finrank ℝ E = 2 * m + 1) :
    α.IsStableHamiltonian σ ↔
      σ.IsClosed ∧ (∀ x, (wedge α (σ.wedgePow m)).val x ≠ 0) ∧
        ∀ x, LinearMap.ker (σ.bilinFormAt x) ≤
          LinearMap.ker ((mextDerivₗ I 1 α).bilinFormAt x) := by
  simp only [← isContact_iff_wedge_wedgePow_apply_ne_zero hm]
  exact ⟨fun h ↦ ⟨h.isClosed, h.isContact, h.ker_le_ker⟩, fun ⟨h₁, h₂, h₃⟩ ↦ ⟨h₁, h₂, h₃⟩⟩

end Basic

section Smooth

variable [IsManifold I ∞ M] [FiniteDimensional ℝ E] {α : SmoothForm I M ℝ 1}
  {σ : SmoothForm I M ℝ 2}

/-- **The characteristic vector field is smooth** when `α_x` is contact for `σ_x` at every point
of a finite-dimensional manifold. -/
theorem contMDiff_characteristicVectorField
    (hc : ∀ x, Module.Dual.IsContact (degreeOneEquiv α x : TangentSpace I x →ₗ[ℝ] ℝ)
      (σ.bilinFormAt x)) :
    ContMDiff I I.tangent ∞ (T% (α.characteristicVectorField σ)) := by
  -- The bundle map `v ↦ ι_v σ + α(v) α`.
  set Φ : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ := fun x ↦
    SmoothTwoForm.flat σ x + (degreeOneEquiv α x).smulRight (degreeOneEquiv α x)
  have hΦapp (x : M) (v w : TangentSpace I x) : Φ x v w =
      (σ.bilinFormAt x + (degreeOneEquiv α x : TangentSpace I x →ₗ[ℝ] ℝ).smulRight
        (degreeOneEquiv α x : TangentSpace I x →ₗ[ℝ] ℝ)) v w := by
    simp [Φ]
  have hΦ : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) x (Φ x)) :=
    fun x₀ ↦ by
      have hα₁ : ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
          (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ) (E := fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) x
            (degreeOneEquiv α x)) x₀ :=
        (degreeOneEquiv α).contMDiff x₀
      exact ContMDiffAt.add_sectionAlong (SmoothTwoForm.contMDiff_flat σ x₀)
        (hα₁.clm_bundle_smulRight hα₁)
  have hinv (x : M) : (Φ x).IsInvertible :=
    ContinuousLinearMap.isInvertible_of_separatingLeft fun (v : TangentSpace I x) hv ↦
      (hc x).separatingLeft_add_smulRight (isAlt_bilinFormAt _ x) v
        fun w ↦ (hΦapp x v w).symm.trans (hv w)
  -- The characteristic vector is the preimage of `α` under `Φ`.
  have hR (x : M) : α.characteristicVectorField σ x = (Φ x).inverse (degreeOneEquiv α x) := by
    have h := ((hc x).add_smulRight_apply_eq_self_iff (isAlt_bilinFormAt _ x)).2
      ⟨(hc x).apply_reebVector, LinearMap.mem_ker.1 ((hc x).reebVector_mem_ker
        (isAlt_bilinFormAt _ x))⟩
    rw [← characteristicVectorField_def] at h
    have hΦR : Φ x (α.characteristicVectorField σ x) = degreeOneEquiv α x :=
      ContinuousLinearMap.ext fun w ↦ (hΦapp x _ w).trans (LinearMap.congr_fun h w)
    rw [← hΦR, (hinv x).inverse_apply_self]
  have h := (hΦ.clm_bundle_inverse hinv).clm_bundle_apply (degreeOneEquiv α).contMDiff
  convert h using 2 with x
  rw [hR]

namespace IsStableHamiltonian

variable (h : α.IsStableHamiltonian σ)
include h

/-- The characteristic vector field `R` of a stable Hamiltonian structure `(α, σ)` preserves the
two-form: `L_R σ = 0`. -/
theorem mlieDerivForm_characteristicVectorField_twoForm :
    mlieDerivForm (α.characteristicVectorField σ) σ.val = 0 := by
  rw [mlieDerivForm_eq_mextDeriv_interior
    ((contMDiff_characteristicVectorField h.isContact).mdifferentiable (by simp)) h.isClosed,
    interior_characteristicVectorField h.isContact]
  simp

/-- The characteristic vector field `R` of a stable Hamiltonian structure `(α, σ)` preserves the
one-form: `L_R α = 0`. -/
theorem mlieDerivForm_characteristicVectorField_oneForm :
    mlieDerivForm (α.characteristicVectorField σ) α.val = 0 := by
  have hR := (contMDiff_characteristicVectorField h.isContact).mdifferentiable (by simp)
  funext y
  refine ContinuousAlternatingMap.ext fun v ↦ ?_
  obtain ⟨w, rfl⟩ : ∃ w, v = ![w] := ⟨v 0, funext fun i ↦ by fin_cases i; rfl⟩
  rw [mlieDerivForm_apply_eq_mextDeriv_add (f := fun _ ↦ (1 : ℝ))
    (fun y ↦ apply_characteristicVectorField (h.isContact y)) (α.mdifferentiable y) (hR y),
    h.mextDeriv_characteristicVectorField_left]
  simp [mvfderiv_const]

variable [I.Boundaryless] [T2Space M]

/-- **The flow of the characteristic vector field preserves the two-form.** Wherever the maximal
flow `φ` of the characteristic vector field of a stable Hamiltonian structure `(α, σ)` through
`x` is defined at time `t`, `(φₜ^* σ)ₓ = σₓ`. -/
theorem mpullback_flowOf_characteristicVectorField_twoForm {t : ℝ} {x : M}
    (hx : (t, x) ∈ flowDomain (α.characteristicVectorField σ)) :
    TauCeti.mpullback I I (flowOf (α.characteristicVectorField σ) t) σ.val x = σ.val x :=
  mpullback_flowOf_apply_of_mextDeriv_interior_eq_zero
    ((contMDiff_characteristicVectorField h.isContact).of_le (by simp)) h.isClosed
    (by rw [interior_characteristicVectorField h.isContact]; simp) hx

/-- **The flow of the characteristic vector field preserves the one-form.** Wherever the maximal
flow `φ` of the characteristic vector field of a stable Hamiltonian structure `(α, σ)` through
`x` is defined at time `t`, `(φₜ^* α)ₓ = αₓ`. -/
theorem mpullback_flowOf_characteristicVectorField_oneForm {t : ℝ} {x : M}
    (hx : (t, x) ∈ flowDomain (α.characteristicVectorField σ)) :
    TauCeti.mpullback I I (flowOf (α.characteristicVectorField σ) t) α.val x = α.val x :=
  mpullback_flowOf_apply_of_interior_mextDeriv_eq_zero
    ((contMDiff_characteristicVectorField h.isContact).of_le (by simp))
    (fun y ↦ apply_characteristicVectorField (h.isContact y))
    h.interior_mextDeriv_characteristicVectorField hx

end IsStableHamiltonian

end Smooth

end SmoothForm

end TauCeti
