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
public import SymplecticGeometry.Topology.Sets.Strip
import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Leibniz
import TauCeti.Geometry.Manifold.MFDeriv.Prod
import TauCeti.Geometry.Manifold.VectorBundle.Bilinear.SmulRight
import TauCeti.Geometry.Manifold.VectorBundle.Hom
import TauCeti.Geometry.Manifold.VectorBundle.Translate
import TauCeti.Geometry.Symplectic.Manifold.Opens
import TauCeti.Topology.Algebra.Module.BilinearForm
import SymplecticGeometry.Geometry.Symplectic.Manifold.Family

/-!
# Stable Hamiltonian structures: wedge criterion, invariance and the model

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
* **The stable Hamiltonian model** `TauCeti.SmoothForm.stableHamiltonianModel α σ`, the two-form
  `σ - d(r α)` on `ℝ × M` (the book's `Ω - d(r λ)`), with `r` the real coordinate. Its slice
  at `r` is `σ - r dα`, and at `(r, x)` it is nondegenerate exactly when `α_x` is contact for
  `σ_x - r dα_x`. For a stable Hamiltonian structure it is therefore nondegenerate along
  `{0} × M`; on a compact `M` it is symplectic on a strip `(-ε, ε) × M`
  (`SymplecticGeometry.symmStrip`), and wherever it is nondegenerate the kernel of its slice is
  that of `σ`.

The proof of `contMDiff_characteristicVectorField` adapts Tau Ceti's proof of
`TauCeti.SmoothForm.IsContactForm.contMDiff_reebVectorField`, through the inverse of the contact
flat map (`TauCeti.SmoothForm.IsContactForm.contactFlatEquiv`), with `σ` in place of `dα`. The
pointwise step of the wedge criterion,
`TauCeti.SmoothForm.isContact_iff_wedge_wedgePow_apply_ne_zero`, adapts Tau Ceti's
`TauCeti.SmoothForm.isContactFormAt_iff_wedge_wedgePow_apply_ne_zero` in the same way. The
computation of the model, `TauCeti.SmoothForm.stableHamiltonianModel_apply`, and its reading as a
symplectization form of linear algebra, which gives
`TauCeti.SmoothForm.nondegenerate_bilinFormAt_stableHamiltonianModel_iff`, adapt Tau Ceti's
`TauCeti.SmoothForm.mextDeriv_symplectization_apply` and
`TauCeti.SmoothForm.isNondegenerate_mextDerivₗ_symplectization_iff`, with the factor `r` in place
of `eᵗ`.

## Main results

* `TauCeti.SmoothForm.isStableHamiltonian_iff_wedge_wedgePow_apply_ne_zero`
* `TauCeti.SmoothForm.contMDiff_characteristicVectorField`
* `TauCeti.SmoothForm.IsStableHamiltonian.mlieDerivForm_characteristicVectorField_twoForm`,
  `TauCeti.SmoothForm.IsStableHamiltonian.mlieDerivForm_characteristicVectorField_oneForm`
* `TauCeti.SmoothForm.IsStableHamiltonian.mpullback_flowOf_characteristicVectorField_twoForm`,
  `TauCeti.SmoothForm.IsStableHamiltonian.mpullback_flowOf_characteristicVectorField_oneForm`
* `TauCeti.SmoothForm.IsContactForm.isStableHamiltonian_neg`,
  `TauCeti.SmoothForm.characteristicVectorField_neg_mextDerivₗ`
* `TauCeti.SmoothForm.stableHamiltonianModel_apply`,
  `TauCeti.SmoothForm.mpullback_prodMk_stableHamiltonianModel`,
  `TauCeti.SmoothForm.nondegenerate_bilinFormAt_stableHamiltonianModel_iff`
* `TauCeti.SmoothForm.IsStableHamiltonian.isNondegenerate_stableHamiltonianModel_zero`,
  `TauCeti.SmoothForm.IsStableHamiltonian.exists_isSymplectic_stableHamiltonianModel`,
  `TauCeti.SmoothForm.IsStableHamiltonian.ker_mpullback_prodMk_stableHamiltonianModel`

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

section Model

/-! ### The stable Hamiltonian model -/

variable [IsManifold I ∞ M]

/-- The **stable Hamiltonian model** of a one-form `α` and a two-form `σ` on `M`: the two-form
`σ - d(r α)` on `ℝ × M`, where `r` is the real coordinate and `α`, `σ` are pulled back along the
projection to `M`. In McDuff–Salamon's notation, with `(Ω, λ) = (σ, α)`, it is `Ω - d(r λ)`. When
`(α, σ)` is a stable Hamiltonian structure on a compact manifold, it is symplectic on a strip
`(-ε, ε) × M` (`IsStableHamiltonian.exists_isSymplectic_stableHamiltonianModel`). -/
def stableHamiltonianModel (α : SmoothForm I M ℝ 1) (σ : SmoothForm I M ℝ 2) :
    SmoothTwoForm (𝓘(ℝ).prod I) (ℝ × M) :=
  mpullback Prod.snd contMDiff_snd σ -
    mextDerivₗ (𝓘(ℝ).prod I) 1
      (funSMulₗ (⟨Prod.fst, contMDiff_fst⟩ : C^∞⟮𝓘(ℝ).prod I, ℝ × M; ℝ⟯)
        (mpullback Prod.snd contMDiff_snd α))

/-- The stable Hamiltonian model is `σ - d(r α)`, with `σ` and `α` pulled back along the
projection to `M` and `r` the real coordinate. -/
theorem stableHamiltonianModel_def (α : SmoothForm I M ℝ 1) (σ : SmoothForm I M ℝ 2) :
    stableHamiltonianModel α σ =
      mpullback Prod.snd contMDiff_snd σ -
        mextDerivₗ (𝓘(ℝ).prod I) 1
          (funSMulₗ (⟨Prod.fst, contMDiff_fst⟩ : C^∞⟮𝓘(ℝ).prod I, ℝ × M; ℝ⟯)
            (mpullback Prod.snd contMDiff_snd α)) :=
  (rfl)

/-- The value of the stable Hamiltonian model `σ - r dα - dr ∧ α` at `(r, x)` on tangent vectors
`(s, v)` and `(s', w)`: it is `σ_x(v, w) - r dα_x(v, w) - (s α_x(w) - s' α_x(v))`. -/
theorem stableHamiltonianModel_apply (α : SmoothForm I M ℝ 1) (σ : SmoothForm I M ℝ 2)
    (p : ℝ × M) (v w : TangentSpace (𝓘(ℝ).prod I) p) :
    (stableHamiltonianModel α σ).eval₂ p v w =
      σ.eval₂ p.2 (Manifold.tangentSpaceProdEquiv p v).2 (Manifold.tangentSpaceProdEquiv p w).2 -
        p.1 * (mextDerivₗ I 1 α).eval₂ p.2 (Manifold.tangentSpaceProdEquiv p v).2
          (Manifold.tangentSpaceProdEquiv p w).2 -
        (NormedSpace.fromTangentSpace p.1 (Manifold.tangentSpaceProdEquiv p v).1 *
            α.val p.2 ![(Manifold.tangentSpaceProdEquiv p w).2] -
          NormedSpace.fromTangentSpace p.1 (Manifold.tangentSpaceProdEquiv p w).1 *
            α.val p.2 ![(Manifold.tangentSpaceProdEquiv p v).2]) := by
  set β : SmoothForm (𝓘(ℝ).prod I) (ℝ × M) ℝ 1 := mpullback Prod.snd contMDiff_snd α
  set g : C^∞⟮𝓘(ℝ).prod I, ℝ × M; ℝ⟯ := ⟨Prod.fst, contMDiff_fst⟩
  have hβ (u : TangentSpace (𝓘(ℝ).prod I) p) :
      β.val p ![u] = α.val p.2 ![(Manifold.tangentSpaceProdEquiv p u).2] := by
    simp only [β, mpullback_snd_apply, Matrix.vec_single_eq_const]
  -- By naturality, `dβ` is `dα` on the second components.
  have hdβ : mextDeriv β.val p ![v, w] =
      (mextDerivₗ I 1 α).eval₂ p.2 (Manifold.tangentSpaceProdEquiv p v).2
        (Manifold.tangentSpaceProdEquiv p w).2 := by
    rw [← eval₂_mpullback_snd, ← mextDerivₗ_mpullback, SmoothBundleForm.eval₂_apply,
      mextDerivₗ_apply]
  -- The derivative of the coordinate `r` in the direction of `(s, v)` is `s`.
  have hg (u : TangentSpace (𝓘(ℝ).prod I) p) :
      mvfderiv (𝓘(ℝ).prod I) g p u =
        NormedSpace.fromTangentSpace p.1 (Manifold.tangentSpaceProdEquiv p u).1 := by
    rw [Manifold.tangentSpaceProdEquiv_apply, ← mul_one (NormedSpace.fromTangentSpace _ _),
      ← smul_eq_mul]
    exact (hasDerivAt_id p.1).mvfderiv_comp_fst_apply u
  rw [stableHamiltonianModel_def, SmoothBundleForm.eval₂_apply, Submodule.coe_sub, Pi.sub_apply,
    ContinuousAlternatingMap.sub_apply, ← SmoothBundleForm.eval₂_apply, eval₂_mpullback_snd,
    mextDerivₗ_apply, coe_funSMulₗ g β,
    mextDeriv_fun_smul_apply ((g.contMDiff p).mdifferentiableAt (by simp))
      (β.mdifferentiableAt p), hg, hg, hβ, hβ, hdβ]
  simp only [g, ContMDiffMap.coeFn_mk]
  ring

/-- **The slices of the stable Hamiltonian model.** The pullback of the model along
`x ↦ (r, x)` is `σ - r dα`. -/
theorem mpullback_prodMk_stableHamiltonianModel (α : SmoothForm I M ℝ 1)
    (σ : SmoothForm I M ℝ 2) (r : ℝ) :
    mpullback (Prod.mk r) (contMDiff_const.prodMk contMDiff_id) (stableHamiltonianModel α σ) =
      σ - r • mextDerivₗ I 1 α := by
  have hsnd {k : ℕ} (φ : SmoothForm I M ℝ k) :
      mpullback (Prod.mk r) (contMDiff_const.prodMk contMDiff_id)
        (mpullback (Prod.snd : ℝ × M → M) (contMDiff_snd (I := 𝓘(ℝ))) φ) = φ := by
    rw [mpullback_mpullback]
    -- `Prod.snd ∘ Prod.mk r` is the identity of `M` by definition.
    exact LinearMap.congr_fun mpullback_id φ
  set g : C^∞⟮𝓘(ℝ).prod I, ℝ × M; ℝ⟯ := ⟨Prod.fst, contMDiff_fst⟩
  have hsmul : mpullback (Prod.mk r) (contMDiff_const.prodMk contMDiff_id)
      (funSMulₗ g (mpullback Prod.snd contMDiff_snd α)) = r • α := by
    apply Subtype.ext
    rw [coe_mpullback, coe_funSMulₗ g, TauCeti.mpullback_fun_smul,
      ← coe_mpullback (Prod.mk r) (contMDiff_const.prodMk contMDiff_id), hsnd, smul_toRoughForm]
    simp only [g, ContMDiffMap.coeFn_mk, Pi.smul_def]
  rw [stableHamiltonianModel_def, map_sub, hsnd, ← mextDerivₗ_mpullback, hsmul, map_smul]

/-- The stable Hamiltonian model of a closed two-form is closed. -/
theorem isClosed_stableHamiltonianModel {α : SmoothForm I M ℝ 1} {σ : SmoothForm I M ℝ 2}
    (hσ : σ.IsClosed) : (stableHamiltonianModel α σ).IsClosed := by
  rw [stableHamiltonianModel_def]
  exact (hσ.mpullback _ _).sub (isClosed_mextDerivₗ _)

/-- At `(r, x)`, the stable Hamiltonian model is the symplectization form of the covector `-α_x`
and the bilinear form `σ_x - r dα_x`, read through the splitting
`T_(r, x)(ℝ × M) = ℝ × T_x M`. -/
private theorem bilinFormAt_stableHamiltonianModel (α : SmoothForm I M ℝ 1)
    (σ : SmoothForm I M ℝ 2) (p : ℝ × M) :
    (stableHamiltonianModel α σ).bilinFormAt p =
      LinearMap.BilinForm.congr
        (((NormedSpace.fromTangentSpace (𝕜 := ℝ) p.1).symm.prodCongr
          (ContinuousLinearEquiv.refl ℝ (TangentSpace I p.2))).trans
          (Manifold.tangentSpaceProdEquiv p).symm).toLinearEquiv
        (Module.Dual.symplectizationForm (-degreeOneEquiv α p.2 : TangentSpace I p.2 →ₗ[ℝ] ℝ)
          ((σ - p.1 • mextDerivₗ I 1 α).bilinFormAt p.2)) := by
  refine LinearMap.ext₂ fun v w ↦ ?_
  rw [bilinFormAt_apply, stableHamiltonianModel_apply, LinearMap.BilinForm.congr_apply,
    Module.Dual.symplectizationForm_apply]
  -- The inverse of the splitting sends `u` to its two components `(s, v)`.
  simp only [ContinuousLinearEquiv.coe_symm_toLinearEquiv, ContinuousLinearEquiv.symm_trans_apply,
    ContinuousLinearEquiv.symm_symm, ContinuousLinearEquiv.prodCongr_symm,
    ContinuousLinearEquiv.prodCongr_apply, ContinuousLinearEquiv.refl_symm,
    ContinuousLinearEquiv.coe_refl', id_eq, LinearMap.neg_apply, degreeOneEquiv_coe_apply,
    SmoothBundleForm.eval₂_apply, Submodule.coe_sub, Submodule.coe_smul, Pi.sub_apply,
    Pi.smul_apply, ContinuousAlternatingMap.sub_apply, ContinuousAlternatingMap.smul_apply,
    bilinFormAt_apply, smul_eq_mul]
  ring

/-- The stable Hamiltonian model is nondegenerate at `(r, x)` exactly when `α_x` is contact for
`σ_x - r dα_x`. -/
theorem nondegenerate_bilinFormAt_stableHamiltonianModel_iff (α : SmoothForm I M ℝ 1)
    (σ : SmoothForm I M ℝ 2) (p : ℝ × M) :
    ((stableHamiltonianModel α σ).bilinFormAt p).Nondegenerate ↔
      Module.Dual.IsContact (degreeOneEquiv α p.2 : TangentSpace I p.2 →ₗ[ℝ] ℝ)
        ((σ - p.1 • mextDerivₗ I 1 α).bilinFormAt p.2) := by
  rw [bilinFormAt_stableHamiltonianModel, LinearMap.BilinForm.nondegenerate_congr_iff,
    ← Module.Dual.isContact_iff_nondegenerate_symplectizationForm, ← neg_one_smul ℝ,
    Module.Dual.isContact_smul_iff (by norm_num)]

namespace IsStableHamiltonian

variable {α : SmoothForm I M ℝ 1} {σ : SmoothForm I M ℝ 2} (h : α.IsStableHamiltonian σ)
include h

/-- The stable Hamiltonian model of a stable Hamiltonian structure is nondegenerate at every
point `(0, x)` of the zero slice. -/
theorem isNondegenerate_stableHamiltonianModel_zero (x : M) :
    ((stableHamiltonianModel α σ).bilinFormAt ((0 : ℝ), x)).Nondegenerate := by
  rw [nondegenerate_bilinFormAt_stableHamiltonianModel_iff, zero_smul, sub_zero]
  exact h.isContact x

/-- **The stable Hamiltonian model is symplectic near the zero slice.** For a stable Hamiltonian
structure `(α, σ)` on a compact finite-dimensional manifold `M`, the model `σ - d(r α)` is a
symplectic form on the strip `(-ε, ε) × M` for some `ε > 0`. -/
theorem exists_isSymplectic_stableHamiltonianModel [FiniteDimensional ℝ E] [CompactSpace M] :
    ∃ ε > 0, SmoothTwoForm.IsSymplectic
      (mpullback (Subtype.val : SymplecticGeometry.symmStrip M ε → ℝ × M) contMDiff_subtypeVal
        (stableHamiltonianModel α σ)) := by
  obtain ⟨ε, hε, hle⟩ := SymplecticGeometry.exists_symmStrip_le
    (U := ⟨_, SmoothTwoForm.isOpen_setOf_nondegenerate_bilinFormAt (stableHamiltonianModel α σ)⟩)
    h.isNondegenerate_stableHamiltonianModel_zero
  refine ⟨ε, hε, (isClosed_stableHamiltonianModel h.isClosed).mpullback _ _,
    SmoothTwoForm.isNondegenerate_iff_forall_ker_bilinFormAt_eq_bot.2 fun p ↦ ?_⟩
  exact ((SmoothTwoForm.nondegenerate_bilinFormAt_mpullback_subtype_val_iff p).2
    (hle p.property)).ker_eq_bot

/-- **The kernels of the slices of the model.** At a point `(r, x)` where the stable Hamiltonian
model of a stable Hamiltonian structure `(α, σ)` on a finite-dimensional manifold is
nondegenerate, the kernel of its slice `σ - r dα` at `x` is the kernel of `σ_x`. -/
theorem ker_mpullback_prodMk_stableHamiltonianModel [FiniteDimensional ℝ E] {r : ℝ} {x : M}
    (hnd : ((stableHamiltonianModel α σ).bilinFormAt (r, x)).Nondegenerate) :
    LinearMap.ker ((mpullback (Prod.mk r) (contMDiff_const.prodMk contMDiff_id)
      (stableHamiltonianModel α σ)).bilinFormAt x) = LinearMap.ker (σ.bilinFormAt x) := by
  have hc' := (nondegenerate_bilinFormAt_stableHamiltonianModel_iff α σ (r, x)).1 hnd
  have hc := h.isContact x
  -- The kernel of `σ_x` lies in that of `dα_x`, hence in that of `σ_x - r dα_x`.
  have hle : LinearMap.ker (σ.bilinFormAt x) ≤
      LinearMap.ker ((σ - r • mextDerivₗ I 1 α).bilinFormAt x) := fun v hv ↦ by
    have hv' := h.ker_le_ker x hv
    rw [LinearMap.mem_ker] at hv hv' ⊢
    refine LinearMap.ext fun w ↦ ?_
    have h₁ := LinearMap.congr_fun hv w
    have h₂ := LinearMap.congr_fun hv' w
    simp only [bilinFormAt_apply, SmoothBundleForm.eval₂_apply, Submodule.coe_sub,
      Submodule.coe_smul, Pi.sub_apply, Pi.smul_apply, ContinuousAlternatingMap.sub_apply,
      ContinuousAlternatingMap.smul_apply, LinearMap.zero_apply, smul_eq_mul] at h₁ h₂ ⊢
    rw [h₁, h₂, mul_zero, sub_zero]
  -- Both kernels are lines spanned by Reeb vectors of `α_x`, and the two Reeb vectors agree.
  rw [mpullback_prodMk_stableHamiltonianModel,
    hc'.ker_eq_span_reebVector (isAlt_bilinFormAt _ x),
    hc.ker_eq_span_reebVector (isAlt_bilinFormAt _ x)]
  congr 2
  refine ((hc'.eq_reebVector_iff_of_isAlt (isAlt_bilinFormAt _ x)).2
    ⟨hc.apply_reebVector, ?_⟩).symm
  exact LinearMap.mem_ker.1 (hle (hc.reebVector_mem_ker (isAlt_bilinFormAt _ x)))

end IsStableHamiltonian

end Model

end SmoothForm

end TauCeti
