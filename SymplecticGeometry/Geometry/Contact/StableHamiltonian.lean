/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Contact.Symplectization.Basic
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Smooth
public import TauCeti.Geometry.Contact.Flat
public import TauCeti.Geometry.Contact.StableHamiltonian
public import TauCeti.Geometry.Contact.Volume
public import TauCeti.Geometry.Manifold.DifferentialForm.Flow
public import SymplecticGeometry.Geometry.Manifold.Strip
public import SymplecticGeometry.Topology.Algebra.Module.Alternating.Basic
import TauCeti.Geometry.Manifold.DifferentialForm.Flow.Family
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Flow.Family
import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Leibniz
import TauCeti.Geometry.Manifold.ContMDiff.Subtype
import TauCeti.Geometry.Manifold.MFDeriv.Prod
import SymplecticGeometry.Geometry.Manifold.MFDeriv.Prod
import TauCeti.Geometry.Manifold.VectorBundle.Bilinear.SmulRight
import TauCeti.Geometry.Manifold.VectorBundle.Hom
import TauCeti.Geometry.Manifold.VectorBundle.Translate
import TauCeti.Geometry.Manifold.VectorBundle.SectionAlongMap.Regularity
import TauCeti.Geometry.Symplectic.Manifold.Opens
import TauCeti.Topology.Algebra.Module.BilinearForm
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.SmoothFamily.Basic
import SymplecticGeometry.Geometry.Manifold.MFDeriv.Prod
import SymplecticGeometry.Geometry.Symplectic.Manifold.Family
import SymplecticGeometry.Geometry.Symplectic.Manifold.Opens
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import TauCeti.Geometry.Symplectic.Manifold.RelativeMoser

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
  pulls `σ` and `α` back to themselves wherever it is defined. On a compact boundaryless
  manifold `R` is complete
  (`TauCeti.SmoothForm.IsStableHamiltonian.isCompleteVectorField_characteristicVectorField`), and
  when `R` is complete each time-`t` map of its flow, as Tau Ceti's diffeomorphism
  `TauCeti.globalFlowDiffeomorph`, pulls `σ` and `α` back to themselves.
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
  that of `σ`. For the contact pair `(α, -dα)` the model is `-d((1 + r) α)`, and where `r > -1`
  it is the pullback of the symplectization form `d(eˢ (-α))` along `(r, x) ↦ (log (1 + r), x)`.
* **The structure on the zero slice of a symplectic strip.** For a two-form `σ` on the strip,
  with slices `σ_r` along `SymplecticGeometry.symmStripMk`, put `Ω₀ = σ_0` and
  `λ₀ = -ι₀^*(ι_{∂_r} σ)` (`TauCeti.SmoothForm.zeroSliceOneForm`). Along `{0} × M`, `σ` equals
  the model of `(λ₀, Ω₀)` on the whole tangent space of `ℝ × M`. If `σ` is symplectic and its
  slices all have the same kernels, `(λ₀, Ω₀)` is a stable Hamiltonian structure: the contact
  condition is the nondegeneracy of `σ` along `{0} × M`, read through the model, and the kernel
  condition follows from Cartan's formula, which makes `d λ₀` a multiple of the `r`-derivative of
  the slices at `0`, and this derivative vanishes on the common kernel.
* **The converse normal form.** For such `σ` on a compact `M`, some strip of width `δ ≤ ε` maps
  into the strip of width `ε` by an injective local diffeomorphism which fixes `{0} × M` and pulls
  `σ` back to the model of `(λ₀, Ω₀)`
  (`TauCeti.SmoothForm.exists_mpullback_eq_stableHamiltonianModel`). Since `σ` and the model
  agree on the whole tangent space along the zero slice, Tau Ceti's Moser theorem near a compact
  submanifold, `TauCeti.SmoothTwoForm.exists_diffeomorph_opens_of_eq_along`, applied along the
  embedding `x ↦ (0, x)`, gives a diffeomorphism between neighbourhoods of `{0} × M`, and the tube
  lemma `SymplecticGeometry.exists_symmStrip_le` a strip inside the first.
* **The milestone**
  (`TauCeti.SmoothForm.IsStableHamiltonian.characteristicVectorField_and_stableHamiltonianModel`)
  collects these results for a stable Hamiltonian structure on a compact boundaryless manifold of
  dimension `2 m + 1`, together with Tau Ceti's characterization of the characteristic field
  (`TauCeti.SmoothForm.eq_characteristicVectorField_iff`).

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
of `eᵗ`. The kernel condition on the zero slice differentiates the slices with Tau Ceti's
`TauCeti.SmoothForm.hasDerivAt_mpullback_prodMk_timeDeriv`, after pulling `σ` back to `ℝ × M`
along `(r, x) ↦ ((2 ε / π) arctan r, x)`.

## Main results

* `TauCeti.SmoothForm.isStableHamiltonian_iff_wedge_wedgePow_apply_ne_zero`
* `TauCeti.SmoothForm.contMDiff_characteristicVectorField`
* `TauCeti.SmoothForm.IsStableHamiltonian.mlieDerivForm_characteristicVectorField_twoForm`,
  `TauCeti.SmoothForm.IsStableHamiltonian.mlieDerivForm_characteristicVectorField_oneForm`
* `TauCeti.SmoothForm.IsStableHamiltonian.mpullback_flowOf_characteristicVectorField_twoForm`,
  `TauCeti.SmoothForm.IsStableHamiltonian.mpullback_flowOf_characteristicVectorField_oneForm`
* `TauCeti.SmoothForm.IsStableHamiltonian.isCompleteVectorField_characteristicVectorField`
* in the namespace `TauCeti.SmoothForm.IsStableHamiltonian`:
  `mpullback_globalFlowDiffeomorph_characteristicVectorField_twoForm`,
  `mpullback_globalFlowDiffeomorph_characteristicVectorField_oneForm`
* `TauCeti.SmoothForm.IsContactForm.isStableHamiltonian_neg`,
  `TauCeti.SmoothForm.characteristicVectorField_neg_mextDerivₗ`
* `TauCeti.SmoothForm.stableHamiltonianModel_apply`,
  `TauCeti.SmoothForm.mpullback_prodMk_stableHamiltonianModel`,
  `TauCeti.SmoothForm.nondegenerate_bilinFormAt_stableHamiltonianModel_iff`
* `TauCeti.SmoothForm.IsStableHamiltonian.nondegenerate_bilinFormAt_stableHamiltonianModel_zero`,
  `TauCeti.SmoothForm.IsStableHamiltonian.exists_isSymplectic_stableHamiltonianModel`,
  `TauCeti.SmoothForm.IsStableHamiltonian.ker_mpullback_prodMk_stableHamiltonianModel`
* `TauCeti.SmoothForm.val_symmStripMk_zero_eq_stableHamiltonianModel`,
  `TauCeti.SmoothForm.isStableHamiltonian_zeroSliceOneForm`
* `TauCeti.SmoothForm.exists_mpullback_eq_stableHamiltonianModel`
* `TauCeti.SmoothForm.stableHamiltonianModel_neg_mextDerivₗ`,
  `TauCeti.SmoothForm.mpullback_subtypeVal_stableHamiltonianModel_neg_mextDerivₗ`
* `TauCeti.SmoothForm.IsStableHamiltonian.characteristicVectorField_and_stableHamiltonianModel`

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
theorem isContact_iff_wedge_wedgePow_apply_ne_zero {m : ℕ}
    (hm : finrank ℝ E = 2 * m + 1) (α : SmoothForm I M ℝ 1) (σ : SmoothForm I M ℝ 2) (x : M) :
    Module.Dual.IsContact (degreeOneEquiv α x : TangentSpace I x →ₗ[ℝ] ℝ) (σ.bilinFormAt x) ↔
      (wedge α (σ.wedgePow m)).val x ≠ 0 := by
  have : FiniteDimensional ℝ E := Module.finite_of_finrank_eq_succ hm
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
theorem isStableHamiltonian_iff_wedge_wedgePow_apply_ne_zero {m : ℕ}
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
      -- The fibrewise additive structure, given directly: searching for it times out once the
      -- relative Moser theorem is imported.
      let : ∀ x : M, AddCommMonoid (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
        fun _ ↦ ContinuousLinearMap.addCommMonoid
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
  refine ContinuousAlternatingMap.ext_fin_one fun w ↦ ?_
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

/-- On a compact boundaryless manifold, the characteristic vector field of a stable Hamiltonian
structure is complete. -/
theorem isCompleteVectorField_characteristicVectorField [CompactSpace M] :
    IsCompleteVectorField (α.characteristicVectorField σ) :=
  isCompleteVectorField_of_compactSpace
    ((contMDiff_characteristicVectorField h.isContact).of_le (by simp))

/-- **The global flow of the characteristic vector field preserves the two-form.** If the
characteristic vector field of a stable Hamiltonian structure `(α, σ)` is complete, the
diffeomorphism `φₜ` given by its flow at any time `t` satisfies `φₜ^* σ = σ`. -/
theorem mpullback_globalFlowDiffeomorph_characteristicVectorField_twoForm
    (hc : IsCompleteVectorField (α.characteristicVectorField σ)) (t : ℝ) :
    mpullback (globalFlowDiffeomorph hc le_top (contMDiff_characteristicVectorField h.isContact) t)
      (globalFlowDiffeomorph hc le_top
        (contMDiff_characteristicVectorField h.isContact) t).contMDiff σ = σ := by
  refine Subtype.ext (funext fun x ↦ ?_)
  rw [coe_mpullback, coe_globalFlowDiffeomorph, ← flowOf_eq_globalFlow]
  exact h.mpullback_flowOf_characteristicVectorField_twoForm (hc.mem_flowDomain t x)

/-- **The global flow of the characteristic vector field preserves the one-form.** If the
characteristic vector field of a stable Hamiltonian structure `(α, σ)` is complete, the
diffeomorphism `φₜ` given by its flow at any time `t` satisfies `φₜ^* α = α`. -/
theorem mpullback_globalFlowDiffeomorph_characteristicVectorField_oneForm
    (hc : IsCompleteVectorField (α.characteristicVectorField σ)) (t : ℝ) :
    mpullback (globalFlowDiffeomorph hc le_top (contMDiff_characteristicVectorField h.isContact) t)
      (globalFlowDiffeomorph hc le_top
        (contMDiff_characteristicVectorField h.isContact) t).contMDiff α = α := by
  refine Subtype.ext (funext fun x ↦ ?_)
  rw [coe_mpullback, coe_globalFlowDiffeomorph, ← flowOf_eq_globalFlow]
  exact h.mpullback_flowOf_characteristicVectorField_oneForm (hc.mem_flowDomain t x)

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
      (funSMulₗ (ContMDiffMap.fst : C^∞⟮𝓘(ℝ).prod I, ℝ × M; ℝ⟯)
        (mpullback Prod.snd contMDiff_snd α))

/-- The stable Hamiltonian model is `σ - d(r α)`, with `σ` and `α` pulled back along the
projection to `M` and `r` the real coordinate. -/
theorem stableHamiltonianModel_def (α : SmoothForm I M ℝ 1) (σ : SmoothForm I M ℝ 2) :
    stableHamiltonianModel α σ =
      mpullback Prod.snd contMDiff_snd σ -
        mextDerivₗ (𝓘(ℝ).prod I) 1
          (funSMulₗ (ContMDiffMap.fst : C^∞⟮𝓘(ℝ).prod I, ℝ × M; ℝ⟯)
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
  set g : C^∞⟮𝓘(ℝ).prod I, ℝ × M; ℝ⟯ := ContMDiffMap.fst
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
  simp only [g, ContMDiffMap.fst_apply]
  ring

/-- **The slices of the stable Hamiltonian model.** The pullback of the model along
`x ↦ (r, x)` is `σ - r dα`. -/
@[simp]
theorem mpullback_prodMk_stableHamiltonianModel (α : SmoothForm I M ℝ 1)
    (σ : SmoothForm I M ℝ 2) (r : ℝ) :
    mpullback (Prod.mk r) (contMDiff_const.prodMk contMDiff_id) (stableHamiltonianModel α σ) =
      σ - r • mextDerivₗ I 1 α := by
  set g : C^∞⟮𝓘(ℝ).prod I, ℝ × M; ℝ⟯ := ContMDiffMap.fst
  have hsmul : mpullback (Prod.mk r) (contMDiff_const.prodMk contMDiff_id)
      (funSMulₗ g (mpullback Prod.snd contMDiff_snd α)) = r • α := by
    -- Both sides send `x` to `r`.
    have hg : g.comp ⟨Prod.mk r, contMDiff_const.prodMk contMDiff_id⟩ = ContMDiffMap.const r := by
      ext
      simp [g]
    rw [mpullback_funSMulₗ, mpullback_prodMk_mpullback_snd, hg, funSMulₗ_const]
  rw [stableHamiltonianModel_def, map_sub, mpullback_prodMk_mpullback_snd, ← mextDerivₗ_mpullback,
    hsmul, map_smul]

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
theorem nondegenerate_bilinFormAt_stableHamiltonianModel_zero (x : M) :
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
    (U := ⟨_,
      SmoothTwoForm.isOpen_setOfPred_nondegenerate_bilinFormAt (stableHamiltonianModel α σ)⟩)
    h.nondegenerate_bilinFormAt_stableHamiltonianModel_zero
  exact ⟨ε, hε, (isClosed_stableHamiltonianModel h.isClosed).isSymplectic_mpullback_subtype_val
    fun _ hp ↦ hle hp⟩

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
    rw [LinearMap.mem_ker, bilinFormAt_sub, bilinFormAt_smul, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.mem_ker.1 hv, LinearMap.mem_ker.1 (h.ker_le_ker x hv),
      smul_zero, sub_zero]
  -- Both kernels are lines spanned by Reeb vectors of `α_x`, and the two Reeb vectors agree.
  rw [mpullback_prodMk_stableHamiltonianModel,
    hc'.ker_eq_span_reebVector (isAlt_bilinFormAt _ x),
    hc.ker_eq_span_reebVector (isAlt_bilinFormAt _ x)]
  congr 2
  refine ((hc'.eq_reebVector_iff_of_isAlt (isAlt_bilinFormAt _ x)).2
    ⟨hc.apply_reebVector, ?_⟩).symm
  exact LinearMap.mem_ker.1 (hle (hc.reebVector_mem_ker (isAlt_bilinFormAt _ x)))

end IsStableHamiltonian

/-- **The model of the contact pair.** For a one-form `α`, the stable Hamiltonian model of
`(α, -dα)` is `-d((1 + r) α)` on `ℝ × M`, with `α` pulled back along the projection to `M` and
`r` the real coordinate. -/
theorem stableHamiltonianModel_neg_mextDerivₗ (α : SmoothForm I M ℝ 1) :
    stableHamiltonianModel α (-mextDerivₗ I 1 α) =
      -mextDerivₗ (𝓘(ℝ).prod I) 1
        (funSMulₗ (1 + ContMDiffMap.fst) (mpullback Prod.snd contMDiff_snd α)) := by
  rw [stableHamiltonianModel_def, map_neg, ← mextDerivₗ_mpullback, funSMulₗ_add,
    funSMulₗ_one, map_add, neg_add, sub_eq_add_neg]

/-- **The model of the contact pair is a symplectization form.** On an open set `U` of `ℝ × M`
where `r > -1`, the stable Hamiltonian model of `(α, -dα)` is the pullback of the exterior
derivative `d(eˢ (-α))` of the symplectization form of `-α` (McDuff–Salamon's `-d(eˢ α)`) along
`(r, x) ↦ (log (1 + r), x)`. -/
theorem mpullback_subtypeVal_stableHamiltonianModel_neg_mextDerivₗ (α : SmoothForm I M ℝ 1)
    {U : TopologicalSpace.Opens (ℝ × M)} (hU : ∀ p ∈ U, -1 < p.1) :
    mpullback (Subtype.val : U → ℝ × M) contMDiff_subtypeVal
        (stableHamiltonianModel α (-mextDerivₗ I 1 α)) =
      mpullback (fun p : U ↦ (Real.log (1 + p.val.1), p.val.2))
        ((((contMDiff_const.add contMDiff_fst).comp contMDiff_subtypeVal).log
          fun p ↦ (by linarith [hU p.val p.property] : (0 : ℝ) < 1 + p.val.1).ne').prodMk
          (contMDiff_snd.comp contMDiff_subtypeVal))
        (mextDerivₗ (𝓘(ℝ).prod I) 1 (-α).symplectization) := by
  rw [stableHamiltonianModel_neg_mextDerivₗ, map_neg, ← mextDerivₗ_mpullback,
    ← mextDerivₗ_mpullback, ← map_neg]
  congr 1
  have hΨ : ContMDiff (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) ∞
      (fun p : U ↦ (Real.log (1 + p.val.1), p.val.2)) :=
    (((contMDiff_const.add contMDiff_fst).comp contMDiff_subtypeVal).log
      fun p ↦ (by linarith [hU p.val p.property] : (0 : ℝ) < 1 + p.val.1).ne').prodMk
      (contMDiff_snd.comp contMDiff_subtypeVal)
  -- The map covers `Subtype.val` on the factor `M`, so it pulls `-α` back as `Subtype.val` does.
  have hβ : mpullback _ hΨ (mpullback Prod.snd contMDiff_snd (-α)) =
      -mpullback Subtype.val contMDiff_subtypeVal (mpullback Prod.snd contMDiff_snd α) := by
    rw [mpullback_mpullback_of_comp_eq hΨ contMDiff_snd contMDiff_subtypeVal contMDiff_snd rfl,
      map_neg, map_neg]
  -- The pullback of `eˢ (-α)` is `-(1 + r) α`, since `exp (log (1 + r)) = 1 + r`.
  set e : C^∞⟮𝓘(ℝ).prod I, ℝ × M; ℝ⟯ :=
    ⟨fun p ↦ Real.exp p.1, Real.contDiff_exp.contMDiff.comp contMDiff_fst⟩ with he
  have he_apply : ∀ p, e p = Real.exp p.1 := fun p ↦ by rw [he, ContMDiffMap.coeFn_mk]
  have hcomp : e.comp ⟨_, hΨ⟩ =
      (1 + ContMDiffMap.fst : C^∞⟮𝓘(ℝ).prod I, ℝ × M; ℝ⟯).comp
        ⟨Subtype.val, contMDiff_subtypeVal⟩ := by
    ext p
    simp [he_apply, Real.exp_log (by linarith [hU p.val p.property] : (0 : ℝ) < 1 + p.val.1)]
  rw [symplectization_eq_funSMulₗ (-α) he_apply,
    mpullback_funSMulₗ, mpullback_funSMulₗ, hβ, map_neg, hcomp]

end Model

section Converse

/-! ### The structure on the zero slice of a symplectic strip -/

open SymplecticGeometry

variable {ε : ℝ}

/-
The proof of the kernel condition reads the strip through the smooth map
`(r, x) ↦ (c r, x)` from `ℝ × M` onto it, with `c r = (2 ε / π) arctan r`, so that Tau Ceti's
`TauCeti.SmoothForm.hasDerivAt_mpullback_prodMk_timeDeriv`, which differentiates the slices of a
form on `ℝ × M`, applies to the pullback `β` of `σ`. Since `c'(0) ≠ 0`, the slice at `0` of
`ι_{∂_t} β` is a nonzero multiple of `λ₀`.
-/

/-- The reparametrization `c r = (2 ε / π) arctan r` of `(-ε, ε)` by `ℝ`. -/
private def stripReparam (ε r : ℝ) : ℝ := 2 * ε / Real.pi * Real.arctan r

private theorem abs_stripReparam_lt (hε : 0 < ε) (r : ℝ) : |stripReparam ε r| < ε := by
  have h1 := Real.neg_pi_div_two_lt_arctan r
  have h2 := Real.arctan_lt_pi_div_two r
  have hπ := Real.pi_pos
  rw [stripReparam, abs_lt]
  constructor
  · have : 2 * ε / Real.pi * (-(Real.pi / 2)) < 2 * ε / Real.pi * Real.arctan r :=
      mul_lt_mul_of_pos_left h1 (by positivity)
    field_simp at this ⊢
    linarith
  · have : 2 * ε / Real.pi * Real.arctan r < 2 * ε / Real.pi * (Real.pi / 2) :=
      mul_lt_mul_of_pos_left h2 (by positivity)
    field_simp at this ⊢
    linarith

private theorem contDiff_stripReparam : ContDiff ℝ ∞ (stripReparam ε) :=
  contDiff_const.mul Real.contDiff_arctan

private theorem hasDerivAt_stripReparam : HasDerivAt (stripReparam ε) (2 * ε / Real.pi) 0 := by
  have h := (Real.hasDerivAt_arctan (0 : ℝ)).const_mul (2 * ε / Real.pi)
  unfold stripReparam
  simpa using h

private theorem stripReparam_zero : stripReparam ε 0 = 0 := by simp [stripReparam]

/-- The map `(r, x) ↦ (c r, x)` from `ℝ × M` to the strip. -/
private def stripChart (hε : 0 < ε) (p : ℝ × M) : symmStrip M ε :=
  symmStripMk (abs_stripReparam_lt hε p.1) p.2

private theorem val_comp_stripChart (hε : 0 < ε) :
    Subtype.val ∘ stripChart (M := M) hε = Prod.map (stripReparam ε) id := by
  funext p
  simp [stripChart, Prod.map]

private theorem contMDiff_stripChart (hε : 0 < ε) :
    ContMDiff (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) ∞ (stripChart (M := M) hε) := by
  rw [← TauCeti.ContMDiff.subtypeVal_comp_iff, val_comp_stripChart]
  exact contDiff_stripReparam.contMDiff.prodMap contMDiff_id

private theorem stripChart_comp_prodMk (hε : 0 < ε) (r : ℝ) :
    stripChart (M := M) hε ∘ Prod.mk r = symmStripMk (abs_stripReparam_lt hε r) := rfl

private theorem stripChart_zero (hε : 0 < ε) (y : M) :
    stripChart hε ((0 : ℝ), y) = symmStripMk (abs_zero.trans_lt hε) y :=
  Subtype.ext (by simp [stripChart, stripReparam_zero])

private theorem mfderiv_stripChart_apply (hε : 0 < ε) (y : M) (s : ℝ) (w : TangentSpace I y) :
    mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (stripChart hε) ((0 : ℝ), y)
      ((s, w) : TangentSpace (𝓘(ℝ).prod I) ((0 : ℝ), y)) =
      (2 * ε / Real.pi * s, w) := by
  refine (TauCeti.Manifold.mfderiv_subtype_val_comp_apply (U := symmStrip M ε)
    (f := stripChart hε) (I := 𝓘(ℝ).prod I) (J := 𝓘(ℝ).prod I) _).symm.trans ?_
  rw [val_comp_stripChart]
  have h := TauCeti.Manifold.mfderiv_prodMap_apply (I := 𝓘(ℝ)) (J := I) (I' := 𝓘(ℝ)) (J' := I)
    (p := ((0 : ℝ), y))
    (contDiff_stripReparam.contMDiff.mdifferentiableAt (by simp) : MDifferentiableAt 𝓘(ℝ) 𝓘(ℝ)
      (stripReparam ε) 0) mdifferentiableAt_id (s, w)
  rw [Manifold.tangentSpaceProdEquiv_symm_apply, Manifold.tangentSpaceProdEquiv_symm_apply] at h
  refine h.trans ?_
  rw [mfderiv_id, mfderiv_eq_fderiv, hasDerivAt_stripReparam.hasFDerivAt.fderiv]
  refine Prod.ext ?_ rfl
  -- The tangent spaces of `ℝ` are `ℝ`, and the casts between them are the identity.
  change s • (2 * ε / Real.pi) = _
  rw [smul_eq_mul, mul_comm]

variable [IsManifold I ∞ M]

private theorem mpullback_prodMk_zero_timeInterior_apply (hε : 0 < ε)
    (σ : SmoothTwoForm (𝓘(ℝ).prod I) (symmStrip M ε)) (y : M) (w : TangentSpace I y) :
    (mpullback (Prod.mk 0) (contMDiff_const.prodMk contMDiff_id)
      (mpullback (stripChart hε) (contMDiff_stripChart hε) σ).timeInterior).val y ![w] =
      2 * ε / Real.pi * σ.bilinFormAt (symmStripMk (abs_zero.trans_lt hε) y)
        ((1 : ℝ), (0 : E)) ((0 : ℝ), w) := by
  rw [mpullback_apply_one, coe_timeInterior]
  refine (RoughForm.interior_apply _ _ _ _).trans ?_
  have h₁ : mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (stripChart hε) ((0 : ℝ), y)
      ((1 : ℝ), (0 : E)) = (2 * ε / Real.pi) • ((1 : ℝ), (0 : E)) := by
    rw [Prod.smul_mk, smul_eq_mul, smul_zero]
    -- The closing `rfl` identifies a tangent vector of the strip with an element of `ℝ × E`.
    exact (mfderiv_stripChart_apply hε y 1 0).trans (by rw [mul_one]; rfl)
  have h₂ : mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (stripChart hε) ((0 : ℝ), y)
      (mfderiv I (𝓘(ℝ).prod I) (Prod.mk (0 : ℝ)) y w) = ((0 : ℝ), w) := by
    rw [mfderiv_prodMk_right_apply]
    exact (mfderiv_stripChart_apply hε y 0 w).trans (by rw [mul_zero])
  -- `(1, 0)` is a vector of `ℝ × E` rather than of a tangent space, so the evaluation lemma is
  -- applied by unification rather than by `rw`.
  rw [coe_mpullback]
  refine (TauCeti.mpullback_apply_pair _ _ _ ((1 : ℝ), (0 : E)) _).trans ?_
  rw [h₁, h₂, stripChart_zero]
  have h := (σ.bilinFormAt_apply (symmStripMk (abs_zero.trans_lt hε) y)
    ((2 * ε / Real.pi) • ((1 : ℝ), (0 : E))) ((0 : ℝ), w)).trans
    (SmoothBundleForm.eval₂_apply _ _ _ _)
  refine h.symm.trans ?_
  exact LinearMap.map_smul₂ _ _ _ _

/-- For a two-form `σ` on the strip `(-ε, ε) × M`, the one-form `λ₀ = -ι₀^*(ι_{∂_r} σ)` on `M`:
minus the slice at `0` of the contraction of `σ` with `∂_r = (1, 0)`, where `ι₀ : x ↦ (0, x)`. -/
def zeroSliceOneForm (hε : 0 < ε) (σ : SmoothTwoForm (𝓘(ℝ).prod I) (symmStrip M ε)) :
    SmoothForm I M ℝ 1 :=
  (-(2 * ε / Real.pi)⁻¹) •
    mpullback (Prod.mk 0) (contMDiff_const.prodMk contMDiff_id)
      (mpullback (stripChart hε) (contMDiff_stripChart hε) σ).timeInterior

/-- The value of `λ₀` at `x` on `w` is `-σ_(0, x)(∂_r, (0, w))`. -/
theorem zeroSliceOneForm_apply (hε : 0 < ε) (σ : SmoothTwoForm (𝓘(ℝ).prod I) (symmStrip M ε))
    (x : M) (w : TangentSpace I x) :
    (zeroSliceOneForm hε σ).val x ![w] =
      -σ.bilinFormAt (symmStripMk (abs_zero.trans_lt hε) x) ((1 : ℝ), (0 : E)) ((0 : ℝ), w) := by
  rw [zeroSliceOneForm, smul_toRoughForm]
  rw [Pi.smul_apply, ContinuousAlternatingMap.smul_apply,
    mpullback_prodMk_zero_timeInterior_apply, smul_eq_mul, ← mul_assoc, neg_mul,
    inv_mul_cancel₀ (by positivity), neg_one_mul]

/-- `λ₀` is `-ι₀^*(ι_{∂_r} σ)`, with `ι₀ : x ↦ (0, x)` and `∂_r = (1, 0)`. -/
theorem coe_zeroSliceOneForm (hε : 0 < ε) (σ : SmoothTwoForm (𝓘(ℝ).prod I) (symmStrip M ε)) :
    (zeroSliceOneForm hε σ).val =
      -TauCeti.mpullback I (𝓘(ℝ).prod I) (symmStripMk (abs_zero.trans_lt hε))
        (RoughForm.interior (fun _ ↦ ((1 : ℝ), (0 : E))) σ.val) := by
  funext x
  refine ContinuousAlternatingMap.ext_fin_one fun w ↦ ?_
  rw [zeroSliceOneForm_apply, Pi.neg_apply, ContinuousAlternatingMap.neg_apply,
    TauCeti.mpullback_apply_one]
  refine congrArg Neg.neg (((σ.bilinFormAt_apply _ _ _).trans
    (SmoothBundleForm.eval₂_apply _ _ _ _)).trans
      (Eq.trans ?_ (RoughForm.interior_apply _ _ _ _).symm))
  rw [mfderiv_symmStripMk_apply]
  -- The two sides list the same vectors, once as elements of `ℝ × E` and once as tangent vectors.
  rfl

/-- **Along the zero slice, a two-form on the strip agrees with the stable Hamiltonian model** of
its zero slice `Ω₀` and of `λ₀ = -ι₀^*(ι_{∂_r} σ)`: at every point `(0, x)`, on the whole tangent
space of `ℝ × M`. -/
theorem val_symmStripMk_zero_eq_stableHamiltonianModel (hε : 0 < ε)
    (σ : SmoothTwoForm (𝓘(ℝ).prod I) (symmStrip M ε)) (x : M) :
    σ.val (symmStripMk (abs_zero.trans_lt hε) x) =
      (mpullback Subtype.val contMDiff_subtypeVal (stableHamiltonianModel (zeroSliceOneForm hε σ)
        (mpullback (symmStripMk (abs_zero.trans_lt hε)) (contMDiff_symmStripMk _) σ))).val
        (symmStripMk (abs_zero.trans_lt hε) x) := by
  set z := symmStripMk (abs_zero.trans_lt hε) x
  rw [coe_mpullback_subtype_val_apply]
  refine ContinuousAlternatingMap.ext_fin_two fun a b ↦ ?_
  set B : LinearMap.BilinForm ℝ (ℝ × E) := σ.bilinFormAt z
  have halt : B.IsAlt := isAlt_bilinFormAt σ z
  have hsplit (c : ℝ × E) : c = c.1 • ((1 : ℝ), (0 : E)) + ((0 : ℝ), c.2) :=
    Prod.ext (by simp) (by simp)
  have hL : σ.val z ![a, b] = B ((0 : ℝ), a.2) ((0 : ℝ), b.2) +
      a.1 * B ((1 : ℝ), (0 : E)) ((0 : ℝ), b.2) - b.1 * B ((1 : ℝ), (0 : E)) ((0 : ℝ), a.2) := by
    have h : σ.val z ![a, b] = B a b :=
      ((σ.bilinFormAt_apply _ _ _).trans (SmoothBundleForm.eval₂_apply _ _ _ _)).symm
    rw [h]
    conv_lhs => rw [hsplit a, hsplit b]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      halt.self_eq_zero, ← halt.neg_eq ((1 : ℝ), (0 : E)) ((0 : ℝ), a.2)]
    ring
  rw [hL, coe_symmStripMk]
  refine Eq.trans ?_ (SmoothBundleForm.eval₂_apply (stableHamiltonianModel (zeroSliceOneForm hε σ)
    (mpullback (symmStripMk (abs_zero.trans_lt hε)) (contMDiff_symmStripMk _) σ)) ((0 : ℝ), x) a b)
  refine Eq.trans ?_ (stableHamiltonianModel_apply _ _ ((0 : ℝ), x) a b).symm
  simp only [zero_mul, sub_zero, ← bilinFormAt_apply,
    zeroSliceOneForm_apply]
  have ha := Manifold.tangentSpaceProdEquiv_apply (I := 𝓘(ℝ)) (J := I) ((0 : ℝ), x) a
  have hb := Manifold.tangentSpaceProdEquiv_apply (I := 𝓘(ℝ)) (J := I) ((0 : ℝ), x) b
  rw [ha, hb, bilinFormAt_mpullback_symmStripMk, NormedSpace.fromTangentSpace_apply,
    NormedSpace.fromTangentSpace_apply]
  -- Both sides read `σ` at `(0, x)`, with vectors typed in the strip or in `ℝ × M`.
  change _ = B ((0 : ℝ), a.2) ((0 : ℝ), b.2) - (a.1 * -B ((1 : ℝ), (0 : E)) ((0 : ℝ), b.2) -
    b.1 * -B ((1 : ℝ), (0 : E)) ((0 : ℝ), a.2))
  ring

variable [I.Boundaryless]

/-- **The structure on the zero slice.** Let `σ` be a symplectic form on the strip
`(-ε, ε) × M` whose slices `σ_r`, the pullbacks along `x ↦ (r, x)`, have the same kernel at every
point for all `r, r'` in `(-ε, ε)`. Then the zero slice `Ω₀ = σ_0` and the one-form
`λ₀ = -ι₀^*(ι_{∂_r} σ)` form a stable Hamiltonian structure `(λ₀, Ω₀)` on `M`. -/
theorem isStableHamiltonian_zeroSliceOneForm (hε : 0 < ε)
    {σ : SmoothTwoForm (𝓘(ℝ).prod I) (symmStrip M ε)} (hσ : σ.IsSymplectic)
    (hker : ∀ (r : ℝ) (hr : |r| < ε) (r' : ℝ) (hr' : |r'| < ε) (x : M),
      LinearMap.ker ((mpullback (symmStripMk hr) (contMDiff_symmStripMk hr) σ).bilinFormAt x) =
        LinearMap.ker ((mpullback (symmStripMk hr') (contMDiff_symmStripMk hr') σ).bilinFormAt x)) :
    (zeroSliceOneForm hε σ).IsStableHamiltonian
      (mpullback (symmStripMk (abs_zero.trans_lt hε)) (contMDiff_symmStripMk _) σ) where
  isClosed := hσ.isClosed.mpullback _ _
  isContact x := by
    set z := symmStripMk (abs_zero.trans_lt hε) x
    have hval := val_symmStripMk_zero_eq_stableHamiltonianModel hε σ x
    have hB : (mpullback Subtype.val contMDiff_subtypeVal (stableHamiltonianModel
        (zeroSliceOneForm hε σ) (mpullback (symmStripMk (abs_zero.trans_lt hε))
          (contMDiff_symmStripMk _) σ))).bilinFormAt z = σ.bilinFormAt z :=
      LinearMap.ext₂ fun v w ↦ by
        rw [bilinFormAt_apply, bilinFormAt_apply, SmoothBundleForm.eval₂_apply,
          SmoothBundleForm.eval₂_apply, hval]
    have hnd := (SmoothTwoForm.nondegenerate_bilinFormAt_mpullback_subtype_val_iff z).1
      (hB ▸ hσ.isNondegenerate.nondegenerate_bilinFormAt z)
    rw [coe_symmStripMk, nondegenerate_bilinFormAt_stableHamiltonianModel_iff, zero_smul,
      sub_zero] at hnd
    exact hnd
  ker_le_ker x v hv := by
    set β := mpullback (stripChart hε) (contMDiff_stripChart hε) σ
    -- The slices of `β` are those of `σ`, so `v` lies in the kernel of all of them.
    have hslice (u : ℝ) : mpullback (Prod.mk u) (contMDiff_const.prodMk contMDiff_id) β =
        mpullback (symmStripMk (abs_stripReparam_lt hε u)) (contMDiff_symmStripMk _) σ := by
      simp only [β, mpullback_mpullback, stripChart_comp_prodMk]
    have hzero (u : ℝ) (w : TangentSpace I x) :
        (mpullback (Prod.mk u) (contMDiff_const.prodMk contMDiff_id) β).val x ![v, w] = 0 := by
      have hv' : v ∈ LinearMap.ker ((mpullback (symmStripMk (abs_stripReparam_lt hε u))
          (contMDiff_symmStripMk _) σ).bilinFormAt x) := by
        rw [hker _ _ 0 (abs_zero.trans_lt hε) x]
        exact hv
      rw [← SmoothBundleForm.eval₂_apply, ← bilinFormAt_apply, hslice, LinearMap.mem_ker.1 hv',
        LinearMap.zero_apply]
    -- Hence the slice at `0` of the time derivative of `β` vanishes on `v`.
    have hdt (w : TangentSpace I x) :
        (mpullback (Prod.mk 0) (contMDiff_const.prodMk contMDiff_id) β.timeDeriv).val x ![v, w] =
          0 := by
      have h := (ContinuousAlternatingMap.apply ℝ E ℝ ![v, w]).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
        (hasDerivAt_mpullback_prodMk_timeDeriv β 0 x)
      have hfun : (ContinuousAlternatingMap.apply ℝ E ℝ ![v, w] ∘ fun u ↦
          (mpullback (Prod.mk u) (contMDiff_const.prodMk contMDiff_id) β).val x) =
          fun _ ↦ (0 : ℝ) :=
        funext fun u ↦ (ContinuousAlternatingMap.apply_apply).trans (hzero u w)
      rw [hfun] at h
      exact ContinuousAlternatingMap.apply_apply.symm.trans (h.unique (hasDerivAt_const _ _))
    refine LinearMap.mem_ker.2 (LinearMap.ext fun w ↦ ?_)
    rw [zeroSliceOneForm, map_smul, mextDerivₗ_mpullback,
      mextDerivₗ_timeInterior (hσ.isClosed.mpullback _ _), bilinFormAt_smul, LinearMap.smul_apply,
      LinearMap.smul_apply, bilinFormAt_apply, SmoothBundleForm.eval₂_apply, hdt, smul_zero,
      LinearMap.zero_apply]

/-- **The converse of the stable Hamiltonian model.** Let `M` be a compact boundaryless Hausdorff
second-countable manifold, and `σ` a symplectic form on the strip `(-ε, ε) × M` whose slices
`σ_r`, the pullbacks along `x ↦ (r, x)`, have the same kernel at every point for all `r, r'` in
`(-ε, ε)`. Put `Ω₀ = σ_0` and `λ₀ = -ι₀^*(ι_{∂_r} σ)`. Then `(λ₀, Ω₀)` is a stable Hamiltonian
structure, and for some `δ ∈ (0, ε]` there is an injective local diffeomorphism `Φ` from the strip
of width `δ` to the strip of width `ε` which fixes every point `(0, x)` and pulls `σ` back to the
stable Hamiltonian model of `(λ₀, Ω₀)` on the strip of width `δ`. -/
theorem exists_mpullback_eq_stableHamiltonianModel [FiniteDimensional ℝ E] [CompactSpace M]
    [T2Space M] [SecondCountableTopology M] (hε : 0 < ε)
    {σ : SmoothTwoForm (𝓘(ℝ).prod I) (symmStrip M ε)} (hσ : σ.IsSymplectic)
    (hker : ∀ (r : ℝ) (hr : |r| < ε) (r' : ℝ) (hr' : |r'| < ε) (x : M),
      LinearMap.ker ((mpullback (symmStripMk hr) (contMDiff_symmStripMk hr) σ).bilinFormAt x) =
        LinearMap.ker ((mpullback (symmStripMk hr') (contMDiff_symmStripMk hr') σ).bilinFormAt x)) :
    (zeroSliceOneForm hε σ).IsStableHamiltonian
        (mpullback (symmStripMk (abs_zero.trans_lt hε)) (contMDiff_symmStripMk _) σ) ∧
      ∃ δ, ∃ hδ : 0 < δ, δ ≤ ε ∧ ∃ (Φ : symmStrip M δ → symmStrip M ε)
        (hΦ : IsLocalDiffeomorph (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) ∞ Φ), Function.Injective Φ ∧
        (∀ x, Φ (symmStripMk (abs_zero.trans_lt hδ) x) = symmStripMk (abs_zero.trans_lt hε) x) ∧
        mpullback Φ hΦ.contMDiff σ =
          mpullback Subtype.val contMDiff_subtypeVal (stableHamiltonianModel
            (zeroSliceOneForm hε σ)
            (mpullback (symmStripMk (abs_zero.trans_lt hε)) (contMDiff_symmStripMk _) σ)) := by
  have hSH := isStableHamiltonian_zeroSliceOneForm hε hσ hker
  refine ⟨hSH, ?_⟩
  set ι₀ : M → symmStrip M ε := symmStripMk (abs_zero.trans_lt hε)
  set σ₀ := mpullback (Subtype.val : symmStrip M ε → ℝ × M) contMDiff_subtypeVal
    (stableHamiltonianModel (zeroSliceOneForm hε σ) (mpullback ι₀ (contMDiff_symmStripMk _) σ))
  -- Moser's method along the zero slice, where `σ` and the model agree to first order.
  let f : TauCeti.SmoothEmbedding I (𝓘(ℝ).prod I) ∞ M (symmStrip M ε) :=
    .ofIsSmoothEmbedding ι₀ (isSmoothEmbedding_symmStripMk_zero hε)
  have hf (x : M) : f x = ι₀ x := TauCeti.SmoothEmbedding.ofIsSmoothEmbedding_apply _ _ x
  obtain ⟨U₀, U₁, φ, hφf, hφ⟩ := SmoothTwoForm.exists_diffeomorph_opens_of_eq_along f
    (σ₀ := σ₀) (σ₁ := σ) ((isClosed_stableHamiltonianModel hSH.isClosed).mpullback _ _)
    hσ.isClosed (fun x ↦ by
      rw [hf]
      refine (SmoothTwoForm.nondegenerate_bilinFormAt_mpullback_subtype_val_iff _).2 ?_
      rw [coe_symmStripMk]
      exact hSH.nondegenerate_bilinFormAt_stableHamiltonianModel_zero x)
    (fun x ↦ by rw [hf]; exact val_symmStripMk_zero_eq_stableHamiltonianModel hε σ x)
  -- The tube lemma gives a strip of width `δ ≤ ε` inside `U₀`.
  obtain ⟨δ, hδ, hδU⟩ := exists_symmStrip_le (X := M)
    (U := ⟨Subtype.val '' (U₀ : Set (symmStrip M ε)),
      (symmStrip M ε).isOpen.isOpenMap_subtypeVal _ U₀.isOpen⟩)
    fun x ↦ ⟨f x, (hφf x).1, by rw [hf, coe_symmStripMk]⟩
  have hle : min δ ε ≤ ε := min_le_right δ ε
  have hU₀ (p : symmStrip M (min δ ε)) :
      (⟨p.val, symmStrip_mono hle p.property⟩ : symmStrip M ε) ∈ U₀ := by
    obtain ⟨q, hq, hqp⟩ := hδU (symmStrip_mono (min_le_left δ ε) p.property)
    rwa [show q = ⟨p.val, symmStrip_mono hle p.property⟩ from Subtype.ext hqp] at hq
  let j (p : symmStrip M (min δ ε)) : U₀ := ⟨⟨p.val, symmStrip_mono hle p.property⟩, hU₀ p⟩
  have hjval : (Subtype.val ∘ Subtype.val) ∘ j = Subtype.val := rfl
  have hjd : IsLocalDiffeomorph (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) ∞ j :=
    TauCeti.isLocalDiffeomorph_subtypeVal_comp_iff.1
      (TauCeti.isLocalDiffeomorph_inclusion (symmStrip_mono hle))
  have hΦ : IsLocalDiffeomorph (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) ∞ ((Subtype.val ∘ φ) ∘ j) := fun p ↦
    (hjd p).comp (hg := (φ.isLocalDiffeomorph (j p)).comp
      (hg := TauCeti.isLocalDiffeomorph_subtype_val _))
  refine ⟨min δ ε, lt_min hδ hε, hle, (Subtype.val ∘ φ) ∘ j, hΦ, ?_, fun x ↦ ?_, ?_⟩
  · exact Subtype.val_injective.comp (φ.injective.comp fun p q h ↦
      Subtype.ext (congrArg (fun u : U₀ ↦ (u.val : ℝ × M)) h))
  · obtain ⟨hx, hφx, -⟩ := hφf x
    have : j (symmStripMk (abs_zero.trans_lt (lt_min hδ hε)) x) = ⟨f x, hx⟩ :=
      Subtype.ext (Subtype.ext (by simp [j, hf, ι₀]))
    rw [Function.comp_apply, Function.comp_apply, this, hφx, hf]
  · rw [← mpullback_mpullback _ _ hjd.contMDiff (contMDiff_subtypeVal.comp φ.contMDiff),
      ← mpullback_mpullback _ _ φ.contMDiff contMDiff_subtypeVal, hφ]
    simp only [σ₀, ι₀, mpullback_mpullback, hjval]

end Converse

section Milestone

/-! ### The milestone -/

open SymplecticGeometry

variable [IsManifold I ∞ M] [I.Boundaryless] [CompactSpace M] [T2Space M]
  [SecondCountableTopology M]

/-- **Stable Hamiltonian structures and their model on a strip.** Let `M` be a compact
boundaryless manifold of dimension `2 m + 1`. Then:

* a pair `(α', σ')` is a stable Hamiltonian structure exactly when `σ'` is closed, `α' ∧ σ' ^ m`
  vanishes nowhere and `ker σ'_x ⊆ ker dα'_x` at every point;
* for the stable Hamiltonian structure `(α, σ)`, the characteristic vector field `R` is at each
  point the unique tangent vector `v` with `α(v) = 1` and `ι_v σ = 0`; it is complete, and its
  flow pulls back both `σ` and `α` to themselves at all times;
* for some `ε > 0`, the model `σ - d(r α)` is symplectic on the strip `(-ε, ε) × M`, and the
  kernel of each of its slices `σ - r dα`, `|r| < ε`, is the kernel of `σ` at every point;
* for a contact form `β`, `(β, -dβ)` is a stable Hamiltonian structure whose characteristic field
  is the Reeb field of `β`; its model is `-d((1 + r) β)`, and on every open set where `r > -1` it
  is the pullback of `d(eˢ (-β))` along `(r, x) ↦ (log (1 + r), x)`;
* conversely, if `σ'` is a symplectic form on a strip `(-ε, ε) × M` whose slices have the same
  kernels, its zero slice `Ω₀` and the one-form `λ₀ = -ι₀^*(ι_{∂_r} σ')` form a stable Hamiltonian
  structure `(λ₀, Ω₀)`, and an injective local diffeomorphism from a strip of width
  `δ ∈ (0, ε]` into the strip of width `ε`, fixing the zero slice pointwise, pulls `σ'` back to
  the model of `(λ₀, Ω₀)`.

McDuff–Salamon's pair `(Ω, λ)` is `IsStableHamiltonian λ Ω`, and their dimension `2 n - 1` is
`2 m + 1` with `n = m + 1`.

Milestone: *Stable Hamiltonian structures and their neighbourhood model*. -/
theorem IsStableHamiltonian.characteristicVectorField_and_stableHamiltonianModel {m : ℕ}
    (hm : finrank ℝ E = 2 * m + 1) {α : SmoothForm I M ℝ 1} {σ : SmoothForm I M ℝ 2}
    (h : α.IsStableHamiltonian σ) :
    (∀ (α' : SmoothForm I M ℝ 1) (σ' : SmoothForm I M ℝ 2), α'.IsStableHamiltonian σ' ↔
      σ'.IsClosed ∧ (∀ x, (wedge α' (σ'.wedgePow m)).val x ≠ 0) ∧
        ∀ x, LinearMap.ker (σ'.bilinFormAt x) ≤
          LinearMap.ker ((mextDerivₗ I 1 α').bilinFormAt x)) ∧
    (∀ (x : M) (v : TangentSpace I x), v = α.characteristicVectorField σ x ↔
      α.val x ![v] = 1 ∧ ∀ w : TangentSpace I x, σ.val x ![v, w] = 0) ∧
    IsCompleteVectorField (α.characteristicVectorField σ) ∧
    (∀ t : ℝ, TauCeti.mpullback I I (flowOf (α.characteristicVectorField σ) t) σ.val = σ.val ∧
      TauCeti.mpullback I I (flowOf (α.characteristicVectorField σ) t) α.val = α.val) ∧
    (∃ ε > 0, SmoothTwoForm.IsSymplectic
        (mpullback (Subtype.val : symmStrip M ε → ℝ × M) contMDiff_subtypeVal
          (stableHamiltonianModel α σ)) ∧
      ∀ r : ℝ, |r| < ε → ∀ x : M,
        LinearMap.ker ((mpullback (Prod.mk r) (contMDiff_const.prodMk contMDiff_id)
          (stableHamiltonianModel α σ)).bilinFormAt x) = LinearMap.ker (σ.bilinFormAt x)) ∧
    (∀ β : SmoothForm I M ℝ 1, β.IsContactForm →
      β.IsStableHamiltonian (-mextDerivₗ I 1 β) ∧
      β.characteristicVectorField (-mextDerivₗ I 1 β) = β.reebVectorField ∧
      stableHamiltonianModel β (-mextDerivₗ I 1 β) =
        -mextDerivₗ (𝓘(ℝ).prod I) 1
          (funSMulₗ (1 + ContMDiffMap.fst) (mpullback Prod.snd contMDiff_snd β)) ∧
      ∀ (U : TopologicalSpace.Opens (ℝ × M)) (hU : ∀ p ∈ U, -1 < p.1),
        mpullback (Subtype.val : U → ℝ × M) contMDiff_subtypeVal
            (stableHamiltonianModel β (-mextDerivₗ I 1 β)) =
          mpullback (fun p : U ↦ (Real.log (1 + p.val.1), p.val.2))
            ((((contMDiff_const.add contMDiff_fst).comp contMDiff_subtypeVal).log
              fun p ↦ (by linarith [hU p.val p.property] : (0 : ℝ) < 1 + p.val.1).ne').prodMk
              (contMDiff_snd.comp contMDiff_subtypeVal))
            (mextDerivₗ (𝓘(ℝ).prod I) 1 (-β).symplectization)) ∧
    ∀ (ε : ℝ) (hε : 0 < ε) (σ' : SmoothTwoForm (𝓘(ℝ).prod I) (symmStrip M ε)),
      σ'.IsSymplectic →
      (∀ (r : ℝ) (hr : |r| < ε) (r' : ℝ) (hr' : |r'| < ε) (x : M),
        LinearMap.ker ((mpullback (symmStripMk hr) (contMDiff_symmStripMk hr) σ').bilinFormAt x) =
          LinearMap.ker
            ((mpullback (symmStripMk hr') (contMDiff_symmStripMk hr') σ').bilinFormAt x)) →
      (zeroSliceOneForm hε σ').IsStableHamiltonian
          (mpullback (symmStripMk (abs_zero.trans_lt hε)) (contMDiff_symmStripMk _) σ') ∧
        ∃ δ, ∃ hδ : 0 < δ, δ ≤ ε ∧ ∃ (Φ : symmStrip M δ → symmStrip M ε)
          (hΦ : IsLocalDiffeomorph (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) ∞ Φ), Function.Injective Φ ∧
          (∀ x, Φ (symmStripMk (abs_zero.trans_lt hδ) x) =
            symmStripMk (abs_zero.trans_lt hε) x) ∧
          mpullback Φ hΦ.contMDiff σ' =
            mpullback Subtype.val contMDiff_subtypeVal (stableHamiltonianModel
              (zeroSliceOneForm hε σ')
              (mpullback (symmStripMk (abs_zero.trans_lt hε)) (contMDiff_symmStripMk _) σ')) := by
  have : FiniteDimensional ℝ E := Module.finite_of_finrank_eq_succ hm
  have hcomplete := h.isCompleteVectorField_characteristicVectorField
  have hR := contMDiff_characteristicVectorField h.isContact
  -- The time-`t` map of the maximal flow is the diffeomorphism given by the global flow.
  have hflow (t : ℝ) : flowOf (α.characteristicVectorField σ) t =
      globalFlowDiffeomorph hcomplete le_top hR t := by
    rw [coe_globalFlowDiffeomorph, ← flowOf_eq_globalFlow]
  obtain ⟨ε, hε, hsymp⟩ := h.exists_isSymplectic_stableHamiltonianModel
  refine ⟨fun _ _ ↦ isStableHamiltonian_iff_wedge_wedgePow_apply_ne_zero hm,
    fun x _ ↦ eq_characteristicVectorField_iff (h.isContact x), hcomplete,
    fun t ↦ ⟨by
        rw [hflow, ← coe_mpullback _ (globalFlowDiffeomorph hcomplete le_top hR t).contMDiff,
          h.mpullback_globalFlowDiffeomorph_characteristicVectorField_twoForm],
      by
        rw [hflow, ← coe_mpullback _ (globalFlowDiffeomorph hcomplete le_top hR t).contMDiff,
          h.mpullback_globalFlowDiffeomorph_characteristicVectorField_oneForm]⟩,
    ⟨ε, hε, hsymp, fun r hr x ↦ h.ker_mpullback_prodMk_stableHamiltonianModel ?_⟩,
    fun β hβ ↦ ⟨hβ.isStableHamiltonian_neg, characteristicVectorField_neg_mextDerivₗ β,
      stableHamiltonianModel_neg_mextDerivₗ β,
      fun _ hU ↦ mpullback_subtypeVal_stableHamiltonianModel_neg_mextDerivₗ β hU⟩,
    fun _ hε' _ hσ' hker ↦ exists_mpullback_eq_stableHamiltonianModel hε' hσ' hker⟩
  -- The model is nondegenerate at `(r, x)`, since its restriction to the strip is.
  exact (SmoothTwoForm.nondegenerate_bilinFormAt_mpullback_subtype_val_iff
    (⟨(r, x), mem_symmStrip_iff.2 hr⟩ : symmStrip M ε)).1
    (hsymp.isNondegenerate.nondegenerate_bilinFormAt _)

end Milestone

end SmoothForm

end TauCeti
