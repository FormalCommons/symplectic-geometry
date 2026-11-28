/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
public import TauCeti.Geometry.Contact.Jacobi.LieAlgebra
public import TauCeti.Geometry.Contact.Flow
public import TauCeti.Geometry.Contact.Hamiltonian.Naturality
public import TauCeti.Geometry.Contact.Rescale
public import TauCeti.Geometry.Contact.VectorField.Flow
public import TauCeti.Geometry.Manifold.VectorBundle.Bilinear.SmulRight
public import TauCeti.Geometry.Manifold.VectorBundle.Hom.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Scalar
public import TauCeti.Geometry.Manifold.VectorBundle.Translate
public import TauCeti.Geometry.Manifold.VectorBundle.SectionAlongMap.Regularity
public import TauCeti.Geometry.Manifold.Flow.TimeDependent
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Flow.Family

/-!
# Contact vector fields and their Hamiltonians

For a contact form `α` with Reeb field `R` on a finite-dimensional manifold, Tau Ceti's
`TauCeti.SmoothForm.contactHamiltonianLieEquiv` identifies the smooth functions, with the Jacobi
bracket, with the Lie algebra `TauCeti.preservesDistributionLieSubalgebra I α.kerDistribution` of
contact vector fields, the smooth vector fields preserving `ker α`, by `f ↦ X_f`, with inverse
`X ↦ α(X)`. This file adds:

* a differentiable vector field `X` preserves `ker α` exactly when `L_X α = R(α(X)) α`
  (`TauCeti.SmoothForm.IsContactForm.preservesDistribution_kerDistribution_iff_mlieDerivForm_eq`);
* on a boundaryless Hausdorff manifold, a `C³` field `X` preserves `ker α` exactly when its local
  flow carries each hyperplane `ker α_x` to the hyperplane at the image point, in the sense that
  the pulled back form `φ_t^* α` has kernel `ker α_x` at `x` wherever the flow is defined
  (`IsContactForm.preservesDistribution_kerDistribution_iff_ker_mpullback_flowOf`, in
  `TauCeti.SmoothForm`);
* for a nowhere vanishing `C¹` function `f`, the form `f⁻¹ α` is again contact and its Reeb
  field is `X_f`
  (`TauCeti.SmoothForm.IsContactForm.reebVectorField_eq_contactHamiltonianVectorField_of_eq_smul`);
  the identity map carries the coorientation of `α` to that of `f⁻¹ α` exactly when `f` is
  positive (`Diffeomorph.preservesCoorientation_refl_iff_pos`, for any nowhere vanishing
  one-form `α`);
* for a family `f : N → M → ℝ` that is jointly `C^(n+1)`, the fields `(p, x) ↦ X_{f_p}(x)` are
  jointly `C^n`
  (`TauCeti.SmoothForm.IsContactForm.contMDiff_contactHamiltonianVectorField_uncurry`);
* on a boundaryless Hausdorff manifold, the time-dependent flow `φ_{s,t}` of the contact
  Hamiltonian vector fields of a jointly `C³` time-dependent function `f_t` rescales the form:
  `(φ_{s,t}^* α)ₓ = exp (∫ₛᵗ (R f_u)(φ_{s,u} x) du) • αₓ` wherever the flow is defined
  (`TauCeti.SmoothForm.IsContactForm.mpullback_timeDependentFlowOf_apply_eq_exp_integral_smul`).

The theorem `TauCeti.SmoothForm.IsContactForm.contactVectorFields_correspondence` collects these
statements.

The file extends Tau Ceti's file of the same path, in its namespace. The multiplier of a contact
vector field comes from Tau Ceti's
`TauCeti.SmoothForm.IsContactForm.preservesDistribution_kerDistribution_iff` and
`TauCeti.SmoothForm.IsContactHamiltonianVectorField.mlieDerivForm_eq`.
The flow characterization states an equality of kernels, which says more than the
inclusion `dφ_t (ker α_x) ⊆ ker α_(φ_t x)` of Tau Ceti's
`TauCeti.SmoothForm.IsContactForm.preservesDistribution_kerDistribution_iff_mfderiv_flowOf`. Its
forward direction uses the rescaling of `α` by the flow
(`TauCeti.SmoothForm.IsContactHamiltonianVectorField.mpullback_flowOf_apply`); its converse
deduces the inclusion from the equality and applies Tau Ceti's
`TauCeti.SmoothForm.preservesDistribution_kerDistribution_of_mfderiv_flowOf_mem`. The Reeb field
of
`f⁻¹ α` is the case `f = id` of Tau Ceti's
`TauCeti.SmoothForm.IsContactForm.mfderiv_contactHamiltonianVectorField_inv`, which needs `f⁻¹ α`
to be contact; this file proves that too, with
`TauCeti.SmoothForm.isContactForm_iff_of_eq_smul`.

The joint regularity of `X_{f_p}` adapts Tau Ceti's
`TauCeti.SmoothForm.IsContactForm.contMDiff_contactHamiltonianVectorField` to a parameter, as
Tau Ceti's `TauCeti.SmoothTwoForm.IsNondegenerate.contMDiff_hamiltonianVectorField_uncurry` does
for symplectic Hamiltonian fields: the inverse contact flat map, composed with the projection
`N × M → M`, applied to `(f + R f) α - df`. The rescaling formula is the time-dependent analogue
of Tau Ceti's `TauCeti.SmoothForm.IsContactHamiltonianVectorField.mpullback_flowOf_apply`. It
applies `TauCeti.mpullback_timeDependentFlowOf_apply_eq_exp_integral_smul_of_mlieDerivForm_eq`
(`Geometry/Manifold/DifferentialForm/Flow/Family.lean`) to `L_{X_{f_u}} α = (R f_u) α`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §3.5
  (Lemma 3.5.14, the discussion of contact vector fields on p. 132, Exercise 3.5.19(i))
* Hansjörg Geiges, *An Introduction to Contact Topology*, Cambridge Studies in Advanced
  Mathematics 109 (2008), Section 2.3.
-/

public section

noncomputable section

open Bundle VectorField
open scoped ContDiff Manifold Topology

namespace TauCeti.SmoothForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable {α : SmoothForm I M ℝ 1}

/-! ### Contact forms -/

namespace IsContactForm

variable [FiniteDimensional ℝ E] (hα : α.IsContactForm)
include hα

/-- **The multiplier of a contact vector field.** For a contact form `α` with Reeb field `R`, a
differentiable vector field `X` preserves the contact structure `ker α` exactly when
`L_X α = R(α(X)) α`. -/
theorem preservesDistribution_kerDistribution_iff_mlieDerivForm_eq
    {X : (x : M) → TangentSpace I x}
    (hXd : MDifferentiable I I.tangent fun y ↦ (⟨y, X y⟩ : TangentBundle I M)) :
    PreservesDistribution I α.kerDistribution X ↔ mlieDerivForm X α.val = fun x ↦
      mvfderiv I (fun y ↦ α.val y ![X y]) x (α.reebVectorField x) • α.val x :=
  (hα.preservesDistribution_kerDistribution_iff hXd).trans
    ⟨fun h ↦ h.mlieDerivForm_eq hXd,
      fun h ↦ (hα.isContactHamiltonianVectorField_iff_mlieDerivForm hXd).2 ⟨fun _ ↦ rfl, _, h⟩⟩

/-- **Contact vector fields preserve the contact hyperplanes.** For a contact form `α` on a
boundaryless Hausdorff manifold, a `C³` vector field `X` preserves the contact structure `ker α`
exactly when, wherever its maximal flow `φ` is defined at time `t` from `x`, the pulled back form
`φ_t^* α` has the same kernel at `x` as `α`. -/
theorem preservesDistribution_kerDistribution_iff_ker_mpullback_flowOf [I.Boundaryless]
    [T2Space M] {X : (x : M) → TangentSpace I x}
    (hX : ContMDiff I I.tangent 3 fun y ↦ (⟨y, X y⟩ : TangentBundle I M)) :
    PreservesDistribution I α.kerDistribution X ↔ ∀ t x, (t, x) ∈ flowDomain X →
      (TauCeti.mpullback I I (flowOf X t) α.val).ker x = α.kerDistribution x := by
  have hXd : MDifferentiable I I.tangent fun y ↦ (⟨y, X y⟩ : TangentBundle I M) :=
    hX.mdifferentiable (by norm_num)
  refine ⟨fun hpres t x hx ↦ ?_, fun h ↦ ?_⟩
  · -- The flow of the contact Hamiltonian field of `α(X)` rescales `α` by a positive factor.
    have hpull := ((hα.preservesDistribution_kerDistribution_iff hXd).1
      hpres).mpullback_flowOf_apply hα (α.contMDiff_apply_vectorField hX) hx
    ext v
    rw [RoughForm.mem_ker, mem_kerDistribution, hpull, ContinuousAlternatingMap.smul_apply,
      smul_eq_mul, mul_eq_zero, or_iff_right (Real.exp_pos _).ne']
  · -- The flow condition gives `dφ_t (ker α_x) ⊆ ker α_(φ_t x)`.
    exact preservesDistribution_kerDistribution_of_mfderiv_flowOf_mem
      (fun x ↦ (isContactForm_iff_forall_isContactFormAt.1 hα x).ne_zero)
      (hX.of_le (by norm_num)) fun t x hx v hv ↦ by
        rw [← h t x hx, RoughForm.mem_ker, TauCeti.mpullback_apply_one] at hv
        exact mem_kerDistribution.2 hv

/-- **Contact Hamiltonian vector fields as Reeb fields.** For a contact form `α` and a nowhere
vanishing `C¹` function `f`, the form `β = f⁻¹ α` is a contact form, and its Reeb field is the
contact Hamiltonian vector field `X_f` of `f` for `α`. -/
theorem reebVectorField_eq_contactHamiltonianVectorField_of_eq_smul {f : M → ℝ}
    {β : SmoothForm I M ℝ 1} (hf : ContMDiff I 𝓘(ℝ) 1 f) (hf₀ : ∀ x, f x ≠ 0)
    (hβ : ∀ x, β.val x = (f x)⁻¹ • α.val x) :
    β.IsContactForm ∧ β.reebVectorField = α.contactHamiltonianVectorField f := by
  have hu : ContMDiff I 𝓘(ℝ) 1 f⁻¹ := fun x ↦ (hf x).inv₀ (hf₀ x)
  have hu₀ : ∀ x, f⁻¹ x ≠ 0 := fun x ↦ inv_ne_zero (hf₀ x)
  have hβc := (isContactForm_iff_of_eq_smul hu hu₀ hβ).2 hα
  refine ⟨hβc, funext fun x ↦ ?_⟩
  -- The identity map pulls `β` back to `f⁻¹ α`, so it carries `X^α_((f⁻¹)⁻¹)` to `R_β`.
  have h := hβc.mfderiv_contactHamiltonianVectorField_inv (β := α) contMDiff_id
    (fun y ↦ by rw [mfderiv_id, ContinuousLinearMap.coe_id']; exact Function.bijective_id) hu hu₀
    (fun y ↦ by rw [coe_mpullback, TauCeti.mpullback_id, Pi.inv_apply]; exact hβ y) x
  rwa [inv_inv, mfderiv_id, ContinuousLinearMap.id_apply, id_eq, eq_comm] at h

/-! ### Time-dependent contact Hamiltonians -/

section Family

variable {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J 1 N]
  {n : WithTop ℕ∞} {f : N → M → ℝ}

/-- For a contact form `α` with Reeb field `R` and a family of functions `f : N → M → ℝ` that is
jointly `C^(n+1)` on `N × M`, the derivatives `(p, x) ↦ (R f_p)(x)` are jointly `C^n`, for
`n ≤ ∞`. -/
theorem contMDiff_mvfderiv_reebVectorField_uncurry (hn : n ≤ ∞)
    (hf : ContMDiff (J.prod I) 𝓘(ℝ) (n + 1) (Function.uncurry f)) :
    ContMDiff (J.prod I) 𝓘(ℝ) n
      fun q : N × M ↦ mvfderiv I (f q.1) q.2 (α.reebVectorField q.2) := fun q ↦
  (hf.contMDiff_totalSpaceMk_mvfderiv_uncurry q).clm_bundle_apply_scalar
    (((hα.contMDiff_reebVectorField q.2).of_le hn).comp q contMDiffAt_snd)

/-- **Joint regularity of contact Hamiltonian vector fields.** For a contact form `α` on a
finite-dimensional manifold and a family of functions `f : N → M → ℝ` that is jointly `C^(n+1)`
on `N × M`, the contact Hamiltonian vector fields `X_{f_p}` form a jointly `C^n` map
`(p, x) ↦ X_{f_p}(x)` from `N × M` to the tangent bundle, for `n ≤ ∞`. For `N = ℝ` this is the
regularity of the time-dependent field of a time-dependent contact Hamiltonian. -/
theorem contMDiff_contactHamiltonianVectorField_uncurry (hn : n ≤ ∞)
    (hf : ContMDiff (J.prod I) 𝓘(ℝ) (n + 1) (Function.uncurry f)) :
    ContMDiff (J.prod I) I.tangent n fun q : N × M ↦
      (⟨q.2, α.contactHamiltonianVectorField (f q.1) q.2⟩ : TangentBundle I M) := by
  intro q
  have hcov := ((((hf q).of_le le_self_add).add
    (hα.contMDiff_mvfderiv_reebVectorField_uncurry hn hf q)).smul_totalSpace
      (((degreeOneEquiv α).contMDiff.of_le hn).comp contMDiff_snd q)).sub_sectionAlong
    (hf.contMDiff_totalSpaceMk_mvfderiv_uncurry q)
  have hX := ((((contMDiff_contactFlat α).clm_bundle_inverse hα.isInvertible_contactFlat).of_le
    hn).comp contMDiff_snd q).clm_bundle_apply hcov
  simpa only [contactHamiltonianVectorField_def, Pi.add_apply, Function.uncurry_def,
    Function.comp_apply] using hX

end Family

/-- **Time-dependent contact Hamiltonian flows rescale the contact form.** Let `α` be a contact
form with Reeb field `R` on a boundaryless Hausdorff manifold, let `f : ℝ → M → ℝ` be a jointly
`C³` time-dependent function, and let `X t` be the contact Hamiltonian vector field of `f t`.
Wherever the time-dependent flow `φ_{s,t}` of `X` from `(s, x)` is defined up to time `t`,
`(φ_{s,t}^* α)ₓ = exp (∫ₛᵗ (R f_u)(φ_{s,u} x) du) • αₓ`. -/
theorem mpullback_timeDependentFlowOf_apply_eq_exp_integral_smul [I.Boundaryless] [T2Space M]
    {f : ℝ → M → ℝ} (hf : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) 3 (Function.uncurry f))
    {X : ℝ → (x : M) → TangentSpace I x}
    (hX : ∀ t, α.IsContactHamiltonianVectorField (f t) (X t)) {s t : ℝ} {x : M}
    (hx : ((s, t), x) ∈ timeDependentFlowDomain X) :
    TauCeti.mpullback I I (timeDependentFlowOf X s t) α.val x =
      Real.exp (∫ u in s..t, mvfderiv I (f u) (timeDependentFlowOf X s u x)
        (α.reebVectorField (timeDependentFlowOf X s u x))) • α.val x := by
  have hXe : X = fun t ↦ α.contactHamiltonianVectorField (f t) :=
    funext fun t ↦ hα.isContactHamiltonianVectorField_iff_eq.1 (hX t)
  have hX2 : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 2
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)) := by
    rw [hXe]
    exact hα.contMDiff_contactHamiltonianVectorField_uncurry (by simp) (by norm_num [hf])
  have hXu (u : ℝ) : MDifferentiable I I.tangent (fun y ↦ (⟨y, X u y⟩ : TangentBundle I M)) :=
    (hX2.comp ((contMDiff_const (c := u)).prodMk contMDiff_id)).mdifferentiable two_ne_zero
  exact mpullback_timeDependentFlowOf_apply_eq_exp_integral_smul_of_mlieDerivForm_eq hX2
    (g := fun p ↦ mvfderiv I (f p.1) p.2 (α.reebVectorField p.2))
    (hα.contMDiff_mvfderiv_reebVectorField_uncurry (J := 𝓘(ℝ, ℝ)) (n := 0) (by simp)
      (hf.of_le (by norm_num))).continuous (fun u ↦ (hX u).mlieDerivForm_eq (hXu u)) hx

end IsContactForm

end TauCeti.SmoothForm

namespace Diffeomorph

open TauCeti TauCeti.SmoothForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Coorientations of rescaled forms.** For a nowhere vanishing one-form `α` and `β = f⁻¹ α`,
the identity map carries the coorientation of `α` to that of `β` exactly when `f` is positive.
No regularity of `f` is needed. -/
theorem preservesCoorientation_refl_iff_pos {α β : SmoothForm I M ℝ 1} {f : M → ℝ}
    (hα : ∀ x, α.val x ≠ 0) (hβ : ∀ x, β.val x = (f x)⁻¹ • α.val x) :
    (Diffeomorph.refl I M ∞).PreservesCoorientation α β ↔ ∀ x, 0 < f x := by
  simp only [Diffeomorph.preservesCoorientation_def, coe_mpullback, Diffeomorph.coe_refl,
    TauCeti.mpullback_id, hβ]
  refine forall_congr' fun x ↦ ⟨fun ⟨c, hc, hx⟩ ↦ ?_, fun hx ↦ ⟨_, inv_pos.2 hx, ?_⟩⟩
  · exact inv_pos.1 (smul_left_injective ℝ (hα x) hx ▸ hc)
  · rfl

end Diffeomorph

namespace TauCeti.SmoothForm.IsContactForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M] {α : SmoothForm I M ℝ 1}

/-- **Contact vector fields and contact Hamiltonians.** Let `α` be a contact form with Reeb field
`R` on a boundaryless Hausdorff manifold of finite dimension, and call a smooth vector field a
contact vector field when it preserves the contact structure `ker α`. Then:

* a smooth vector field `X` is a contact vector field exactly when `L_X α = g α` for some
  function `g : M → ℝ`, exactly when `L_X α = R(α(X)) α`, and exactly when its local flow `φ_t`
  satisfies `ker (φ_t^* α)ₓ = ker αₓ` wherever it is defined;
* the Lie algebra isomorphism `e = TauCeti.SmoothForm.contactHamiltonianLieEquiv` from the smooth
  functions with the Jacobi bracket to the contact vector fields has inverse `X ↦ α(X)`, and
  `e f` is the unique contact Hamiltonian vector field `X_f` of `f`, that is, the unique field
  with `α(X_f) = f` and `ι_{X_f} dα = R(f) α - df`; it satisfies `L_{X_f} α = R(f) α`, and
  `X_1 = R`;
* for a smooth time-dependent function `f`, the time-dependent flow `φ_t` of `X_{f_t}` from time
  `0` satisfies `(φ_t^* α)ₓ = exp (∫₀ᵗ (R f_s)(φ_s x) ds) • αₓ` wherever it is defined;
* `X_f` is transverse to `ker α` at `x` exactly when `f x ≠ 0`; and if `f` vanishes nowhere and
  `β = f⁻¹ α`, then `β` is a contact form with Reeb field `X_f`, and it induces the coorientation
  of `α` exactly when `f` is positive.

Milestone: *Contact vector fields and contact Hamiltonians*. -/
theorem contactVectorFields_correspondence (hα : α.IsContactForm) :
    (∀ X : (LieAlgebroid.tangent I M).Sections,
      X ∈ preservesDistributionLieSubalgebra I α.kerDistribution ↔ ∃ g : M → ℝ,
        mlieDerivForm ((LieAlgebroid.tangent I M).sectionsEquiv X) α.val =
          fun x ↦ g x • α.val x) ∧
    (∀ X : (LieAlgebroid.tangent I M).Sections,
      X ∈ preservesDistributionLieSubalgebra I α.kerDistribution ↔
        mlieDerivForm ((LieAlgebroid.tangent I M).sectionsEquiv X) α.val = fun x ↦
          mvfderiv I (fun y ↦ α.val y ![(LieAlgebroid.tangent I M).sectionsEquiv X y]) x
            (α.reebVectorField x) • α.val x) ∧
    (∀ X : (LieAlgebroid.tangent I M).Sections,
      X ∈ preservesDistributionLieSubalgebra I α.kerDistribution ↔
        ∀ t x, (t, x) ∈ flowDomain ((LieAlgebroid.tangent I M).sectionsEquiv X) →
          (TauCeti.mpullback I I (flowOf ((LieAlgebroid.tangent I M).sectionsEquiv X) t)
            α.val).ker x = α.kerDistribution x) ∧
    (∀ (X : preservesDistributionLieSubalgebra I α.kerDistribution) (x : M),
      α.jacobiLieAlgebraEquiv hα ((α.contactHamiltonianLieEquiv hα).symm X) x =
        α.val x ![(LieAlgebroid.tangent I M).sectionsEquiv
          (X : (LieAlgebroid.tangent I M).Sections) x]) ∧
    (∀ (f : C^∞⟮I, M; ℝ⟯) (X : (x : M) → TangentSpace I x),
      α.IsContactHamiltonianVectorField f X ↔
        X = (LieAlgebroid.tangent I M).sectionsEquiv (α.contactHamiltonianLieEquiv hα
          ((α.jacobiLieAlgebraEquiv hα).symm f) : (LieAlgebroid.tangent I M).Sections)) ∧
    (∀ f : C^∞⟮I, M; ℝ⟯,
      mlieDerivForm ((LieAlgebroid.tangent I M).sectionsEquiv (α.contactHamiltonianLieEquiv hα
          ((α.jacobiLieAlgebraEquiv hα).symm f) : (LieAlgebroid.tangent I M).Sections))
        α.val = fun x ↦ mvfderiv I f x (α.reebVectorField x) • α.val x) ∧
    α.contactHamiltonianVectorField 1 = α.reebVectorField ∧
    (∀ f : ℝ → M → ℝ, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞ (Function.uncurry f) →
      ∀ X : ℝ → (x : M) → TangentSpace I x,
        (∀ t, α.IsContactHamiltonianVectorField (f t) (X t)) →
        ∀ t x, ((0, t), x) ∈ timeDependentFlowDomain X →
          TauCeti.mpullback I I (timeDependentFlowOf X 0 t) α.val x =
            Real.exp (∫ s in 0..t, mvfderiv I (f s) (timeDependentFlowOf X 0 s x)
              (α.reebVectorField (timeDependentFlowOf X 0 s x))) • α.val x) ∧
    (∀ (f : M → ℝ) (x : M),
      α.contactHamiltonianVectorField f x ∉ α.kerDistribution x ↔ f x ≠ 0) ∧
    (∀ (f : C^∞⟮I, M; ℝ⟯) (β : SmoothForm I M ℝ 1), (∀ x, f x ≠ 0) →
      (∀ x, β.val x = (f x)⁻¹ • α.val x) →
        β.IsContactForm ∧ β.reebVectorField = α.contactHamiltonianVectorField f ∧
          ((Diffeomorph.refl I M ∞).PreservesCoorientation α β ↔ ∀ x, 0 < f x)) := by
  -- The contact vector field of `f` under the isomorphism is `X_f`.
  have hXf (f : C^∞⟮I, M; ℝ⟯) : ⇑((LieAlgebroid.tangent I M).sectionsEquiv
      (α.contactHamiltonianLieEquiv hα ((α.jacobiLieAlgebraEquiv hα).symm f) :
        (LieAlgebroid.tangent I M).Sections)) = α.contactHamiltonianVectorField f := by
    funext x
    rw [coe_contactHamiltonianLieEquiv_apply, contactHamiltonianLieHom_apply,
      LinearEquiv.apply_symm_apply]
  refine ⟨fun X ↦ ?_, fun X ↦ (mem_preservesDistributionLieSubalgebra_iff).trans
      (hα.preservesDistribution_kerDistribution_iff_mlieDerivForm_eq
        ((LieAlgebroid.tangent I M).sectionsEquiv X).mdifferentiable),
    fun X ↦ (mem_preservesDistributionLieSubalgebra_iff).trans
      (hα.preservesDistribution_kerDistribution_iff_ker_mpullback_flowOf
        (((LieAlgebroid.tangent I M).sectionsEquiv X).contMDiff.of_le (by simp))),
    jacobiLieAlgebraEquiv_contactHamiltonianLieEquiv_symm_apply hα, fun f X ↦ ?_, fun f ↦ ?_,
    hα.contactHamiltonianVectorField_one,
    fun f hf X hX t x hx ↦ hα.mpullback_timeDependentFlowOf_apply_eq_exp_integral_smul
      (hf.of_le (by simp)) hX hx,
    fun f x ↦ ((hα.isContactHamiltonianVectorField_contactHamiltonianVectorField f
      ).mem_kerDistribution_iff x).not, fun f β hf₀ hβ ↦ ?_⟩
  · rw [mem_preservesDistributionLieSubalgebra_iff,
      hα.preservesDistribution_kerDistribution_iff
        ((LieAlgebroid.tangent I M).sectionsEquiv X).mdifferentiable,
      hα.isContactHamiltonianVectorField_iff_mlieDerivForm
        ((LieAlgebroid.tangent I M).sectionsEquiv X).mdifferentiable]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨fun _ ↦ rfl, h⟩⟩
  · rw [hXf, hα.isContactHamiltonianVectorField_iff_eq]
  · rw [hXf]
    exact (hα.isContactHamiltonianVectorField_contactHamiltonianVectorField f).mlieDerivForm_eq
      (hα.mdifferentiable_contactHamiltonianVectorField (f.contMDiff.of_le (by simp)))
  · obtain ⟨hβc, hR⟩ := hα.reebVectorField_eq_contactHamiltonianVectorField_of_eq_smul
      (f.contMDiff.of_le (by simp)) hf₀ hβ
    exact ⟨hβc, hR, Diffeomorph.preservesCoorientation_refl_iff_pos hα.apply_ne_zero hβ⟩

end TauCeti.SmoothForm.IsContactForm
