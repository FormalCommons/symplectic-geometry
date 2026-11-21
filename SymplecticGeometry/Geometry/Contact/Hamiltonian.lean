/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
public import TauCeti.Geometry.Contact.Flow
public import TauCeti.Geometry.Contact.Rescale
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.DegreeOne
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.LieDeriv

/-!
# Contact vector fields and their Hamiltonians

For a smooth one-form `α`, the **contact vector fields** `TauCeti.SmoothForm.contactVectorFields`
are the smooth vector fields `X` whose Lie derivative is a pointwise multiple of `α`:
`L_X α = g α` for some function `g : M → ℝ`. They form a submodule of the smooth vector fields.

For a contact form `α` with Reeb field `R` on a finite-dimensional manifold:

* the multiplier is forced to be `g = R(α(X))`
  (`TauCeti.SmoothForm.IsContactForm.mem_contactVectorFields_iff_mlieDerivForm_eq`);
* on a boundaryless Hausdorff manifold, `X` is a contact vector field exactly when its local flow
  carries each hyperplane `ker α_x` to the hyperplane at the image point, in the sense that the
  pulled back form `φ_t^* α` has kernel `ker α_x` at `x` wherever the flow is defined
  (`TauCeti.SmoothForm.IsContactForm.mem_contactVectorFields_iff_kerDistribution_mpullback_flowOf`);
* `X ↦ α(X)` is a linear equivalence from contact vector fields to smooth functions, whose
  inverse sends `f` to its contact Hamiltonian vector field `X_f`
  (`TauCeti.SmoothForm.IsContactForm.contactHamiltonianEquiv`);
* for a nowhere vanishing `C¹` function `f`, the form `f⁻¹ α` is again contact and its Reeb
  field is `X_f`
  (`TauCeti.SmoothForm.IsContactForm.reebVectorField_eq_contactHamiltonianVectorField_of_eq_smul`);
  the identity map carries the coorientation of `α` to that of `f⁻¹ α` exactly when `f` is
  positive (`Diffeomorph.preservesCoorientation_refl_iff_pos`, for any nowhere vanishing
  one-form `α`).

Closure of contact vector fields under sums and scalar multiples uses the linearity of the Lie
derivative in the vector field (`TauCeti.mlieDerivForm_add_left`,
`TauCeti.mlieDerivForm_const_smul_left`, `TauCeti.mlieDerivForm_zero_left`).

The file extends Tau Ceti's file of the same path, in its namespace; the submodule is modelled on
`TauCeti.SmoothTwoForm.symplecticVectorFields`. The converse direction of the flow
characterization adapts the proof of the forward direction of Tau Ceti's
`TauCeti.SmoothForm.IsContactHamiltonianVectorField.mpullback_flowOf_apply_eq_self_iff`:
differentiate the pulled back form at time `0` with `TauCeti.hasDerivAt_mpullback_flowOf_zero`,
on the open set of times where the flow from `x` is defined.

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

/-! ### Contact vector fields -/

/-- The **contact vector fields** of a one-form `α`: the smooth vector fields `X` whose Lie
derivative `L_X α` is a pointwise multiple `g α` of `α`, for some function `g : M → ℝ`. -/
def contactVectorFields (α : SmoothForm I M ℝ 1) :
    Submodule ℝ Cₛ^∞⟮I; E, TangentSpace I (M := M)⟯ where
  carrier := {X | ∃ g : M → ℝ, mlieDerivForm X α.val = fun x ↦ g x • α.val x}
  add_mem' := by
    rintro X Y ⟨g, hg⟩ ⟨h, hh⟩
    refine ⟨g + h, funext fun x ↦ ?_⟩
    have hXd := X.mdifferentiableAt (x := x)
    have hYd := Y.mdifferentiableAt (x := x)
    rw [ContMDiffSection.coe_add, mlieDerivForm_add_left α.val hXd hYd, hg, hh, Pi.add_apply,
      add_smul]
  zero_mem' := ⟨0, by
    rw [ContMDiffSection.coe_zero, mlieDerivForm_zero_left]
    funext x
    simp⟩
  smul_mem' c X := by
    rintro ⟨g, hg⟩
    refine ⟨c • g, ?_⟩
    rw [ContMDiffSection.coe_smul, mlieDerivForm_const_smul_left, hg]
    funext x
    simp [smul_smul]

variable {α : SmoothForm I M ℝ 1}

/-- A smooth vector field is a contact vector field of `α` exactly when `L_X α = g α` for some
function `g`. -/
@[simp]
theorem mem_contactVectorFields_iff {X : Cₛ^∞⟮I; E, TangentSpace I (M := M)⟯} :
    X ∈ α.contactVectorFields ↔ ∃ g : M → ℝ, mlieDerivForm X α.val = fun x ↦ g x • α.val x :=
  Iff.rfl

/-! ### Contact forms -/

namespace IsContactForm

variable [FiniteDimensional ℝ E] (hα : α.IsContactForm)
include hα

/-- A one-form `β` that vanishes on the contact hyperplane `ker α_x` of a contact form is, at
`x`, the multiple `β(R_x) α_x` of `α_x`, where `R` is the Reeb field. -/
theorem apply_eq_apply_reebVectorField_smul_of_kerDistribution_le {β : RoughForm I M ℝ 1}
    {x : M} (hβ : α.kerDistribution x ≤ β.ker x) :
    β x = β x ![α.reebVectorField x] • α.val x := by
  ext v
  obtain ⟨w, rfl⟩ : ∃ w, v = ![w] := ⟨v 0, by ext i; fin_cases i; rfl⟩
  -- Subtract the Reeb component of `w` to land in the contact hyperplane.
  have hw : w - α.val x ![w] • α.reebVectorField x ∈ α.kerDistribution x := by
    rw [mem_kerDistribution, ← degreeOneEquiv_apply_apply_vec, map_sub, map_smul]
    simp [degreeOneEquiv_apply_apply_vec, hα.apply_reebVectorField]
  have h := RoughForm.mem_ker.1 (hβ hw)
  rw [← RoughForm.eval_apply, map_sub, map_smul, RoughForm.eval_apply, RoughForm.eval_apply,
    sub_eq_zero] at h
  rw [h, ContinuousAlternatingMap.smul_apply, smul_eq_mul, smul_eq_mul, mul_comm]

/-- **The multiplier of a contact vector field.** For a contact form `α` with Reeb field `R`, a
smooth vector field `X` is a contact vector field exactly when `L_X α = R(α(X)) α`. -/
theorem mem_contactVectorFields_iff_mlieDerivForm_eq {X : Cₛ^∞⟮I; E, TangentSpace I (M := M)⟯} :
    X ∈ α.contactVectorFields ↔ mlieDerivForm X α.val = fun x ↦
      mvfderiv I (fun y ↦ α.val y ![X y]) x (α.reebVectorField x) • α.val x := by
  refine ⟨fun ⟨g, hg⟩ ↦ funext fun x ↦ ?_, fun h ↦ ⟨_, h⟩⟩
  rw [hg, ← hα.eq_mvfderiv_reebVectorField_of_mlieDerivForm_apply_eq_smul (fun _ ↦ rfl)
    (X.mdifferentiableAt (x := x)) (congrFun hg x)]


/-- A smooth contact vector field of a contact form is the contact Hamiltonian vector field of
its value `α(X)`. -/
theorem isContactHamiltonianVectorField_of_mem_contactVectorFields
    {X : Cₛ^∞⟮I; E, TangentSpace I (M := M)⟯} (hX : X ∈ α.contactVectorFields) :
    α.IsContactHamiltonianVectorField (fun x ↦ α.val x ![X x]) X :=
  (hα.isContactHamiltonianVectorField_iff_mlieDerivForm
    X.mdifferentiable).2 ⟨fun _ ↦ rfl, hX⟩

/-- The contact Hamiltonian vector field of a smooth function is a contact vector field. -/
theorem mem_contactVectorFields_contactHamiltonianVectorField (f : C^∞⟮I, M; ℝ⟯) :
    (⟨α.contactHamiltonianVectorField f,
        hα.contMDiff_contactHamiltonianVectorField le_rfl (f.contMDiff.of_le (by simp))⟩ :
      Cₛ^∞⟮I; E, TangentSpace I (M := M)⟯) ∈ α.contactVectorFields :=
  ⟨_, (hα.isContactHamiltonianVectorField_contactHamiltonianVectorField f).mlieDerivForm_eq
    (hα.mdifferentiable_contactHamiltonianVectorField (f.contMDiff.of_le (by simp)))⟩

/-- **Contact vector fields preserve the contact hyperplanes.** For a contact form `α` on a
boundaryless Hausdorff manifold, a smooth vector field `X` is a contact vector field exactly when,
wherever its maximal flow `φ` is defined at time `t` from `x`, the pulled back form `φ_t^* α` has
the same kernel at `x` as `α`. -/
theorem mem_contactVectorFields_iff_kerDistribution_mpullback_flowOf [I.Boundaryless]
    [T2Space M] {X : Cₛ^∞⟮I; E, TangentSpace I (M := M)⟯} :
    X ∈ α.contactVectorFields ↔ ∀ t x, (t, x) ∈ flowDomain X →
      (TauCeti.mpullback I I (flowOf X t) α.val).ker x = α.kerDistribution x := by
  refine ⟨fun hX t x hx ↦ ?_, fun h ↦ ?_⟩
  · -- The flow of the contact Hamiltonian field of `α(X)` rescales `α` by a positive factor.
    have hpull := (hα.isContactHamiltonianVectorField_of_mem_contactVectorFields hX
      ).mpullback_flowOf_apply hα ((contMDiff_apply_contMDiffSection α X).of_le (by simp)) hx
    ext v
    rw [RoughForm.mem_ker, mem_kerDistribution, hpull, ContinuousAlternatingMap.smul_apply,
      smul_eq_mul, mul_eq_zero, or_iff_right (Real.exp_pos _).ne']
  · -- Near time `0` the pullback at `x` is `c(s) α_x`; differentiate at `s = 0`.
    refine ⟨fun x ↦ mlieDerivForm X α.val x ![α.reebVectorField x], funext fun x ↦ ?_⟩
    have hZ : ContMDiff I I.tangent 2 (fun y ↦ (⟨y, X y⟩ : TangentBundle I M)) :=
      X.contMDiff.of_le (by simp)
    have hZ1 := hZ.of_le one_le_two
    have hd : HasDerivAt (F := E [⋀^Fin 1]→L[ℝ] ℝ)
        (fun s ↦ TauCeti.mpullback I I (flowOf X s) α.val x) (mlieDerivForm X α.val x) 0 :=
      hasDerivAt_mpullback_flowOf_zero hZ x (α.mdifferentiableAt x)
    have hc : HasDerivAt (F := E [⋀^Fin 1]→L[ℝ] ℝ)
        (fun s ↦ TauCeti.mpullback I I (flowOf X s) α.val x ![α.reebVectorField x] • α.val x)
        (mlieDerivForm X α.val x ![α.reebVectorField x] • α.val x) 0 :=
      ((ContinuousAlternatingMap.apply ℝ E ℝ ![α.reebVectorField x]).hasFDerivAt.comp_hasDerivAt
        (0 : ℝ) hd).smul_const (F := E [⋀^Fin 1]→L[ℝ] ℝ) (α.val x)
    have hopen : {s : ℝ | (s, x) ∈ flowDomain X} ∈ 𝓝 0 :=
      ((isOpen_flowDomain hZ1).preimage (continuous_id.prodMk continuous_const)).mem_nhds
        (mem_flowDomain_zero hZ1 x)
    refine hd.unique (hc.congr_of_eventuallyEq ?_)
    filter_upwards [hopen] with s hs
    exact hα.apply_eq_apply_reebVectorField_smul_of_kerDistribution_le (h s x hs).ge

/-- **The contact Hamiltonian of a contact vector field.** For a contact form `α`, the map
`X ↦ α(X)` is a linear equivalence from the contact vector fields to the smooth functions. Its
inverse sends `f` to the contact Hamiltonian vector field `X_f`. -/
def contactHamiltonianEquiv : α.contactVectorFields ≃ₗ[ℝ] C^∞⟮I, M; ℝ⟯ where
  toFun X := ⟨fun x ↦ α.val x ![(X : Cₛ^∞⟮I; E, TangentSpace I (M := M)⟯) x],
    contMDiff_apply_contMDiffSection α X⟩
  -- The anonymous constructors elaborate as subtype terms, on which `ContMDiffMap.coe_add` and
  -- `ContMDiffMap.coe_smul` (both `rfl`) do not match; the final `rfl`s state them pointwise.
  map_add' X Y := ContMDiffMap.ext fun x ↦ by
    simp only [ContMDiffMap.coeFn_mk, Submodule.coe_add, ContMDiffSection.coe_add, Pi.add_apply,
      ← degreeOneEquiv_apply_apply_vec, map_add]
    rfl
  map_smul' c X := ContMDiffMap.ext fun x ↦ by
    simp only [ContMDiffMap.coeFn_mk, Submodule.coe_smul, ContMDiffSection.coe_smul, Pi.smul_apply,
      ← degreeOneEquiv_apply_apply_vec, map_smul]
    rfl
  invFun f := ⟨_, hα.mem_contactVectorFields_contactHamiltonianVectorField f⟩
  left_inv X := by
    refine Subtype.ext (ContMDiffSection.ext fun x ↦ ?_)
    exact (congrFun ((hα.isContactHamiltonianVectorField_iff_eq).1
      (hα.isContactHamiltonianVectorField_of_mem_contactVectorFields X.prop)) x).symm
  right_inv f := by
    ext x
    exact hα.apply_contactHamiltonianVectorField f x

/-- The contact Hamiltonian of a contact vector field `X` is `α(X)`. -/
@[simp]
theorem contactHamiltonianEquiv_apply (X : α.contactVectorFields) (x : M) :
    hα.contactHamiltonianEquiv X x =
      α.val x ![(X : Cₛ^∞⟮I; E, TangentSpace I (M := M)⟯) x] :=
  (rfl)

/-- The inverse of `contactHamiltonianEquiv` sends a smooth function `f` to its contact
Hamiltonian vector field `X_f`. -/
@[simp]
theorem coe_contactHamiltonianEquiv_symm_apply (f : C^∞⟮I, M; ℝ⟯) :
    ⇑(hα.contactHamiltonianEquiv.symm f : Cₛ^∞⟮I; E, TangentSpace I (M := M)⟯) =
      α.contactHamiltonianVectorField f :=
  (rfl)

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
  refine ⟨hβc, ?_⟩
  have h1 : f⁻¹ * f = 1 := funext fun x ↦ inv_mul_cancel₀ (hf₀ x)
  rw [← hα.contactHamiltonianVectorField_of_eq_smul hu hu₀ hβ (hf.mdifferentiable one_ne_zero),
    h1, hβc.contactHamiltonianVectorField_one]

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
