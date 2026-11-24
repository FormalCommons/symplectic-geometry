/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
public import TauCeti.Geometry.Contact.Flow
public import TauCeti.Geometry.Contact.Rescale
public import TauCeti.Geometry.Manifold.VectorBundle.Bilinear.SmulRight
public import TauCeti.Geometry.Manifold.VectorBundle.Hom
public import TauCeti.Geometry.Manifold.VectorBundle.Scalar
public import TauCeti.Geometry.Manifold.VectorBundle.Translate
public import TauCeti.Geometry.Manifold.VectorBundle.SectionAlongMap.Regularity
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.DegreeOne
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Flow.Family
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.LieDeriv
public import SymplecticGeometry.Topology.Algebra.Module.Alternating.Basic

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

Closure of contact vector fields under sums and scalar multiples uses the linearity of the Lie
derivative in the vector field (`TauCeti.mlieDerivForm_add_left`,
`TauCeti.mlieDerivForm_const_smul_left`, `TauCeti.mlieDerivForm_zero_left`).

The file extends Tau Ceti's file of the same path, in its namespace; the submodule is modelled on
`TauCeti.SmoothTwoForm.symplecticVectorFields`. The converse direction of the flow
characterization adapts the proof of the forward direction of Tau Ceti's
`TauCeti.SmoothForm.IsContactHamiltonianVectorField.mpullback_flowOf_apply_eq_self_iff`:
differentiate the pulled back form at time `0` with `TauCeti.hasDerivAt_mpullback_flowOf_zero`,
on the open set of times where the flow from `x` is defined.

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

/-- **The multiplier of a contact vector field.** For a contact form `α` with Reeb field `R`, a
smooth vector field `X` is a contact vector field exactly when `L_X α = R(α(X)) α`. -/
theorem mem_contactVectorFields_iff_mlieDerivForm_eq {X : Cₛ^∞⟮I; E, TangentSpace I (M := M)⟯} :
    X ∈ α.contactVectorFields ↔ mlieDerivForm X α.val = fun x ↦
      mvfderiv I (fun y ↦ α.val y ![X y]) x (α.reebVectorField x) • α.val x := by
  refine ⟨fun ⟨g, hg⟩ ↦ funext fun x ↦ ?_, fun h ↦ ⟨_, h⟩⟩
  rw [hg, ← hα.eq_mvfderiv_reebVectorField_of_mlieDerivForm_apply_eq_smul (fun _ ↦ rfl)
    (X.mdifferentiableAt (x := x)) (congrFun hg x)]


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
    have hpull := ((hα.isContactHamiltonianVectorField_iff_mlieDerivForm X.mdifferentiable).2
      ⟨fun _ ↦ rfl, hX⟩).mpullback_flowOf_apply hα
      ((contMDiff_apply_contMDiffSection α X).of_le (by simp)) hx
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
      hasDerivAt_mpullback_flowOf_zero hZ1 x (α.mdifferentiableAt x)
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
    exact RoughForm.apply_eq_smul_of_ker_le
      ((kerDistribution_eq_ker α x).symm.trans_le (h s x hs).ge) (hα.apply_reebVectorField x)

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
    obtain ⟨g, hg⟩ := X.prop
    exact (congrFun (hα.eq_contactHamiltonianVectorField_of_mlieDerivForm_eq_smul
      X.val.mdifferentiable hg) x).symm
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
`R` on a boundaryless Hausdorff manifold of finite dimension. Then:

* a smooth vector field `X` is a contact vector field exactly when `L_X α = R(α(X)) α`, and
  exactly when its local flow `φ_t` satisfies `ker (φ_t^* α)ₓ = ker αₓ` wherever it is defined;
* `X ↦ α(X)` is a linear equivalence `e` from contact vector fields to smooth functions, and
  `e⁻¹ f` is the unique contact Hamiltonian vector field `X_f` of `f`, that is, the unique field
  with `α(X_f) = f` and `ι_{X_f} dα = R(f) α - df`; it satisfies `L_{X_f} α = R(f) α`, and
  `X_1 = R`;
* for a smooth time-dependent function `f`, the time-dependent flow `φ_t` of `X_{f_t}` from time
  `0` satisfies `(φ_t^* α)ₓ = exp (∫₀ᵗ (R f_s)(φ_s x) ds) • αₓ` wherever it is defined;
* `X_f` is transverse to `ker α` at `x` exactly when `f x ≠ 0`; and if `f` vanishes nowhere and
  `β = f⁻¹ α`, then `β` is a contact form with Reeb field `X_f`, and it induces the coorientation
  of `α` exactly when `f` is positive.

Milestone: *Contact vector fields and contact Hamiltonians*. -/
theorem contactVectorFields_correspondence (hα : α.IsContactForm) :
    (∀ X : Cₛ^∞⟮I; E, TangentSpace I (M := M)⟯, X ∈ α.contactVectorFields ↔
      mlieDerivForm X α.val = fun x ↦
        mvfderiv I (fun y ↦ α.val y ![X y]) x (α.reebVectorField x) • α.val x) ∧
    (∀ X : Cₛ^∞⟮I; E, TangentSpace I (M := M)⟯, X ∈ α.contactVectorFields ↔
      ∀ t x, (t, x) ∈ flowDomain X →
        (TauCeti.mpullback I I (flowOf X t) α.val).ker x = α.kerDistribution x) ∧
    (∀ (X : α.contactVectorFields) (x : M), hα.contactHamiltonianEquiv X x =
      α.val x ![(X : Cₛ^∞⟮I; E, TangentSpace I (M := M)⟯) x]) ∧
    (∀ (f : C^∞⟮I, M; ℝ⟯) (X : (x : M) → TangentSpace I x),
      α.IsContactHamiltonianVectorField f X ↔
        X = (hα.contactHamiltonianEquiv.symm f : Cₛ^∞⟮I; E, TangentSpace I (M := M)⟯)) ∧
    (∀ f : C^∞⟮I, M; ℝ⟯,
      mlieDerivForm (hα.contactHamiltonianEquiv.symm f : Cₛ^∞⟮I; E, TangentSpace I (M := M)⟯)
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
  refine ⟨fun _ ↦ hα.mem_contactVectorFields_iff_mlieDerivForm_eq,
    fun _ ↦ hα.mem_contactVectorFields_iff_kerDistribution_mpullback_flowOf,
    hα.contactHamiltonianEquiv_apply, fun f X ↦ ?_, fun f ↦ ?_,
    hα.contactHamiltonianVectorField_one,
    fun f hf X hX t x hx ↦ hα.mpullback_timeDependentFlowOf_apply_eq_exp_integral_smul
      (hf.of_le (by simp)) hX hx,
    fun f x ↦ ((hα.isContactHamiltonianVectorField_contactHamiltonianVectorField f
      ).mem_kerDistribution_iff x).not, fun f β hf₀ hβ ↦ ?_⟩
  · rw [coe_contactHamiltonianEquiv_symm_apply, hα.isContactHamiltonianVectorField_iff_eq]
  · rw [coe_contactHamiltonianEquiv_symm_apply]
    exact (hα.isContactHamiltonianVectorField_contactHamiltonianVectorField f).mlieDerivForm_eq
      (hα.mdifferentiable_contactHamiltonianVectorField (f.contMDiff.of_le (by simp)))
  · obtain ⟨hβc, hR⟩ := hα.reebVectorField_eq_contactHamiltonianVectorField_of_eq_smul
      (f.contMDiff.of_le (by simp)) hf₀ hβ
    exact ⟨hβc, hR, Diffeomorph.preservesCoorientation_refl_iff_pos hα.apply_ne_zero hβ⟩

end TauCeti.SmoothForm.IsContactForm
