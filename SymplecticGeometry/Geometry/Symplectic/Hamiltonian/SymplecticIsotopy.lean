/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Diffeomorphism.Diffeotopy.Real
public import SymplecticGeometry.Geometry.Diffeomorphism.Diffeotopy.Velocity
public import TauCeti.Geometry.Manifold.DifferentialForm.Flow
public import TauCeti.Geometry.Symplectic.Hamiltonian.SymplecticVectorField
import SymplecticGeometry.Analysis.SpecialFunctions.SmoothTransition
import SymplecticGeometry.Geometry.Symplectic.Flux.Hamiltonian
import TauCeti.Geometry.Manifold.DifferentialForm.Flow.Eulerian
import TauCeti.Geometry.Symplectic.Hamiltonian.Bracket

/-!
# Symplectic vector fields and symplectic isotopies

Let `σ` be a closed two-form on a manifold `M`. A smooth vector field `X` is symplectic when its
contraction `ι_X σ` is closed (`TauCeti.SmoothTwoForm.symplecticVectorFields`). This file shows
that this holds exactly when the local flow of `X` preserves `σ` wherever it is defined, that a
diffeotopy `φ_t` consists of maps preserving `σ` exactly when its velocity `X_t` is symplectic for
every `t`, and that symplectic fields `X`, `Y` have a Hamiltonian bracket, with Hamiltonian
`σ(X, Y)`. Together with Tau Ceti's
`TauCeti.SmoothTwoForm.mem_symplecticVectorFields_iff_mlieDerivForm_eq_zero` this is
McDuff–Salamon, Proposition 3.1.5 and Remark 3.1.6, without compactness, since the isotopy is
given.

## Main results

* `TauCeti.SmoothTwoForm.mem_symplecticVectorFields_iff_forall_mpullback_flowOf_apply`: a smooth
  vector field is symplectic exactly when its local flow preserves `σ` on its domain.
* `TauCeti.SmoothTwoForm.isHamiltonianVectorField_neg_mlieBracket`: for symplectic `X` and `Y`,
  the field `-[X, Y]` (the bracket of McDuff–Salamon, Mathlib's `VectorField.mlieBracket` with the
  opposite sign) is a Hamiltonian vector field of `σ(X, Y)`.
* `TauCeti.Diffeotopy.eulerianField_smoothTransitionFamily`: the Eulerian field of the family
  `u ↦ φ_{s(u)}` over `ℝ`, `s = Real.smoothTransition`, is `s'(u) • X_{s(u)}`.
* `TauCeti.Diffeotopy.mextDeriv_interior_eulerianField_smoothTransitionFamily`: the exterior
  derivative of the contraction of `σ` with that field is `s'(u)` times `d(ι_{X_{s(u)}} σ)`.
* `TauCeti.Diffeotopy.forall_timeSlice_mem_diffeomorphStabilizer_iff`: every `φ_t` preserves `σ`
  exactly when every velocity `X_t` is symplectic.
* `TauCeti.SmoothTwoForm.IsSymplectic.symplecticVectorFields_and_isotopies`: the milestone, which
  collects these results for a symplectic form.

## Implementation notes

The isotopy criterion is Tau Ceti's
`TauCeti.forall_mpullback_eq_iff_forall_mextDeriv_interior_eulerianField_eq_zero`, applied to the
family `u ↦ φ_{s(u)}` over `ℝ` of `Diffeotopy/Real.lean`. Its Eulerian field at `u` is
`s'(u) • X_{s(u)}`, and `s'(u) > 0` for `0 < u < 1` (`Real.smoothTransition.deriv_pos`), so the
theorem gives the closedness of `ι_{X_t} σ` for `0 < t < 1`. At `t = 0` and `t = 1` it follows by
continuity: the forms `d(ι_{X_t} σ)` are a smooth family in `t`
(`SymplecticGeometry.isSmoothFamily_interiorₗ`), which vanishes on the dense set `(0, 1)`
(`SymplecticGeometry.IsSmoothFamily.ext_on`). The flow criterion uses Tau Ceti's
`TauCeti.mpullback_flowOf_apply_of_mextDeriv_interior_eq_zero` in one direction and
`TauCeti.hasDerivAt_mpullback_flowOf_zero` in the other.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §3.1,
  Proposition 3.1.5 and Remark 3.1.6.
-/

public noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {J : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold J ∞ M] {σ : SmoothTwoForm J M}

namespace SmoothTwoForm

/-! ### Symplectic vector fields and their local flows -/

/-- For a closed two-form `σ`, a smooth vector field `X` is symplectic exactly when its local flow
preserves `σ` wherever it is defined: `(φ_t^* σ)_x = σ_x` for every `(t, x)` in the domain of the
flow. -/
theorem mem_symplecticVectorFields_iff_forall_mpullback_flowOf_apply [FiniteDimensional ℝ E]
    [J.Boundaryless] [T2Space M] (hσ : σ.IsClosed) {X : Cₛ^∞⟮J; E, TangentSpace J (M := M)⟯} :
    X ∈ σ.symplecticVectorFields ↔
      ∀ t x, (t, x) ∈ flowDomain X → mpullback J J (flowOf X t) σ.val x = σ.val x := by
  have hX : ContMDiff J J.tangent 2 (fun y ↦ (⟨y, X y⟩ : TangentBundle J M)) :=
    X.contMDiff.of_le (by simp)
  refine ⟨fun h t x hx ↦ mpullback_flowOf_apply_of_mextDeriv_interior_eq_zero hX hσ
    (mem_symplecticVectorFields_iff.1 h) hx, fun h ↦ ?_⟩
  rw [mem_symplecticVectorFields_iff_mlieDerivForm_eq_zero hσ]
  funext y
  -- Near `t = 0` the pulled-back forms at `y` are constant, so their derivative there vanishes.
  have hopen : {s | (s, y) ∈ flowDomain X} ∈ 𝓝 (0 : ℝ) :=
    ((isOpen_flowDomain (hX.of_le one_le_two)).preimage
      (continuous_id.prodMk continuous_const)).mem_nhds
      (mem_flowDomain_zero (hX.of_le one_le_two) y)
  have hconst : (fun s ↦ mpullback J J (flowOf X s) σ.val y) =ᶠ[𝓝 0] fun _ ↦ σ.val y :=
    Filter.mem_of_superset hopen fun s hs ↦ h s y hs
  exact ((hasDerivAt_mpullback_flowOf_zero hX y (σ.mdifferentiableAt y)).congr_of_eventuallyEq
    hconst.symm).unique (hasDerivAt_const 0 _)

/-! ### The bracket of symplectic vector fields -/

/-- For a closed two-form `σ` and symplectic vector fields `X` and `Y`, the field `-[X, Y]` is a
Hamiltonian vector field of `σ(X, Y)`: `ι_{-[X, Y]} σ = d(σ(X, Y))`. Here `[X, Y]` is Mathlib's
`VectorField.mlieBracket`, and `-[X, Y]` is the bracket of McDuff–Salamon. -/
theorem isHamiltonianVectorField_neg_mlieBracket (hσ : σ.IsClosed)
    {X Y : Cₛ^∞⟮J; E, TangentSpace J (M := M)⟯} (hX : X ∈ σ.symplecticVectorFields)
    (hY : Y ∈ σ.symplecticVectorFields) :
    σ.IsHamiltonianVectorField (fun x ↦ SmoothBundleForm.eval₂ σ x (X x) (Y x))
      (-VectorField.mlieBracket J X Y) := by
  have h := isHamiltonianVectorField_iff.1 (isHamiltonianVectorField_mlieBracket hσ hX hY)
  have hswap : (fun x ↦ SmoothBundleForm.eval₂ σ x (X x) (Y x)) =
      -fun x ↦ SmoothBundleForm.eval₂ σ x (Y x) (X x) :=
    funext fun x ↦ SmoothBundleForm.eval₂_swap σ x _ _
  refine isHamiltonianVectorField_iff.2 fun x v ↦ ?_
  rw [hswap, mvfderiv_neg, Pi.neg_apply, SmoothBundleForm.eval₂_neg_left, h x v,
    neg_apply]

end SmoothTwoForm

/-! ### Diffeotopies preserving a closed two-form -/

namespace Diffeotopy

variable (Φ : Diffeotopy J ∞ M)

/-- The Eulerian field at time `u` of the family `u ↦ φ_{s(u)}` over `ℝ` of a diffeotopy `Φ`,
`s = Real.smoothTransition`, is `s'(u)` times the velocity `X_{s(u)}` of `Φ`. -/
theorem eulerianField_smoothTransitionFamily (u : ℝ) :
    eulerianField J (fun v ↦ (Φ.smoothTransitionFamily v).toEquiv) u =
      ⇑(deriv Real.smoothTransition u • Φ.velocity (Real.smoothTransitionUnit u)) := by
  funext y
  obtain ⟨x, rfl⟩ : ∃ x, Φ.smoothTransitionFamily u x = y :=
    ⟨(Φ.smoothTransitionFamily u).symm y, (Φ.smoothTransitionFamily u).apply_symm_apply y⟩
  rw [eulerianField_smoothTransitionFamily_apply, ContMDiffSection.coe_smul, Pi.smul_apply,
    smoothTransitionFamily_apply, velocity_apply_apply]
  -- The sides differ only in the base point that names the fibre of the scalar multiplication,
  -- `Φ (s u, x)` on the left and `Φ.cylinderMap (x, s u)` on the right, equal by definition.
  rfl

/-- The contraction of a two-form `σ` with the Eulerian field at time `u` of the family
`u ↦ φ_{s(u)}`, `s = Real.smoothTransition`, has exterior derivative `s'(u)` times that of the
contraction `ι_{X_{s(u)}} σ` with the velocity of `Φ`. -/
theorem mextDeriv_interior_eulerianField_smoothTransitionFamily (σ : SmoothTwoForm J M) (u : ℝ) :
    mextDeriv (RoughForm.interior
        (eulerianField J (fun v ↦ (Φ.smoothTransitionFamily v).toEquiv) u) σ.val) =
      deriv Real.smoothTransition u •
        mextDeriv (RoughForm.interior (Φ.velocity (Real.smoothTransitionUnit u)) σ.val) := by
  rw [eulerianField_smoothTransitionFamily, ← SmoothTwoForm.coe_interiorₗ, map_smul,
    Submodule.coe_smul, mextDeriv_smul, SmoothTwoForm.coe_interiorₗ]

variable [J.Boundaryless]

/-- **Diffeotopies preserving a closed two-form.** For a closed two-form `σ`, every map `φ_t` of
a diffeotopy preserves `σ` exactly when its velocity `X_t` is a symplectic vector field, that is
`ι_{X_t} σ` is closed, for every `t ∈ [0, 1]`. -/
theorem forall_timeSlice_mem_diffeomorphStabilizer_iff (hσ : σ.IsClosed) :
    (∀ t, Φ.timeSlice t ∈ SmoothForm.diffeomorphStabilizer σ) ↔
      ∀ t, Φ.velocity t ∈ σ.symplecticVectorFields := by
  set ψ : ℝ → M ≃ M := fun v ↦ (Φ.smoothTransitionFamily v).toEquiv
  have hψ : ContMDiff (𝓘(ℝ, ℝ).prod J) J 2 (fun p : ℝ × M ↦ ψ p.1 p.2) :=
    Φ.contMDiff_smoothTransitionFamily.of_le (by simp)
  have hψ' : ContMDiff (𝓘(ℝ, ℝ).prod J) J 2 (fun p : ℝ × M ↦ (ψ p.1).symm p.2) :=
    Φ.contMDiff_smoothTransitionFamily_symm.of_le (by simp)
  have key := forall_mpullback_eq_iff_forall_mextDeriv_interior_eulerianField_eq_zero hψ hψ'
    σ.mdifferentiable ((SmoothForm.isClosed_def σ).1 hσ)
  have hmem (t : unitInterval) : Φ.velocity t ∈ σ.symplecticVectorFields ↔
      mextDerivₗ J 1 (σ.interiorₗ (Φ.velocity t)) = 0 := by
    rw [SmoothTwoForm.mem_symplecticVectorFields_iff, ← SmoothTwoForm.coe_interiorₗ,
      ← mextDerivₗ_apply, ← Submodule.coe_eq_zero]
  have hslice (u : ℝ) : (ψ u : M → M) = Φ.timeSlice (Real.smoothTransitionUnit u) :=
    funext fun x ↦ by
      rw [Diffeomorph.coe_toEquiv, smoothTransitionFamily_apply, timeSlice_apply]
  have hcont : ContinuousOn Real.smoothTransition (Icc 0 1) :=
    Real.smoothTransition.continuous.continuousOn
  -- `s` maps `[0, 1]` onto `[0, 1]`, and `(0, 1)` onto `(0, 1)`.
  have hIcc : Icc (0 : ℝ) 1 ⊆ Real.smoothTransition '' Icc 0 1 := by
    simpa only [Real.smoothTransition.zero, Real.smoothTransition.one] using
      intermediate_value_Icc zero_le_one hcont
  have hIoo : Ioo (0 : ℝ) 1 ⊆ Real.smoothTransition '' Ioo 0 1 := by
    simpa only [Real.smoothTransition.zero, Real.smoothTransition.one] using
      intermediate_value_Ioo zero_le_one hcont
  constructor
  · intro h
    have hu := key.1 fun r u ↦ funext fun x ↦ by
      rw [hslice, hslice, SmoothForm.mem_diffeomorphStabilizer_iff_forall.1 (h _) x,
        SmoothForm.mem_diffeomorphStabilizer_iff_forall.1 (h _) x]
    -- On `(0, 1)` the factor `s'(u)` is positive, so `ι_{X_t} σ` is closed there.
    have hzero : EqOn (fun t ↦ mextDerivₗ J 1 (σ.interiorₗ (Φ.velocity t))) (fun _ ↦ 0)
        (Ioo 0 1) := by
      rintro t ⟨h₀, h₁⟩
      obtain ⟨u, ⟨hu₀, hu₁⟩, hut⟩ := hIoo ⟨h₀, h₁⟩
      obtain rfl : Real.smoothTransitionUnit u = t :=
        Subtype.ext ((Real.coe_smoothTransitionUnit u).trans hut)
      have h0 := hu u
      rw [mextDeriv_interior_eulerianField_smoothTransitionFamily] at h0
      exact (hmem _).1 (SmoothTwoForm.mem_symplecticVectorFields_iff.2
        ((smul_eq_zero.1 h0).resolve_left (Real.smoothTransition.deriv_pos hu₀ hu₁).ne'))
    have hfam := (SymplecticGeometry.isSmoothFamily_interiorₗ σ Φ.contMDiff_velocity).mextDeriv
    intro t
    rw [hmem]
    exact congrFun (hfam.ext_on (SymplecticGeometry.isSmoothFamily_const 0)
      (by rw [dense_iff_closure_eq, closure_Ioo zero_ne_one]; exact Icc_bot_top) hzero) t
  · intro h t
    have hu := key.2 fun u ↦ by
      rw [mextDeriv_interior_eulerianField_smoothTransitionFamily,
        SmoothTwoForm.mem_symplecticVectorFields_iff.1 (h _), smul_zero]
    obtain ⟨u, -, hut⟩ := hIcc t.property
    obtain rfl : Real.smoothTransitionUnit u = t :=
      Subtype.ext ((Real.coe_smoothTransitionUnit u).trans hut)
    refine SmoothForm.mem_diffeomorphStabilizer_iff_forall.2 fun x ↦ ?_
    rw [← hslice, hu u 0, hslice, Real.smoothTransitionUnit_of_nonpos le_rfl, timeSlice_zero]
    exact congrFun (mpullback_id σ.val) x

end Diffeotopy

namespace SmoothTwoForm

/-- **Symplectic vector fields and symplectic isotopies.** Let `σ` be a symplectic form on a
boundaryless Hausdorff manifold `M` modelled on a finite-dimensional space.
* A smooth vector field `X` is symplectic, `d(ι_X σ) = 0`, exactly when `L_X σ = 0`, and exactly
  when its local flow `φ_t` satisfies `(φ_t^* σ)_x = σ_x` wherever it is defined.
* A diffeotopy `φ_t`, `t ∈ [0, 1]`, with velocity `X_t = (∂ₜ φ_t) ∘ φ_t⁻¹`, satisfies
  `φ_t^* σ = σ` for every `t` exactly when `d(ι_{X_t} σ) = 0` for every `t`.
* For symplectic `X` and `Y`, the bracket `[X, Y]_b = -[X, Y]` of McDuff–Salamon, where `[X, Y]`
  is Mathlib's `VectorField.mlieBracket`, satisfies `ι_{[X, Y]_b} σ = d(σ(X, Y))`.

Milestone: *Symplectic vector fields and isotopy generators*. -/
theorem IsSymplectic.symplecticVectorFields_and_isotopies [FiniteDimensional ℝ E]
    [J.Boundaryless] [T2Space M] (hσ : σ.IsSymplectic) :
    (∀ X : Cₛ^∞⟮J; E, TangentSpace J (M := M)⟯,
      (X ∈ σ.symplecticVectorFields ↔ mextDeriv (RoughForm.interior X σ.val) = 0) ∧
      (X ∈ σ.symplecticVectorFields ↔ mlieDerivForm X σ.val = 0) ∧
      (X ∈ σ.symplecticVectorFields ↔
        ∀ t x, (t, x) ∈ flowDomain X → mpullback J J (flowOf X t) σ.val x = σ.val x)) ∧
    (∀ Φ : Diffeotopy J ∞ M, (∀ t, Φ.timeSlice t ∈ SmoothForm.diffeomorphStabilizer σ) ↔
      ∀ t, mextDeriv (RoughForm.interior (Φ.velocity t) σ.val) = 0) ∧
    (∀ X ∈ σ.symplecticVectorFields, ∀ Y ∈ σ.symplecticVectorFields,
      σ.IsHamiltonianVectorField (fun x ↦ SmoothBundleForm.eval₂ σ x (X x) (Y x))
        (-VectorField.mlieBracket J X Y)) :=
  ⟨fun _ ↦ ⟨mem_symplecticVectorFields_iff,
      mem_symplecticVectorFields_iff_mlieDerivForm_eq_zero hσ.isClosed,
      mem_symplecticVectorFields_iff_forall_mpullback_flowOf_apply hσ.isClosed⟩,
    fun Φ ↦ (Φ.forall_timeSlice_mem_diffeomorphStabilizer_iff hσ.isClosed).trans
      (forall_congr' fun _ ↦ mem_symplecticVectorFields_iff),
    fun _ hX _ hY ↦ isHamiltonianVectorField_neg_mlieBracket hσ.isClosed hX hY⟩

end SmoothTwoForm

end TauCeti

end
