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
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.SmoothFamily.Basic
import TauCeti.Geometry.Manifold.DifferentialForm.Flow.Eulerian
import TauCeti.Geometry.Symplectic.Hamiltonian.Bracket

/-!
# Symplectic vector fields and symplectic isotopies

Let `σ` be a closed two-form on a manifold `M`. A smooth vector field `X` is symplectic when its
contraction `ι_X σ` is closed (`TauCeti.SmoothTwoForm.symplecticVectorFields`). This file shows
that this is equivalent to `(φ_t^* σ)_x = σ_x` at each point `(t, x)` of the flow domain, that a
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
* `TauCeti.Diffeotopy.mextDeriv_interior_eulerianField_smoothTransitionFamily`: the exterior
  derivative of the contraction of `σ` with the Eulerian field of the family `u ↦ φ_{s(u)}` over
  `ℝ`, `s = Real.smoothTransition`, is `s'(u)` times `d(ι_{X_{s(u)}} σ)`.
* `TauCeti.Diffeotopy.forall_timeSlice_mem_diffeomorphStabilizer_iff`: every `φ_t` preserves `σ`
  exactly when every velocity `X_t` is symplectic, and then every `ι_{X_t} σ` is closed
  (`TauCeti.Diffeotopy.interiorₗ_smoothVelocity_mem_closedForms`).
* `TauCeti.SmoothTwoForm.IsSymplectic.symplecticVectorFields_and_isotopies`: the milestone, which
  collects these results for a symplectic form.

## Implementation notes

The isotopy criterion is Tau Ceti's
`TauCeti.forall_mpullback_eq_iff_forall_mextDeriv_interior_eulerianField_eq_zero`, applied to the
family `u ↦ φ_{s(u)}` over `ℝ` of `Diffeotopy/Real.lean`. Its Eulerian field at `u` is
`s'(u) • X_{s(u)}` (`TauCeti.Diffeotopy.eulerianField_smoothTransitionFamily`), and
`s'(u) > 0` for `0 < u < 1` (`Real.smoothTransition.deriv_pos`), so the theorem gives the
closedness of `ι_{X_t} σ` for `0 < t < 1`. At `t = 0` and `t = 1` it follows by continuity: the
forms `d(ι_{X_t} σ)` are a smooth family in `t` (`SymplecticGeometry.isSmoothFamily_interiorₗ`),
which vanishes on the dense set `(0, 1)` (`SymplecticGeometry.IsSmoothFamily.ext_on`).
The flow criterion uses Tau Ceti's `TauCeti.mpullback_flowOf_apply_of_mextDeriv_interior_eq_zero`
in one direction and `TauCeti.hasDerivAt_mpullback_flowOf_zero` in the other. That second
direction is adapted from Tau Ceti's
`TauCeti.SmoothForm.IsContactHamiltonianVectorField.mpullback_flowOf_apply_eq_self_iff`
(`TauCeti/Geometry/Contact/Flow.lean`): the pulled-back forms are constant near time `0`, so their
derivative there vanishes.

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

/-- For a closed two-form `σ`, a smooth vector field `X` is symplectic if and only if the
pullback of `σ` by its local flow `φ_t` agrees with `σ` at `x`, `(φ_t^* σ)_x = σ_x`, for each
`(t, x)` in the flow domain of `X`. -/
theorem mem_symplecticVectorFields_iff_forall_mpullback_flowOf_apply [FiniteDimensional ℝ E]
    [J.Boundaryless] [T2Space M] (hσ : σ.IsClosed) {X : Cₛ^∞⟮J; E, TangentSpace J (M := M)⟯} :
    X ∈ σ.symplecticVectorFields ↔
      ∀ t x, (t, x) ∈ flowDomain X → mpullback J J (flowOf X t) σ.val x = σ.val x := by
  have hX : ContMDiff J J.tangent 1 (fun y ↦ (⟨y, X y⟩ : TangentBundle J M)) :=
    X.contMDiff.of_le (by simp)
  refine ⟨fun h t x hx ↦ mpullback_flowOf_apply_of_mextDeriv_interior_eq_zero
    hX hσ (mem_symplecticVectorFields_iff.1 h) hx, fun h ↦ ?_⟩
  rw [mem_symplecticVectorFields_iff_mlieDerivForm_eq_zero hσ]
  funext y
  -- Near `t = 0` the pulled-back forms at `y` are constant, so their derivative there vanishes.
  have hopen : {s | (s, y) ∈ flowDomain X} ∈ 𝓝 (0 : ℝ) :=
    ((isOpen_flowDomain hX).preimage
      (continuous_id.prodMk continuous_const)).mem_nhds
      (mem_flowDomain_zero hX y)
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
  rw [← VectorField.mlieBracket_swap]
  exact isHamiltonianVectorField_mlieBracket hσ hY hX

end SmoothTwoForm

/-! ### Diffeotopies preserving a closed two-form -/

namespace Diffeotopy

variable (Φ : Diffeotopy J ∞ M)

/-- The contraction of a two-form `σ` with the Eulerian field at time `u` of the family
`u ↦ φ_{s(u)}`, `s = Real.smoothTransition`, has exterior derivative `s'(u)` times that of the
contraction `ι_{X_{s(u)}} σ` with the velocity of `Φ`. -/
theorem mextDeriv_interior_eulerianField_smoothTransitionFamily (σ : SmoothTwoForm J M) (u : ℝ) :
    mextDeriv (RoughForm.interior
        (eulerianField J (fun v ↦ (Φ.smoothTransitionFamily v).toEquiv) u) σ.val) =
      deriv Real.smoothTransition u •
        mextDeriv
          (RoughForm.interior (Φ.smoothVelocity (unitInterval.smoothTransition u)) σ.val) := by
  rw [eulerianField_smoothTransitionFamily, ← SmoothTwoForm.coe_interiorₗ, map_smul,
    Submodule.coe_smul, mextDeriv_smul, SmoothTwoForm.coe_interiorₗ]

variable [J.Boundaryless]

/-- **Diffeotopies preserving a closed two-form.** For a closed two-form `σ`, every map `φ_t` of
a diffeotopy preserves `σ` exactly when its velocity `X_t` is a symplectic vector field, that is
`ι_{X_t} σ` is closed, for every `t ∈ [0, 1]`. -/
theorem forall_timeSlice_mem_diffeomorphStabilizer_iff (hσ : σ.IsClosed) :
    (∀ t, Φ.timeSlice t ∈ SmoothForm.diffeomorphStabilizer σ) ↔
      ∀ t, Φ.smoothVelocity t ∈ σ.symplecticVectorFields := by
  set ψ : ℝ → M ≃ M := fun v ↦ (Φ.smoothTransitionFamily v).toEquiv
  have hψ : ContMDiff (𝓘(ℝ, ℝ).prod J) J 2 (fun p : ℝ × M ↦ ψ p.1 p.2) :=
    Φ.contMDiff_smoothTransitionFamily.of_le (by simp)
  have hψ' : ContMDiff (𝓘(ℝ, ℝ).prod J) J 2 (fun p : ℝ × M ↦ (ψ p.1).symm p.2) :=
    Φ.contMDiff_smoothTransitionFamily_symm.of_le (by simp)
  have key := forall_mpullback_eq_iff_forall_mextDeriv_interior_eulerianField_eq_zero hψ hψ'
    σ.mdifferentiable ((SmoothForm.isClosed_def σ).1 hσ)
  have hmem (t : unitInterval) : Φ.smoothVelocity t ∈ σ.symplecticVectorFields ↔
      mextDerivₗ J 1 (σ.interiorₗ (Φ.smoothVelocity t)) = 0 := by
    rw [SmoothTwoForm.mem_symplecticVectorFields_iff, ← SmoothTwoForm.coe_interiorₗ,
      ← mextDerivₗ_apply, ← Submodule.coe_eq_zero]
  have hslice (u : ℝ) : (ψ u : M → M) = Φ.timeSlice (unitInterval.smoothTransition u) :=
    funext fun x ↦ by
      rw [Diffeomorph.coe_toEquiv, smoothTransitionFamily_apply, timeSlice_apply]
  constructor
  · intro h
    have hu := key.1 fun r u ↦ funext fun x ↦ by
      rw [hslice, hslice, SmoothForm.mem_diffeomorphStabilizer_iff_forall.1 (h _) x,
        SmoothForm.mem_diffeomorphStabilizer_iff_forall.1 (h _) x]
    -- On `(0, 1)` the factor `s'(u)` is positive, so `ι_{X_t} σ` is closed there.
    have hzero : EqOn (fun t ↦ mextDerivₗ J 1 (σ.interiorₗ (Φ.smoothVelocity t))) (fun _ ↦ 0)
        (Ioo 0 1) := by
      intro t ht
      obtain ⟨u, ⟨hu₀, hu₁⟩, rfl⟩ := unitInterval.surjOn_smoothTransition_Ioo ht
      have h0 := hu u
      rw [mextDeriv_interior_eulerianField_smoothTransitionFamily] at h0
      exact (hmem _).1 (SmoothTwoForm.mem_symplecticVectorFields_iff.2
        ((smul_eq_zero.1 h0).resolve_left (Real.smoothTransition.deriv_pos hu₀ hu₁).ne'))
    have hfam :=
      (SymplecticGeometry.isSmoothFamily_interiorₗ σ Φ.contMDiff_smoothVelocity).mextDeriv
    intro t
    rw [hmem]
    exact congrFun (hfam.ext_on (SymplecticGeometry.isSmoothFamily_const 0)
      (by rw [dense_iff_closure_eq, closure_Ioo zero_ne_one]; exact Icc_bot_top) hzero) t
  · intro h t
    have hu := key.2 fun u ↦ by
      rw [mextDeriv_interior_eulerianField_smoothTransitionFamily,
        SmoothTwoForm.mem_symplecticVectorFields_iff.1 (h _), smul_zero]
    obtain ⟨u, rfl⟩ := unitInterval.smoothTransition_surjective t
    refine SmoothForm.mem_diffeomorphStabilizer_iff_forall.2 fun x ↦ ?_
    rw [← hslice, hu u 0, hslice, unitInterval.smoothTransition_of_nonpos le_rfl, timeSlice_zero]
    exact congrFun (mpullback_id σ.val) x

/-- If every map of a diffeotopy preserves a closed two-form `σ`, then every contraction
`ι_{X_t} σ` of `σ` with its velocity is a closed one-form. -/
theorem interiorₗ_smoothVelocity_mem_closedForms (hσ : σ.IsClosed)
    (hΦ : ∀ t, Φ.timeSlice t ∈ SmoothForm.diffeomorphStabilizer σ) (t : unitInterval) :
    σ.interiorₗ (Φ.smoothVelocity t) ∈ closedForms J M 1 := by
  rw [mem_closedForms, SmoothTwoForm.coe_interiorₗ]
  exact SmoothTwoForm.mem_symplecticVectorFields_iff.1
    ((Φ.forall_timeSlice_mem_diffeomorphStabilizer_iff hσ).1 hΦ t)

end Diffeotopy

namespace SmoothTwoForm

/-- **Symplectic vector fields and symplectic isotopies.** Let `σ` be a symplectic form on a
boundaryless Hausdorff manifold `M` modelled on a finite-dimensional space.
* A smooth vector field `X` is symplectic, `d(ι_X σ) = 0`, exactly when `L_X σ = 0`, and exactly
  when its local flow `φ_t` satisfies `(φ_t^* σ)_x = σ_x` at each `(t, x)` of its flow domain.
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
      (forall_congr' fun _ ↦ by
        rw [mem_symplecticVectorFields_iff, TauCeti.Diffeotopy.coe_smoothVelocity]),
    fun _ hX _ hY ↦ isHamiltonianVectorField_neg_mlieBracket hσ.isClosed hX hY⟩

end SmoothTwoForm

end TauCeti

end
