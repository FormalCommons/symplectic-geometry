/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.OrderedFlow
public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Reparam
public import SymplecticGeometry.Geometry.Diffeomorphism.Diffeotopy.Velocity
public import SymplecticGeometry.Geometry.Manifold.Algebra.Monoid
public import SymplecticGeometry.Geometry.Manifold.Instances.Icc

/-!
# Truncations of diffeotopies

For a diffeotopy `φ_t`, `t ∈ [0, 1]`, and a time `T ∈ [0, 1]`, the **truncation**
`Φ.truncate T` is the diffeotopy `t ↦ φ_{T t}`: it runs through the motion of `Φ` up to time `T`,
at speed `T`, and ends at `φ_T`. It is Tau Ceti's reparametrization `TauCeti.Diffeotopy.reparam`
along the smooth map `s ↦ T s` of the unit interval. Unlike Mathlib's `Path.truncate`, which
restricts a path to a subinterval without changing its domain, the truncation rescales time so
that it is again parametrized by `[0, 1]`.

Truncation commutes with the pointwise operations `trans` and `symm`, and the truncation of an
ordered flow `ψ^(v 0)_(A 0 t) ∘ ⋯ ∘ ψ^(v (k-1))_(A (k-1) t)` is the ordered flow of the time
functions `t ↦ A i (T t)`. By the chain rule, the velocity of the truncation at time `t` is
`T X_{T t}`, where `X` is the velocity of `Φ`.

The truncations are the initial pieces of a diffeotopy, whose fluxes McDuff–Salamon differentiate
in time in the proofs of Theorem 10.2.5 and Proposition 10.2.12.

## Main definitions

* `TauCeti.Diffeotopy.truncate`: the diffeotopy `t ↦ φ_{T t}`.

## Main results

* `TauCeti.Diffeotopy.truncate_apply`, `timeSlice_truncate`, `final_truncate`: the truncation at
  time `t` is `φ_{T t}`, and it ends at `φ_T`.
* `TauCeti.Diffeotopy.truncate_one`, `truncate_zero`, `truncate_truncate`: truncating at `1` does
  nothing, at `0` gives the constant diffeotopy, and truncations compose.
* `TauCeti.Diffeotopy.truncate_trans`, `truncate_symm`: truncation commutes with the pointwise
  operations.
* `TauCeti.Diffeotopy.truncate_orderedGlobalFlowDiffeotopy`: truncations of ordered flows.
* `TauCeti.Diffeotopy.velocity_truncate`, `smoothVelocity_truncate`: the velocity of the
  truncation is `T X_{T t}`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §10.2.
-/

public noncomputable section

open unitInterval
open scoped Manifold ContDiff

namespace TauCeti.Diffeotopy

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {J : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω}

section Truncate

variable (Φ Ψ : Diffeotopy J n M) (T : I)

/-- The **truncation** of a diffeotopy `φ` at time `T ∈ [0, 1]`: the diffeotopy `t ↦ φ_{T t}`,
which runs through the motion of `φ` up to time `T`, rescaled to the unit interval. It is the
reparametrization of `φ` along `s ↦ T s`. -/
def truncate : Diffeotopy J n M :=
  Φ.reparam (ContMDiffMap.mulLeft T)

/-- The truncation at time `T` is the reparametrization along `s ↦ T s`. -/
theorem truncate_def : Φ.truncate T = Φ.reparam (ContMDiffMap.mulLeft T) :=
  (rfl)

/-- The truncation at time `T` is `φ_{T t}` at time `t`. -/
@[simp]
theorem truncate_apply (p : I × M) : Φ.truncate T p = Φ (T * p.1, p.2) := by
  rw [truncate_def, reparam_apply_of_map_zero _ (by simp), ContMDiffMap.mulLeft_apply]

/-- The time slices of the truncation at time `T` are `φ_{T t}`. -/
@[simp]
theorem timeSlice_truncate (t : I) : (Φ.truncate T).timeSlice t = Φ.timeSlice (T * t) :=
  _root_.Diffeomorph.ext fun x ↦ by simp

/-- The truncation at time `T` ends at `φ_T`. -/
@[simp]
theorem final_truncate : (Φ.truncate T).final = Φ.timeSlice T := by
  rw [final_def, timeSlice_truncate, mul_one]

/-- Truncating at time `1` does nothing. -/
@[simp]
theorem truncate_one : Φ.truncate 1 = Φ :=
  ext fun p ↦ by simp

/-- Truncating at time `0` gives the constant diffeotopy. -/
@[simp]
theorem truncate_zero : Φ.truncate 0 = refl J n M :=
  ext fun p ↦ by simp

/-- Truncations compose: truncating at `T` and then at `S` is truncating at `T S`. -/
@[simp]
theorem truncate_truncate (S : I) : (Φ.truncate T).truncate S = Φ.truncate (T * S) :=
  ext fun p ↦ by simp [mul_assoc]

/-- Truncation commutes with pointwise composition. -/
theorem truncate_trans : (Φ.trans Ψ).truncate T = (Φ.truncate T).trans (Ψ.truncate T) :=
  reparam_trans _ _ (by simp)

/-- Truncation commutes with pointwise inversion. -/
theorem truncate_symm : Φ.symm.truncate T = (Φ.truncate T).symm := by
  rw [truncate_def, truncate_def, reparam_symm _ (by simp)]

end Truncate

section OrderedFlow

variable [FiniteDimensional ℝ E] [T2Space M] [BoundarylessManifold J M] [IsManifold J 1 M]
  {n : ℕ∞} [IsManifold J n M]

/-- The truncation at time `T` of the ordered flow of complete fields `v i` along time functions
`A i` is the ordered flow of the same fields along the time functions `t ↦ A i (T t)`. -/
theorem truncate_orderedGlobalFlowDiffeotopy (hn : 1 ≤ n) {k : ℕ}
    (v : Fin k → (x : M) → TangentSpace J x)
    (hv : ∀ i, CMDiff n (fun y ↦ (⟨y, v i y⟩ : TangentBundle J M)))
    (hc : ∀ i, IsCompleteVectorField (v i)) (A : Fin k → ℝ → ℝ) (hA : ∀ i, ContDiff ℝ n (A i))
    (hA₀ : ∀ i, A i 0 = 0) (T : I) :
    (orderedGlobalFlowDiffeotopy hn v hv hc A hA hA₀).truncate T =
      orderedGlobalFlowDiffeotopy hn v hv hc (fun i t ↦ A i (T * t))
        (fun i ↦ (hA i).comp (contDiff_const.mul contDiff_id)) (fun i ↦ by simp [hA₀]) :=
  ext fun p ↦ by simp

end OrderedFlow

section Velocity

/-- The velocity of the truncation at time `T` is `T X_{T t}` at time `t`, where `X` is the
velocity of `φ`. -/
theorem velocity_truncate (Φ : Diffeotopy J n M) (hn : 1 ≤ n) (T t : I) :
    (Φ.truncate T).velocity t = (T : ℝ) • Φ.velocity (T * t) := by
  funext y
  obtain ⟨x, rfl⟩ : ∃ x, Φ.truncate T (t, x) = y := ⟨_, (Φ.truncate T).apply_mk_symm_apply t y⟩
  have hcomp : (fun s : I ↦ Φ.truncate T (s, x)) = (fun u : I ↦ Φ (u, x)) ∘ (fun s : I ↦ T * s) :=
    funext fun s ↦ Φ.truncate_apply T (s, x)
  have hd : MDifferentiableAt (𝓡∂ 1) J (fun u : I ↦ Φ (u, x)) (T * t) :=
    (Φ.contMDiff.comp (contMDiff_id.prodMk contMDiff_const)).mdifferentiableAt
      (zero_lt_one.trans_le hn).ne'
  rw [velocity_apply, mfderiv_cylinderMap_time _ hn, Pi.smul_apply, truncate_apply,
    velocity_apply, mfderiv_cylinderMap_time _ hn]
  simp only
  rw [hcomp, mfderiv_comp_apply t hd mdifferentiableAt_mul_left, mfderiv_mul_left_one, map_smul]

variable [IsManifold J ∞ M]

/-- `velocity_truncate` for the smooth vector fields `smoothVelocity`. -/
theorem smoothVelocity_truncate (Φ : Diffeotopy J ∞ M) (T t : I) :
    (Φ.truncate T).smoothVelocity t = (T : ℝ) • Φ.smoothVelocity (T * t) := by
  ext y
  rw [coe_smoothVelocity, velocity_truncate _ (by simp), ContMDiffSection.coe_smul,
    coe_smoothVelocity]

end Velocity

end TauCeti.Diffeotopy

end
