/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Basic
import TauCeti.Geometry.Manifold.Diffeomorph.Basic

/-!
# Diffeotopies that transport a family of distributions

A family of distributions on a manifold `M` over the unit interval is a map
`ξ : unitInterval → Π x : M, Submodule ℝ (TangentSpace J x)`. A diffeotopy `ψ_t` of `M`
*transports* `ξ` if `ψ_t^* ξ_t = ξ_0` for every `t`: at each point `x`, the vectors of `ξ_0 x`
are exactly those that the differential of `ψ_t` at `x` sends into `ξ_t (ψ_t x)`. The pullback
is written with `Submodule.comap`, as Tau Ceti writes pullbacks of distributions
(`TauCeti.IsContactDistribution.exists_darbouxChart`).

## Main definitions

* `TauCeti.Diffeotopy.Transports`: the diffeotopy `Φ` transports the family `ξ`.

## Main results

* `TauCeti.Diffeotopy.transports_iff`: the unfolding of the definition.
* `TauCeti.Diffeotopy.transports_refl`: the constant diffeotopy transports every constant family.
* `TauCeti.Diffeotopy.Transports.mfderiv_timeSlice_comp_symm_mem`: a transporting diffeotopy
  carries `ξ_s` into `ξ_t` along `φ_t ∘ φ_s⁻¹`, for all times `s` and `t`.
* `TauCeti.Diffeotopy.Transports.trans`: if `χ` preserves `ξ_0` at all times and `Φ` transports
  `ξ`, then `χ.trans Φ`, whose slice at `t` is `ψ_t ∘ χ_t`, transports `ξ`. So a transporting
  diffeotopy can be changed by composing it with any diffeotopy that preserves `ξ_0`.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Theorem 2.2.2 (Gray stability), whose isotopy transports a family of contact structures in
  this sense.
-/

public section

open scoped ContDiff Manifold

namespace TauCeti.Diffeotopy

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {J : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω}

/-- A diffeotopy `ψ_t` of `M` **transports** a family `ξ_t` of distributions on `M`,
`t ∈ [0, 1]`, if `ψ_t^* ξ_t = ξ_0` for every `t`: for all `t` and `x`, a tangent vector at `x`
lies in `ξ_0 x` if and only if the differential of `ψ_t` at `x` sends it into
`ξ_t (ψ_t x)`.

The predicate has this meaning only for `1 ≤ n`. For `n = 0`, `mfderiv` is `0` where a slice is
not differentiable, so there the condition forces `ξ_0 x = ⊤`. -/
def Transports (Φ : Diffeotopy J n M)
    (ξ : unitInterval → Π x : M, Submodule ℝ (TangentSpace J x)) : Prop :=
  ∀ t x, ξ 0 x = (ξ t (Φ (t, x))).comap (mfderiv J J (Φ.timeSlice t) x).toLinearMap

/-- The definition of `TauCeti.Diffeotopy.Transports`, unfolded. -/
theorem transports_iff {Φ : Diffeotopy J n M}
    {ξ : unitInterval → Π x : M, Submodule ℝ (TangentSpace J x)} :
    Φ.Transports ξ ↔
      ∀ t x, ξ 0 x = (ξ t (Φ (t, x))).comap (mfderiv J J (Φ.timeSlice t) x).toLinearMap :=
  Iff.rfl

/-- The constant diffeotopy at the identity transports every constant family of
distributions. -/
theorem transports_refl (D : Π x : M, Submodule ℝ (TangentSpace J x)) :
    (refl J n M).Transports fun _ ↦ D := by
  intro t x
  rw [timeSlice_refl, Diffeomorph.coe_refl, mfderiv_id, refl_apply]
  exact (Submodule.comap_id _).symm

/-- If `χ` preserves the initial distribution `ξ_0` at all times and `Φ` transports `ξ`, then the
composite diffeotopy `χ.trans Φ`, whose slice at `t` is `ψ_t ∘ χ_t`, transports `ξ`. -/
theorem Transports.trans (hn : 1 ≤ n) {χ Φ : Diffeotopy J n M}
    {ξ : unitInterval → Π x : M, Submodule ℝ (TangentSpace J x)}
    (hχ : χ.Transports fun _ ↦ ξ 0) (hΦ : Φ.Transports ξ) : (χ.trans Φ).Transports ξ := by
  have hn₀ : n ≠ 0 := (zero_lt_one.trans_le hn).ne'
  intro t x
  have hΦ' := hΦ t (χ.timeSlice t x)
  rw [← timeSlice_apply] at hΦ'
  have hχ' : ξ 0 x = (ξ 0 (χ.timeSlice t x)).comap (mfderiv J J (χ.timeSlice t) x).toLinearMap := by
    rw [timeSlice_apply]; exact hχ t x
  rw [← timeSlice_apply, timeSlice_trans, Diffeomorph.coe_trans,
    mfderiv_comp x ((Φ.timeSlice t).mdifferentiable hn₀ _) ((χ.timeSlice t).mdifferentiable hn₀ _),
    hχ', hΦ', ContinuousLinearMap.toLinearMap_comp, Function.comp_apply,
    Submodule.comap_comp]

/-- **Transport between two times.** If `Φ` transports `ξ`, then for all times `s` and `t` the
differential of `φ_t ∘ φ_s⁻¹` at `φ_s x` sends `ξ_s (φ_s x)` into `ξ_t (φ_t x)`. -/
theorem Transports.mfderiv_timeSlice_comp_symm_mem (hn : 1 ≤ n) {Φ : Diffeotopy J n M}
    {ξ : unitInterval → Π x : M, Submodule ℝ (TangentSpace J x)} (hΦ : Φ.Transports ξ)
    (s t : unitInterval) (x : M) {w : TangentSpace J (Φ.timeSlice s x)}
    (hw : w ∈ ξ s (Φ.timeSlice s x)) :
    mfderiv J J (fun y ↦ Φ.timeSlice t ((Φ.timeSlice s).symm y)) (Φ.timeSlice s x) w ∈
      ξ t (Φ.timeSlice t x) := by
  have hn₀ : n ≠ 0 := (zero_lt_one.trans_le hn).ne'
  have hs := hΦ s x
  have ht := hΦ t x
  rw [← timeSlice_apply] at hs ht
  -- The vector `v` at `x` that `φ_s` sends to `w` lies in `ξ 0 x`, so `φ_t` sends it into `ξ t`.
  set v : TangentSpace J x := mfderiv J J (Φ.timeSlice s).symm (Φ.timeSlice s x) w
  have hdv : mfderiv J J (Φ.timeSlice s) x v = w :=
    Diffeomorph.mfderiv_apply_mfderiv_symm_apply _ hn₀ x w
  have hv : mfderiv J J (Φ.timeSlice t) x v ∈ ξ t (Φ.timeSlice t x) := by
    -- Membership in a `comap` is membership of the image.
    have h₁ : v ∈ (ξ s (Φ.timeSlice s x)).comap (mfderiv J J (Φ.timeSlice s) x).toLinearMap :=
      (congrArg (· ∈ ξ s (Φ.timeSlice s x)) hdv).mpr hw
    exact ht.le (hs.ge h₁)
  have hF : MDifferentiableAt J J (fun y ↦ Φ.timeSlice t ((Φ.timeSlice s).symm y))
      (Φ.timeSlice s x) :=
    ((Φ.timeSlice t).mdifferentiable hn₀ _).comp _ ((Φ.timeSlice s).symm.mdifferentiable hn₀ _)
  have hcomp : (fun y ↦ Φ.timeSlice t ((Φ.timeSlice s).symm y)) ∘ Φ.timeSlice s =
      Φ.timeSlice t :=
    funext fun y ↦ by rw [Function.comp_apply, Diffeomorph.symm_apply_apply]
  have h := mfderiv_comp_apply x hF ((Φ.timeSlice s).mdifferentiable hn₀ x) v
  rw [hcomp] at h
  exact (congrArg (· ∈ ξ t (Φ.timeSlice t x))
    ((congrArg (mfderiv J J _ (Φ.timeSlice s x)) hdv).symm.trans h.symm)).mpr hv

end TauCeti.Diffeotopy

end
