/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Basic
import TauCeti.Geometry.Manifold.Distribution.Diffeomorph

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
* `TauCeti.Diffeotopy.transports_iff_forall_mem_iff`, `TauCeti.Diffeotopy.Transports.mem_iff`:
  the same, as membership conditions at each time.
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

/-- A diffeotopy transports `ξ` exactly when, at every time `t`, the differential of `ψ_t` carries
`ξ_0` onto `ξ_t`: a vector at `x` lies in `ξ_0 x` if and only if its image lies in
`ξ_t (ψ_t x)`. This is the form of the hypotheses of Tau Ceti's lemmas on diffeomorphisms that
carry one distribution onto another, such as `Diffeomorph.mem_iff_mfderiv_trans_apply_mem`. -/
theorem transports_iff_forall_mem_iff {Φ : Diffeotopy J n M}
    {ξ : unitInterval → Π x : M, Submodule ℝ (TangentSpace J x)} :
    Φ.Transports ξ ↔ ∀ t x (v : TangentSpace J x),
      v ∈ ξ 0 x ↔ mfderiv J J (Φ.timeSlice t) x v ∈ ξ t (Φ.timeSlice t x) :=
  forall_congr' fun _ ↦ forall_congr' fun _ ↦ by
    rw [← timeSlice_apply, SetLike.ext_iff]
    simp only [Submodule.mem_comap, ContinuousLinearMap.coe_coe]

/-- If `Φ` transports `ξ`, then at every time `t` the differential of `ψ_t` carries `ξ_0` onto
`ξ_t`. -/
theorem Transports.mem_iff {Φ : Diffeotopy J n M}
    {ξ : unitInterval → Π x : M, Submodule ℝ (TangentSpace J x)} (hΦ : Φ.Transports ξ)
    (t : unitInterval) (x : M) (v : TangentSpace J x) :
    v ∈ ξ 0 x ↔ mfderiv J J (Φ.timeSlice t) x v ∈ ξ t (Φ.timeSlice t x) :=
  transports_iff_forall_mem_iff.1 hΦ t x v

/-- If `χ` preserves the initial distribution `ξ_0` at all times and `Φ` transports `ξ`, then the
composite diffeotopy `χ.trans Φ`, whose slice at `t` is `ψ_t ∘ χ_t`, transports `ξ`. -/
theorem Transports.trans (hn : 1 ≤ n) {χ Φ : Diffeotopy J n M}
    {ξ : unitInterval → Π x : M, Submodule ℝ (TangentSpace J x)}
    (hχ : χ.Transports fun _ ↦ ξ 0) (hΦ : Φ.Transports ξ) : (χ.trans Φ).Transports ξ := by
  refine transports_iff_forall_mem_iff.2 fun t x v ↦ ?_
  rw [timeSlice_trans]
  exact Diffeomorph.mem_iff_mfderiv_trans_apply_mem _ _ (zero_lt_one.trans_le hn).ne'
    (hχ.mem_iff t) (hΦ.mem_iff t) x v

/-- **Transport between two times.** If `Φ` transports `ξ`, then for all times `s` and `t` the
differential of `φ_t ∘ φ_s⁻¹` at `φ_s x` sends `ξ_s (φ_s x)` into `ξ_t (φ_t x)`. -/
theorem Transports.mfderiv_timeSlice_comp_symm_mem (hn : 1 ≤ n) {Φ : Diffeotopy J n M}
    {ξ : unitInterval → Π x : M, Submodule ℝ (TangentSpace J x)} (hΦ : Φ.Transports ξ)
    (s t : unitInterval) (x : M) {w : TangentSpace J (Φ.timeSlice s x)}
    (hw : w ∈ ξ s (Φ.timeSlice s x)) :
    mfderiv J J (fun y ↦ Φ.timeSlice t ((Φ.timeSlice s).symm y)) (Φ.timeSlice s x) w ∈
      ξ t (Φ.timeSlice t x) := by
  have hn₀ : n ≠ 0 := (zero_lt_one.trans_le hn).ne'
  -- `φ_s⁻¹` carries `ξ_s` onto `ξ_0` and `φ_t` carries `ξ_0` onto `ξ_t`, so their composite
  -- `φ_t ∘ φ_s⁻¹` carries `ξ_s` onto `ξ_t`.
  have h := (Diffeomorph.mem_iff_mfderiv_trans_apply_mem _ _ hn₀
    (Diffeomorph.mem_iff_mfderiv_symm_apply_mem _ hn₀ (hΦ.mem_iff s)) (hΦ.mem_iff t)
    (Φ.timeSlice s x) w).1 hw
  rw [Diffeomorph.coe_trans] at h
  -- `h` is the claim at the base point `φ_t (φ_s⁻¹ (φ_s x))`, which is `φ_t x` only
  -- propositionally; membership of a vector of the model space moves along that equality.
  have hcongr : ∀ {y : M}, y = Φ.timeSlice t x → ∀ u : E,
      (u : TangentSpace J y) ∈ ξ t y → (u : TangentSpace J (Φ.timeSlice t x)) ∈
        ξ t (Φ.timeSlice t x) := by
    rintro _ rfl _ hu
    exact hu
  exact hcongr (by rw [Function.comp_apply, Diffeomorph.symm_apply_apply]) _ h

end TauCeti.Diffeotopy

end
