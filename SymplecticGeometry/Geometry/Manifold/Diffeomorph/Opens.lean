/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
public import TauCeti.Geometry.Manifold.ContMDiff.Subtype

/-!
# Restricting a diffeomorphism to open subsets

A diffeomorphism `Φ : U₀ ≃ₘ^n⟮I, I'⟯ V₀` between open subsets of `M` and `M'`, and smaller open
subsets `U ⊆ U₀` and `V ⊆ V₀` that correspond under `Φ`, give a diffeomorphism
`U ≃ₘ^n⟮I, I'⟯ V`, `Diffeomorph.restrictOpens`. Its two maps are smooth because their composites
with the inclusions are those of `Φ` and of its inverse with inclusions of open sets
(`TauCeti.ContMDiff.subtypeVal_comp_iff`, `contMDiff_inclusion`).

## Main definitions

* `Diffeomorph.restrictOpens Φ hU hV h`: the restriction of `Φ` as a diffeomorphism from `U`
  onto `V`, with `coe_restrictOpens_apply` and `coe_restrictOpens_symm_apply`.
-/

public section

open TopologicalSpace
open scoped Manifold

namespace Diffeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E E' H H' M M' : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'}
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace M'] [ChartedSpace H' M']
  {n : WithTop ℕ∞}

/-- The restriction of a diffeomorphism `Φ : U₀ → V₀` between open subsets of `M` and `M'` to
smaller open subsets `U ⊆ U₀` and `V ⊆ V₀` that correspond under `Φ`, as a diffeomorphism from
`U` onto `V`. -/
noncomputable def restrictOpens {U₀ U : Opens M} {V₀ V : Opens M'} (Φ : U₀ ≃ₘ^n⟮I, I'⟯ V₀)
    (hU : U ≤ U₀) (hV : V ≤ V₀) (h : ∀ x : U₀, (x : M) ∈ U ↔ (Φ x : M') ∈ V) : U ≃ₘ^n⟮I, I'⟯ V where
  toFun x := ⟨Φ (Opens.inclusion hU x), (h _).1 x.property⟩
  invFun y :=
    ⟨Φ.symm (Opens.inclusion hV y), (h _).2 (by rw [Φ.apply_symm_apply]; exact y.property)⟩
  left_inv x := by
    have := congrArg Subtype.val (Φ.symm_apply_apply (Opens.inclusion hU x))
    exact Subtype.ext this
  right_inv y := by
    have := congrArg Subtype.val (Φ.apply_symm_apply (Opens.inclusion hV y))
    exact Subtype.ext this
  contMDiff_toFun := by
    refine (TauCeti.ContMDiff.subtypeVal_comp_iff V _).1 ?_
    exact (contMDiff_subtypeVal (U := V₀)).comp (Φ.contMDiff.comp (contMDiff_inclusion hU))
  contMDiff_invFun := by
    refine (TauCeti.ContMDiff.subtypeVal_comp_iff U _).1 ?_
    exact (contMDiff_subtypeVal (U := U₀)).comp (Φ.symm.contMDiff.comp (contMDiff_inclusion hV))

@[simp]
theorem coe_restrictOpens_apply {U₀ U : Opens M} {V₀ V : Opens M'} (Φ : U₀ ≃ₘ^n⟮I, I'⟯ V₀)
    (hU : U ≤ U₀) (hV : V ≤ V₀) (h : ∀ x : U₀, (x : M) ∈ U ↔ (Φ x : M') ∈ V) (x : U) :
    (Φ.restrictOpens hU hV h x : M') = Φ (Opens.inclusion hU x) :=
  (rfl)

@[simp]
theorem coe_restrictOpens_symm_apply {U₀ U : Opens M} {V₀ V : Opens M'}
    (Φ : U₀ ≃ₘ^n⟮I, I'⟯ V₀) (hU : U ≤ U₀) (hV : V ≤ V₀) (h : ∀ x : U₀, (x : M) ∈ U ↔ (Φ x : M') ∈ V)
    (y : V) : ((Φ.restrictOpens hU hV h).symm y : M) = Φ.symm (Opens.inclusion hV y) :=
  (rfl)

end Diffeomorph

end
