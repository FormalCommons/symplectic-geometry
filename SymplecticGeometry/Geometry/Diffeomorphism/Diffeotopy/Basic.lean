/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Basic
public import SymplecticGeometry.Geometry.Manifold.Diffeomorph.Prod.Basic
public import TauCeti.Geometry.Manifold.ContMDiff.Subtype

/-!
# Basic facts about diffeotopies

For a diffeotopy `φ_t`, `t ∈ [0, 1]`, of a manifold `M` (`TauCeti.Diffeotopy`), of any smoothness,
`φ_t x` lies in the connected component of `x`, since `t ↦ φ_t x` is a path from `x`
(`TauCeti.Diffeotopy.connectedComponent_apply`).

A diffeomorphism `Ψ` of `[0, 1] × M` that preserves the time coordinate need not be the identity
at time zero, but composing it with `id × Ψ_0⁻¹`, for its time-zero slice `Ψ_0`, gives the
diffeotopy `t ↦ Ψ_t ∘ Ψ_0⁻¹` (`TauCeti.Diffeotopy.ofFstEq`). The time slices of a diffeotopy
are the slices of its total diffeomorphism (`TauCeti.Diffeotopy.timeSlice_eq_slice`).

A diffeotopy that fixes every point outside a set `K` at all times maps every set containing `K`
onto itself at all times (`TauCeti.Diffeotopy.apply_mem_iff_of_subset`). A diffeotopy restricts
to a diffeotopy of every open set that each time slice maps onto itself
(`TauCeti.Diffeotopy.subtype`).

## Main definitions

* `TauCeti.Diffeotopy.ofFstEq Ψ hΨ`: the diffeotopy `t ↦ Ψ_t ∘ Ψ_0⁻¹` of a time-preserving
  diffeomorphism `Ψ` of `[0, 1] × M`.
* `TauCeti.Diffeotopy.subtype Φ U hU`: the restriction of `Φ` to an open set `U` that every time
  slice maps onto itself.

## Main results

* `TauCeti.Diffeotopy.connectedComponent_apply`: `φ_t x` lies in the connected component of `x`.
* `TauCeti.Diffeotopy.timeSlice_eq_slice`: `Φ.timeSlice t` is the slice at `t` of the total
  diffeomorphism of `Φ` (`Diffeomorph.slice`).
* `TauCeti.Diffeotopy.apply_mem_iff_of_subset`: a diffeotopy that is the identity off `K` maps
  every superset of `K` onto itself at all times.
-/

public noncomputable section

open Set
open scoped ContDiff Manifold

namespace TauCeti.Diffeotopy

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {J : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω}

/-- A diffeotopy moves every point inside its connected component: `φ_t x` lies in the connected
component of `x`. -/
theorem connectedComponent_apply (Φ : Diffeotopy J n M) (p : unitInterval × M) :
    connectedComponent (Φ p) = connectedComponent p.2 := by
  have hc : Continuous fun s : unitInterval ↦ Φ (s, p.2) :=
    Φ.contMDiff.continuous.comp (continuous_id.prodMk continuous_const)
  have hsub := (isPreconnected_univ.image _ hc.continuousOn).subset_connectedComponent
    ⟨0, mem_univ _, Φ.apply_zero p.2⟩
  exact (connectedComponent_eq (hsub ⟨p.1, mem_univ _, rfl⟩)).symm

/-- The time-`t` slice of a diffeotopy is the slice at `t` of its total diffeomorphism. -/
theorem timeSlice_eq_slice (Φ : Diffeotopy J n M) (t : unitInterval) :
    Φ.timeSlice t = Φ.toDiffeomorph.slice Φ.fst_apply t :=
  Diffeomorph.ext fun x ↦ by rw [timeSlice_apply, Diffeomorph.slice_apply, coe_apply]

section ofFstEq

variable (Ψ : (unitInterval × M) ≃ₘ^n⟮(𝓡∂ 1).prod J, (𝓡∂ 1).prod J⟯ unitInterval × M)
  (hΨ : ∀ p, (Ψ p).1 = p.1)

/-- The diffeotopy `t ↦ Ψ_t ∘ Ψ_0⁻¹` of a diffeomorphism `Ψ` of `[0, 1] × M` that preserves the
time coordinate, where `Ψ_t` is the slice of `Ψ` at `t`. Its total diffeomorphism is
`Ψ ∘ (id × Ψ_0⁻¹)`. -/
def ofFstEq : Diffeotopy J n M where
  toDiffeomorph :=
    ((Diffeomorph.refl (𝓡∂ 1) unitInterval n).prodCongr (Ψ.slice hΨ 0).symm).trans Ψ
  fst_apply p := by
    rw [Diffeomorph.coe_trans, Function.comp_apply, hΨ, Diffeomorph.coe_prodCongr,
      Diffeomorph.coe_refl, Prod.map_fst, id_eq]
  snd_apply_zero' x := by
    rw [Diffeomorph.coe_trans, Function.comp_apply, Diffeomorph.coe_prodCongr,
      Diffeomorph.coe_refl, Prod.map_apply, id_eq, ← Diffeomorph.slice_apply Ψ hΨ,
      Diffeomorph.apply_symm_apply]

/-- The total diffeomorphism of `ofFstEq Ψ hΨ` is `Ψ ∘ (id × Ψ_0⁻¹)`. -/
theorem toDiffeomorph_ofFstEq : (ofFstEq Ψ hΨ).toDiffeomorph =
    ((Diffeomorph.refl (𝓡∂ 1) unitInterval n).prodCongr (Ψ.slice hΨ 0).symm).trans Ψ :=
  (rfl)

/-- The diffeotopy `ofFstEq Ψ hΨ` sends `(t, x)` to `Ψ_t (Ψ_0⁻¹ x)`. -/
@[simp]
theorem ofFstEq_apply (p : unitInterval × M) :
    ofFstEq Ψ hΨ p = Ψ.slice hΨ p.1 ((Ψ.slice hΨ 0).symm p.2) := by
  rw [coe_apply, toDiffeomorph_ofFstEq, Diffeomorph.slice_apply, Diffeomorph.coe_trans,
    Function.comp_apply, Diffeomorph.coe_prodCongr, Diffeomorph.coe_refl, Prod.map_apply, id_eq]

/-- The time-`t` slice of `ofFstEq Ψ hΨ` is `Ψ_t ∘ Ψ_0⁻¹`. -/
@[simp]
theorem timeSlice_ofFstEq (t : unitInterval) :
    (ofFstEq Ψ hΨ).timeSlice t = (Ψ.slice hΨ 0).symm.trans (Ψ.slice hΨ t) :=
  Diffeomorph.ext fun x ↦ by
    rw [timeSlice_apply, ofFstEq_apply, Diffeomorph.coe_trans, Function.comp_apply]

/-- The final map of `ofFstEq Ψ hΨ` is `Ψ_1 ∘ Ψ_0⁻¹`. -/
@[simp]
theorem final_ofFstEq : (ofFstEq Ψ hΨ).final = (Ψ.slice hΨ 0).symm.trans (Ψ.slice hΨ 1) := by
  rw [final_def, timeSlice_ofFstEq]

end ofFstEq

/-! ### Invariant sets and restrictions -/

/-- If a diffeotopy fixes every point outside `K` at all times, then each time slice maps `K` into
itself, and so maps every set `U ⊇ K` onto itself: `φ_t x ∈ U ↔ x ∈ U`. -/
theorem apply_mem_iff_of_subset (Φ : Diffeotopy J n M) {K U : Set M} (hKU : K ⊆ U)
    (hΦK : ∀ t, ∀ x ∉ K, Φ (t, x) = x) (t : unitInterval) (x : M) : Φ (t, x) ∈ U ↔ x ∈ U := by
  by_cases hx : x ∈ K
  · -- A point of `K` is not sent outside `K`, where `φ_t` is the identity, as `φ_t` is injective.
    have hΦx : Φ (t, x) ∈ K := by
      by_contra h
      have h' : Φ.timeSlice t (Φ (t, x)) = Φ.timeSlice t x := by
        rw [timeSlice_apply, timeSlice_apply, hΦK t _ h]
      exact h (by rw [(Φ.timeSlice t).injective h']; exact hx)
    exact iff_of_true (hKU hΦx) (hKU hx)
  · rw [hΦK t x hx]

variable (Φ : Diffeotopy J n M) (U : TopologicalSpace.Opens M)
  (hU : ∀ t x, Φ (t, x) ∈ U ↔ x ∈ U)

/-- The restriction of a diffeotopy `Φ` of `M` to an open set `U` that every time slice maps onto
itself, as a diffeotopy of `U`. -/
def subtype : Diffeotopy J n U where
  toDiffeomorph :=
    { toFun := fun p ↦ (p.1, ⟨Φ (p.1, p.2), (hU p.1 p.2).2 p.2.property⟩)
      invFun := fun p ↦ (p.1, ⟨Φ.symm (p.1, p.2),
        (hU p.1 _).1 (by rw [apply_symm_apply_mk]; exact p.2.property)⟩)
      left_inv := fun p ↦ Prod.ext rfl (Subtype.ext (Φ.symm_apply_apply_mk p.1 p.2))
      right_inv := fun p ↦ Prod.ext rfl (Subtype.ext (Φ.apply_symm_apply_mk p.1 p.2))
      contMDiff_toFun := contMDiff_fst.prodMk <| (ContMDiff.subtypeVal_comp_iff U _).1 <|
        Φ.contMDiff.comp (contMDiff_fst.prodMk (contMDiff_subtypeVal.comp contMDiff_snd))
      contMDiff_invFun := contMDiff_fst.prodMk <| (ContMDiff.subtypeVal_comp_iff U _).1 <|
        Φ.symm.contMDiff.comp (contMDiff_fst.prodMk (contMDiff_subtypeVal.comp contMDiff_snd)) }
  fst_apply _ := rfl
  snd_apply_zero' x := Subtype.ext (Φ.apply_zero x)

/-- The restriction `Φ.subtype U hU` moves a point of `U` as `Φ` does. -/
@[simp]
theorem subtype_apply_coe (p : unitInterval × U) : (Φ.subtype U hU p : M) = Φ (p.1, p.2) :=
  (rfl)

end TauCeti.Diffeotopy

end
