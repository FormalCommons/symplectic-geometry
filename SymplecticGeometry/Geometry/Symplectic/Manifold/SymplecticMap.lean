/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
public import TauCeti.Geometry.Symplectic.Manifold.SymplecticMap
import SymplecticGeometry.Topology.Algebra.Module.Alternating.Basic

/-!
# Symplectic maps on a set, and on open subsets

A map `φ` that is symplectic on a set `s` from `σ` to `σ'`, in the sense of Tau Ceti's
`TauCeti.SmoothTwoForm.IsSymplecticMapOn`, pulls `σ'` back to `σ` at each point of `s`
(`TauCeti.SmoothTwoForm.IsSymplecticMapOn.mpullback_apply`). This is the pointwise form, on a
set and with no regularity of `φ`, of Tau Ceti's
`TauCeti.SmoothTwoForm.isSymplecticMap_iff_mpullback_eq`.

Symplectomorphisms restrict to open subsets that correspond under them, for the restricted forms:
`TauCeti.SmoothTwoForm.IsSymplectomorphism.subtype`, for Tau Ceti's `Diffeomorph.subtype`;
`TauCeti.SmoothTwoForm.isSymplectomorphism_nestedOpen`, for Tau Ceti's `Diffeomorph.nestedOpen`;
and, composing the two, `TauCeti.SmoothTwoForm.IsSymplectomorphism.subtype_nestedOpen`, for a
symplectomorphism between open subsets restricted to smaller open subsets.

## References

* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 3.1.
-/

public section

open scoped ContDiff Manifold

namespace TauCeti.SmoothTwoForm

variable {E H M E' H' M' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']
  {σ : SmoothTwoForm I M} {σ' : SmoothTwoForm I' M'} {φ : M → M'} {s : Set M}

/-- A symplectic map on `s` from `σ` to `σ'` pulls `σ'` back to `σ` at each point of `s`. -/
theorem IsSymplecticMapOn.mpullback_apply (h : σ.IsSymplecticMapOn σ' φ s) {x : M}
    (hx : x ∈ s) : TauCeti.mpullback I I' φ σ'.val x = σ.val x :=
  ContinuousAlternatingMap.ext_fin_two fun v w ↦ by
    have h' := h.apply hx v w
    rw [SmoothBundleForm.eval₂_apply, SmoothBundleForm.eval₂_apply] at h'
    rw [TauCeti.mpullback_apply, ← h']
    exact congrArg _ (funext fun i ↦ by fin_cases i <;> simp)


/-! ### Restriction to open subsets -/

section Opens

open TopologicalSpace

/-- **Restricting a symplectomorphism to open subsets.** A symplectomorphism `Φ` from `σ` to `σ'`
restricts to a symplectomorphism `Φ.subtype h` from `σ|U` to `σ'|V`, for open subsets `U` and
`V` that correspond under `Φ`. -/
theorem IsSymplectomorphism.subtype {Φ : M ≃ₘ⟮I, I'⟯ M'} (hΦ : σ.IsSymplectomorphism σ' Φ)
    {U : Opens M} {V : Opens M'} (h : ∀ x, x ∈ U ↔ Φ x ∈ V) :
    IsSymplectomorphism (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal σ)
      (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal σ') (Φ.subtype h) := by
  rw [isSymplectomorphism_iff_mpullback_eq] at hΦ ⊢
  rw [SmoothForm.mpullback_mpullback_of_comp_eq _ _ contMDiff_subtypeVal Φ.contMDiff
    (funext fun x ↦ Diffeomorph.subtype_apply_coe Φ h x), hΦ]

/-- For open subsets `U ≤ D` of `M`, Tau Ceti's `Diffeomorph.nestedOpen`, from the preimage of `U`
in `D` onto `U`, is a symplectomorphism from the restriction of `σ|D` to `σ|U`. -/
theorem isSymplectomorphism_nestedOpen (σ : SmoothTwoForm I M) {U D : Opens M} (h : U ≤ D) :
    IsSymplectomorphism
      (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal
        (SmoothForm.mpullback (Subtype.val : D → M) contMDiff_subtypeVal σ))
      (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal σ)
      (Diffeomorph.nestedOpen (I := I) (n := ∞) h) := by
  rw [isSymplectomorphism_iff_mpullback_eq]
  exact SmoothForm.mpullback_mpullback_of_comp_eq _ _ contMDiff_subtypeVal contMDiff_subtypeVal
    (funext fun x ↦ by simp only [Function.comp_apply, Diffeomorph.nestedOpen_apply]) σ

/-- **Restricting a symplectomorphism between open subsets.** Let `Φ` be a symplectomorphism from
`σ|U₀` to `σ'|V₀`, for open subsets `U₀` of `M` and `V₀` of `M'`, and let `U ≤ U₀` and `V ≤ V₀` be
open subsets that correspond under `Φ`. Then its restriction, the diffeomorphism from `U` onto `V`
built from `Diffeomorph.subtype` and `Diffeomorph.nestedOpen`, is a symplectomorphism from `σ|U`
to `σ'|V`. -/
theorem IsSymplectomorphism.subtype_nestedOpen {U₀ U : Opens M} {V₀ V : Opens M'}
    {Φ : U₀ ≃ₘ⟮I, I'⟯ V₀}
    (hΦ : IsSymplectomorphism (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal σ)
      (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal σ') Φ)
    (hU : U ≤ U₀) (hV : V ≤ V₀)
    (h : ∀ x, x ∈ Opens.comap ⟨Subtype.val, continuous_subtypeVal⟩ U ↔
      Φ x ∈ Opens.comap ⟨Subtype.val, continuous_subtypeVal⟩ V) :
    IsSymplectomorphism (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal σ)
      (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal σ')
      ((Diffeomorph.nestedOpen hU).symm.trans ((Φ.subtype h).trans (Diffeomorph.nestedOpen hV))) :=
  ((isSymplectomorphism_nestedOpen σ hU).symm (by simp)).trans
    ((hΦ.subtype h).trans (isSymplectomorphism_nestedOpen σ' hV) (by simp)) (by simp)

end Opens

end TauCeti.SmoothTwoForm

end
