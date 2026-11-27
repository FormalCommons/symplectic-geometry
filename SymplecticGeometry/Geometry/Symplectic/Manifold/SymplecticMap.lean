/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.SymplecticMap
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import SymplecticGeometry.Topology.Algebra.Module.Alternating.Basic
import TauCeti.Geometry.Manifold.DifferentialForm.Opens.PartialDiffeomorph

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
`TauCeti.SmoothTwoForm.isSymplectomorphism_setCongr`, for `Diffeomorph.setCongr`, the
identity between equal open subsets; and, composing the first two,
`TauCeti.SmoothTwoForm.IsSymplectomorphism.restrOpens`, for `Diffeomorph.restrOpens`,
a symplectomorphism between open subsets restricted to smaller open subsets. A partial
diffeomorphism that is symplectic on its source is a symplectomorphism from its
source onto its target, for Tau Ceti's `PartialDiffeomorph.toDiffeomorphSourceTarget`
(`TauCeti.SmoothTwoForm.IsSymplecticMapOn.isSymplectomorphism_toDiffeomorphSourceTarget`).

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
    rw [TauCeti.mpullback_apply_pair, ← h']

/-! ### Restriction to open subsets -/

section Opens

open TopologicalSpace

/-- **Restricting a symplectomorphism to open sets.** If a diffeomorphism `φ : M ≃ M'` is a
symplectomorphism from `σ` to `σ'` and maps the open set `U` of `M` onto the open set `U'` of
`M'`, its restriction `U ≃ U'` is a symplectomorphism from the restriction of `σ` to `U` to the
restriction of `σ'` to `U'`. -/
theorem IsSymplectomorphism.subtype {φ : M ≃ₘ⟮I, I'⟯ M'} (hφ : σ.IsSymplectomorphism σ' φ)
    {U : TopologicalSpace.Opens M} {U' : TopologicalSpace.Opens M'} (h : ∀ x, x ∈ U ↔ φ x ∈ U') :
    SmoothTwoForm.IsSymplectomorphism (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal σ)
      (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal σ') (φ.subtype h) := by
  rw [isSymplectomorphism_iff_mpullback_eq] at hφ ⊢
  rw [SmoothForm.mpullback_mpullback_of_comp_eq _ _ contMDiff_subtypeVal φ.contMDiff
    (funext (φ.subtype_apply_coe h)), hφ]

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

/-- For equal open subsets `U = V` of `M`, the identity `Diffeomorph.setCongr` from `U` to `V`
is a symplectomorphism from the restriction of `σ` to `U` to its restriction to `V`. -/
theorem isSymplectomorphism_setCongr (σ : SmoothTwoForm I M) {U V : Opens M} (h : U = V) :
    IsSymplectomorphism (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal σ)
      (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal σ)
      (Diffeomorph.setCongr (I := I) (n := ∞) h) := by
  rw [Diffeomorph.setCongr_def]
  exact (isSymplectomorphism_refl σ).subtype _

/-- **Restricting a symplectomorphism between open subsets.** Let `Φ` be a symplectomorphism from
`σ|U₀` to `σ'|V₀`, for open subsets `U₀` of `M` and `V₀` of `M'`, and let `U ≤ U₀` and `V ≤ V₀` be
open subsets that correspond under `Φ`. Then its restriction `Diffeomorph.restrOpens`, the
diffeomorphism from `U` onto `V` that takes the values of `Φ`, is a symplectomorphism from `σ|U`
to `σ'|V`. -/
theorem IsSymplectomorphism.restrOpens {U₀ U : Opens M} {V₀ V : Opens M'}
    {Φ : U₀ ≃ₘ⟮I, I'⟯ V₀}
    (hΦ : IsSymplectomorphism (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal σ)
      (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal σ') Φ)
    (hU : U ≤ U₀) (hV : V ≤ V₀) (h : ∀ x : U₀, (x : M) ∈ U ↔ (Φ x : M') ∈ V) :
    IsSymplectomorphism (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal σ)
      (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal σ') (Φ.restrOpens hU hV h) := by
  rw [Diffeomorph.restrOpens_def]
  exact ((isSymplectomorphism_nestedOpen σ hU).symm (by simp)).trans
    ((hΦ.subtype _).trans (isSymplectomorphism_nestedOpen σ' hV) (by simp)) (by simp)

/-- **A partial diffeomorphism symplectic on its source is a symplectomorphism of open subsets.**
If a partial diffeomorphism `Φ` from `M` to `M'` is a symplectic map from `σ` to `σ'` on its
source, then `Φ.toDiffeomorphSourceTarget`, from the source of `Φ` onto its target, is a
symplectomorphism from the restriction of `σ` to the source to the restriction of `σ'` to the
target. -/
theorem IsSymplecticMapOn.isSymplectomorphism_toDiffeomorphSourceTarget
    {Φ : PartialDiffeomorph I I' M M' ∞} (h : σ.IsSymplecticMapOn σ' Φ Φ.source) :
    IsSymplectomorphism (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal σ)
      (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal σ') Φ.toDiffeomorphSourceTarget := by
  rw [isSymplectomorphism_iff_mpullback_eq]
  exact (SmoothForm.mpullback_toDiffeomorphSourceTarget_eq_iff _).2 fun _ hx ↦
    h.mpullback_apply hx

end Opens

end TauCeti.SmoothTwoForm

end
