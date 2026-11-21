/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Closed
import TauCeti.Geometry.Manifold.TubularNeighborhood.RelativePoincare
import TauCeti.Geometry.Manifold.SmoothEmbedding.LocalDiffeomorph
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.LocalDiffeomorph
import TauCeti.Geometry.Manifold.DifferentialForm.Opens

/-!
# Primitives with prescribed pullback near an embedded submanifold

Let `f : M → N` be a smooth embedding of boundaryless finite-dimensional manifolds, with `N`
Hausdorff and second countable, let `θ` be a closed smooth `(k + 1)`-form on `N`, and let `β` be a
smooth `k`-form on `M` with `dβ = f^* θ`. Then on an open neighbourhood of the image of `f`,
`θ` has a smooth primitive whose pullback along `f` is `β`
(`TauCeti.SmoothEmbedding.exists_mextDeriv_eq_and_mpullback_eq`). For `β = 0` this is Tau Ceti's
relative Poincaré lemma `TauCeti.SmoothEmbedding.exists_isSmoothForm_relative_primitive`.

The proof follows the converse half of McDuff–Salamon's Proposition 3.5.31: a smooth retraction
`ρ` onto the image (`TauCeti.SmoothEmbedding.exists_contMDiffOn_retraction`) extends `β` to
`ρ^* β`; the form `θ - d(ρ^* β)` is closed with zero pullback along `f`, so the relative Poincaré
lemma gives a primitive `μ` of it vanishing along `f`, and `ρ^* β + μ` is the primitive sought.
Both steps live on open submanifolds of `N`. The primitive is extended by zero to `N`; near the
image its regularity and exterior derivative are those of its restrictions to these open
submanifolds, whose inclusions are local diffeomorphisms
(`IsLocalDiffeomorphAt.contMDiffAt_mpullback_form_iff`, `TauCeti.mpullback_mextDeriv_at`).

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Proposition 3.5.31.
-/

public section

open Bundle Manifold Set
open scoped ContDiff Manifold

namespace TauCeti.SmoothEmbedding

variable {E V H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ V G}
  [I.Boundaryless] [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
  [T2Space N] [SecondCountableTopology N]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- **Primitives with prescribed pullback near an embedded submanifold.** Let `f : M → N` be a
smooth embedding, `θ` a closed smooth `(k + 1)`-form on `N` and `β` a smooth `k`-form on `M` with
`dβ = f^* θ`. Then there are an open neighbourhood `U` of the image of `f` and a `k`-form `γ` on
`N`, smooth at every point of `U`, with `dγ = θ` on `U` and `f^* γ = β`. -/
theorem exists_mextDeriv_eq_and_mpullback_eq (f : SmoothEmbedding I J ∞ M N) {k : ℕ}
    {θ : SmoothForm J N F (k + 1)} (hθ : θ.IsClosed) {β : SmoothForm I M F k}
    (hβ : mextDerivₗ I k β = SmoothForm.mpullback f f.contMDiff θ) :
    ∃ U : Set N, IsOpen U ∧ range f ⊆ U ∧ ∃ γ : RoughForm J N F k,
      (∀ x ∈ U, ContMDiffAt J (J.prod 𝓘(ℝ, V [⋀^Fin k]→L[ℝ] F)) ∞
        (fun y ↦ TotalSpace.mk' (V [⋀^Fin k]→L[ℝ] F) y (γ y)) x) ∧
      (∀ x ∈ U, mextDeriv γ x = θ.val x) ∧ mpullback I J f γ = β.val := by
  rcases isEmpty_or_nonempty M with hM | hM
  · exact ⟨∅, isOpen_empty, by simp [range_eq_empty], 0, by simp, by simp,
      funext fun x ↦ isEmptyElim x⟩
  obtain ⟨W, hW, hfW, -, r, hr, hrf⟩ := f.exists_contMDiffOn_retraction isOpen_univ (subset_univ _)
  -- Work on the open submanifold `T = W`, where `r` is a smooth retraction.
  let T : TopologicalSpace.Opens N := ⟨W, hW⟩
  have hval : ContMDiff J J ∞ (Subtype.val : T → N) := contMDiff_subtypeVal
  let ρ : T → M := fun y ↦ r y
  have hρ : ContMDiff J I ∞ ρ := fun y ↦
    ((hr _ y.property).contMDiffAt (hW.mem_nhds y.property)).comp y hval.contMDiffAt
  have hfT : ∀ x, f x ∈ T := fun x ↦ hfW (mem_range_self x)
  let j := f.codRestrict T hfT
  have hjd : MDifferentiable I J j := j.contMDiff.mdifferentiable (by simp)
  have hvj : Subtype.val ∘ j = f := f.val_comp_codRestrict T hfT
  have hρj : ρ ∘ j = _root_.id := funext fun x ↦
    (congrArg r (f.val_codRestrict_apply T hfT x)).trans (hrf x)
  -- The closed form `η = θ - d(ρ^* β)` on `T` pulls back to zero along `j`.
  let βT := SmoothForm.mpullback ρ hρ β
  let η := SmoothForm.mpullback Subtype.val hval θ - mextDerivₗ J k βT
  have hdη : mextDeriv η.val = 0 :=
    (SmoothForm.isClosed_def η).1 ((hθ.mpullback _ hval).sub (SmoothForm.isClosed_mextDerivₗ βT))
  have hjβT : mpullback (F := F) I J j βT.val = β.val := by
    rw [SmoothForm.coe_mpullback, ← mpullback_comp hjd (hρ.mdifferentiable (by simp)), hρj,
      mpullback_id]
  have hjdβT : mpullback (F := F) I J j (mextDerivₗ J k βT).val = (mextDerivₗ I k β).val := by
    rw [← SmoothForm.coe_mpullback _ j.contMDiff, ← SmoothForm.mextDerivₗ_mpullback,
      mextDerivₗ_apply, mextDerivₗ_apply, SmoothForm.coe_mpullback, hjβT]
  have hjη : mpullback (F := F) I J j η.val = 0 := by
    rw [Submodule.coe_sub, mpullback_sub, hjdβT, hβ, SmoothForm.coe_mpullback,
      SmoothForm.coe_mpullback, ← mpullback_comp hjd (hval.mdifferentiable (by simp)), hvj,
      sub_self]
  -- The relative Poincaré lemma on `T` gives a primitive `μ` of `η` vanishing along `j`.
  obtain ⟨W', -, hjW', hprim⟩ := j.exists_isSmoothForm_relative_primitive (F := F) isOpen_univ
    (subset_univ _)
  obtain ⟨μ, hμ, hdμ, hμ0, -⟩ := hprim (le_top : (1 : ℕ∞) ≤ ⊤) η.isSmoothForm hdη hjη
  -- On `W'`, the form `ξ = ρ^* β + μ` is a smooth primitive of `θ`.
  have hval' : ContMDiff J J ∞ (Subtype.val : W' → T) := contMDiff_subtypeVal
  let μS : SmoothForm J W' F k := ⟨μ, hμ.mem_smoothBundleForms⟩
  let ξ := SmoothForm.mpullback Subtype.val hval' βT + μS
  have hdξ : (mextDerivₗ J k ξ).val =
      mpullback (F := F) J J (Subtype.val : W' → T)
        (SmoothForm.mpullback Subtype.val hval θ).val := by
    rw [map_add, SmoothForm.mextDerivₗ_mpullback, Submodule.coe_add, mextDerivₗ_apply,
      SmoothForm.coe_mpullback, show μS.val = μ from rfl, hdμ, ← mpullback_add]
    congr 1
    exact congrArg Subtype.val
      (add_sub_cancel (mextDerivₗ J k βT) (SmoothForm.mpullback Subtype.val hval θ))
  -- Extend `ξ` by zero from `W'` to `N`.
  classical
  let γ : RoughForm J N F k := fun y ↦
    if hy : y ∈ W then if hy' : (⟨y, hy⟩ : T) ∈ W' then ξ.val ⟨⟨y, hy⟩, hy'⟩ else 0 else 0
  have hγ : mpullback (F := F) J J (Subtype.val : W' → T)
      (mpullback J J (Subtype.val : T → N) γ) = ξ.val := funext fun w ↦ by
    rw [mpullback_subtype_val_apply, mpullback_subtype_val_apply]
    exact (dite_eq_left_of_eq_true (eq_true (w : T).property)).trans
      (dite_eq_left_of_eq_true (eq_true w.property))
  -- Both restrictions of `γ` are smooth at the points of `W'`.
  have hγs (w : W') :
      ContMDiffAt J (J.prod 𝓘(ℝ, V [⋀^Fin k]→L[ℝ] F)) ∞
        (fun y ↦ TotalSpace.mk' (V [⋀^Fin k]→L[ℝ] F) y
          (mpullback J J (Subtype.val : T → N) γ y)) (w : T) ∧
      ContMDiffAt J (J.prod 𝓘(ℝ, V [⋀^Fin k]→L[ℝ] F)) ∞
        (fun y ↦ TotalSpace.mk' (V [⋀^Fin k]→L[ℝ] F) y (γ y)) ((w : T) : N) := by
    have h₁ := ((isLocalDiffeomorph_subtype_val (n := ∞) (U := W') w).contMDiffAt_mpullback_form_iff
      (m := ∞) (by simp)).1 (by rw [hγ]; exact ξ.contMDiff w)
    have h₂ := isLocalDiffeomorph_subtype_val (I := J) (n := ∞) (U := T) (w : T)
    exact ⟨h₁, (h₂.contMDiffAt_mpullback_form_iff (m := ∞) (by simp)).1 h₁⟩
  refine ⟨Subtype.val '' (W' : Set T), hW.isOpenMap_subtypeVal _ W'.isOpen,
    fun _ ⟨x, hx⟩ ↦ ⟨j x, hjW' (mem_range_self x), hx ▸ congrFun hvj x⟩, γ,
    fun _ ⟨t, ht, h⟩ ↦ h ▸ (hγs ⟨t, ht⟩).2, ?_, ?_⟩
  · rintro _ ⟨t, ht, rfl⟩
    obtain ⟨hs₁, hs₂⟩ := hγs ⟨t, ht⟩
    have h₁ := mpullback_mextDeriv_at (hval t |>.of_le (by simp)) (hs₂.of_le (by simp))
    have h₂ := mpullback_mextDeriv_at (hval' ⟨t, ht⟩ |>.of_le (by simp)) (hs₁.of_le (by simp))
    have e₁ : mextDeriv γ t = mextDeriv (mpullback J J (Subtype.val : T → N) γ) t :=
      (mpullback_subtype_val_apply _ t).symm.trans h₁
    have e₂ : mextDeriv (mpullback J J (Subtype.val : T → N) γ) t = θ.val t := by
      refine (mpullback_subtype_val_apply _ (⟨t, ht⟩ : W')).symm.trans (h₂.trans ?_)
      rw [hγ, ← mextDerivₗ_apply, hdξ, mpullback_subtype_val_apply, SmoothForm.coe_mpullback,
        mpullback_subtype_val_apply]
    exact e₁.trans e₂
  · have hj' : ∀ x, j x ∈ W' := fun x ↦ hjW' (mem_range_self x)
    let j' := j.codRestrict W' hj'
    have hf' : f = (Subtype.val ∘ Subtype.val) ∘ j' := by
      rw [Function.comp_assoc, j.val_comp_codRestrict W' hj', hvj]
    have hμj : mpullback (F := F) I J j' μ = 0 := by
      funext x
      ext v
      rw [mpullback_apply, show j' x = ⟨j x, hj' x⟩ from Subtype.ext (j.val_codRestrict_apply ..),
        hμ0]
      simp
    rw [hf', mpullback_comp (j'.contMDiff.mdifferentiable (by simp))
      ((hval.comp hval').mdifferentiable (by simp)), mpullback_comp
      (hval'.mdifferentiable (by simp)) (hval.mdifferentiable (by simp)), hγ,
      Submodule.coe_add, mpullback_add, show μS.val = μ from rfl, hμj, add_zero,
      SmoothForm.coe_mpullback, ← mpullback_comp (j'.contMDiff.mdifferentiable (by simp))
      (hval'.mdifferentiable (by simp)), j.val_comp_codRestrict W' hj', hjβT]

end TauCeti.SmoothEmbedding

end
