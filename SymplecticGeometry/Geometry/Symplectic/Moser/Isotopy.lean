/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Basic
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic
public import TauCeti.Geometry.Manifold.SmoothIsotopy.Basic
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Flow.Family
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.SmoothFamily.Basic
import SymplecticGeometry.Geometry.Manifold.TubularNeighborhood.RelativePoincare
import SymplecticGeometry.Geometry.Symplectic.Moser.Family
import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Extend
import TauCeti.Geometry.Manifold.SmoothIsotopy.Diffeotopy
import TauCeti.Geometry.Symplectic.Manifold.Opens

/-!
# The Moser isotopy fixing a compact submanifold

Let `σ₀`, `σ₁` be closed two-forms on a boundaryless manifold `M` with the same pullback to a
compact embedded submanifold `f : Q → M`, and let `σ_t = σ₀ + t (σ₁ - σ₀)` be the segment between
them. This file builds a compactly supported diffeotopy `Ψ` of `M` with `Ψ_t^* σ_t = σ₀` near
`f(Q)`, for every `t ∈ [0, 1]` at once, and with `Ψ_t` fixing `f(Q)` pointwise, and derives the
relative Moser theorem fixing a submanifold from it.

## Main results

* `TauCeti.SmoothEmbedding.exists_diffeotopy_fix_eventually_mpullback_eq`: the diffeotopy near
  the image of a compact embedded submanifold `f : Q → M`, assuming only `f^* σ₁ = f^* σ₀`. The
  primitive comes from Tau Ceti's relative Poincaré lemma on a tube around `f(Q)`
  (`TauCeti.SmoothEmbedding.exists_isSmoothForm_relative_primitive`, in the form of
  `TauCeti.SmoothEmbedding.exists_smoothForm_relative_primitive_sub`). On the tube, Moser's
  argument along a family
  (`TauCeti.SmoothEmbedding.exists_diffeotopy_fix_eventually_mpullback_eq_of_timeDeriv`,
  in `Moser/Family.lean`) runs for the segment `SmoothForm.lineMapFamily` with that primitive
  constant in time, and the diffeotopy built on the tube is extended by the identity
  (`TauCeti.Diffeotopy.exists_extend_of_isCompact`).
* `TauCeti.SmoothEmbedding.exists_smoothIsotopy_fix_mpullback_eq`: the relative Moser theorem
  fixing a submanifold, with a primitive `σ` of `σ₁ - σ₀` such that `f^* σ = 0`, as a smooth
  isotopy of embeddings of an open neighbourhood `U` of `f(Q)` starting at the inclusion, whose
  time-one map is a diffeomorphism from `U` onto an open set.

The first proof adapts the reduction to a tube in Tau Ceti's
`TauCeti.SmoothTwoForm.exists_diffeomorph_fix_embedding_eventually_mpullback_eq`, and the
restriction of the time-one map to open sets in the second follows
`TauCeti.SmoothTwoForm.exists_diffeomorph_opens_of_eq_along`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §3.2,
  Exercise 3.2.6.
* [A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, Berlin, 2001][CannasdaSilva2001Lectures], Lectures 6–7.
* J. Moser, *On the volume elements on a manifold*, Transactions of the American Mathematical
  Society 120 (1965), 286–294.
-/

public section

noncomputable section

open Bundle Set Filter TauCeti SymplecticGeometry
open scoped Manifold Topology ContDiff

namespace TauCeti.SmoothEmbedding

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [SecondCountableTopology M]
  {E' H' Q : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [J.Boundaryless]
  [TopologicalSpace Q] [ChartedSpace H' Q] [IsManifold J ∞ Q] [CompactSpace Q]

/-- **The Moser diffeotopy fixing a compact submanifold.** Let `σ₀`, `σ₁` be closed two-forms on a
boundaryless second-countable Hausdorff manifold `M` with the same pullback to a compact embedded
submanifold `f : Q → M`, and let every form `σ_s = σ₀ + s (σ₁ - σ₀)`, `s ∈ [0, 1]`, be
nondegenerate at the points of `f(Q)`. Then there is a diffeotopy `Ψ` of `M` which fixes every
point outside a compact set at all times, fixes every point of `f(Q)` at all times, and satisfies
`Ψ_t^* σ_t = σ₀` for every `t ∈ [0, 1]` on one neighbourhood of `f(Q)`. -/
theorem exists_diffeotopy_fix_eventually_mpullback_eq (f : SmoothEmbedding J I ∞ Q M)
    {σ₀ σ₁ : SmoothTwoForm I M} (h₀ : σ₀.IsClosed) (h₁ : σ₁.IsClosed)
    (hf : SmoothForm.mpullback f f.contMDiff σ₁ = SmoothForm.mpullback f f.contMDiff σ₀)
    (hnd : ∀ q, ∀ s ∈ Icc (0 : ℝ) 1,
      ((σ₀ + s • (σ₁ - σ₀)).bilinFormAt (f q)).Nondegenerate) :
    ∃ Ψ : Diffeotopy I ∞ M, (∃ C, IsCompact C ∧ ∀ t, ∀ x ∉ C, Ψ (t, x) = x) ∧
      (∀ t q, Ψ (t, f q) = f q) ∧
      ∀ᶠ x in 𝓝ˢ (range f), ∀ t : unitInterval,
        (SmoothForm.mpullback (Ψ.timeSlice t) (Ψ.timeSlice t).contMDiff
          (σ₀ + (t : ℝ) • (σ₁ - σ₀))).val x = σ₀.val x := by
  -- The relative Poincaré lemma gives a primitive of `σ₁ - σ₀` on a tubular neighbourhood `W` of
  -- `f(Q)`, vanishing along `f(Q)`.
  obtain ⟨W, -, hfW, βW, hdβW, hβW0, -⟩ :=
    f.exists_smoothForm_relative_primitive_sub h₀ h₁ hf isOpen_univ (subset_univ _)
  -- Moser's argument along the segment of the restricted forms, with the primitive `βW` constant
  -- in time, runs on the open submanifold `W`.
  let g := f.codRestrict W fun q ↦ hfW (mem_range_self q)
  have hg (q : Q) : (g q : M) = f q := f.val_codRestrict_apply _ _ q
  set τ₀ := SmoothForm.mpullback (Subtype.val : W → M) contMDiff_subtypeVal σ₀
  set τ₁ := SmoothForm.mpullback (Subtype.val : W → M) contMDiff_subtypeVal σ₁
  have hτ₀ : τ₀.IsClosed := h₀.mpullback _ _
  have hτ : (τ₁ - τ₀).IsClosed := (h₁.mpullback _ _).sub hτ₀
  have hσt (u : ℝ) :
      SmoothForm.mpullback (Prod.mk u) (contMDiff_const.prodMk contMDiff_id)
        (SmoothForm.lineMapFamily τ₀ τ₁ (contDiff_id (n := ∞))) = τ₀ + u • (τ₁ - τ₀) :=
    SmoothForm.mpullback_prodMk_lineMapFamily τ₀ τ₁ _ u
  set γ : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × W) ℝ 1 := SmoothForm.mpullback Prod.snd contMDiff_snd βW
  have hβt (u : ℝ) :
      SmoothForm.mpullback (Prod.mk u) (contMDiff_const.prodMk contMDiff_id) γ = βW :=
    SmoothForm.mpullback_prodMk_mpullback_snd βW u
  obtain ⟨Λ, ⟨C, hC, hΛC⟩, hΛK, hΛ⟩ :=
    g.exists_diffeotopy_fix_eventually_mpullback_eq_of_timeDeriv
    (SmoothForm.lineMapFamily τ₀ τ₁ (contDiff_id (n := ∞)))
    (fun t _ ↦ by rw [hσt]; exact hτ₀.add (hτ.smul t))
    γ
    (Eventually.of_forall fun p ↦ by
      have h := congrArg (fun α : SmoothTwoForm I W ↦ α.val p.2)
        (SmoothForm.mpullback_prodMk_timeDeriv_lineMapFamily τ₀ τ₁ (contDiff_id (n := ∞)) p.1)
      simp only [deriv_id, one_smul] at h
      rw [h, hβt, hdβW])
    (fun t _ ↦ by
      rw [hβt]
      ext q v
      rw [SmoothForm.mpullback_apply, show g q = ⟨f q, hfW (mem_range_self q)⟩ from
        Subtype.ext (hg q), hβW0 q]
      simp)
    (fun t ht q ↦ by
      rw [hσt, ← map_sub, ← map_smul, ← map_add]
      exact (SmoothTwoForm.nondegenerate_bilinFormAt_mpullback_subtype_val_iff (g q)).2
        (hg q ▸ hnd q t ht))
  simp only [hσt, zero_smul, add_zero] at hΛ
  -- Extend the compactly supported diffeotopy of `W` by the identity.
  obtain ⟨Ψ, hΨW, hΨC⟩ := Λ.exists_extend_of_isCompact isLocalDiffeomorph_subtype_val
    W.isOpen.isOpenEmbedding_subtypeVal hC hΛC
  have hcomp (t : unitInterval) :
      ⇑(Ψ.timeSlice t) ∘ (Subtype.val : W → M) = Subtype.val ∘ ⇑(Λ.timeSlice t) :=
    funext fun z ↦ by simp only [Function.comp_apply, Diffeotopy.timeSlice_apply, hΨW]
  refine ⟨Ψ, ⟨Subtype.val '' C, hC.image continuous_subtypeVal, hΨC⟩,
    fun t q ↦ by rw [← hg, hΨW, hΛK], ?_⟩
  -- On `W`, the pullback by `Ψ_t` is the pullback by `Λ_t` of the restricted forms.
  obtain ⟨U, ⟨hU, hKU⟩, hUΛ⟩ := (hasBasis_nhdsSet (range g)).mem_iff.1 hΛ
  refine mem_of_superset ((W.isOpen.isOpenEmbedding_subtypeVal.isOpenMap U hU).mem_nhdsSet.2 ?_)
    ?_
  · rintro _ ⟨q, rfl⟩
    exact ⟨g q, hKU (mem_range_self q), hg q⟩
  · rintro _ ⟨z, hz, rfl⟩ t
    have h := hUΛ hz t
    rw [← map_sub, ← map_smul, ← map_add] at h
    rw [← SmoothForm.coe_mpullback_subtype_val_apply,
      SmoothForm.mpullback_mpullback_of_comp_eq _ _ (Λ.timeSlice t).contMDiff
        contMDiff_subtypeVal (hcomp t)]
    exact h.trans (SmoothForm.coe_mpullback_subtype_val_apply σ₀ z)

open TopologicalSpace in
/-- **The relative Moser theorem fixing a submanifold.** Let `σ₀`, `σ₁` be two-forms on a
boundaryless second-countable Hausdorff manifold `M`, with `σ₀` closed and `σ₁ - σ₀ = dσ` for a
smooth one-form `σ` whose pullback to a compact embedded submanifold `f : Q → M` vanishes, and let
every form `σ_t = σ₀ + t (σ₁ - σ₀)`, `t ∈ [0, 1]`, be nondegenerate at the points of `f(Q)`. (Then
`σ₁` is closed too.) Then there are an open neighbourhood `U` of `f(Q)` and a smooth isotopy of
embeddings `ψ_t : U → M` starting at the inclusion, with `ψ_t` fixing every point of `f(Q)` and
`ψ_t^* σ_t = σ₀` on `U` for every `t ∈ [0, 1]`. Its time-one map `g` is a diffeomorphism from `U`
onto an open set `V`.

For forms given only on an open set `O ⊇ f(Q)`, apply the theorem to the open submanifold `O` and
to `f.codRestrict O`; composing the isotopy with the inclusion of `O` gives one into `M`.

Milestone: *Relative Moser theorem fixing a submanifold*. -/
theorem exists_smoothIsotopy_fix_mpullback_eq (f : SmoothEmbedding J I ∞ Q M)
    {σ₀ σ₁ : SmoothTwoForm I M} (h₀ : σ₀.IsClosed)
    {σ : SmoothForm I M ℝ 1} (hσ : mextDeriv σ.val = (σ₁ - σ₀).val)
    (hfσ : SmoothForm.mpullback f f.contMDiff σ = 0)
    (hnd : ∀ q, ∀ s ∈ Icc (0 : ℝ) 1,
      ((σ₀ + s • (σ₁ - σ₀)).bilinFormAt (f q)).Nondegenerate) :
    ∃ (U : Opens M) (hU : range f ⊆ U) (g : C^∞⟮I, U; I, M⟯)
      (ψ : SmoothIsotopy (SmoothEmbedding.ofOpens (I := I) (n := ∞) U).toContMDiffMap g),
      (∀ t q, ψ (t, ⟨f q, hU (mem_range_self q)⟩) = f q) ∧
      (∀ t : unitInterval, SmoothForm.mpullback (ψ.timeSlice t) (ψ.timeSlice t).contMDiff
          (σ₀ + (t : ℝ) • (σ₁ - σ₀)) =
        SmoothForm.mpullback (Subtype.val : U → M) contMDiff_subtypeVal σ₀) ∧
      ∃ (V : Opens M) (φ : U ≃ₘ⟮I, I⟯ V), ∀ x, (φ x : M) = g x := by
  -- `σ₁ - σ₀ = dσ`, so `σ₁` is closed and `f^*(σ₁ - σ₀) = d(f^*σ) = 0`.
  have hdσ : mextDerivₗ I 1 σ = σ₁ - σ₀ := Subtype.ext ((mextDerivₗ_apply _ _ _).trans hσ)
  have h₁ : σ₁.IsClosed := by
    have h : (σ₁ - σ₀).IsClosed := by
      rw [SmoothForm.isClosed_def, ← hσ, SmoothForm.mextDeriv_mextDeriv]
    simpa only [add_sub_cancel] using h₀.add h
  have hf : SmoothForm.mpullback f f.contMDiff σ₁ = SmoothForm.mpullback f f.contMDiff σ₀ := by
    rw [← sub_eq_zero, ← map_sub, ← hdσ, ← SmoothForm.mextDerivₗ_mpullback, hfσ, map_zero]
  obtain ⟨Ψ, -, hΨf, hΨ⟩ := exists_diffeotopy_fix_eventually_mpullback_eq f h₀ h₁ hf hnd
  obtain ⟨U, ⟨hU, hfU⟩, hUΨ⟩ := (hasBasis_nhdsSet (range f)).mem_iff.1 hΨ
  let U' : Opens M := ⟨U, hU⟩
  let V : Opens M := ⟨Ψ.final.symm ⁻¹' U, hU.preimage Ψ.final.symm.continuous⟩
  have hUV (x : M) : x ∈ U' ↔ Ψ.final x ∈ V := by
    rw [Opens.mem_mk, Opens.mem_mk, mem_preimage, Diffeomorph.symm_apply_apply]
  let ψ := Ψ.smoothIsotopy _ (SmoothEmbedding.ofOpens (I := I) (n := ∞) U').isSmoothEmbedding
  refine ⟨U', hfU, _, ψ, fun t q ↦ by simpa [ψ] using hΨf t q, fun t ↦ ?_, V,
    Ψ.final.subtype hUV, fun x ↦ ?_⟩
  · have hψ : ⇑(ψ.timeSlice t) = ⇑(Ψ.timeSlice t) ∘ Subtype.val := by
      funext x
      simp [ψ]
    apply Subtype.ext
    funext z
    rw [SmoothForm.coe_mpullback, hψ,
      ← SmoothForm.coe_mpullback _ ((Ψ.timeSlice t).contMDiff.comp contMDiff_subtypeVal),
      ← SmoothForm.mpullback_mpullback _ _ contMDiff_subtypeVal,
      SmoothForm.coe_mpullback_subtype_val_apply,
      SmoothForm.coe_mpullback_subtype_val_apply]
    exact hUΨ z.property t
  · simp

end TauCeti.SmoothEmbedding
