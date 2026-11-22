/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Moser.Field
public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Basic
public import TauCeti.Geometry.Manifold.SmoothIsotopy.Basic
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.SmoothFamily.Basic
import SymplecticGeometry.Geometry.Manifold.TubularNeighborhood.RelativePoincare
import SymplecticGeometry.Geometry.Symplectic.Manifold.Family
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Flow.Family
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Pullback.Family
import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Extend
import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Flow
import TauCeti.Geometry.Manifold.PartitionOfUnity.Compact
import TauCeti.Geometry.Manifold.SmoothIsotopy.Diffeotopy
import TauCeti.Geometry.Symplectic.Manifold.Opens

/-!
# The Moser isotopy fixing a compact submanifold

Let `σ₀`, `σ₁` be closed two-forms on a boundaryless manifold `M` and let `σ_t = σ₀ + t (σ₁ - σ₀)`
be the segment between them. This file builds a compactly supported diffeotopy `Ψ` of `M` with
`Ψ_t^* σ_t = σ₀` near a compact set or a compact embedded submanifold, for every `t ∈ [0, 1]` at
once, and with `Ψ_t` fixing that set pointwise. The diffeotopy is the flow from time `0` of the
cut-off Moser field `SymplecticGeometry.moserField`, which solves `ι_{X_t} σ_t = -β` near the set
for a primitive `β` of `σ₁ - σ₀` vanishing along it.

## Main results

* `TauCeti.SmoothTwoForm.exists_diffeotopy_fix_eventually_mpullback_eq_of_mextDeriv_eq_sub`: the
  diffeotopy near a compact set `K`, given a global primitive `β` of `σ₁ - σ₀` vanishing on `K`
  and nondegeneracy of `σ_s` along `K` for `s ∈ [0, 1]`.
* `TauCeti.SmoothEmbedding.exists_diffeotopy_fix_eventually_mpullback_eq`: the diffeotopy near
  the image of a compact embedded submanifold `f : Q → M`, assuming only `f^* σ₁ = f^* σ₀`. The
  primitive comes from Tau Ceti's relative Poincaré lemma on a tube around `f(Q)`
  (`TauCeti.SmoothEmbedding.exists_isSmoothForm_relative_primitive`, in the form of
  `TauCeti.SmoothEmbedding.exists_smoothForm_relative_primitive_sub`); the diffeotopy built on
  the tube is extended by the identity (`TauCeti.Diffeotopy.exists_extend_of_isCompact`).
* `TauCeti.SmoothEmbedding.exists_smoothIsotopy_fix_mpullback_eq`: the relative Moser theorem
  fixing a submanifold, with a primitive `σ` of `σ₁ - σ₀` such that `f^* σ = 0`, as a smooth
  isotopy of embeddings of an open neighbourhood `U` of `f(Q)` starting at the inclusion, whose
  time-one map is a diffeomorphism from `U` onto an open set.

The first proof adapts Tau Ceti's
`TauCeti.SmoothTwoForm.exists_diffeomorph_fix_eventually_mpullback_eq_of_mextDeriv_eq_sub`
(`TauCeti/Geometry/Symplectic/Manifold/RelativeMoser.lean`), whose trajectory argument it runs
for every time `t ∈ [0, 1]` along the linear segment instead of for time one along a
reparametrized one. The second adapts the reduction to a tube in Tau Ceti's
`TauCeti.SmoothTwoForm.exists_diffeomorph_fix_embedding_eventually_mpullback_eq`, and the
restriction of the time-one map to open sets in the third follows
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

namespace TauCeti.SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

/-- **The Moser diffeotopy relative to a compact set, with a given primitive.** Let `σ₀`, `σ₁` be
two-forms on a boundaryless Hausdorff manifold, with `σ₀` closed and `σ₁ - σ₀ = dβ` for a smooth
one-form `β`. Let `K` be a compact set on which `β` vanishes and at whose points every form
`σ_s = σ₀ + s (σ₁ - σ₀)`, `s ∈ [0, 1]`, is nondegenerate. Then there is a diffeotopy `Ψ` which
fixes every point outside a compact set at all times, fixes every point of `K` at all times, and
satisfies `Ψ_t^* σ_t = σ₀` for every `t ∈ [0, 1]` on one neighbourhood of `K`. -/
theorem exists_diffeotopy_fix_eventually_mpullback_eq_of_mextDeriv_eq_sub
    {σ₀ σ₁ : SmoothTwoForm I M} (h₀ : σ₀.IsClosed) {β : SmoothForm I M ℝ 1}
    (hβ : mextDeriv β.val = (σ₁ - σ₀).val)
    {K : Set M} (hK : IsCompact K) (hβK : ∀ x ∈ K, β.val x = 0)
    (hnd : ∀ x ∈ K, ∀ s ∈ Icc (0 : ℝ) 1, ((σ₀ + s • (σ₁ - σ₀)).bilinFormAt x).Nondegenerate) :
    ∃ Ψ : Diffeotopy I ∞ M, (∃ C, IsCompact C ∧ ∀ t, ∀ x ∉ C, Ψ (t, x) = x) ∧
      (∀ t, ∀ x ∈ K, Ψ (t, x) = x) ∧
      ∀ᶠ x in 𝓝ˢ K, ∀ t : unitInterval,
        (SmoothForm.mpullback (Ψ.timeSlice t) (Ψ.timeSlice t).contMDiff
          (σ₀ + (t : ℝ) • (σ₁ - σ₀))).val x = σ₀.val x := by
  -- The points `(s, x)` at which `σ_s = σ₀ + s (σ₁ - σ₀)` is nondegenerate form an open set.
  set O := {p : ℝ × M | ((σ₀ + p.1 • (σ₁ - σ₀)).flat p.2).IsInvertible}
  have hO : IsOpen O := isOpen_setOf_isInvertible_flat_add_smul_sub σ₀ σ₁
  have hKO : Icc (0 : ℝ) 1 ×ˢ K ⊆ O := fun p hp ↦ isInvertible_flat_iff.2 (hnd _ hp.2 _ hp.1)
  have hIK : IsCompact (Icc (0 : ℝ) 1 ×ˢ K) := isCompact_Icc.prod hK
  obtain ⟨ρ, hρ, hρ1, hρc, hρO, -⟩ :=
    hIK.exists_contMDiff_one_nhds_tsupport_subset (𝓘(ℝ, ℝ).prod I) hO hKO
  set σ := SmoothForm.lineMapFamily σ₀ σ₁ (contDiff_id (n := ∞))
  set β' : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) ℝ 1 :=
    SmoothForm.mpullback Prod.snd contMDiff_snd β
  have hσt (u : ℝ) :
      SmoothForm.mpullback (Prod.mk u) (contMDiff_const.prodMk contMDiff_id) σ =
        σ₀ + u • (σ₁ - σ₀) :=
    SmoothForm.mpullback_prodMk_lineMapFamily σ₀ σ₁ _ u
  have hβt (u : ℝ) :
      SmoothForm.mpullback (Prod.mk u) (contMDiff_const.prodMk contMDiff_id) β' = β :=
    SmoothForm.mpullback_prodMk_mpullback_snd u β
  have hinv : ∀ p ∈ tsupport ρ, (SmoothTwoForm.flat
      (SmoothForm.mpullback (Prod.mk p.1) (contMDiff_const.prodMk contMDiff_id) σ)
        p.2).IsInvertible :=
    fun p hp ↦ by rw [hσt]; exact hρO hp
  have hX := contMDiff_moserField σ β' hρ hinv
  have hX₁ := hX.of_le (m := 1) (by simp)
  set C := Prod.snd '' tsupport ρ
  have hC : IsCompact C := hρc.isCompact.image continuous_snd
  have hXC (u : ℝ) (y : M) (hy : y ∉ C) : moserField σ β' ρ u y = 0 :=
    moserField_eq_zero_of_notMem_tsupport fun h ↦ hy ⟨_, h, rfl⟩
  have hXK (u : ℝ) (x : M) (hx : x ∈ K) : moserField σ β' ρ u x = 0 :=
    moserField_eq_zero_of_apply_eq_zero (by rw [hβt]; exact hβK x hx)
  have hc := isCompleteVectorField_timeDependentSuspensionField hX₁ hC hXC
  let Ψ := timeDependentFlowDiffeotopy (by simp) hX hc
  have hΨ (t : unitInterval) :
      ⇑(Ψ.timeSlice t) = timeDependentFlowOf (moserField σ β' ρ) 0 t := by
    funext x
    rw [Diffeotopy.timeSlice_apply, timeDependentFlowDiffeotopy_apply]
  have hzero (x : M) (hx : ∀ u, moserField σ β' ρ u x = 0) (s t : ℝ) :
      timeDependentFlowOf (moserField σ β' ρ) s t x = x :=
    timeDependentFlowOf_eq_self_of_forall_eq_zero hX₁ hx s t
  refine ⟨Ψ, ⟨C, hC, fun t x hx ↦ timeDependentFlowDiffeotopy_apply_of_forall_eq_zero _ _ _
    (fun u ↦ hXC u x hx) t⟩, fun t x hx ↦ timeDependentFlowDiffeotopy_apply_of_forall_eq_zero _ _ _
    (fun u ↦ hXK u x hx) t, ?_⟩
  -- `S`: the points near which `ρ = 1` and `σ_s` is nondegenerate, where Moser's equation holds.
  set S := {p : ℝ × M | ∀ᶠ q in 𝓝 p, ρ q = 1 ∧ ((σ₀ + q.1 • (σ₁ - σ₀)).flat q.2).IsInvertible}
  have hKS : Icc (0 : ℝ) 1 ×ˢ K ⊆ S := fun p hp ↦
    ((eventually_nhdsSet_iff_forall.1 hρ1) p hp).and (hO.mem_nhds (hKO hp))
  -- The trajectories starting near `K` stay in `S` up to time `1`.
  have hφ : Continuous fun p : ℝ × M ↦
      (p.1, timeDependentFlowOf (moserField σ β' ρ) 0 p.1 p.2) :=
    continuous_fst.prodMk ((contMDiff_timeDependentFlowOf hc le_top hX).comp
      ((contMDiff_const.prodMk contMDiff_fst).prodMk contMDiff_snd)).continuous
  have hT : IsOpen {p : ℝ × M |
      (p.1, timeDependentFlowOf (moserField σ β' ρ) 0 p.1 p.2) ∈ S} :=
    isOpen_setOfPred_eventually_nhds.preimage hφ
  obtain ⟨u, W, -, hW, hu, hKW, huW⟩ := generalized_tube_lemma isCompact_Icc hK hT
    fun p hp ↦ by
      rw [mem_ofPred_eq, hzero p.2 (fun u ↦ hXK u p.2 hp.2)]
      exact hKS ⟨hp.1, hp.2⟩
  -- Moser's equation holds at every point `(s, y)` of `S`.
  have hrate (s : ℝ) (y : M) (hy : (s, y) ∈ S) :
      (mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk s)
          (mlieDerivForm (fun _ ↦ ((1 : ℝ), (0 : E))) σ.val) +
        mlieDerivForm (moserField σ β' ρ s) (mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk s) σ.val))
          y = 0 := by
    -- The slices `σ₀ + u (σ₁ - σ₀)` have velocity `σ₁ - σ₀`.
    have hvel : (SmoothForm.mpullback (Prod.mk s) (contMDiff_const.prodMk contMDiff_id)
        σ.timeDeriv).val y = (σ₁ - σ₀).val y := by
      have h := congrArg (fun α : SmoothTwoForm I M ↦ α.val y)
        (SmoothForm.mpullback_prodMk_timeDeriv_lineMapFamily σ₀ σ₁ (contDiff_id (n := ∞)) s)
      simpa only [deriv_id, one_smul] using h
    -- The slice at time `s` is closed, since `σ₁ - σ₀ = dβ`.
    have hclosed : mextDeriv
        (SmoothForm.mpullback (Prod.mk s) (contMDiff_const.prodMk contMDiff_id) σ).val y = 0 := by
      have h₁ : (σ₁ - σ₀).IsClosed := by
        rw [SmoothForm.isClosed_def, ← hβ, SmoothForm.mextDeriv_mextDeriv]
      rw [hσt]
      exact congrFun ((SmoothForm.isClosed_def _).1 (h₀.add (h₁.smul s))) y
    refine moserField_rate_eq_zero hclosed
      (((Continuous.prodMk_right s).continuousAt.eventually hy).mono fun z hz ↦
        ⟨hz.1, by rw [hσt]; exact hz.2⟩) ?_
    rw [hvel, hβt, hβ]
  filter_upwards [hW.mem_nhdsSet.2 hKW] with x hx t
  have h := mpullback_timeDependentFlowOf_mpullback_prodMk_apply_eq_of_forall_mem_uIcc
    (hX.of_le (by simp)) hc (fun _ _ ↦ (σ.contMDiff.of_le (by simp)).contMDiffAt)
    (s := 0) (t := t) (x := x) fun s hs ↦ hrate s _
      (huW (mk_mem_prod (hu (Icc_subset_Icc_right t.property.2
        ((uIcc_of_le t.property.1).subset hs))) hx))
  simp only [σ, SmoothForm.coe_mpullback_prodMk_lineMapFamily, id_eq, zero_smul, add_zero] at h
  rw [SmoothForm.coe_mpullback, hΨ]
  exact h

end TauCeti.SmoothTwoForm

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
  -- Moser's argument runs on the open submanifold `W`, with the restricted forms.
  let g : Q → W := fun q ↦ ⟨f q, hfW (mem_range_self q)⟩
  have hgK : IsCompact (range g) :=
    isCompact_range (f.contMDiff.continuous.subtype_mk fun q ↦ hfW (mem_range_self q))
  obtain ⟨Λ, ⟨C, hC, hΛC⟩, hΛK, hΛ⟩ :=
    SmoothTwoForm.exists_diffeotopy_fix_eventually_mpullback_eq_of_mextDeriv_eq_sub
      (h₀.mpullback _ _) hdβW hgK
      (by rintro _ ⟨q, rfl⟩; exact hβW0 q)
      (by
        rintro _ ⟨q, rfl⟩ s hs
        rw [← map_sub, ← map_smul, ← map_add]
        exact (SmoothTwoForm.nondegenerate_bilinFormAt_mpullback_subtype_val_iff (g q)).2
          (hnd q s hs))
  -- Extend the compactly supported diffeotopy of `W` by the identity.
  obtain ⟨Ψ, hΨW, hΨC⟩ := Λ.exists_extend_of_isCompact isLocalDiffeomorph_subtype_val
    W.isOpen.isOpenEmbedding_subtypeVal hC hΛC
  have hcomp (t : unitInterval) :
      ⇑(Ψ.timeSlice t) ∘ (Subtype.val : W → M) = Subtype.val ∘ ⇑(Λ.timeSlice t) :=
    funext fun z ↦ by simp only [Function.comp_apply, Diffeotopy.timeSlice_apply, hΨW]
  refine ⟨Ψ, ⟨Subtype.val '' C, hC.image continuous_subtypeVal, hΨC⟩,
    fun t q ↦ (hΨW t (g q)).trans (congrArg Subtype.val (hΛK t _ (mem_range_self q))), ?_⟩
  -- On `W`, the pullback by `Ψ_t` is the pullback by `Λ_t` of the restricted forms.
  obtain ⟨U, ⟨hU, hKU⟩, hUΛ⟩ := (hasBasis_nhdsSet (range g)).mem_iff.1 hΛ
  refine mem_of_superset ((W.isOpen.isOpenEmbedding_subtypeVal.isOpenMap U hU).mem_nhdsSet.2 ?_)
    ?_
  · rintro _ ⟨q, rfl⟩
    exact ⟨g q, hKU (mem_range_self q), rfl⟩
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
