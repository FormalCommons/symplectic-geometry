/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.SmoothIsotopy.IsSymplectic
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Flow.Family
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Opens
import SymplecticGeometry.Geometry.Manifold.IsManifold.SecondCountable
import SymplecticGeometry.Geometry.Manifold.SmoothIsotopy.Extension
import SymplecticGeometry.Geometry.Symplectic.Moser.Family
import TauCeti.Geometry.Manifold.Immersion.LocalDiffeomorph
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import TauCeti.Geometry.Manifold.MFDeriv.Basic
import TauCeti.Geometry.Manifold.SmoothEmbedding.Diffeomorph
import TauCeti.Geometry.Manifold.SmoothEmbedding.LocalDiffeomorph
import TauCeti.Geometry.Manifold.TubularNeighborhood.Existence

/-!
# Neighbourhood extension of isotopies of submanifolds

Let `σ` be a symplectic form on a boundaryless manifold `M`, `i : Q → M` a compact embedded
submanifold and `e_t`, `t ∈ [0, 1]`, a smooth isotopy of embeddings starting at `i` such that
`e_t^* σ = i^* σ` for every `t`. Then `e` extends to a symplectic isotopy of an open
neighbourhood `U` of `i(Q)`: there is a smooth isotopy `F_t : U → M` starting at the inclusion
with `F_t^* σ = σ` on `U` and `F_t ∘ i = e_t` for every `t`
(`TauCeti.SmoothIsotopy.exists_isSymplectic_extension_of_mpullback_eq`). No condition on the
rank of `i^* σ` is needed.

## The proof

1. Isotopy extension at every time
   (`TauCeti.SmoothIsotopy.exists_contMDiff_diffeomorph_forall_apply_eq`) gives a jointly
   smooth family `ψ_t` of diffeomorphisms of `M` over all real times, with `ψ_0 = id` and
   `ψ_t ∘ i = e_t` for `t ∈ [0, 1]`. A smooth retraction `r : W → Q` of an open neighbourhood
   `W` of `i(Q)` (`TauCeti.SmoothEmbedding.exists_contMDiffOn_retraction`) is fixed.
2. On `ℝ × W` let `A (t, w) = ψ_t w`, `B (t, w) = ψ_t (i (r w))` and `C (t, w) = i (r w)`, and
   let `S = A^* σ - B^* σ + C^* σ`. It is closed, so by Cartan's formula the slices of its
   time derivative are the differentials of the slices of `γ = ι_{∂_t} S`
   (`TauCeti.SmoothForm.mextDerivₗ_timeInterior`). For `t ∈ [0, 1]` the slice `B_t^* σ` is
   `r^* e_t^* σ = r^* i^* σ = C_t^* σ`, so `S_t = ψ_t^* σ`, which is symplectic. Since
   `r ∘ i = id`, the maps `A` and `B` agree on `ℝ × Q`, so the pullback of `S` to `ℝ × Q` is
   that of `i^* σ` along the projection, and `γ` pulls back to `0` on every slice of `Q`.
3. Moser's argument along a family fixing a compact submanifold
   (`TauCeti.SmoothEmbedding.exists_diffeotopy_fix_eventually_mpullback_eq_of_timeDeriv`), on
   the manifold `W`, gives a diffeotopy `Ψ` of `W` fixing `i(Q)` with `Ψ_t^* S_t = S_0 = σ` on a
   neighbourhood `U` of `i(Q)`. The isotopy `F_t = ψ_t ∘ Ψ_t` of `U` is the extension.

The form `S` differs from `ψ_t^* σ` only at times outside `[0, 1]`. The correction terms
`- B^* σ + C^* σ` make the primitive `γ` vanish on `Q` at every real time, which Moser's argument
needs near `[0, 1]`. Subtracting `r^* i^* γ'` from the plain primitive `γ' = ι_{∂_t} ψ^* σ`
instead would not do: the slices of `i^* γ'` are closed only for `t ∈ [0, 1]`, so the corrected
form is a primitive of the time derivative only on `[0, 1]`, and not on a neighbourhood of it.

## Main results

* `TauCeti.SmoothIsotopy.exists_isSymplectic_extension_of_mpullback_eq`: an isotopy of a compact
  embedded submanifold that keeps the pullback of a symplectic form fixed extends to a
  symplectic isotopy of a neighbourhood.

## Implementation notes

The symplectic form is called `σ`, since `ω` is a token once the scope `ContDiff` is open. The
start of the extension is a map `g₀` with `∀ x, g₀ x = x`, the inclusion of `U`, rather than the
term `⟨Subtype.val, contMDiff_subtypeVal⟩`, so that the isotopy coerces to a function.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Exercise 3.4.20 (the statement) and Lemma 3.2.1 (Moser's argument).
-/

public section

noncomputable section

open Set Filter Function Manifold TopologicalSpace
open scoped Manifold ContDiff Topology

namespace TauCeti.SmoothIsotopy

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {E' H' Q : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [J.Boundaryless]
  [TopologicalSpace Q] [ChartedSpace H' Q] [IsManifold J ∞ Q] [CompactSpace Q]

/-- The Moser step of `exists_isSymplectic_extension_of_mpullback_eq`. Let `ψ_t` be a jointly
smooth family of diffeomorphisms of `M` over `ℝ` with `ψ_0 = id`, let `i : Q → M` be a compact
submanifold inside an open set `W`, with `f : Q → W` the same map into `W` and a smooth
retraction `r : W → Q`, and let `e_t = ψ_t ∘ i` for `t ∈ [0, 1]` with `e_t^* σ = i^* σ`. Then there
is a diffeotopy `Ψ` of `W` fixing `f(Q)` with `Ψ_t^* ψ_t^* σ = σ` near `f(Q)` for every
`t ∈ [0, 1]`. -/
private theorem exists_diffeotopy_mpullback_eq [FiniteDimensional ℝ E']
    [SecondCountableTopology M] {σ : SmoothTwoForm I M} (hσ : σ.IsSymplectic)
    (ψ : ℝ → M ≃ₘ⟮I, I⟯ M) (hψ : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M ↦ ψ p.1 p.2))
    (hψ₀ : ∀ y, ψ 0 y = y) {W : Opens M} (f : SmoothEmbedding J I ∞ Q W)
    (i : SmoothEmbedding J I ∞ Q M) (hfi : ∀ q, (f q : M) = i q) {r : W → Q}
    (hr : ContMDiff I J ∞ r) (hrf : ∀ q, r (f q) = q) {f₁ : C^∞⟮J, Q; I, M⟯}
    (e : SmoothIsotopy i.toContMDiffMap f₁)
    (he : ∀ t, TauCeti.mpullback J I (fun q ↦ e (t, q)) σ.val = TauCeti.mpullback J I i σ.val)
    (hψe : ∀ t : unitInterval, ∀ q, ψ t (i q) = e (t, q)) :
    ∃ Ψ : Diffeotopy I ∞ W, (∀ t q, Ψ (t, f q) = f q) ∧
      ∀ᶠ w in 𝓝ˢ (range f), ∀ t : unitInterval,
        (SmoothForm.mpullback (Ψ.timeSlice t) (Ψ.timeSlice t).contMDiff
          (SmoothForm.mpullback (fun w : W ↦ ψ t w)
            (hψ.comp (contMDiff_const.prodMk contMDiff_subtypeVal)) σ)).val w =
          (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal σ).val w := by
  set ρ : W → M := fun w ↦ i (r w)
  have hρ : ContMDiff I I ∞ ρ := i.contMDiff.comp hr
  set A : ℝ × W → M := fun p ↦ ψ p.1 p.2
  have hA : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ A :=
    hψ.comp (contMDiff_fst.prodMk (contMDiff_subtypeVal.comp contMDiff_snd))
  set B : ℝ × W → M := fun p ↦ ψ p.1 (ρ p.2)
  have hB : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ B :=
    hψ.comp (contMDiff_fst.prodMk (hρ.comp contMDiff_snd))
  -- The family `S = A^* σ - B^* σ + C^* σ`, with `C (t, w) = ρ w`.
  set S : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × W) ℝ 2 :=
    SmoothForm.mpullback A hA σ - SmoothForm.mpullback B hB σ +
      SmoothForm.mpullback Prod.snd contMDiff_snd (SmoothForm.mpullback ρ hρ σ)
  have hS : S.IsClosed :=
    ((hσ.isClosed.mpullback A hA).sub (hσ.isClosed.mpullback B hB)).add
      ((hσ.isClosed.mpullback ρ hρ).mpullback Prod.snd contMDiff_snd)
  -- For `t ∈ [0, 1]`, the slice of `S` at `t` is `ψ_t^* σ`.
  have hslice (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) S =
        SmoothForm.mpullback (fun w : W ↦ ψ t w)
          (hψ.comp (contMDiff_const.prodMk contMDiff_subtypeVal)) σ := by
    have hBt : SmoothForm.mpullback (B ∘ Prod.mk t) (hB.comp (contMDiff_const.prodMk contMDiff_id))
        σ = SmoothForm.mpullback ((ρ ∘ Prod.snd) ∘ Prod.mk t)
          (hρ.comp ((contMDiff_snd (I := 𝓘(ℝ, ℝ))).comp
            (contMDiff_const.prodMk contMDiff_id))) σ := by
      apply Subtype.ext
      have h₁ : B ∘ Prod.mk t = (fun q ↦ e (⟨t, ht⟩, q)) ∘ r :=
        funext fun w ↦ hψe ⟨t, ht⟩ (r w)
      have h₂ : (ρ ∘ Prod.snd) ∘ Prod.mk t = i ∘ r := rfl
      rw [SmoothForm.coe_mpullback, SmoothForm.coe_mpullback, h₁, h₂,
        TauCeti.mpullback_comp (f := r) (g := fun q ↦ e (⟨t, ht⟩, q)) (hr.mdifferentiable (by simp))
          ((e.contMDiff.comp (contMDiff_const.prodMk contMDiff_id)).mdifferentiable (by simp)),
        TauCeti.mpullback_comp (hr.mdifferentiable (by simp))
          (i.contMDiff.mdifferentiable (by simp)), he]
    simp only [S, map_add, map_sub, SmoothForm.mpullback_mpullback]
    rw [hBt, sub_add_cancel]
    -- `A ∘ Prod.mk t` is `fun w ↦ ψ t w` by definition of the composition.
    rfl
  -- The slices of the time derivative of `S` are the differentials of those of `γ = ι_{∂_t} S`.
  have hγ (p : ℝ × W) :
      (SmoothForm.mpullback (Prod.mk p.1) (contMDiff_const.prodMk contMDiff_id)
          S.timeDeriv).val p.2 =
        mextDeriv (SmoothForm.mpullback (Prod.mk p.1) (contMDiff_const.prodMk contMDiff_id)
          S.timeInterior).val p.2 := by
    rw [← SmoothForm.mextDerivₗ_timeInterior hS, ← SmoothForm.mextDerivₗ_mpullback,
      mextDerivₗ_apply]
  -- On `ℝ × Q`, the maps `A` and `B` agree, so `γ` pulls back to `0` there.
  have hAB : A ∘ Prod.map id f = B ∘ Prod.map id f := by
    funext p
    simp only [A, B, ρ, comp_apply, Prod.map_fst, Prod.map_snd, id, hrf, hfi]
  have hγf (t : ℝ) : SmoothForm.mpullback f f.contMDiff
      (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id)
        S.timeInterior) = 0 := by
    rw [← SmoothForm.mpullback_prodMk_mpullback_prodMap f f.contMDiff]
    have hS' : SmoothForm.mpullback (Prod.map id f) (contMDiff_id.prodMap f.contMDiff) S =
        SmoothForm.mpullback Prod.snd contMDiff_snd
          (SmoothForm.mpullback (ρ ∘ f) (hρ.comp f.contMDiff) σ) := by
      simp only [S, map_add, map_sub, SmoothForm.mpullback_mpullback, hAB, sub_self, zero_add]
      -- `(ρ ∘ Prod.snd) ∘ Prod.map id f` is `(ρ ∘ f) ∘ Prod.snd` by definition of the composition.
      rfl
    rw [SmoothForm.mpullback_prodMap_timeInterior f f.contMDiff, hS',
      SmoothForm.timeInterior_mpullback_snd, map_zero]
  -- `S_t` is nondegenerate for `t ∈ [0, 1]`, since `ψ_t ∘ Subtype.val` is a local diffeomorphism.
  have hnd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (q : Q) :
      ((SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) S).bilinFormAt
        (f q)).Nondegenerate := by
    rw [hslice t ht]
    exact (hσ.isNondegenerate.isNondegenerate_mpullback_of_isLocalDiffeomorph
      (fun w ↦ (isLocalDiffeomorph_subtype_val w).comp I M
        ((ψ t).isLocalDiffeomorph (w : M)))).nondegenerate_bilinFormAt (f q)
  obtain ⟨Ψ, -, hΨf, hΨ⟩ := f.exists_diffeotopy_fix_eventually_mpullback_eq_of_timeDeriv S
    (fun t _ ↦ hS.mpullback _ _) S.timeInterior (Eventually.of_forall hγ) (fun t _ ↦ hγf t) hnd
  refine ⟨Ψ, hΨf, hΨ.mono fun w hw t ↦ ?_⟩
  have h₀ : SmoothForm.mpullback (Prod.mk 0) (contMDiff_const.prodMk contMDiff_id) S =
      SmoothForm.mpullback Subtype.val contMDiff_subtypeVal σ := by
    rw [hslice 0 ⟨le_rfl, zero_le_one⟩]
    have h : (fun w : W ↦ ψ 0 w) = Subtype.val := funext fun w ↦ hψ₀ w
    exact Subtype.ext (by rw [SmoothForm.coe_mpullback, SmoothForm.coe_mpullback, h])
  rw [← h₀, ← hw t, hslice t t.property]

/-- **Neighbourhood extension of isotopies of submanifolds.** Let `σ` be a symplectic form on a
finite-dimensional, Hausdorff, σ-compact, boundaryless manifold `M`, let `i : Q → M` be a
compact embedded submanifold without boundary, and let `e` be a smooth isotopy of embeddings
from `i` to `f₁` that keeps the pullback of `σ` fixed: `e_t^* σ = i^* σ` for every
`t ∈ [0, 1]`. Then there are an open neighbourhood `U` of `i(Q)` and a symplectic isotopy `F`
of `U` into `M`, starting at the inclusion `g₀` of `U`, with `F_t^* σ = σ` on `U` and
`F_t ∘ i = e_t` for every `t`. No condition on the rank of `i^* σ` is needed.

Milestone: *Neighbourhood extension of submanifold isotopies*. -/
theorem exists_isSymplectic_extension_of_mpullback_eq [SigmaCompactSpace M]
    {σ : SmoothTwoForm I M} (hσ : σ.IsSymplectic) (i : SmoothEmbedding J I ∞ Q M)
    {f₁ : C^∞⟮J, Q; I, M⟯} (e : SmoothIsotopy i.toContMDiffMap f₁)
    (he : ∀ t, TauCeti.mpullback J I (fun q ↦ e (t, q)) σ.val = TauCeti.mpullback J I i σ.val) :
    ∃ (U : Opens M) (hU : range i ⊆ U) (g₀ g₁ : C^∞⟮I, U; I, M⟯) (_ : ∀ x, g₀ x = x)
      (F : SmoothIsotopy g₀ g₁),
      F.IsSymplectic (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal σ) σ ∧
      ∀ t q, F (t, ⟨i q, hU ⟨q, rfl⟩⟩) = e (t, q) := by
  rcases isEmpty_or_nonempty Q with hQ | hQ
  · -- For `Q = ∅`, the constant isotopy of the empty open set will do.
    refine ⟨⊥, fun x ⟨q, _⟩ ↦ isEmptyElim q, ⟨Subtype.val, contMDiff_subtypeVal⟩, _,
      fun _ ↦ rfl, ContMDiffMap.smoothIsotopyRefl _ (IsSmoothEmbedding.id.comp_subtypeVal ⊥),
      SmoothIsotopy.IsSymplectic.refl _ (SmoothForm.coe_mpullback _ _ _).symm,
      fun _ q ↦ isEmptyElim q⟩
  -- The model of `Q` is finite-dimensional, since `i` is an immersion into `M`.
  have : FiniteDimensional ℝ E' := finiteDimensional_of_injective_mfderiv
    (i.isImmersion.mfderiv_injective (by simp) (Classical.arbitrary Q))
  have := I.locallyCompactSpace
  have := ChartedSpace.locallyCompactSpace H M
  have := I.secondCountableTopology_of_sigmaCompact M
  -- Isotopy extension over `ℝ`, and a retraction onto `i(Q)`.
  obtain ⟨ψ, hψ, hψ₀, -, -, -, hψe⟩ :=
    e.exists_contMDiff_diffeomorph_forall_apply_eq (isCompact_univ (X := Q))
  obtain ⟨W, hW, hiW, -, r, hr, hri⟩ := i.exists_contMDiffOn_retraction isOpen_univ (subset_univ _)
  set Wo : Opens M := ⟨W, hW⟩
  have hiWo (q : Q) : i q ∈ Wo := hiW ⟨q, rfl⟩
  set f := i.codRestrict Wo hiWo
  have hfi (q : Q) : (f q : M) = i q := i.val_codRestrict_apply Wo hiWo q
  obtain ⟨Ψ, hΨf, hΨ⟩ := exists_diffeotopy_mpullback_eq hσ ψ hψ hψ₀ f i hfi
    (hr.comp_contMDiff contMDiff_subtypeVal fun w ↦ w.property) (fun q ↦ by simp [hfi, hri]) e he
    (fun t q ↦ hψe t q (mem_univ q))
  -- The neighbourhood `U ⊆ W` of `i(Q)` on which `Ψ` corrects the pullbacks.
  obtain ⟨V, hV, hfV, hVΨ⟩ := eventually_nhdsSet_iff_exists.1 hΨ
  set U : Opens M := ⟨Subtype.val '' V, Wo.isOpen.isOpenMap_subtypeVal V hV⟩
  have hUW : U ≤ Wo := by
    rintro _ ⟨w, -, rfl⟩
    exact w.property
  set incl : U → Wo := Opens.inclusion hUW
  have hincl : ContMDiff I I ∞ incl := contMDiff_inclusion hUW
  have hinclV (x : U) : incl x ∈ V := by
    obtain ⟨w, hw, hwx⟩ := x.property
    convert hw
    exact Subtype.ext hwx.symm
  have hemb_incl : IsSmoothEmbedding I I ∞ incl :=
    isSmoothEmbedding_subtypeVal_comp_iff.mp (IsSmoothEmbedding.id.comp_subtypeVal U)
  -- The isotopy `F_t = ψ_t ∘ Ψ_t` of `U`.
  set m : unitInterval × U → M := fun p ↦ ψ p.1 (Ψ (p.1, incl p.2))
  have hm : ContMDiff ((𝓡∂ 1).prod I) I ∞ m :=
    hψ.comp ((contMDiff_subtypeVal_Icc.comp contMDiff_fst).prodMk
      (contMDiff_subtypeVal.comp (Ψ.contMDiff.comp (contMDiff_fst.prodMk
        (hincl.comp contMDiff_snd)))))
  have hmt (t : unitInterval) :
      (fun x ↦ m (t, x)) = (fun w : Wo ↦ ψ t w) ∘ Ψ.timeSlice t ∘ incl :=
    funext fun x ↦ by rw [comp_apply, comp_apply, Diffeotopy.timeSlice_apply]
  have hemb (t : unitInterval) : IsSmoothEmbedding I I ∞ (fun x ↦ m (t, x)) := by
    rw [hmt]
    exact isSmoothEmbedding_diffeomorph_comp (isSmoothEmbedding_subtypeVal_comp_iff.mpr
      (isSmoothEmbedding_diffeomorph_comp hemb_incl (Ψ.timeSlice t))) (ψ t)
  set g : unitInterval → C^∞⟮I, U; I, M⟯ := fun t ↦
    ⟨fun x ↦ m (t, x), hm.comp (contMDiff_const.prodMk contMDiff_id)⟩
  refine ⟨U, fun _ ⟨q, hq⟩ ↦ hq ▸ ⟨f q, hfV ⟨q, rfl⟩, hfi q⟩, g 0, g 1, fun x ↦ ?_,
    ⟨⟨m, hm⟩, fun _ ↦ rfl, fun _ ↦ rfl, hemb⟩, isSymplectic_def.2 fun t ↦ ?_,
    fun t q ↦ ?_⟩
  · simp [g, m, Diffeotopy.apply_zero, hψ₀, incl]
  · -- `F_t^* σ = incl^* Ψ_t^* ψ_t^* σ = incl^* σ` at every point of `U`.
    funext x
    have hΨt := (Ψ.timeSlice t).contMDiff
    have hψt : ContMDiff I I ∞ (fun w : Wo ↦ ψ t w) :=
      hψ.comp (contMDiff_const.prodMk contMDiff_subtypeVal)
    -- The slices of `F` are those of the motion `m` by construction.
    change TauCeti.mpullback I I (fun x ↦ m (t, x)) σ.val x = _
    rw [hmt, TauCeti.mpullback_comp ((hΨt.comp hincl).mdifferentiable (by simp))
      (hψt.mdifferentiable (by simp)),
      TauCeti.mpullback_comp (hincl.mdifferentiable (by simp)) (hΨt.mdifferentiable (by simp))]
    rw [← SmoothForm.coe_mpullback _ hψt, ← SmoothForm.coe_mpullback _ hΨt]
    ext v
    rw [TauCeti.mpullback_apply, hVΨ _ (hinclV x) t, ← TauCeti.mpullback_apply,
      SmoothForm.coe_mpullback, TauCeti.mpullback_inclusion_mpullback_subtype_val,
      SmoothForm.coe_mpullback]
  · -- The point `⟨i q, _⟩` of `U` is sent by the inclusion to `f q`, which `Ψ` fixes.
    -- `F` is the motion `m` by construction.
    change ψ t (Ψ (t, incl _)) = e (t, q)
    rw [show incl _ = f q from Subtype.ext (hfi q).symm, hΨf, hfi]
    exact hψe t q (mem_univ q)

end TauCeti.SmoothIsotopy
