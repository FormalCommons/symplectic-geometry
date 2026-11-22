/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.Liouville.Collar
public import TauCeti.Geometry.Symplectic.Manifold.Flat
import TauCeti.Geometry.Manifold.DifferentialForm.Interior
import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
import TauCeti.Geometry.Manifold.Flow.Diffeomorph
import TauCeti.Geometry.Manifold.ModelTransport.Interior
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Opens
import SymplecticGeometry.Geometry.Manifold.Flow.Basic
import SymplecticGeometry.Geometry.Manifold.VectorField.Pullback
import SymplecticGeometry.Geometry.Symplectic.Liouville.ContactType

/-!
# Liouville scaling along integral curves

Let `Z` be the Liouville field of a one-form `α`, `ι_Z dα = α`, on a boundaryless manifold, and
let `Φ : ℝ × S → M` have each line `t ↦ Φ (t, s)` an integral curve of `Z` on an interval
`(a, b)`. For `t₀ ∈ (a, b)` with a smooth slice `Φ (t₀, ·)`, the map `Φ` is the flow of `Z` out of
that slice, run for time `t - t₀`; so it is smooth on `(a, b) × S`
(`TauCeti.contMDiffAt_of_isMIntegralCurveOn`) and, by Tau Ceti's
`TauCeti.mpullback_flowOf_comp_apply_eq_symplectization`, it pulls `α` back to the
symplectization form `e^(t - t₀) Φ(t₀, ·)^* α`
(`TauCeti.mpullback_apply_eq_symplectization_of_isMIntegralCurveOn`).

The same holds in the interior of a manifold with boundary, for a field that is Liouville only on
an open set. Let `σ` be a closed two-form on `W`, `Y` a smooth vector field, and `U` an open
subset of the interior of `W` with `L_Y σ = σ` on `U`. If `Φ` maps `(a, b) × S` into `U` and its
lines are integral curves of `Y`, then `Φ` pulls the primitive `ι_Y σ` back to
`e^(t - t₀) Φ(t₀, ·)^*(ι_Y σ)`; it vanishes on `∂ₜ`, since `ι_Y σ (Y) = σ(Y, Y) = 0`
(`TauCeti.mpullback_interiorₗ_apply_eq_symplectization_of_isMIntegralCurveOn`). The proof
restricts `Y` and `ι_Y σ` to `U`, as `TauCeti.SmoothEmbedding.exists_pos_forall_liouvilleCollar`
does, and re-models `U`, which has no boundary points, over the model vector space by Tau Ceti's
`TauCeti.BoundarylessModel.interiorDiffeomorph`, where the boundaryless case applies.

In McDuff–Salamon's signs, with the primitive `λ = -ι_Y σ` and `α = -Φ(t₀, ·)^*(ι_Y σ)`, the
identity reads `Φ^* λ = e^(t - t₀) α`.

## Main results

* `TauCeti.mpullback_apply_eq_symplectization_of_isMIntegralCurveOn`: Liouville scaling along
  integral curves on a boundaryless manifold.
* `TauCeti.mpullback_interiorₗ_apply_eq_symplectization_of_isMIntegralCurveOn`: Liouville scaling
  along integral curves in the interior of a manifold with boundary.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §3.5.
-/

public section

open Set Bundle Filter Function TopologicalSpace
open scoped Manifold ContDiff Topology

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {E' H' S : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace S] [ChartedSpace H' S]

namespace TauCeti

/-- Pulling a form on `ℝ × S` back along the time shift `(t, s) ↦ (t - c, s)` evaluates it at the
shifted point: the shift has the identity as its differential. -/
theorem mpullback_fst_sub_const_apply {k : ℕ} (c : ℝ)
    (γ : RoughForm (𝓘(ℝ).prod J) (ℝ × S) ℝ k) (p : ℝ × S) :
    mpullback (𝓘(ℝ).prod J) (𝓘(ℝ).prod J) (fun q : ℝ × S ↦ (q.1 - c, q.2)) γ p =
      γ (p.1 - c, p.2) := by
  have hsub : HasMFDerivAt 𝓘(ℝ) 𝓘(ℝ) (fun r : ℝ ↦ r - c) p.1 (ContinuousLinearMap.id ℝ ℝ) :=
    hasMFDerivAt_iff_hasFDerivAt.2 ((hasFDerivAt_id _).sub_const c)
  have hd : mfderiv (𝓘(ℝ).prod J) (𝓘(ℝ).prod J) (fun q : ℝ × S ↦ (q.1 - c, q.2)) p =
      ContinuousLinearMap.id ℝ _ := by
    -- The shift is `Prod.map (· - c) id`, whose differential is a product map.
    change mfderiv (𝓘(ℝ).prod J) (𝓘(ℝ).prod J) (Prod.map (fun r : ℝ ↦ r - c) id) p = _
    rw [mfderiv_prodMap hsub.mdifferentiableAt mdifferentiableAt_id, hsub.mfderiv, mfderiv_id]
    -- The product of two identities is the identity, by definition.
    rfl
  ext v
  rw [mpullback_apply, hd]
  -- The shifted point is `(p.1 - c, p.2)` by definition.
  rfl

section Boundaryless

/-! ### Integral curves on a boundaryless manifold -/

variable [I.Boundaryless] {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] {Z : (x : M) → TangentSpace I x} {Φ : ℝ × S → M} {a b t₀ t : ℝ}

omit [FiniteDimensional ℝ E] in
/-- If the lines `t ↦ Φ (t, s)` are integral curves of the `C¹` field `Z` on `(a, b)` and
`t₀, t ∈ (a, b)`, then near `(t, s)` the map `Φ` is the flow of `Z` out of the slice at `t₀`, run
for time `q.1 - t₀`. -/
theorem eventuallyEq_flowOf_sub_of_isMIntegralCurveOn (hZ : ContMDiff I I.tangent 1 (T% Z))
    (hΦZ : ∀ s, IsMIntegralCurveOn (fun t ↦ Φ (t, s)) Z (Ioo a b)) (ht₀ : t₀ ∈ Ioo a b)
    (ht : t ∈ Ioo a b) (s : S) :
    Φ =ᶠ[𝓝 (t, s)] fun q ↦ flowOf Z (q.1 - t₀) (Φ (t₀, q.2)) := by
  filter_upwards [(isOpen_Ioo.prod isOpen_univ).mem_nhds (mk_mem_prod ht (mem_univ s))] with p hp
  exact ((hΦZ p.2).flowOf_sub_eq hZ ht₀ hp.1).symm

/-- If the lines `t ↦ Φ (t, s)` are integral curves of the smooth field `Z` on `(a, b)` and the
slice `Φ (t₀, ·)` at some `t₀ ∈ (a, b)` is smooth, then `Φ` is smooth at every point of
`(a, b) × S`. -/
theorem contMDiffAt_of_isMIntegralCurveOn (hZ : ContMDiff I I.tangent ∞ (T% Z))
    (hΦZ : ∀ s, IsMIntegralCurveOn (fun t ↦ Φ (t, s)) Z (Ioo a b)) (ht₀ : t₀ ∈ Ioo a b)
    (hΦ₀ : ContMDiff J I ∞ fun s ↦ Φ (t₀, s)) (ht : t ∈ Ioo a b) (s : S) :
    ContMDiffAt (𝓘(ℝ).prod J) I ∞ Φ (t, s) :=
  (contMDiffAt_flowOf_comp le_top hZ (contMDiffAt_fst.sub contMDiffAt_const)
    (hΦ₀.comp contMDiff_snd).contMDiffAt ((hΦZ s).sub_mem_flowDomain ht₀ ht)).congr_of_eventuallyEq
    (eventuallyEq_flowOf_sub_of_isMIntegralCurveOn (hZ.of_le (by norm_num)) hΦZ ht₀ ht s)

variable [IsManifold J ∞ S]

/-- **Liouville scaling along integral curves.** Let the smooth vector field `Z` be the Liouville
field of the one-form `α`, `ι_Z dα = α`, on a boundaryless manifold, let each line
`t ↦ Φ (t, s)` of `Φ : ℝ × S → M` be an integral curve of `Z` on `(a, b)`, and let `t₀ ∈ (a, b)`
have a smooth slice `Φ (t₀, ·)`. Then at every `(t, s)` with `t ∈ (a, b)`, `Φ` pulls `α` back to
the value at `(t - t₀, s)` of the symplectization form of the pullback of `α` to the slice, the
one-form `e^(t - t₀) Φ(t₀, ·)^* α`. -/
theorem mpullback_apply_eq_symplectization_of_isMIntegralCurveOn
    (hZ : ContMDiff I I.tangent ∞ (T% Z)) {α : SmoothForm I M ℝ 1}
    (hZα : (mextDeriv α.val).interior Z = α.val)
    (hΦZ : ∀ s, IsMIntegralCurveOn (fun t ↦ Φ (t, s)) Z (Ioo a b)) (ht₀ : t₀ ∈ Ioo a b)
    (hΦ₀ : ContMDiff J I ∞ fun s ↦ Φ (t₀, s)) (ht : t ∈ Ioo a b) (s : S) :
    mpullback (𝓘(ℝ).prod J) I Φ α.val (t, s) =
      (SmoothForm.mpullback _ hΦ₀ α).symplectization.val (t - t₀, s) := by
  have hdom := (hΦZ s).sub_mem_flowDomain ht₀ ht
  have hΨ : MDifferentiableAt (𝓘(ℝ).prod J) I (fun q : ℝ × S ↦ flowOf Z q.1 (Φ (t₀, q.2)))
      (t - t₀, s) :=
    (contMDiffAt_flowOf_comp le_top hZ contMDiffAt_fst (hΦ₀.comp contMDiff_snd).contMDiffAt
      hdom).mdifferentiableAt (by simp)
  have hshift : MDifferentiableAt (𝓘(ℝ).prod J) (𝓘(ℝ).prod J)
      (fun q : ℝ × S ↦ (q.1 - t₀, q.2)) (t, s) :=
    (((contMDiff_fst.sub contMDiff_const).prodMk contMDiff_snd :
      ContMDiff (𝓘(ℝ).prod J) (𝓘(ℝ).prod J) 1 fun q : ℝ × S ↦ (q.1 - t₀, q.2)) (t, s)
      ).mdifferentiableAt one_ne_zero
  -- `Φ` is, near `(t, s)`, the flow map of Tau Ceti's theorem composed with the time shift.
  rw [(eventuallyEq_flowOf_sub_of_isMIntegralCurveOn (hZ.of_le (by norm_num)) hΦZ ht₀ ht
      s).mpullback_eq, ← comp_def (fun q : ℝ × S ↦ flowOf Z q.1 (Φ (t₀, q.2)))
      (fun q : ℝ × S ↦ (q.1 - t₀, q.2)), mpullback_comp_at hshift hΨ,
    mpullback_fst_sub_const_apply, mpullback_flowOf_comp_apply_eq_symplectization hZ hΦ₀ hZα hdom]

end Boundaryless

/-! ### An open set without boundary points, re-modelled over `E` -/

variable {W : Type*} [TopologicalSpace W] [ChartedSpace H W]

variable (I) in
/-- An open set `U` of `W`, as a manifold modelled on `E` through Tau Ceti's `BoundarylessModel`;
its charts are the extended charts of `W`, which is possible when `U` has no boundary points. -/
private def InteriorModel (U : Opens W) : Type _ := BoundarylessModel I U

private noncomputable instance (U : Opens W) : TopologicalSpace (InteriorModel I U) :=
  inferInstanceAs (TopologicalSpace (BoundarylessModel I U))

private instance [T2Space W] (U : Opens W) : T2Space (InteriorModel I U) :=
  inferInstanceAs (T2Space U)

private noncomputable instance [IsManifold I ∞ W] (U : Opens W) [BoundarylessManifold I U] :
    ChartedSpace E (InteriorModel I U) :=
  BoundarylessModel.interiorChartedSpace I (M := U)

private instance [IsManifold I ∞ W] (U : Opens W) [BoundarylessManifold I U] :
    IsManifold 𝓘(ℝ, E) ∞ (InteriorModel I U) :=
  BoundarylessModel.instIsManifoldInteriorChartedSpace I (M := U)

variable (I) in
/-- The identity of `U`, as a diffeomorphism onto its re-modelled copy. -/
private noncomputable def interiorModelDiffeomorph [IsManifold I ∞ W] (U : Opens W)
    [BoundarylessManifold I U] :
    U ≃ₘ^∞⟮I, 𝓘(ℝ, E)⟯ InteriorModel I U :=
  BoundarylessModel.interiorDiffeomorph I (M := U) ∞

variable [IsManifold I ∞ W] [T2Space W] [IsManifold J ∞ S]

/-- **Liouville scaling along integral curves in the interior.** Let `σ` be a closed two-form on
`W`, `Y` a smooth vector field, and `U` an open subset of the interior of `W` on which
`L_Y σ = σ`. Let `Φ : ℝ × S → W` map `(a, b) × S` into `U`, with each `t ↦ Φ (t, s)` an
integral curve of `Y` on `(a, b)`, and let `t₀ ∈ (a, b)` have a smooth slice `Φ (t₀, ·)`. Then
at every `(t, s)` with `t ∈ (a, b)`, `Φ` pulls the primitive `ι_Y σ` back to the value at
`(t - t₀, s)` of the symplectization form of the pullback of `ι_Y σ` to the slice, the
one-form `e^(t - t₀) Φ(t₀, ·)^*(ι_Y σ)`. -/
theorem mpullback_interiorₗ_apply_eq_symplectization_of_isMIntegralCurveOn
    {σ : SmoothTwoForm I W} (hσ : σ.IsClosed) {Y : (x : W) → TangentSpace I x}
    (hY : ContMDiff I I.tangent ∞ (T% Y)) {U : Set W} (hU : IsOpen U) (hUW : U ⊆ I.interior W)
    (hYσ : ∀ x ∈ U, mlieDerivForm Y σ.val x = σ.val x) {Φ : ℝ × S → W} {a b : ℝ}
    (hΦU : ∀ t ∈ Ioo a b, ∀ s, Φ (t, s) ∈ U)
    (hΦY : ∀ s, IsMIntegralCurveOn (fun t ↦ Φ (t, s)) Y (Ioo a b)) {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b)
    (hΦ₀ : ContMDiff J I ∞ fun s ↦ Φ (t₀, s)) {t : ℝ} (ht : t ∈ Ioo a b) (s : S) :
    mpullback (𝓘(ℝ).prod J) I Φ (σ.interiorₗ ⟨Y, hY⟩).val (t, s) =
      (SmoothForm.mpullback _ hΦ₀ (σ.interiorₗ ⟨Y, hY⟩)).symplectization.val (t - t₀, s) := by
  classical
  set U' : Opens W := ⟨U, hU⟩
  have : BoundarylessManifold I U' :=
    ⟨fun x ↦ I.isInteriorPoint_iff_isInteriorPoint_val.2 (hUW x.property)⟩
  set M' := InteriorModel I U'
  set h := interiorModelDiffeomorph I U'
  have hYU : ContMDiffOn I I.tangent ∞ (T% Y) U := hY.contMDiffOn
  -- The field `Y` and the primitive `ι_Y σ`, restricted to `U'`.
  let Y₁ : (x : U') → TangentSpace I x := VectorField.mpullback I I Subtype.val Y
  have hY₁ : ContMDiff I I.tangent ∞ (T% Y₁) := VectorField.contMDiff_mpullback_subtypeVal hYU
  let β₁ : SmoothForm I U' ℝ 1 :=
    ⟨_, (isSmoothForm_mpullback_subtypeVal_interior (U := U')
      σ.isSmoothForm.contMDiff.contMDiffOn hYU).mem_smoothBundleForms⟩
  have hβ₁ : β₁.val = mpullback I I Subtype.val (RoughForm.interior Y σ.val) := rfl
  have hdβ₁ : (mextDeriv β₁.val).interior Y₁ = β₁.val :=
    interior_mextDeriv_mpullback_subtypeVal_interior hσ hYU hYσ
  -- The same, transported to the re-modelled copy `M'` of `U'`.
  let Z : (x : M') → TangentSpace 𝓘(ℝ, E) x := VectorField.mpullback 𝓘(ℝ, E) I h.symm Y₁
  have hZ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent ∞ (T% Z) := by
    have := h.symm.isLocalDiffeomorph.contMDiffOn_mpullback (t := univ) hY₁.contMDiffOn le_rfl
    rwa [preimage_univ, contMDiffOn_univ] at this
  have hZY₁ (y : M') : mfderiv 𝓘(ℝ, E) I h.symm y (Z y) = Y₁ (h.symm y) :=
    (h.symm.isLocalDiffeomorph y).mfderiv_apply_mpullback (by simp) Y₁
  let β : SmoothForm 𝓘(ℝ, E) M' ℝ 1 := SmoothForm.mpullback h.symm h.symm.contMDiff β₁
  have hβ : β.val = mpullback 𝓘(ℝ, E) I h.symm β₁.val := SmoothForm.coe_mpullback _ _ _
  have hdβ : (mextDeriv β.val).interior Z = β.val := by
    have hd : mextDeriv β.val = mpullback 𝓘(ℝ, E) I h.symm (mextDeriv β₁.val) := by
      funext y
      rw [hβ]
      exact (mpullback_mextDeriv_at (h.symm.contMDiff.contMDiffAt.of_le (by norm_num))
        ((β₁.contMDiff (h.symm y)).of_le (by norm_num))).symm
    rw [hd, ← mpullback_interior _ _ _ _ hZY₁, hdβ₁, hβ]
  -- The lines of `Φ`, as curves in `U'`, and their images in `M'`.
  let γ : S → ℝ → U' := fun s τ ↦
    if hτ : Φ (τ, s) ∈ U then ⟨Φ (τ, s), hτ⟩ else ⟨Φ (t₀, s), hΦU t₀ ht₀ s⟩
  have hγ (s : S) {τ : ℝ} (hτ : τ ∈ Ioo a b) : (γ s τ : W) = Φ (τ, s) := by
    simp [γ, hΦU τ hτ s]
  have hγY (s : S) : IsMIntegralCurveOn (γ s) Y₁ (Ioo a b) := by
    refine VectorField.isMIntegralCurveOn_mpullback_subtypeVal_iff.2 fun τ hτ ↦ ?_
    refine ((hΦY s τ hτ).congr_of_eventuallyEq (f₁ := Subtype.val ∘ γ s)
      (eventually_nhdsWithin_of_forall fun τ' hτ' ↦ hγ s hτ') (hγ s hτ)).congr_mfderiv
      (ContinuousLinearMap.ext fun r ↦ ?_)
    -- The two sides are `r • Y` at the same point, read in two equal tangent spaces.
    beta_reduce
    rw [comp_apply, ← hγ s hτ]
    rfl
  let Φ' : ℝ × S → M' := fun p ↦ h (γ p.2 p.1)
  have hΦ'Z (s : S) : IsMIntegralCurveOn (fun t ↦ Φ' (t, s)) Z (Ioo a b) :=
    (h.isMIntegralCurveOn_comp_iff (by simp)
      (h.symm.mfderiv_symm_apply_eq_of_mfderiv_apply_eq (by simp) hZY₁)).2 (hγY s)
  -- The slice of `Φ'` at `t₀` is the slice of `Φ`, read in `M'`.
  let ι₁ : S → U' := fun s ↦ ⟨Φ (t₀, s), hΦU t₀ ht₀ s⟩
  have hι₁ : ContMDiff J I ∞ ι₁ := (ContMDiff.subtypeVal_comp_iff _ ι₁).1 hΦ₀
  have hΦ'ι₁ : (fun s ↦ Φ' (t₀, s)) = h ∘ ι₁ := funext fun s ↦ by simp [Φ', γ, ι₁, hΦU t₀ ht₀ s]
  have hΦ'₀ : ContMDiff J 𝓘(ℝ, E) ∞ fun s ↦ Φ' (t₀, s) := hΦ'ι₁ ▸ h.contMDiff.comp hι₁
  have hval (y : U') : MDifferentiableAt I I (Subtype.val : U' → W) y :=
    (contMDiff_subtypeVal (n := 1) y).mdifferentiableAt one_ne_zero
  have hια : SmoothForm.mpullback _ hΦ'₀ β =
      SmoothForm.mpullback _ hΦ₀ (σ.interiorₗ ⟨Y, hY⟩) := by
    refine Subtype.ext (funext fun s ↦ ?_)
    rw [SmoothForm.coe_mpullback, SmoothForm.coe_mpullback _ hΦ₀, hβ,
      ← mpullback_comp_at ((hΦ'₀ s).mdifferentiableAt (by simp))
        (h.symm.mdifferentiable (by simp) _),
      hΦ'ι₁, show h.symm ∘ h ∘ ι₁ = ι₁ from funext fun s ↦ h.symm_apply_apply _, hβ₁,
      ← mpullback_comp_at ((hι₁ s).mdifferentiableAt (by simp)) (hval _),
      SmoothTwoForm.coe_interiorₗ, ContMDiffSection.coeFn_mk]
    -- `Subtype.val ∘ ι₁` is the slice of `Φ` by definition of `ι₁`.
    rfl
  -- `Φ` is `Φ'` read back in `W`, near `(t, s)`.
  let j : M' → W := Subtype.val ∘ h.symm
  have hΦeq : Φ =ᶠ[𝓝 (t, s)] j ∘ Φ' := by
    filter_upwards [(isOpen_Ioo.prod isOpen_univ).mem_nhds (mk_mem_prod ht (mem_univ s))] with p hp
    simp only [comp_apply, j, Φ', h.symm_apply_apply, hγ p.2 hp.1]
  have hj (y : M') : MDifferentiableAt 𝓘(ℝ, E) I j y :=
    (hval _).comp y (h.symm.mdifferentiable (by simp) y)
  have hjβ : mpullback 𝓘(ℝ, E) I j (σ.interiorₗ ⟨Y, hY⟩).val = β.val := by
    funext y
    rw [hβ, hβ₁, mpullback_comp_at (h.symm.mdifferentiable (by simp) y) (hval _),
      SmoothTwoForm.coe_interiorₗ, ContMDiffSection.coeFn_mk]
  rw [hΦeq.mpullback_eq, mpullback_comp_at ((contMDiffAt_of_isMIntegralCurveOn hZ hΦ'Z ht₀ hΦ'₀ ht
      s).mdifferentiableAt (by simp)) (hj _), hjβ,
    mpullback_apply_eq_symplectization_of_isMIntegralCurveOn hZ hdβ hΦ'Z ht₀ hΦ'₀ ht, hια]

end TauCeti

end
