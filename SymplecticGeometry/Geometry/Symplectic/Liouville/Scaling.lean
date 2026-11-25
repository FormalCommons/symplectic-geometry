/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.Liouville.Collar
public import TauCeti.Geometry.Symplectic.Manifold.Flat
import TauCeti.Geometry.Manifold.Flow.Diffeomorph
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Pullback.LocalDiffeomorph
import SymplecticGeometry.Geometry.Manifold.Flow.Basic
import SymplecticGeometry.Geometry.Manifold.MFDeriv.Opens
import TauCeti.Geometry.Manifold.ModelTransport.Interior
import SymplecticGeometry.Geometry.Manifold.VectorField.Pullback
import SymplecticGeometry.Geometry.Symplectic.Liouville.ContactType

/-!
# Liouville scaling along integral curves

Let `Z` be the Liouville field of a one-form `α`, `ι_Z dα = α`, on a boundaryless manifold, and
let `Φ : ℝ × S → M` have each line `t ↦ Φ (t, s)` an integral curve of `Z` on an interval
`(a, b)`. For `t₀ ∈ (a, b)` with a smooth slice `Φ (t₀, ·)`, the map `Φ` is the flow of `Z` out of
that slice, run for time `t - t₀`; so it is smooth on `(a, b) × S`
(`TauCeti.contMDiffAt_of_isMIntegralCurveOn`, in `SymplecticGeometry.Geometry.Manifold.Flow.Basic`)
and, by Tau Ceti's `TauCeti.mpullback_flowOf_comp_apply_eq_symplectization`, it pulls `α` back to
the symplectization form `e^(t - t₀) Φ(t₀, ·)^* α`
(`TauCeti.mpullback_apply_eq_symplectization_of_isMIntegralCurveOn`). Tau Ceti's theorem asks for
a boundaryless model; a manifold without boundary points over any model is re-modelled over the
model vector space by Tau Ceti's `TauCeti.BoundarylessModel.interiorDiffeomorph`, with the atlas
`TauCeti.BoundarylessModel.interiorChartedSpace` as a local instance, and a diffeomorphism, being
a local diffeomorphism, pulls a Liouville pair back to a Liouville
pair (`IsLocalDiffeomorph.interior_mextDeriv_mpullback_of_interior_mextDeriv`, in
`SymplecticGeometry.Geometry.Manifold.DifferentialForm.Pullback.LocalDiffeomorph`).

The same holds in the interior of a manifold with boundary, for a field that is Liouville only on
an open set. Let `σ` be a closed two-form on `W`, `Y` a smooth vector field, and `U` an open
subset of the interior of `W` with `L_Y σ = σ` on `U`. If `Φ` maps `(a, b) × S` into `U` and its
lines are integral curves of `Y`, then `Φ` pulls the primitive `ι_Y σ` back to
`e^(t - t₀) Φ(t₀, ·)^*(ι_Y σ)`; it vanishes on `∂ₜ`, since `ι_Y σ (Y) = σ(Y, Y) = 0`
(`TauCeti.mpullback_interiorₗ_apply_eq_symplectization_of_isMIntegralCurveOn`). The proof
restricts `Y` and `ι_Y σ` to `U` (`TauCeti.SmoothForm.restrictInterior`, Liouville there by
`TauCeti.SmoothTwoForm.interior_mextDeriv_restrictInterior`), as
`TauCeti.SmoothEmbedding.exists_pos_forall_liouvilleCollar` does; `U` has no boundary points, so
the boundaryless case applies there.

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

attribute [local instance] TauCeti.BoundarylessModel.interiorChartedSpace

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

/-! ### Integral curves on a boundaryless manifold -/

section Boundaryless

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {Z : (x : M) → TangentSpace I x} {Φ : ℝ × S → M} {a b t₀ t : ℝ} [IsManifold J ∞ S]

/-- The case of a boundaryless model, where Tau Ceti's theorem applies. -/
private theorem mpullback_apply_eq_symplectization_of_isMIntegralCurveOn_of_boundaryless
    [I.Boundaryless]
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

variable [BoundarylessManifold I M]

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
  -- Transport `Z`, `α` and `Φ` to the copy `M'` of `M` modelled on `E`.
  set h := BoundarylessModel.interiorDiffeomorph I (M := M) ∞
  let Z' : (y : BoundarylessModel I M) → TangentSpace 𝓘(ℝ, E) y :=
    VectorField.mpullback 𝓘(ℝ, E) I h.symm Z
  have hZ' : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent ∞ (T% Z') := by
    have := h.symm.isLocalDiffeomorph.contMDiffOn_mpullback (t := univ) hZ.contMDiffOn le_rfl
    rwa [preimage_univ, contMDiffOn_univ] at this
  let α' : SmoothForm 𝓘(ℝ, E) (BoundarylessModel I M) ℝ 1 :=
    SmoothForm.mpullback h.symm h.symm.contMDiff α
  have hα' : α'.val = mpullback 𝓘(ℝ, E) I h.symm α.val := SmoothForm.coe_mpullback _ _ _
  have hdα' : (mextDeriv α'.val).interior Z' = α'.val := by
    rw [hα']
    exact h.symm.isLocalDiffeomorph.interior_mextDeriv_mpullback_of_interior_mextDeriv
      (by simp) hZα
  have hΦ'Z (s : S) : IsMIntegralCurveOn (fun t ↦ h (Φ (t, s))) Z' (Ioo a b) :=
    (h.isMIntegralCurveOn_comp_iff (by simp) (h.symm.mfderiv_symm_apply_eq_of_mfderiv_apply_eq
      (by simp) (h.symm.mfderiv_apply_mpullback (by simp) Z))).2 (hΦZ s)
  have hΦ'₀ : ContMDiff J 𝓘(ℝ, E) ∞ fun s ↦ h (Φ (t₀, s)) := h.contMDiff.comp hΦ₀
  have hια : SmoothForm.mpullback _ hΦ'₀ α' = SmoothForm.mpullback _ hΦ₀ α := by
    simp only [α', SmoothForm.mpullback_mpullback, comp_def, h.symm_apply_apply]
  have hΦΦ' : mpullback (𝓘(ℝ).prod J) I Φ α.val =
      mpullback (𝓘(ℝ).prod J) I (h.symm ∘ fun p ↦ h (Φ p)) α.val := by
    simp only [comp_def, h.symm_apply_apply]
  rw [hΦΦ', mpullback_comp_at ((contMDiffAt_of_isMIntegralCurveOn le_top hZ' hΦ'Z ht₀ hΦ'₀ ht
      s).mdifferentiableAt (by simp)) (h.symm.mdifferentiable (by simp) _), ← hα',
    mpullback_apply_eq_symplectization_of_isMIntegralCurveOn_of_boundaryless hZ' hdα' hΦ'Z ht₀
      hΦ'₀ ht, hια]

end Boundaryless

/-! ### Integral curves in the interior of a manifold with boundary -/

variable {W : Type*} [TopologicalSpace W] [ChartedSpace H W] [IsManifold I ∞ W] [T2Space W]
  [IsManifold J ∞ S]

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
  have hYU : ContMDiffOn I I.tangent ∞ (T% Y) U := hY.contMDiffOn
  -- The field `Y` and the primitive `ι_Y σ`, restricted to `U'`.
  let Y₁ : (x : U') → TangentSpace I x := VectorField.mpullback I I Subtype.val Y
  have hY₁ : ContMDiff I I.tangent ∞ (T% Y₁) := VectorField.contMDiff_mpullback_subtypeVal hYU
  let β₁ : SmoothForm I U' ℝ 1 := σ.restrictInterior Y hYU
  have hβ₁ : β₁.val = mpullback I I Subtype.val (σ.interiorₗ ⟨Y, hY⟩).val := by
    rw [SmoothForm.coe_restrictInterior, SmoothTwoForm.coe_interiorₗ, ContMDiffSection.coeFn_mk]
  have hdβ₁ : (mextDeriv β₁.val).interior Y₁ = β₁.val :=
    SmoothTwoForm.interior_mextDeriv_restrictInterior hσ hYU hYσ
  -- The lines of `Φ`, as curves in `U'`.
  let Φ₁ : ℝ × S → U' := fun p ↦
    if hp : Φ p ∈ U then ⟨Φ p, hp⟩ else ⟨Φ (t₀, p.2), hΦU t₀ ht₀ p.2⟩
  have hΦ₁ {p : ℝ × S} (hp : p.1 ∈ Ioo a b) : (Φ₁ p : W) = Φ p := by
    simp [Φ₁, hΦU p.1 hp p.2]
  have hΦ₁Y (s : S) : IsMIntegralCurveOn (fun t ↦ Φ₁ (t, s)) Y₁ (Ioo a b) :=
    VectorField.isMIntegralCurveOn_mpullback_subtypeVal_iff.2
      ((hΦY s).congr fun τ hτ ↦ hΦ₁ (p := (τ, s)) hτ)
  -- The slice of `Φ₁` at `t₀` is the slice of `Φ`, read in `U'`.
  have hΦ₁₀ : ContMDiff J I ∞ fun s ↦ Φ₁ (t₀, s) :=
    (ContMDiff.subtypeVal_comp_iff _ _).1 (by simpa [comp_def, hΦ₁ (p := (t₀, _)) ht₀] using hΦ₀)
  have hια : SmoothForm.mpullback _ hΦ₁₀ β₁ =
      SmoothForm.mpullback _ hΦ₀ (σ.interiorₗ ⟨Y, hY⟩) := by
    -- `β₁` is the pullback of `ι_Y σ` along the inclusion, as a smooth form.
    rw [show β₁ = SmoothForm.mpullback Subtype.val contMDiff_subtypeVal (σ.interiorₗ ⟨Y, hY⟩) from
      Subtype.ext (hβ₁.trans (SmoothForm.coe_mpullback _ _ _).symm)]
    simp only [SmoothForm.mpullback_mpullback, comp_def, hΦ₁ (p := (t₀, _)) ht₀]
  -- `Φ` is `Φ₁` read back in `W`, near `(t, s)`.
  have hΦeq : Φ =ᶠ[𝓝 (t, s)] Subtype.val ∘ Φ₁ := by
    filter_upwards [(isOpen_Ioo.prod isOpen_univ).mem_nhds (mk_mem_prod ht (mem_univ s))] with p hp
    exact (hΦ₁ hp.1).symm
  rw [hΦeq.mpullback_eq, mpullback_comp_at ((contMDiffAt_of_isMIntegralCurveOn le_top hY₁ hΦ₁Y ht₀
      hΦ₁₀ ht s).mdifferentiableAt (by simp)) SymplecticGeometry.mdifferentiableAt_subtypeVal,
    ← hβ₁,
    mpullback_apply_eq_symplectization_of_isMIntegralCurveOn hY₁ hdβ₁ hΦ₁Y ht₀ hΦ₁₀ ht, hια]

end TauCeti

end
