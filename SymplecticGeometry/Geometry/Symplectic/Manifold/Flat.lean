/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Pullback
public import TauCeti.Geometry.Symplectic.Lagrangian.Basic
public import TauCeti.Geometry.Symplectic.Manifold.Flat
import TauCeti.Analysis.Normed.Module.Alternating.Curry
import TauCeti.Geometry.Manifold.VectorBundle.Hom

/-!
# Inverse flat maps of covector fields

For a two-form `σ` and a covector field `c` on `M`, the vector field `x ↦ (σ♭_x)⁻¹ (c x)`
contracts with `σ` to `c` at each point where the flat map `σ♭_x` is invertible, and it is
smooth at each point where `c` is smooth and `σ♭` is invertible. Tau Ceti's
`TauCeti.SmoothTwoForm.IsNondegenerate.interiorEquiv` gives this field for a one-form smooth on
all of `M` and a nondegenerate form; the lemmas here are pointwise, so they apply to covector
fields smooth only near a set, and to families of two-forms along a map.

Let `σ` be a nondegenerate two-form on a boundaryless finite-dimensional manifold and `β` a
one-form. If `β` vanishes at a point `x` and its coordinate expression in the chart at `x` has
zero derivative there, then the coordinate expression of the vector field `(σ♭)⁻¹ β` in the chart
at `x` also has zero derivative at the chart point of `x`. In the relative Moser argument this is
what makes the Moser flow fix `x` to first order ([McDuffSalamon2017], §3.2;
[McDuffSalamon2019Errata], p. 109): the derivative is the hypothesis of Tau Ceti's
`TauCeti.mfderiv_timeDependentFlowOf_eq_id_of_forall_eq_zero`.

## Main results

* `TauCeti.SmoothTwoForm.interior_flat_inverse_apply`: `ι_{(σ♭)⁻¹ c} σ = c` at a point where
  `σ♭` is invertible, and
  `TauCeti.SmoothTwoForm.IsNondegenerate.interior_flat_inverse_ofSubsingleton`, the identity of
  rough one-forms for a nondegenerate `σ`.
* `TauCeti.SmoothTwoForm.mfderiv_flat_mpullback_inverse_apply`: inverse flat maps commute with
  smooth maps whose differential is invertible at the point, the form being pulled back and the
  covector composed with the differential.
* `TauCeti.SmoothTwoForm.contMDiffAt_sectionAlong_flat_inverse_apply`: the field `(σ♭)⁻¹ c`, for
  a family of two-forms along a map, is smooth where `c` and the forms are and the flat map is
  invertible. For a single two-form, Tau Ceti's `TauCeti.SmoothTwoForm.contMDiffAt_inverse_flat`
  gives the smoothness of `(σ♭)⁻¹` at such a point.
* `TauCeti.SmoothTwoForm.IsNondegenerate.hasFDerivAt_mpullbackWithin_interiorEquiv_symm`: the
  coordinate expression of `(σ♭)⁻¹ β` has zero derivative where `β` vanishes to first order.
* `TauCeti.SmoothTwoForm.IsNondegenerate.orthogonal_flat` and
  `TauCeti.SmoothTwoForm.Compatible.orthogonal_flatComp`: the orthogonal of a subspace for the
  bilinear form `σ♭_x` is its symplectic complement, and, for a compatible almost complex
  structure `J`, its orthogonal for `σ(J ·, ·)` is its orthogonal for the metric `σ(·, J ·)`.
* `TauCeti.SmoothTwoForm.Tames.flatComp_apply_self_eq_zero_iff`: if `σ` tames `J`, the form
  `σ(J ·, ·)` vanishes on the diagonal only at `0`.
* `TauCeti.SmoothTwoForm.contMDiff_flat_pullback` and
  `TauCeti.SmoothTwoForm.contMDiff_flatComp_pullback`: along a smooth map `f`, the forms
  `σ♭_{f q}` and `σ(C ·, ·)` at `f q` are smooth sections of the bundle of bilinear forms on
  the pull-back `f *ᵖ TM`.

The smoothness lemma takes the argument by which Tau Ceti's
`TauCeti.SmoothTwoForm.IsNondegenerate.interiorEquiv` shows that its inverse is smooth
(`ContMDiffAt.clm_bundle_inverse`, then `ContMDiffAt.clm_bundle_apply`) and makes it
pointwise, for a family of two-forms along a map.

The proof of `hasFDerivAt_mpullbackWithin_interiorEquiv_symm` adapts Tau Ceti's private
`hasFDerivAt_mpullbackWithin_moserField`
(`TauCeti/Geometry/Symplectic/Manifold/RelativeMoser.lean`) from the cut-off Moser field to a
general inverse flat map: in the chart, the field is the inverse of the flat map of the
coordinate form applied to the coordinate expression of `β`; these inverses stay bounded near
the chart point, and `β` vanishes there to first order.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017]
* [D. McDuff and D. Salamon, *Errata*][McDuffSalamon2019Errata]
-/

public section

open Bundle Set Filter
open scoped ContDiff Manifold Topology

namespace TauCeti

namespace SmoothTwoForm

section FlatInverse

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {σ : SmoothTwoForm I M}

/-- At a point `x` where the flat map of `σ` is invertible, the vector field
`y ↦ (σ♭_y)⁻¹ (c y)` contracts with `σ` to the covector `c x`, read as a one-form:
`ι_{(σ♭)⁻¹ c} σ = c` at `x`. -/
theorem interior_flat_inverse_apply (σ : SmoothTwoForm I M)
    (c : (x : M) → TangentSpace I x →L[ℝ] ℝ) {x : M} (hx : (σ.flat x).IsInvertible) :
    RoughForm.interior (fun y ↦ (σ.flat y).inverse (c y)) σ.val x =
      ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace I x) ℝ 0 (c x) := by
  rw [interior_apply_eq_ofSubsingleton_flat, hx.self_apply_inverse]

/-- For a nondegenerate two-form `σ` on a finite-dimensional manifold and a rough one-form `β`,
the vector field `x ↦ (σ♭_x)⁻¹ β_x`, with `β_x` read as a covector, contracts with `σ` to `β`. -/
theorem IsNondegenerate.interior_flat_inverse_ofSubsingleton [FiniteDimensional ℝ E]
    (h : σ.IsNondegenerate) (β : RoughForm I M ℝ 1) :
    RoughForm.interior (fun x ↦ (σ.flat x).inverse
      ((ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace I x) ℝ 0).symm (β x)))
        σ.val = β :=
  funext fun x ↦ (interior_flat_inverse_apply σ _ (h.isInvertible_flat x)).trans
    ((ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace I x) ℝ 0).apply_symm_apply _)

variable [CompleteSpace E]

/-- **Inverse flat maps along a smooth family of two-forms.** Let `σ m` be smooth two-forms on
`M` and `c m` covectors at `b m`, depending on `m ∈ N`, along a map `b : N → M`. If the values
`(σ m)_(b m)` and the covectors `c m` depend `C^n` on `m` at `m₀`, and the flat map of `σ m₀` at
`b m₀` is invertible, then the vectors `((σ m)♭_(b m))⁻¹ (c m)` depend `C^n` on `m` at `m₀`, as a
map into the tangent bundle. -/
theorem contMDiffAt_sectionAlong_flat_inverse_apply {EN HN N : Type*} [NormedAddCommGroup EN]
    [NormedSpace ℝ EN] [TopologicalSpace HN] {J : ModelWithCorners ℝ EN HN} [TopologicalSpace N]
    [ChartedSpace HN N] {n : WithTop ℕ∞} {b : N → M} {σ : N → SmoothTwoForm I M}
    {c : (m : N) → TangentSpace I (b m) →L[ℝ] ℝ} {m₀ : N}
    (hσ : ContMDiffAt J (I.prod 𝓘(ℝ, E [⋀^Fin 2]→L[ℝ] ℝ)) n
      (fun m ↦ TotalSpace.mk' (E [⋀^Fin 2]→L[ℝ] ℝ)
        (E := fun x : M ↦ TangentSpace I x [⋀^Fin 2]→L[ℝ] Trivial M ℝ x) (b m) ((σ m).val (b m)))
      m₀)
    (hinv : ((σ m₀).flat (b m₀)).IsInvertible)
    (hc : ContMDiffAt J (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) n
      (fun m ↦ TotalSpace.mk' (E →L[ℝ] ℝ) (E := fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) (b m)
        (c m)) m₀) :
    ContMDiffAt J I.tangent n
      (fun m ↦ (⟨b m, ((σ m).flat (b m)).inverse (c m)⟩ : TangentBundle I M)) m₀ :=
  (ContMDiffAt.clm_bundle_inverse (x := m₀) (b := b) (E₁ := TangentSpace I)
    (E₂ := fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) (ϕ := fun m ↦ (σ m).flat (b m))
    (contMDiffAt_sectionAlong_flat hσ) hinv).clm_bundle_apply hc

end FlatInverse

namespace IsNondegenerate

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] {σ : SmoothTwoForm I M}

/-- **The inverse flat map of a one-form with zero first jet.** Let `σ` be a nondegenerate
two-form and `β` a one-form that vanishes at `x` and whose coordinate expression in the chart at
`x` has zero derivative at the chart point of `x`. Then the coordinate expression of the vector
field `(σ♭)⁻¹ β` in the chart at `x` has zero derivative at that point. -/
theorem hasFDerivAt_mpullbackWithin_interiorEquiv_symm (h : σ.IsNondegenerate)
    {β : SmoothForm I M ℝ 1} {x : M} (hβx : β.val x = 0)
    (hβ : HasFDerivAt (RoughForm.inChartAt β.val x) (0 : E →L[ℝ] E [⋀^Fin 1]→L[ℝ] ℝ)
      (extChartAt I x x)) :
    HasFDerivAt (VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm
      (h.interiorEquiv.symm β) (range I)) (0 : E →L[ℝ] E) (extChartAt I x x) := by
  set z₀ := extChartAt I x x
  set V : E → E := VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm
    (h.interiorEquiv.symm β) (range I)
  -- The flat maps of the coordinate expression of `σ`.
  set F : E → E →L[ℝ] E →L[ℝ] ℝ := fun z ↦ ContinuousAlternatingMap.flatL ℝ E ℝ
    (RoughForm.inChartAt σ.val x z)
  have hFc : ContinuousAt F z₀ := by
    have hc := (σ.isSmoothForm.contDiffWithinAt_inChartAt_self x).continuousWithinAt
    rw [I.range_eq_univ, continuousWithinAt_univ] at hc
    exact (ContinuousAlternatingMap.flatL ℝ E ℝ).continuous.continuousAt.comp hc
  have hF₀ : (F z₀).IsInvertible := by
    simp only [F, z₀, RoughForm.inChartAt_extChartAt_self, ← flat_def]
    exact h.isInvertible_flat x
  -- In the chart, `σ'♭(z) (V z) = β'(z)`, read as alternating maps of one vector.
  have hkey : ∀ᶠ z in 𝓝 z₀, ‖F z (V z)‖ = ‖RoughForm.inChartAt β.val x z‖ :=
    eventually_of_mem (extChartAt_target_mem_nhds x) fun z hz ↦ by
      have hi := RoughForm.inChartAt_interior (h.interiorEquiv.symm β) σ.val hz
      rw [interior_interiorEquiv_symm] at hi
      refine (ContinuousAlternatingMap.norm_ofSubsingleton (ι := Fin 1) 0 _).symm.trans ?_
      rw [ContinuousAlternatingMap.ofSubsingleton_flatL_apply, hi]
  -- The inverses of `σ'♭(z)` are bounded near `z₀`, so `V = O(β')`.
  set G : E → (E →L[ℝ] ℝ) →L[ℝ] E := fun z ↦ (F z).inverse
  -- Name the operator norm instance: inferring it through the dual space times out.
  let : NormedAddCommGroup ((E →L[ℝ] ℝ) →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
  have hGc : ContinuousAt G z₀ := (hF₀.contDiffAt_map_inverse (n := 0)).continuousAt.comp hFc
  have hbig : V =O[𝓝 z₀] RoughForm.inChartAt β.val x := by
    refine Asymptotics.IsBigO.of_bound (‖G z₀‖ + 1) ?_
    filter_upwards [hFc.eventually hF₀.eventually_nhds, hkey,
      hGc.norm.eventually (gt_mem_nhds (lt_add_one ‖G z₀‖))] with z hzF hzk hzG
    calc ‖V z‖ = ‖G z (F z (V z))‖ := by rw [hzF.inverse_apply_self]
      _ ≤ ‖G z‖ * ‖F z (V z)‖ := (G z).le_opNorm _
      _ ≤ (‖G z₀‖ + 1) * ‖RoughForm.inChartAt β.val x z‖ := by rw [hzk]; gcongr
  -- `β'` vanishes to first order at `z₀`, hence so does `V`.
  have hβ₀ : RoughForm.inChartAt β.val x z₀ = 0 :=
    (RoughForm.inChartAt_extChartAt_self _ x).trans hβx
  have hV₀ : V z₀ = 0 := by
    have h0 : h.interiorEquiv.symm β ((extChartAt I x).symm z₀) = 0 := by
      rw [interiorEquiv_symm_apply_eq_zero_iff, extChartAt_to_inv]
      exact hβx
    simp only [V]
    rw [VectorField.mpullbackWithin_apply, h0, map_zero]
    -- The zero of the tangent space of the model space is the zero of `E`.
    rfl
  have hβo := hβ.isLittleO
  simp only [hβ₀, sub_zero, zero_apply] at hβo
  exact .of_isLittleO (by
    simpa only [hV₀, sub_zero, zero_apply] using hbig.trans_isLittleO hβo)

end IsNondegenerate

section Orthogonal

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {σ : SmoothTwoForm I M} {Jc : SmoothAlmostComplexStructure I M}

/-- The orthogonal of a subspace for the flat map of a nondegenerate two-form is its symplectic
complement. -/
theorem IsNondegenerate.orthogonal_flat (hω : σ.IsNondegenerate) (x : M)
    (N : Submodule ℝ (TangentSpace I x)) :
    LinearMap.BilinForm.orthogonal (σ.flat x).toLinearMap₁₂ N =
      (hω.symplecticFormAt x).orthogonal N := by
  rw [SymplecticForm.orthogonal_def]
  congr 1
  ext v w
  simp

/-- For a compatible almost complex structure `J`, the orthogonal of a subspace for the forms
`σ(J ·, ·)` is its orthogonal for the metric `g = σ(·, J ·)`: by invariance, the two forms differ
by a sign. -/
theorem Compatible.orthogonal_flatComp (hc : σ.Compatible Jc) (x : M)
    (N : Submodule ℝ (TangentSpace I x)) :
    LinearMap.BilinForm.orthogonal (σ.flatComp Jc.toEndomorphism x).toLinearMap₁₂ N =
      ((hc.isNondegenerate.symplecticFormAt x).associatedBilinForm
        (Jc.almostComplexStructureAt x)).orthogonal N := by
  ext w
  simp only [LinearMap.BilinForm.mem_orthogonal_iff]
  refine forall₂_congr fun v _ ↦ ?_
  have h := (SymplecticForm.invariant_iff _ _).1 (hc.compatibleAt x).invariant v
    (Jc.almostComplexStructureAt x w)
  simp only [AlmostComplexStructure.apply_apply, map_neg] at h
  simp only [SymplecticForm.associatedBilinForm_apply, ContinuousLinearMap.toLinearMap₁₂_apply,
    flatComp_apply]
  rw [← h, neg_eq_zero]
  simp

/-- If `σ` tames `J`, the bilinear form `σ(J ·, ·)` vanishes on the diagonal only at `0`, since
`σ(J u, u) = -σ(u, J u)`. -/
theorem Tames.flatComp_apply_self_eq_zero_iff (h : σ.Tames Jc) {x : M} {u : TangentSpace I x} :
    σ.flatComp Jc.toEndomorphism x u u = 0 ↔ u = 0 := by
  refine ⟨fun hu ↦ ?_, fun hu ↦ by simp [hu]⟩
  by_contra hne
  have hp := tames_iff.1 h x u hne
  rw [flatComp_apply, ContinuousLinearMap.comp_apply, flat_apply, SmoothBundleForm.eval₂_swap,
    neg_eq_zero] at hu
  exact hp.ne' (by simpa using hu)

end Orthogonal

section Pullback

variable {E E' H H' M Q K : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  [TopologicalSpace Q] [ChartedSpace H' Q] [FunLike K Q M] [ContinuousMapClass K Q M]

/-- Along a `C^∞` map `f`, the flat maps `v ↦ σ(v, ·)` of `σ` at the points `f q` form a smooth
section of the bundle of bilinear forms on the pull-back `f *ᵖ TM`. -/
theorem contMDiff_flat_pullback (σ : SmoothTwoForm I M) (f : K) (hf : ContMDiff J I ∞ f) :
    ContMDiff J (J.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun q ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun q ↦ ((f : Q → M) *ᵖ (TangentSpace I)) q →L[ℝ]
          ((f : Q → M) *ᵖ (TangentSpace I)) q →L[ℝ] ℝ) q (σ.flat (f q))) :=
  (Bundle.Pullback.contMDiff_bilinear_section_iff f hf _).mpr (σ.contMDiff_flat.comp hf)

/-- Along a `C^∞` map `f`, the forms `σ(C ·, ·)` at the points `f q`, for a smooth section `C` of
`End(TM)`, form a smooth section of the bundle of bilinear forms on the pull-back `f *ᵖ TM`. -/
theorem contMDiff_flatComp_pullback (σ : SmoothTwoForm I M)
    (C : Cₛ^∞⟮I; E →L[ℝ] E, fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x⟯) (f : K)
    (hf : ContMDiff J I ∞ f) :
    ContMDiff J (J.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun q ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun q ↦ ((f : Q → M) *ᵖ (TangentSpace I)) q →L[ℝ]
          ((f : Q → M) *ᵖ (TangentSpace I)) q →L[ℝ] ℝ) q (σ.flatComp C (f q))) :=
  (Bundle.Pullback.contMDiff_bilinear_section_iff f hf _).mpr
    ((σ.flatComp C).contMDiff.comp hf)

end Pullback

section Naturality

variable {E E' H H' M M' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']

/-- **Naturality of inverse flat maps.** For a `C^∞` map `ψ : M → M'` whose differential at `x`
is invertible, a two-form `σ` on `M'` and a covector `c` at `ψ x`, the differential of `ψ` at `x`
carries `((ψ^* σ)♭_x)⁻¹ (c ∘ dψ_x)` to `(σ♭_{ψ x})⁻¹ c`. Both sides are `0` when the flat maps
are not invertible, as they then both are not. -/
theorem mfderiv_flat_mpullback_inverse_apply {ψ : M → M'} (hψ : ContMDiff I I' ∞ ψ)
    (σ : SmoothTwoForm I' M') {x : M} (hx : (mfderiv I I' ψ x).IsInvertible)
    (c : TangentSpace I' (ψ x) →L[ℝ] ℝ) :
    mfderiv I I' ψ x ((flat (SmoothForm.mpullback ψ hψ σ) x).inverse
        (c ∘L mfderiv I I' ψ x)) =
      (σ.flat (ψ x)).inverse c := by
  obtain ⟨e, he⟩ := hx
  -- Precomposition with `dψ_x`, from covectors at `ψ x` to covectors at `x`.
  set P := e.symm.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)
  have hP (f : TangentSpace I' (ψ x) →L[ℝ] ℝ) : P f = f ∘L mfderiv I I' ψ x := by
    ext v
    simp [P, ← he]
  -- The flat map of `ψ^* σ` at `x` is that of `σ` at `ψ x`, conjugated by `dψ_x`.
  have hflat : flat (SmoothForm.mpullback ψ hψ σ) x =
      (P : _ →L[ℝ] _) ∘L σ.flat (ψ x) ∘L (e : TangentSpace I x →L[ℝ] TangentSpace I' (ψ x)) := by
    ext v w
    rw [flat_apply, SmoothForm.eval₂_mpullback]
    simp [hP, he]
  rw [hflat, ContinuousLinearMap.inverse_equiv_comp, ContinuousLinearMap.inverse_comp_equiv,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, P.symm_apply_eq.2 (hP c).symm,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, ← he,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]

end Naturality

end SmoothTwoForm

end TauCeti

end
